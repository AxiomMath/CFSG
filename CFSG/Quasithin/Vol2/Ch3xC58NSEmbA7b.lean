module

public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbA7a
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.C58NS.Emb

open Equiv

theorem le_range_ofSubtype {α : Type*} [DecidableEq α] {O : α → Prop} [DecidablePred O]
    {K : Subgroup (Perm α)} (hK : ∀ k ∈ K, ∀ x, ¬ O x → k x = x) :
    K ≤ (Perm.ofSubtype : Perm (Subtype O) →* Perm α).range := by
  intro k hk
  have hfix := hK k hk
  have h₁ : ∀ x, O x ↔ O (k x) := by
    intro x
    constructor
    · intro hx
      by_contra hkx
      have h2 : k x = x := k.injective (hfix (k x) hkx)
      exact hkx (by rw [h2]; exact hx)
    · intro hkx
      by_contra hx
      exact hx (hfix x hx ▸ hkx)
  have h₁' : ∀ x, O (k x) ↔ O x := fun x => (h₁ x).symm
  refine ⟨k.subtypePerm h₁', Perm.ofSubtype_subtypePerm h₁' fun x hx => ?_⟩
  by_contra hO
  exact hx (hfix x hO)

theorem card_comap_ofSubtype {α : Type*} [DecidableEq α] {O : α → Prop} [DecidablePred O]
    {K : Subgroup (Perm α)} (hK : K ≤ (Perm.ofSubtype : Perm (Subtype O) →* Perm α).range) :
    Nat.card (K.comap (Perm.ofSubtype : Perm (Subtype O) →* Perm α)) = Nat.card K := by
  have hinj : Function.Injective (Perm.ofSubtype : Perm (Subtype O) →* Perm α) :=
    fun a b h => Perm.ofSubtype_injective h
  have h := Subgroup.card_map_of_injective (K := K.comap
    (Perm.ofSubtype : Perm (Subtype O) →* Perm α)) hinj
  rw [Subgroup.map_comap_eq_self hK] at h
  exact h.symm

theorem comap_ofSubtype_le_alt {α : Type*} [Fintype α] [DecidableEq α] {O : α → Prop}
    [DecidablePred O] {K : Subgroup (Perm α)} (hKA : K ≤ alternatingGroup α) :
    K.comap (Perm.ofSubtype : Perm (Subtype O) →* Perm α) ≤ alternatingGroup (Subtype O) := by
  intro σ hσ
  rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype]
  exact Perm.mem_alternatingGroup.mp (hKA hσ)

theorem card_filter_ne (p : Fin 7) : (Finset.univ.filter fun x : Fin 7 => x ≠ p).card = 6 := by
  revert p
  decide

theorem card_filter_ne_ne (p q : Fin 7) (hpq : p ≠ q) :
    (Finset.univ.filter fun x : Fin 7 => x ≠ p ∧ x ≠ q).card = 5 := by
  revert p q
  decide

theorem false_of_fixSet_eq_singleton {H D : Subgroup (Perm (Fin 7))} [IsSimpleGroup H]
    (hH : Nat.card H = 60) (hHA : H ≤ alternatingGroup (Fin 7))
    (hDA : D ≤ alternatingGroup (Fin 7)) (hD : Nat.card D = 8)
    (hDN : D ≤ Subgroup.normalizer (H : Set (Perm (Fin 7)))) {p : Fin 7}
    (hp : fixSet H = {p}) : False := by
  classical
  have hpH : p ∈ fixSet H := by rw [hp]; rfl
  set M := H ⊔ D with hM
  have hMN : M ≤ Subgroup.normalizer (H : Set (Perm (Fin 7))) := sup_le Subgroup.le_normalizer hDN
  have hMp : ∀ m ∈ M, ∀ x, ¬ (x ≠ p) → m x = x := by
    have hle : M ≤ MulAction.stabilizer (Perm (Fin 7)) p := by
      refine sup_le (fun h hh => ?_) (fun d hd => ?_)
      · exact hpH h hh
      · have h1 := mem_fixSet_of_mem_normalizer (hDN hd) hpH
        rw [hp] at h1
        exact h1
    intro m hm x hx
    push Not at hx
    rw [hx]
    exact MulAction.mem_stabilizer_iff.mp (hle hm)
  set f := (Perm.ofSubtype : Perm {x : Fin 7 // x ≠ p} →* Perm (Fin 7)) with hf
  have hMr := le_range_ofSubtype (O := fun x : Fin 7 => x ≠ p) hMp
  have hcardM' := card_comap_ofSubtype hMr
  have hM'A := comap_ofSubtype_le_alt (O := fun x : Fin 7 => x ≠ p) (sup_le hHA hDA)
  have hO : Fintype.card {x : Fin 7 // x ≠ p} = 6 := by
    rw [Fintype.card_subtype]
    exact card_filter_ne p
  have hO' : 5 ≤ Nat.card {x : Fin 7 // x ≠ p} := by
    rw [Nat.card_eq_fintype_card, hO]
    norm_num
  have : Nontrivial {x : Fin 7 // x ≠ p} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hO]; norm_num)
  have hAlt : Nat.card (alternatingGroup {x : Fin 7 // x ≠ p}) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, hO]
    decide
  have hsimp : IsSimpleGroup (alternatingGroup {x : Fin 7 // x ≠ p}) :=
    alternatingGroup.isSimpleGroup hO'
  set I : Subgroup (alternatingGroup {x : Fin 7 // x ≠ p}) :=
    (M.comap f).subgroupOf (alternatingGroup {x : Fin 7 // x ≠ p}) with hI
  have hIc : Nat.card I = Nat.card M := by
    rw [← hcardM']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'A).toEquiv
  have hMdvd : Nat.card M ∣ 360 := by
    rw [← hIc, ← hAlt]
    exact Subgroup.card_subgroup_dvd_card I
  have h120 : 120 ∣ Nat.card M := by
    have h60 : 60 ∣ Nat.card M := hH ▸ Subgroup.card_dvd_of_le le_sup_left
    have h8 : 8 ∣ Nat.card M := hD ▸ Subgroup.card_dvd_of_le le_sup_right
    exact Nat.lcm_dvd h60 h8
  obtain ⟨c, hc⟩ := h120
  have hc3 : c ∣ 3 := by
    rw [hc, show (360 : ℕ) = 120 * 3 by norm_num] at hMdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 120)).mp hMdvd
  have hcle : c ≤ 3 := Nat.le_of_dvd (by norm_num) hc3
  interval_cases c
  · omega
  ·
    have hidx : I.index = 3 := by
      have h := I.index_mul_card
      rw [hIc, hc, hAlt] at h
      omega
    have hdvd := Subgroup.index_normalCore_dvd_factorial_index I
    rw [hidx] at hdvd
    rcases (Subgroup.normalCore_normal I).eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.index_bot, hAlt] at hdvd
      revert hdvd
      decide
    · have hle := Subgroup.normalCore_le I
      rw [ht, top_le_iff] at hle
      rw [hle, Subgroup.index_top] at hidx
      omega
  · omega
  ·
    have hItop : I = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hIc, hc, hAlt]
    set J : Subgroup (alternatingGroup {x : Fin 7 // x ≠ p}) :=
      (H.comap f).subgroupOf (alternatingGroup {x : Fin 7 // x ≠ p}) with hJ
    have hHr : H ≤ f.range := le_sup_left.trans hMr
    have hH'A : H.comap f ≤ alternatingGroup {x : Fin 7 // x ≠ p} :=
      (Subgroup.comap_mono le_sup_left).trans hM'A
    have hJc : Nat.card J = 60 := by
      rw [← hH, ← card_comap_ofSubtype hHr]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'A).toEquiv
    have hJn : J.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgI : g ∈ I := by rw [hItop]; exact Subgroup.mem_top g
      have hgM : f (g : Perm {x : Fin 7 // x ≠ p}) ∈ M :=
        Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp hgI)
      have hnH : f (n : Perm {x : Fin 7 // x ≠ p}) ∈ H :=
        Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp hn)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hMN hgM) _).mp hnH
    rcases hJn.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot] at hJc
      omega
    · rw [ht, Subgroup.card_top, hAlt] at hJc
      omega

theorem eq_map_alt_of_fixSet {H : Subgroup (Perm (Fin 7))} (hH : Nat.card H = 60)
    (hHA : H ≤ alternatingGroup (Fin 7)) {p q : Fin 7} (hpq : p ≠ q) (hf : fixSet H = {p, q}) :
    H = (alternatingGroup {x : Fin 7 // x ≠ p ∧ x ≠ q}).map
      (Perm.ofSubtype : Perm {x : Fin 7 // x ≠ p ∧ x ≠ q} →* Perm (Fin 7)) := by
  classical
  have hHp : ∀ h ∈ H, ∀ x, ¬ (x ≠ p ∧ x ≠ q) → h x = x := by
    intro h hh x hx
    have hx' : x ∈ fixSet H := by
      rw [hf]
      by_cases hxp : x = p
      · exact Or.inl hxp
      · exact Or.inr (by by_contra hxq; exact hx ⟨hxp, hxq⟩)
    exact hx' h hh
  have hr := le_range_ofSubtype (O := fun x : Fin 7 => x ≠ p ∧ x ≠ q) hHp
  have hc := card_comap_ofSubtype hr
  have hA := comap_ofSubtype_le_alt (O := fun x : Fin 7 => x ≠ p ∧ x ≠ q) hHA
  have hO : Fintype.card {x : Fin 7 // x ≠ p ∧ x ≠ q} = 5 := by
    rw [Fintype.card_subtype]
    exact card_filter_ne_ne p q hpq
  have : Nontrivial {x : Fin 7 // x ≠ p ∧ x ≠ q} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hO]; norm_num)
  have hAlt : Nat.card (alternatingGroup {x : Fin 7 // x ≠ p ∧ x ≠ q}) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, hO]
    decide
  have heq : H.comap (Perm.ofSubtype : Perm {x : Fin 7 // x ≠ p ∧ x ≠ q} →* Perm (Fin 7)) =
      alternatingGroup {x : Fin 7 // x ≠ p ∧ x ≠ q} :=
    Subgroup.eq_of_le_of_card_ge hA (le_of_eq (by rw [hc, hAlt, hH]))
  rw [← heq, Subgroup.map_comap_eq_self hr]

end CFSG.Quasithin.C58NS.Emb
