module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem inf_eq_bot_of_card_two {Z X : Subgroup G} (hZ : Nat.card Z = 2) (h : ¬ Z ≤ X) :
    Z ⊓ X = ⊥ := by
  have hdvd : Nat.card ↥(Z ⊓ X) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ X ≤ Z)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact Subgroup.card_eq_one.1 h1
  · have heq : Z ⊓ X = Z := Subgroup.eq_of_le_of_card_ge (inf_le_left : Z ⊓ X ≤ Z)
      (by rw [h2, hZ])
    exact (h (heq ▸ (inf_le_right : Z ⊓ X ≤ X))).elim

theorem le_of_mem_of_card_two {Z X : Subgroup G} (hZ : Nat.card Z = 2) {x : G} (hx : x ∈ Z)
    (hx1 : x ≠ 1) (hxX : x ∈ X) : Z ≤ X := by
  by_contra h
  have := inf_eq_bot_of_card_two hZ h
  have hm : x ∈ Z ⊓ X := ⟨hx, hxX⟩
  rw [this] at hm
  exact hx1 (Subgroup.mem_bot.1 hm)

theorem mul_mem_four {Z : Subgroup G} (hZ : Nat.card Z = 4) {a b c : G} (ha : a ∈ Z)
    (hb : b ∈ Z) (hc : c ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : a * b = 1 ∨ a * b = a ∨ a * b = b ∨ a * b = c := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hnd : [1, a, b, c, a * b].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hc1, Ne.symm h1⟩, ⟨hab, hac, Ne.symm h2⟩,
      ⟨hbc, Ne.symm h3⟩, Ne.symm h4, not_false, List.nodup_nil⟩
  have hcard : ([1, a, b, c, a * b].toFinset).card = 5 := by
    rw [List.toFinset_card_of_nodup hnd]; rfl
  have hsub : ([1, a, b, c, a * b].toFinset : Set G) ⊆ (Z : Set G) := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact ha
    · exact hb
    · exact hc
    · exact Z.mul_mem ha hb
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  have : Nat.card (Z : Set G) = Nat.card Z := rfl
  omega

theorem comm_swap (hS : Sit H M S) {m α' γ' : Geo H M} (hm : vtype m = true) (hα : α' ∈ nbrs m)
    (hγ : γ' ∈ nbrs m) (hne : α' ≠ γ') {w : G} (hwm : w ∈ stab m) (hwγ : w ∈ stab γ')
    (hwα : w ∉ stab α') {z : G} (hz : z ∈ Zv α') (hz1 : z ≠ 1) :
    ⁅z, w⁆ ∈ Zv γ' ∧ ⁅z, w⁆ ≠ 1 := by
  classical
  obtain ⟨ε, hε, hεα, hεγ, hall⟩ := S35.Std.nbrs_S3_third hS hm hα hγ hne
  set g : ↥(H ⊔ M) := ⟨w, stab_le m hwm⟩ with hg
  have hgα : g • α' ∈ nbrs m := S35.Std.smul_mem_nbrs_of_stab (g := g) hwm hα
  have h1 : g • α' ≠ α' := fun h => hwα (mem_stab_of_smul_eq h)
  have hgγ : g • γ' = γ' := smul_eq_of_mem_stab hwγ
  have h2 : g • α' ≠ γ' := fun h => hne (MulAction.injective g (h.trans hgγ.symm))
  have hgε : g • α' = ε := by
    rcases hall _ hgα with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  have hZε : Zv ε = conjSub w (Zv α') := by
    rw [← hgε, Zv_smul]
  have hα5 : vtype α' = false := S35.Std.vtype_nbr_S3 hm hα
  have hγ5 : vtype γ' = false := S35.Std.vtype_nbr_S3 hm hγ
  have hε5 : vtype ε = false := S35.Std.vtype_nbr_S3 hm hε
  have hZα : Zv α' ≤ Zv m := S35.Std.Zv_le_Zv_of_nbr hS hα5 (S35.Std.mem_nbrs_symm.1 hα)
  have hZγ : Zv γ' ≤ Zv m := S35.Std.Zv_le_Zv_of_nbr hS hγ5 (S35.Std.mem_nbrs_symm.1 hγ)
  have hZε' : Zv ε ≤ Zv m := S35.Std.Zv_le_Zv_of_nbr hS hε5 (S35.Std.mem_nbrs_symm.1 hε)
  have hαγ := (S35.Std.Zv_ne hS hm hα hγ hne).2.2
  have hαε := (S35.Std.Zv_ne hS hm hα hε (Ne.symm hεα)).2.2
  have hγε := (S35.Std.Zv_ne hS hm hγ hε (Ne.symm hεγ)).2.2
  have hcγ : Nat.card (Zv γ') = 2 := hS.cardZ5 γ' hγ5
  have hc4 : Nat.card (Zv m) = 4 := hS.cardZ3 m hm
  have hinf : ∀ {A B : Subgroup G} {x : G}, A ⊓ B = ⊥ → x ∈ A → x ∈ B → x = 1 := by
    intro A B x hAB hxA hxB
    have : x ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [hAB] at this
    exact Subgroup.mem_bot.1 this
  obtain ⟨b, hbγ, hb1⟩ : ∃ b ∈ Zv γ', b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Zv γ' = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hcγ
    omega
  set c : G := w * z⁻¹ * w⁻¹ with hc
  have hcε : c ∈ Zv ε := by
    rw [hZε]
    exact conj_mem_conjSub_iff.2 (Subgroup.inv_mem _ hz)
  have hc1 : c ≠ 1 := by
    intro h
    apply hz1
    calc z = (w⁻¹ * (w * z⁻¹ * w⁻¹) * w)⁻¹ := by group
      _ = 1 := by rw [show w * z⁻¹ * w⁻¹ = 1 from h]; group
  have hzc : z ≠ c := fun h => hz1 (hinf hαε hz (h ▸ hcε))
  have hzb : z ≠ b := fun h => hz1 (hinf hαγ hz (h ▸ hbγ))
  have hcb : c ≠ b := fun h => hc1 (hinf (by rw [inf_comm]; exact hγε) hcε (h ▸ hbγ))
  have hcomm : ⁅z, w⁆ = z * c := by
    rw [commutatorElement_def, hc]; group
  have hzcm : z * c ∈ Zv m := Subgroup.mul_mem _ (hZα hz) (hZε' hcε)
  have hzcb : z * c = b := by
    rcases mul_mem_four hc4 (hZα hz) (hZε' hcε) (hZγ hbγ) hz1 hc1 hb1 hzc hzb hcb with
      h | h | h | h
    · have hcz : c = z⁻¹ := eq_inv_of_mul_eq_one_right h
      exact absurd (hinf hαε (hcz ▸ (Zv α').inv_mem hz) hcε) hc1
    · exact absurd (mul_eq_left.1 h) hc1
    · exact absurd (mul_eq_right.1 h) hz1
    · exact h
  refine ⟨hcomm ▸ hzcb ▸ hbγ, ?_⟩
  rw [hcomm, hzcb]
  exact hb1

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
