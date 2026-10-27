module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.CharacteristicSimplePower

universe u v

private theorem exists_normal_minimal_card
    {G : Type u} [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → Nat.card N ≤ Nat.card M := by
  let _ : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hne : {N : Subgroup G | N.Normal ∧ N ≠ ⊥}.Nonempty :=
    ⟨⊤, inferInstance, top_ne_bot⟩
  obtain ⟨N, ⟨hN, hN0⟩, hmin⟩ := Set.Finite.exists_minimalFor
    (fun N : Subgroup G => Nat.card N) _ (Set.toFinite _) hne
  refine ⟨N, hN, hN0, fun M hM hM0 => ?_⟩
  rcases le_total (Nat.card N) (Nat.card M) with h | h
  · exact h
  · exact hmin ⟨hM, hM0⟩ h

theorem card_lt_card_of_lt
    {G : Type u} [Group G] [Finite G] {K L : Subgroup G} (h : K < L) :
    Nat.card K < Nat.card L := by
  apply Nat.lt_of_not_ge
  intro hcard
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hcard)

private theorem sSupIndep_insert_of_disjoint
    {G : Type u} [Group G] {s : Set (Subgroup G)} {M : Subgroup G}
    (hM : M.Normal) (hs : sSupIndep s) (hd : Disjoint M (sSup s)) :
    sSupIndep (insert M s) := by
  by_cases hMs : M ∈ s
  · rwa [Set.insert_eq_self.2 hMs]
  intro a ha
  rcases ha with rfl | ha
  · have h1 : insert a s \ {a} = s := by simp [Set.sdiff_singleton_eq_self hMs]
    rw [h1]
    exact hd
  · have hne : a ≠ M := fun h => hMs (h ▸ ha)
    have hdiff : insert M s \ {a} = insert M (s \ {a}) := by
      rw [Set.insert_sdiff_of_notMem _ (by simpa using hne.symm)]
    rw [hdiff, sSup_insert]
    have hK : sSup (s \ {a}) ≤ sSup s := sSup_le_sSup Set.sdiff_subset
    have haS : a ≤ sSup s := le_sSup ha
    have hda : Disjoint a (sSup (s \ {a})) := hs ha
    rw [Subgroup.disjoint_def]
    intro x hxa hx
    have := hM
    obtain ⟨m, hm, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    have hmS : m ∈ sSup s := by
      have hmk : m = m * k * k⁻¹ := by group
      rw [hmk]
      exact mul_mem (haS hxa) (inv_mem (hK hk))
    have hm1 : m = 1 := Subgroup.disjoint_def.1 hd hm hmS
    subst hm1
    simp only [one_mul] at hxa ⊢
    exact Subgroup.disjoint_def.1 hda hxa hk

theorem le_centralizer_of_normal_of_disjoint
    {G : Type u} [Group G] {K L : Subgroup G}
    (hK : K.Normal) (hL : L.Normal) (h : Disjoint K L) :
    L ≤ Subgroup.centralizer (K : Set G) :=
  fun _ hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
    (Subgroup.commute_of_normal_of_disjoint K L hK hL h x _ hx hy).eq

private theorem normal_map_subtype_of_sup_centralizer_eq_top
    {G : Type u} [Group G] {K : Subgroup G}
    (hK : K.Normal) (hsup : K ⊔ Subgroup.centralizer (K : Set G) = ⊤)
    (M : Subgroup K) [M.Normal] : (M.map K.subtype).Normal := by
  have := hK
  constructor
  rintro x ⟨y, hy, rfl⟩ g
  obtain ⟨k, hk, c, hc, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top g : g ∈ K ⊔ _)
  rw [Subgroup.mem_centralizer_iff] at hc
  have hyc : c * (y : G) = (y : G) * c := (hc _ y.property).symm
  refine ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, ‹M.Normal›.conj_mem y hy ⟨k, hk⟩, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_rev]
  calc k * (y : G) * k⁻¹ = k * (c * (y : G) * c⁻¹) * k⁻¹ := by rw [hyc]; group
       _ = k * c * (y : G) * (c⁻¹ * k⁻¹) := by group

theorem nonempty_mulEquivPi
    {G : Type u} [Group G] {ι : Type v} {H : ι → Subgroup G} [Fintype ι]
    (hnorm : ∀ i, (H i).Normal) (hind : iSupIndep H) (hsup : ⨆ i, H i = ⊤) :
    Nonempty (G ≃* ((i : ι) → H i)) := by
  refine ⟨?_⟩
  have hcomm : Pairwise fun i j : ι =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij
    exact Subgroup.commute_of_normal_of_disjoint (H i) (H j)
      (hnorm i) (hnorm j) (hind.pairwiseDisjoint hij)
  apply MulEquiv.symm
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  refine ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hind, ?_⟩
  apply MonoidHom.range_eq_top.mp
  exact Subgroup.noncommPiCoprod_range.trans hsup

theorem exists_sSupIndep_isSimpleGroup
    {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hchar : ∀ H : Subgroup G, H.Characteristic → H = ⊥ ∨ H = ⊤) :
    ∃ (s : Set (Subgroup G)) (N : Subgroup G), N ∈ s ∧ IsSimpleGroup N ∧
      (∀ K ∈ s, K.Normal) ∧ (∀ K ∈ s, Nonempty (K ≃* N)) ∧
      sSupIndep s ∧ sSup s = ⊤ := by
  classical
  let _ : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨N, hN, hN0, hmin⟩ := exists_normal_minimal_card (G := G)
  have := hN
  set P : Set (Subgroup G) → Prop := fun s =>
    N ∈ s ∧ (∀ K ∈ s, K.Normal) ∧ (∀ K ∈ s, Nonempty (K ≃* N)) ∧ sSupIndep s
  have hPne : {s | P s}.Nonempty :=
    ⟨{N}, rfl, fun K hK => hK ▸ hN,
      fun K hK => ⟨hK ▸ MulEquiv.refl _⟩, sSupIndep_singleton N⟩
  obtain ⟨s, hs, hmax⟩ := Set.Finite.exists_maximalFor
    (fun s : Set (Subgroup G) => Nat.card (sSup s : Subgroup G)) {s | P s}
      (Set.toFinite _) hPne
  obtain ⟨hNs, hnorm, hiso, hind⟩ := hs
  set H := sSup s with hH
  have hNH : N ≤ H := le_sSup hNs
  have hHnorm : H.Normal := Subgroup.sSup_normal s hnorm
  have hkey : ∀ φ : G ≃* G, Subgroup.map (φ : G →* G) H ≤ H := by
    intro φ
    rw [hH, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => Subgroup.map_le_iff_le_comap.1 ?_
    set Kφ := Subgroup.map (φ : G →* G) K
    by_contra hnle
    have hKφnorm : Kφ.Normal := (hnorm K hK).map _ φ.surjective
    have hKφiso : Nonempty (Kφ ≃* N) :=
      ⟨(K.equivMapOfInjective (φ : G →* G) φ.injective).symm.trans (hiso K hK).some⟩
    have hKφcard : Nat.card Kφ = Nat.card N := Nat.card_congr hKφiso.some.toEquiv
    have hdisj : Disjoint Kφ H := by
      have := hKφnorm
      have hlt : Kφ ⊓ H < Kφ := lt_of_le_of_ne inf_le_left fun he => hnle (he ▸ inf_le_right)
      have hDcard : Nat.card (Kφ ⊓ H : Subgroup G) < Nat.card N :=
        hKφcard ▸ card_lt_card_of_lt hlt
      rw [disjoint_iff]
      by_contra h0
      exact absurd (hmin _ (Subgroup.normal_inf_normal Kφ H) h0) (not_le.2 hDcard)
    have hP' : P (insert Kφ s) := by
      refine ⟨Set.mem_insert_of_mem _ hNs, ?_, ?_, sSupIndep_insert_of_disjoint hKφnorm hind hdisj⟩
      · rintro L (rfl | hL)
        · exact hKφnorm
        · exact hnorm L hL
      · rintro L (rfl | hL)
        · exact hKφiso
        · exact hiso L hL
    have hltH : H < Kφ ⊔ H :=
      lt_of_le_of_ne le_sup_right fun he => hnle (le_sup_left.trans he.symm.le)
    have hsup' : sSup (insert Kφ s) = Kφ ⊔ H := sSup_insert
    have hle := hmax hP' (by simp only [hsup']; exact (card_lt_card_of_lt hltH).le)
    simp only [hsup'] at hle
    exact absurd hle (not_le.2 (card_lt_card_of_lt hltH))
  have hHtop : H = ⊤ := by
    rcases hchar H (Subgroup.characteristic_iff_map_le.2 hkey) with h | h
    · exact absurd (le_bot_iff.1 (h ▸ hNH)) hN0
    · exact h
  have hcent : N ⊔ Subgroup.centralizer (N : Set G) = ⊤ := by
    have hrest : sSup (s \ {N}) ≤ Subgroup.centralizer (N : Set G) :=
      le_centralizer_of_normal_of_disjoint hN
        (Subgroup.sSup_normal _ fun K hK => hnorm K hK.1) (hind hNs)
    have hall : N ⊔ sSup (s \ {N}) = ⊤ := by
      rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_self.2 hNs, ← hH, hHtop]
    exact top_le_iff.1 (hall.ge.trans (sup_le_sup_left hrest N))
  have hNsimple : IsSimpleGroup N := by
    have : Nontrivial N := N.nontrivial_iff_ne_bot.2 hN0
    refine ⟨fun {M} hM => ?_⟩
    have := hM
    by_cases h0 : M = ⊥
    · exact Or.inl h0
    refine Or.inr ?_
    have h1 := hmin _ (normal_map_subtype_of_sup_centralizer_eq_top hN hcent M) (by
      rw [Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]; exact h0)
    rw [Subgroup.card_subtype] at h1
    exact Subgroup.eq_of_le_of_card_ge le_top (by rwa [Subgroup.card_top])
  exact ⟨s, N, hNs, hNsimple, hnorm, hiso, hind, by rw [← hH, hHtop]⟩

end FiveTransitive.CharacteristicSimplePower

end CFSG
