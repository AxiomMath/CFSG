module

public import CFSG.Quasithin.SteinbergCBSevenPoints
public import CFSG.Quasithin.SteinbergCBAlternatingFive

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

@[expose] def sevenAltFixTwo : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7) ⊓
    MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7)

theorem mem_sevenAltFixTwo {g : Perm (Fin 7)} :
    g ∈ sevenAltFixTwo ↔ sign g = 1 ∧ g 0 = 0 ∧ g 1 = 1 := by
  rw [sevenAltFixTwo, Subgroup.mem_inf, Subgroup.mem_inf, mem_alternatingGroup,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Perm.smul_def, Perm.smul_def,
    and_assoc]

theorem card_filter_sevenAltFixTwo : (Finset.univ.filter fun g : Perm (Fin 7) =>
    sign g = 1 ∧ g 0 = 0 ∧ g 1 = 1).card = 60 := by
  decide +kernel

theorem nat_card_sevenAltFixTwo : Nat.card sevenAltFixTwo = 60 := by
  rw [← card_filter_sevenAltFixTwo, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_sevenAltFixTwo)

theorem invariant_finset_seven : ∀ M : Finset (Fin 7),
    (∀ x, x ∈ M ↔ (swap 0 1 : Perm (Fin 7)) x ∈ M) →
    (∀ x, x ∈ M ↔ (swap 2 3 : Perm (Fin 7)) x ∈ M) →
    (∀ x, x ∈ M ↔ (swap 4 5 : Perm (Fin 7)) x ∈ M) →
    (∀ x, x ∈ M ↔ (swap 2 4 * swap 3 5 : Perm (Fin 7)) x ∈ M) →
    (M.card = 5 ∨ M.card = 6) → M = {2, 3, 4, 5, 6} ∨ M = {0, 1, 2, 3, 4, 5} := by
  decide +kernel

theorem nat_card_sevenP : Nat.card sevenP = 16 := by
  rw [← sevenA_inf_sevenB, ← card_filter_sevenCond, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_inf, mem_sevenA, mem_sevenB, sevenCond]

theorem sevenP_fix_six {p : Perm (Fin 7)} (hp : p ∈ sevenP) : p 6 = 6 := by
  rw [← sevenA_inf_sevenB] at hp
  exact (mem_sevenB.1 (Subgroup.mem_inf.1 hp).2).1

theorem card_support_of_orderOf_eq_five {g : Perm (Fin 7)} (hg : orderOf g = 5) :
    g.support.card = 5 := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (hg ▸ (by norm_num : Nat.Prime 5))
  rw [hg] at hn
  have hsum := sum_cycleType g
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : g.support.card ≤ 7 := (Finset.card_le_univ _).trans (Fintype.card_fin 7).le
  omega

theorem nat_card_mulAut_alternating_five : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective (conjPerm 5)
    ⟨conjPerm_injective (by norm_num), conjPerm_surjective (Or.inl rfl)⟩), Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem A7_Sylow_normalized_A5_fixes_two_coordinates {A : Subgroup (Perm (Fin 7))}
    (hA7 : A ≤ alternatingGroup (Fin 7)) (hA5 : Nonempty (A ≃* alternatingGroup (Fin 5)))
    (hP : sevenP ≤ normalizer (A : Set (Perm (Fin 7)))) : A = sevenAltFixTwo := by
  classical
  obtain ⟨e⟩ := hA5
  have hcardA : Nat.card A = 60 := by rw [Nat.card_congr e.toEquiv, nat_card_alternating_five]
  have : IsSimpleGroup A := e.isSimpleGroup
  have hidx : ∀ H : Subgroup A, H ≠ ⊤ → 5 ≤ H.index := by
    intro H hH
    have hcore : H.normalCore = ⊥ := by
      have := H.normalCore_normal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
      · exact h
      · exact absurd (top_le_iff.1 (h ▸ H.normalCore_le)) hH
    have h1 := Subgroup.index_normalCore_le_factorial_index H
    rw [hcore, Subgroup.index_bot, hcardA] at h1
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k, H.index = k := ⟨_, rfl⟩
    rw [hk] at h1 hlt
    interval_cases k <;> simp [Nat.factorial] at h1
  set Mset : Set (Fin 7) := {x | ∃ a ∈ A, a x ≠ x} with hMset
  have hmoved : ∀ x, x ∈ Mset ↔ MulAction.stabilizer A x ≠ ⊤ := by
    intro x
    constructor
    · rintro ⟨a, ha, hax⟩ h
      exact hax (by
        have := (h ▸ Subgroup.mem_top (⟨a, ha⟩ : A) : (⟨a, ha⟩ : A) ∈ MulAction.stabilizer A x)
        exact this)
    · intro h
      by_contra hx
      apply h
      rw [eq_top_iff]
      rintro ⟨a, ha⟩ -
      rw [MulAction.mem_stabilizer_iff]
      by_contra hne
      exact hx ⟨a, ha, hne⟩
  have horb : ∀ x ∈ Mset, 5 ≤ (MulAction.orbit A x).ncard := fun x hx => by
    rw [← MulAction.index_stabilizer]
    exact hidx _ ((hmoved x).1 hx)
  have horbM : ∀ x ∈ Mset, MulAction.orbit A x ⊆ Mset := by
    rintro x hx _ ⟨⟨a, ha⟩, rfl⟩
    by_contra hy
    obtain ⟨b, hb, hbx⟩ := hx
    apply hy
    refine ⟨a * b * a⁻¹, A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha), fun h => hbx ?_⟩
    change (a * b * a⁻¹) (a x) = a x at h
    simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply] at h
    exact a.injective h
  have hncard_univ : (Set.univ : Set (Fin 7)).ncard = 7 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∈ Mset := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      refine Equiv.Perm.ext fun y => ?_
      by_contra hne
      exact h y ⟨a, ha, hne⟩
    rw [hbot, Subgroup.card_bot] at hcardA
    omega
  have hMO : ∀ x ∈ Mset, Mset = MulAction.orbit A x := by
    intro x hx
    refine le_antisymm (fun y hy => ?_) (horbM x hx)
    by_contra hyO
    have hdisj : Disjoint (MulAction.orbit A x) (MulAction.orbit A y) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      apply hyO
      have h1 : MulAction.orbit A z = MulAction.orbit A x := MulAction.orbit_eq_iff.2 hz1
      have h2 : MulAction.orbit A z = MulAction.orbit A y := MulAction.orbit_eq_iff.2 hz2
      rw [← h1, h2]
      exact MulAction.mem_orbit_self y
    have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have h2 : (MulAction.orbit A x ∪ MulAction.orbit A y).ncard ≤ 7 :=
      (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans hncard_univ.le
    have := horb x hx
    have := horb y hy
    omega
  have hMcard : Mset.ncard = 5 ∨ Mset.ncard = 6 := by
    have h1 : Mset.ncard = (MulAction.stabilizer A x₀).index := by
      rw [hMO x₀ hx₀, MulAction.index_stabilizer]
    have h2 : Mset.ncard ∣ 60 := h1 ▸ hcardA ▸ Subgroup.index_dvd_card _
    have h3 : Mset.ncard ≤ 7 :=
      (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans hncard_univ.le
    have h4 : 5 ≤ Mset.ncard := by
      rw [hMO x₀ hx₀]
      exact horb x₀ hx₀
    obtain ⟨k, hk⟩ : ∃ k, Mset.ncard = k := ⟨_, rfl⟩
    rw [hk] at h2 h3 h4 ⊢
    interval_cases k
    · left; rfl
    · right; rfl
    · norm_num at h2
  have hinvM : ∀ p ∈ sevenP, ∀ x, x ∈ Mset ↔ p x ∈ Mset := by
    have key : ∀ p ∈ sevenP, ∀ x, x ∈ Mset → p x ∈ Mset := by
      rintro p hp x ⟨a, ha, hax⟩
      refine ⟨p * a * p⁻¹, (mem_normalizer_iff.1 (hP hp) a).1 ha, fun h => hax ?_⟩
      change (p * a * p⁻¹) (p x) = p x at h
      simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply] at h
      exact p.injective h
    intro p hp x
    refine ⟨key p hp x, fun h => ?_⟩
    have := key p⁻¹ (sevenP.inv_mem hp) (p x) h
    simpa [Perm.inv_def] using this
  set Mfin : Finset (Fin 7) := Mset.toFinset with hMfin
  have hmemfin : ∀ x, x ∈ Mfin ↔ x ∈ Mset := fun x => Set.mem_toFinset
  have hgen : ∀ q ∈ ({swap 0 1, swap 2 3, swap 4 5, swap 2 4 * swap 3 5} : Set (Perm (Fin 7))),
      ∀ x, x ∈ Mfin ↔ q x ∈ Mfin := fun q hq x => by
    rw [hmemfin, hmemfin]
    exact hinvM q (subset_closure hq) x
  have hcases := invariant_finset_seven Mfin (hgen _ (by simp)) (hgen _ (by simp))
    (hgen _ (by simp)) (hgen _ (by simp))
    (by rw [hMfin, ← Set.ncard_eq_toFinset_card']; exact hMcard)
  rcases hcases with hM1 | hM2
  ·
    have hfix : ∀ a ∈ A, a 0 = 0 ∧ a 1 = 1 := by
      intro a ha
      have h0 : (0 : Fin 7) ∉ Mset := fun h => by
        have := (hmemfin 0).2 h
        rw [hM1] at this
        simp at this
      have h1 : (1 : Fin 7) ∉ Mset := fun h => by
        have := (hmemfin 1).2 h
        rw [hM1] at this
        simp at this
      refine ⟨?_, ?_⟩
      · by_contra hne
        exact h0 ⟨a, ha, hne⟩
      · by_contra hne
        exact h1 ⟨a, ha, hne⟩
    have hle : A ≤ sevenAltFixTwo := fun a ha => mem_sevenAltFixTwo.2
      ⟨mem_alternatingGroup.1 (hA7 ha), (hfix a ha).1, (hfix a ha).2⟩
    exact eq_of_le_of_card_ge hle (by rw [hcardA, nat_card_sevenAltFixTwo])
  ·
    exfalso
    have h6 : ∀ a ∈ A, a 6 = 6 := by
      intro a ha
      by_contra hne
      have := (hmemfin 6).2 ⟨a, ha, hne⟩
      rw [hM2] at this
      simp at this
    have hfive : ∀ x : Fin 7, x ≠ 6 → ∃ g ∈ A, g x = x ∧ ∀ z, z ≠ x → z ≠ 6 → g z ≠ z := by
      intro x hx6
      have hxM : x ∈ Mset := by
        rw [← hmemfin, hM2]
        revert hx6
        revert x
        decide
      have hidx6 : (MulAction.stabilizer A x).index = 6 := by
        rw [MulAction.index_stabilizer, ← hMO x hxM]
        have := hMcard
        have h' : Mset.ncard = Mfin.card := by
          rw [hMfin, Set.ncard_eq_toFinset_card']
        rw [h', hM2]
        rfl
      have hcard10 : Nat.card (MulAction.stabilizer A x) = 10 := by
        have h := card_mul_index (MulAction.stabilizer A x)
        rw [hidx6, hcardA] at h
        omega
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨⟨⟨g, hgA⟩, hgx⟩, hg5⟩ :=
        exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer A x) 5
          (by rw [hcard10]; norm_num)
      have hgx' : g x = x := hgx
      have hord : orderOf g = 5 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hg5
        exact hg5
      have hsupp := card_support_of_orderOf_eq_five hord
      have hsub : g.support ⊆ Finset.univ \ {x, 6} := by
        intro z hz
        rw [mem_support] at hz
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and, not_or]
        exact ⟨fun h => hz (h ▸ hgx'), fun h => hz (h ▸ h6 g hgA)⟩
      have hcard5 : (Finset.univ \ {x, 6} : Finset (Fin 7)).card = 5 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair hx6]
      have heq : g.support = Finset.univ \ {x, 6} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hsupp, hcard5])
      refine ⟨g, hgA, hgx', fun z hzx hz6 => ?_⟩
      rw [← mem_support, heq]
      simp [hzx, hz6]
    have hcent : ∀ c ∈ sevenP, (∀ a ∈ A, c * a = a * c) → c = 1 := by
      intro c hc hca
      have hc6 := sevenP_fix_six hc
      refine Equiv.Perm.ext fun x => ?_
      by_cases hx6 : x = 6
      · rw [hx6, hc6]
        rfl
      obtain ⟨g, hgA, hgx, hgz⟩ := hfive x hx6
      have hcx : g (c x) = c x := by
        have := congrArg (· x) (hca g hgA)
        simp only [Perm.mul_apply, hgx] at this
        exact this.symm
      by_contra hne
      have hcx6 : c x ≠ 6 := fun h => hx6 (c.injective (h.trans hc6.symm))
      exact hgz (c x) hne hcx6 hcx
    set N := normalizer (A : Set (Perm (Fin 7))) with hN
    set A' := A.subgroupOf N with hA'
    have hA'n : A'.Normal := Subgroup.normal_in_normalizer
    let φ : sevenP →* MulAut A' := (MulAut.conjNormal (H := A')).comp (Subgroup.inclusion hP)
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨c, hc⟩ h1
      refine Subtype.ext (hcent c hc fun a ha => ?_)
      have haN : a ∈ N := le_normalizer ha
      have h2 := congrArg (fun f : MulAut A' => (((f ⟨⟨a, haN⟩, ha⟩ : A') : N) :
        Perm (Fin 7))) h1
      simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h2
      have h3 : c * a * c⁻¹ = a := by
        simpa using h2
      calc c * a = c * a * c⁻¹ * c := by group
        _ = a * c := by rw [h3]
    have hdvd := Subgroup.card_dvd_of_injective φ hφinj
    rw [nat_card_sevenP, Nat.card_congr (MulAut.congr ((subgroupOfEquivOfLe
      (le_normalizer (H := A))).trans e)).toEquiv, nat_card_mulAut_alternating_five] at hdvd
    norm_num at hdvd

end CFSG.Quasithin.SteinbergCB
