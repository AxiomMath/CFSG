module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearTorusReflection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCentralizers

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {G : Type u} [Group G] [Finite G]

theorem reference_torus_matches_partition
    (P A B T : Subgroup G) (hP : IsPGroup 2 P) [IsCyclic T]
    (hTcard : Nat.card T = Nat.card A) (hAodd : Odd (Nat.card A))
    (hAcard : 1 < Nat.card A) (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (hcover : ∀ x : G, x ≠ 1 → ∃ V : Subgroup G, x ∈ V ∧
      ((∃ g : G, V = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g : G, V = A.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g : G, V = B.map (MulAut.conj g).toMonoidHom))) :
    ∃ g : G, T = A.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := T)
  have htorder : orderOf (t : G) = Nat.card A := by
    exact (Subgroup.orderOf_coe t).trans
      ((orderOf_eq_card_of_forall_mem_zpowers ht).trans hTcard)
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htorder
    omega
  obtain ⟨V, htV, hV⟩ := hcover t htne
  have hTV : T ≤ V := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ht ⟨x, hx⟩)
    have hpow : (t : G) ^ n = x := by
      simpa only [SubgroupClass.coe_zpow] using congrArg Subtype.val hn
    rw [← hpow]
    exact V.zpow_mem htV n
  have horderV : Nat.card A ∣ Nat.card V := by
    have hd := orderOf_dvd_natCard (⟨(t : G), htV⟩ : V)
    have hvorder : orderOf (⟨(t : G), htV⟩ : V) = Nat.card A :=
      (Subgroup.orderOf_coe (⟨(t : G), htV⟩ : V)).symm.trans htorder
    exact hvorder ▸ hd
  rcases hV with hPV | hAV | hBV
  · obtain ⟨g, rfl⟩ := hPV
    have hVP := hP.map (MulAut.conj g).toMonoidHom
    have hcoporder := hVP.orderOf_coprime hAodd.coprime_two_left
      (⟨(t : G), htV⟩ : P.map (MulAut.conj g).toMonoidHom)
    have hone : Nat.card A = 1 := by
      have hcopself : Nat.Coprime (Nat.card A) (Nat.card A) := by
        have hvorder : orderOf
            (⟨(t : G), htV⟩ : P.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
          (Subgroup.orderOf_coe
            (⟨(t : G), htV⟩ : P.map (MulAut.conj g).toMonoidHom)).symm.trans htorder
        exact hvorder ▸ hcoporder
      exact Nat.eq_one_of_dvd_coprimes hcopself dvd_rfl dvd_rfl
    omega
  · obtain ⟨g, rfl⟩ := hAV
    refine ⟨g, Subgroup.eq_of_le_of_card_ge hTV ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hTcard]
  · obtain ⟨g, rfl⟩ := hBV
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at horderV
    have hone := hcop.eq_one_of_dvd horderV
    omega

omit [Finite G] in
theorem conjugate_reflection_torus_odd_centralizer
    (T : Subgroup G) [IsCyclic T] (w : G)
    (hw : w ∈ Subgroup.normalizer (T : Set G)) (hwsq : w * w = 1)
    (hinv : ∀ y : G, y ∈ T → w * y * w⁻¹ = y⁻¹)
    (hnormalizer : ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w)
    (e : G ≃* G) (x : G) (hxT : x ∈ T.map e.toMonoidHom)
    (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    IsCyclic (Subgroup.centralizer ({x} : Set G)) ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card T ∧
        ∀ u : G, u * x * u⁻¹ = x⁻¹ →
          ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
            u * y * u⁻¹ = y⁻¹ := by
  have hx0T : e.symm x ∈ T := Subgroup.mem_map_equiv.mp hxT
  have hx0ne : e.symm x ≠ 1 := fun h => hx (by
    simpa only [e.apply_symm_apply, e.map_one] using congrArg e h)
  have hx0odd : Odd (orderOf (e.symm x)) := by
    exact (orderOf_injective e.symm.toMonoidHom e.symm.injective x).symm ▸ hxodd
  have hRne : Subgroup.zpowers (e.symm x) ≠ ⊥ := by
    intro h
    exact hx0ne (Subgroup.zpowers_eq_bot.mp h)
  obtain ⟨hC0, hwholeinv⟩ := odd_element_centralizer_eq_reflection_torus T w
    (e.symm x) hw hwsq hinv hx0T hx0ne hx0odd
      (hnormalizer _ (Subgroup.zpowers_le_of_mem hx0T) hRne)
  have hcyclic0 : IsCyclic (Subgroup.centralizer ({e.symm x} : Set G)) := by
    rw [hC0]
    infer_instance
  have hcyclic : IsCyclic (Subgroup.centralizer ({x} : Set G)) := by
    have h := (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.elementCentralizerEquiv
      e (e.symm x)).isCyclic.mp hcyclic0
    rw [e.apply_symm_apply x] at h
    exact h
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card T := by
    have h := Nat.card_congr
      (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.elementCentralizerEquiv
        e (e.symm x)).toEquiv
    simpa only [e.apply_symm_apply, hC0] using h.symm
  refine ⟨hcyclic, hcard, ?_⟩
  intro u hux y hy
  have hux0 : e.symm u * e.symm x * (e.symm u)⁻¹ = (e.symm x)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg e.symm hux
  have hy0 : e.symm y ∈ Subgroup.centralizer ({e.symm x} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg e.symm
      (Subgroup.mem_centralizer_singleton_iff.mp hy)
  apply e.symm.injective
  simpa only [map_mul, map_inv] using hwholeinv (e.symm u) hux0 (e.symm y) hy0

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
