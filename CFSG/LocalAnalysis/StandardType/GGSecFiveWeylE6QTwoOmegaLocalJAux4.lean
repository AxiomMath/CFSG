module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCPrimary

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

theorem center_le_centralizer_Bs_of_innerAction {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hperf : commutator ↥L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    (Subgroup.center L).map (Subgroup.subtype L) ≤ Subgroup.centralizer (Bs : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  let b' : ↥Bs := ⟨b, hb⟩
  obtain ⟨φ, hφmem, hφ⟩ := hI b hb
  rw [LargeEvenInnSet] at hφmem
  obtain ⟨r, rfl⟩ := hφmem
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ↥L,
      θ (QuotientGroup.mk' (Subgroup.center L) l₀) = r := by
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    exact ⟨l₀, hq⟩
  have hcongr : (MulAut.congr θ)
      (e6QTwoQuotCenterAutHom ↥L (e6QTwoBstarConjAction hBsN b'⁻¹)) =
        MulAut.conj r := by
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [e6QTwoQuotCenterAutHom_mk]
    have h := hφ l (e6QTwoBstarConjAction hBsN b'⁻¹ l) (by
      simpa using e6QTwoBstarConjAction_apply hBsN b'⁻¹ l)
    simpa using h.symm
  have hconj : (MulAut.congr θ)
      (e6QTwoQuotCenterAutHom ↥L (MulAut.conj l₀)) = MulAut.conj r := by
    rw [e6QTwoQuotCenterAutHom_conj]
    have h1 : (MulAut.congr θ)
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥L) l₀)) =
          MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center ↥L) l₀)) := by
      ext x
      simp [MulAut.congr, MulAut.conj_apply]
    rw [h1, hl₀]
  have hinner : e6QTwoBstarConjAction hBsN b'⁻¹ = MulAut.conj l₀ := by
    apply e6QTwoQuotCenterAutHom_injective (L' := ↥L) hperf
    apply (MulAut.congr θ).injective
    rw [hcongr, hconj]
  have hzfix : e6QTwoBstarConjAction hBsN b'⁻¹ z = z := by
    rw [hinner]
    show l₀ * z * l₀⁻¹ = z
    have hcomm : (l₀ : ↥L) * z = z * l₀ :=
      Subgroup.mem_center_iff.mp hz l₀
    calc l₀ * z * l₀⁻¹ = z * l₀ * l₀⁻¹ := by rw [hcomm]
      _ = z := by simp
  have hb : b⁻¹ * (z : G) * b = (z : G) := by
    have h := e6QTwoBstarConjAction_apply hBsN b'⁻¹ z
    rw [hzfix] at h
    simpa using h.symm
  have h2 : b * z * b⁻¹ = z := by
    calc b * z * b⁻¹ = b * (b⁻¹ * z * b) * b⁻¹ := by rw [hb]
      _ = z := by group
  calc b * z = b * z * b⁻¹ * b := by group
    _ = z * b := by rw [h2]


open Polynomial Module

theorem exists_pow_mem_specialBlock_of_fixedSpace_eq_zero
    (hK : Nat.card K = 2)
    {n x' : ↥(CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4))}
    (hx3 : orderOf x' = 3) (hn : Commute n x')
    (h0 : Module.finrank K
      (fixedSpace (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 0) :
    ∃ j : ℕ, (n * (x' ^ j)⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived
        (TableBOrth.qPlusForm K 4))) ∈
      (specialBlock (TableBOrth.qPlusForm K 4)
        (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (X ^ 2 + X + 1)).subgroupOf
        (CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4)) := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  let Q : QuadraticForm K (Fin 4 ⊕ Fin 4 → K) := TableBOrth.qPlusForm K 4
  let xV : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := x'
  have hQ : Q.polarBilin.Nondegenerate := TableBOrth.nondegenerate_qPlusForm (K := K) 4
  have hdim : finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by simp
  have hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even 4 := by
    constructor
    · intro _; norm_num
    · intro _; simpa [Q, TableBOrth.qPlusForm] using
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 4)
  obtain ⟨hx, hpq, hmem, s, hs, hsm, htype⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.dims_of_orderOf_three (Or.inl hK) hQ hdim hV
      x' hx3
  have hmem' : (X ^ 2 + X + 1 : K[X]) ∈
      primaryFactors (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toLinearMap := by
    simpa [xV] using hmem
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
    ⟨irreducible_of_mem_primaryFactors hmem'⟩
  have hs0 : s = 0 := by rw [hs] at h0; omega
  have hsm' : s + primaryMultiplicity xV.toLinearMap (X ^ 2 + X + 1) = 4 := by
    simpa [xV] using hsm
  have hm4 : primaryMultiplicity xV.toLinearMap (X ^ 2 + X + 1) = 4 := by
    omega
  have hnEnd : Commute (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) xV := by
    have h := congrArg (fun e : ↥(CFSG.RankThree.Classical2.orthDerived Q) =>
      (e : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) hn.eq
    apply LinearEquiv.ext
    intro v
    have h2 := congrArg (fun e : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) => e v) h
    simpa [xV, LinearEquiv.mul_apply] using h2
  have hxmem : xV ∈ isometryCentralizer Q xV := by
    rw [mem_isometryCentralizer]
    exact ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem v, fun v => rfl⟩
  have hnmem : (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
      isometryCentralizer Q xV := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have hnO : (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q :=
        orthDerived_le_orthogonalGroup n.2
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hnO v
    · simpa [LinearEquiv.mul_apply] using LinearEquiv.congr_fun hnEnd.eq v
  have hothers : othersSpace xV.toLinearMap (X ^ 2 + X + 1) ≤ fixedSpace xV := by
    unfold othersSpace
    refine iSup_le fun k => iSup_le fun hk => ?_
    by_cases hk1 : k = X - 1
    · rw [hk1, fixedSpace_eq_primaryComponent]
    · exact absurd (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.eq_phi hx hpq (by simpa [xV] using hk.1) hk1) hk.2.1
  have hfix_bot : fixedSpace xV = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hxsupp : xV ∈ supportedBlock Q xV (X ^ 2 + X + 1) := by
    refine mem_supportedBlock.mpr ⟨hxmem, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      have hvbot : v ∈ (⊥ : Submodule K (Fin 4 ⊕ Fin 4 → K)) := by
        rw [← hfix_bot]; exact hothers hv
      simpa using hvbot
    rw [hv0, map_zero]
  have hnsupp : (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
      supportedBlock Q xV (X ^ 2 + X + 1) := by
    refine mem_supportedBlock.mpr ⟨hnmem, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      have hvbot : v ∈ (⊥ : Submodule K (Fin 4 ⊕ Fin 4 → K)) := by
        rw [← hfix_bot]; exact hothers hv
      simpa using hvbot
    rw [hv0, map_zero]
  let α : AdjoinRoot (X ^ 2 + X + 1 : K[X]) := AdjoinRoot.root (X ^ 2 + X + 1)
  have hα3 : α ^ 3 = 1 :=
    CFSG.RankThree.PartOne.KCOrthogonal.root_pow_eq_one (hx.dvd_X_pow_sub_one hmem)
  have hαne : α ≠ 1 :=
    CFSG.RankThree.PartOne.KCOrthogonal.root_ne_one
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.monic_phi.1
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_ne
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hα3
    exact zero_ne_one hα3
  have hα4 : α ^ 4 = α := by
    calc α ^ 4 = α ^ 3 * α := by ring_nf
      _ = α := by rw [hα3, one_mul]
  have hdetx : blockDet Q xV (X ^ 2 + X + 1) ⟨xV, hxsupp⟩ = α ^ 4 := by
    rw [OddOrderIsometry.blockDet_self_eq hx hmem' hxsupp, hm4]
  let v : AdjoinRoot (X ^ 2 + X + 1 : K[X]) :=
    blockDet Q xV (X ^ 2 + X + 1) ⟨n, hnsupp⟩
  have hunit : IsUnit v := by
    let gE : (primaryComponent xV.toLinearMap (X ^ 2 + X + 1)) ≃ₗ[AdjoinRoot (X ^ 2 + X + 1 : K[X])]
        (primaryComponent xV.toLinearMap (X ^ 2 + X + 1)) :=
      LinearMap.GeneralLinearGroup.toLinearEquiv
        (blockGL Q xV (X ^ 2 + X + 1) ⟨n, hnsupp⟩)
    have hgE : v = LinearMap.det (gE : Module.End (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
        (primaryComponent xV.toLinearMap (X ^ 2 + X + 1))) := by
      change blockDet Q xV (X ^ 2 + X + 1) ⟨n, hnsupp⟩ =
        LinearMap.det (gE : Module.End (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
          (primaryComponent xV.toLinearMap (X ^ 2 + X + 1)))
      rw [blockDet_apply]
      rfl
    rw [hgE]
    exact LinearEquiv.isUnit_det' gE
  have hcardE : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : K[X])) = 4 := by
    have : Module.Finite K (AdjoinRoot (X ^ 2 + X + 1 : K[X])) :=
      (AdjoinRoot.powerBasis (irreducible_of_mem_primaryFactors hmem').ne_zero).finite
    rw [Module.natCard_eq_pow_finrank (K := K),
      (AdjoinRoot.powerBasis (irreducible_of_mem_primaryFactors hmem').ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, CFSG.HardMathSupport.Dickson.Bal207.OrthFix.monic_phi.2, hK]
    norm_num
  haveI : Finite (AdjoinRoot (X ^ 2 + X + 1 : K[X])) := Module.finite_of_finite K
  let vu : (AdjoinRoot (X ^ 2 + X + 1 : K[X]))ˣ := hunit.unit
  have hvu_val : (vu : AdjoinRoot (X ^ 2 + X + 1 : K[X])) = v := IsUnit.unit_spec hunit
  let αu : (AdjoinRoot (X ^ 2 + X + 1 : K[X]))ˣ := Units.mk0 α hα0
  have hαu3 : αu ^ 3 = 1 := by
    ext
    simpa [αu] using hα3
  have hαune : αu ≠ 1 := by
    intro h
    apply hαne
    simpa [αu] using congrArg Units.val h
  have hcardU : Nat.card ((AdjoinRoot (X ^ 2 + X + 1 : K[X]))ˣ) = 3 := by
    rw [Nat.card_units, hcardE]
  have hordαu : orderOf αu = 3 := orderOf_eq_prime hαu3 hαune
  have hgen : Subgroup.zpowers αu = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hordαu, hcardU]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen ▸ Subgroup.mem_top vu)
  let j : ℕ := (m % 3).toNat
  have hjnonneg : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
  have hjcast : (j : ℤ) = m % 3 := Int.toNat_of_nonneg hjnonneg
  have hjeq : αu ^ j = vu := by
    have hmod : αu ^ (m % 3) = αu ^ m :=
      (zpow_eq_zpow_emod' m (by simpa using hαu3)).symm
    rw [← zpow_natCast (αu) j, hjcast, hmod]
    exact hm
  have hdetn : blockDet Q xV (X ^ 2 + X + 1) ⟨n, hnsupp⟩ = α ^ j := by
    have h := congrArg Units.val hjeq
    rw [Units.val_pow_eq_pow_val, hvu_val] at h
    simpa [αu, α, Units.val_mk0] using h.symm
  have hxjsupp : (xV ^ j) ∈ supportedBlock Q xV (X ^ 2 + X + 1) :=
    Subgroup.pow_mem _ hxsupp j
  have hxjeq : (⟨xV ^ j, hxjsupp⟩ : ↥(supportedBlock Q xV (X ^ 2 + X + 1))) =
      (⟨xV, hxsupp⟩ : ↥(supportedBlock Q xV (X ^ 2 + X + 1))) ^ j := by
    apply Subtype.ext
    rfl
  have hxdetj : blockDet Q xV (X ^ 2 + X + 1) ⟨xV ^ j, hxjsupp⟩ = α ^ j := by
    rw [hxjeq, map_pow]
    rw [show blockDet Q xV (X ^ 2 + X + 1) ⟨xV, hxsupp⟩ = α by rw [hdetx, hα4]]
  have hgsupp : ((n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *
      (xV ^ j)⁻¹) ∈ supportedBlock Q xV (X ^ 2 + X + 1) :=
    Subgroup.mul_mem _ hnsupp (Subgroup.inv_mem _ hxjsupp)
  have hgdet : blockDet Q xV (X ^ 2 + X + 1)
      ⟨(n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹, hgsupp⟩ = 1 := by
    have hmul := map_mul (blockDet Q xV (X ^ 2 + X + 1))
      ⟨(n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹, hgsupp⟩
      ⟨xV ^ j, hxjsupp⟩
    have hprod : (⟨(n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹,
        hgsupp⟩ * ⟨xV ^ j, hxjsupp⟩ : ↥(supportedBlock Q xV (X ^ 2 + X + 1))) =
        ⟨n, hnsupp⟩ := by
      apply Subtype.ext
      change (n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹ * xV ^ j = n
      group
    rw [hprod, hdetn, hxdetj] at hmul
    have h1 : blockDet Q xV (X ^ 2 + X + 1)
        ⟨(n : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (xV ^ j)⁻¹, hgsupp⟩ *
          α ^ j = α ^ j := by simpa using hmul.symm
    refine mul_right_cancel₀ (pow_ne_zero j hα0) ?_
    rw [h1, one_mul]
  refine ⟨j, ?_⟩
  rw [Subgroup.mem_subgroupOf]
  exact mem_specialBlock.mpr ⟨by simpa [xV] using hgsupp, by simpa [xV] using hgdet⟩

end CFSG.StandardType.E6QTwo

end
