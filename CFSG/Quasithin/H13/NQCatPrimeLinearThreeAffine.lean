module

public import CFSG.Quasithin.H13.NQCatAffineLevi
public import CFSG.Quasithin.H13.NQCatSubnormalCore
public import CFSG.Quasithin.H13.NQCatPrimeLinearThreeRankOne
public import CFSG.Quasithin.H13.LocDblMatrix

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Quasithin CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar

theorem exists_central_involution_sylow {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (D : Subgroup (SL3 F)) [D.Normal] (hDc : D ≤ center (SL3 F))
    (T : Sylow 2 (SL3 F ⧸ D)) :
    ∃ t ∈ (T : Subgroup (SL3 F ⧸ D)), (∀ x ∈ (T : Subgroup (SL3 F ⧸ D)), x * t = t * x) ∧
      orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2SL : 2 ∣ Nat.card (SL3 F) := by
    rw [card_SL_three']
    have h1 : Even (Nat.card F ^ 2 - 1) := Nat.Odd.sub_odd hF.pow odd_one
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (even_iff_two_dvd.mp h1) _) _
  have h2A : 2 ∣ Nat.card (SL3 F ⧸ D) := by
    rw [D.card_eq_card_quotient_mul_card_subgroup] at h2SL
    exact (Nat.Coprime.dvd_mul_right
      (Nat.coprime_two_left.mpr (scalar_kernel_odd F D hDc))).mp h2SL
  have : Nontrivial ↥(T : Subgroup (SL3 F ⧸ D)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (T.ne_bot_of_dvd_card h2A)
  have hZ : Nontrivial ↥(center ↥(T : Subgroup (SL3 F ⧸ D))) := T.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcardZ⟩ := ((T.isPGroup'.to_subgroup _).nontrivial_iff_card).mp hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
    (hcardZ ▸ dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn))
  refine ⟨((z : ↥(T : Subgroup (SL3 F ⧸ D))) : SL3 F ⧸ D),
    (z : ↥(T : Subgroup (SL3 F ⧸ D))).2,
    fun x hx => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem affine_case {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hFp : Nat.card F = p) (hp5 : 5 ≤ p) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ scalars 3 F) {W : Submodule F (Fin 3 → F)} {N : Type*} [CommGroup N]
    {φ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut N}
    (htrans : ∀ n m : N, n ≠ 1 → m ≠ 1 → ∃ A, φ A n = m)
    (θ : N ⋊[φ] Matrix.SpecialLinearGroup (Fin 2) F →* SL3 F) (hθ : Function.Injective θ)
    (hrange : θ.range = (CFSG.perfectResidual ↥(stabilizer W)).map (stabilizer W).subtype)
    (hZ : θ.range ⊓ scalars 3 F = ⊥) (ρ : ↥(stabilizer W) →* GL (Fin 2) F)
    (hρ : Function.Surjective ρ) (hθQ : θ.range ≤ stabilizer W)
    (hρθ : ∀ x, ρ ⟨θ x, hθQ ⟨x, rfl⟩⟩ = Matrix.SpecialLinearGroup.toGL x.right)
    (hker : ∀ g : ↥(stabilizer W), ρ g = 1 → (g : SL3 F) ∈ (θ.comp SemidirectProduct.inl).range)
    (T : Sylow 2 (SL3 F ⧸ D)) {B : Subgroup (SL3 F ⧸ D)} (hBq : ¬ CFSG.IsQuasisimple ↥B)
    (hB : B ∈ cComp (B ⊔ (T : Subgroup (SL3 F ⧸ D))))
    (hMW : (B ⊔ (T : Subgroup (SL3 F ⧸ D))).comap (QuotientGroup.mk' D) ≤ stabilizer W) :
    Function.Injective ((QuotientGroup.mk' D).comp θ) ∧
      ((QuotientGroup.mk' D).comp θ).range = B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : SL3 F →* SL3 F ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  set M : Subgroup (SL3 F ⧸ D) := B ⊔ (T : Subgroup (SL3 F ⧸ D)) with hM
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have hYD : θ.range ⊓ D = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hD).trans hZ.le)
  have hinjOn := injOn_mk_of_inf_eq_bot hYD
  have hinj : Function.Injective (π.comp θ) := fun x y hxy =>
    hθ (hinjOn ⟨x, rfl⟩ ⟨y, rfl⟩ hxy)
  set Bt : Subgroup (SL3 F) := B.comap π with hBt
  set C : Subgroup (SL3 F) := (CFSG.perfectResidual ↥Bt).map Bt.subtype with hC
  have hCB : C.map π = B := map_perfectResidual_comap_eq π hπs hBperf
  have hCperf : ⁅C, C⁆ = C := by
    have h1 : Group.IsPerfect (CFSG.perfectResidual ↥Bt) :=
      (CFSG.perfect_residual_characterization (G := ↥Bt)).2.2.1
    rw [Subgroup.isPerfect_iff] at h1
    rw [hC, ← Subgroup.map_commutator, h1]
  have hCBt : C ≤ Bt := map_subtype_le _
  have hCM : C ≤ M.comap π := hCBt.trans (comap_mono le_sup_left)
  have hC1 : C ≠ ⊥ := fun h => ne_bot_of_mem_cComp hB (by rw [← hCB, h, Subgroup.map_bot])
  have hCY : C ≤ θ.range := by
    rw [hrange]
    exact le_map_perfectResidual_of_perfect (hCM.trans hMW) hCperf
  have hCq : ¬ CFSG.IsQuasisimple ↥C := by
    intro hq
    apply hBq
    have hinjC : Function.Injective (π.comp C.subtype) := fun x y hxy =>
      Subtype.ext (hinjOn (hCY x.2) (hCY y.2) hxy)
    have hrangeC : (π.comp C.subtype).range = B := by
      rw [MonoidHom.range_comp, range_subtype, hCB]
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((MonoidHom.ofInjective hinjC).trans (MulEquiv.subgroupCongr hrangeC))).1 hq
  have hBMs : (B.subgroupOf M).IsSubnormal :=
    (mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hB)).2.2.1
  let f : ↥(M.comap π) →* ↥M := (π.comp (M.comap π).subtype).codRestrict M fun x => x.2
  have hK : (Bt.subgroupOf (M.comap π)).IsSubnormal := by
    have h1 : (B.subgroupOf M).comap f = Bt.subgroupOf (M.comap π) := by
      ext x
      exact Iff.rfl
    rw [← h1]
    exact hBMs.comap f
  have hCnorm : ∀ g ∈ Bt, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    have hCsub' : C.subgroupOf Bt = CFSG.perfectResidual ↥Bt :=
      comap_map_eq_self_of_injective Bt.subtype_injective _
    have hCN : (C.subgroupOf Bt).Normal := by
      rw [hCsub']
      exact Subgroup.normal_of_characteristic _
    intro g hg c hc
    have h1 : (⟨c, hCBt hc⟩ : ↥Bt) ∈ C.subgroupOf Bt := mem_subgroupOf.mpr hc
    have h2 := mem_subgroupOf.mp (hCN.conj_mem _ h1 ⟨g, hg⟩)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hCsub : (C.subgroupOf (M.comap π)).IsSubnormal := by
    have hHK : ((C.subgroupOf (M.comap π)).subgroupOf (Bt.subgroupOf (M.comap π))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
      have hg := g.2
      rw [mem_subgroupOf] at hg
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hCnorm _ hg _ hn
    exact Subgroup.IsSubnormal.trans (fun x hx => by
      rw [mem_subgroupOf] at hx ⊢
      exact hCBt hx) hHK.isSubnormal hK
  obtain ⟨S, hSM⟩ := exists_sylow_le_comap π hπs T
    (le_sup_right : (T : Subgroup (SL3 F ⧸ D)) ≤ M)
  have hCeq : C = θ.range := eq_range_of_affine hFp hp5 ρ hρ htrans θ hθ hθQ hρθ hker hMW S
    hSM hCM hCY hCperf hC1 hCsub hCq
  refine ⟨hinj, ?_⟩
  rw [MonoidHom.range_comp, ← hCeq, hCB]

theorem affine_conclusions {F : Type} [Field F] [Finite F] {p a b : ℕ} [Fact p.Prime] [CharP F p]
    (hFp : Nat.card F = p) (hab : b * a = 2) (D : Subgroup (SL3 F)) [D.Normal]
    {W : Submodule F (Fin 3 → F)} {φ : Matrix.SpecialLinearGroup (Fin 2) F →*
      MulAut (Multiplicative (Matrix (Fin a) (Fin b) F))}
    (θ : Multiplicative (Matrix (Fin a) (Fin b) F) ⋊[φ] Matrix.SpecialLinearGroup (Fin 2) F →*
      SL3 F)
    (hrange : θ.range = (CFSG.perfectResidual ↥(stabilizer W)).map (stabilizer W).subtype)
    (hU : (θ.comp SemidirectProduct.inl).range = radU F W) {B : Subgroup (SL3 F ⧸ D)}
    (hinj : Function.Injective ((QuotientGroup.mk' D).comp θ))
    (hB : ((QuotientGroup.mk' D).comp θ).range = B) :
    B = (CFSG.perfectResidual ↥((stabilizer W).map (QuotientGroup.mk' D))).map
        ((stabilizer W).map (QuotientGroup.mk' D)).subtype ∧
      (radU F W).map (QuotientGroup.mk' D) ≤ B ∧
      IsElementaryAbelian p ↥((radU F W).map (QuotientGroup.mk' D)) ∧
      Nat.card ↥((radU F W).map (QuotientGroup.mk' D)) = p ^ 2 ∧
      ∃ ψ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
        ψ.ker = ((radU F W).map (QuotientGroup.mk' D)).subgroupOf B := by
  have hUB : (((QuotientGroup.mk' D).comp θ).comp SemidirectProduct.inl).range =
      (radU F W).map (QuotientGroup.mk' D) := by
    rw [MonoidHom.comp_assoc, MonoidHom.range_comp, hU]
  subst hB
  rw [← hUB]
  obtain ⟨hle, hψ⟩ := affine_image_projection _ hinj
  refine ⟨?_, hle, isElementaryAbelian_range_of_comm _ (fun x y => mul_comm x y)
    pow_char_multiplicative_matrix, ?_, hψ⟩
  · rw [MonoidHom.range_comp, hrange]
    exact map_perfectResidual_subgroup _ _
  · rw [← Nat.card_congr (MonoidHom.ofInjective
      (f := ((QuotientGroup.mk' D).comp θ).comp SemidirectProduct.inl)
      (hinj.comp SemidirectProduct.inl_injective)).toEquiv, card_multiplicative_matrix, hab, hFp]

variable {F : Type} [Field F] [Finite F]

theorem prime_linear_three_nonquasisimple_local_actual_affine_production
    (hI : OddLinearThreeInvolutionSylowStructure F) {p : ℕ}
    [hp : Fact p.Prime] (hFp : Nat.card F = p) (hp5 : 5 ≤ p) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ scalars 3 F) (T : Sylow 2 (SL3 F ⧸ D)) {B : Subgroup (SL3 F ⧸ D)}
    (hBq : ¬ CFSG.IsQuasisimple ↥B) (hB : B ∈ cComp (B ⊔ (T : Subgroup (SL3 F ⧸ D)))) :
    CFSG.pCore 2 ↥(B ⊔ (T : Subgroup (SL3 F ⧸ D))) = ⊥ ∧
      ∃ W : Submodule F (Fin 3 → F), (finrank F W = 1 ∨ finrank F W = 2) ∧
        B ⊔ (T : Subgroup (SL3 F ⧸ D)) ≤ (stabilizer W).map (QuotientGroup.mk' D) ∧
        B = (CFSG.perfectResidual ↥((stabilizer W).map (QuotientGroup.mk' D))).map
          ((stabilizer W).map (QuotientGroup.mk' D)).subtype ∧
        (radU F W).map (QuotientGroup.mk' D) ≤ B ∧
        IsElementaryAbelian p ↥((radU F W).map (QuotientGroup.mk' D)) ∧
        Nat.card ↥((radU F W).map (QuotientGroup.mk' D)) = p ^ 2 ∧
        (∃ ψ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
          ψ.ker = ((radU F W).map (QuotientGroup.mk' D)).subgroupOf B) ∧
        (finrank F W = 2 → ∃ s : SL3 F, (flagSpace 3 F 2).map (Matrix.mulVecLin s.val) = W ∧
          Function.Injective ((QuotientGroup.mk' D).comp (natTheta F s)) ∧
          ((QuotientGroup.mk' D).comp (natTheta F s)).range = B ∧
          ((natTheta F s).comp SemidirectProduct.inl).range = radU F W ∧
          ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F)
            (X : Multiplicative (Matrix (Fin 2) (Fin 1) F)),
            natTheta F s (SemidirectProduct.inr A) * natTheta F s (SemidirectProduct.inl X) *
              (natTheta F s (SemidirectProduct.inr A))⁻¹ = natTheta F s
                (SemidirectProduct.inl (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X)))) ∧
        (finrank F W = 1 → ∃ s : SL3 F, (flagSpace 3 F 1).map (Matrix.mulVecLin s.val) = W ∧
          Function.Injective ((QuotientGroup.mk' D).comp (dualTheta F s)) ∧
          ((QuotientGroup.mk' D).comp (dualTheta F s)).range = B ∧
          ((dualTheta F s).comp SemidirectProduct.inl).range = radU F W ∧
          ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F)
            (X : Multiplicative (Matrix (Fin 1) (Fin 2) F)),
            dualTheta F s (SemidirectProduct.inr A) * dualTheta F s (SemidirectProduct.inl X) *
              (dualTheta F s (SemidirectProduct.inr A))⁻¹ = dualTheta F s
                (SemidirectProduct.inl
                  (Multiplicative.ofAdd (Multiplicative.toAdd X * (A⁻¹).val)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have hchar : CharP F p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hFp])
  have hF : Odd (Nat.card F) := by
    rw [hFp]
    exact hp.out.odd_of_ne_two (by omega)
  have h4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four_of_le (by omega)
  have hDc : D ≤ center (SL3 F) := hD.trans (scalars_le_center 3 F)
  set π : SL3 F →* SL3 F ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : π.ker ≤ center (SL3 F) := by rw [hπ, QuotientGroup.ker_mk']; exact hDc
  set M : Subgroup (SL3 F ⧸ D) := B ⊔ (T : Subgroup (SL3 F ⧸ D)) with hM
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have hO2 : CFSG.pCore 2 ↥M = ⊥ := by
    by_contra hO2
    obtain ⟨t, htT, htZ, ht2⟩ := exists_central_involution_sylow hF D hDc T
    obtain ⟨-, _, -, -, -, -, -, ⟨e⟩⟩ :=
      prime_linear_three_positive_two_core_actual_rank_one_equality hI hFp hp5 D hD T hB hO2
        htT htZ ht2
    exact hBq ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2
      (isQuasisimple_SL2_of_four h4))
  let θ₃ : SL3 F →* LinearMap.GeneralLinearGroup F (Fin 3 → F) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin 3) F ≃* _).toMonoidHom.comp
      Matrix.SpecialLinearGroup.toGL
  have hθ₃ : Function.Injective θ₃ :=
    Matrix.GeneralLinearGroup.toLin.injective.comp Matrix.SpecialLinearGroup.toGL_injective
  have hV3 : finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  have : Finite (LinearMap.GeneralLinearGroup F (Fin 3 → F)) := LocDbl.finite_GL
  have hOpB : CFSG.pCore p ↥B ≠ ⊥ := by
    intro hbot
    obtain ⟨-, -, -, -, hcomm⟩ := LocDbl.nonquasisimple_Fitting_of_mem_cComp hB hBq
    apply hcomm
    refine LocDbl.commutator_fitting_eq_bot_of_pCore fun ℓ hℓ => ?_
    by_cases hℓp : ℓ = p
    · rw [hℓp, hbot, Subgroup.commutator_bot_right]
    · have : Fact ℓ.Prime := ⟨hℓ⟩
      have hNn : (((CFSG.pCore ℓ ↥B).map B.subtype).subgroupOf B).Normal := by
        rw [show ((CFSG.pCore ℓ ↥B).map B.subtype).subgroupOf B = CFSG.pCore ℓ ↥B from
          comap_map_eq_self_of_injective B.subtype_injective _]
        exact CFSG.pCore_normal
      have hcom := commute_of_normal_coprime_of_finrank_three hV3 θ₃ hθ₃ D hDc hBperf
        (map_subtype_le _) hNn hℓp (CFSG.pCore_isPGroup.map _)
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro b _
      rw [mem_centralizer_iff]
      intro n hn
      exact Subtype.ext (hcom (b : SL3 F ⧸ D) b.2 (n : SL3 F ⧸ D) ⟨n, hn, rfl⟩).symm
  have hBMs : (B.subgroupOf M).IsSubnormal :=
    (mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hB)).2.2.1
  have hOpM : CFSG.pCore p ↥M ≠ ⊥ := by
    intro hbot
    apply hOpB
    have h1 := map_pCore_le_pCore_of_isSubnormal' (p := p) hBMs
    rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (subtype_injective _)] at h1
    have h2 := CFSG.LieType.SteinbergBR.pCore_map_equiv p
      (subgroupOfEquivOfLe (le_sup_left : B ≤ M))
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  set Np : Subgroup (SL3 F ⧸ D) := (CFSG.pCore p ↥M).map M.subtype with hNp
  have hNpp : IsPGroup p ↥Np := CFSG.pCore_isPGroup.map _
  have hNpM : Np ≤ M := map_subtype_le _
  have hNpn : (Np.subgroupOf M).Normal := by
    rw [hNp, show ((CFSG.pCore p ↥M).map M.subtype).subgroupOf M = CFSG.pCore p ↥M from
      comap_map_eq_self_of_injective M.subtype_injective _]
    exact CFSG.pCore_normal
  have hMN : M ≤ normalizer (Np : Set (SL3 F ⧸ D)) :=
    (normal_subgroupOf_iff_le_normalizer hNpM).mp hNpn
  obtain ⟨U₀, hUchar, hUN⟩ := exists_normal_sylow_of_central_kernel π hπs hker hNpp
  set Ut : Subgroup (SL3 F) := (U₀ : Subgroup (Np.comap π)).map (Np.comap π).subtype with hUt
  have hMU : M.comap π ≤ normalizer (Ut : Set (SL3 F)) :=
    ((comap_mono hMN).trans (le_normalizer_comap π)).trans
      (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hUp : IsPGroup p ↥(Ut.map θ₃) := (U₀.isPGroup'.map _).map θ₃
  have hUne : Ut.map θ₃ ≠ ⊥ := by
    have hNpne : Np ≠ ⊥ := fun h =>
      hOpM ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
    obtain ⟨n, hn, hn1⟩ : ∃ n ∈ Np, n ≠ 1 := by
      obtain ⟨n, hn⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNpne
      exact ⟨n, n.2, fun h => hn (Subtype.ext h)⟩
    obtain ⟨q, hq, hqn⟩ := hUN n hn
    intro hbot
    have hθq : θ₃ (q : SL3 F) ∈ Ut.map θ₃ := ⟨q, ⟨q, hq, rfl⟩, rfl⟩
    rw [hbot, mem_bot] at hθq
    apply hn1
    rw [← hqn, hθ₃ (hθq.trans (map_one θ₃).symm), map_one]
  set W : Submodule F (Fin 3 → F) := LocDbl.fixedSpace (Ut.map θ₃) with hWdef
  have hW0 : W ≠ ⊥ := LocDbl.exists_fixed_ne_zero (p := p) (by rw [hV3]; norm_num) hUp
  have hWtop : W ≠ ⊤ := LocDbl.fixedSpace_ne_top hUne
  have hWdim : finrank F W = 1 ∨ finrank F W = 2 := by
    have h1 : 1 ≤ finrank F W := Submodule.one_le_finrank_iff.mpr hW0
    have h2 : finrank F W < 3 := by
      have h3 := Submodule.finrank_lt hWtop
      rwa [hV3] at h3
    omega
  have hMW : M.comap π ≤ stabilizer W := by
    intro g hg
    rw [mem_stabilizer_iff_map_le]
    rintro _ ⟨w, hw, rfl⟩
    have hgN : θ₃ g ∈ normalizer ((Ut.map θ₃ : Subgroup _) : Set _) :=
      le_normalizer_map θ₃ ⟨g, hMU hg, rfl⟩
    exact LocDbl.fixedSpace_invariant hgN hw
  have hMP : M ≤ (stabilizer W).map π := by
    intro m hm
    obtain ⟨g, rfl⟩ := hπs m
    exact ⟨g, hMW (show g ∈ M.comap π from hm), rfl⟩
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect h4).commutator_eq_top
  obtain ⟨s, hs⟩ := exists_map_flagSpace_eq W
  rcases hWdim with hW1 | hW2
  · rw [hW1] at hs
    obtain ⟨hθinj, hrange, hU, hZ⟩ := dualTheta_spec hSL hs
    obtain ⟨ρ, hθQ, hρs, hρθ, hρker⟩ := levi_dual hs
    obtain ⟨hinj, hBrange⟩ := affine_case hFp hp5 D hD phiR_transitive (dualTheta F s) hθinj
      hrange hZ ρ hρs hθQ hρθ hρker T hBq hB hMW
    obtain ⟨hBeq, hUle, hel, hcard, hψ⟩ :=
      affine_conclusions (a := 1) (b := 2) hFp rfl D (dualTheta F s) hrange hU hinj hBrange
    exact ⟨hO2, W, Or.inl hW1, hMP, hBeq, hUle, hel, hcard, hψ,
      fun h => absurd (hW1.symm.trans h) (by norm_num),
      fun _ => ⟨s, hs, hinj, hBrange, hU, dualTheta_conj s⟩⟩
  · rw [hW2] at hs
    obtain ⟨hθinj, hrange, hU, hZ⟩ := natTheta_spec hSL hs
    obtain ⟨ρ, hθQ, hρs, hρθ, hρker⟩ := levi_nat hs
    obtain ⟨hinj, hBrange⟩ := affine_case hFp hp5 D hD phiL_transitive (natTheta F s) hθinj
      hrange hZ ρ hρs hθQ hρθ hρker T hBq hB hMW
    obtain ⟨hBeq, hUle, hel, hcard, hψ⟩ :=
      affine_conclusions (a := 2) (b := 1) hFp rfl D (natTheta F s) hrange hU hinj hBrange
    exact ⟨hO2, W, Or.inr hW2, hMP, hBeq, hUle, hel, hcard, hψ,
      fun _ => ⟨s, hs, hinj, hBrange, hU, natTheta_conj s⟩,
      fun h => absurd (hW2.symm.trans h) (by norm_num)⟩

end CFSG.Quasithin.H13.NQCat
