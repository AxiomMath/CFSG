module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements
import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneForm
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
import CFSG.LocalAnalysis.StandardType.GGFusionShadowOrthogonal
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.Assembly.GL83LieDefs
import CFSG.ClassicalGroups.Alternating.TransvectionGenerationTwo

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType

private theorem oid_mulAut_congr_conj {R R' : Type} [Group R] [Group R'] (e : R ≃* R') (r : R) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem oid_ggLAut_congr {G : Type} [Group G] (L : Subgroup G) {R R' : Type} [Group R]
    [Group R'] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (θ' : ↥L ⧸ Subgroup.center ↥L ≃* R')
    (g : Subgroup.normalizer (L : Set G)) :
    ggLAut L θ' g = MulAut.congr (θ.symm.trans θ') (ggLAut L θ g) := by
  ext x
  obtain ⟨q, rfl⟩ := θ'.surjective x
  induction q using QuotientGroup.induction_on with
  | H l =>
      rw [ggLAut_apply, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.symm_symm]
      rw [ggLAut_apply]
      simp

private noncomputable def oid_omegaEquivOfIsometry {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K] {Q : QuadraticForm K (ι → K)}
    {Q' : QuadraticForm K (ι' → K)} (e : Q.IsometryEquiv Q') :
    ↥(LargeEvenOmega (⇑Q)) ≃* ↥(LargeEvenOmega (⇑Q')) :=
  (Subgroup.equivMapOfInjective (LargeEvenOmega (⇑Q))
      (ggFusionShadow_glLinConj e.toLinearEquiv).toMonoidHom
      (ggFusionShadow_glLinConj e.toLinearEquiv).injective).trans
    (MulEquiv.subgroupCongr
      (ggFusionShadow_map_statedOmega_glLinConj e.toLinearEquiv (fun v => e.map_app v)))

private theorem oid_charSum_top_congr {K : Type} [Field K] [CharP K 2] {V V' : Type}
    [AddCommGroup V] [Module K V] [Fintype V] [AddCommGroup V'] [Module K V'] [Fintype V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q') :
    OrdPNsOm.charSum Q ⊤ = OrdPNsOm.charSum Q' ⊤ := by
  have hftV : Fintype ↥(⊤ : Submodule K V) := Fintype.ofFinite _
  have hftV' : Fintype ↥(⊤ : Submodule K V') := Fintype.ofFinite _
  let f : ↥(⊤ : Submodule K V) ≃ ↥(⊤ : Submodule K V') :=
    { toFun := fun v => ⟨e v, Submodule.mem_top⟩
      invFun := fun w => ⟨e.symm w, Submodule.mem_top⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  rw [OrdPNsOm.charSum_eq, OrdPNsOm.charSum_eq]
  exact Fintype.sum_equiv f _ _ (fun v => congrArg OrdPNsOm.chi (e.map_app v).symm)

private theorem oid_bc_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have hcharK : CharP K 2 := by
    have hftK : Fintype K := Fintype.ofFinite K
    apply charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
    simpa [Nat.card_eq_fintype_card] using hK
  have h2 : ∀ x : K, x = 0 ∨ x = 1 :=
    CFSG.ClassicalGroups.Alternating.eq_zero_or_eq_one_of_card_eq_two hK
  have hc : c = 1 := by
    rcases h2 c with h | h
    · exact absurd (h ▸ hirr 0) (by simp)
    · exact h
  refine ⟨?_, hc⟩
  rcases h2 b with h | h
  · exfalso
    apply hirr 1
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [h, hc]
    linear_combination htwo
  · exact h

private theorem oid_orthInnerDiagData_holds_aux : OrthInnerDiagData := by
  intro G _ _ H E t δ h h4
  obtain ⟨hperf, lab, _, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hlab', _, _⟩ := hQ
  subst lab
  by_cases ht : Even t
  · have hlabD : planeAmbientLabel (.orthogonal δ) t =
        (⟨.D, t + δ.val, 1⟩ : LargeEvenLabel) := by
      simp [planeAmbientLabel, ht]
    rw [hlabD] at hraw
    simp only [LargeEvenRawDatumLegacy] at hraw
    split_ifs at hraw with h3
    · omega
    obtain ⟨K, hKf, hKfin, hKq, hQR⟩ := hraw
    obtain ⟨-, -, θ₀, -, hEN', hInd'⟩ := hQR
    have hK2 : Nat.card K = 2 := by simpa using hKq
    have hftK : Fintype K := Fintype.ofFinite K
    have hcharK : CharP K 2 := by
      apply charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      simpa [Nat.card_eq_fintype_card] using hK2
    have hdim : Module.finrank K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) =
        2 * (t + δ.val) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
        (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ)
        (CFSG.StandardType.GGQ2Frame.OrthBlocks.nondegenerate_planeQForm
          (K := K) (t := t) (δ := δ))
        (n := t + δ.val) (by omega) hdim with hplus | ⟨b, c, hirr, hne⟩
    ·
      obtain ⟨e⟩ := hplus
      let eqv : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (t + δ.val))) ≃*
          ↥(CFSG.StandardType.GGQ2Frame.OrthBlocks.omegaQ (K := K) t δ) :=
        (CFSG.StandardType.TableBOrth.projMkEquiv
          (CFSG.StandardType.TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot
            (K := K) (m := t + δ.val) (by omega))).symm.trans
          ((MulEquiv.subgroupCongr (congrArg LargeEvenOmega
            (CFSG.StandardType.TableBOrth.coe_qPlusForm
              (K := K) (t + δ.val)).symm)).trans
            ((oid_omegaEquivOfIsometry
              (Q := CFSG.StandardType.TableBOrth.qPlusForm K (t + δ.val))
              (Q' := CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ) e.symm).trans
              (MulEquiv.subgroupCongr (congrArg LargeEvenOmega
                (CFSG.StandardType.GGQ2Frame.OrthBlocks.coe_planeQForm
                  (K := K) (t := t) (δ := δ))))))
      refine ⟨K, inferInstance, inferInstance, inferInstance, hK2, hperf,
        θ₀.trans eqv, hEN', ?_⟩
      intro b hb
      obtain ⟨r, hr⟩ := ggLAut_mem_of_induces H θ₀ hEN' hInd' hb
      refine ⟨eqv r, ?_⟩
      rw [oid_ggLAut_congr H θ₀ (θ₀.trans eqv) ⟨b, hEN' hb⟩, ← hr]
      rw [show θ₀.symm.trans (θ₀.trans eqv) = eqv from by
        ext x
        simp [MulEquiv.trans_apply]]
      exact (oid_mulAut_congr_conj eqv r).symm
    ·
      obtain ⟨e⟩ := hne
      have hcs : OrdPNsOm.charSum
            (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ) ⊤ =
          (-2 : ℤ) ^ t * 2 ^ δ.val :=
        CFSG.StandardType.GGQ2Frame.OrthBlocks.charSum_planeQForm
          (K := K) (t := t) (δ := δ) hK2
      have hminus : OrdPNsOm.charSum
            (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) b c) ⊤ =
          -(2 : ℤ) ^ (t + δ.val) := by
        have h := (OrthTorus.charSum_qMinusForm (K := K) (m := t + δ.val - 1)
          (b := b) (c := c) hirr).1
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ t + δ.val), hK2] at h
      have hqi : (CFSG.LieType.Universal.Spin.quadMinus (t + δ.val) K b c).IsometryEquiv
          (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) b c) := by
        suffices h : (CFSG.LieType.Universal.Spin.quadMinus
            (t + δ.val - 1 + 1) K b c).IsometryEquiv
            (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) b c) by
          rwa [Nat.sub_add_cancel (show 1 ≤ t + δ.val by omega)] at h
        exact (CFSG.StandardType.TableBOrth.qMinusIsometry (K := K) (t + δ.val - 1) b c).symm
      have h1 : OrdPNsOm.charSum
            (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ) ⊤ =
          OrdPNsOm.charSum
            (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) b c) ⊤ :=
        (oid_charSum_top_congr e).trans (oid_charSum_top_congr hqi)
      have hAB : (-2 : ℤ) ^ t * 2 ^ δ.val = -(2 : ℤ) ^ (t + δ.val) := by
        rw [← hcs, h1, hminus]
      have hneg : (-2 : ℤ) ^ t = 2 ^ t := by
        rw [show (-2 : ℤ) = (-1) * 2 by norm_num, mul_pow, ht.neg_one_pow, one_mul]
      have h2 : (-2 : ℤ) ^ t * 2 ^ δ.val = (2 : ℤ) ^ (t + δ.val) := by
        rw [hneg, ← pow_add]
      have hpos : (0 : ℤ) < 2 ^ (t + δ.val) := pow_pos (by norm_num) _
      linarith
  ·
    have hlabD : planeAmbientLabel (.orthogonal δ) t =
        (⟨.twD, t + δ.val, 1⟩ : LargeEvenLabel) := by
      simp [planeAmbientLabel, ht]
    rw [hlabD] at hraw
    simp only [LargeEvenRawDatumLegacy] at hraw
    split_ifs at hraw with h2 h3
    · omega
    · omega
    obtain ⟨K, hKf, hKfin, hKq, b, c, hirr, hQR⟩ := hraw
    obtain ⟨-, -, θ₀, -, hEN', hInd'⟩ := hQR
    have hK2 : Nat.card K = 2 := by simpa using hKq
    have hftK : Fintype K := Fintype.ofFinite K
    have hcharK : CharP K 2 := by
      apply charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      simpa [Nat.card_eq_fintype_card] using hK2
    obtain ⟨hb, hc⟩ := oid_bc_eq_one hK2 hirr
    subst b
    subst c
    have hdim : Module.finrank K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) =
        2 * (t + δ.val) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
        (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ)
        (CFSG.StandardType.GGQ2Frame.OrthBlocks.nondegenerate_planeQForm
          (K := K) (t := t) (δ := δ))
        (n := t + δ.val) (by omega) hdim with hplus | ⟨b₀, c₀, hirr₀, hne⟩
    ·
      obtain ⟨e⟩ := hplus
      have hcs : OrdPNsOm.charSum
            (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ) ⊤ =
          (-2 : ℤ) ^ t * 2 ^ δ.val :=
        CFSG.StandardType.GGQ2Frame.OrthBlocks.charSum_planeQForm
          (K := K) (t := t) (δ := δ) hK2
      have hq : OrdPNsOm.charSum
            (CFSG.StandardType.TableBOrth.qPlusForm K (t + δ.val)) ⊤ =
          (2 : ℤ) ^ (t + δ.val) := by
        have h := OrthTorus.charSum_qPlusForm (K := K) (n := t + δ.val - 1)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ t + δ.val), hK2] at h
      have h1 : OrdPNsOm.charSum
            (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ) ⊤ =
          OrdPNsOm.charSum
            (CFSG.StandardType.TableBOrth.qPlusForm K (t + δ.val)) ⊤ :=
        oid_charSum_top_congr e
      have hodd : Odd t := Nat.not_even_iff_odd.mp ht
      have hneg : (-2 : ℤ) ^ t = -(2 : ℤ) ^ t := by
        rw [show (-2 : ℤ) = (-1) * 2 by norm_num, mul_pow, hodd.neg_one_pow, neg_one_mul]
      have hAB : (-2 : ℤ) ^ t * 2 ^ δ.val = (2 : ℤ) ^ (t + δ.val) := by
        rw [← hcs, h1, hq]
      have h2 : (-2 : ℤ) ^ t * 2 ^ δ.val = -(2 : ℤ) ^ (t + δ.val) := by
        rw [hneg, neg_mul, ← pow_add]
      have hpos : (0 : ℤ) < 2 ^ (t + δ.val) := pow_pos (by norm_num) _
      linarith
    ·
      obtain ⟨e⟩ := hne
      obtain ⟨hb₀, hc₀⟩ := oid_bc_eq_one hK2 hirr₀
      subst b₀
      subst c₀
      have hqi : (CFSG.LieType.Universal.Spin.quadMinus (t + δ.val) K 1 1).IsometryEquiv
          (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) 1 1) := by
        suffices h : (CFSG.LieType.Universal.Spin.quadMinus
            (t + δ.val - 1 + 1) K 1 1).IsometryEquiv
            (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) 1 1) by
          rwa [Nat.sub_add_cancel (show 1 ≤ t + δ.val by omega)] at h
        exact (CFSG.StandardType.TableBOrth.qMinusIsometry (K := K) (t + δ.val - 1) 1 1).symm
      let e₂ : (CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ).IsometryEquiv
          (CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) 1 1) :=
        e.trans hqi
      let eqv : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (K := K) (t + δ.val - 1) 1 1)) ≃*
          ↥(CFSG.StandardType.GGQ2Frame.OrthBlocks.omegaQ (K := K) t δ) :=
        (CFSG.StandardType.TableBOrth.projMkEquiv
          (CFSG.StandardType.TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot
            (K := K) (m := t + δ.val - 1) 1 1)).symm.trans
          ((MulEquiv.subgroupCongr (congrArg LargeEvenOmega
            (CFSG.StandardType.TableBOrth.coe_qMinusForm
              (K := K) (m := t + δ.val - 1) (b := 1) (c := 1)).symm)).trans
            ((oid_omegaEquivOfIsometry
              (Q := CFSG.StandardType.TableBOrth.qMinusForm K (t + δ.val - 1) 1 1)
              (Q' := CFSG.StandardType.GGQ2Frame.OrthBlocks.planeQForm K t δ) e₂.symm).trans
              (MulEquiv.subgroupCongr (congrArg LargeEvenOmega
                (CFSG.StandardType.GGQ2Frame.OrthBlocks.coe_planeQForm
                  (K := K) (t := t) (δ := δ))))))
      refine ⟨K, inferInstance, inferInstance, inferInstance, hK2, hperf,
        θ₀.trans eqv, hEN', ?_⟩
      intro b hb
      obtain ⟨r, hr⟩ := ggLAut_mem_of_induces H θ₀ hEN' hInd' hb
      refine ⟨eqv r, ?_⟩
      rw [oid_ggLAut_congr H θ₀ (θ₀.trans eqv) ⟨b, hEN' hb⟩, ← hr]
      rw [show θ₀.symm.trans (θ₀.trans eqv) = eqv from by
        ext x
        simp [MulEquiv.trans_apply]]
      exact (oid_mulAut_congr_conj eqv r).symm

theorem orthInnerDiagData_holds : OrthInnerDiagData := oid_orthInnerDiagData_holds_aux

end CFSG.StandardType.GGQ2Frame.OrthPlacement
