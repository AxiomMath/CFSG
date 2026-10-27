module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
import CFSG.RankThree.PartTwo.Sec10.Item107ProofBasic
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Aux
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

section U48

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
  (SU4 Dstd SU4_eq_gramSU equivSU4 exists_map_conj_Dstd exists_isPrimitiveRoot_three
    mem_Dstd_of_isDiag card_Dstd σ4)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK)
open CFSG.RankThree.Classical (unitaryDiagGL unitaryPermGL unitaryDiagGL_mem_gramSU
  unitaryPermGL_mem_gramSU)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt baseA pow_val_add card_baseA)
open CFSG.RankThree.PartTwo.Sec8.Item812Res12 (sgnV)
open CFSG.LieType.Universal.Unitary (SUid)

private noncomputable def dg (u : Kˣ) (e : Fin 4 → ZMod 3) : GL (Fin 4) K :=
  unitaryDiagGL fun i => u ^ (e i).val

private theorem coe_dg (u : Kˣ) (e : Fin 4 → ZMod 3) :
    ((dg u e : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal fun i => ((u ^ (e i).val : Kˣ) : K) :=
  rfl

private theorem dg_add {u : Kˣ} (hu : u ^ 3 = 1) (e e' : Fin 4 → ZMod 3) :
    dg u (e + e') = dg u e * dg u e' := by
  apply Units.ext
  rw [Units.val_mul, coe_dg, coe_dg, coe_dg, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, pow_val_add hu, Units.val_mul]

private theorem dg_zero (u : Kˣ) : dg u 0 = 1 := by
  apply Units.ext
  rw [coe_dg, Units.val_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp

private theorem permGL_mul_dg (π : Equiv.Perm (Fin 4)) (u : Kˣ) (e : Fin 4 → ZMod 3) :
    unitaryPermGL π * dg u e * (unitaryPermGL π)⁻¹ = dg u (e ∘ π) := by
  apply Units.ext
  change (π.permMatrix K) * Matrix.diagonal _ * (π⁻¹).permMatrix K = Matrix.diagonal _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  have h : Equiv.symm (π⁻¹) = π := by rw [Equiv.Perm.inv_def, Equiv.symm_symm]
  simp only [Function.comp_id, Function.id_comp, h]
  exact Matrix.submatrix_diagonal_equiv _ π

private theorem exists_unit_three : ∃ u : Kˣ, u ^ 3 = 1 ∧ u ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  refine ⟨hu.unit, ?_, ?_⟩
  · apply Units.ext
    simpa using hζ.pow_eq_one
  · intro h
    exact hζ.ne_one (by norm_num) (by simpa using congrArg Units.val h)

private theorem zmod_eq_zero_of_pow_val {u : Kˣ} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) {a : ZMod 3}
    (h : u ^ a.val = 1) : a = 0 := by
  have ha : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases ha a with rfl | rfl | rfl
  · rfl
  · have h1 : (1 : ZMod 3).val = 1 := rfl
    rw [h1, pow_one] at h
    exact absurd h hu1
  · have h2 : (2 : ZMod 3).val = 2 := rfl
    rw [h2] at h
    exact absurd (calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu3, h]; simp) hu1

private theorem dg_injective {u : Kˣ} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) {e : Fin 4 → ZMod 3}
    (h : dg u e = 1) : e = 0 := by
  funext i
  have h1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) i i) h
  simp only [coe_dg, Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h1
  exact zmod_eq_zero_of_pow_val hu3 hu1 (Units.ext h1)


private def lin4 (v : Fin 3 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![v 0 + v 1 + v 2, -v 0 - v 1 + v 2, v 0 - v 1 - v 2, -v 0 + v 1 - v 2]

private theorem lin4_add (v w : Fin 3 → ZMod 3) : lin4 (v + w) = lin4 v + lin4 w := by
  funext i
  fin_cases i <;> simp [lin4] <;> ring

private theorem lin4_zero : lin4 0 = 0 := by
  funext i
  fin_cases i <;> simp [lin4]

private theorem sum_lin4 (v : Fin 3 → ZMod 3) : ∑ i, lin4 v i = 0 := by
  simp [Fin.sum_univ_four, lin4]
  ring

private noncomputable def tauGL {u : Kˣ} (hu : u ^ 3 = 1) :
    Multiplicative (Fin 3 → ZMod 3) →* GL (Fin 4) K where
  toFun v := dg u (lin4 (Multiplicative.toAdd v))
  map_one' := by simp [lin4_zero, dg_zero]
  map_mul' v w := by simp [lin4_add, dg_add hu]

private theorem dg_mem {u : Kˣ} (hu : u ^ 3 = 1) (e : Fin 4 → ZMod 3) (he : ∑ i, e i = 0) :
    dg u e ∈ SUid σ4 4 := by
  rw [SU4_eq_gramSU]
  refine unitaryDiagGL_mem_gramSU hK (fun i => ?_) ?_
  · rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm_eq_pow,
      ← Units.val_pow_eq_pow_val, ← pow_mul,
      show (e i).val * (2 ^ 3 + 1) = 3 * (3 * (e i).val) by ring, pow_mul, hu, one_pow,
      Units.val_one]
  · have hdvd : 3 ∣ ∑ i, (e i).val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using he
    obtain ⟨k, hk⟩ := hdvd
    rw [← Units.coe_prod, Finset.prod_pow_eq_pow_sum, hk, pow_mul, hu, one_pow, Units.val_one]

private noncomputable def tauSU {u : Kˣ} (hu : u ^ 3 = 1) :
    Multiplicative (Fin 3 → ZMod 3) →* SU4 :=
  (tauGL hu).codRestrict _ fun v => dg_mem hu _ (sum_lin4 _)

private theorem coe_tauSU {u : Kˣ} (hu : u ^ 3 = 1) (v : Multiplicative (Fin 3 → ZMod 3)) :
    (((tauSU hu v : SU4) : GL (Fin 4) K)) = dg u (lin4 (Multiplicative.toAdd v)) :=
  rfl

private def permT : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 1 3

private def permS : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private theorem sign_permT : Equiv.Perm.sign permT = 1 := by decide

private theorem sign_permS : Equiv.Perm.sign permS = 1 := by decide

private noncomputable def permSU (π : Equiv.Perm (Fin 4)) (hπ : Equiv.Perm.sign π = 1) : SU4 :=
  ⟨unitaryPermGL π, by rw [SU4_eq_gramSU]; exact unitaryPermGL_mem_gramSU hK hπ⟩

private theorem coe_permSU (π : Equiv.Perm (Fin 4)) (hπ : Equiv.Perm.sign π = 1) :
    (((permSU π hπ : SU4) : GL (Fin 4) K)) = unitaryPermGL π :=
  rfl

private theorem lin4_rot : ∀ v : Fin 3 → ZMod 3, lin4 ![v 2, v 0, v 1] = lin4 v ∘ permT := by
  decide

private theorem lin4_sgnV : ∀ v : Fin 3 → ZMod 3, lin4 (sgnV v) = lin4 v ∘ permS := by
  decide

private theorem lin4_inj : ∀ v : Fin 3 → ZMod 3, lin4 v = 0 → v = 0 := by
  decide

private theorem conj_tauSU {u : Kˣ} (hu : u ^ 3 = 1) (π : Equiv.Perm (Fin 4))
    (hπ : Equiv.Perm.sign π = 1) (v w : Fin 3 → ZMod 3) (h : lin4 w = lin4 v ∘ π) :
    permSU π hπ * tauSU hu (Multiplicative.ofAdd v) * (permSU π hπ)⁻¹ =
      tauSU hu (Multiplicative.ofAdd w) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_permSU, coe_tauSU, coe_tauSU,
    permGL_mul_dg]
  simp only [toAdd_ofAdd, h]


private theorem vec_sum : ∀ v : Fin 3 → ZMod 3,
    (v 0).val • (Pi.single 0 1 : Fin 3 → ZMod 3) + (v 1).val • (Pi.single 1 1 : Fin 3 → ZMod 3) +
      (v 2).val • (Pi.single 2 1 : Fin 3 → ZMod 3) = v := by
  decide

private theorem vecElt_tau {H : Type} [Group H] (τ : Multiplicative (Fin 3 → ZMod 3) →* H)
    (v : Fin 3 → ZMod 3) :
    vecElt (fun i => τ (Multiplicative.ofAdd (Pi.single i 1))) v =
      τ (Multiplicative.ofAdd v) := by
  have e : ∀ (i : Fin 3) (n : ℕ), τ (Multiplicative.ofAdd (Pi.single i 1)) ^ n =
      τ (Multiplicative.ofAdd (n • (Pi.single i 1 : Fin 3 → ZMod 3))) := by
    intro i n
    rw [ofAdd_nsmul, map_pow]
  simp only [vecElt]
  rw [e, e, e, ← map_mul, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simpa only [toAdd_mul, toAdd_ofAdd] using vec_sum v

private theorem three_smul_single (i : Fin 3) : 3 • (Pi.single i 1 : Fin 3 → ZMod 3) = 0 := by
  revert i
  decide

private theorem wreathFacts_of_tau {H : Type} [Group H]
    (τ : Multiplicative (Fin 3 → ZMod 3) →* H) (hτ : Function.Injective τ) {w : H}
    (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v : Fin 3 → ZMod 3, w * τ (Multiplicative.ofAdd v) * w⁻¹ =
      τ (Multiplicative.ofAdd ![v 2, v 0, v 1]))
    (hne : ∀ v : Fin 3 → ZMod 3, τ (Multiplicative.ofAdd v) ≠ w) :
    WreathFacts (fun i => τ (Multiplicative.ofAdd (Pi.single i 1))) w where
  pow_z i := by
    rw [← map_pow, ← ofAdd_nsmul, three_smul_single, ofAdd_zero, map_one]
  comm_z i j := (Commute.all _ _).map τ
  inj v hv := by
    rw [vecElt_tau] at hv
    have h1 : τ (Multiplicative.ofAdd v) = τ 1 := by rw [map_one]; exact hv
    exact ofAdd_eq_one.mp (hτ h1)
  pow_t := hw3
  conj0 := by
    have h := hwτ (Pi.single 0 1)
    have e : (![(Pi.single 0 1 : Fin 3 → ZMod 3) 2, (Pi.single 0 1 : Fin 3 → ZMod 3) 0,
        (Pi.single 0 1 : Fin 3 → ZMod 3) 1] : Fin 3 → ZMod 3) = Pi.single 1 1 := by decide
    rw [e] at h
    exact h
  conj1 := by
    have h := hwτ (Pi.single 1 1)
    have e : (![(Pi.single 1 1 : Fin 3 → ZMod 3) 2, (Pi.single 1 1 : Fin 3 → ZMod 3) 0,
        (Pi.single 1 1 : Fin 3 → ZMod 3) 1] : Fin 3 → ZMod 3) = Pi.single 2 1 := by decide
    rw [e] at h
    exact h
  conj2 := by
    have h := hwτ (Pi.single 2 1)
    have e : (![(Pi.single 2 1 : Fin 3 → ZMod 3) 2, (Pi.single 2 1 : Fin 3 → ZMod 3) 0,
        (Pi.single 2 1 : Fin 3 → ZMod 3) 1] : Fin 3 → ZMod 3) = Pi.single 0 1 := by decide
    rw [e] at h
    exact h
  t_ne v hv := by
    rw [vecElt_tau] at hv
    exact hne v hv


private theorem permT_pow_three : (permSU permT sign_permT) ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_permSU, pow_three]
  change permT.permMatrix K * (permT.permMatrix K * permT.permMatrix K) = _
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  have h : permT * (permT * permT) = 1 := by decide
  rw [mul_assoc, h, Matrix.permMatrix_one]
  rfl

private theorem tauSU_ne_permT {u : Kˣ} (hu : u ^ 3 = 1) (v : Fin 3 → ZMod 3) :
    tauSU hu (Multiplicative.ofAdd v) ≠ permSU permT sign_permT := by
  intro h
  have h1 := congrArg (fun g : SU4 => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 3) h
  change (Matrix.diagonal _ : Matrix (Fin 4) (Fin 4) K) 1 3 = (permT.permMatrix K) 1 3 at h1
  rw [Matrix.diagonal_apply_ne _ (by decide), CFSG.RankThree.Classical.permMatrix_apply',
    if_pos (by decide)] at h1
  exact zero_ne_one h1

private theorem baseA_tau_eq_Dstd {u : Kˣ} (hu : u ^ 3 = 1) {t : SU4}
    (hf : WreathFacts (fun i => tauSU hu (Multiplicative.ofAdd (Pi.single i 1))) t) :
    baseA (fun i => tauSU hu (Multiplicative.ofAdd (Pi.single i 1))) = Dstd := by
  have hmem : ∀ i, tauSU hu (Multiplicative.ofAdd (Pi.single i 1)) ∈ Dstd := fun i =>
    mem_Dstd_of_isDiag (by rw [coe_tauSU, coe_dg]; exact Matrix.isDiag_diagonal _) (hf.pow_z i)
  have hle : baseA (fun i => tauSU hu (Multiplicative.ofAdd (Pi.single i 1))) ≤ Dstd :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (hmem 0)) (Subgroup.zpowers_le.mpr (hmem 1)))
      (Subgroup.zpowers_le.mpr (hmem 2))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Dstd, card_baseA hf])

private theorem conjSignModel_SU4 : ConjSignModel SU4 := by
  obtain ⟨u, hu3, hu1⟩ := exists_unit_three
  have hτ : Function.Injective (tauSU hu3) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : dg u (lin4 (Multiplicative.toAdd v)) = 1 := congrArg Subtype.val hv
    exact Multiplicative.toAdd.injective (lin4_inj _ (dg_injective hu3 hu1 h1))
  have hf := wreathFacts_of_tau (tauSU hu3) hτ permT_pow_three
    (fun v => conj_tauSU hu3 permT sign_permT v _ (lin4_rot v)) (tauSU_ne_permT hu3)
  refine ⟨_, permSU permT sign_permT, permSU permS sign_permS, hf, fun w => ?_, fun E hE => ?_⟩
  · rw [vecElt_tau, vecElt_tau]
    exact conj_tauSU hu3 permS sign_permS w _ (lin4_sgnV w)
  · obtain ⟨g, hg⟩ := exists_map_conj_Dstd hE.1 hE.2
    exact ⟨g, by rw [baseA_tau_eq_Dstd hu3 hf]; exact hg⟩


private theorem conjSignModel_of_mulEquiv_big {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ConjSignModel H) : ConjSignModel G := by
  obtain ⟨z, t, s, hf, hs, hconj⟩ := h
  have hvec : ∀ v, vecElt (fun i => e.symm (z i)) v = e.symm (vecElt z v) := by
    intro v
    simp [vecElt, map_mul, map_pow]
  refine ⟨fun i => e.symm (z i), e.symm t, e.symm s, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i j => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_, fun v hv => ?_⟩
    · rw [← map_pow, hf.pow_z i, map_one]
    · rw [← map_mul, ← map_mul, hf.comm_z i j]
    · rw [hvec] at hv
      exact hf.inj v (e.symm.injective (by rw [map_one]; exact hv))
    · rw [← map_pow, hf.pow_t, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, hf.conj0]
    · rw [← map_inv, ← map_mul, ← map_mul, hf.conj1]
    · rw [← map_inv, ← map_mul, ← map_mul, hf.conj2]
    · rw [hvec] at hv
      exact hf.t_ne v (e.symm.injective hv)
  · intro w
    rw [hvec, hvec, ← map_inv, ← map_mul, ← map_mul, hs w]
  · intro E hE
    obtain ⟨g, hg⟩ := hconj (E.map e.toMonoidHom) (hE.map e)
    have hbase : baseA (fun i => e.symm (z i)) = (baseA z).map e.symm.toMonoidHom := by
      simp only [baseA, Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    refine ⟨e.symm g, ?_⟩
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hg, hbase, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext b
    simp [MulAut.conj_apply]

theorem conjSignModel_projSU_four_eight : ConjSignModel (projSU 4 2 3) :=
  conjSignModel_of_mulEquiv_big equivSU4 conjSignModel_SU4

end U48

theorem normIrred_projSU_four_eight : NormIrred (projSU 4 2 3) :=
  NormIrred.of_conjSignModel conjSignModel_projSU_four_eight

theorem normIrred_projSL_two_twentySeven : NormIrred (projSL 2 (GaloisField 3 3)) := by
  intro E U hE hUE hN
  obtain ⟨x, hxN, hxo, hxfix⟩ := KFacts.KS10Borel.exists_normalizer_orderOf_thirteen
    (Sec4.projSLEquivPSL (GaloisField 3 3)) hE.2
  exact Sec10.Item107Proof.eq_bot_or_eq_of_le_normalizer hE.2
    (by rw [← hxo]; exact pow_orderOf_eq_one x) hxfix hUE (hN hxN)

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
