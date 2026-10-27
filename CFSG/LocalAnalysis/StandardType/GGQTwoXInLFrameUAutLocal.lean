module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFrame
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar
public import CFSG.LieType.Universal.Unitary.Comparison

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Phan
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

@[expose] noncomputable def ggQTwoXInLU_blockCover {n : ℕ} {K : Type} [Field K] [Finite K]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (S : Finset (Fin (n + 1))) :
    ↥(unitarySU 2 1 K S.card) →* G :=
  C.φ.comp (TableBUE.blockExtSU S C.field)

private lemma ggQTUa_psiS_range {n : ℕ} {K : Type} [Field K] [Finite K]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (S : Finset (Fin (n + 1))) :
    (ggQTwoXInLU_blockCover C S).range = (TableBUE.blockSU (K := K) (n := 1) S).map C.φ := by
  rw [ggQTwoXInLU_blockCover, MonoidHom.range_comp, TableBUE.range_blockExtSU]

@[expose] noncomputable def ggQTwoXInLU_suEquiv {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (S : Finset (Fin (n + 1))) :
    Su K 2 1 S.card ≃* ↥(unitarySU 2 1 K S.card) :=
  letI : Fact (Nat.Prime 2) := ⟨C.field.prime⟩
  letI : CharP K 2 := C.field.charP
  MulEquiv.subgroupCongr
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1)
      (by rw [C.field.card]; norm_num) S.card)

@[expose] noncomputable def ggQTwoXInLU_blockCoverSU {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (S : Finset (Fin (n + 1))) :
    Su K 2 1 S.card →* G :=
  (ggQTwoXInLU_blockCover C S).comp (ggQTwoXInLU_suEquiv C S).toMonoidHom

theorem ggQTwoXInLU_blockCoverSU_range {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (S : Finset (Fin (n + 1))) :
    (ggQTwoXInLU_blockCoverSU C S).range = (TableBUE.blockSU (K := K) (n := 1) S).map C.φ := by
  unfold ggQTwoXInLU_blockCoverSU
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (ggQTwoXInLU_suEquiv C S).surjective, Subgroup.map_top,
    ggQTUa_psiS_range]

private lemma ggQTUa_omega_cube {n : ℕ} {K : Type} [Field K] [Finite K]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) : C.ω ^ 3 = 1 := by
  have hcardU : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, C.field.card]
    norm_num
  have h := pow_card_eq_one' (x := C.ω)
  rwa [hcardU] at h

private lemma ggQTUa_diagHom_isDiag {d : ℕ} {K : Type} [Field K] (t : Fin d → Kˣ) :
    ggIsDiagMat (diagHom d t) :=
  ⟨fun a => (t a : K), coe_diagHom t⟩

private lemma ggQTUa_diagHom_isUnitary {d : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2] (ω : Kˣ) (hω3 : ω ^ 3 = 1) (v : Fin d → ZMod 3) :
    ggIsUnitaryMat (p := 2) (f := 1) (diagHom d (fun a => ω ^ (v a).val)) := by
  have hω3K : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  unfold ggIsUnitaryMat
  rw [coe_diagHom, conjTr, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have hfun : (fun i => unitaryInvolution K 2 1 (↑(ω ^ (v i).val)) * ↑(ω ^ (v i).val)) =
      fun _ => (1 : K) := by
    funext i
    rw [unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 from rfl, Units.val_pow_eq_pow_val,
      ← pow_mul, ← pow_add, show (v i).val * 2 + (v i).val = 3 * (v i).val by ring, pow_mul,
      hω3K, one_pow]
  rw [hfun, Matrix.diagonal_one]

theorem ggQTwoXInLU_blockCover_actsDiag {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (S : Finset (Fin (n + 1))) :
    GGActsDiagonally (p := 2) (f := 1) (ggQTwoXInLU_blockCoverSU C S) Bs := by
  classical
  intro b hb
  let v : Fin (n + 1) → ZMod 3 :=
    fun i => (C.ι (Additive.ofMul ⟨b, hb⟩) : Fin (n + 1) → ZMod 3) i
  let t : Fin S.card → Kˣ := fun a => C.ω ^ (v (S.equivFin.symm a)).val
  let g : GL (Fin S.card) K := diagHom S.card t
  have hω3K : (C.ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ggQTUa_omega_cube C, Units.val_one]
  have ht3 : ∀ a, (t a : K) ^ (2 ^ 1 + 1) = 1 := by
    intro a
    show ((C.ω ^ (v (S.equivFin.symm a)).val : Kˣ) : K) ^ (2 ^ 1 + 1) = 1
    rw [show (2 : ℕ) ^ 1 + 1 = 3 from rfl, Units.val_pow_eq_pow_val, ← pow_mul,
      mul_comm, pow_mul, hω3K, one_pow]
  refine ⟨g, ggQTUa_diagHom_isDiag t,
    ggQTUa_diagHom_isUnitary C.ω (ggQTUa_omega_cube C) (fun a => v (S.equivFin.symm a)), ?_⟩
  intro x
  let X : Matrix (Fin S.card) (Fin S.card) K :=
    (((ggQTwoXInLU_suEquiv C S x : ↥(unitarySU 2 1 K S.card)) : GL (Fin S.card) K) :
      Matrix (Fin S.card) (Fin S.card) K)
  let yU : ↥(unitarySU 2 1 K S.card) :=
    ⟨g * ((ggQTwoXInLU_suEquiv C S x : ↥(unitarySU 2 1 K S.card)) : GL (Fin S.card) K) * g⁻¹,
      SURep.conj_mem_unitarySU C.field ht3 (ggQTwoXInLU_suEquiv C S x).2⟩
  let y : Su K 2 1 S.card := (ggQTwoXInLU_suEquiv C S).symm yU
  have hy : ggQTwoXInLU_suEquiv C S y = yU := MulEquiv.apply_symm_apply _ _
  refine ⟨y, ?_, ?_⟩
  · change ((ggQTwoXInLU_suEquiv C S y : ↥(unitarySU 2 1 K S.card)) : GL (Fin S.card) K) =
      g * (x : GL (Fin S.card) K) * g⁻¹
    rw [hy]
    rfl
  · obtain ⟨s, hsmat, hsφ⟩ := C.diag ⟨b, hb⟩
    rw [show b = C.φ s from hsφ.symm]
    simp only [ggQTwoXInLU_blockCoverSU, ggQTwoXInLU_blockCover, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    have hD : ((s : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        Matrix.diagonal (fun i => (C.ω ^ (v i).val : K)) := by
      rw [hsmat, coe_diagHom]
      simp only [Units.val_pow_eq_pow_val]
      rfl
    have hconj := CFSG.StandardType.blockExt_conj_diagonal (S := S)
      (D := (s : GL (Fin (n + 1)) K)) (t := fun i => (C.ω ^ (v i).val : K)) hD X
    have hyUmat : ((yU : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
        Matrix.diagonal (fun a => (t a : K)) * X *
          Matrix.diagonal (fun a => ((t a : K))⁻¹) := by
      change (((g * ((ggQTwoXInLU_suEquiv C S x : ↥(unitarySU 2 1 K S.card)) : GL (Fin S.card) K) *
        g⁻¹ : GL (Fin S.card) K)) : Matrix (Fin S.card) (Fin S.card) K) = _
      rw [show g = diagHom S.card t from rfl]
      change ((diagHom S.card t : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) * X *
          (((diagHom S.card t)⁻¹ : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) = _
      rw [LineU.coe_inv_diag (coe_diagHom t), coe_diagHom]
    change ((s : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        TableBUE.blockExt S X *
        ((((s : ↥(unitarySU 2 1 K (n + 1)))⁻¹ : ↥(unitarySU 2 1 K (n + 1))) : GL
          (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      TableBUE.blockExt S ((yU : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K)
    rw [Subgroup.coe_inv, hyUmat]
    exact hconj

private lemma ggQTUa_psiS_ker_eq_bot {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (c : Fin (n + 1)) :
    (ggQTwoXInLU_blockCover C (Finset.univ.erase c)).ker = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  have hzker : TableBUE.blockExtSU (Finset.univ.erase c) C.field z ∈ C.φ.ker := by
    rw [MonoidHom.mem_ker]
    exact hz
  have hzcent : TableBUE.blockExtSU (Finset.univ.erase c) C.field z ∈
      Subgroup.center ↥(unitarySU 2 1 K (n + 1)) := C.ker_le hzker
  have hcomm : ∀ g ∈ unitarySU 2 1 K (n + 1),
      ((TableBUE.blockExtSU (Finset.univ.erase c) C.field z :
        ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) * g =
      g * ((TableBUE.blockExtSU (Finset.univ.erase c) C.field z :
        ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) := by
    intro g hg
    simpa using congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcent) ⟨g, hg⟩).symm
  have hscal := TableBUE.mem_scalars_of_commute (n := 1) (p := 3) (d := n + 1) C.field
    Nat.prime_three (by norm_num : 3 ∣ 2 ^ 1 + 1) hcomm
  obtain ⟨mu, hmu⟩ := hscal
  have hNmat : (((TableBUE.blockExtSU (Finset.univ.erase c) C.field z :
      ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      TableBUE.blockExt (Finset.univ.erase c)
        (((z : GL (Fin (Finset.univ.erase c).card) K)) :
          Matrix (Fin (Finset.univ.erase c).card) (Fin (Finset.univ.erase c).card) K) :=
    TableBUE.coe_blockExtSU (S := Finset.univ.erase c) (h := C.field) z
  have hcc : (((TableBUE.blockExtSU (Finset.univ.erase c) C.field z :
      ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c = 1 := by
    rw [hNmat]
    simp [TableBUE.blockExt]
  rw [← hmu] at hcc
  have hcc' : (↑mu : K) = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply_eq, Matrix.scalar_apply]
      using hcc
  have hmu1 : mu = 1 := Units.ext hcc'
  have hz1 : ((TableBUE.blockExtSU (Finset.univ.erase c) C.field z :
      ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) = 1 := by
    rw [← hmu, hmu1, map_one]
  exact TableBUE.blockExtSU_injective (S := Finset.univ.erase c) (h := C.field) (by
    apply Subtype.ext
    rw [hz1, map_one]
    rfl)

private lemma ggQTUa_psiSU_ker_le_center {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (c : Fin (n + 1)) :
    (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)).ker ≤
      Subgroup.center (Su K 2 1 (Finset.univ.erase c).card) := by
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  have hz' : ggQTwoXInLU_suEquiv C (Finset.univ.erase c) z ∈
      (ggQTwoXInLU_blockCover C (Finset.univ.erase c)).ker := by
    rw [MonoidHom.mem_ker]
    change (ggQTwoXInLU_blockCover C (Finset.univ.erase c))
      (ggQTwoXInLU_suEquiv C (Finset.univ.erase c) z) = 1
    exact hz
  rw [ggQTUa_psiS_ker_eq_bot C c] at hz'
  have hz1 : ggQTwoXInLU_suEquiv C (Finset.univ.erase c) z = 1 := Subgroup.mem_bot.mp hz'
  have hz2 : z = 1 := (ggQTwoXInLU_suEquiv C (Finset.univ.erase c)).injective (by rw [hz1, map_one])
  rw [hz2]
  exact Subgroup.one_mem _

theorem ggQTwoXInLU_blockCover_localHyp {n : ℕ} {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2]
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) (c : Fin (n + 1))
    (hcent : Nat.card ↥(B ⊓ Subgroup.centralizer
      (((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase c)).map C.φ : Subgroup G) :
        Set G)) = 3) (hn6 : 6 ≤ n) :
    GGNSLocalHyp 3 B Bs K 1 (Finset.univ.erase c).card
      (ggQTwoXInLU_blockCoverSU C (Finset.univ.erase c)) := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hcard : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [C.field.card]
    norm_num
  have hfour : 4 ≤ (Finset.univ.erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    simp
    omega
  exact ⟨Nat.prime_three, by norm_num, hcard, by norm_num, hfour,
    ggQTUa_psiSU_ker_le_center C c, hcfg.2.1, ggNSPosPD_routeCfg_rank hcfg, Or.inr hstar.1,
    by rw [ggQTwoXInLU_blockCoverSU_range]; exact hcent, hS.1.2.2.2.1, fun b hb => by
      obtain ⟨g, -, hg⟩ := ggQTwoXInLU_blockCover_actsDiag C (Finset.univ.erase c) b hb
      exact ⟨g, hg⟩⟩

end CFSG.StandardType

end
