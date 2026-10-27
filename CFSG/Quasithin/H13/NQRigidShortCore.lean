module

public import CFSG.Quasithin.H13.NQRigidShortSection
public import CFSG.Quasithin.H13.NQRigidShortMax
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMinPBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatMinPImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatMinPK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatMinPCampbell
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockCanon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockCComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockCommute
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelMinPImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelW
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelSum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockType
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockCommute
public import CFSG.Quasithin.H13.NQRigidShortTools

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.BlueprintB2 (centerTorsion mem_centerTorsion_iff)
open CFSG.QuasithinUnique.Setup.Family (IsComp IsBestOffender)
open scoped Pointwise MatrixGroups IsMulCommutative

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem cpu_short_of_setup
    {L S M : Subgroup Γ} (hchar : CFSG.IsCharacteristicP 2 Γ) (hS2 : IsPGroup 2 S)
    (hQS : CFSG.pCore 2 Γ ≤ S) (hLn : L.Normal) (hLS : (L : Set Γ) * (S : Set Γ) = Set.univ)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L))
    (hLperf : Group.IsPerfect ↥L) (hLM : ¬ L ≤ M)
    (hM : ∀ D : Subgroup ↥S, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map S.subtype : Subgroup Γ) : Set Γ) ≤ M)
    {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (eJ : (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L) ⧸
      center (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L) ≃* SL(2, F)) :
    CFSG.QuasithinUnique.IsShort2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup Γ := centerTorsion 2 (CFSG.pCore 2 Γ) with hV
  have hVn : V.Normal := CFSG.QuasithinUnique.Setup.normal_centerTorsion_pCore 2
  set ρ : Γ →* MulAut ↥V := MulAut.conjNormal with hρ
  have hρapp : ∀ (g : Γ) (v : ↥V), ((ρ g v : ↥V) : Γ) = g * v * g⁻¹ :=
    fun g v => MulAut.conjNormal_apply g v
  obtain ⟨hred, -, hQC, hCZ, hcop, -, -, hJV, A, -, hAne, hAel, hAbest⟩ :=
    NQBlock.characteristic_normalizer_control_produces_central_core_best_offender hchar hS2 hQS
      hLn hLS hLq hLM hM hV ρ hρapp
  obtain ⟨hVn', hVe, hVO⟩ := hred
  have : IsMulCommutative ↥V := hVe.toIsMulCommutative
  have hVv : ∀ v : ↥V, v * v = 1 := by
    intro v
    rw [← pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hVe.exponent_dvd_p v
  have hGLS : ∀ g : Γ, ∃ l ∈ L, ∃ s ∈ S, l * s = g := by
    intro g
    have hg : g ∈ (L : Set Γ) * (S : Set Γ) := hLS ▸ Set.mem_univ g
    obtain ⟨l, hl, s, hs, hls⟩ := hg
    exact ⟨l, hl, s, hs, hls⟩
  have hLStop : L ⊔ S = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨l, hl, s, hs, rfl⟩ := hGLS g
    exact mul_mem (mem_sup_left hl) (mem_sup_right hs)
  have hkerLb : ((QuotientGroup.mk' (CFSG.pCore 2 Γ)).subgroupMap L).ker =
      (CFSG.pCore 2 Γ).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 Γ) (x : Γ) = 1 := congrArg Subtype.val h
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    · intro h
      apply Subtype.ext
      show QuotientGroup.mk' (CFSG.pCore 2 Γ) (x : Γ) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h
  let θ : (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L) ≃* ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))) :=
    (QuotientGroup.quotientMulEquivOfEq hkerLb.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk' (CFSG.pCore 2 Γ)).subgroupMap_surjective L))
  have hLbq : CFSG.IsQuasisimple ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv θ hLq
  have hZb : center ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))) = ⊥ :=
    CFSG.QuasithinUnique.Setup.Lift.center_eq_bot_of_odd_central_extension hF hLbq.1
      ((centerQuotEquivOfMulEquiv θ).symm.trans eJ) (Nat.coprime_two_right.mp hcop)
  have hZJ : center (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L) = ⊥ := by
    have h := CFSG.QuasithinUnique.Setup.Lift.center_map_equiv θ
    rw [hZb] at h
    exact (map_eq_bot_iff_of_injective _ θ.injective).mp h
  have hCQ : centralizer (V : Set Γ) = CFSG.pCore 2 Γ := by
    refine le_antisymm (fun c hc => ?_) hQC
    have h1 := hCZ (mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 Γ)) hc)
    rw [hZb, Subgroup.map_bot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have : IsSimpleGroup ((↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L) ⧸
      center (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L)) := hLq.2.1
  have hSLs : IsSimpleGroup SL(2, F) := eJ.symm.isSimpleGroup
  have hnc : ∃ a b : SL(2, F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLq.2.2
    exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hO2 := eq_bot_of_normal_of_isPGroup_range hVO
  have hGL : ρ.range ≤ normalizer ((L.map ρ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    rintro _ ⟨b, rfl⟩
    exact le_normalizer_map ρ ⟨b, normalizer_eq_top_iff.mpr hLn ▸ mem_top b, rfl⟩
  have hLG : L.map ρ ≤ ρ.range := map_le_range ρ L
  have hPG : S.map ρ ≤ ρ.range := map_le_range ρ S
  have hP₀2 : IsPGroup 2 (S.map ρ) := hS2.map ρ
  have hGLP : ∀ g ∈ ρ.range, ∃ l ∈ L.map ρ, ∃ s ∈ S.map ρ, g = l * s := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := hGLS b
    exact ⟨ρ k, mem_map_of_mem ρ hk, ρ r, mem_map_of_mem ρ hr, map_mul ρ k r⟩
  have hkerL0 : (ρ.subgroupMap L).ker = (CFSG.pCore 2 Γ).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hCQ]
    constructor
    · intro h
      exact (conjNormal_eq_one_iff (x : Γ)).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((conjNormal_eq_one_iff (x : Γ)).mpr h)
  let eL₀ : ↥(L.map ρ) ≃* (↥L ⧸ (CFSG.pCore 2 Γ).subgroupOf L) :=
    (QuotientGroup.quotientKerEquivOfSurjective _ (ρ.subgroupMap_surjective L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerL0)
  let α₀ : ↥(L.map ρ) ≃* SL(2, F) :=
    eL₀.trans (QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZJ.symm).trans eJ))
  have hL₀q : CFSG.IsQuasisimple ↥(L.map ρ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eL₀.symm hLq
  have hcomp : IsComp (L.map ρ) ρ.range := by
    refine ⟨hLG, CFSG.Open.IsSubnormal.step hLG
      ((normal_subgroupOf_iff_le_normalizer hLG).mpr hGL) (CFSG.Open.IsSubnormal.refl _), ?_⟩
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hL₀q)
  have : IsSimpleGroup ↥(L.map ρ) := α₀.isSimpleGroup
  have hZL₀ : center ↥(L.map ρ) = ⊥ := center_eq_bot_of_isSimpleGroup (by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨α₀.symm a, α₀.symm b, fun h => hab (by simpa using congrArg α₀ h)⟩)
  have hE := eq_one_of_mem_centralizer hO2 hGL hP₀2 hPG hGLP hZL₀
  have hB₀P : (A.map S.subtype).map ρ ≤ S.map ρ := map_mono (map_subtype_le A)
  obtain ⟨X, hXB₀, hXbest, hLX⟩ :=
    exists_bestOffender_le hO2 hGL hP₀2 hPG hGLP hB₀P hAne hAel hAbest
  obtain ⟨hXL, hXcard⟩ := offender_le_of_sl2_component hVv hcomp hXbest hLX hE hn hF hnc α₀
  obtain ⟨hUcard, hidx, hPU, hmaxU⟩ :=
    sylow_max_of_sl2_normal hLG hGL hPG hP₀2 hGLP hF α₀ hXL (hXB₀.trans hB₀P) hXcard
  have hU1 : (S.map ρ ⊓ L.map ρ : Subgroup (MulAut ↥V)) ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hUcard
    have h1 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  have hP1 : S.map ρ ≠ ⊥ := fun h => hXbest.2.1 (eq_bot_iff.mpr ((hXB₀.trans hB₀P).trans h.le))
  have hker : ρ.ker ≤ S := fun x hx =>
    hQS (hCQ ▸ (conjNormal_eq_one_iff x).mp (MonoidHom.mem_ker.mp hx))
  obtain ⟨hSsyl, hSnn, hSmax⟩ := sylow_max_of_image ρ hS2 hker hO2 (hP₀2.to_le inf_le_left)
    (inf_le_left.trans hPG) hU1 hidx hPU hmaxU hP1
  have hAut : autOn (⊤ : Subgroup Γ) V = ρ.range := autOn_top_eq_range
  have hcomp' : IsComp (L.map ρ) (autOn (⊤ : Subgroup Γ) V) := hAut ▸ hcomp
  have hset : CFSG.QuasithinUnique.Setup.Lift.EvenSL2Setting (⊤ : Subgroup Γ) S
      ((normalizer ((S.map ρ ⊓ L.map ρ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V))).comap ρ)
      V n F := by
    refine ⟨by omega, by rw [Nat.card_eq_fintype_card, hF], hSsyl, hSnn, hSmax,
      isTwoReducedIn_top hVe hVO, ?_,
      CFSG.QuasithinUnique.Setup.Top.not_isSolvable_of_isComp hcomp', ⟨L.map ρ, hcomp', ⟨?_⟩⟩⟩
    · rw [← CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ, commutator_comm]
      exact hJV
    · exact (QuotientGroup.quotientMulEquivOfEq hZL₀).trans (QuotientGroup.quotientBot.trans α₀)
  have hcharTop := charTwo_top_of_isCharacteristicP hchar
  have hLc : CFSG.QuasithinUnique.Setup.Lift.IsCompList (autOn (⊤ : Subgroup Γ) V) 1
      (fun _ => L.map ρ) := hAut ▸ isCompList_one hcomp hE
  have hout := QuasithinUnique.Setup.Lift.actual_block_production_of_canonical
      (QuasithinUnique.Setup.Lift.natural_canonical_of_decomp
          QuasithinUnique.Setup.Lift.blockTransferProp QuasithinUnique.Setup.Lift.natVleSProp
          QuasithinUnique.Setup.Lift.natBaseProp QuasithinUnique.Setup.Lift.natYProp
          QuasithinUnique.Setup.Lift.natMinPBasicProp QuasithinUnique.Setup.Lift.natMinPImageProp
          QuasithinUnique.Setup.Lift.natMinPKProp QuasithinUnique.Setup.Lift.natMinPCampbellProp
          QuasithinUnique.Setup.Lift.natResidualProp QuasithinUnique.Setup.Lift.natAdapterProp
          QuasithinUnique.Setup.Lift.natQProp QuasithinUnique.Setup.Lift.natGenProp
          QuasithinUnique.Setup.Lift.natSumProp QuasithinUnique.Setup.Lift.natKernelProp
          QuasithinUnique.Setup.Lift.natCanonicalProp
          QuasithinUnique.Setup.Lift.natBlockTransportProp QuasithinUnique.Setup.Lift.natCCompProp
          QuasithinUnique.Setup.Lift.natCommuteProp)
      (QuasithinUnique.Setup.Lift.deleted_canonical_of_decomp
          QuasithinUnique.Setup.Lift.blockTransferProp QuasithinUnique.Setup.Lift.delBaumannProp
          QuasithinUnique.Setup.Lift.delBaseProp QuasithinUnique.Setup.Lift.delSeedProp
          QuasithinUnique.Setup.Lift.delH0Prop QuasithinUnique.Setup.Lift.delMinPBasicProp
          QuasithinUnique.Setup.Lift.delMinPImageProp QuasithinUnique.Setup.Lift.delWProp
          QuasithinUnique.Setup.Lift.delResidualProp QuasithinUnique.Setup.Lift.delAdapterProp
          QuasithinUnique.Setup.Lift.delQProp QuasithinUnique.Setup.Lift.delGenProp
          QuasithinUnique.Setup.Lift.delSumProp QuasithinUnique.Setup.Lift.delKernelProp
          QuasithinUnique.Setup.Lift.delBlockImageProp QuasithinUnique.Setup.Lift.delBlockCoreProp
          QuasithinUnique.Setup.Lift.delBlockTypeProp QuasithinUnique.Setup.Lift.delBlockGenProp
          QuasithinUnique.Setup.Lift.delBlockCommuteProp) Γ (⊤ : Subgroup Γ) S _ V n F hset hcharTop
    (not_le_normalizer_of_char_baum hLM hM) 1 (fun _ => L.map ρ) hLc
  have hodd := hout.product.1
  rw [iSup_const] at hodd
  have hSN : S ≤ normalizer (L : Set Γ) := (normalizer_eq_top_iff.mpr hLn).ge.trans' le_top
  have hL : CFSG.QuasithinUnique.Setup.oddOrderSubgroup (⊤ : Subgroup Γ) = L := by
    rw [← hLStop]
    exact CFSG.QuasithinUnique.Setup.Lift.oddOrderSubgroup_sup_eq hLperf hS2 hSN
  have hchi := hout.chi0 0
  rw [← hodd, hL] at hchi
  exact hchi.1.1

end CFSG.Quasithin.H13.NQRigid
