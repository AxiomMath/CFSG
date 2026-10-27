module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofCtr
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.Reducible
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Comp
public import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec18.Rem187
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

@[expose] def Step166KCommD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ U ∈ scriptQ A (lB A), U ≤ Subgroup.centralizer ({d} : Set G) →
      ⁅⁅U, Subgroup.zpowers c⁆, lB A (Subgroup.closure {c, d})⁆ ≤
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G))

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem commutator_lB_le_pCoreOf (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hKd : Step166KCommD) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {P : Subgroup G} (hPQ : P ∈ scriptQ A (lB A))
    (hPd : ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G)) :
    ⁅⁅P, Subgroup.zpowers c⁆, lB A (Subgroup.closure {c, d})⁆ ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G) with hC
  set U : Subgroup G := P ⊓ C with hU
  have hcA : c ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hAc : A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩)
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (mem_scriptQ_iff.mp hPQ).2.1
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hAP (hAc.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUQ : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hPQ inf_le_left hAU
  have hUC : U ≤ Subgroup.centralizer ({d} : Set G) := inf_le_right
  have hPcop : Nat.Coprime 3 (Nat.card P) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three P).mp (mem_scriptQ_iff.mp hPQ).1)
  have hcp : IsPGroup 3 (Subgroup.zpowers c) :=
    h.isE27.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA)
  have hcP : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans hAP
  have hidem : ⁅⁅P, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ = ⁅P, Subgroup.zpowers c⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent
      3 Nat.prime_three (Subgroup.zpowers c) P hcp hcP hPcop
  have hle : ⁅P, Subgroup.zpowers c⁆ ≤ U :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hcP) hPd
  have heq : ⁅P, Subgroup.zpowers c⁆ = ⁅U, Subgroup.zpowers c⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_mono inf_le_left le_rfl)
    calc ⁅P, Subgroup.zpowers c⁆ = ⁅⁅P, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ := hidem.symm
      _ ≤ ⁅U, Subgroup.zpowers c⁆ := Subgroup.commutator_mono hle le_rfl
  rw [heq]
  exact hKd G A c L Y₀ h hJ d hdA hd1 hdc U hUQ hUC

private theorem eq_sup_pCoreOf_perfectResidual {C V L₀ : Subgroup G}
    (hLC : L₀ ≤ C) (hVC : V ≤ C) (hCV : C ≤ Subgroup.normalizer (V : Set G))
    (hV2 : IsPGroup 2 V) (hLp : Group.IsPerfect ↥L₀) :
    inSubgroup perfectResidual (L₀ ⊔ V) =
      L₀ ⊔ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual (L₀ ⊔ V)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := L₀ ⊔ V with hN
  set X : Subgroup G := inSubgroup perfectResidual N with hX
  have hXN : X ≤ N := Subgroup.map_subtype_le _
  have hLX : L₀ ≤ X := KFacts.le_inSubgroup_perfectResidual hLp le_sup_left
  have hXC : X ≤ C := hXN.trans (sup_le hLC hVC)
  have hXV : X ⊓ V ≤ CFSG.Open.pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      (hV2.to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (hXC.trans hCV)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hded : X ≤ L₀ ⊔ V ⊓ X := by
    intro x hx
    have hxN : x ∈ L₀ ⊔ V := hXN hx
    have hmul : x ∈ ((L₀ : Set G) * (V : Set G)) := by
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right L₀ V (hLC.trans hCV)]
    obtain ⟨l, hl, v, hv, rfl⟩ := hmul
    have hvX : v ∈ X := by
      have h1 : l⁻¹ * (l * v) ∈ X := X.mul_mem (X.inv_mem (hLX hl)) hx
      simpa using h1
    exact Subgroup.mul_mem_sup hl
      (Subgroup.mem_inf.mpr ⟨hv, hvX⟩)
  have hsup : X ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 X := by
    calc X ≤ L₀ ⊔ V ⊓ X := hded
      _ = L₀ ⊔ X ⊓ V := by rw [inf_comm]
      _ ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 X := sup_le_sup_left hXV _
  exact le_antisymm hsup (sup_le hLX (CFSG.LieType.BorelTits.pCoreOf_le 2 X))

private theorem inf_pCoreOf_perfectResidual_eq {C V L₀ : Subgroup G}
    (hLC : L₀ ≤ C) (hVC : V ≤ C) (hCV : C ≤ Subgroup.normalizer (V : Set G))
    (hV2 : IsPGroup 2 V) (hLp : Group.IsPerfect ↥L₀) :
    L₀ ⊓ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual (L₀ ⊔ V)) =
      CFSG.Open.pCoreOf 2 L₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := inSubgroup perfectResidual (L₀ ⊔ V) with hX
  have hLX : L₀ ≤ X := KFacts.le_inSubgroup_perfectResidual hLp le_sup_left
  have hXsup : X = L₀ ⊔ CFSG.Open.pCoreOf 2 X :=
    eq_sup_pCoreOf_perfectResidual hLC hVC hCV hV2 hLp
  refine le_antisymm (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLX) (le_inf ?_ ?_)
  · exact CFSG.LieType.BorelTits.pCoreOf_le 2 L₀
  · exact Sec18.pCoreOf_le_pCoreOf_of_eq_sup hLX hXsup

private theorem nonempty_quotient_pCore_equiv_perfectResidual {C V L₀ : Subgroup G}
    (hLC : L₀ ≤ C) (hVC : V ≤ C) (hCV : C ≤ Subgroup.normalizer (V : Set G))
    (hV2 : IsPGroup 2 V) (hLp : Group.IsPerfect ↥L₀) :
    Nonempty ((↥(inSubgroup perfectResidual (L₀ ⊔ V)) ⧸
        CFSG.pCore 2 ↥(inSubgroup perfectResidual (L₀ ⊔ V))) ≃*
      (↥L₀ ⧸ CFSG.pCore 2 ↥L₀)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := inSubgroup perfectResidual (L₀ ⊔ V) with hX
  set OX : Subgroup G := CFSG.Open.pCoreOf 2 X with hOX
  have hLX : L₀ ≤ X := KFacts.le_inSubgroup_perfectResidual hLp le_sup_left
  have hXsup : X = L₀ ⊔ OX := eq_sup_pCoreOf_perfectResidual hLC hVC hCV hV2 hLp
  have hInt : L₀ ⊓ OX = CFSG.Open.pCoreOf 2 L₀ :=
    inf_pCoreOf_perfectResidual_eq hLC hVC hCV hV2 hLp
  have hnorm : L₀ ≤ Subgroup.normalizer (OX : Set G) :=
    hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hsubL : OX.subgroupOf L₀ = CFSG.pCore 2 ↥L₀ := by
    ext z
    constructor
    · intro hz
      have hz' : (z : G) ∈ L₀ ⊓ OX := ⟨z.2, Subgroup.mem_subgroupOf.mp hz⟩
      rw [hInt] at hz'
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz'
      rw [← Subtype.ext hwz]
      exact hw
    · intro hz
      have hz' : (z : G) ∈ L₀ ⊓ OX := by
        rw [hInt]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hz'.2
  have hsubX : OX.subgroupOf X = CFSG.pCore 2 ↥X := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hz)
      rw [← Subtype.ext hwz]
      exact hw
    · intro hz
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
  have hPle : OX ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hPXn : X ≤ Subgroup.normalizer (OX : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  letI : (OX.subgroupOf L₀).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  letI : (OX.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPXn
  let ψ : ↥L₀ →* (↥X ⧸ OX.subgroupOf X) :=
    (QuotientGroup.mk' (OX.subgroupOf X)).comp (Subgroup.inclusion hLX)
  have hker : ψ.ker = OX.subgroupOf L₀ := by
    ext z
    constructor
    · intro hz
      have h1 : ((Subgroup.inclusion hLX z : ↥X) : G) ∈ OX :=
        Subgroup.mem_subgroupOf.mp
          ((QuotientGroup.eq_one_iff (Subgroup.inclusion hLX z)).mp hz)
      exact Subgroup.mem_subgroupOf.mpr h1
    · intro hz
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hLX z)).mpr
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz))
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (OX.subgroupOf X) q
    have hx : (x : G) ∈ L₀ ⊔ OX := hXsup ▸ x.2
    have hmul : (x : G) ∈ ((L₀ : Set G) * (OX : Set G)) := by
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right L₀ OX hnorm]
    obtain ⟨l, hl, o, ho, hlo⟩ := hmul
    have hoX : o ∈ X := hPle ho
    have ho1 : QuotientGroup.mk' (OX.subgroupOf X) (⟨o, hoX⟩ : ↥X) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ho)
    have hxeq : x = (⟨l, hLX hl⟩ : ↥X) * ⟨o, hoX⟩ := by
      ext
      simpa using hlo.symm
    refine ⟨⟨l, hl⟩, ?_⟩
    show QuotientGroup.mk' (OX.subgroupOf X) (Subgroup.inclusion hLX ⟨l, hl⟩) =
      QuotientGroup.mk' (OX.subgroupOf X) x
    rw [hxeq, map_mul, ho1, mul_one]
    rfl
  have e₁ : (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) ≃* (↥L₀ ⧸ ψ.ker) :=
    (QuotientGroup.quotientMulEquivOfEq hsubL.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker.symm)
  have e₂ : (↥L₀ ⧸ ψ.ker) ≃* (↥X ⧸ OX.subgroupOf X) :=
    (QuotientGroup.quotientKerEquivRange ψ).trans
      ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv)
  have e₃ : (↥X ⧸ OX.subgroupOf X) ≃* (↥X ⧸ CFSG.pCore 2 ↥X) :=
    QuotientGroup.quotientMulEquivOfEq hsubX
  exact ⟨((e₁.trans e₂).trans e₃).symm⟩

private theorem map_conj_le_normalizer_of_le {H X : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (X : Set G))
    (hH : H ≤ Subgroup.normalizer (X : Set G)) :
    H.map (MulAut.conj k).toMonoidHom ≤ Subgroup.normalizer (X : Set G) := by
  have hkX : X.map (MulAut.conj k).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hk
  have hk'X : X.map (MulAut.conj k⁻¹).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (X : Set G)).inv_mem hk)
  intro q hq
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hhX : X.map (MulAut.conj h).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH hh)
  have hconj : MulAut.conj ((MulAut.conj k).toMonoidHom h) =
      MulAut.conj k * MulAut.conj h * (MulAut.conj k)⁻¹ := by
    rw [show (MulAut.conj k).toMonoidHom h = k * h * k⁻¹ from rfl, map_mul, map_mul, map_inv]
  have hcomp : ((MulAut.conj k * MulAut.conj h * (MulAut.conj k)⁻¹ : MulAut G) : G →* G) =
      ((MulAut.conj k).toMonoidHom.comp (MulAut.conj h).toMonoidHom).comp
        ((MulAut.conj k)⁻¹).toMonoidHom := by
    ext x
    show (MulAut.conj k * MulAut.conj h * (MulAut.conj k)⁻¹) x =
      (MulAut.conj k) ((MulAut.conj h) ((MulAut.conj k)⁻¹ x))
    rw [MulAut.mul_apply, MulAut.mul_apply]
  have hC : ((MulAut.conj k)⁻¹).toMonoidHom = (MulAut.conj k⁻¹).toMonoidHom := by
    rw [show (MulAut.conj k)⁻¹ = MulAut.conj k⁻¹ from (map_inv MulAut.conj k).symm]
  rw [hconj, hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hC, hk'X, hhX, hkX]

private theorem commutator_iSup_conj_le {K Z L V : Subgroup G}
    (hZL : Z ≤ Subgroup.centralizer (L : Set G))
    (hZV : Z ≤ Subgroup.normalizer (V : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hKL : ⁅K, L⁆ ≤ V) :
    ⁅(⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom), L⁆ ≤ V := by
  have hQ : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ≤
      Subgroup.normalizer (V : Set G) :=
    iSup_le fun k => map_conj_le_normalizer_of_le (hKV k.2) hZV
  refine Subgroup.commutator_le.mpr ?_
  intro q hq l hl
  have key : ∀ q ∈ (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom),
      q ∈ Subgroup.normalizer (V : Set G) ∧ ∀ l ∈ L, ⁅q, l⁆ ∈ V := by
    intro q hq
    refine Subgroup.iSup_induction (fun k : K => Z.map (MulAut.conj (k : G)).toMonoidHom)
      (C := fun q => q ∈ Subgroup.normalizer (V : Set G) ∧ ∀ l ∈ L, ⁅q, l⁆ ∈ V) hq ?_ ?_ ?_
    · intro k z hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      refine ⟨hQ (Subgroup.mem_iSup_of_mem k (Subgroup.mem_map_of_mem _ hz')), ?_⟩
      intro l hl
      have hconj : ⁅(MulAut.conj (k : G)).toMonoidHom z', l⁆ =
          (MulAut.conj (k : G)).toMonoidHom
            ⁅z', ((MulAut.conj (k : G))⁻¹).toMonoidHom l⁆ := by
        have h := conjugate_commutatorElement (g₁ := z')
          (g₂ := ((MulAut.conj (k : G))⁻¹).toMonoidHom l) (g₃ := (k : G))
        have hk : (k : G) * ((MulAut.conj (k : G))⁻¹).toMonoidHom l * (k : G)⁻¹ = l := by
          rw [show (MulAut.conj (k:G))⁻¹ = MulAut.conj ((k:G)⁻¹) from
            (map_inv MulAut.conj (k:G)).symm]
          show (k:G) * ((k:G)⁻¹ * l * ((k:G)⁻¹)⁻¹) * (k:G)⁻¹ = l
          group
        rw [hk] at h
        exact h.symm
      rw [hconj]
      have hl1 : ((MulAut.conj (k : G))⁻¹).toMonoidHom l = ⁅(k : G)⁻¹, l⁆ * l := by
        rw [show (MulAut.conj (k:G))⁻¹ = MulAut.conj ((k:G)⁻¹) from
          (map_inv MulAut.conj (k:G)).symm]
        rw [commutatorElement_def]
        show (k:G)⁻¹ * l * ((k:G)⁻¹)⁻¹ = ((k:G)⁻¹ * l * ((k:G)⁻¹)⁻¹ * l⁻¹) * l
        group
      have hl' : ((MulAut.conj (k : G))⁻¹).toMonoidHom l ∈ ((V : Set G) * (L : Set G)) := by
        rw [hl1]
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left V L hLV]
        exact mul_mem (Subgroup.mem_sup_left
          (hKL (Subgroup.commutator_mem_commutator (K.inv_mem k.2) hl)))
          (Subgroup.mem_sup_right hl)
      obtain ⟨v, hv, m, hm, hvm⟩ := hl'
      have hzv : ⁅z', v⁆ ∈ V := by
        have h1 : z' * v * z'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hZV hz') v).mp hv
        have h2 : ⁅z', v⁆ = (z' * v * z'⁻¹) * v⁻¹ := by
          rw [commutatorElement_def]
        rw [h2]
        exact V.mul_mem h1 (V.inv_mem hv)
      have hzm : ⁅z', m⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (hZL hz') m hm).symm
      have hcomm : ⁅z', ((MulAut.conj (k : G))⁻¹).toMonoidHom l⁆ = ⁅z', v⁆ := by
        rw [← hvm, commutatorElement_mul_right_eq_mul_conj, hzm]
        simp
      rw [hcomm]
      exact (Subgroup.mem_normalizer_iff.mp (hKV k.2) ⁅z', v⁆).mp hzv
    · refine ⟨Subgroup.one_mem _, fun l _ => ?_⟩
      rw [commutatorElement_one_left]
      exact V.one_mem
    · intro x y hx hy
      refine ⟨(Subgroup.normalizer (V : Set G)).mul_mem hx.1 hy.1, fun l hl => ?_⟩
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hx.1 (⁅y, l⁆)).mp (hy.2 l hl)) (hx.2 l hl)
  exact ((key q hq).2 l hl)

private theorem le_normalizer_iSup_conj {A K Z : Subgroup G}
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer
      ((⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    refine Subgroup.iSup_induction (fun k : K => Z.map (MulAut.conj (k : G)).toMonoidHom)
      (C := fun y => a * y * a⁻¹ ∈ ⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) hx ?_ ?_ ?_
    · intro k y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_iSup_of_mem
        (⟨a * (k : G) * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAK ha) (k : G)).mp k.2⟩ : K) ?_
      refine Subgroup.mem_map.mpr ⟨a * z * a⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hAZ ha) z).mp hz
      · show (a * (k : G) * a⁻¹) * (a * z * a⁻¹) * (a * (k : G) * a⁻¹)⁻¹ =
          a * (k * z * k⁻¹) * a⁻¹
        simp only [zpow_neg_one, Subgroup.coe_inv]
        group
    · simp
    · intro y z hy hz
      show a * (y * z) * a⁻¹ ∈ _
      rw [show a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) from by group]
      exact mul_mem hy hz
  · intro hx
    have hx' : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ ∈
        ⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom := by
      refine Subgroup.iSup_induction (fun k : K => Z.map (MulAut.conj (k : G)).toMonoidHom)
        (C := fun y => a⁻¹ * y * a⁻¹⁻¹ ∈
          ⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) hx ?_ ?_ ?_
      · intro k y hy
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_iSup_of_mem
          (⟨a⁻¹ * (k : G) * a⁻¹⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hAK (A.inv_mem ha)) (k : G)).mp k.2⟩ : K) ?_
        refine Subgroup.mem_map.mpr ⟨a⁻¹ * z * a⁻¹⁻¹, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hAZ (A.inv_mem ha)) z).mp hz
        · show (a⁻¹ * (k : G) * a⁻¹⁻¹) * (a⁻¹ * z * a⁻¹⁻¹) * (a⁻¹ * (k : G) * a⁻¹⁻¹)⁻¹ =
            a⁻¹ * (k * z * k⁻¹) * a⁻¹⁻¹
          simp only [zpow_neg_one, Subgroup.coe_inv, inv_inv]
          group
      · simp
      · intro y z hy hz
        show a⁻¹ * (y * z) * a⁻¹⁻¹ ∈ _
        rw [show a⁻¹ * (y * z) * a⁻¹⁻¹ = (a⁻¹ * y * a⁻¹⁻¹) * (a⁻¹ * z * a⁻¹⁻¹) from by group]
        exact mul_mem hy hz
    have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [h2] at hx'

private theorem oPrimeResidualOf_le_of_isPGroup_quotient {X Y : Subgroup G} (hXY : X ≤ Y)
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) [(X.subgroupOf Y).Normal]
    (h2 : IsPGroup 2 (↥Y ⧸ X.subgroupOf Y)) :
    oPrimeResidualOf 3 Y ≤ X := by
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have key : ∀ t : ↥Y, (∃ k, t ^ 3 ^ k = 1) → QuotientGroup.mk' (X.subgroupOf Y) t = 1 := by
    rintro t ⟨k, hk⟩
    have h1 : orderOf (QuotientGroup.mk' (X.subgroupOf Y) t) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    obtain ⟨j, hj⟩ := h2.exists_orderOf_dvd_pow (QuotientGroup.mk' (X.subgroupOf Y) t)
    have hcop : Nat.Coprime (3 ^ k) (2 ^ j) :=
      ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow k j
    have hone : orderOf (QuotientGroup.mk' (X.subgroupOf Y) t) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 hj)
    exact orderOf_eq_one_iff.mp hone
  have hkey : (oPrimeResidual 3 ↥Y).map (QuotientGroup.mk' (X.subgroupOf Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hq
    refine Subgroup.mem_bot.mpr ?_
    refine Subgroup.closure_induction
      (p := fun t _ => QuotientGroup.mk' (X.subgroupOf Y) t = 1)
      (fun u hu => ?_) ?_ (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_) ht
    · rcases hu with ⟨k, hk⟩
      exact key u ⟨k, hk⟩
    · exact map_one _
    · rw [map_mul, ha, hb, mul_one]
    · rw [map_inv, ha, inv_one]
  have hmem : QuotientGroup.mk' (X.subgroupOf Y) y' ∈
      (oPrimeResidual 3 ↥Y).map (QuotientGroup.mk' (X.subgroupOf Y)) :=
    Subgroup.mem_map_of_mem _ hy'
  rw [hkey, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y').mp hmem)

private theorem le_sup_inf_of_eq_perfectResidual {L V X : Subgroup G}
    (hX : X = inSubgroup perfectResidual (L ⊔ V)) (hLX : L ≤ X)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : X ≤ L ⊔ (X ⊓ V) := by
  subst hX
  intro x hx
  have hxN : x ∈ L ⊔ V := Subgroup.map_subtype_le _ hx
  have hmul : x ∈ ((L : Set G) * (V : Set G)) := by
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right L V hLV]
  obtain ⟨l, hl, v, hv, rfl⟩ := hmul
  have hvX : v ∈ inSubgroup perfectResidual (L ⊔ V) := by
    have h1 : l⁻¹ * (l * v) ∈ inSubgroup perfectResidual (L ⊔ V) :=
      (inSubgroup perfectResidual (L ⊔ V)).mul_mem
        ((inSubgroup perfectResidual (L ⊔ V)).inv_mem (hLX hl)) hx
    simpa using h1
  exact Subgroup.mul_mem_sup hl (Subgroup.mem_inf.mpr ⟨hvX, hv⟩)

private theorem mem_scriptY4_and_omg_of_tripleCover (h : Sec17Std G A c L Y₀)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) {L₀ X : Subgroup G}
    (hL₀d : L₀ ≤ Subgroup.centralizer ({d} : Set G)) (hL₀perf : Group.IsPerfect ↥L₀)
    (hAL₀ : A ≤ Subgroup.normalizer (L₀ : Set G)) (hL₀Δ : L₀ ≤ delta A (lB A) L₀)
    (hL₀6 : Sec4.IsTripleCover (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) (alternatingGroup (Fin 6)))
    (hX : X = inSubgroup perfectResidual
      (L₀ ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))) :
    X ∈ scriptY4 A (lB A) ∧ omg155 A X ∧
      X ≤ Subgroup.centralizer ({d} : Set G) ∧
      X ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ∧
      L₀ ≤ X ∧
      Subgroup.normalizer
          (L₀ ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) : Subgroup G) ≤
        Subgroup.normalizer (X : Set G) ∧
      Subgroup.centralizer ({d} : Set G) ≠ ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hGsimple : IsSimpleGroup G := h.isSimpleGroup
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  let V : Subgroup G := CFSG.Open.pCoreOf 2 C
  let N : Subgroup G := L₀ ⊔ V
  have hXN : X = inSubgroup perfectResidual N := hX
  subst hXN
  let X : Subgroup G := inSubgroup perfectResidual N
  have hAc : A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩)
  have hCV : C ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hVn : V ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hV3 : ¬ 3 ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := hV2.exists_card_eq
    rw [hn]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hLC : L₀ ≤ C := hL₀d
  have hCN : C ≠ ⊤ := by
    intro htop
    have hZbot : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨a, b, hab⟩ := h.nonabelian
        exact hab ((Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a) b).symm)
    have hdZ : d ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [hZbot, Subgroup.mem_bot] at hdZ
    exact hd1 hdZ
  have hXN' : X ≤ N := Subgroup.map_subtype_le _
  have hXC : X ≤ C := hXN'.trans (sup_le hLC hVn)
  have hXne : X ≠ ⊤ := fun h => hCN (top_le_iff.mp (h ▸ hXC))
  have hLX : L₀ ≤ X := KFacts.le_inSubgroup_perfectResidual hL₀perf le_sup_left
  have hXNF : Subgroup.normalizer (N : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual N
  have hXperf : Group.IsPerfect ↥X := by
    haveI : Group.IsPerfect ↥(perfectResidual ↥N) :=
      (CFSG.perfect_residual_characterization (G := ↥N)).2.2.1
    exact Group.IsPerfect.map N.subtype
  have hXsup : X = L₀ ⊔ CFSG.Open.pCoreOf 2 X :=
    eq_sup_pCoreOf_perfectResidual hLC hVn hCV hV2 hL₀perf
  have hXinf : L₀ ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 L₀ :=
    inf_pCoreOf_perfectResidual_eq hLC hVn hCV hV2 hL₀perf
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf hAL₀ (hAc.trans hCV)).trans (Subgroup.inf_normalizer_le_normalizer_sup L₀ V)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hAN.trans hXNF
  haveI hS6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (α := Fin 6) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hnc6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    by_contra hcontra
    push Not at hcontra
    haveI hcomm : IsMulCommutative ↥(alternatingGroup (Fin 6)) := ⟨⟨hcontra⟩⟩
    have hpr := (Group.is_simple_iff_prime_card (α := ↥(alternatingGroup (Fin 6)))).mp hS6
    rw [card_alternatingGroup_six] at hpr
    norm_num at hpr
  have hLq : CFSG.IsQuasisimple (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) := by
    obtain ⟨hz3, ⟨φ⟩⟩ := hL₀6
    have hperfU : Group.IsPerfect (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L₀))
        (QuotientGroup.mk'_surjective _)
    refine ⟨hperfU, φ.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hnc6
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by simpa using congrArg φ h)⟩
  have hO3L : oPrimeResidual 3 (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) = ⊤ :=
    Proof171Steps.oPrimeResidual_eq_top_of_isTripleCover hL₀6
      Proof171Steps.oPrimeResidual_alternatingGroup_six
  have hcardL : Nat.card (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) = 1080 := by
    obtain ⟨hz3, ⟨φ⟩⟩ := hL₀6
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L₀ ⧸ CFSG.pCore 2 ↥L₀))
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_six, hz3] at h
    simpa using h
  obtain ⟨eX⟩ := nonempty_quotient_pCore_equiv_perfectResidual hLC hVn hCV hV2 hL₀perf
  have hXq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) :=
    CFSG.IsQuasisimple.of_mulEquiv eX hLq
  have hcardX : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 1080 := by
    rw [Nat.card_congr eX.toEquiv, hcardL]
  have hO3X : oPrimeResidual 3 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊤ :=
    Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv eX hO3L
  have hXres : X = oPrimeResidualOf 3 X := by
    have hker : Group.IsSolvable ↥(QuotientGroup.mk' (CFSG.pCore 2 ↥X)).ker := by
      rw [QuotientGroup.ker_mk']
      haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥X) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).isNilpotent
      exact IsNilpotent.to_isSolvable
    have h := Proof171Steps.eq_oPrimeResidualOf_of_hom hXperf
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) hker ?_
    · exact h
    · have hrange : (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).range = ⊤ :=
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
      have htop : oPrimeResidual 3 (↥(⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X))) = ⊤ :=
        Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv Subgroup.topEquiv hO3X
      exact Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv
        (MulEquiv.subgroupCongr hrange) htop
  have hXVQ : X ⊓ V ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_of_le_of_normal hdA inf_le_right hVn hCV hV3 ?_
    exact (le_inf hAX (hAc.trans hCV)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hXΔ : X = delta A (lB A) X := by
    refine le_antisymm ?_ (delta_le X)
    calc X ≤ L₀ ⊔ (X ⊓ V) := le_sup_inf_of_eq_perfectResidual rfl hLX (hLC.trans hCV)
      _ ≤ delta A (lB A) X := sup_le (hL₀Δ.trans (delta_mono hLX)) (le_delta hXVQ inf_le_left)
  have hX4 : X ∈ scriptY4 A (lB A) := ⟨⟨hXne, hAX⟩, hXres, hXΔ, hXq⟩
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hΩ : omg155 A X := by
    left
    constructor
    · rintro ⟨n, -, hiso⟩
      exact not_isoLThreePi_of_card_small (Or.inr hcardX) 2 n hiso
    · refine ⟨fun e => ?_⟩
      have hc := Nat.card_congr e.toEquiv
      rw [hcardX, hA5card] at hc
      norm_num at hc
  exact ⟨hX4, hΩ, hXC, hXN', hLX, hXNF, hCN⟩

private theorem q_facts {d : G} {L₀ X Q K R Z : Subgroup G}
    (hQ : Q = ⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom)
    (hL₀d : L₀ ≤ Subgroup.centralizer ({d} : Set G))
    (hXC : X ≤ Subgroup.centralizer ({d} : Set G))
    (hXN : X ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))
    (hXNF : Subgroup.normalizer
        (L₀ ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) : Subgroup G) ≤
      Subgroup.normalizer (X : Set G))
    (hKQ : K ∈ scriptQ A (lB A)) (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hKL₀ : ⁅K, L₀⁆ ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))
    (hR2 : IsPGroup 2 R) (hRQ : R ∈ scriptQ A (lB A))
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hZR : Z ≤ R) (hZ1 : Z ≠ ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZL₀ : Z ≤ Subgroup.centralizer (L₀ : Set G))
    (hZd : Z ≤ Subgroup.centralizer ({d} : Set G)) :
    Q ∈ scriptQ A (lB A) ∧ IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
      Q ≤ Subgroup.centralizer ({d} : Set G) ∧
      A ≤ Subgroup.normalizer (Q : Set G) ∧
      K ≤ Subgroup.normalizer (Q : Set G) ∧
      K ≤ Subgroup.normalizer (X : Set G) ∧
      Q ≤ Subgroup.normalizer (X : Set G) ∧
      ⁅Q, X⁆ ≤ CFSG.Open.pCoreOf 2 X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  let V : Subgroup G := CFSG.Open.pCoreOf 2 C
  let N : Subgroup G := L₀ ⊔ V
  subst hQ
  have hZQ : Z ≤ ⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom := by
    intro z hz
    refine Subgroup.mem_iSup_of_mem (1 : K) ?_
    simpa using hz
  have hQne : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ≠ ⊥ :=
    fun h => hZ1 (le_bot_iff.mp (h ▸ hZQ))
  have hQR : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ≤ R := by
    refine iSup_le fun k => ?_
    calc Z.map (MulAut.conj (k : G)).toMonoidHom
        ≤ R.map (MulAut.conj (k : G)).toMonoidHom := Subgroup.map_mono hZR
      _ = R := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKR k.2)
  have hQ2 : IsPGroup 2 ((⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) : Subgroup G) :=
    hR2.to_le hQR
  have hQA : A ≤ Subgroup.normalizer
      (((⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) : Subgroup G) : Set G) :=
    le_normalizer_iSup_conj hAZ (mem_scriptQ_iff.mp hKQ).2.1
  have hQC : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ≤ C := by
    refine iSup_le fun k => ?_
    calc Z.map (MulAut.conj (k : G)).toMonoidHom
        ≤ C.map (MulAut.conj (k : G)).toMonoidHom := Subgroup.map_mono hZd
      _ = C := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((hKd.trans Subgroup.le_normalizer) k.2)
  have hQQ : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hRQ hQR hQA
  have hZV : Z ≤ Subgroup.normalizer (V : Set G) :=
    hZd.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)
  have hZL : Z ≤ Subgroup.normalizer (L₀ : Set G) :=
    hZL₀.trans (Subgroup.centralizer_le_normalizer _)
  have hZN : Z ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf hZL hZV).trans (Subgroup.inf_normalizer_le_normalizer_sup L₀ V)
  have hZX : Z ≤ Subgroup.normalizer (X : Set G) := hZN.trans hXNF
  have hKC : K ≤ C := hKd
  have hKV : K ≤ Subgroup.normalizer (V : Set G) :=
    hKC.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
    change K ≤ Subgroup.normalizer ((L₀ ⊔ V : Subgroup G) : Set G)
    rw [sup_comm]
    refine CFSG.Section9.le_normalizer_sup_of_le_normalizer_left_commutator_right_sec9 V L₀ K hKV ?_
    intro k hk l hl
    exact (Subgroup.commutator_comm (H₁ := K) (H₂ := L₀) ▸ hKL₀)
      (Subgroup.commutator_mem_commutator hl hk)
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := hKN.trans hXNF
  have hQX : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ≤
      Subgroup.normalizer (X : Set G) :=
    iSup_le fun k => map_conj_le_normalizer_of_le (hKX k.2) hZX
  have hKQn : K ≤ Subgroup.normalizer
      (((⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact CFSG.RankThree.PartTwo.Sec13.F135Last.r3c_conj_mem_orbit (S := Z) hk hy
    · intro hy
      have h := CFSG.RankThree.PartTwo.Sec13.F135Last.r3c_conj_mem_orbit (S := Z)
        (K.inv_mem hk) hy
      have h2 : k⁻¹ * (k * y * k⁻¹) * (k⁻¹)⁻¹ = y := by group
      rwa [h2] at h
  have hLV : L₀ ≤ Subgroup.normalizer (V : Set G) :=
    hL₀d.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)
  have hQV : (⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom) ≤
      Subgroup.normalizer (V : Set G) :=
    hQC.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)
  have hQVcomm : ⁅(⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom), V⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQV
  have hQL : ⁅(⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom), L₀⁆ ≤ V :=
    commutator_iSup_conj_le hZL₀ hZV hKV hLV hKL₀
  have hQNX : ⁅(⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom), X⁆ ≤ X := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQX
  have hQXV : ⁅(⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom), X⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr ?_
    intro q hq x hx
    have hxN : x ∈ L₀ ⊔ V := hXN hx
    have hmul : x ∈ ((L₀ : Set G) * (V : Set G)) := by
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right L₀ V hLV]
    obtain ⟨l, hl, v, hv, rfl⟩ := hmul
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅q, l⁆ ∈ V := hQL (Subgroup.commutator_mem_commutator hq hl)
    have h2 : ⁅q, v⁆ ∈ V := hQVcomm (Subgroup.commutator_mem_commutator hq hv)
    have h3 : l * ⁅q, v⁆ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hl) ⁅q, v⁆).mp h2
    simpa only [mul_assoc] using V.mul_mem h1 h3
  have hQO2 : ⁅(⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom), X⁆ ≤
      CFSG.Open.pCoreOf 2 X :=
    (le_inf hQNX hQXV).trans (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXC)
  exact ⟨hQQ, hQ2, hQne, hQC, hQA, hKQn, hKX, hQX, hQO2⟩

private theorem y_facts {X Q Y : Subgroup G} (hY : Y = X ⊔ Q)
    (hX4 : X ∈ scriptY4 A (lB A))
    (hQ : Q ∈ scriptQ A (lB A)) (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hQA : A ≤ Subgroup.normalizer (Q : Set G))
    (hQX : Q ≤ Subgroup.normalizer (X : Set G))
    (hQO2 : ⁅Q, X⁆ ≤ CFSG.Open.pCoreOf 2 X)
    (hne : Y ≠ ⊤) :
    Y ∈ scriptY3 A (lB A) ∧ oPrimeResidualOf 3 Y = X ∧
      Y = X ⊔ CFSG.Open.pCoreOf 2 Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hY
  have hQO2X : Q ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hQX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hP2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' (H := CFSG.Open.pCoreOf 2 X) (K := Q)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hQ2 hQO2X
  have hXnormP : X ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) : Set G) := by
    have hfwd : ∀ x ∈ X, ∀ z ∈ (CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G),
        x * z * x⁻¹ ∈ (CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) := by
      intro x hx z hz
      have hzm : z ∈ ((CFSG.Open.pCoreOf 2 X : Set G) * (Q : Set G)) := by
        rwa [← Subgroup.coe_mul_of_right_le_normalizer_left (CFSG.Open.pCoreOf 2 X) Q hQO2X]
      obtain ⟨n, hn, q, hq, rfl⟩ := hzm
      have h1 : x * n * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx) n).mp hn
      have h2 : x * q * x⁻¹ ∈ (CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) := by
        have h2a : x * q * x⁻¹ = ⁅x, q⁆ * q := by
          rw [commutatorElement_def]
          group
        rw [h2a]
        have hxq : ⁅x, q⁆ ∈ CFSG.Open.pCoreOf 2 X := by
          rw [Subgroup.commutator_comm] at hQO2
          exact hQO2 (Subgroup.commutator_mem_commutator hx hq)
        exact Subgroup.mul_mem_sup hxq hq
      rw [show x * (n * q) * x⁻¹ = (x * n * x⁻¹) * (x * q * x⁻¹) from by group]
      exact (CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G).mul_mem (Subgroup.mem_sup_left h1) h2
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨hfwd x hx z, fun hz => by
      have h := hfwd x⁻¹ (X.inv_mem hx) (x * z * x⁻¹) hz
      have h2 : x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ = z := by group
      rwa [h2] at h⟩
  have hQnormP : Q ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) : Set G) :=
    (le_inf hQO2X Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hYnormP : X ⊔ Q ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) : Set G) := sup_le hXnormP hQnormP
  have hPleY : (CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) ≤ X ⊔ Q :=
    sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans le_sup_left) le_sup_right
  have hPnorm : ((CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G).subgroupOf (X ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleY).mpr hYnormP
  have hPO2Y : (CFSG.Open.pCoreOf 2 X ⊔ Q : Subgroup G) ≤ CFSG.Open.pCoreOf 2 (X ⊔ Q) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hPleY hPnorm hP2
  have hQO2Y : Q ≤ CFSG.Open.pCoreOf 2 (X ⊔ Q) := le_sup_right.trans hPO2Y
  have hYO2ne : CFSG.Open.pCoreOf 2 (X ⊔ Q) ≠ ⊥ :=
    fun hbot => hQne (le_bot_iff.mp (hbot ▸ hQO2Y))
  have hYeq2 : X ⊔ Q = X ⊔ CFSG.Open.pCoreOf 2 (X ⊔ Q) := by
    refine le_antisymm ?_ (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ Q)))
    calc X ⊔ Q = X ⊔ (CFSG.Open.pCoreOf 2 X ⊔ Q) := by
          rw [← sup_assoc, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X)]
      _ ≤ X ⊔ CFSG.Open.pCoreOf 2 (X ⊔ Q) := sup_le_sup_left hPO2Y X
  have hXY : X ≤ X ⊔ Q := le_sup_left
  have hYnormX : X ⊔ Q ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hQX
  haveI hXsub : (X.subgroupOf (X ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr hYnormX
  have hquot2 : IsPGroup 2 (↥(X ⊔ Q) ⧸ X.subgroupOf (X ⊔ Q)) := by
    haveI : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 (X ⊔ Q)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ Q)
    let φ : ↥(CFSG.Open.pCoreOf 2 (X ⊔ Q)) →* (↥(X ⊔ Q) ⧸ X.subgroupOf (X ⊔ Q)) :=
      (QuotientGroup.mk' (X.subgroupOf (X ⊔ Q))).comp
        (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ Q)))
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (X.subgroupOf (X ⊔ Q)) q
      have hy : (y : G) ∈ X ⊔ CFSG.Open.pCoreOf 2 (X ⊔ Q) := hYeq2 ▸ y.2
      have hmul : (y : G) ∈ ((X : Set G) * (CFSG.Open.pCoreOf 2 (X ⊔ Q) : Set G)) := by
        rwa [← Subgroup.coe_mul_of_left_le_normalizer_right X (CFSG.Open.pCoreOf 2 (X ⊔ Q))
          (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ Q)))]
      obtain ⟨x, hx, n, hn, hxn⟩ := hmul
      refine ⟨⟨n, hn⟩, ?_⟩
      show QuotientGroup.mk' (X.subgroupOf (X ⊔ Q))
          (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ Q)) ⟨n, hn⟩) =
        QuotientGroup.mk' (X.subgroupOf (X ⊔ Q)) y
      have hx1 : QuotientGroup.mk' (X.subgroupOf (X ⊔ Q)) (⟨x, hXY hx⟩ : ↥(X ⊔ Q)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
      have hyeq : y = (⟨x, hXY hx⟩ : ↥(X ⊔ Q)) *
          ⟨n, CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ Q) hn⟩ := by
        ext
        simpa using hxn.symm
      rw [hyeq, map_mul, hx1, one_mul]
      rfl
    exact IsPGroup.of_surjective (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ Q)) φ hφ
  have hO3Yle : oPrimeResidualOf 3 (X ⊔ Q) ≤ X :=
    oPrimeResidualOf_le_of_isPGroup_quotient hXY hYnormX hquot2
  have hO3Y : oPrimeResidualOf 3 (X ⊔ Q) = X := by
    refine le_antisymm hO3Yle ?_
    calc X = oPrimeResidualOf 3 X := hX4.2.1
      _ ≤ oPrimeResidualOf 3 (X ⊔ Q) :=
        oPrimeResidualOf_mono 3 le_sup_left
  have hAY : A ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G) :=
    (le_inf hX4.1.2 hQA).trans (Subgroup.inf_normalizer_le_normalizer_sup X Q)
  have hYΔ : X ⊔ Q = delta A (lB A) (X ⊔ Q) := by
    refine le_antisymm ?_ (delta_le (X ⊔ Q))
    exact sup_le (hX4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hQ le_sup_right)
  have hY3 : (X ⊔ Q) ∈ scriptY3 A (lB A) := ⟨⟨⟨hne, hAY⟩, hYO2ne⟩, hYΔ⟩
  exact ⟨hY3, hO3Y, hYeq2⟩

private theorem w_facts {Y K W : Subgroup G} (hW : W = Y ⊔ K)
    (hY3 : Y ∈ scriptY3 A (lB A))
    (hK : K ∈ scriptQ A (lB A))
    (hKY : K ≤ Subgroup.normalizer (Y : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hne : W ≠ ⊤) :
    W ∈ scriptY3 A (lB A) ∧ Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 W : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hW
  have hYW : Y ≤ Y ⊔ K := le_sup_left
  have hWYnorm : Y ⊔ K ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hKY
  have hO2YW : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 (Y ⊔ K) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hYW hWYnorm
  have hYO2ne : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY3.1.2
  have hWO2ne : CFSG.Open.pCoreOf 2 (Y ⊔ K) ≠ ⊥ :=
    fun hbot => hYO2ne (le_bot_iff.mp (hbot ▸ hO2YW))
  have hAW : A ≤ Subgroup.normalizer ((Y ⊔ K : Subgroup G) : Set G) :=
    (le_inf hY3.1.1.2 hAK).trans (Subgroup.inf_normalizer_le_normalizer_sup Y K)
  have hWΔ : Y ⊔ K = delta A (lB A) (Y ⊔ K) := by
    refine le_antisymm ?_ (delta_le (Y ⊔ K))
    exact sup_le (hY3.2.le.trans (delta_mono le_sup_left)) (le_delta hK le_sup_right)
  refine ⟨⟨⟨⟨hne, hAW⟩, hWO2ne⟩, hWΔ⟩, ?_⟩
  exact hYW.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ K))

theorem le_M_of_commutator_le_pCoreOf (h : Sec17Std G A c L Y₀) (h155 : Item155 A (lB A))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) {L₀ : Subgroup G}
    (hL₀d : L₀ ≤ Subgroup.centralizer ({d} : Set G)) (hL₀perf : Group.IsPerfect ↥L₀)
    (hAL₀ : A ≤ Subgroup.normalizer (L₀ : Set G)) (hL₀Δ : L₀ ≤ delta A (lB A) L₀)
    (hL₀6 : Sec4.IsTripleCover (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) (alternatingGroup (Fin 6)))
    {K R Z : Subgroup G} (hKQ : K ∈ scriptQ A (lB A))
    (hKd : K ≤ Subgroup.centralizer ({d} : Set G))
    (hKL₀ : ⁅K, L₀⁆ ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))
    (hR2 : IsPGroup 2 R) (hRQ : R ∈ scriptQ A (lB A))
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hZR : Z ≤ R) (hZ1 : Z ≠ ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hZL₀ : Z ≤ Subgroup.centralizer (L₀ : Set G))
    (hZd : Z ≤ Subgroup.centralizer ({d} : Set G)) :
    K ≤ Subgroup.normalizer (Y₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  let V : Subgroup G := CFSG.Open.pCoreOf 2 C
  let X : Subgroup G := inSubgroup perfectResidual (L₀ ⊔ V)
  let Q : Subgroup G := ⨆ k : K, Z.map (MulAut.conj (k : G)).toMonoidHom
  obtain ⟨hX4, hΩ, hXC, hXN, _, hXNF, hCne⟩ :=
    mem_scriptY4_and_omg_of_tripleCover h hdA hd1 hL₀d hL₀perf hAL₀ hL₀Δ hL₀6 rfl
  obtain ⟨hQQ, hQ2, hQne, hQC, hQA, hQKn, hKX, hQX, hQO2⟩ :=
    q_facts (Q := Q) rfl hL₀d hXC hXN hXNF hKQ hKd hKL₀ hR2 hRQ hKR hZR hZ1 hAZ hZL₀ hZd
  have hYne : X ⊔ Q ≠ ⊤ := fun htop => hCne (top_le_iff.mp (htop ▸ sup_le hXC hQC))
  obtain ⟨hY3, hO3Y, hYeq⟩ :=
    y_facts (Y := X ⊔ Q) rfl hX4 hQQ hQ2 hQne hQA hQX hQO2 hYne
  have hKY : K ≤ Subgroup.normalizer (X ⊔ Q : Subgroup G) :=
    (le_inf hKX hQKn).trans (Subgroup.inf_normalizer_le_normalizer_sup X Q)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := (mem_scriptQ_iff.mp hKQ).2.1
  have hKC : K ≤ C := hKd
  have hWne : (X ⊔ Q) ⊔ K ≠ ⊤ := fun htop =>
    hCne (top_le_iff.mp (htop ▸ sup_le (sup_le hXC hQC) hKC))
  obtain ⟨hW3, hYNO2W⟩ := w_facts (W := (X ⊔ Q) ⊔ K) rfl hY3 hKQ hKY hAK hWne
  have hWle : (X ⊔ Q) ⊔ K ≤ Subgroup.normalizer (Y₀ : Set G) := by
    refine Proof166Res3.le_M_of_y4 (X := (X ⊔ Q) ⊔ K) (Y' := X ⊔ Q)
      h h155 hW3 hY3 hYNO2W ?_ ?_ ?_
    · rw [hO3Y]; exact hYeq
    · rw [hO3Y]; exact hX4
    · rw [hO3Y]; exact hΩ
  exact le_trans le_sup_right hWle

end CFSG.RankThree.PartTwo.Sec16.Ctr166
