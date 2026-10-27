module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Ext
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Conj
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.GH74.Generic.S45.LSporWit
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.CosetTableShort
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Uniqueness.Bender.Outer
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public section

namespace CFSG.Quasithin.A312J2

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier (j2P j2PermEquiv)
open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.E2P.SporB.J2Lat
open CFSG.QuasithinUnique.K1.SporadicPerm

theorem j2_C2_data :
    ∃ C Q : Subgroup (Equiv.Perm (Fin 315)), C ≤ j2P ∧ Nat.card C = 1920 ∧ ⁅C, C⁆ = C ∧
      Q ≤ C ∧ C ≤ normalizer (Q : Set (Equiv.Perm (Fin 315))) ∧ Nat.card Q = 32 ∧
      Nat.card ↥(C ⊓ centralizer (Q : Set (Equiv.Perm (Fin 315)))) = 2 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨hQcard, hQC2, hC2Q, hC2cent⟩ := j2_Q_facts
  have hmem : _ ∈ j2Rows := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hr := hrows _ hmem
  have hC2 : genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
    have h := hr.2.2.2.1
    dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C2Gens]
    exact h
  have hcard : Nat.card ↥(j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _)) = 1920 := by
    have h := hr.2.2.2.2.1
    dsimp only at h
    exact h
  have hperf : ⁅genOf 315 j2C2Gens, genOf 315 j2C2Gens⁆ = genOf 315 j2C2Gens :=
    (CFSG.GH74.Generic.S45.perfWitOK_spec (by norm_num)
      (CFSG.GH74.Generic.S45.perfWit_of_all CFSG.GH74.Generic.S45.perfWit_j2_2A _ hmem rfl)).1
  refine ⟨genOf 315 j2C2Gens, genOf 315 j2QGens, ?_, ?_, hperf, hQC2, hC2Q, hQcard, hC2cent⟩
  · rw [hC2]
    exact inf_le_left
  · rw [hC2]
    exact hcard

noncomputable def j2CtxA :
    LatCtx ↥CFSG.Sporadic.J2.J 315 (List ℕ) :=
  j2Ctx

theorem j2A_hL :
    j2CtxA.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size

theorem j2A_J :
    j2CtxA.J = 5 :=
  lat_J_eq j2CtxA j2A_hL

theorem j2A_sylow :
    IsSylowTwoOf j2CtxA.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨j2CtxA.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index j2CtxA.S
  have hN : j2CtxA.D.O.lbl.size = 4725 := j2_O_size
  rw [j2CtxA.S_card, j2CtxA.hΓ, hN] at h1
  have h2 : j2CtxA.S.index = 4725 := by
    have : j2CtxA.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem j2A_card
    {j : ℕ} (hj : j < 5) :
    Nat.card (j2CtxA.Y j) = (#[1, 3, 9, 15, 3] : Array ℕ)[j]! * 2 ^ 7 :=
  lat_card j2CtxA j2A_hL j (by simpa using hj)

theorem j2_Y3_ext :
    IsExt ↥(j2CtxA.Y 3) (fun V _ => IsExtraspecial2 2 V) (fun Z _ => IsAlt 5 Z) ∧
      ⁅j2CtxA.Y 3, j2CtxA.Y 3⁆ = j2CtxA.Y 3 := by
  obtain ⟨C, Q, hCP, hCcard, hCperf, hQC, hCQ, hQcard, hcent⟩ := j2_C2_data
  have hext := isExt_of_subgroup_data hCcard hCperf hQC hCQ hQcard hcent
  have hdvd : Nat.card j2CtxA.S ∣ Nat.card C := by
    have hk : j2CtxA.k = 7 := rfl
    rw [j2CtxA.S_card, hCcard, hk]
    norm_num
  obtain ⟨ψ⟩ : Nonempty (↥CFSG.Sporadic.J2.J ≃* ↥j2P) :=
    ⟨CFSG.Sporadic.Bridge.J2.nativeEquiv.symm.trans j2PermEquiv⟩
  have hall : ∀ Z : Subgroup ↥CFSG.Sporadic.J2.J, j2CtxA.S ≤ Z →
      ∃ j ≤ 5, Z = memberOrTop 5 j2CtxA.Y j := fun Z hZ => lat_all j2CtxA j2A_hL Z hZ
  have eH : ↥(C.subgroupOf j2P) ≃* ↥C := Subgroup.subgroupOfEquivOfLe hCP
  obtain ⟨j, hj, hcardY, hextY, hperfY⟩ := @exists_member_ext ↥CFSG.Sporadic.J2.J ↥j2P ↥C
    inferInstance inferInstance inferInstance inferInstance ψ j2CtxA.S j2A_sylow 5 j2CtxA.Y hall
    (C.subgroupOf j2P) eH hdvd (fun V _ => IsExtraspecial2 2 V) (fun V _ => IsAlt 5 V)
    (fun _ _ _ _ e h => IsExtraspecial2.of_mulEquiv e h)
    (fun _ _ _ _ e h => by obtain ⟨f⟩ := h; exact ⟨e.symm.trans f⟩) hext
    (Subgroup.isPerfect_iff.mpr hCperf)
  rw [hCcard] at hcardY
  have hj3 : j = 3 := by
    by_cases hj5 : j < 5
    · have hm : memberOrTop 5 j2CtxA.Y j = j2CtxA.Y j := by simp [memberOrTop, hj5]
      rw [hm, j2A_card hj5] at hcardY
      interval_cases j <;> simp_all
    · exfalso
      have hm : memberOrTop 5 j2CtxA.Y j = ⊤ := by simp [memberOrTop, hj5]
      rw [hm, Subgroup.card_top, CFSG.Sporadic.J2.card_J] at hcardY
      omega
  subst hj3
  have hm : memberOrTop 5 j2CtxA.Y 3 = j2CtxA.Y 3 := by simp [memberOrTop]
  rw [hm] at hextY hperfY
  exact ⟨hextY, hperfY⟩

end CFSG.Quasithin.A312J2
