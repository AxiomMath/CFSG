module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ONProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ONProofImg
import CFSG.RankThree.PartTwo.Sec14.Item148PointProofPGL
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ONProofType

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148

@[expose] def KF148ONA7 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L K N : Subgroup Γ) (e : Γ),
    Late.IsE27 A → e ∈ A → e ≠ 1 → L ≤ Subgroup.centralizer ({e} : Set Γ) →
    A ≤ Subgroup.normalizer (L : Set Γ) →
    IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L) CFSG.Blueprint.NativeSporadic.ON →
    K ≤ L → A ≤ Subgroup.normalizer (K : Set Γ) →
    N ≤ K → [(N.subgroupOf K).Normal] → A ≤ Subgroup.normalizer (N : Set Γ) →
    ¬ 3 ∣ Nat.card N →
    IsQuasisimple (↥K ⧸ N.subgroupOf K) →
    Sec4.IsTripleCover (↥K ⧸ N.subgroupOf K) (alternatingGroup (Fin 7)) →
    Late.sectionCentralizer A K N = (Subgroup.zpowers e : Set Γ) →
    ∃ x ∈ Subgroup.centralizer (A : Set Γ), orderOf x = 3 ∧ x ∉ A

namespace Res9ON

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_quotient_inf_equiv_img148 {A Y : Subgroup G} [(ker148 A Y).Normal]
    {K : Subgroup G} (hKM : K ≤ Y ⊔ A) [((K ⊓ pPrimeCoreOf 3 Y).subgroupOf K).Normal] :
    Nonempty (↥K ⧸ (K ⊓ pPrimeCoreOf 3 Y).subgroupOf K ≃* ↥(img148 A Y K)) := by
  set φ := Main148.phi148 (A := A) (Y := Y) hKM with hφ
  have hker : φ.ker = (K ⊓ pPrimeCoreOf 3 Y).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, hφ, Main148.phi148_eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr (Main148.range_phi148 hKM)))⟩

theorem false_of_isTripleCover_img148 (hKF : KF148ONA7) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hON3 : Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le)
      CFSG.Blueprint.NativeSporadic.ON)
    (htc : Sec4.IsTripleCover ↥(img148 A Y K) (alternatingGroup (Fin 7))) : False := by
  obtain ⟨hB, -, -, heB, he1, hK, hKΔ, hKLe, hLe, -⟩ := hP
  have heA : e ∈ A := hB.1 heB
  have hA : Late.IsE27 A := h.isE27'
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha heA)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hKΔ
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hAL : A ≤ Subgroup.normalizer (Le : Set G) :=
    Item148Point.le_normalizer_of_perfect_le148 hAe hLe hKLe hAK hKp
      (Res7Sig.ne_bot_of_isQuasisimple148 hKq)
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLe
  have hLq : IsQuasisimple (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  set N : Subgroup G := K ⊓ pPrimeCoreOf 3 Y with hNdef
  have hNK : N ≤ K := inf_le_left
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, le_normalizer_pPrimeCoreOf 3 Y (hKY hk)⟩
  have hNn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAK ha, normalizer_le_normalizer_pPrimeCoreOf 3 Y (hY.2 ha)⟩
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
      (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have := hNn
  obtain ⟨ψ⟩ := nonempty_quotient_inf_equiv_img148 (A := A) (Y := Y) hKM
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := isSimpleGroup_a7_148.1
  have hKαq : IsQuasisimple ↥(img148 A Y K) := Res8ON.isQuasisimple_of_isTripleCover hKαp htc
  have hqN : IsQuasisimple (↥K ⧸ N.subgroupOf K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hKαq
  have htcN : Sec4.IsTripleCover (↥K ⧸ N.subgroupOf K) (alternatingGroup (Fin 7)) :=
    Res8ON.isTripleCover_congr148 ψ.symm htc
  have hsecN : Late.sectionCentralizer A K N = (Subgroup.zpowers e : Set G) := by
    rw [← hsec]
    ext a
    constructor
    · rintro ⟨haA, h⟩
      exact ⟨haA, fun x hx => (h x hx).2⟩
    · rintro ⟨haA, h⟩
      refine ⟨haA, fun x hx => ⟨?_, h x hx⟩⟩
      have h1 : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK haA) x).mp hx
      exact K.mul_mem h1 (K.inv_mem hx)
  obtain ⟨x, hxC, hx3, hxA⟩ := hKF G A Le K N e hA heA he1 hLeC hAL hLq hON3 hKLe hAK hNK
    hAN hN3 hqN htcN hsecN
  exact hxA (Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian
    (by rw [← hx3]; exact pow_orderOf_eq_one x)
    (fun a ha => Subgroup.mem_centralizer_iff.mp hxC a ha))

theorem kType148_of_kType148Cover (hKF : KF148ONA7) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hkt : KType148Cover A Y e K Le) : KType148 A Y e K Le := by
  rcases hkt with hkt | ⟨hsec, hON3, htc⟩
  · exact hkt
  · exact (false_of_isTripleCover_img148 hKF h hY hP hsec hON3 htc).elim

end Res9ON

theorem step148KType_of_step148KTypeCover (hKF : KF148ONA7) (hKT : Step148KTypeCover) :
    Step148KType := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP
  let := ker148_normal hY.2
  exact Res9ON.kType148_of_kType148Cover hKF h hY hP
    (hKT G A c L h Y hY hs hYB B Q e K Le hP)

end CFSG.RankThree.PartTwo.Sec14
