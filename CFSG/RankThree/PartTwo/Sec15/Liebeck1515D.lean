module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec15.Liebeck143AtDelta
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec15.Liebeck143At

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem isZCentral_of_isThreeCentralIn
    {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hd1 : d ≠ 1) (hd : IsThreeCentralIn L d) : IsZCentral L d := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hdL, S, hS1, hS2⟩ := hd
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hS1 hS2
  exact ⟨_, hSy, hZ⟩

theorem zpowers_eq_of_point
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L : Subgroup G} {d : G}
    (h : Gagen1515Fpf.Ctx A c L d) (hΩB : ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c, d})
    {c' d' : G} {L' : Subgroup G} (hc'Ω : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c')
    (hJ' : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hd'A : d' ∈ A) (hd'1 : d' ≠ 1) (hd'c : IsThreeCentralIn L' d') :
    Subgroup.zpowers d' = Subgroup.zpowers d := by
  have hA : Late.IsE27 A := h.isE27
  have hcA : c ∈ A := h.sec13Data.mem_A
  have hD' : Sec13Data G A c' L' :=
    { h.sec13Data with zpowers_mem_omegaA := hc'Ω, mem_lA := hL' }
  have hd'Z : IsZCentral L' d' := isZCentral_of_isThreeCentralIn hJ' hd'1 hd'c
  obtain ⟨hdΩ, hpts⟩ := h.omega_facts h134 h48
  have hcL : c ∉ L := (j2_point_facts h.sec13Data h.conf.j2).1
  have hcd : c ∉ Subgroup.zpowers d := fun hm => hcL (Subgroup.zpowers_le.mpr h.mem_L hm)
  have hdc : d ∉ Subgroup.zpowers c := Proof152ResW.not_mem_zpowers_symm hA h.ne_d hcA hcd
  have hΩc' : omegaA A ≠ {Subgroup.zpowers c'} := by
    intro heq
    have h1 : Subgroup.zpowers c ∈ ({Subgroup.zpowers c'} : Set (Subgroup G)) :=
      heq ▸ h.sec13Data.zpowers_mem_omegaA
    have h2 : Subgroup.zpowers (c * d) ∈ ({Subgroup.zpowers c'} : Set (Subgroup G)) :=
      heq ▸ hpts d (Subgroup.mem_zpowers d)
    rw [Set.mem_singleton_iff] at h1 h2
    have hcd' : c * d ∈ Subgroup.zpowers c := by
      rw [h1, ← h2]
      exact Subgroup.mem_zpowers _
    apply hdc
    have e : d = c⁻¹ * (c * d) := by group
    rw [e]
    exact (Subgroup.zpowers c).mul_mem
      ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c)) hcd'
  obtain ⟨hd'Ω, hpts'⟩ := Proof15Res11.omega_facts h134 h48 hD' hJ' hΩc' hd'A hd'1 hd'Z
  have hc'B : c' ∈ Subgroup.closure {c, d} :=
    Subgroup.zpowers_le.mp (hΩB _ hc'Ω)
  have hc'd'B : c' * d' ∈ Subgroup.closure {c, d} :=
    Subgroup.zpowers_le.mp (hΩB _ (hpts' d' (Subgroup.mem_zpowers d')))
  have hd'B : d' ∈ Subgroup.closure {c, d} := by
    have e : d' = c'⁻¹ * (c' * d') := by group
    rw [e]
    exact mul_mem (inv_mem hc'B) hc'd'B
  have hBA : Subgroup.closure {c, d} ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  by_contra hne
  have hd'3 : Nat.card (Subgroup.zpowers d') = 3 :=
    Sec13.card_zpowers_of_pow_three (hA.1.2 d' hd'A) hd'1
  obtain ⟨k, hk, hkeq⟩ := Proof152ResW.exists_eq_zpowers_mul hA hcA h.mem_d h.ne_d hcd
    (Subgroup.zpowers_le.mpr (hBA hd'B)) hd'3 hne
  exact hd'Ω (hkeq ▸ hpts k hk)

theorem exists_xd
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5) (h143 : Ronan148Q.Item143QS14) {A : Subgroup G}
    {c : G} {L : Subgroup G} {d : G} (h : Gagen1515Fpf.Ctx A c L d)
    (hΩB : ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c, d}) :
    ∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d ∧ 𝒳.Nonempty ∧
      Gagen1515Fpf.x₀ L d ≤ sSup 𝒳 ∧
      deltaZero A (lB A) (Subgroup.centralizer ({d} : Set G)) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ sSup 𝒳 ∧
      sSup 𝒳 ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) =
        inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) ∧
      Group.IsPerfect ↥(sSup 𝒳) ∧
      (Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) := by
  have hS : Sec14Std G A c L := h.conf.sec15R.toSec14Std
  obtain ⟨-, hXcover, -, -, -, hX3, hXΔ⟩ := h.residual_facts
  obtain ⟨hdΩ, -⟩ := h.omega_facts h134 h48
  have hcard : 3 ∣ Nat.card ↥(Gagen1515Fpf.x₀ L d) := by
    rw [Proof15Res11.card_of_isTripleCover_a6 hXcover]
    norm_num
  obtain ⟨b, d', Lb, 𝒳, hbΩ, hLb, hJb, hd'A, hd'1, hd'c, -, h𝒳, hne𝒳, hYX, hΔ, hinv, hcase⟩ :=
    Liebeck156.exists_le_of_item143Q h45 hS (h143 G A c L hS) h.mem_d h.ne_d hdΩ
      (Item148HJ.residual_le_centralizer_singleton L d) hXΔ hX3 hcard
  rcases hcase with ⟨X, -, -, hne⟩ | ⟨-, htypes⟩
  · exact absurd (zpowers_eq_of_point h134 h48 h hΩB hbΩ hLb hJb hd'A hd'1 hd'c).symm hne
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr h.isE27.1.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.mem_d))
  have hno : Ronan148W.NoNormal3 (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) := by
    rcases htypes with hON | h6 | hcp
    · exact Ronan148W.noNormal3_of_isTripleCover_ON hON
    · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact Ronan148W.noNormal3_of_isTripleCover
        (by rw [Ronan148W.card_alternatingGroup_six]; norm_num) h6
    · exact Ronan148W.noNormal3_of_isCentralProductA6Covers hcp
  exact ⟨𝒳, h𝒳, hne𝒳, hYX, Liebeck156.deltaZero_le_of_inv143Q h.mem_d hAd hΔ hinv,
    Liebeck156.inf_pPrimeCoreOf_eq_theta h𝒳 hno,
    Proof171Steps.isPerfect_sSup fun M hM => Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hM),
    htypes⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
