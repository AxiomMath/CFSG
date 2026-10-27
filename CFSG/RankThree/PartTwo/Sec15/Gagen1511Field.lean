module

public import CFSG.RankThree.PartTwo.Sec15.Item1511Proof
import CFSG.RankThree.PartTwo.Sec15.Gagen1511FieldY4
import CFSG.RankThree.PartTwo.Sec15.Liebeck159Omega
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOmg
import CFSG.RankThree.PartOne.S11d.FinalLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Field

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem false_of_point_of_meetsY4
    (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0 A (lB A)) {c' : G} {L' : Subgroup G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') {k : ℕ} (hk : 1 ≤ k)
    (hε : IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 k)
    (hmeet : MeetsY4 A (lB A) L' Y)
    (hΩ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c' : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≤ P → A ≠ omegaOneThree P) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR' : Sec15R G A c' L' := Proof1511.sec15R_point h hc' hL'
  have hD' := hR'.toSec13Data
  obtain ⟨j, hj, hL3'⟩ :=
    Sec16.Proof166Res4.isL3TwoPow_of_isLThreeEpsAt_two h.hypR.2 hc' hL' hk hε
  have hA3 : IsPGroup 3 A := fun g =>
    ⟨1, Subtype.ext (by simpa using h.isElemAbelian.2 (g : G) g.2)⟩
  obtain ⟨P, hP, hAP⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge
    (K := Subgroup.normalizer (Subgroup.zpowers c' : Set G) ⊓ Subgroup.normalizer (Y : Set G))
    (Q := A) (fun x hx => ⟨hD'.A_le_normalizer_zpowers hx, hY.1.1.2 hx⟩) hA3
  rcases h158 G A c' L' hR' (p := 2) (e := j) hj hL3' Y hY hmeet P hAP hP with
    ⟨-, hAΩ⟩ | ⟨-, -, -, hFall⟩
  · exact hΩ P hP hAP hAΩ
  ·
    obtain ⟨F, hFs⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Subgroup.zpowers c' ⊔ L')
    obtain ⟨hF, hΩF, h9F⟩ := hFall F hFs
    exact Proof1511.false_of_sylow hset h133 h159 h1510 hBr hR' hL3' hFs.le hF hΩF h9F

section Field


theorem false_of_field_point (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Sec15.Item1510R) (hBr : Sec16.Step169TwoBridge) (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0 A (lB A)) [(ker148 A Y).Normal] {c' : G} (hc'A : c' ∈ A)
    {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hX : Sec4.IsoLThreePi ↥(img148 A Y (deltaZero A (lB A) Y)) 2 (3 * n))
    (hsplit : img148 A Y (deltaZero A (lB A) Y ⊔ A) =
      img148 A Y (deltaZero A (lB A) Y) ⊔ Subgroup.zpowers (alpha148 A Y c' hc'A))
    (hfield : KFacts.InducesStdKind (img148 A Y (deltaZero A (lB A) Y)) (alpha148 A Y c' hc'A)
      .field)
    (hε : IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 (n * m)) {K : Subgroup G}
    (hKp : Group.IsPerfect ↥K) (hKΔ : K = deltaZero A (lB A) K) (hKLY : K ≤ L' ⊓ Y)
    (hKn : Sec4.IsoLThreePi ↥(img148 A Y K) 2 n) : False := by
  have hYΔ : Y = deltaZero A (lB A) Y :=
    Proof1515.eq_deltaZero_of_mem_scriptY4
      (forall_exists_isHyperplane_lB_eq_bot h134 h48 Sec4.Sporadic.rank3II_4_15) h hY.1
  have hK4 := mem_scriptY4_of_isoLThreePi_img148 hY.1 (hKLY.trans inf_le_right) hKp hKΔ hn hKn
  exact false_of_point_of_meetsY4 h158 hset h133 h159 h1510 hBr h hY hc' hL' (Nat.mul_pos hn hm)
    hε ⟨K, hK4, hKLY⟩ fun P hP hAP => Liebeck159.leaf2_omega_ne (Proof1511.sec15R_point h hc' hL')
      hc'A hY.1.1.2 hYΔ hn hX hsplit hfield hKLY hKn hP hAP

end Field

end CFSG.RankThree.PartTwo.Sec15.Proof1511Field
