module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847Fields
import CFSG.GroupTheory.CoprimeSupPCore
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenJ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Rank
public import CFSG.Adapters.LieModelSimple
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem g4N_normalizer_ne_top_of_isPGroup (D : Data G) {Z : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hZ : IsPGroup r Z) (hZ1 : Z ≠ ⊥) :
    Subgroup.normalizer (Z : Set G) ≠ ⊤ := by
  intro htop
  haveI : IsSimpleGroup G := D.standing.simple
  haveI : Fact r.Prime := ⟨hr⟩
  haveI hnorm : Z.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have hZtop : Z = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with h | h
    · exact absurd h hZ1
    · exact h
  have hP : IsPGroup r G := by
    have hZ' : IsPGroup r ↥(⊤ : Subgroup G) := hZtop ▸ hZ
    exact IsPGroup.of_equiv hZ' Subgroup.topEquiv
  haveI : Group.IsNilpotent G := hP.isNilpotent
  haveI : IsMulCommutative G :=
    Group.IsNilpotent.nilpotencyClass_le_one_iff.mp
      (Group.nilpotencyClass_le_one_of_isSimple_of_isNilpotent (G := G))
  obtain ⟨x, y, hxy⟩ := D.standing.nonab
  exact hxy (mul_comm x y)

private theorem g4N_hyp919c_of_commutator_le (D : Data G) {L D₃ Z : Subgroup G} {r : ℕ}
    (hL : L ∈ calC D.M) (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3)
    (hD₃U : D₃ ∈ uniqueSet D.M) (hr : r.Prime) (hr2 : r ≠ 2) (hZr : IsPGroup r Z)
    (hZ1 : Z ≠ ⊥) (hZL : ⁅Z, L⁆ ≤ pCoreOf 2 L)
    (hHM : ¬ normalizer (Z : Set G) ≤ D.M) :
    PartTwo.Hyp919c D L D₃ (L ⊓ centralizer (Z : Set G)) (normalizer (Z : Set G)) := by
  have hYL : L ⊓ centralizer (Z : Set G) ≤ L := inf_le_left
  have hYM : L ⊓ centralizer (Z : Set G) ≤ D.M := hYL.trans hL.1.le
  have hYH : L ⊓ centralizer (Z : Set G) ≤ normalizer (Z : Set G) :=
    (inf_le_right : L ⊓ centralizer (Z : Set G) ≤ centralizer (Z : Set G)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hsup : L = (L ⊓ centralizer (Z : Set G)) ⊔ pCoreOf 2 L :=
    (CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le hr hr2 hZr hZL).symm
  have hsup' : L = (L ⊓ (L ⊓ centralizer (Z : Set G))) ⊔ pCoreOf 2 L := by
    rw [inf_eq_right.mpr hYL]
    exact hsup
  have hN : ((L ⊓ (L ⊓ centralizer (Z : Set G))).subgroupOf
      (L ⊓ centralizer (Z : Set G))).Normal := by
    rw [inf_eq_right.mpr hYL, Subgroup.subgroupOf_self]
    exact inferInstance
  have hidx : ((L ⊓ (L ⊓ centralizer (Z : Set G))).subgroupOf
      (L ⊓ centralizer (Z : Set G))).index = 2 ^ 0 := by
    rw [inf_eq_right.mpr hYL, Subgroup.subgroupOf_self, Subgroup.index_top, pow_zero]
  exact ⟨hL, hD₃L, hD₃, hD₃U, hYM, hsup', hN, ⟨0, hidx⟩,
    g4N_normalizer_ne_top_of_isPGroup D hr hZr hZ1, hYH, hHM⟩

private theorem g4N_normalizer_le_of_forall (D : Data G) (h920 : R920odd D) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hp5 : 5 < p) (hLp : IsL2Odd (Bar2 L) p)
    (hN : ∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {D₃ : Subgroup G} (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {Z : Subgroup G} (hZr : IsPGroup r Z) (hZ1 : Z ≠ ⊥)
    (hZL : ⁅Z, L⁆ ≤ CFSG.Open.pCoreOf 2 L) : Subgroup.normalizer (Z : Set G) ≤ D.M := by
  by_contra hHM
  have hc := g4N_hyp919c_of_commutator_le D hL hD₃L hD₃ hD₃U hr hr2 hZr hZ1 hZL hHM
  have hsup : L = (L ⊓ centralizer (Z : Set G)) ⊔ pCoreOf 2 L :=
    (CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le hr hr2 hZr hZL).symm
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv
    (inf_le_left : L ⊓ centralizer (Z : Set G) ≤ L) hsup
  obtain ⟨A, hAY, hAcard, hAodd, hAnM⟩ := h920 L D₃ (L ⊓ centralizer (Z : Set G))
    (normalizer (Z : Set G)) hc inf_le_left p hLp.admissible.1 hp5
    (CFSG.Blueprint.LieModel.of_mulEquiv e hLp)
  exact hAnM (hN A (hAY.trans inf_le_left) hAcard hAodd)

namespace Ctx21

private theorem g4N_false_of_isL2Odd_of_forall (D : Data G) (Ch : Choice2011 G)
    (h212 : S21_12 D Ch) (h920 : R920odd D) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hLp : IsL2Odd (Bar2 L) p) {D₃ : Subgroup G} (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3)
    (hD₃U : D₃ ∈ uniqueSet D.M)
    (hN : ∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M) : False := by
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hp2 : p ≠ 2 := by omega
  haveI : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hLp
  have hZc : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZc
  have hChev : IsChev (BarInf L) p :=
    ⟨.PSL, 2, 1, hLp.admissible, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLp⟩
  have h12 := h212 hH c₀ L hL p hp hp2 hChev
  obtain ⟨b, hbB0, r, hr, hr2, hr3, hbo⟩ := exists_mem_B0_orderOf_ne_three c hn3
  have hb3 : b ∈ CFSG.Quasithin.opResidual 3 c.B0 :=
    CFSG.Quasithin.mem_opResidual_of_coprime hbB0 (by
      rw [hbo]
      exact (Nat.coprime_primes hr Nat.prime_three).2 hr3)
  have hb1 : b ≠ 1 := by
    intro hb
    rw [hb, orderOf_one] at hbo
    exact hr.ne_one hbo.symm
  set Z : Subgroup G := Subgroup.zpowers b with hZ
  have hZr : IsPGroup r Z := by
    rw [hZ]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have hZ1 : Z ≠ ⊥ := by
    rw [hZ, Ne, Subgroup.zpowers_eq_bot]
    exact hb1
  have hZle : Z ≤ c₀.B := by
    rw [hZ]
    exact Subgroup.zpowers_le.mpr hbB0
  have hZres : Z ≤ CFSG.Quasithin.opResidual 3 c₀.B := by
    rw [hZ]
    exact Subgroup.zpowers_le.mpr hb3
  have hZL : ⁅Z, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
    (Subgroup.commutator_mono hZres le_rfl).trans h12.2
  exact (s21_2 D Ch hH c₀ Z hZle)
    (g4N_normalizer_le_of_forall D h920 hL hp5 hLp hN hD₃L hD₃ hD₃U hr hr2 hZr hZ1 hZL)

end Ctx21

private theorem g4N_isSimpleGroup_of_shape {K : Subgroup G}
    (hKs : (∃ n : ℕ, IsL2 (Bar2 K) n) ∨ (∃ m : ℕ, IsPowTwo m ∧ IsU3 (Bar2 K) m) ∨
      IsJ1 (Bar2 K) ∨ ∃ q : ℕ, q.Prime ∧ IsL2Odd (Bar2 K) q) :
    IsSimpleGroup (Bar2 K) := by
  rcases hKs with ⟨n, h⟩ | ⟨m, -, h⟩ | h | ⟨q, -, h⟩
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSU) (by decide) h
  · exact (kJ1_holds (Bar2 K) h).2.1
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h

private theorem g4N_s21_19_of_forall (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h212 : S21_12 D Ch) (h8107 : F08.R8107 D) (h920 : R920odd D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hN : ∀ L ∈ calC D.M, ∀ K ∈ calC D.M, L ≠ K → (L.subgroupOf D.M).Normal → ∀ p : ℕ,
      5 < p → IsL2Odd (Bar2 L) p → CFSG.Open.pRank 3 L = 1 → CFSG.Open.pRank 3 K = 1 →
      center (Bar2 L) = ⊥ → center (Bar2 K) = ⊥ → ∀ A : Subgroup G, A ≤ L →
        (Nat.card A).Prime → Odd (Nat.card A) → normalizer (A : Set G) ≤ D.M) :
    S21_19 D Ch := by
  intro hH c L hL K hK hLK hLn hLs hKs
  rcases hLs with hJ1 | ⟨p, hp, hp5, hLp⟩
  · exact Ctx21.false_of_isJ1_of_shape D Ch h211 h8107 hH c hL hK hLK hLn hJ1 hKs
  · have hL3 := pRank_three_eq_one_and_thin8_or_isU3
      (Or.inr (Or.inr (Or.inr ⟨p, hp, hLp⟩)))
    have hK3 := pRank_three_eq_one_and_thin8_or_isU3 hKs
    have h3L : 3 ∣ Nat.card L :=
      CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three (by rw [hL3.1])
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
    let D₃ : Subgroup G := Subgroup.zpowers ((x : ↥L) : G)
    have hxG : orderOf ((x : ↥L) : G) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    have hD₃L : D₃ ≤ L := Subgroup.zpowers_le.mpr x.2
    have hD₃3 : Nat.card D₃ = 3 := by
      rw [show D₃ = Subgroup.zpowers ((x : ↥L) : G) from rfl, Nat.card_zpowers, hxG]
    have hD₃U : D₃ ∈ uniqueSet D.M :=
      mem_uniqueSet_of_card_eq_three D h8107 hL hK hLK hL3 hK3 hD₃L hD₃3
    haveI : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hLp
    haveI : IsSimpleGroup (Bar2 K) := g4N_isSimpleGroup_of_shape hKs
    exact Ctx21.g4N_false_of_isL2Odd_of_forall D Ch h212 h920 hH c (hn3 hH c) hL hp hp5 hLp hD₃L
      hD₃3 hD₃U (hN L hL K hK hLK hLn p hp5 hLp hL3.1 hK3.1 (uc22p21k_center_eq_bot hL.2.2)
        (uc22p21k_center_eq_bot hK.2.2))

theorem s21_19_of_r847E3Thin (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h212 : S21_12 D Ch) (h8107 : F08.R8107 D) (h847 : R847E3Thin D) (he : evenRank G = 3)
    (h920 : R920odd D) (hsig : D.sig.Nonempty) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) :
    S21_19 D Ch :=
  g4N_s21_19_of_forall D Ch h211 h212 h8107 h920 hn3
    fun _ hL _ hK hLK hLn _ hp5 hLp hL3 hK3 hZL hZK _ hAL hA hAo =>
      R847E3.normalizer_le_of_thin_of_ne h847 he hsig hL hLn
        (thin8_of_isL2Odd_bar2 hLp.admissible.1 (by omega) hLp) hK hLK
        (by rw [hZL, Subgroup.card_bot]; norm_num) (by rw [hZK, Subgroup.card_bot]; norm_num)
        hL3.ge hK3.ge hAL hA (fun h2 => by rw [h2] at hAo; exact (by decide : ¬ Odd 2) hAo) rfl

theorem s21_19_of_r847ThinPair (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h212 : S21_12 D Ch) (h8107 : F08.R8107 D) (h847 : R847ThinPair D) (h920 : R920odd D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) : S21_19 D Ch :=
  g4N_s21_19_of_forall D Ch h211 h212 h8107 h920 hn3
    fun _ hL _ hK hLK hLn _ hp5 hLp hL3 hK3 _ _ _ hAL hA hAo => Classical.byContradiction
      (false_of_r847ThinPair D h847 hL hK hLK hp5 hLp hLn
        ((CFSG.SectionRank.pRank_coe_eq_openPRank 3 _).trans hL3).ge
        ((CFSG.SectionRank.pRank_coe_eq_openPRank 3 _).trans hK3).ge hAL hA hAo)

end CFSG.LocalAnalysis.UniquenessCase.UC22
