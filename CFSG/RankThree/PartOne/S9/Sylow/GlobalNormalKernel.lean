module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalQDShape
public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Sec9B
open scoped commutatorElement

theorem normalOddCoreActionKernelCentralization_of
    (hI1 : SelectedPrimeMinimalTwoActionReduction) (hI2 : TwoLocalRankTwoOddCoreAction)
    (hESAE : ExceptionalSmallActionExclusion) : NormalOddCoreActionKernelCentralization := by
  intro G _ _ p hG hgood A R hA hAcard hR2 hAN hRA hR1 hBcard b hb hb1 hRθ q hq hq2 hqp X hXq
    hRAX hXexp hXcl hRX hmin
  have hp : p.Prime := hG.prime
  have hbA : b ∈ A := hb.1
  have hbC : b ∈ Subgroup.centralizer (R : Set G) := hb.2
  have hidx := relIndex_inf_centralizer_eq hp hAcard hBcard
  have hpB : p ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) := by
    rw [hBcard]; exact Nat.le_self_pow (by norm_num) p
  obtain ⟨-, hres⟩ := hI1 G hG.evenRank_eq p hp hG.mem_sigma hG.three_lt q hq hq2 hqp A R X hA
    hAN hR2 hRA hR1 hRAX (isPGroup_of_forall_pow_eq_one hXexp) hXexp hXcl hRX hidx hpB hmin hgood
  rcases hres with hBX | ⟨hp5, ⟨e⟩, hRC, hXR, hXB, hq1, hloc, hshapeX⟩
  · exact hBX
  exfalso
  subst hp5
  have hq5 : 5 < q := by have := hq.two_le; omega
  obtain ⟨a, haA, haC⟩ := exists_mem_not_mem_centralizer hp hAcard hBcard
  have ha1 : a ≠ 1 := fun h => haC (h ▸ Subgroup.one_mem _)
  have hcomm : a * b = b * a := (isElementaryAbelian_iff_forall.mp hA).1 a haA b hbA
  have haH : a ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    mem_normalizer_zpowers_of_commute hcomm
  set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hH
  have hRH : R ≤ H := hRθ.trans (Subgroup.map_subtype_le _)
  have hzA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr haA
  have hzH : Subgroup.zpowers a ≤ H := (Subgroup.zpowers_le).mpr haH
  have hA₀card : Nat.card ↥(Subgroup.zpowers a) = 5 := card_zpowers_eq hp hA haA ha1
  have hRA₀ : ⁅R, Subgroup.zpowers a⁆ = R :=
    commutator_zpowers_eq hp hA hAcard hAN hRA hBcard haA haC
  have hRO : ⁅R, inSubgroup (pCore q) H⁆ ≠ ⊥ := fun h =>
    hRX (le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hXq).trans h.le))
  have hloc' : localRank q ↥H ≤ 2 := (CFSG.RankThree.PartTwo.localRank_subgroup_le hq H).trans hloc
  obtain ⟨-, -, hshapeD⟩ := relative_twoLocalRankTwoOddCoreAction hI2 H (Subgroup.zpowers a) R
    hp hq (by norm_num) (by omega) (by omega) hzH hRH hA₀card (hzA.trans hAN) hR2 hR1 hRA₀ hRO
    hloc'
  have hXD : X ≤ omegaOne q (inSubgroup (pCore q) H) := fun x hx =>
    Subgroup.subset_closure ⟨hXq hx, hXexp x hx⟩
  have hXeq : X = omegaOne q (inSubgroup (pCore q) H) :=
    eq_of_le_of_isQDShape hq hXD hshapeX hshapeD
  have := hG.simple
  refine hESAE G hG.nonabelian hG.kProper hG.charTwo hG.evenRank_eq.le q hq hq5 hloc A R _ b
    hbA hb1 ⟨hA, by simpa using hAcard, hRθ, hAN, hRA, ⟨e⟩, by simpa using hBcard, hbC, rfl,
    ?_, hshapeD⟩
  rw [← hXeq]
  exact hRC

end CFSG.RankThree.PartOne
