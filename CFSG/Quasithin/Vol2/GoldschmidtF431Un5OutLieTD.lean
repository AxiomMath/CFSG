module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTA
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTB
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Field
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5td_ker (z : hypSU hK 2 1) (hz : z ∈ (hypProj hK 2 1).ker) :
    z ∈ Subgroup.center (hypSU hK 2 1) ∧ Odd (orderOf z) := by
  rw [ker_hypProj] at hz
  refine ⟨Subgroup.mem_center_iff.2 fun y => scalar_central hz y, ?_⟩
  obtain ⟨c, -, hc5, hc⟩ := hz
  have h5 : z ^ 5 = 1 := by
    apply Subtype.ext
    change (z : GL (HypIndex 2 1) K) ^ 5 = 1
    rw [hc, ← map_pow, hc5, map_one]
  exact Odd.of_dvd_nat (by decide : Odd 5) (orderOf_dvd_of_pow_eq_one h5)

theorem un5_card_le_of_fixed_Y {R : Subgroup (hypPSU hK 2 1)} (hR : IsPGroup 2 R)
    (hfix : ∀ x ∈ R, fieldP hK (bar5 hK) x = x) : Nat.card R ≤ (2 ^ f) ^ 4 := by
  have := CFSG.RankThree.PartOne.U5K.Hyp.finite_hypSU hK
  obtain ⟨H, hH2, hfixH, hmap, -⟩ := un5ta_exists_lift (hypProj hK 2 1)
    (hypProj_surjective hK 2 1) (un5td_ker hK) (fieldAut hK (bar5 hK)) (fieldP hK (bar5 hK))
    (fun g => (fieldP_apply hK _ g).symm) R hR hfix
  have h1 := un5_card_le_of_fixed hK hH2 (fun g hg a b =>
    congrFun (congrFun (congrArg (fun x : hypSU hK 2 1 => mat x) (hfixH g hg)) a) b)
  have h2 : Nat.card (H.map (hypProj hK 2 1)) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective
      (fun x : H => (⟨hypProj hK 2 1 x, Subgroup.mem_map_of_mem _ x.2⟩ :
        H.map (hypProj hK 2 1))) (fun y => by
        obtain ⟨x, hx, hxy⟩ := y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
  rw [hmap] at h2
  exact h2.trans h1

end CFSG.Quasithin.H13.F431.Un.OL5
