module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7I
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7II
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7Geo
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LModel
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Alpha
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem leaf_E7_of (h36 : A36ForSQTK) (h5 : Stmt3_3_5)
    (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Leaf_E7 := by
  intro G _ _ T M L D H K q facts e6i e6ii
  have c := facts.cfg
  have hLS1 := leaf_LS1_of h5 h9 hGA h128 h37 h38 h39 G T M L D H K q c
  obtain ⟨m, -⟩ := c.exists_vmod h36 h5 h7 h9 hGA h128 h37 h38 h39
  have hcard : Nat.card (a2Z T) = 2 := m.card_Z_eq_two (le_conjClosure _ _)
  have hUV := facts.UH_le_VH
  obtain ⟨g, hg⟩ := facts.exists_critPair
  have hP := facts.e7Pair h36 hLS1 hcard hg (e6ii g hg)
  by_cases hD : centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K) =
      conjSub (g : G) (a2UH L T H K)
  · exact e7_caseI hP (le_conjClosure _ _) facts.e5c (e6i g hg) hD
  · have hlt := lt_of_le_of_ne (centralizerMod_le_left _ _ _) hD
    obtain ⟨k, hk, hlt', hle'⟩ := facts.exists_reversed h36 hLS1 hcard e6ii hg hlt
    have hPk := facts.e7Pair h36 hLS1 hcard hk (e6ii k hk)
    obtain ⟨-, c₀, hc₀, hc₀R⟩ := facts.exists_conj_le hLS1 hk
    exact e7_caseII hPk ⟨c₀, hc₀, (conjSub_mono c₀ (conjSub_mono (k : G) hUV)).trans hc₀R⟩ hlt' hle'

end CFSG.Quasithin.H13.NFa2
