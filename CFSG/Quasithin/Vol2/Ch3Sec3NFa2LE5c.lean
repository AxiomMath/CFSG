module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE5cA

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem leaf_E5c_of (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    Leaf_E5c := by
  intro hG1 hG4 G _ _ T M L D H K q c x hx
  have hxN₀ : x ∈ a2G2 K T ⊓ Subgroup.normalizer (a2Vp L T H : Set G) :=
    ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    c.normalizer_Vp_le_normalizer_R hG1 hG4 h36 h5 h7 h9 hGA h128 h37 h38 h39 hxN₀
  have hxM : x ∈ M := c.normalizer_le_M h5 h7 h9 hxR
  have hM := (h5 G T M L c.nf.hyp.toSetup331).1
  rw [c.mPlus_eq] at hM
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := by
    rw [hM] at hxM
    exact hxM
  obtain ⟨m, y₀, hy₀Y, hy₀L, hy₀α⟩ := c.exists_vmod h36 h5 h7 h9 hGA h128 h37 h38 h39
  have hxZ : x ∈ Subgroup.centralizer (a2Z T : Set G) := c.G2_le_centralizer_Z h36 hx.1
  have hVeq : vPlus L T = conjClosure (quasithinOmegaOneCenter T) L := by
    show conjClosure (quasithinOmegaOneCenter T) (mPlus L T) = _
    rw [c.mPlus_eq]
  have hxV : x ∈ Subgroup.normalizer (a2V L T : Set G) := by
    show x ∈ Subgroup.normalizer (vPlus L T : Set G)
    rw [hVeq]
    exact mem_normalizer_conjClosure_of hxL (Subgroup.centralizer_le_normalizer _ hxZ)
  exact m.centralizes hxL hxV hxZ hx.2 ⟨y₀, hy₀Y, hy₀L, hy₀α⟩

end CFSG.Quasithin.H13.NFa2
