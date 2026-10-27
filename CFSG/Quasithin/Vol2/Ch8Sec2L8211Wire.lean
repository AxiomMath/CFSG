module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8211Parts
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

@[expose] def Stmt8_2_11_comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    Hyp7_3_1 T L I → Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
    ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ch8Lz L z ∈ cComp (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G))


theorem stmt8_2_11_modules_of_comp'
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal)
    (h822 : Stmt8_2_2) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12)
    (hm24 : SchurMult2M24) (h1 : Stmt8_2_11_comp) : Stmt8_2_11_modules :=
  stmt8_2_11_modules_of_comp h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829
    kg82CoverL34_holds kg82CoverM22_holds hm24 h1

theorem stmt8_2_13_of_comp
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal)
    (h822 : Stmt8_2_2) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12)
    (h8293 : Stmt8_2_9_three) (h8210 : Stmt8_2_10) (h1 : Stmt8_2_11_comp)
    (h8212 : Stmt8_2_12) (hm24 : SchurMult2M24) : Stmt8_2_13 :=
  stmt8_2_13_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 h8293 h8210 h8212
      (step8_2_13_insp_of h8210
          (stmt8_2_11_modules_of_comp' h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hm24 h1)
          h8212) hm24

end CFSG.Quasithin.H13
