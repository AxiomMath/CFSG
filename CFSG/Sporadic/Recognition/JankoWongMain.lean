module

public import CFSG.Sporadic.Recognition.JankoWongSec4Final
public import CFSG.Sporadic.Recognition.JankoWongLocal
public import CFSG.GH74.GLS.Stage12.McLRec

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem jwContains :
    Stage12.McLRec.JWContains := by
  rintro G _ _ hs hnab ⟨z, hz, -, hH⟩
  obtain ⟨S⟩ := nonempty_setup_of_doubleCover hs hnab hz.1 hH
  exact S.exists_subgroup_mulEquiv_mcl

theorem s_McL_leaf :
    Stage12.S_McL_leaf :=
  Stage12.McLRec.S_McL_leaf_of_JWContains jwContains

theorem mclRecognition :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 → Group.IsPerfect ↥(centralizer ({t} : Set G)) →
        center ↥(centralizer ({t} : Set G)) = zpowers (zIn t) →
        Nonempty (↥(centralizer ({t} : Set G)) ⧸ zpowers (zIn t) ≃* alternatingGroup (Fin 8)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.McL) := by
  intro G _ _ hs hnab t ht hperf hcen hquot
  obtain ⟨hcentral, hclass, hH⟩ :=
    oneClassDoubleCover_of_perfect_centralizer hs hnab ht hperf hcen hquot
  exact s_McL_leaf G hs hnab ⟨t, hcentral, hclass, hH⟩

end CFSG.Sporadic.Recognition.JankoWong
