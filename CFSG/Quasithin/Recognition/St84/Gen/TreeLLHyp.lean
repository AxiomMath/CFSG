module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLMin
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.St84 CFSG.Quasithin.Fan86
  CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112ll_locTransBase {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112EOdd L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseA (f112Gold L1 L2 S)), g • a = b) ∧
    (∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112EOdd L1 L2 S ⊓
        MulAction.stabilizer (f112Gold L1 L2 S).Universal
          (baseB (f112Gold L1 L2 S)), g • a = b) := by
  constructor
  · intro a b ha hb
    obtain ⟨g, hgMA, hgab⟩ := f112llMA_trans hF hm h1 a b ha hb
    refine ⟨g, ⟨f112sa_oTwoRes_left_map_le_EOdd hgMA, ?_⟩, hgab⟩
    rw [stabilizer_baseA]
    exact f112llMA_le_range L1 L2 S hgMA
  · intro a b ha hb
    obtain ⟨g, hgMB, hgab⟩ := f112slMB_trans hF hn h2 a b ha hb
    refine ⟨g, ⟨f112slMB_le_E hgMB, ?_⟩, hgab⟩
    rw [stabilizer_baseB]
    exact f112saMB_le_range L1 L2 S hgMB

theorem f112ll_edgeTransitive {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    EdgeTransitive (f112Gold L1 L2 S).treeGraph (f112EOdd L1 L2 S) := by
  obtain ⟨hα, hβ⟩ := f112ll_locTransBase hF hm hn h1 h2
  exact edgeTransitive_of_locTrans (f112Gold L1 L2 S).treeGraph_isTree.connected
    (adj_smul (f112Gold L1 L2 S)) (f112EOdd L1 L2 S)
    (adj_baseA_baseB (f112Gold L1 L2 S)) hα hβ

theorem f112ll_edgeTransitive_top {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    EdgeTransitive (f112Gold L1 L2 S).treeGraph (⊤ : Subgroup ↥(f112EOdd L1 L2 S)) := by
  intro u v u' v' huv hu'v'
  obtain ⟨g, hg, hmap⟩ := f112ll_edgeTransitive hF hm hn h1 h2 u v u' v' huv hu'v'
  exact ⟨⟨g, hg⟩, Subgroup.mem_top _, hmap⟩

theorem f112ll_sup_edgeStab {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    f112EOdd L1 L2 S ⊔
        (MulAction.stabilizer (f112Gold L1 L2 S).Universal
            (baseA (f112Gold L1 L2 S)) ⊓
          MulAction.stabilizer (f112Gold L1 L2 S).Universal
            (baseB (f112Gold L1 L2 S))) = ⊤ :=
  sup_eq_top_of_edgeTransitive (adj_smul (f112Gold L1 L2 S))
    (f112sa_preservesParts L1 L2 S) (adj_baseA_baseB (f112Gold L1 L2 S))
    (f112ll_edgeTransitive hF hm hn h1 h2)

theorem f112ll_EOdd_normal {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (f112EOdd L1 L2 S).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  rw [← f112ll_sup_edgeStab hF hm hn h1 h2]
  exact sup_le Subgroup.le_normalizer (f112sa_edgeStab_le_normalizer L1 L2 S)

theorem f112ll_charTwoStab {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CharTwoStab (V := Vtx (f112Gold L1 L2 S)) (G := ↥(f112EOdd L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  intro v
  let X := f112Gold L1 L2 S
  let Uv : Subgroup X.Universal := MulAction.stabilizer X.Universal v
  let E := f112EOdd L1 L2 S
  haveI hUvfin : Finite Uv := finite_stabilizer X v
  have hEn : (E.subgroupOf Uv).Normal := (f112ll_EOdd_normal hF hm hn h1 h2).subgroupOf Uv
  have hEq : E.subgroupOf Uv = (E ⊓ Uv).subgroupOf Uv := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hcharU : CharTwo Uv := f112_charTwo_stabilizer_of_hyp111R hR v
  have hcharSub : CharTwo ((E ⊓ Uv).subgroupOf Uv) := by
    have hHn : ((E ⊓ Uv).subgroupOf Uv).Normal := by rw [← hEq]; exact hEn
    exact CFSG.Quasithin.A4.charTwo_of_normal (H := (E ⊓ Uv).subgroupOf Uv)
      (N := ⊤) le_top (Subgroup.le_normalizer_of_normal) (f112_charTwo_top hcharU)
  have hcharI : CharTwo (E ⊓ Uv) :=
    CFSG.Quasithin.F6.charTwo_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ Uv ≤ Uv)) hcharSub
  have hstab : MulAction.stabilizer ↥E v = (Uv).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E v]
  rw [hstab]
  let e : ↥(E ⊓ Uv) ≃* ↥((Uv).subgroupOf E) :=
  { toFun := fun x => ⟨⟨(x : X.Universal), x.2.1⟩, x.2.2⟩
    invFun := fun x => ⟨(x.1 : X.Universal), ⟨x.1.2, x.2⟩⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun x => by ext; rfl
    map_mul' := fun x y => by ext; rfl }
  exact CFSG.Quasithin.F6.charTwo_of_mulEquiv e hcharI

theorem f112ll_localL2 {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∀ v : Vtx (f112Gold L1 L2 S), ∃ N : Subgroup ↥(f112EOdd L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) v
        (nOf (f112Gold L1 L2 S).treeGraph v) N := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  intro v
  let X := f112Gold L1 L2 S
  let E := f112EOdd L1 L2 S
  obtain ⟨w, hw⟩ := f112sa_exists_adj (L1 := L1) (L2 := L2) (S := S) v
  obtain ⟨g, -, hcase⟩ := f112ll_edgeTransitive_top hF hm hn h1 h2
    (baseA X) (baseB X) v w (adj_baseA_baseB X) hw
  have hadjE : ∀ (k : ↥E) (u w : Vtx X),
      X.treeGraph.Adj (k • u) (k • w) ↔ X.treeGraph.Adj u w :=
    fun k u w => adj_smul X (k : X.Universal) u w
  rcases hcase with ⟨hga, -⟩ | ⟨-, hgb⟩
  · obtain ⟨N, hN⟩ := f112ll_localL2_baseA hF hm h1
    refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_⟩
    have htrans := IsLocL2.smul (Γ := X.treeGraph) hadjE hN g
    have hnα : nOf X.treeGraph (g • baseA X) = m :=
      f112_nOf_alpha_of_isL2Quot hR (by omega) h1 (g : X.Universal)
    rw [← hga, hnα]
    exact htrans
  · obtain ⟨N, hN⟩ := f112sl_localL2_baseB hF hn h2
    refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_⟩
    have htrans := IsLocL2.smul (Γ := X.treeGraph) hadjE hN g
    have hnβ : nOf X.treeGraph (g • baseB X) = n :=
      f112_nOf_beta_of_isL2Quot hR (by omega) h2 (g : X.Universal)
    rw [← hgb, hnβ]
    exact htrans

theorem f112ll_hyp30 {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp30 (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S) where
  isTree := (f112Gold L1 L2 S).treeGraph_isTree
  adj_smul := by
    intro g u v
    exact adj_smul (f112Gold L1 L2 S) (g : (f112Gold L1 L2 S).Universal) u v
  faithful := by
    intro g hg
    apply Subtype.ext
    exact f112_faithful_of_hyp111R
      (hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2)
      (g : (f112Gold L1 L2 S).Universal) (fun v => hg v)
  edgeTrans := f112ll_edgeTransitive_top hF hm hn h1 h2
  minimal := f112ll_minimality hF hm hn h1 h2
  finite_stab := by
    intro v
    haveI : Finite ↥(f112P1 L1 L2 S) := Subtype.finite
    haveI : Finite ↥(f112P2 L1 L2 S) := Subtype.finite
    haveI hfin : Finite (MulAction.stabilizer (f112Gold L1 L2 S).Universal v) :=
      finite_stabilizer (f112Gold L1 L2 S) v
    rw [← MulAction.stabilizer_subgroupOf (f112EOdd L1 L2 S) v]
    exact Finite.of_injective
      (fun x : ↥((MulAction.stabilizer (f112Gold L1 L2 S).Universal v).subgroupOf
          (f112EOdd L1 L2 S)) =>
        (⟨(x.1 : (f112Gold L1 L2 S).Universal), x.2⟩ :
          ↥(MulAction.stabilizer (f112Gold L1 L2 S).Universal v)))
      (by
        intro a b h
        have hU : (a.1.1 : (f112Gold L1 L2 S).Universal) = b.1.1 :=
          congrArg (fun x : ↥(MulAction.stabilizer (f112Gold L1 L2 S).Universal v) =>
            (x : (f112Gold L1 L2 S).Universal)) h
        exact Subtype.ext (Subtype.ext hU))
  valency := fun v => f112_valency_of_isL2Quot
    (hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2) (by omega) (by omega) h1 h2 v
  locL2 := f112ll_localL2 hF hm hn h1 h2

end CFSG.Quasithin.F112R.St84
