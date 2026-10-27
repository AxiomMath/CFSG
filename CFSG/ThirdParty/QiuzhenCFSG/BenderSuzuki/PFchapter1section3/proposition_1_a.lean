module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Proposition 1(a)
-/

private theorem proposition_1_a_restricted_hypothesisA1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q X : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ peterfalviV D t) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let ΩX : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
    let HX : Subgroup L := H.comap L.subtype
    let DX : Subgroup L := D.comap L.subtype
    let QX : Subgroup L := Q.comap L.subtype
    let tX : L := ⟨t, t_mem_centralizer_of_le_peterfalviV D (peterfalviV D t) X t hX_le_V rfl⟩
    @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX := by
  classical
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let ΩX : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
  let HX : Subgroup L := H.comap L.subtype
  let DX : Subgroup L := D.comap L.subtype
  let QX : Subgroup L := Q.comap L.subtype
  let tX : L := ⟨t, t_mem_centralizer_of_le_peterfalviV D (peterfalviV D t) X t hX_le_V rfl⟩
  change @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX
  have hX_le_D : X ≤ D := fun x hx => (hX_le_V hx).1
  have hfixed : 3 ≤ Nat.card ΩX := by
    simpa [ΩX] using proposition_5_fixed_point_card_ge_three
      H D Q t s hA1 hsH hsI hsStructure X hX_ne hX_le_V
  have h6 := proposition_6_a H D Q X t hA1 hX_le_D hfixed
  refine
    { two_transitive := ?_
      point_stabilizer := ?_
      involution_t := ?_
      t_not_mem_H := ?_
      D_eq := ?_
      Q_le_H := ?_
      D_le_H := ?_
      Q_normal_in_H := ?_
      Q_disjoint_D := ?_
      Q_sup_D := ?_
      Q_even := ?_
      D_odd := ?_ }
  · rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab' : (a : Ω) ≠ (b : Ω) := fun h => hab (Subtype.ext h)
    have hcd' : (c : Ω) ≠ (d : Ω) := fun h => hcd (Subtype.ext h)
    rcases h6.1 (a : Ω) (b : Ω) (c : Ω) (d : Ω)
        a.2 b.2 c.2 d.2 hab' hcd' with ⟨g, hgL, hga, hgb⟩
    refine ⟨⟨g, hgL⟩, ?_, ?_⟩
    · exact Subtype.ext hga
    · exact Subtype.ext hgb
  · rcases hA1.point_stabilizer with ⟨base, hHbase⟩
    have hbase_fixed : base ∈ fixedPointsOfSubgroup G Ω X := by
      intro x hx
      have hxH : x ∈ H := hA1.D_le_H (hX_le_D hx)
      simpa [hHbase, MulAction.mem_stabilizer_iff] using hxH
    let baseX : ΩX := ⟨base, hbase_fixed⟩
    refine ⟨baseX, ?_⟩
    ext l
    constructor
    · intro hl
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      have hlH : (l : G) ∈ H := hl
      change (l : G) • base = base
      simpa [hHbase, MulAction.mem_stabilizer_iff] using hlH
    · intro hl
      change (l : G) ∈ H
      have hfix : (l : G) • base = base := by
        have := MulAction.mem_stabilizer_iff.mp hl
        exact congrArg Subtype.val this
      simpa [hHbase, MulAction.mem_stabilizer_iff] using hfix
  · simpa [tX, IsInvolution] using hA1.involution_t
  · intro htH
    exact hA1.t_not_mem_H htH
  · ext x
    constructor
    · intro hxD
      have hxD' : (x : G) ∈ D := hxD
      rw [hA1.D_eq] at hxD'
      refine ⟨hxD'.1, ?_⟩
      rcases hxD'.2 with ⟨y, hyH, hyx⟩
      have hy_eq : y = t * (x : G) * t⁻¹ := by
        calc
          y = t * ((MulAut.conj t⁻¹) y) * t⁻¹ := by simp [mul_assoc]
          _ = t * (x : G) * t⁻¹ := congrArg (fun z : G => t * z * t⁻¹) hyx
      have hyL : y ∈ L := by
        rw [hy_eq]
        exact L.mul_mem (L.mul_mem tX.property x.property) (L.inv_mem tX.property)
      refine ⟨⟨y, hyL⟩, hyH, ?_⟩
      apply Subtype.ext
      exact hyx
    · rintro ⟨hxH, hxR⟩
      have hxR' : (x : G) ∈ rightConjugate H t := by
        rcases hxR with ⟨y, hyH, hyx⟩
        refine ⟨(y : G), hyH, ?_⟩
        exact congrArg Subtype.val hyx
      change (x : G) ∈ D
      rw [hA1.D_eq]
      exact ⟨hxH, hxR'⟩
  · intro x hx
    exact hA1.Q_le_H hx
  · intro x hx
    exact hA1.D_le_H hx
  · rw [Subgroup.normal_subgroupOf_iff]
    · intro q h qQ hH
      change (h * q * h⁻¹ : L) ∈ QX
      exact
        (Subgroup.normal_subgroupOf_iff hA1.Q_le_H).mp hA1.Q_normal_in_H
          (q : G) (h : G) qQ hH
    · intro x hx
      exact hA1.Q_le_H hx
  · rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      change x = 1
      apply Subtype.ext
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
        hA1.Q_disjoint_D.le_bot ⟨hx.1, hx.2⟩
      simpa using hxbot
    · exact bot_le
  · change Q.subgroupOf L ⊔ D.subgroupOf L = H.subgroupOf L
    rw [← Subgroup.inf_subgroupOf_right Q L,
      ← Subgroup.inf_subgroupOf_right D L,
      ← Subgroup.inf_subgroupOf_right H L]
    rw [inf_comm Q L, inf_comm D L, inf_comm H L]
    rw [← Subgroup.subgroupOf_sup inf_le_left inf_le_left, h6.2.2.2.2.2]
  · change Even (Nat.card (Q.subgroupOf L))
    rw [← Subgroup.inf_subgroupOf_right Q L]
    rw [natCard_subgroupOf_eq (Q ⊓ L) L inf_le_right, inf_comm]
    exact proposition_6_b H D Q X t hA1 hX_le_D hfixed
  · change Odd (Nat.card (D.subgroupOf L))
    rw [← Subgroup.inf_subgroupOf_right D L]
    rw [natCard_subgroupOf_eq (D ⊓ L) L inf_le_right, inf_comm]
    exact hA1.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)


private theorem proposition_1_a_restricted_action_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let ΩX : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
    let HX : Subgroup L := H.comap L.subtype
    let DX : Subgroup L := D.comap L.subtype
    let QX : Subgroup L := Q.comap L.subtype
    let tX : L :=
      ⟨t, t_mem_centralizer_of_le_peterfalviV D V X t hX_le_V hsec.section2.V_eq⟩
    @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX ∧
      (let NL : Subgroup G :=
        (L ⊓ D) ⊓ Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G)
       (∀ n : L, n ∈ pointStabilizerCore L ΩX ↔ (n : G) ∈ NL) ∧
        NL ≤ L ⊓ V) := by
  classical
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let ΩX : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
  let HX : Subgroup L := H.comap L.subtype
  let DX : Subgroup L := D.comap L.subtype
  let QX : Subgroup L := Q.comap L.subtype
  let tX : L :=
    ⟨t, t_mem_centralizer_of_le_peterfalviV D V X t hX_le_V hsec.section2.V_eq⟩
  change @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX ∧
    (let NL : Subgroup G :=
      (L ⊓ D) ⊓ Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G)
     (∀ n : L, n ∈ pointStabilizerCore L ΩX ↔ (n : G) ∈ NL) ∧ NL ≤ L ⊓ V)
  have hA1 : HypothesisA1 G Ω H D Q t := hsec.section2.hA.A1
  have hX_le_pV : X ≤ peterfalviV D t := by
    simpa [← hsec.section2.V_eq] using hX_le_V
  have hA1X : @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX :=
    proposition_1_a_restricted_hypothesisA1 H D Q X t s hA1 hsec.s_mem_H hsec.s_involution
      hsec.s_conjugate hX_ne hX_le_pV
  refine ⟨hA1X, ?_⟩
  rcases proposition_4_b HX DX QX tX hA1X with ⟨p, hp, _hp_unique⟩
  have h4c := proposition_4_c HX DX QX tX p.1 hA1X hp.1 hp.2.1
    ⟨p.2, hp.2.2.1, hp.2.2.2⟩
  let NL : Subgroup G :=
    (L ⊓ D) ⊓ Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G)
  change (∀ n : L, n ∈ pointStabilizerCore L ΩX ↔ (n : G) ∈ NL) ∧ NL ≤ L ⊓ V
  have hcoreIff : ∀ n : L, n ∈ pointStabilizerCore L ΩX ↔ (n : G) ∈ NL := by
    intro n
    rw [h4c.1]
    constructor
    · intro hn
      refine ⟨⟨n.property, hn.1⟩, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      let qL : L := ⟨q, hq.1⟩
      have hqQX : qL ∈ QX := hq.2
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hn.2 qL hqQX)
    · intro hn
      refine ⟨hn.1.2, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      have hcomm := (Subgroup.mem_centralizer_iff.mp hn.2) (q : G) ⟨q.property, hq⟩
      exact Subtype.ext hcomm
  refine ⟨hcoreIff, ?_⟩
  intro n hn
  refine ⟨hn.1.1, ?_⟩
  let nL : L := ⟨n, hn.1.1⟩
  have hnCore : nL ∈ pointStabilizerCore L ΩX := (hcoreIff nL).2 hn
  have hnVx : nL ∈ peterfalviV DX tX := h4c.2.1 hnCore
  change nL ∈ DX ⊓ Subgroup.centralizer ({tX} : Set L) at hnVx
  rw [hsec.section2.V_eq]
  refine ⟨hnVx.1, ?_⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_singleton_iff.mp hnVx.2)

public theorem proposition_1_a
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ V) :
    let L : Subgroup G := Subgroup.centralizer (X : Set G)
    let ΩX : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
    let HX : Subgroup L := H.comap L.subtype
    let DX : Subgroup L := D.comap L.subtype
    let QX : Subgroup L := Q.comap L.subtype
    let tX : L :=
      ⟨t, t_mem_centralizer_of_le_peterfalviV D V X t hX_le_V hsec.section2.V_eq⟩
    @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX ∧
      (let NL : Subgroup G :=
        (L ⊓ D) ⊓ Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G)
       (∀ n : L, n ∈ pointStabilizerCore L ΩX ↔ (n : G) ∈ NL) ∧
        NL ≤ L ⊓ V) :=
  proposition_1_a_restricted_action_obligation
    H D Q K V W Q0 S Q1 X t s hsec hX_ne hX_le_V

public theorem proposition_1_a_pair_transitive_on_fixed_points
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 X : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ V) :
    ∀ a b c d : Ω,
      a ∈ fixedPointsOfSubgroup G Ω X →
      b ∈ fixedPointsOfSubgroup G Ω X →
      c ∈ fixedPointsOfSubgroup G Ω X →
      d ∈ fixedPointsOfSubgroup G Ω X →
      a ≠ b → c ≠ d →
        ∃ g : G, g ∈ Subgroup.centralizer (X : Set G) ∧ g • a = c ∧ g • b = d := by
  classical
  let L : Subgroup G := Subgroup.centralizer (X : Set G)
  let ΩX : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  letI : MulAction L ΩX := fixedPointCentralizerAction G Ω X
  let HX : Subgroup L := H.comap L.subtype
  let DX : Subgroup L := D.comap L.subtype
  let QX : Subgroup L := Q.comap L.subtype
  let tX : L :=
    ⟨t, t_mem_centralizer_of_le_peterfalviV D V X t hX_le_V hsec.section2.V_eq⟩
  have hA1X : @HypothesisA1 L ΩX inferInstance inferInstance inferInstance inferInstance HX DX QX tX :=
    (proposition_1_a H D Q K V W Q0 S Q1 X t s hsec hX_ne hX_le_V).1
  intro a b c d ha hb hc hd hab hcd
  let aX : ΩX := ⟨a, ha⟩
  let bX : ΩX := ⟨b, hb⟩
  let cX : ΩX := ⟨c, hc⟩
  let dX : ΩX := ⟨d, hd⟩
  have habX : aX ≠ bX := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hcdX : cX ≠ dX := by
    intro h
    exact hcd (congrArg Subtype.val h)
  rcases (MulAction.is_two_pretransitive_iff.mp hA1X.two_transitive) habX hcdX with
    ⟨g, hga, hgb⟩
  refine ⟨g, g.property, ?_, ?_⟩
  · exact congrArg Subtype.val hga
  · exact congrArg Subtype.val hgb

end PFchapter1section3
end CFSG.BenderSuzuki
