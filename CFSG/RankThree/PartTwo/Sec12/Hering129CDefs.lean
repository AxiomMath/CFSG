module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def IsType122 (X : Type) [Group X] : Prop :=
  Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
    Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22

structure Census129 {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] (c a : Q) (I X : Subgroup Q)
    (f : ↥I →* Lb) : Prop where
  quasisimple : CFSG.IsQuasisimple Q
  theta_eq_bot : aschbacherSolvableCore 3 Q = ⊥
  sectionFourHyp : SectionFourHyp Q
  orderOf_c : orderOf c = 3
  c_mem : c ∈ I
  le_centralizer : I ≤ Subgroup.centralizer ({c} : Set Q)
  isPerfect : Group.IsPerfect I
  isSubnormal : (I.subgroupOf (Subgroup.centralizer ({c} : Set Q))).IsSubnormal
  ne_top : I ≠ ⊤
  surjective : Function.Surjective f
  ker_solvable : Group.IsSolvable f.ker
  ker_three : ¬ 3 ∣ Nat.card f.ker
  quasisimple_Lb : CFSG.IsQuasisimple Lb
  type_Lb : IsType122 Lb
  a_mem : a ∈ I
  orderOf_a : orderOf a = 3
  a_not_mem : a ∉ Subgroup.zpowers c
  le_X : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ X
  X_le : X ≤ (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ⊔ Subgroup.center Q
  beta : ∀ t : Q, t ∈ Subgroup.centralizer
    ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup Q) : Set Q) → t ^ 3 = 1 → t ∈ X
  gamma : Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup Q) : Set Q) ≤
    Subgroup.normalizer (Subgroup.zpowers c : Set Q)
  eps : ∀ F : Subgroup Q, F ≤ I → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 → c ∈ F →
    Subgroup.normalizer (F : Set Q) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Q)

@[expose] def CensusConcl (Q Lb : Type) [Group Q] [Group Lb] : Prop :=
  (Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      Sec4.IsTripleCover Lb (alternatingGroup (Fin 6))) ∨
    ∃ q : TauCeti.PrimePower, Sec4.IsSLThreePiAt Lb q.card ∧
      (Sec4.IsoGTwo Q q ∨ ∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid,
        Nonempty (Q ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))

@[expose] def KFCensusOn (P : ∀ (Q : Type) [Group Q], Prop) : Prop :=
  ∀ (Q Lb : Type) [Group Q] [Finite Q] [Group Lb] (c a : Q) (I X : Subgroup Q) (f : ↥I →* Lb),
    P Q → Census129 c a I X f → CensusConcl Q Lb

@[expose] def KFCensus : Prop := KFCensusOn (fun Q _ => Sec4.IsList46 Q)

@[expose] def KFCensus46One : Prop := KFCensusOn (fun Q _ => Sec4.IsList46One Q)

@[expose] def KFCensus46Two : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Two Q)

@[expose] def KFCensus46Three : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Three Q)

@[expose] def KFCensus46Four : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Four Q)

@[expose] def KFCensus46Five : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Five Q)

@[expose] def KFCensus46Six : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Six Q)

@[expose] def KFCensus46Seven : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Seven Q)

@[expose] def KFCensus46Eight : Prop := KFCensusOn (fun Q _ => Sec4.IsList46Eight Q)

theorem kFCensus_of_families (h1 : KFCensus46One) (h2 : KFCensus46Two) (h3 : KFCensus46Three)
    (h4 : KFCensus46Four) (h5 : KFCensus46Five) (h6 : KFCensus46Six) (h7 : KFCensus46Seven)
    (h8 : KFCensus46Eight) : KFCensus := by
  intro Q Lb _ _ _ c a I X f hQ d
  rcases (Sec4.isList46_iff Q).mp hQ with h | h | h | h | h | h | h | h
  · exact h1 Q Lb c a I X f h d
  · exact h2 Q Lb c a I X f h d
  · exact h3 Q Lb c a I X f h d
  · exact h4 Q Lb c a I X f h d
  · exact h5 Q Lb c a I X f h d
  · exact h6 Q Lb c a I X f h d
  · exact h7 Q Lb c a I X f h d
  · exact h8 Q Lb c a I X f h d

end CFSG.RankThree.PartTwo.Sec12
