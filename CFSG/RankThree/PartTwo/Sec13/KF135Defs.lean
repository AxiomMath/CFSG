module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKF135

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.RankThree.PartTwo.Sec13.F135Last

structure KF135Hyp (S : Type) [Group S] [Finite S] (p : ℕ) (P : Subgroup (MulAut S))
    (x u : MulAut S) (V : Subgroup (MulAut S)) : Prop where
  simple : IsSimpleGroup S
  nonab : ∃ a b : S, a * b ≠ b * a
  prime : p.Prime
  seven_le : 7 ≤ p
  pgroup : IsPGroup p P
  card : p ^ 3 ≤ Nat.card P
  exponent : ∀ y ∈ P, y ^ p = 1
  x_mem : x ∈ P
  x_order : orderOf x = p
  u_ne : u ≠ 1
  u_two : ∃ k : ℕ, u ^ 2 ^ k = 1
  u_comm : u * x = x * u
  V_ne : V ≠ ⊥
  V_two : IsPGroup 2 V
  V_norm : ∀ v ∈ V, x * v * x⁻¹ ∈ V
  V_comm : ⁅V, Subgroup.zpowers x⁆ = V
  h2a : ∀ F : Subgroup (MulAut S), F ≤ (MulAut.conj : S →* MulAut S).range →
    CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
    ∀ T : Subgroup S, T ≠ ⊥ → IsPGroup 2 T → ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T
  h2b : ∀ F : Subgroup (MulAut S), F ≤ P → CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
    ∀ T : Subgroup S, T ≠ ⊥ → IsPGroup 2 T → ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T

@[expose] def Fam1 (G : Type) [Group G] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ Nonempty (G ≃* projSL 2 (GaloisField p e))

@[expose] def Fam2 (G : Type) [Group G] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
    (Nonempty (G ≃* projSL 3 (GaloisField p e)) ∨ Nonempty (G ≃* projSU 3 p e))

@[expose] def Fam3 (G : Type) [Group G] : Prop :=
  ∃ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)

@[expose] def Fam4 (G : Type) [Group G] : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoGTwo G q) ∨
      Nonempty (G ≃* projSp 2 (GaloisField p 1)) ∨
      Nonempty (G ≃* projSL 4 (GaloisField p 1)) ∨ Nonempty (G ≃* projSU 4 p 1))

@[expose] def Fam5 (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (G ≃* alternatingGroup (Fin n))

@[expose] def Fam6 (G : Type) [Group G] : Prop :=
  ∃ s ∈ sporadics42, Nonempty (G ≃* Spor s)

@[expose] def Fam7 (G : Type) [Group G] : Prop :=
  IsChevTwoRankTwo G

@[expose] def Fam8 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 5 2 1) ∨
    Nonempty (G ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 6 2 1) ∨
    Nonempty (G ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 1)) ∨
    Nonempty (G ≃* projSp 4 (GaloisField 2 1)) ∨
    Nonempty (G ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
    (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
    Nonempty (G ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 2)) ∨
    Nonempty (G ≃* projSU 5 2 2) ∨ Nonempty (G ≃* projSU 5 2 3) ∨
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)

@[expose] def Fam9 (G : Type) [Group G] : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ e ≤ 3 ∧
      (Nonempty (G ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (G ≃* projSU 3 3 e))) ∨
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) ∨
    Nonempty (G ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (G ≃* projSU 4 3 1)

theorem list42_iff (G : Type) [Group G] :
    Sec4.Census.List42 G ↔ Fam1 G ∨ Fam2 G ∨ Fam3 G ∨ Fam4 G ∨ Fam5 G ∨ Fam6 G ∨ Fam7 G ∨
      Fam8 G ∨ Fam9 G :=
  Iff.rfl

@[expose] def KF135At (Fam : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (P : Subgroup (MulAut S)) (x u : MulAut S)
    (V : Subgroup (MulAut S)), Fam S → KF135Hyp S p P x u V → Identified p S

theorem kF135_of_families (h1 : KF135At Fam1) (h2 : KF135At Fam2) (h3 : KF135At Fam3)
    (h4 : KF135At Fam4) (h5 : KF135At Fam5) (h6 : KF135At Fam6) (h7 : KF135At Fam7)
    (h8 : KF135At Fam8) (h9 : KF135At Fam9) : KF135 := by
  intro S _ _ hS hnab hL p hp hp7 P hP hcard hexp x hxP hxo u hu1 hu2 hux V hV1 hV2 hVn hVc
    h2a h2b
  have hH : KF135Hyp S p P x u V :=
    ⟨hS, hnab, hp, hp7, hP, hcard, hexp, hxP, hxo, hu1, hu2, hux, hV1, hV2, hVn, hVc, h2a, h2b⟩
  rcases (list42_iff S).1 hL with hF | hF | hF | hF | hF | hF | hF | hF | hF
  · exact h1 S p P x u V hF hH
  · exact h2 S p P x u V hF hH
  · exact h3 S p P x u V hF hH
  · exact h4 S p P x u V hF hH
  · exact h5 S p P x u V hF hH
  · exact h6 S p P x u V hF hH
  · exact h7 S p P x u V hF hH
  · exact h8 S p P x u V hF hH
  · exact h9 S p P x u V hF hH

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
