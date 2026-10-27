module

import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Inv143Q (A : Subgroup G) (a d : G) (X : Subgroup G) : Prop :=
  Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) ∨
    (Subgroup.zpowers a = Subgroup.zpowers d ∧ X ∈ thetaComponentsAt 3 a ∧
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∧
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer
          ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G))

@[expose] noncomputable def Desc143Case2QAt (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (a : G) : Prop :=
  ∃ (b d : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧
    Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn Lb d ∧ a ∈ Subgroup.closure {b, d} ∧
    ∃ X : Subgroup G,
      delta A LB (Subgroup.centralizer ({a} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X ∧
      Inv143Q A a d X ∧
      ((X ∈ thetaComponentsAt 3 a ∧
          X = LB (Subgroup.closure {a, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
          Subgroup.zpowers a ≠ Subgroup.zpowers d) ∨
        (Subgroup.zpowers a = Subgroup.zpowers d ∧
          (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
          (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              CFSG.Blueprint.NativeSporadic.ON ∨
            Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              (alternatingGroup (Fin 6)) ∨
            IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))))

@[expose] noncomputable def Item143QAt (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (a : G) : Prop :=
  ∀ Q ∈ maxInvariantPiSubgroups (delta A LB (Subgroup.centralizer ({a} : Set G))) A
      (piCompl 3),
    Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer ({a} : Set G)) ∧
    (delta A LB (Subgroup.centralizer ({a} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∨
      Desc143Case2QAt A LB a)

@[expose] noncomputable def Item143Q (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A → Item143QAt A LB a

@[expose] noncomputable def Item143QS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item143Q A (lB A)

@[expose] noncomputable def Item143NNHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ¬ AllPointsHJ A → Item143N A (lB A)

@[expose] noncomputable def HJConfig143Q (A : Subgroup G) (b : G) : Prop :=
  Desc143Case2QAt A (lB A) b

@[expose] noncomputable def Step148PointHJQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
        ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        HJConfig143Q A b →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

@[expose] def Step143HJDescTwoQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Subgroup.zpowers a = Subgroup.zpowers d →
          ∃ (b' d' : G) (Lb' : Subgroup G), Subgroup.zpowers b' ∈ omegaA A ∧ Lb' ∈ lA A b' ∧
            Nonempty (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
            d' ∈ A ∧ d' ≠ 1 ∧ IsThreeCentralIn Lb' d' ∧ a ∈ Subgroup.closure {b', d'} ∧
            ∃ X : Subgroup G,
              X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∧
              (∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
                lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ∧
              Inv143Q A a d' X ∧
              ((X ∈ thetaComponentsAt 3 a ∧
                  X = lB A (Subgroup.closure {a, b'}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
                  Subgroup.zpowers a ≠ Subgroup.zpowers d') ∨
                (Subgroup.zpowers a = Subgroup.zpowers d' ∧
                  (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
                  (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                      CFSG.Blueprint.NativeSporadic.ON ∨
                    Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                      (alternatingGroup (Fin 6)) ∨
                    IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))))

@[expose] def Step143HJDescXQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb →
          ∃ (b' d' : G) (Lb' : Subgroup G), Subgroup.zpowers b' ∈ omegaA A ∧ Lb' ∈ lA A b' ∧
            Nonempty (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
            d' ∈ A ∧ d' ≠ 1 ∧ IsThreeCentralIn Lb' d' ∧ a ∈ Subgroup.closure {b', d'} ∧
            ∃ X : Subgroup G,
              X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∧
              (∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
                lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ∧
              Inv143Q A a d' X ∧
              ((X ∈ thetaComponentsAt 3 a ∧
                  X = lB A (Subgroup.closure {a, b'}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
                  Subgroup.zpowers a ≠ Subgroup.zpowers d') ∨
                (Subgroup.zpowers a = Subgroup.zpowers d' ∧
                  (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
                  (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                      CFSG.Blueprint.NativeSporadic.ON ∨
                    Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                      (alternatingGroup (Fin 6)) ∨
                    IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))))

@[expose] def Step143HJDescFixQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb →
          ∃ (b' d' : G) (Lb' : Subgroup G), Subgroup.zpowers b' ∈ omegaA A ∧ Lb' ∈ lA A b' ∧
            Nonempty (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
            d' ∈ A ∧ d' ≠ 1 ∧ IsThreeCentralIn Lb' d' ∧ a ∈ Subgroup.closure {b', d'} ∧
            ∃ X : Subgroup G,
              X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∧
              (∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
                lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ∧
              Inv143Q A a d' X ∧
              ((X ∈ thetaComponentsAt 3 a ∧
                  X = lB A (Subgroup.closure {a, b'}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
                  Subgroup.zpowers a ≠ Subgroup.zpowers d') ∨
                (Subgroup.zpowers a = Subgroup.zpowers d' ∧
                  (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
                  (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                      CFSG.Blueprint.NativeSporadic.ON ∨
                    Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                      (alternatingGroup (Fin 6)) ∨
                    IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)))) ∧
              ∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
                ∀ R : Subgroup G,
                  R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
                    Subgroup.centralizer (D : Set G) →
                  ¬ 3 ∣ Nat.card R → A ≤ Subgroup.normalizer (R : Set G) → R = ⁅R, A⁆ →
                    R ≤ qBound A (lB A) D

@[expose] def Step143HJQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Item143QAt A (lB A) a

omit [Finite G] in
theorem Inv143Q.inf_le {A : Subgroup G} {a d : G} {X : Subgroup G} (h : Inv143Q A a d X) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) :=
  h.elim (fun h => inf_le_left.trans h) fun h => h.2.2.2

omit [Finite G] in
theorem Inv143Q.le_normalizer {A : Subgroup G} {a d : G} {X : Subgroup G} (h : Inv143Q A a d X)
    (hA : IsMulCommutative A) (ha : a ∈ A) :
    A ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) :=
  fun x hx => h.inf_le ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩)), Subgroup.le_normalizer hx⟩

omit [Finite G] in
theorem Inv143Q.centralizer_le {A : Subgroup G} {a d : G} {X : Subgroup G} (h : Inv143Q A a d X)
    (ha : a ∈ A) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) :=
  fun x hx => h.inf_le ⟨Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) hx,
    Subgroup.centralizer_le_normalizer (A : Set G) hx⟩

theorem item143_of_item143Q {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : Item143Q A LB) : Item143 A LB := fun a ha ha1 hΩ Q hQ =>
  (h a ha ha1 hΩ Q hQ).imp_right (Or.imp_right fun ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, hab,
    X, hX, _, hcase⟩ => ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, hab, X, hX, hcase⟩)

theorem concl143_of_item143Q {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : Item143Q A LB) : Concl143 A LB := fun a ha ha1 hΩ Q hQ => (h a ha ha1 hΩ Q hQ).1

theorem item143N_of_item143Q_of_not_allPointsHJ (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hNHJ : ¬ AllPointsHJ A) (hq : Item143Q A (lB A)) : Item143N A (lB A) := by
  intro a ha ha1 hΩ Q hQ
  obtain ⟨hQq, h1 | ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, -⟩⟩ := hq a ha ha1 hΩ Q hQ
  · exact ⟨hQq, Or.inl h1⟩
  · exact (hNHJ fun e he => exists_hj_of_hj_point h134 h48 h415 h hb hLb hJ hdA hd1 hdc he).elim

theorem item143NNHJ_of_item143QS14 (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hq : Item143QS14) : Item143NNHJ := fun G _ _ A c L h hNHJ =>
  item143N_of_item143Q_of_not_allPointsHJ h134 h48 h415 h hNHJ (hq G A c L h)

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
