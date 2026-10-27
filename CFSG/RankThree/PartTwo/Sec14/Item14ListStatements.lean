module

public import CFSG.RankThree.PartTwo.Sec13.Steps
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Alpha

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)

noncomputable abbrev k142 : Subgroup G :=
  delta A LB (Subgroup.normalizer (Subgroup.zpowers c : Set G))

noncomputable abbrev kA142 : Subgroup G := k142 A LB c ⊔ A

@[expose] noncomputable def ker142 : Subgroup ↥(kA142 A LB c) :=
  (pPrimeCoreOf 3 (k142 A LB c) ⊔ Subgroup.zpowers c).subgroupOf (kA142 A LB c)

variable {A LB c}

omit [Finite G] in
theorem ker142_normal (hAab : IsMulCommutative A) (hcA : c ∈ A) : (ker142 A LB c).Normal := by
  set K := k142 A LB c
  have hKN : K ≤ Subgroup.normalizer (pPrimeCoreOf 3 K : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hKc : K ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := delta_le _
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact congrArg Subtype.val (hAab.is_comm.comm ⟨c, hcA⟩ ⟨x, hx⟩)
  have hAO : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 K : Set G) :=
    hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hle : pPrimeCoreOf 3 K ⊔ Subgroup.zpowers c ≤ kA142 A LB c :=
    sup_le ((pPrimeCoreOf_le 3 K).trans le_sup_left)
      ((Subgroup.zpowers_le.mpr hcA).trans le_sup_right)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (sup_le ?_ ?_)
  · exact le_normalizer_sup (A := K) hKN hKc
  · exact le_normalizer_sup (A := A) hAO hAc

@[expose] noncomputable def img142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    [(ker142 A LB c).Normal] (X : Subgroup G) :
    Subgroup (↥(kA142 A LB c) ⧸ ker142 A LB c) :=
  (X.subgroupOf (kA142 A LB c)).map (QuotientGroup.mk' (ker142 A LB c))

@[expose] noncomputable def alpha142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    [(ker142 A LB c).Normal] (a : G) (ha : a ∈ A) : ↥(kA142 A LB c) ⧸ ker142 A LB c :=
  QuotientGroup.mk' (ker142 A LB c) ⟨a, Subgroup.mem_sup_right ha⟩

@[expose] noncomputable def thetaC142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    [(ker142 A LB c).Normal] (x : ↥(kA142 A LB c) ⧸ ker142 A LB c) :
    Subgroup (↥(kA142 A LB c) ⧸ ker142 A LB c) :=
  inSubgroup (aschbacherSolvableCore 3) (img142 A LB c (k142 A LB c) ⊓ Subgroup.centralizer {x})

@[expose] noncomputable def thetaCA142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    [(ker142 A LB c).Normal] : Subgroup (↥(kA142 A LB c) ⧸ ker142 A LB c) :=
  inSubgroup (aschbacherSolvableCore 3)
    (img142 A LB c (k142 A LB c) ⊓ Subgroup.centralizer (img142 A LB c A : Set _))

end Alpha

@[expose] def IsThreeCentralIn {Γ : Type*} [Group Γ] (X : Subgroup Γ) (x : Γ) : Prop :=
  ∃ hx : x ∈ X, ∃ S : Sylow 3 ↥X, (⟨x, hx⟩ : ↥X) ∈ (S : Subgroup ↥X) ∧
    (S : Subgroup ↥X) ≤ Subgroup.centralizer {(⟨x, hx⟩ : ↥X)}

@[expose] noncomputable def Item142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) (hAab : IsMulCommutative A) (hcA : c ∈ A) : Prop :=
  letI := ker142_normal (LB := LB) hAab hcA
  ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3),
    Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer ({c} : Set G)) ∧
    ((Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) ∧
        Q = k142 A LB c ∧
        pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤ k142 A LB c ∧
        Nat.card (k142 A LB c) =
          2 * Nat.card (pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) ∨
      (k142 A LB c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∧
        (((IsLThreePi ↥(img142 A LB c L) ∨
              Nonempty (↥(img142 A LB c L) ≃*
                alternatingGroup (Fin 7)) ∨
              Nonempty (↥(img142 A LB c L) ≃*
                CFSG.Blueprint.NativeSporadic.M12)) ∧
            ∃ (a : G) (ha : a ∈ A), alpha142 A LB c a ha ≠ 1 ∧
              img142 A LB c Q =
                thetaC142 A LB c (alpha142 A LB c a ha) ⊔ thetaCA142 A LB c) ∨
          (Nonempty (↥(img142 A LB c L) ≃*
              CFSG.Blueprint.NativeSporadic.M22) ∧
            (CFSG.Assembly.IsElemAbelian 2 (img142 A LB c Q) ∧
              Nat.card (img142 A LB c Q) = 16) ∧
            ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
              Subgroup.closure {alpha142 A LB c a ha, alpha142 A LB c b hb} =
                img142 A LB c A ∧
              img142 A LB c Q =
                thetaC142 A LB c (alpha142 A LB c a ha) ⊔
                  thetaC142 A LB c (alpha142 A LB c b hb) ∧
              thetaC142 A LB c (alpha142 A LB c a ha) ⊓
                  thetaC142 A LB c (alpha142 A LB c b hb) = ⊥) ∨
          (Nonempty (↥(img142 A LB c L) ≃*
              CFSG.Blueprint.NativeSporadic.J2) ∧
            (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
              Nonempty (↥(img142 A LB c Q) ≃*
                ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
            ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G) (hd : d ∈ A),
              Subgroup.closure {alpha142 A LB c a ha, alpha142 A LB c b hb} =
                img142 A LB c A ∧
              alpha142 A LB c d hd ≠ 1 ∧
              IsThreeCentralIn (img142 A LB c L) (alpha142 A LB c d hd) ∧
              Subgroup.zpowers (alpha142 A LB c a ha) ≠
                Subgroup.zpowers (alpha142 A LB c d hd) ∧
              Subgroup.zpowers (alpha142 A LB c b hb) ≠
                Subgroup.zpowers (alpha142 A LB c d hd) ∧
              img142 A LB c Q =
                thetaC142 A LB c (alpha142 A LB c a ha) ⊔
                    thetaC142 A LB c (alpha142 A LB c b hb) ⊔
                  (img142 A LB c Q ⊓
                    Subgroup.centralizer {alpha142 A LB c d hd})))))

@[expose] def IsCentralProductA6Covers (Y : Type*) [Group Y] : Prop :=
  ∃ U V : Subgroup Y, U.Normal ∧ V.Normal ∧ U ⊔ V = ⊤ ∧ ⁅U, V⁆ = ⊥ ∧
    Nat.card ↥(U ⊓ V) = 3 ∧ Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)) ∧
    Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6))

@[expose] noncomputable def Item143 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
    ∀ Q ∈ maxInvariantPiSubgroups (delta A LB (Subgroup.centralizer ({a} : Set G))) A
        (piCompl 3),
      Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer ({a} : Set G)) ∧
      (delta A LB (Subgroup.centralizer ({a} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∨
        ∃ (b d : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧
          Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn Lb d ∧ a ∈ Subgroup.closure {b, d} ∧
          ∃ X : Subgroup G,
            delta A LB (Subgroup.centralizer ({a} : Set G)) =
              pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X ∧
            ((X ∈ thetaComponentsAt 3 a ∧
                X = LB (Subgroup.closure {a, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
                Subgroup.zpowers a ≠ Subgroup.zpowers d) ∨
              (Subgroup.zpowers a = Subgroup.zpowers d ∧
                (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
                (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                    CFSG.Blueprint.NativeSporadic.ON ∨
                  Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
                    (alternatingGroup (Fin 6)) ∨
                  IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)))))


section Alpha148

@[expose] noncomputable def ker148 (A Y : Subgroup G) : Subgroup ↥(Y ⊔ A) :=
  (pPrimeCoreOf 3 Y).subgroupOf (Y ⊔ A)

omit [Finite G] in
theorem ker148_normal {A Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    (ker148 A Y).Normal := by
  have hYN : Y ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hAN : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    hY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hle : pPrimeCoreOf 3 Y ≤ Y ⊔ A := (pPrimeCoreOf_le 3 Y).trans le_sup_left
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (sup_le hYN hAN)

@[expose] noncomputable def img148 (A Y : Subgroup G) [(ker148 A Y).Normal] (X : Subgroup G) :
    Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) :=
  (X.subgroupOf (Y ⊔ A)).map (QuotientGroup.mk' (ker148 A Y))

@[expose] noncomputable def alpha148 (A Y : Subgroup G) [(ker148 A Y).Normal] (a : G)
    (ha : a ∈ A) : ↥(Y ⊔ A) ⧸ ker148 A Y :=
  QuotientGroup.mk' (ker148 A Y) ⟨a, Subgroup.mem_sup_right ha⟩

end Alpha148

@[expose] def IsA6CoverTimesA5 (X : Type*) [Group X] : Prop :=
  ∃ U V : Subgroup X, U.Normal ∧ V.Normal ∧ U ⊓ V = ⊥ ∧ U ⊔ V = ⊤ ∧
    Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)) ∧
    Nonempty (↥V ≃* alternatingGroup (Fin 5))

@[expose] def IsLThreeEpsAt (X : Type) [Group X] (p f : ℕ) [Fact p.Prime] : Prop :=
  Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) ∨
    (2 < p ^ f ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f))

@[expose] def IsZ3PGLThreeAt (X : Type) [Group X] (p f : ℕ) : Prop :=
  ∃ (π : Bool) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧ Sec4.ModThree π (p ^ f) ∧
    Nonempty (X ≃* Multiplicative (ZMod 3) ×
      CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi π 3 (p ^ f) K))

@[expose] noncomputable def Item148 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A),
    letI := ker148_normal hY.2
    (((deltaZero A LB Y).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal ∧
    (
      deltaZero A LB Y ≤ pPrimeCoreOf 3 Y ∨
      (∃ c : G, Subgroup.zpowers c ∈ omegaA A ∧
        deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
          deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        ∃ L ∈ lA A c,
          Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
          ((Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
                CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
                CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
            Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 7))) ∨
          (∃ (p f e : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e ∧
            Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p (f * e) ∧
            IsLThreeEpsAt ↥(img148 A Y (deltaZero A LB Y)) p f) ∨
          (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
            (Sec4.IsTripleCover ↥(img148 A Y (deltaZero A LB Y)) (alternatingGroup (Fin 6)) ∨
              Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 5))))) ∨
      (∃ (c d : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c ∧
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
        deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
          deltaZero A LB (Y ⊓ Subgroup.centralizer ({d} : Set G)) ∧
        (Sec4.IsTripleCover ↥(img148 A Y (deltaZero A LB Y)) CFSG.Blueprint.NativeSporadic.ON ∨
          IsCentralProductA6Covers ↥(img148 A Y (deltaZero A LB Y)) ∨
          IsA6CoverTimesA5 ↥(img148 A Y (deltaZero A LB Y)) ∨
          Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃*
            alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
          Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))) ∨
      (Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 10)) ∧
        (∃ (c : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c ∧
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) ∧
        (Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
      (∃ (c : G) (hcA : c ∈ A) (L : Subgroup G) (n m : ℕ), Subgroup.zpowers c ∈ omegaA A ∧
        L ∈ lA A c ∧ 1 ≤ n ∧ 1 ≤ m ∧
        Sec4.IsoLThreePi ↥(img148 A Y (deltaZero A LB Y)) 2 (3 * n) ∧
        img148 A Y (deltaZero A LB Y ⊔ A) =
          img148 A Y (deltaZero A LB Y) ⊔ Subgroup.zpowers (alpha148 A Y c hcA) ∧
        alpha148 A Y c hcA ∉ img148 A Y (deltaZero A LB Y) ∧
        KFacts.InducesStdKind (img148 A Y (deltaZero A LB Y)) (alpha148 A Y c hcA) .field ∧
        IsLThreeEpsAt (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 (n * m) ∧
        inSubgroup perfectResidual
            (oPrimeResidualOf 3 (deltaZero A LB Y ⊓ Subgroup.centralizer ({c} : Set G))) =
          deltaZero A LB (inSubgroup perfectResidual
            (oPrimeResidualOf 3 (deltaZero A LB Y ⊓ Subgroup.centralizer ({c} : Set G)))) ∧
        ∃ K : Subgroup G, K ≤ L ⊓ Y ∧ Sec4.IsoLThreePi ↥(img148 A Y K) 2 n ∧
          Group.IsPerfect ↥K ∧ K = deltaZero A LB K) ∨
      (Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃*
          alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) ∧
        (∃ (c : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c ∧
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) ∧
        (omegaA A).ncard = 6) ∨
      (∃ (a₁ a₂ : G) (L₁ L₂ J₁ J₂ : Subgroup G) (p₁ f₁ e₁ p₂ f₂ e₂ : ℕ)
          (_ : Fact p₁.Prime) (_ : Fact p₂.Prime),
        Subgroup.zpowers a₁ ∈ omegaA A ∧ Subgroup.zpowers a₂ ∈ omegaA A ∧
        L₁ ∈ lA A a₁ ∧ L₂ ∈ lA A a₂ ∧ J₁ ≤ L₁ ⊓ Y ∧ J₂ ≤ L₂ ⊓ Y ∧
        img148 A Y J₁ ⊔ img148 A Y J₂ = img148 A Y (deltaZero A LB Y) ∧
        img148 A Y J₁ ⊓ img148 A Y J₂ = ⊥ ∧ ⁅img148 A Y J₁, img148 A Y J₂⁆ = ⊥ ∧
        1 ≤ f₁ ∧ 1 ≤ e₁ ∧ 1 ≤ f₂ ∧ 1 ≤ e₂ ∧
        IsZ3PGLThreeAt ↥(img148 A Y (J₁ ⊔ A)) p₁ f₁ ∧
        IsZ3PGLThreeAt ↥(img148 A Y (J₂ ⊔ A)) p₂ f₂ ∧
        Sec4.IsoLThreePi (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁) p₁ (f₁ * e₁) ∧
        Sec4.IsoLThreePi (↥L₂ ⧸ aschbacherSolvableCore 3 ↥L₂) p₂ (f₂ * e₂)))

end CFSG.RankThree.PartTwo.Sec14
