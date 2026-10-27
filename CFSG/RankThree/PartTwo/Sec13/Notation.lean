module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem autThetaQuot_mono {G : Type*} [Group G] [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y)
    (L : Subgroup G) : Sec4.autThetaQuot X L ≤ Sec4.autThetaQuot Y L := by
  intro τ hτ
  obtain ⟨h, hN, hX, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  exact Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, hXY hX, rfl⟩

section Star

variable {G : Type*} [Group G]

theorem centralizer_singleton_eq_of_zpowers_eq {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have key : ∀ {x y : G}, x ∈ Subgroup.zpowers y → ∀ g : G,
      g ∈ Subgroup.centralizer ({y} : Set G) → g ∈ Subgroup.centralizer ({x} : Set G) := by
    intro x y hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact Commute.zpow_right hg k
  ext g
  constructor
  · exact key (h ▸ Subgroup.mem_zpowers b) g
  · exact key (h.symm ▸ Subgroup.mem_zpowers a) g

theorem starCondition_congr_aux {A K₁ K₂ : Subgroup G} (hK : K₁ = K₂) {N₁ : Subgroup K₁}
    {N₂ : Subgroup K₂} [N₁.Normal] [N₂.Normal] (hN : N₁.map K₁.subtype = N₂.map K₂.subtype) :
    (thetaAlpha 3 ((A.subgroupOf K₁).map (QuotientGroup.mk' N₁)) ≤
        aschbacherSolvableCore 3 (K₁ ⧸ N₁)) ↔
      (thetaAlpha 3 ((A.subgroupOf K₂).map (QuotientGroup.mk' N₂)) ≤
        aschbacherSolvableCore 3 (K₂ ⧸ N₂)) := by
  subst hK
  obtain rfl : N₁ = N₂ := Subgroup.map_injective K₁.subtype_injective hN
  rfl

theorem starConditionAt_congr {A : Subgroup G} {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    StarConditionAt A a ↔ StarConditionAt A b := by
  unfold StarConditionAt
  refine starCondition_congr_aux (centralizer_singleton_eq_of_zpowers_eq h) ?_
  simp only [centralLine, MonoidHom.map_zpowers, Subgroup.coe_subtype]
  exact h

end Star

section Omega

variable {G : Type*} [Group G]

@[expose] def omegaA (A : Subgroup G) : Set (Subgroup G) :=
  {F | F ≤ A ∧ Nat.card F = 3 ∧ ∃ a : G, F = Subgroup.zpowers a ∧ ¬ StarConditionAt A a}

theorem mem_omegaA_iff {A F : Subgroup G} :
    F ∈ omegaA A ↔
      F ≤ A ∧ Nat.card F = 3 ∧ ∃ a : G, F = Subgroup.zpowers a ∧ ¬ StarConditionAt A a :=
  Iff.rfl

theorem zpowers_mem_omegaA_iff {A : Subgroup G} {a : G} :
    Subgroup.zpowers a ∈ omegaA A ↔
      a ∈ A ∧ Nat.card (Subgroup.zpowers a) = 3 ∧ ¬ StarConditionAt A a := by
  constructor
  · rintro ⟨hle, hcard, b, hb, hstar⟩
    exact ⟨hle (Subgroup.mem_zpowers a), hcard, (starConditionAt_congr hb).not.mpr hstar⟩
  · rintro ⟨ha, hcard, hstar⟩
    exact ⟨Subgroup.zpowers_le.mpr ha, hcard, a, rfl, hstar⟩

@[expose] noncomputable def lA [Finite G] (A : Subgroup G) (c : G) : Set (Subgroup G) :=
  {L | L ∈ thetaComponentsAt 3 c ∧ A ≤ Subgroup.normalizer (L : Set G) ∧
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) ∧
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L)) ≠ ⊥}

theorem mem_lA_iff [Finite G] {A L : Subgroup G} {c : G} :
    L ∈ lA A c ↔ L ∈ thetaComponentsAt 3 c ∧ A ≤ Subgroup.normalizer (L : Set G) ∧
      Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
        (Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L)) ≠ ⊥ :=
  Iff.rfl

theorem lA_subset [Finite G] (A : Subgroup G) (c : G) : lA A c ⊆ thetaComponentsAt 3 c :=
  fun _ hL => hL.1

end Omega

section Hyp

variable {G : Type*} [Group G] [Finite G]

@[expose] def HypS (A : Subgroup G) : Prop :=
  A ∈ partTwoE G ∧ A ∉ partTwoT G ∧
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A → ∀ K ∈ lA A a, a ∉ K

@[expose] def HypT (A : Subgroup G) : Prop :=
  A ∈ partTwoE G ∧ A ∉ partTwoT G ∧
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A →
      collectionIn (partTwoT G) (Subgroup.centralizer ({a} : Set G)) = ∅

end Hyp

structure Sec13Data (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends PartTwoStanding G where
  partTwoS_eq : partTwoS G = ∅
  mem_partTwoF : A ∈ partTwoF G
  not_mem_partTwoT : A ∉ partTwoT G
  zpowers_mem_omegaA : Subgroup.zpowers c ∈ omegaA A
  mem_lA : L ∈ lA A c

theorem Sec13Data.mem_partTwoE {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}
    (h : Sec13Data G A c L) : A ∈ partTwoE G :=
  (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ h.mem_partTwoF

@[expose] def IsLThreePi (X : Type) [Group X] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi X p e

@[expose] def Chosen136 {G : Type} [Group G] [Finite G] (A : Subgroup G) : Prop :=
  A ∈ partTwoF G ∧ ∀ c : G, Subgroup.zpowers c ∈ omegaA A → ∀ L ∈ lA A c,
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12)) ∧
    ∀ K ∈ thetaComponentsAt 3 c, 3 ∣ Nat.card K → K = L

end CFSG.RankThree.PartTwo.Sec13
