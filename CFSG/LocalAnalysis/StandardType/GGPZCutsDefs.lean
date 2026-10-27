module

public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZPrem {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel) (X : Subgroup G)
    (m : ℕ) (z : ↥Bs) : Prop :=
  GGResHyp p B Bs x L D J y K ∧ (X = L ∨ X = K) ∧ LargeEvenInLambda2 labJ ∧
    LargeEvenInLambda2 labX ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
    GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) ∧ ggRowTwoNodeSmall p labJ labX ∧
    (((labX.tag = .A ∨ labX.tag = .twA) ∧ m = labX.rank) ∨
      ((labX.tag = .E6 ∨ labX.tag = .twE6) ∧ m = 6)) ∧ Nat.card ↥Bs = p ^ m ∧
    Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank ∧ GGReflGenerated p (ggAutomizer J Bs) ∧
    (z : G) ∈ D ∧ (z : G) ∉ Subgroup.zpowers x ∧ (z : G) ∉ Subgroup.zpowers y

@[expose] def GGPZVertInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∃ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y ∧
      J ≤ Y ∧ Bs ≤ Subgroup.normalizer (Y : Set G)

@[expose] def GGPZMultInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)

@[expose] def GGPZEndpointInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) →
      ∃ (r n c : ℕ) (W : Type) (_ : Group W) (_ : Finite W) (f : W →* MulAut ↥Bs),
        GGWeylTypeData r n c ∧ labJ.rank ≤ r ∧ r ≤ m ∧ Nat.card W = n ∧
          Nat.card ↥(Subgroup.center W) = c ∧ ggAutomizer Y Bs ≤ f.range

theorem ggPZ_closure_orbit_le {G : Type} [Group G] {Bs : Subgroup G}
    (p : ℕ) (AJ A Q : Subgroup (MulAut ↥Bs)) (z : ↥Bs)
    (hAJ : AJ ≤ Q)
    (hfix : ∀ t, t ∈ ggPZFixRefl p A z → t ∈ Subgroup.normalizer Q) :
    Subgroup.closure (ggPZOrbit p AJ A z) ≤ Q := by
  have hN : Subgroup.closure (ggPZFixRefl p A z) ≤ Subgroup.normalizer Q :=
    (Subgroup.closure_le (K := (Subgroup.normalizer Q : Subgroup (MulAut ↥Bs)))
      (k := ggPZFixRefl p A z)).mpr hfix
  refine (Subgroup.closure_le (K := Q) (k := ggPZOrbit p AJ A z)).mpr ?_
  rintro t ⟨r, hrAJ, _hrrefl, g, hg, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hN hg) r).mp (hAJ hrAJ)

section Numerical

variable {W T : Type*} [Group W] [Group T] [Finite W] [Finite T]

private theorem ggPZ_eq_range_of_card_eq (f : W →* T) {O : Subgroup T} (hO : O ≤ f.range)
    (hcard : Nat.card O = Nat.card W) : O = f.range := by
  have hdvd1 : Nat.card O ∣ Nat.card f.range := Subgroup.card_dvd_of_le hO
  have hdvd2 : Nat.card f.range ∣ Nat.card O := by
    rw [hcard]
    exact Subgroup.card_range_dvd f
  have hrangeO : Nat.card f.range = Nat.card O := Nat.dvd_antisymm hdvd2 hdvd1
  exact Subgroup.eq_of_le_of_card_ge hO (le_of_eq hrangeO)

private theorem ggPZ_ker_eq_bot_of_card_eq (f : W →* T) {O : Subgroup T} (hO : O ≤ f.range)
    (hcard : Nat.card O = Nat.card W) : f.ker = ⊥ := by
  have hdvd1 : Nat.card O ∣ Nat.card f.range := Subgroup.card_dvd_of_le hO
  have hdvd2 : Nat.card f.range ∣ Nat.card O := by
    rw [hcard]
    exact Subgroup.card_range_dvd f
  have hrangeO : Nat.card f.range = Nat.card O := Nat.dvd_antisymm hdvd2 hdvd1
  have hrange : Nat.card f.range = Nat.card W := hrangeO.trans hcard
  have hker_mul : Nat.card f.ker * Nat.card f.range = Nat.card W :=
    Subgroup.card_ker_mul_card_range f
  rw [hrange] at hker_mul
  exact Subgroup.eq_bot_of_card_eq f.ker
    ((Nat.mul_eq_right (Nat.card_pos (α := W)).ne').mp hker_mul)

private theorem ggPZ_card_center_eq_of_card_eq (f : W →* T) {O : Subgroup T} (hO : O ≤ f.range)
    (hcard : Nat.card O = Nat.card W) :
    Nat.card (Subgroup.center ↥O) = Nat.card (Subgroup.center W) := by
  have hOeq : O = f.range := ggPZ_eq_range_of_card_eq f hO hcard
  have hker : f.ker = ⊥ := ggPZ_ker_eq_bot_of_card_eq f hO hcard
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  rw [hOeq]
  exact (Nat.card_congr (Subgroup.centerCongr (MonoidHom.ofInjective hf)).toEquiv).symm

theorem ggPZ_card_dvd_and_center_card_eq (f : W →* T) {O : Subgroup T} (hO : O ≤ f.range) :
    Nat.card O ∣ Nat.card W ∧
      (Nat.card O = Nat.card W →
        Nat.card (Subgroup.center ↥O) = Nat.card (Subgroup.center W)) :=
  ⟨(Subgroup.card_dvd_of_le hO).trans (Subgroup.card_range_dvd f),
    fun h => ggPZ_card_center_eq_of_card_eq f hO h⟩

end Numerical

end CFSG.StandardType

end
