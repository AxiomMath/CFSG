module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Basic
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem map_conj_eq_self {Q : Subgroup G} (hQ : Q.Normal) (g : G) :
    Q.map (MulAut.conj g).toMonoidHom = Q := by
  apply le_antisymm
  · rintro x ⟨q, hq, rfl⟩
    simpa using hQ.conj_mem q hq g
  · intro x hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simpa using hQ.conj_mem x hx g⁻¹
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem commutator_zpowers_le_of_normal {Q : Subgroup G} (hQ : Q.Normal) (u : G) :
    ⁅Q, Subgroup.zpowers u⁆ ≤ Q :=
  (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers u) (K := Q)).1
    (by rw [Subgroup.normalizer_eq_top (h := hQ)]; exact le_top)

theorem commutator_zpowers_conj {Q : Subgroup G} (hQ : Q.Normal) (u g : G) :
    ⁅Q, Subgroup.zpowers (g * u * g⁻¹)⁆ =
      (⁅Q, Subgroup.zpowers u⁆).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_commutator, map_conj_eq_self hQ, MonoidHom.map_zpowers]
  rfl

theorem card_commutator_zpowers_eq_of_isConj {Q : Subgroup G} (hQ : Q.Normal) {u w : G}
    (h : IsConj u w) :
    Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      Nat.card (⁅Q, Subgroup.zpowers w⁆ : Subgroup G) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  rw [commutator_zpowers_conj hQ]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (by simpa using (MulAut.conj g).injective)).symm

theorem sixFiveGlobal_of_inputs
    {Q : Subgroup G} (hQn : Q.Normal) {u w : G}
    (hZc : (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) ≤ Subgroup.center G)
    (hZtop : Subgroup.center G ≤ (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G))
    (hQF : Q ≤ ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆)
    (hPR : ⁅Q, Subgroup.zpowers u⁆ ≤
      Subgroup.normalizer ((⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G))
    (hcardP : Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard *
        Nat.card (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G))
    (hcardR : Nat.card (⁅Q, Subgroup.zpowers w⁆ : Subgroup G) =
      Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G)) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ ∧
      Subgroup.center G = ⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ ∧
      Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
        Nat.card (Subgroup.center G) := by
  classical
  set P : Subgroup G := ⁅Q, Subgroup.zpowers u⁆ with hP
  set R : Subgroup G := ⁅Q, Subgroup.zpowers w⁆ with hR
  set Z : Subgroup G := P ⊓ R with hZ
  have hPle : P ≤ Q := commutator_zpowers_le_of_normal hQn u
  have hRle : R ≤ Q := commutator_zpowers_le_of_normal hQn w
  have hFle : P ⊔ R ≤ Q := sup_le hPle hRle
  have hQeq : Q = P ⊔ R := le_antisymm hQF hFle
  have hcenter : Subgroup.center G = Z := le_antisymm (by simpa [hZ] using hZtop)
    (by simpa [hZ] using hZc)
  have hprod : Nat.card Q * Nat.card Z = Nat.card P * Nat.card R := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := P) (K := R) hPR
    simpa only [hQeq, hZ] using h
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hcardZ : Nat.card Z = Nat.card (Subgroup.center G) := by rw [hcenter]
  refine ⟨hQeq, hcenter, ?_⟩
  have hsq : Nat.card Q * Nat.card Z =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard * Nat.card Z *
        ((D ∩ Subgroup.centralizer ({u} : Set G)).ncard * Nat.card Z) := by
    rw [hprod, hcardR, hcardP]
  have hmain : Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
      Nat.card Z := by
    have h1 : Nat.card Q * Nat.card Z =
        ((D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 * Nat.card Z) * Nat.card Z := by
      rw [hsq]; ring
    exact Nat.eq_of_mul_eq_mul_right hZpos h1
  rw [hmain, hcardZ]

theorem sixFiveGlobal 
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hodd : IsOddTransp D)
    (hgen : Subgroup.closure D = ⊤) {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G)
    {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hQF : Q ≤ ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆)
    (hPR : ⁅Q, Subgroup.zpowers u⁆ ≤
      Subgroup.normalizer ((⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G))
    (hZc : (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) ≤ Subgroup.center G)
    (hZtop : Subgroup.center G ≤
      (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G))
    (hcardP : Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard *
        Nat.card (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G)) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ ∧
      Subgroup.center G = ⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ ∧
      Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
        Nat.card (Subgroup.center G) := by
  have hQn : Q.Normal := by rw [hQ]; exact CFSG.pCore_normal
  have hcardR : Nat.card (⁅Q, Subgroup.zpowers w⁆ : Subgroup G) =
      Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) :=
    (card_commutator_zpowers_eq_of_isConj hQn (isConj_of_isClass hcls hu hw)).symm
  exact sixFiveGlobal_of_inputs hQn hZc hZtop hQF hPR hcardP hcardR

end CFSG.OddTranspositions
