module

public import CFSG.RankThree.GF2n.Parrott.SpinForms
public import CFSG.RankThree.GF2n.Parrott.Section4FixDimBridge
public import CFSG.RankThree.GF2n.Parrott.OrthogonalV
public import CFSG.RankThree.GF2n.Parrott.CommutatorDetermined
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

noncomputable def vecToV (h : Tim79a.ParrottHyp z) (P : GL8) (w : V) :
    QuotientV.V z :=
  (mulEquivV h).symm (Multiplicative.ofAdd (((P : Matrix (Fin 8) (Fin 8) (ZMod 2))) *ᵥ w))

theorem toAdd_mulEquivV_vecToV (h : Tim79a.ParrottHyp z) (P : GL8) (w : V) :
    Multiplicative.toAdd (mulEquivV h (vecToV h P w)) =
      ((P : Matrix (Fin 8) (Fin 8) (ZMod 2))) *ᵥ w := by
  simp [vecToV]

theorem vecToV_add (h : Tim79a.ParrottHyp z) (P : GL8) (u w : V) :
    vecToV h P (u + w) = vecToV h P u * vecToV h P w := by
  apply (mulEquivV h).injective
  rw [map_mul]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_mulEquivV_vecToV, toAdd_mulEquivV_vecToV, toAdd_mulEquivV_vecToV,
    Matrix.mulVec_add]

theorem vecToV_injective (h : Tim79a.ParrottHyp z) (P : GL8) :
    Function.Injective (vecToV h P) := by
  intro w w' hww
  have h1 := congrArg (fun v => Multiplicative.toAdd (mulEquivV h v)) hww
  simp only [toAdd_mulEquivV_vecToV] at h1
  have h2 := congrArg (fun u => ((P⁻¹ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h2
  exact h2

theorem vecToV_surjective (h : Tim79a.ParrottHyp z) (P : GL8) :
    Function.Surjective (vecToV h P) := by
  intro v
  refine ⟨((P⁻¹ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
    Multiplicative.toAdd (mulEquivV h v), ?_⟩
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_mulEquivV_vecToV, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem conjV_vecToV (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (y : ↥(H z)) (w : V) :
    conjV h y (vecToV h P w) =
      vecToV h P (((rhoA (qH D y) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) := by
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [← mulVec_mulAutVEquivGL h (conjV h y) (vecToV h P w), toAdd_mulEquivV_vecToV,
    ← actionQA45_qH D h y, hP, toAdd_mulEquivV_vecToV]
  have key : (P * rhoA (qH D y) * P⁻¹ * P : GL8) = P * rhoA (qH D y) := by group
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, key, Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem qVZMod_seven (h : Tim79a.ParrottHyp z) (a b c : QuotientV.V z) :
    qVZMod h (a * b * c) + qVZMod h (a * b) + qVZMod h (a * c) + qVZMod h (b * c) +
      qVZMod h a + qVZMod h b + qVZMod h c = 0 := by
  rw [qVZMod_mul_add h (a * b) c, polarVZMod_add h a b c, qVZMod_mul_add h a c,
    qVZMod_mul_add h b c]
  have key : ∀ x1 x2 x3 x4 x5 x6 : ZMod 2,
      (x1 + x2 + (x3 + x4)) + x1 + (x5 + x2 + x3) + (x6 + x2 + x4) + x5 + x6 + x2 = 0 := by
    decide
  exact key _ _ _ _ _ _

theorem qVZMod_vecToV_eq_q (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (w : V) :
    qVZMod h (vecToV h P w) = q w := by
  have hQ : (fun w : V => qVZMod h (vecToV h P w)) = 0 ∨
      (fun w : V => qVZMod h (vecToV h P w)) = q := by
    refine spinInvariantQuadratic_unique _ ?_ ?_
    · intro u u' w
      have h1 := qVZMod_seven h (vecToV h P u) (vecToV h P u') (vecToV h P w)
      rwa [← vecToV_add, ← vecToV_add, ← vecToV_add, ← vecToV_add] at h1
    · intro a w
      obtain ⟨y, rfl⟩ := qH_surjective D a
      show qVZMod h (vecToV h P _) = qVZMod h (vecToV h P w)
      rw [← conjV_vecToV D h P hP y w, qVZMod_conj]
  rcases hQ with h0 | hq
  · exfalso
    have hall : ∀ v : QuotientV.V z, qVZMod h v = 0 := by
      intro v
      obtain ⟨w', rfl⟩ := vecToV_surjective h P v
      exact congrFun h0 w'
    have hone : ∀ v : QuotientV.V z, v = 1 := by
      intro v
      refine polarVZMod_nondegenerate h v (fun w' => ?_)
      have h1 := qVZMod_mul_add h v w'
      rw [hall, hall, hall] at h1
      simpa using h1.symm
    have hcard := QuotientV.card_V h
    have hsub : Subsingleton (QuotientV.V z) := ⟨fun a b => (hone a).trans (hone b).symm⟩
    have h1 : Nat.card (QuotientV.V z) = 1 := Nat.card_unique
    rw [hcard] at h1
    norm_num at h1
  · exact congrFun hq w

theorem fixed_space_faithful_of_spin (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (hM : ∀ a b : A45, IsConj a (uA * vA) → a * b = b * a →
      (∀ w : V, ((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w → q w = 0 →
        ((rhoA b : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) → b = 1 ∨ b = a) :
    ∀ y y' : ↥(H z), IsConj (qH D y) (uA * vA) → qH D y * qH D y' = qH D y' * qH D y →
      (∀ v : QuotientV.V z, conjV h y v = v → qVZMod h v = 0 → conjV h y' v = v) →
        qH D y' = 1 ∨ qH D y' = qH D y := by
  intro y y' hc hcomm hfix
  refine hM (qH D y) (qH D y') hc hcomm ?_
  intro w hw hqw
  have h1 : conjV h y (vecToV h P w) = vecToV h P w := by
    rw [conjV_vecToV D h P hP y w, hw]
  have h2 : qVZMod h (vecToV h P w) = 0 := by
    rw [qVZMod_vecToV_eq_q D h P hP w]
    exact hqw
  have h3 := hfix _ h1 h2
  rw [conjV_vecToV D h P hP y' w] at h3
  exact vecToV_injective h P h3

theorem exists_conj_of_qVZMod_eq_zero (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {v w : QuotientV.V z}
    (hv : v ≠ 1) (hw : w ≠ 1) (hqv : qVZMod h v = 0) (hqw : qVZMod h w = 0) :
    ∃ g : ↥(H z), conjV h g v = w := by
  obtain ⟨a, rfl⟩ := vecToV_surjective h P v
  obtain ⟨b, rfl⟩ := vecToV_surjective h P w
  have hzero : vecToV h P 0 = 1 := by
    apply (mulEquivV h).injective
    apply Multiplicative.toAdd.injective
    simp [toAdd_mulEquivV_vecToV]
  have ha0 : a ≠ 0 := fun h0 => hv (h0 ▸ hzero)
  have hb0 : b ≠ 0 := fun h0 => hw (h0 ▸ hzero)
  rw [qVZMod_vecToV_eq_q D h P hP] at hqv hqw
  obtain ⟨c, hc⟩ := spinSingular_transitive a b ha0 hb0 hqv hqw
  obtain ⟨g, rfl⟩ := qH_surjective D c
  exact ⟨g, by rw [conjV_vecToV D h P hP g a, hc]⟩

end CFSG.RankThree.GF2n.Parrott
