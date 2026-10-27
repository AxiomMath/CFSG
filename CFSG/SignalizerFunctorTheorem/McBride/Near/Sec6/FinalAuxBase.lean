module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {G : Type u} [Group G]

theorem perfRes_le (X : Subgroup G) : perfRes X ≤ X :=
  Subgroup.map_subtype_le _

theorem isPerfect_perfRes [Finite G] (X : Subgroup G) : Group.IsPerfect ↥(perfRes X) :=
  Nonsolvable.isPerfect_perfectResidual_map X

theorem le_perfRes_of_isPerfect {P X : Subgroup G} (hP : Group.IsPerfect ↥P) (h : P ≤ X) :
    P ≤ perfRes X :=
  Nonsolvable.le_perfectResidual_map_of_isPerfect hP h

theorem perfRes_mono [Finite G] {X Y : Subgroup G} (h : X ≤ Y) : perfRes X ≤ perfRes Y :=
  le_perfRes_of_isPerfect (isPerfect_perfRes X) ((perfRes_le X).trans h)

theorem admits_perfRes {Q X : Subgroup G} (h : Admits Q X) : Admits Q (perfRes X) :=
  le_trans h (Nonsolvable.normalizer_le_normalizer_perfectResidual_map X)

theorem perfRes_eq_bot_iff [Finite G] (X : Subgroup G) :
    perfRes X = ⊥ ↔ Group.IsSolvable ↥X := by
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable]
  unfold perfRes
  constructor
  · intro hbot
    exact Subgroup.map_injective X.subtype_injective (hbot.trans (Subgroup.map_bot _).symm)
  · intro hbot
    rw [show CFSG.perfectResidual ↥X = ⊥ from hbot, Subgroup.map_bot]

theorem admits_sectionCentralizer {Q X Y : Subgroup G} (hX : Admits Q X) (hY : Admits Q Y) :
    Admits Q (sectionCentralizer X Y) := by
  have key : ∀ q ∈ Q, ∀ g ∈ sectionCentralizer X Y, q * g * q⁻¹ ∈ sectionCentralizer X Y := by
    intro q hq g hg
    obtain ⟨hgX, hgY, hgc⟩ := mem_sectionCentralizer_iff.mp hg
    refine mem_sectionCentralizer_iff.mpr ⟨mul_mem (mul_mem (hX hq) hgX) (inv_mem (hX hq)),
      mul_mem (mul_mem (hY hq) hgY) (inv_mem (hY hq)), fun y hy => ?_⟩
    have hy' : q⁻¹ * y * q ∈ Y := (Subgroup.mem_normalizer_iff''.mp (hY hq) y).mp hy
    have h1 := hgc _ hy'
    have h2 : q * ⁅g, q⁻¹ * y * q⁆ * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hX hq) _).mp h1
    have e : ⁅q * g * q⁻¹, y⁆ = q * ⁅g, q⁻¹ * y * q⁆ * q⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h2
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key q hq z hz, fun hz => ?_⟩
  simpa [mul_assoc] using key q⁻¹ (inv_mem hq) _ hz

variable {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem admits_thetaN (X : Subgroup G) : Admits A (thetaN p A θ X) := by
  unfold thetaN
  exact Admits.iSup fun Y => Admits.iSup fun hY => hY.1.1

theorem dZero_le_dsub : dZero p A θ ≤ dsub A θ :=
  iSup₂_le fun _ _ => inf_le_left

theorem admits_of_le_dsub (hθ : NearFunctor p A θ) {X : Subgroup G} (h : X ≤ dsub A θ) :
    Admits A X :=
  (Subgroup.le_centralizer_iff.mpr (h.trans (dsub_le_centralizer hθ))).trans
    (Subgroup.centralizer_le_normalizer _)

theorem admits_centralizer {Q X : Subgroup G} (hX : Admits Q X) :
    Admits Q (Subgroup.centralizer (X : Set G)) := by
  have key : ∀ q ∈ Q, ∀ c ∈ Subgroup.centralizer (X : Set G),
      q * c * q⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro q hq c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : q⁻¹ * x * q ∈ X := (Subgroup.mem_normalizer_iff''.mp (hX hq) x).mp hx
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (q * c * q⁻¹) = q * ((q⁻¹ * x * q) * c) * q⁻¹ := by group
      _ = q * (c * (q⁻¹ * x * q)) * q⁻¹ := by rw [h1]
      _ = (q * c * q⁻¹) * x := by group
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key q hq z hz, fun hz => ?_⟩
  simpa [mul_assoc] using key q⁻¹ (inv_mem hq) _ hz

theorem admits_dOne (hθ : NearFunctor p A θ) : Admits A (dOne p A θ) :=
  admits_of_le_dsub hθ ((Subgroup.map_subtype_le _).trans dZero_le_dsub)

theorem admits_dTwo (hθ : NearFunctor p A θ) : Admits A (dTwo p A θ) :=
  admits_of_le_dsub hθ (inf_le_left.trans dZero_le_dsub)

theorem admits_sOne (hθ : NearFunctor p A θ) : Admits A (sOne p A θ) :=
  (admits_thetaN _).inf (admits_centralizer (admits_dOne hθ))

theorem admits_sTwo (hθ : NearFunctor p A θ) : Admits A (sTwo p A θ) :=
  (admits_thetaN _).inf (admits_sectionCentralizer (admits_sOne hθ)
    ((admits_dTwo hθ).sup (admits_sOne hθ)))

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
