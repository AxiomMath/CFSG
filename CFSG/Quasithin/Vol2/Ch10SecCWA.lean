module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

namespace CW

theorem nonempty_mulEquiv_zmod_prod_aux {p : ℕ} [hp : Fact p.Prime] {X : Type*}
    [CommGroup X] [Finite X] [Module (ZMod p) (Additive X)] (hcard : Nat.card X = p ^ 2) :
    Nonempty (X ≃* Multiplicative (ZMod p × ZMod p)) := by
  have : Module.Finite (ZMod p) (Additive X) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) (Additive X) =
      Module.finrank (ZMod p) (ZMod p × ZMod p) := by
    have h1 := FiniteField.pow_finrank_eq_natCard p (Additive X)
    have h2 : Module.finrank (ZMod p) (ZMod p × ZMod p) = 2 := by simp
    rw [h2]
    have h3 : Nat.card (Additive X) = p ^ 2 := hcard
    rw [h3] at h1
    exact Nat.pow_right_injective hp.out.two_le h1
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod p) hfin
  exact ⟨MulEquiv.toAdditiveLeft.symm e.toAddEquiv⟩

theorem nonempty_mulEquiv_zmod_prod {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (hcard : Nat.card X = p ^ 2) (hexp : ∀ x : X, x ^ p = 1) :
    Nonempty (X ≃* Multiplicative (ZMod p × ZMod p)) := by
  let _ : CommGroup X := IsPGroup.commGroupOfCardEqPrimeSq hcard
  have hA : ∀ a : Additive X, p • a = 0 := fun a => by
    change Additive.ofMul ((Additive.toMul a) ^ p) = Additive.ofMul 1
    rw [hexp]
  exact @nonempty_mulEquiv_zmod_prod_aux p hp X (IsPGroup.commGroupOfCardEqPrimeSq hcard) _
    (AddCommGroup.zmodModule hA) hcard

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuV_le_of {Vp : Subgroup G}
    (hV : Sub326iii T L I ∧ Vp = fsuVM T L I ∨ ¬ Sub326iii T L I ∧ Vp = fsuV T I) :
    fsuV T I ≤ Vp := by
  rcases hV with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact le_conjClosure _ _
  · exact le_rfl

end CW

theorem tmpL6_3_2_10_eight_of
    (h : ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
      thompsonJ T ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) →
      ∀ S : Subgroup G, IsPGroup 2 ↥S → thompsonJ T ≤ S →
        thompsonJ T = thompsonJ S ∧
          Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G)) :
    TmpL6_3_2_10_eight :=
  fun G _ _ T L I _ hfsu hV hJ S hS hJS =>
    h G T L I hfsu (hJ.trans (Subgroup.centralizer_le (CW.fsuV_le_of hV))) S hS hJS

end CFSG.Quasithin.Vol2.Ch10
