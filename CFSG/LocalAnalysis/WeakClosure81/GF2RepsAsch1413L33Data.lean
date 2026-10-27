module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Core
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Theta
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Abs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.GH74.KGroups.L3Eps

theorem asch1413_l33_data {Q : Type} [Group Q] [Finite Q] {L A : Subgroup Q}
    (hF : genFittingFStar Q = L) (hmodel : LieModel ↥L .PSL 3 3 1)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) :
    ∃ (z i : Q) (X : Subgroup Q), z ∈ A ∧ i * i = z ∧
      i ∈ (⨆ c ∈ centralizer ({z} : Set Q), A.map (MulAut.conj c).toMonoidHom) ∧
      Nat.card X = 9 ∧ (∀ x ∈ X, z * x * z⁻¹ = x⁻¹) ∧ (∀ x ∈ X, i * x * i⁻¹ ∈ X) := by
  obtain ⟨θ₀, hθ₀, hL₀, hr₀⟩ := l33_theta0 hF hmodel
  obtain ⟨z, hzA, hz1, hzL⟩ := l33_exists_inner θ₀ hθ₀ hL₀ hA hAe
  have hz2 : z * z = 1 := by
    have h := hAe.2 z hzA
    simpa [pow_two] using h
  obtain ⟨θ, hθ, hθz, hL, hr⟩ := l33_theta_norm θ₀ hθ₀ hL₀ hr₀ hzL hz2 hz1
  let A' : Subgroup (MulAut L33P) := A.map θ
  have hA' : Nat.card A' = 4 := by
    change Nat.card (A.map θ) = 4
    rw [Subgroup.card_map_of_injective hθ, hA]
  have hAe' : IsElemAbelian 2 A' := by
    haveI : IsMulCommutative ↥A := hAe.1
    refine ⟨Subgroup.map_isMulCommutative (H := A) θ, ?_⟩
    intro x hx
    obtain ⟨x0, hx0, hx0eq⟩ := Subgroup.mem_map.mp hx
    rw [← hx0eq, ← map_pow, hAe.2 x0 hx0, map_one]
  have hzA' : (MulAut.conj (tInv : L33P)) ∈ A' :=
    Subgroup.mem_map.mpr ⟨z, hzA, hθz⟩
  obtain ⟨i', hi'2, hi'mem, hi'norm⟩ := l33_core A' hA' hAe' hzA'
  have hSle : (⨆ c ∈ (inner L33P ⊓
        centralizer ({MulAut.conj (tInv : L33P)} : Set (MulAut L33P))),
        A'.map (MulAut.conj c).toMonoidHom) ≤
      ((⨆ c ∈ centralizer ({z} : Set Q), A.map (MulAut.conj c).toMonoidHom)).map θ := by
    refine iSup₂_le fun c hc => ?_
    obtain ⟨q, hqθ⟩ := MonoidHom.mem_range.mp (hr hc.1)
    have hqcent : q ∈ centralizer ({z} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hθ
      rw [map_mul, map_mul, hqθ, hθz]
      exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hA'map : A'.map (MulAut.conj c).toMonoidHom =
        (A.map (MulAut.conj q).toMonoidHom).map θ := by
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨a', ha', ha'x⟩
        obtain ⟨a, ha, haa'⟩ := Subgroup.mem_map.mp ha'
        have hconj : (MulEquiv.toMonoidHom (MulAut.conj c)) (θ a) =
            θ (MulAut.conj q a) := by
          change c * θ a * c⁻¹ = θ (q * a * q⁻¹)
          rw [map_mul, map_mul, map_inv, hqθ]
        refine ⟨MulAut.conj q a, ⟨a, ha, rfl⟩, ?_⟩
        rw [← ha'x, ← haa']
        exact hconj.symm
      · rintro ⟨b, hb, hbx⟩
        obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hb
        have hconj : (MulEquiv.toMonoidHom (MulAut.conj c)) (θ a) =
            θ (MulAut.conj q a) := by
          change c * θ a * c⁻¹ = θ (q * a * q⁻¹)
          rw [map_mul, map_mul, map_inv, hqθ]
        refine ⟨θ a, ⟨a, ha, rfl⟩, ?_⟩
        rw [← hbx, ← hab]
        exact hconj
    rw [hA'map]
    exact Subgroup.map_mono (le_iSup₂ (f := fun c (_ : c ∈ centralizer ({z} : Set Q)) =>
      A.map (MulAut.conj c).toMonoidHom) q hqcent)
  have hi'S : i' ∈ ((⨆ c ∈ centralizer ({z} : Set Q),
      A.map (MulAut.conj c).toMonoidHom)).map θ := hSle hi'mem
  obtain ⟨i, hi, hθi⟩ := Subgroup.mem_map.mp hi'S
  have hii : i * i = z := by
    apply hθ
    rw [map_mul, hθi, hi'2, hθz]
  let X : Subgroup Q := l33X.comap θ
  have hXcard : Nat.card X = 9 := by
    change Nat.card (l33X.comap θ) = 9
    have h1 : Nat.card ((l33X.comap θ).map θ) = Nat.card (l33X.comap θ) :=
      Subgroup.card_map_of_injective hθ
    rw [Subgroup.map_comap_eq_self (l33X_le_inner.trans hr), l33X_card] at h1
    exact h1.symm
  have hXz : ∀ x ∈ X, z * x * z⁻¹ = x⁻¹ := by
    intro x hx
    change θ x ∈ l33X at hx
    apply hθ
    have h := l33X_inverted (θ x) hx
    simpa only [map_mul, map_inv, hθz] using h
  have hXi : ∀ x ∈ X, i * x * i⁻¹ ∈ X := by
    intro x hx
    change θ x ∈ l33X at hx
    have h := hi'norm (θ x) hx
    show θ (i * x * i⁻¹) ∈ l33X
    simpa only [map_mul, map_inv, hθi] using h
  exact ⟨z, i, X, hzA, hii, hi, hXcard, hXz, hXi⟩

theorem asch1413_L33_of_model {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hF : genFittingFStar Q = L) (hmodel : LieModel ↥L .PSL 3 3 1)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A) : False := by
  obtain ⟨z, i, X, hzA, hii, hi, hX, hXz, hXi⟩ := asch1413_l33_data hF hmodel hA hAe
  exact asch1413_L33_false hV hρ hq hzA hii hi hX hXz hXi

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
