module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def GGNbrLSideDichElt (lab : LargeEvenLabel) (R : Type) [Group R] : Prop :=
  ∀ a b : R, a ≠ 1 → a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a →
    ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set R)) →
      ∀ Q : ℕ, 4 ≤ Q → 3 ∣ Q - 1 →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Q ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃* projectiveSL 3 F)) →
        ∀ α : MulAut (↥J ⧸ Subgroup.center ↥J), GGNbrLSideInduces (MulAut.conj b) J α →
          GGInnDiagPSL3 Q (↥J ⧸ Subgroup.center ↥J) α ∨ GGNbrLSideLargeRank lab

private theorem conj_eq_one_iff {R : Type} [Group R] (hZ : Subgroup.center R = ⊥) (x : R) :
    MulAut.conj x = 1 ↔ x = 1 := by
  refine ⟨fun hx => ?_, fun hx => by rw [hx, map_one]⟩
  have hmem : x ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : x * g * x⁻¹ = g := by
      simpa [MulAut.conj_apply] using congrArg (fun f : MulAut R => f g) hx
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

private theorem fixSubgroup_conj_eq_centralizer {R : Type} [Group R] (x : R) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem ggNbrLSideDich_of_elt {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) (hZ : Subgroup.center R = ⊥) (h : GGNbrLSideDichElt lab R) :
    GGNbrLSideDich lab I := by
  intro φ hφ ψ hψ hφne hφ3 hψ3 hcomm J hJ Q hQ4 hQ3 hPSL α hα
  obtain ⟨a, rfl⟩ := hI hφ
  obtain ⟨b, rfl⟩ := hI hψ
  have ha1 : a ≠ 1 := fun ha => hφne ((conj_eq_one_iff hZ a).mpr ha)
  have ha3 : a ^ 3 = 1 := (conj_eq_one_iff hZ (a ^ 3)).mp (by rw [map_pow]; exact hφ3)
  have hb3 : b ^ 3 = 1 := (conj_eq_one_iff hZ (b ^ 3)).mp (by rw [map_pow]; exact hψ3)
  have hab : a * b = b * a := by
    have hcab : MulAut.conj (a * b) = MulAut.conj (b * a) := by
      rw [map_mul, map_mul, hcomm]
    have hc : (a * b) * (b * a)⁻¹ = 1 :=
      (conj_eq_one_iff hZ _).mp (by rw [map_mul, map_inv, hcab, mul_inv_cancel])
    exact mul_inv_eq_one.mp hc
  have hJ' : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set R)) := by
    rwa [← fixSubgroup_conj_eq_centralizer a]
  exact h a b ha1 ha3 hb3 hab J hJ' Q hQ4 hQ3 hPSL α hα

end CFSG.StandardType
