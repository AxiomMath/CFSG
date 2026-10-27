module

public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift
public import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TotallySplit

public section

open Module
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem pow_le_card_of_abelian_subgroup {X Γ : Type*} [Group X] [Group Γ] (φ : Γ →* X)
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hexp : ∀ v ∈ V, v ^ s = 1)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V)
    (E : Subgroup Γ) [Finite E] (hE : IsMulCommutative E) (hEexp : ∀ g ∈ E, g ^ r = 1)
    (hfaith : ∀ g ∈ E, (∀ v ∈ V, φ g * v * (φ g)⁻¹ = v) → g = 1) {a : ℕ}
    (hEa : Nat.card E = r ^ a) (hV : V ≠ ⊥) : s ^ a ≤ Nat.card V := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  have : Fact r.Prime := ⟨hr⟩
  let F := AlgebraicClosure (ZMod s)
  obtain ⟨m, ρ, hcard, hρ1⟩ := exists_rep_of_elementary_abelian φ V hs hexp hnorm F
  let ρE : E →* Module.End F (Fin m → F) := ρ.comp E.subtype
  have hρE : Function.Injective ρE := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hfaith g g.2 (hρ1 g hg))
  have hm : 1 ≤ m := by
    by_contra hcon
    have hm0 : m = 0 := by omega
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have h1 : Nat.card V = 1 := by rw [hcard, hm0, pow_zero]
    have := Nat.card_eq_one_iff_unique.mp h1
    obtain ⟨hu⟩ := this
    have : (⟨v, hv⟩ : V) = 1 := Subsingleton.elim _ _
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hinv : (Nat.card (⊤ : Subgroup E) : F) ≠ 0 := by
    rw [Subgroup.card_top, hEa, Ne, CharP.cast_eq_zero_iff F s]
    intro h
    exact hrs ((Nat.prime_dvd_prime_iff_eq hs hr).mp (hs.dvd_of_dvd_pow h)).symm
  have hcommT : IsMulCommutative (⊤ : Subgroup E) :=
    ⟨⟨fun x y => Subtype.ext (mul_comm' x.1 y.1)⟩⟩
  let Zs : Subgroup E :=
    { carrier := {g | ∃ c : F, ρE g = c • 1}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨c * d, ?_⟩
        rw [map_mul, hc, hd, smul_mul_smul_comm, one_mul]
      one_mem' := ⟨1, by rw [map_one, one_smul]⟩
      inv_mem' := by
        rintro a ⟨c, hc⟩
        have h1 : ρE a * ρE a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [hc, smul_mul_assoc, one_mul] at h1
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at h1
          exact zero_ne_one h1
        refine ⟨c⁻¹, ?_⟩
        have h2 := congrArg (fun T => c⁻¹ • T) h1
        simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h2
        exact h2 }
  have hZs : ∀ g, g ∈ Zs ↔ ∃ c : F, ρE g = c • 1 := fun g => Iff.rfl
  have hexpZ : ∀ g ∈ (⊤ : Subgroup E), g ^ r ∈ Zs := by
    intro g _
    have : g ^ r = 1 := Subtype.ext (hEexp g g.2)
    rw [this]
    exact Zs.one_mem
  have hb := card_le_of_abelian_mod_scalars hr.pos ρE Zs ⊤ hcommT hinv le_top hZs hexpZ
  rw [Subgroup.card_top, hEa, Module.finrank_fin_fun] at hb
  have hZcard : Nat.card Zs ≤ r := by
    choose c hc using fun g : Zs => (hZs g.1).mp g.2
    have hc_inj : Function.Injective c := by
      intro g h hgh
      apply Subtype.ext
      apply hρE
      rw [hc g, hc h, hgh]
    have hc_root : ∀ g : Zs, c g ^ r = 1 := by
      intro g
      have h1 : ρE (g.1 ^ r) = 1 := by
        have : g.1 ^ r = 1 := Subtype.ext (hEexp g.1.1 g.1.2)
        rw [this, map_one]
      rw [map_pow, hc g, smul_pow, one_pow] at h1
      have h2 : c g ^ r • (1 : Module.End F (Fin m → F)) = 1 := h1
      let v : Fin m → F := Pi.single ⟨0, hm⟩ 1
      have hv0 : v ≠ 0 := by
        intro h
        have := congrFun h ⟨0, hm⟩
        simp [v] at this
      have h3 := LinearMap.congr_fun h2 v
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h3
      exact smul_left_injective F hv0 (h3.trans (one_smul F v).symm)
    let ι : Zs → {u : F // u ^ r = 1} := fun g => ⟨c g, hc_root g⟩
    have hι : Function.Injective ι := fun g h hgh => hc_inj (congrArg Subtype.val hgh)
    have hfin : Finite {u : F // u ^ r = 1} := finite_nthRoots F r hr.pos
    exact (Nat.card_le_card_of_injective ι hι).trans (card_nthRoots_le F r hr.pos)
  have h1 : r ^ a ≤ r * r ^ (m - 1) := hb.trans (Nat.mul_le_mul_right _ hZcard)
  have h2 : r * r ^ (m - 1) = r ^ m := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2] at h1
  have h3 : a ≤ m := (Nat.pow_le_pow_iff_right hr.one_lt).mp h1
  rw [hcard]
  exact Nat.pow_le_pow_right hs.pos h3

end CFSG.SignalizerFunctorTheorem.NonLocal
