module

public import CFSG.RankThree.PartOne.N1322.MonoNormal2
import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.RankThree.PartOne.S12.ReflThree

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

@[expose] def zU : Fin 3 → Kˣ := fun j => epsU 1 j * epsU 2 j

theorem P12_sq : (permMono (swap 1 2) : GL (Fin 3) K) * permMono (swap 1 2) = 1 := by
  rw [← map_mul, swap_mul_self, map_one]

theorem P01_sq : (permMono (swap 0 1) : GL (Fin 3) K) * permMono (swap 0 1) = 1 := by
  rw [← map_mul, swap_mul_self, map_one]

theorem braid_PP : (permMono (swap 1 2) * permMono (swap 0 1) * permMono (swap 1 2) :
    GL (Fin 3) K) = permMono (swap 0 1) * permMono (swap 1 2) * permMono (swap 0 1) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  decide

theorem Z_sq : (mono (swap 1 2) zU : GL (Fin 3) K) * mono (swap 1 2) zU = 1 := by
  rw [mono_mul]
  refine (mono_ext (by simp) (fun j => ?_)).trans mono_one
  fin_cases j <;> simp [zU, epsU, swap_apply_def]

theorem braid_PZ : (permMono (swap 0 1) * mono (swap 1 2) zU * permMono (swap 0 1) :
    GL (Fin 3) K) = mono (swap 1 2) zU * permMono (swap 0 1) * mono (swap 1 2) zU := by
  simp only [permMono_apply]
  rw [mono_mul, mono_mul, mono_mul, mono_mul]
  exact mono_ext (by decide) (fun j => by fin_cases j <;> simp [zU, epsU, swap_apply_def])

theorem comm_PZ : (permMono (swap 1 2) * mono (swap 1 2) zU : GL (Fin 3) K) =
    mono (swap 1 2) zU * permMono (swap 1 2) := by
  simp only [permMono_apply]
  rw [mono_mul, mono_mul]
  exact mono_ext (by simp) (fun j => by fin_cases j <;> simp [zU, epsU, swap_apply_def])

theorem P12_ne_one : (permMono (swap 1 2) : GL (Fin 3) K) ≠ 1 := by
  intro h
  rw [permMono_apply, ← mono_one] at h
  have := (mono_injective h).1
  revert this
  decide

theorem P12_ne_Z (h2 : (2 : K) ≠ 0) : (permMono (swap 1 2) : GL (Fin 3) K) ≠ mono (swap 1 2) zU := by
  intro h
  rw [permMono_apply] at h
  have := congrFun (mono_injective h).2 1
  simp [zU, epsU] at this
  exact neg_one_ne_one h2 this.symm

theorem P12_ne_P01 : (permMono (swap 1 2) : GL (Fin 3) K) ≠ permMono (swap 0 1) := by
  intro h
  rw [permMono_apply, permMono_apply] at h
  have := (mono_injective h).1
  revert this
  decide

theorem perm4_center : ∀ τ : Perm (Fin 4), (∀ σ : Perm (Fin 4), σ * τ = τ * σ) → τ = 1 := by
  decide

theorem mult_two_cases : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ Multiplicative.toAdd a = 1 := by
  decide

theorem mono_normal (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X)
    (hc2 : ∃ μ : K, μ ≠ 0 ∧ d.c = μ • Pi.single 2 1)
    (e0 : eps 0 ∈ d.D) (e1 : eps 1 ∈ d.D) (e2 : eps 2 ∈ d.D)
    (a01 : aref 0 1 1 ∈ d.Lm) (a12 : aref 1 2 1 ∈ d.X)
    (hL01 : ∀ s : Kˣ, aref 0 1 s ∈ d.Lm → s = 1 ∨ s = -1) :
    Nonempty (d.X ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  have hXle : d.X ≤ wb3 K := by
    rw [h.gen]
    exact (Subgroup.closure_le _).mpr (D_subset_wb3 h2 h hm hc2 a01 a12 hL01)
  have hXD : ∀ g ∈ d.D, g ∈ d.X := fun g hg => by
    rw [h.gen]; exact Subgroup.subset_closure hg
  obtain ⟨hwfin, hwcard⟩ := wb3_finite_card (K := K) h2
  have hfin : Finite d.X := Finite.of_injective (Subgroup.inclusion hXle)
    (Subgroup.inclusion_injective hXle)
  have hcardX : Nat.card d.X ≤ 48 := by
    have := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hXle)
    omega
  have hp01 : (permMono (swap 0 1) : GL (Fin 3) K) ∈ d.X := by
    have : (permMono (swap 0 1) : GL (Fin 3) K) = aref 0 1 1 := by
      show mono (swap 0 1) (fun _ => 1) = mono (swap 0 1) (aU 0 1 1)
      rw [aU_one]
    rw [this]; exact h.Lle a01
  have hp12 : (permMono (swap 1 2) : GL (Fin 3) K) ∈ d.X := by
    have : (permMono (swap 1 2) : GL (Fin 3) K) = aref 1 2 1 := by
      show mono (swap 1 2) (fun _ => 1) = mono (swap 1 2) (aU 1 2 1)
      rw [aU_one]
    rw [this]; exact a12
  have hZ : (mono (swap 1 2) zU : GL (Fin 3) K) ∈ d.X := by
    have : (mono (swap 1 2) zU : GL (Fin 3) K) = permMono (swap 1 2) * (eps 1 * eps 2) := by
      rw [eps, eps, mono_mul, permMono_apply, mono_mul]
      exact mono_ext (by simp) (fun j => by simp [zU])
    rw [this]
    exact d.X.mul_mem hp12 (d.X.mul_mem (hXD _ e1) (hXD _ e2))
  have hM : (mono 1 (fun _ => (-1 : Kˣ)) : GL (Fin 3) K) ∈ d.X := by
    have : (mono 1 (fun _ => (-1 : Kˣ)) : GL (Fin 3) K) = eps 0 * eps 1 * eps 2 := by
      rw [eps, eps, eps, mono_mul, mono_mul]
      exact mono_ext (by simp) (fun j => by fin_cases j <;> simp [epsU])
    rw [this]
    exact d.X.mul_mem (d.X.mul_mem (hXD _ e0) (hXD _ e1)) (hXD _ e2)
  let x : d.X := ⟨permMono (swap 1 2), hp12⟩
  let y : d.X := ⟨permMono (swap 0 1), hp01⟩
  let z : d.X := ⟨mono (swap 1 2) zU, hZ⟩
  let m : d.X := ⟨mono 1 (fun _ => (-1 : Kˣ)), hM⟩
  obtain ⟨Ψ, hΨinj, -, -, -⟩ := ReflF.exists_perm_four (H := d.X) (x := x) (y := y) (z := z)
    (Subtype.ext P12_sq) (Subtype.ext P01_sq) (Subtype.ext Z_sq) (Subtype.ext braid_PP)
    (Subtype.ext braid_PZ) (Subtype.ext comm_PZ)
    (fun h' => P12_ne_one (congrArg Subtype.val h'))
    (fun h' => P12_ne_Z h2 (congrArg Subtype.val h'))
    (fun h' => P12_ne_P01 (congrArg Subtype.val h'))
  have hm2 : m * m = 1 := by
    apply Subtype.ext
    show mono 1 (fun _ => (-1 : Kˣ)) * mono 1 (fun _ => (-1 : Kˣ)) = (1 : GL (Fin 3) K)
    rw [mono_mul]
    exact (mono_ext (by simp) (fun j => by simp)).trans mono_one
  have hm1 : m ≠ 1 := by
    intro h'
    have h'' : (mono 1 (fun _ => (-1 : Kˣ)) : GL (Fin 3) K) = 1 := congrArg Subtype.val h'
    rw [← mono_one] at h''
    have := congrFun (mono_injective h'').2 0
    exact neg_one_ne_one h2 this
  have hcentral : ∀ w : d.X, Commute m w := by
    intro w
    apply Subtype.ext
    obtain ⟨σ, a, hw⟩ := hm.isMono w.1 w.2
    show mono 1 (fun _ => (-1 : Kˣ)) * (w : GL (Fin 3) K) = (w : GL (Fin 3) K) * mono 1 (fun _ => -1)
    rw [hw, mono_mul, mono_mul]
    exact mono_ext (by simp) (fun j => by simp [mul_comm])
  have hm2' : m ^ 2 = 1 := by rw [pow_two]; exact hm2
  let φ₁ : Multiplicative (ZMod 2) →* d.X :=
    { toFun := fun a => m ^ (Multiplicative.toAdd a).val
      map_one' := by simp
      map_mul' := fun a b => by
        show m ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val =
          m ^ (Multiplicative.toAdd a).val * m ^ (Multiplicative.toAdd b).val
        rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hm2'] }
  let Φ : Multiplicative (ZMod 2) × Perm (Fin 4) →* d.X :=
    MonoidHom.noncommCoprod φ₁ Ψ (fun a τ => ((hcentral (Ψ τ)).pow_left _))
  have hΦ : ∀ a τ, Φ (a, τ) = φ₁ a * Ψ τ := fun a τ => by
    simp [Φ, MonoidHom.noncommCoprod_apply]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, τ⟩ hφ
    rw [hΦ] at hφ
    rcases mult_two_cases a with ha | ha
    · subst ha
      have : Ψ τ = 1 := by simpa [φ₁] using hφ
      have hτ : τ = 1 := hΨinj (by rw [this, map_one])
      rw [hτ]
      rfl
    · exfalso
      have hφa : φ₁ a = m := by
        show m ^ (Multiplicative.toAdd a).val = m
        rw [ha]
        show m ^ 1 = m
        exact pow_one m
      rw [hφa] at hφ
      have hΨτ : Ψ τ = m := by
        have := eq_inv_of_mul_eq_one_right hφ
        rw [this]; exact inv_eq_of_mul_eq_one_right hm2
      have hτ : τ = 1 := by
        apply perm4_center
        intro σ
        apply hΨinj
        rw [map_mul, map_mul, hΨτ]
        exact (hcentral (Ψ σ)).symm.eq
      apply hm1
      rw [← hΨτ, hτ, map_one]
  have hcardG : Nat.card (Multiplicative (ZMod 2) × Perm (Fin 4)) = 48 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by rw [hcardG]; exact hcardX)
  exact ⟨(MulEquiv.ofBijective Φ hbij).symm⟩

end CFSG.RankThree.PartOne.N1322
