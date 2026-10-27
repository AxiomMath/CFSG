module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearPrime
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMove
public import Mathlib.FieldTheory.Finite.Basic

public noncomputable section

namespace CFSG.StandardType.TypeA

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {L : Type} [Group L] [Finite L] {ψ : L →* projectiveSL d K}
  {A : Subgroup (MulAut L)}

theorem card_kernel_image_ge_sq_of_cube {p : ℕ} (hp : p.Prime) (hd : 0 < d)
    {G : Subgroup (GL (Fin d) K)} (hG : PGLTor.IsProjElem p G)
    (D : PGLTor.CentralBlockModel p G)
    (hcard : p ^ 3 * (Nat.card K - 1) ≤ Nat.card G) :
    p ^ 2 ≤ Nat.card (D.kernel.map (conjAut d K)) := by
  let Y := D.kernel.map (conjAut d K)
  have hscalar : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin d) u ∈ D.kernel := by
    intro u
    apply (D.kernel_mem_iff _ (hG.scalar_mem u)).mpr
    exact ⟨u, by rw [map_pow]⟩
  have hK : D.kernel = Y.comap (conjAut d K) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · intro x hx
      obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hx
      have hc := QuotMove.isScalarQuot_PSL (K := K) hd
      obtain ⟨u, hu⟩ := hc.exists_scalar_mul_of_eq
        (M := ⟨x, Subgroup.mem_top _⟩) (M' := ⟨y, Subgroup.mem_top _⟩) he.symm
      change x = GeneralLinearGroup.scalar (Fin d) u * y at hu
      rw [hu]
      exact D.kernel.mul_mem (hscalar u) hy
  have hYrange : (Y : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  have hKcard : Nat.card D.kernel = Nat.card Y * (Nat.card K - 1) := by
    rw [hK, card_comap_eq hd hYrange]
  have hs : 0 < Nat.card K - 1 := by have := Finite.one_lt_card (α := K); omega
  have hle : p ^ 3 * (Nat.card K - 1) ≤ (Nat.card Y * p) * (Nat.card K - 1) := by
    calc p ^ 3 * (Nat.card K - 1) ≤ Nat.card G := hcard
      _ ≤ Nat.card D.kernel * p := D.card_le_kernel_mul
      _ = (Nat.card Y * p) * (Nat.card K - 1) := by rw [hKcard]; ac_rfl
  have h1 : p ^ 3 ≤ Nat.card Y * p := Nat.le_of_mul_le_mul_right hle hs
  have h2 : p ^ 2 * p ≤ Nat.card Y * p := by simpa only [pow_succ] using h1
  exact Nat.le_of_mul_le_mul_right h2 hp.pos

omit [Finite L] in
theorem card_actor_le_of_scalar_lift_bound (hd : 0 < d)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L, φ (ψ l) = ψ (a l))
    {n : ℕ}
    (hbound : Nat.card ((inducedSub ψ A).comap (conjAut d K)) ≤ n * (Nat.card K - 1)) :
    Nat.card A ≤ n := by
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  rw [card_comap_eq hd hXI, hcardX] at hbound
  have hK : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  exact Nat.le_of_mul_le_mul_right hbound hK

omit [Finite L] in
theorem card_actor_le_of_central_nontoral_lifts {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L, φ (ψ l) = ψ (a l))
    (hcent : ∀ x ∈ (inducedSub ψ A).comap (conjAut d K), x ^ p = 1 →
      ∀ y ∈ (inducedSub ψ A).comap (conjAut d K), y * x = x * y)
    (hnt : ¬ PGLTor.IsToral ((inducedSub ψ A).comap (conjAut d K))) :
    Nat.card A ≤ p ^ (d / p) := by
  have hG : PGLTor.IsProjElem p ((inducedSub ψ A).comap (conjAut d K)) :=
    isProjElem_comap hd (isElemAbelian_inducedSub hψ hA)
  have hbound := (PGLTor.toral_or_card_le_of_central_sharp hp hp2 hpK hG hcent).resolve_left hnt
  apply card_actor_le_of_scalar_lift_bound hd hψ hker hperf hAI
  simpa only [Fintype.card_fin] using hbound

end CFSG.StandardType.TypeA
