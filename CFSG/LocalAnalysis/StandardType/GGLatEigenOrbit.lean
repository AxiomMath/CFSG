module

public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame

public section

namespace CFSG.StandardType

section LatticeOrbitSums

variable {N : ℕ}

@[expose] def latOrbitSum (p : ℕ) (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (α : Fin N → ℤ) : Fin N → ZMod p :=
  fun j => if latPerm π α = α then (latCorootZ S α j : ZMod p)
    else (latCorootZ S α j : ZMod p) + (latCorootZ S (latPerm π α) j : ZMod p)

private theorem latPerm_single_eq (π : Equiv.Perm (Fin N)) (k : Fin N) :
    latPerm π (Pi.single k (1 : ℤ)) = Pi.single (π k) 1 := by
  funext i
  simp only [latPerm, Pi.single_apply, Equiv.symm_apply_eq]

private theorem latGram_perm_perm (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (hS : ∀ i j, S (π i) (π j) = S i j) (α β : Fin N → ℤ) :
    latGram S (latPerm π α) (latPerm π β) = latGram S α β := by
  unfold latGram latPerm
  refine Fintype.sum_equiv π.symm _ _ fun i => ?_
  refine Fintype.sum_equiv π.symm _ _ fun j => ?_
  have h := hS (π.symm i) (π.symm j)
  simp only [Equiv.apply_symm_apply] at h
  simp [h]

private theorem latCorootZ_perm (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (hS : ∀ i j, S (π i) (π j) = S i j) (α : Fin N → ℤ) (i : Fin N) :
    latCorootZ S (latPerm π α) i = latCorootZ S α (π.symm i) := by
  have h1 : latGram S (Pi.single i 1) (latPerm π α) =
      latGram S (Pi.single (π.symm i) 1) α := by
    have h : (Pi.single i (1 : ℤ) : Fin N → ℤ) = latPerm π (Pi.single (π.symm i) 1) := by
      rw [latPerm_single_eq, Equiv.apply_symm_apply]
    rw [h, latGram_perm_perm S π hS]
  have h2 : latGram S (latPerm π α) (latPerm π α) = latGram S α α :=
    latGram_perm_perm S π hS α α
  simp only [latCorootZ, h1, h2]

theorem latEigenCoroot_le_closure_orbitSum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (hS : ∀ i j, S (π i) (π j) = S i j) (O : Set (Fin N → ℤ)) :
    latEigenCoroot p S π O ⊆
      (AddSubgroup.closure (latOrbitSum p S π '' O) : Set (Fin N → ZMod p)) := by
  rintro g ⟨x, hx, hxg, z, -, hz⟩
  let C : AddSubgroup (Fin N → ZMod p) := AddSubgroup.closure (latOrbitSum p S π '' O)
  let ψ : (Fin N → ℤ) →+ (Fin N → ZMod p) :=
    AddMonoidHom.mk' (fun x j => (x j : ZMod p) + (x (π.symm j) : ZMod p)) (by
      intro x y
      funext j
      simp only [Pi.add_apply, Int.cast_add]
      ring)
  have key : ∀ y ∈ Submodule.span ℤ (latCorootZ S '' O), ψ y ∈ C := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨α, hα, rfl⟩ := hy
      have hmem : latOrbitSum p S π α ∈ C := AddSubgroup.subset_closure ⟨α, hα, rfl⟩
      have hψ : ψ (latCorootZ S α) = fun j =>
          (latCorootZ S α j : ZMod p) + (latCorootZ S (latPerm π α) j : ZMod p) := by
        funext j
        simp [ψ, latCorootZ_perm S π hS]
      rw [hψ]
      by_cases hfix : latPerm π α = α
      · have : (fun j => (latCorootZ S α j : ZMod p) + (latCorootZ S (latPerm π α) j : ZMod p)) =
            (2 : ℕ) • latOrbitSum p S π α := by
          funext j
          simp [latOrbitSum, hfix, two_mul]
        rw [this]
        exact AddSubgroup.nsmul_mem C hmem 2
      · have : (fun j => (latCorootZ S α j : ZMod p) + (latCorootZ S (latPerm π α) j : ZMod p)) =
            latOrbitSum p S π α := by
          funext j
          simp [latOrbitSum, hfix]
        rw [this]
        exact hmem
    | zero => simp
    | add y w _ _ hy hw =>
      rw [map_add]
      exact C.add_mem hy hw
    | smul r y _ hy =>
      rw [map_zsmul]
      exact C.zsmul_mem hy r
  have hfixed : ∀ j, (x (π.symm j) : ZMod p) = (x j : ZMod p) := by
    intro j
    have h := congrFun hz j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    have h' : ((x (π.symm j) - x j : ℤ) : ZMod p) = ((p : ℤ) * z j : ℤ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod p) h
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul] at h'
    exact sub_eq_zero.1 h'
  have h2g : ψ x = (2 : ℕ) • g := by
    funext j
    simp only [ψ, AddMonoidHom.mk'_apply, hfixed j, Pi.smul_apply, ← hxg j, nsmul_eq_mul]
    push_cast
    ring
  have hodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  have hg : g = (k + 1) • ((2 : ℕ) • g) := by
    funext j
    show g j = (k + 1) • ((2 : ℕ) • g j)
    have hp0 : ((2 * k + 1 : ℕ) : ZMod p) = 0 := by
      rw [← hk]
      exact ZMod.natCast_self p
    have h21 : ((k + 1 : ℕ) : ZMod p) * ((2 : ℕ) : ZMod p) = 1 := by
      push_cast at hp0 ⊢
      linear_combination hp0
    rw [nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, h21, one_mul]
  rw [hg]
  have : (2 : ℕ) • g = ψ x := h2g.symm
  rw [this]
  exact C.nsmul_mem (key x hx) (k + 1)

end LatticeOrbitSums

end CFSG.StandardType
