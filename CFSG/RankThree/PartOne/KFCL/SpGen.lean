module

public import CFSG.RankThree.PartOne.KFCL.SpOrbit

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def pl : Fin 3 ⊕ Fin 3 → Fin 3 := Sum.elim id id

theorem pl_par (a : Fin 3 ⊕ Fin 3) : pl (par a) = pl a := by
  rcases a with i | i <;> rfl

theorem mem_coords_iff_pl {k : Fin 3} {a : Fin 3 ⊕ Fin 3} : a ∈ coords k ↔ pl a = k := by
  rw [mem_coords]
  rcases a with i | i
  · simp [pl]
  · simp [pl]

variable (K) in
@[expose] def HL : Subgroup (StatedSp 3 K) where
  carrier := {g | ∀ a b, pl a ≠ pl b → mat 3 K g a b = 0}
  one_mem' := by
    intro a b hab
    rw [map_one]
    exact Matrix.one_apply_ne (fun h => hab (by rw [h]))
  mul_mem' := by
    intro x y hx hy a b hab
    rw [map_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases hac : pl a = pl c
    · rw [hy c b (by rw [← hac]; exact hab), mul_zero]
    · rw [hx a c hac, zero_mul]
  inv_mem' := by
    intro x hx a b hab
    rw [mat_inv_apply, hx (par b) (par a) (by rw [pl_par, pl_par]; exact hab.symm), mul_zero]

theorem mem_HL {g : StatedSp 3 K} : g ∈ HL K ↔ ∀ a b, pl a ≠ pl b → mat 3 K g a b = 0 := Iff.rfl

theorem suppGroup_le_HL {X : Set (Fin 3 ⊕ Fin 3)} {k : Fin 3} (hX : X ⊆ coords k) :
    suppGroup X ≤ HL K := by
  intro x hx
  rw [mem_HL]
  intro a b hab
  have h1 := hx a b (fun h => hab (by
    have ha := mem_coords_iff_pl.1 (hX h.1)
    have hb := mem_coords_iff_pl.1 (hX h.2)
    rw [ha, hb]))
  rw [h1]
  exact Matrix.one_apply_ne (fun h => hab (by rw [h]))

theorem HL_ne_top : HL K ≠ ⊤ := by
  intro h
  have hmem : elt (.difference 0 1 h01) (1 : K) ∈ HL K := by rw [h]; exact Subgroup.mem_top _
  have := hmem (Sum.inl 0) (Sum.inl 1) (by decide)
  rw [mat_elt_difference_apply] at this
  exact one_ne_zero this

@[expose] def Qf (v : Fin 3 ⊕ Fin 3 → K) : K := ∑ i : Fin 3, v (Sum.inl i) * v (Sum.inr i)

variable (K) in
@[expose] def HS : Subgroup (StatedSp 3 K) where
  carrier := {g | ∀ v, Qf (mat 3 K g *ᵥ v) = Qf v}
  one_mem' := by
    intro v
    rw [map_one, Matrix.one_mulVec]
  mul_mem' := by
    intro x y hx hy v
    rw [map_mul, ← Matrix.mulVec_mulVec, hx, hy]
  inv_mem' := by
    intro x hx v
    have h := hx (mat 3 K x⁻¹ *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec] at h
    exact h.symm

theorem eq_or_eq_par_of_pl_eq {a b : Fin 3 ⊕ Fin 3} (h : pl a = pl b) : a = b ∨ a = par b := by
  rcases a with i | i <;> rcases b with j | j
  · left
    exact congrArg Sum.inl h
  · right
    exact congrArg Sum.inl h
  · right
    exact congrArg Sum.inr h
  · left
    exact congrArg Sum.inr h

theorem Qf_comp_perm {σ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hσ : σ ∈ Hp 3) (v : Fin 3 ⊕ Fin 3 → K) :
    Qf (v ∘ σ) = Qf v := by
  set g : Fin 3 → K := fun k => v (Sum.inl k) * v (Sum.inr k) with hg
  have hpair : ∀ a, v a * v (par a) = g (pl a) := by
    intro a
    rcases a with k | k
    · rfl
    · exact mul_comm _ _
  have hinj : Function.Injective (fun i : Fin 3 => pl (σ (Sum.inl i))) := by
    intro i j hij
    rcases eq_or_eq_par_of_pl_eq hij with h | h
    · exact Sum.inl_injective (σ.injective h)
    · exfalso
      have h1 := hσ (Sum.inl j)
      rw [par_inl] at h1
      have h2 : σ (Sum.inl i) = σ (Sum.inr j) := by
        rw [h, h1]
      exact Sum.inl_ne_inr (σ.injective h2)
  have hbij : Function.Bijective (fun i : Fin 3 => pl (σ (Sum.inl i))) :=
    Finite.injective_iff_bijective.1 hinj
  calc Qf (v ∘ σ) = ∑ i : Fin 3, g (pl (σ (Sum.inl i))) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have h := hσ (Sum.inl i)
        rw [par_inl] at h
        simp only [Function.comp_apply]
        rw [← hpair, h]
    _ = ∑ i : Fin 3, g i := hbij.sum_comp g
    _ = Qf v := rfl

section QElt

theorem Qf_elt_diff01 (c : K) (v : Fin 3 ⊕ Fin 3 → K) :
    Qf (mat 3 K (elt (.difference 0 1 h01) c) *ᵥ v) = Qf v := by
  rw [mat_elt]
  simp [Qf, E, Fin.sum_univ_three, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Function.update_apply]
  ring

theorem Qf_elt_diff10 (c : K) (v : Fin 3 ⊕ Fin 3 → K) :
    Qf (mat 3 K (elt (.difference 1 0 h01.symm) c) *ᵥ v) = Qf v := by
  rw [mat_elt]
  simp [Qf, E, Fin.sum_univ_three, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Function.update_apply]
  ring

theorem Ss_le_HS : Ss K ≤ HS K := by
  rintro _ ⟨A, rfl⟩
  refine Subgroup.closure_induction
    (p := fun A _ => shortBlock K h01 A ∈ HS K) ?_ ?_ ?_ ?_ (mem_closure_sl2 A)
  · rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [shortBlock_sl2Upper]
      exact fun v => Qf_elt_diff01 c v
    · rw [shortBlock_sl2Lower]
      exact fun v => Qf_elt_diff10 c v
  · rw [map_one]
    exact (HS K).one_mem
  · intro x y _ _ hx hy
    rw [map_mul]
    exact (HS K).mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact (HS K).inv_mem hx

theorem HS_ne_top : HS K ≠ ⊤ := by
  intro h
  have hmem : elt (.positiveLong 0) (1 : K) ∈ HS K := by rw [h]; exact Subgroup.mem_top _
  have := hmem (Pi.single (Sum.inr 0) 1)
  rw [mat_elt] at this
  simp [Qf, E, Fin.sum_univ_three, Pi.single_apply] at this

section Perm

variable [CharP K 2]

theorem permSp_mem_HS {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) :
    permSp (K := K) τ hτ ∈ HS K := by
  intro v
  have : mat 3 K (permSp τ hτ) *ᵥ v = v ∘ (⇑(τ⁻¹)) := by
    rw [mat_permSp, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  rw [this]
  exact Qf_comp_perm ((Hp 3).inv_mem hτ) v

end Perm

end QElt

section Orbit

variable [CharP K 2]

theorem Sl_conj_le_HL {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) :
    (Sl K).map (MulAut.conj (permSp τ hτ)).toMonoidHom ≤ HL K := by
  rw [Sl, range_longBlock, map_conj_suppGroup]
  refine suppGroup_le_HL (k := pl (τ (Sum.inl 0))) ?_
  rintro _ ⟨a, ha, rfl⟩
  rcases mem_coords.1 ha with rfl | rfl
  · exact mem_coords_iff_pl.2 rfl
  · have h1 := hτ (Sum.inl 0)
    rw [par_inl] at h1
    rw [mem_coords_iff_pl, h1, pl_par]

theorem hgen_Sp : ∀ Std' : Set (Subgroup (StatedSp 3 K)), Std' ⊆ SpStd K → Std' ≠ SpStd K →
    ∃ P : Subgroup (StatedSp 3 K), P ≠ ⊤ ∧ ∀ B ∈ blockOrbit (spWeyl 3 K) Std', B ≤ P := by
  intro Std' hsub hne
  by_cases hSl : Sl K ∈ Std'
  · have hSs : Ss K ∉ Std' := by
      intro hSs
      apply hne
      refine Set.Subset.antisymm hsub ?_
      rintro S (rfl | rfl)
      · exact hSl
      · exact hSs
    refine ⟨HL K, HL_ne_top, ?_⟩
    rintro B ⟨w, hw, S, hS, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := mem_spWeyl_iff.1 hw
    have hSeq : S = Sl K := by
      rcases hsub hS with h | h
      · exact h
      · exact absurd (h ▸ hS) hSs
    subst hSeq
    exact Sl_conj_le_HL hτ
  · refine ⟨HS K, HS_ne_top, ?_⟩
    rintro B ⟨w, hw, S, hS, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := mem_spWeyl_iff.1 hw
    have hSeq : S = Ss K := by
      rcases hsub hS with h | h
      · exact absurd (h ▸ hS) hSl
      · exact h
    subst hSeq
    rintro _ ⟨y, hy, rfl⟩
    exact (HS K).mul_mem ((HS K).mul_mem (permSp_mem_HS hτ) (Ss_le_HS hy))
      ((HS K).inv_mem (permSp_mem_HS hτ))

end Orbit

end CFSG.RankThree.PartOne.KFCL.Sp
