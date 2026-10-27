module

public import CFSG.RankThree.PartOne.KFCL.SpPeel

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFCL.BlockSL CFSG.LieType.Steinberg.Sp
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups commutatorElement Classical

variable {K : Type} [Field K] [CharP K 2] {p : ℕ}

omit [CharP K 2] in
theorem commute_suppGroup_of_trivial {t : StatedSp 3 K} (ht : t ∈ spTorus p 3 K) {X : Set (Fin 3 ⊕ Fin 3)}
    (hX : ∀ a ∈ X, mat 3 K t a a = 1) {g : StatedSp 3 K} (hg : g ∈ suppGroup X) : Commute t g := by
  have hdiag : ∀ a b, a ≠ b → mat 3 K t a b = 0 := fun a b hab => spTorus_apply_ne ht hab
  refine (commute_iff_entries hdiag).2 (fun a b => ?_)
  by_cases hab : mat 3 K g a b = 0
  · rw [hab, mul_zero, zero_mul]
  · by_cases hXab : a ∈ X ∧ b ∈ X
    · rw [hX a hXab.1, hX b hXab.2]
      exact mul_comm _ _
    · have := hg a b hXab
      rw [this] at hab
      have hab' : a = b := by
        by_contra hne
        exact hab (Matrix.one_apply_ne hne)
      subst hab'
      exact mul_comm _ _

theorem Sl_conj_planeSwap (k : Fin 3) :
    ∃ (τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (hτ : τ ∈ Hp 3),
      (Sl K).map (MulAut.conj (permSp τ hτ)).toMonoidHom = suppGroup (coords k) := by
  refine ⟨Equiv.sumCongr (Equiv.swap 0 k) (Equiv.swap 0 k), sumCongr_mem_Hp _, ?_⟩
  rw [Sl, range_longBlock, map_conj_suppGroup]
  congr 1
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases mem_coords.1 hd with rfl | rfl
    · exact mem_coords.2 (Or.inl (by simp))
    · exact mem_coords.2 (Or.inr (by simp))
  · intro hc
    rcases mem_coords.1 hc with rfl | rfl
    · exact ⟨Sum.inl 0, inl_mem_coords 0, by simp⟩
    · exact ⟨Sum.inr 0, inr_mem_coords 0, by simp⟩

theorem suppGroup_coords_le_Jjoin {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K) {k : Fin 3}
    (hk : ∀ s ∈ S, mat 3 K s (Sum.inl k) (Sum.inl k) = 1) :
    suppGroup (coords k) ≤ Jjoin p S := by
  obtain ⟨τ, hτ, hB⟩ := Sl_conj_planeSwap (K := K) k
  have hS : S ≤ spTorus p 3 K ⊓ Subgroup.centralizer
      ((suppGroup (coords k) : Subgroup (StatedSp 3 K)) : Set (StatedSp 3 K)) := by
    intro s hs
    refine ⟨hST hs, ?_⟩
    show s ∈ Subgroup.centralizer ((suppGroup (coords k) : Subgroup (StatedSp 3 K)) : Set (StatedSp 3 K))
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    refine (commute_suppGroup_of_trivial (hST hs) (X := coords k) (fun a ha => ?_) hg).symm.eq
    rcases mem_coords.1 ha with rfl | rfl
    · exact hk s hs
    · rw [show (Sum.inr k : Fin 3 ⊕ Fin 3) = par (Sum.inl k) from rfl, spTorus_par (hST hs), hk s hs, inv_one]
  rw [← hB] at hS ⊢
  exact le_Jjoin (conj_Sl_mem_orbit hτ) hS

theorem shortBlock_range_le_conj {i j : Fin 3} (hij : i ≠ j) {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)}
    (hτ : τ ∈ Hp 3) (h0 : τ (Sum.inl 0) = Sum.inl i) (h1 : τ (Sum.inl 1) = Sum.inl j) :
    (shortBlock K hij).range ≤ (Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom := by
  rintro _ ⟨A, rfl⟩
  refine Subgroup.closure_induction
    (p := fun A _ => shortBlock K hij A ∈ (Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom) ?_ ?_ ?_ ?_
    (mem_closure_sl2 A)
  · rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [shortBlock_sl2Upper]
      have : elt (.difference i j hij) c =
          permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
      rw [this]
      exact Wel_mem_conj hτ c
    · rw [shortBlock_sl2Lower]
      have h1' : τ (Sum.inl 1) = Sum.inl j := h1
      have : elt (.difference j i hij.symm) c =
          permSp τ hτ * elt (.difference 1 0 h01.symm) c * (permSp τ hτ)⁻¹ := by
        apply mat_injective
        rw [mat_conj_elt_diff, mat_elt, h0, h1]
        simp [E]
      rw [this]
      exact Subgroup.mem_map.2 ⟨_, ⟨sl2Lower c, shortBlock_sl2Lower h01 c⟩, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem suppGroup_coords_union_le_Jjoin {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K)
    {i j : Fin 3} (hij : i ≠ j) (hi : ∀ s ∈ S, mat 3 K s (Sum.inl i) (Sum.inl i) = 1)
    (hj : ∀ s ∈ S, mat 3 K s (Sum.inl j) (Sum.inl j) = 1) :
    suppGroup (coords i ∪ coords j) ≤ Jjoin p S := by
  rw [← shortBlock_sup_longBlock_eq_suppGroup hij, sup_le_iff]
  constructor
  · obtain ⟨π, h0, h1⟩ := exists_perm_pair' (show (0 : Fin 3) ≠ 1 by decide) hij
    have hτ := sumCongr_mem_Hp π
    have e0 : (Equiv.sumCongr π π) (Sum.inl 0) = Sum.inl i := by simp [h0]
    have e1 : (Equiv.sumCongr π π) (Sum.inl 1) = Sum.inl j := by simp [h1]
    refine (shortBlock_range_le_conj hij hτ e0 e1).trans (le_Jjoin (conj_Ss_mem_orbit hτ) ?_)
    refine le_hyp_conj_Ss hST hτ ?_
    rw [e0, e1]
    funext s
    simp only [cls]
    rw [hi s.1 s.2, hj s.1 s.2]
  · rw [range_longBlock]
    exact suppGroup_coords_le_Jjoin hST hj

end CFSG.RankThree.PartOne.KFCL.Sp
