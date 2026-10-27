module

import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

structure WeylIso (p n : ℕ) (E L : Subgroup G) where
  ψ : ↥(Subgroup.closure (reflectionSet p E)) ≃* Equiv.Perm (Fin (n + 1))
  isSwap : ∀ (t : MulAut E) (ht : t ∈ reflectionSet p E),
    (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap
  surj : ∀ σ : Equiv.Perm (Fin (n + 1)), σ.IsSwap →
    ∃ (t : MulAut E) (ht : t ∈ reflectionSet p E), ψ ⟨t, Subgroup.subset_closure ht⟩ = σ
  point : Fin (n + 1)
  fixes : ∀ x ∈ torusImage E L,
    ∃ h : x ∈ Subgroup.closure (reflectionSet p E), (ψ ⟨x, h⟩) point = point

namespace WeylIso

variable {p n : ℕ} {E L : Subgroup G} (W : WeylIso p n E L)

omit [Finite G] in
theorem card_stabilizer_fin (k : Fin (n + 1)) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) k) = n.factorial := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) k)
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_perm,
    Nat.card_fin, Nat.factorial_succ] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) (h1.trans (mul_comm _ _))

theorem exists_fin_ne (hn : 4 ≤ n) (a b c d : Fin (n + 1)) :
    ∃ m : Fin (n + 1), m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d := by
  have hcard : ({a, b, c, d} : Finset (Fin (n + 1))).card <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩

omit [Finite G] in
theorem ne_of_swap_fix {X : Type} [DecidableEq X] {a b m : X} (hab : a ≠ b)
    (h : Equiv.swap a b m = m) : m ≠ a ∧ m ≠ b := by
  constructor
  · rintro rfl
    rw [Equiv.swap_apply_left] at h
    exact hab h.symm
  · rintro rfl
    rw [Equiv.swap_apply_right] at h
    exact hab h

omit [Finite G] in
theorem mem_torusWeyl_of_mem_reflectionSet {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    t ∈ torusWeyl E := by
  obtain ⟨-, X, -, htX⟩ := ht
  exact Sec127.torusImage_le_torusWeyl E X htX

omit [Finite G] in
theorem closure_le_weyl : Subgroup.closure (reflectionSet p E) ≤ torusWeyl E :=
  (Subgroup.closure_le _).2 fun _ ht => mem_torusWeyl_of_mem_reflectionSet ht

omit [Finite G] in
theorem exists_lift {g : MulAut E} (hg : g ∈ torusWeyl E) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), conjAut E w hw = g := by
  have hg' : g ∈ E.normalizerMonoidHom.range := hg
  obtain ⟨⟨w, hw⟩, h⟩ := MonoidHom.mem_range.mp hg'
  exact ⟨w, hw, h⟩

theorem conj_mem_reflectionSet_of_weyl (hp : p.Prime) {g t : MulAut E} (hg : g ∈ torusWeyl E)
    (ht : t ∈ reflectionSet p E) : g * t * g⁻¹ ∈ reflectionSet p E := by
  obtain ⟨w, hw, rfl⟩ := exists_lift hg
  exact conj_mem_reflectionSet hp ht hw

omit [Finite G] in
theorem exists_conj_eq_of_swaps {S : Set (MulAut E)}
    (ψ : ↥(Subgroup.closure S) ≃* Equiv.Perm (Fin (n + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ S), (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    {s t : MulAut E} (hs : s ∈ S) (ht : t ∈ S) :
    ∃ g ∈ Subgroup.closure S, g * s * g⁻¹ = t := by
  obtain ⟨a, b, hab, hsab⟩ := hsw s hs
  obtain ⟨c, d, hcd, htcd⟩ := hsw t ht
  obtain ⟨τ, hτ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hcd)
  refine ⟨((ψ.symm τ : ↥(Subgroup.closure S)) : MulAut E), (ψ.symm τ).2, ?_⟩
  have h : ψ.symm τ * (⟨s, Subgroup.subset_closure hs⟩ : ↥(Subgroup.closure S)) *
      (ψ.symm τ)⁻¹ = ⟨t, Subgroup.subset_closure ht⟩ := by
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hsab, htcd, hτ]
  exact congrArg Subtype.val h

omit [Finite G] in
include W in
theorem exists_conj_eq {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (ht : t ∈ reflectionSet p E) :
    ∃ g ∈ Subgroup.closure (reflectionSet p E), g * s * g⁻¹ = t :=
  exists_conj_eq_of_swaps W.ψ W.isSwap hs ht

theorem mem_torusImage_iff (hL : Nat.card (torusImage E L) = n.factorial) {x : MulAut E}
    (hx : x ∈ Subgroup.closure (reflectionSet p E)) :
    x ∈ torusImage E L ↔ (W.ψ ⟨x, hx⟩) W.point = W.point := by
  have hLC : torusImage E L ≤ Subgroup.closure (reflectionSet p E) := fun y hy =>
    (W.fixes y hy).fst
  have hmemS1 : ∀ y : ↥(Subgroup.closure (reflectionSet p E)),
      y ∈ (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) W.point).map W.ψ.symm.toMonoidHom ↔
        W.ψ y W.point = W.point := by
    intro y
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def]
  have hle : (torusImage E L).subgroupOf (Subgroup.closure (reflectionSet p E)) ≤
      (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) W.point).map W.ψ.symm.toMonoidHom := by
    intro y hy
    obtain ⟨h, h2⟩ := W.fixes y (Subgroup.mem_subgroupOf.1 hy)
    exact (hmemS1 y).2 h2
  have hc1 : Nat.card ((MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) W.point).map
      W.ψ.symm.toMonoidHom) = n.factorial := by
    rw [Subgroup.card_map_of_injective W.ψ.symm.injective, card_stabilizer_fin]
  have hc2 : Nat.card ((torusImage E L).subgroupOf (Subgroup.closure (reflectionSet p E))) =
      n.factorial := by
    rw [← hL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv
  have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hc1.trans hc2.symm))
  have hiff : (⟨x, hx⟩ : ↥(Subgroup.closure (reflectionSet p E))) ∈
      (torusImage E L).subgroupOf (Subgroup.closure (reflectionSet p E)) ↔
      (⟨x, hx⟩ : ↥(Subgroup.closure (reflectionSet p E))) ∈
      (MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) W.point).map W.ψ.symm.toMonoidHom := by
    rw [heq]
  rw [hmemS1] at hiff
  exact hiff

include W in
theorem conj_mem_torusImage (hL : Nat.card (torusImage E L) = n.factorial) {s : MulAut E}
    (hs : s ∈ reflectionSet p E) {σ : Equiv.Perm (Fin (n + 1))} {a b : Fin (n + 1)}
    (hsab : W.ψ ⟨s, Subgroup.subset_closure hs⟩ = Equiv.swap a b) (ha : σ a ≠ W.point)
    (hb : σ b ≠ W.point) :
    ((W.ψ.symm σ : ↥(Subgroup.closure (reflectionSet p E))) : MulAut E) * s *
      ((W.ψ.symm σ : ↥(Subgroup.closure (reflectionSet p E))) : MulAut E)⁻¹ ∈
        torusImage E L := by
  have hmem : ((W.ψ.symm σ * (⟨s, Subgroup.subset_closure hs⟩ :
      ↥(Subgroup.closure (reflectionSet p E))) * (W.ψ.symm σ)⁻¹ :
      ↥(Subgroup.closure (reflectionSet p E))) : MulAut E) ∈
      Subgroup.closure (reflectionSet p E) := SetLike.coe_mem _
  have h := (W.mem_torusImage_iff hL hmem).2
  apply h
  show (W.ψ (W.ψ.symm σ * (⟨s, Subgroup.subset_closure hs⟩ :
      ↥(Subgroup.closure (reflectionSet p E))) * (W.ψ.symm σ)⁻¹)) W.point = W.point
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hsab, ← Equiv.swap_apply_apply]
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)

include W in
theorem exists_conj_into_L (hL : Nat.card (torusImage E L) = n.factorial) {s t : MulAut E}
    (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E)
    (hfix : ∃ m, W.ψ ⟨s, Subgroup.subset_closure hs⟩ m = m ∧
      W.ψ ⟨t, Subgroup.subset_closure ht⟩ m = m) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L ∧
      conjAut E w hw * t * (conjAut E w hw)⁻¹ ∈ torusImage E L := by
  obtain ⟨a, b, hab, hsab⟩ := W.isSwap s hs
  obtain ⟨c, d, hcd, htcd⟩ := W.isSwap t ht
  obtain ⟨m, hms, hmt⟩ := hfix
  rw [hsab] at hms
  rw [htcd] at hmt
  obtain ⟨hma, hmb⟩ := ne_of_swap_fix hab hms
  obtain ⟨hmc, hmd⟩ := ne_of_swap_fix hcd hmt
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap m W.point with hσdef
  have hσm : σ m = W.point := Equiv.swap_apply_left m W.point
  have hne : ∀ x : Fin (n + 1), x ≠ m → σ x ≠ W.point := fun x hx h =>
    hx (σ.injective (h.trans hσm.symm))
  obtain ⟨w, hw, hwg⟩ := exists_lift (closure_le_weyl (E := E) (W.ψ.symm σ).2)
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hwg]
    exact W.conj_mem_torusImage hL hs hsab (hne a (Ne.symm hma)) (hne b (Ne.symm hmb))
  · rw [hwg]
    exact W.conj_mem_torusImage hL ht htcd (hne c (Ne.symm hmc)) (hne d (Ne.symm hmd))

omit [Finite G] in
include W in
theorem exists_common_fixed (hn : 4 ≤ n) {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (ht : t ∈ reflectionSet p E) :
    ∃ m, W.ψ ⟨s, Subgroup.subset_closure hs⟩ m = m ∧
      W.ψ ⟨t, Subgroup.subset_closure ht⟩ m = m := by
  obtain ⟨a, b, -, hsab⟩ := W.isSwap s hs
  obtain ⟨c, d, -, htcd⟩ := W.isSwap t ht
  obtain ⟨m, hma, hmb, hmc, hmd⟩ := exists_fin_ne hn a b c d
  refine ⟨m, ?_, ?_⟩
  · rw [hsab]
    exact Equiv.swap_apply_of_ne_of_ne hma hmb
  · rw [htcd]
    exact Equiv.swap_apply_of_ne_of_ne hmc hmd

omit [Finite G] in
theorem nonempty_of_eq {S : Set (MulAut E)} (hS : reflectionSet p E = S)
    (ψ : ↥(Subgroup.closure S) ≃* Equiv.Perm (Fin (n + 1)))
    (hsw : ∀ (t : MulAut E) (ht : t ∈ S), (ψ ⟨t, Subgroup.subset_closure ht⟩).IsSwap)
    (hsurj : ∀ σ : Equiv.Perm (Fin (n + 1)), σ.IsSwap →
      ∃ (t : MulAut E) (ht : t ∈ S), ψ ⟨t, Subgroup.subset_closure ht⟩ = σ)
    (k : Fin (n + 1)) (hk : ∀ x ∈ torusImage E L,
      ∃ h : x ∈ Subgroup.closure S, (ψ ⟨x, h⟩) k = k) : Nonempty (WeylIso p n E L) := by
  subst hS
  exact ⟨⟨ψ, hsw, hsurj, k, hk⟩⟩

end WeylIso

end CFSG.RankThree.PartOne
