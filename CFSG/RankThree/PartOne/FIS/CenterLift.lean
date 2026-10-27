module

public import CFSG.RankThree.PartOne.FIS.CenterQuotient
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Permutation.SymmetricCoxeter
open Equiv Equiv.Perm

private theorem isSwap_adjSwap {m i : ℕ} (hi : i < m) : (adjSwap m i).IsSwap :=
  ⟨⟨i, by omega⟩, ⟨i + 1, by omega⟩, by simp [Fin.ext_iff], adjSwap_of_lt hi⟩

private theorem adjSwap_apply_left {m i : ℕ} (hi : i < m) :
    adjSwap m i ⟨i, by omega⟩ = ⟨i + 1, by omega⟩ := by
  rw [adjSwap_of_lt hi]
  exact swap_apply_left _ _

private theorem adjSwap_apply_of_ne {m i : ℕ} (hi : i < m) (x : Fin (m + 1)) (h0 : x.val ≠ i)
    (h1 : x.val ≠ i + 1) : adjSwap m i x = x := by
  rw [adjSwap_of_lt hi]
  exact swap_apply_of_ne_of_ne (fun h => h0 (congrArg Fin.val h))
    (fun h => h1 (congrArg Fin.val h))

private theorem adjSwap_mul_succ_ne {m i : ℕ} (hi : i + 1 < m) :
    adjSwap m i * adjSwap m (i + 1) ≠ adjSwap m (i + 1) * adjSwap m i := by
  intro h
  have h' := DFunLike.congr_fun h ⟨i, by omega⟩
  simp only [Perm.mul_apply] at h'
  rw [adjSwap_apply_of_ne hi ⟨i, by omega⟩ (by simp only; omega) (by simp only; omega),
    adjSwap_apply_left (by omega), adjSwap_apply_left hi] at h'
  simp [Fin.ext_iff] at h'

private theorem adjSwap_ne_of_add_two_le {m i j : ℕ} (hij : i + 2 ≤ j) (hj : j < m) :
    adjSwap m i ≠ adjSwap m j := by
  intro h
  have h' := DFunLike.congr_fun h ⟨i, by omega⟩
  rw [adjSwap_apply_left (by omega), adjSwap_apply_of_ne hj ⟨i, by omega⟩ (by simp only; omega)
    (by simp only; omega)] at h'
  simp [Fin.ext_iff] at h'

theorem exists_coxeter_lift {G : Type} [Group G] {D : Set G} (hP : Pair G D) {m : ℕ}
    (ψ : Perm (Fin (m + 1)) ≃* (G ⧸ Subgroup.center G))
    (hψ : ψ '' {σ | σ.IsSwap} = QuotientGroup.mk' (Subgroup.center G) '' D) :
    ∃ t : ℕ → G, IsCoxeterA m t ∧ ∀ i, i < m →
      t i ∈ D ∧ QuotientGroup.mk' (Subgroup.center G) (t i) = ψ (adjSwap m i) := by
  generalize hπ : QuotientGroup.mk' (Subgroup.center G) = π at hψ ⊢
  have hex : ∀ i : ℕ, ∃ x : G, i < m → x ∈ D ∧ π x = ψ (adjSwap m i) := by
    intro i
    by_cases hi : i < m
    · have hmem : ψ (adjSwap m i) ∈ π '' D := hψ ▸ ⟨adjSwap m i, isSwap_adjSwap hi, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hmem
      exact ⟨x, fun _ => ⟨hx, hxe⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose t ht using hex
  refine ⟨t, ⟨fun i hi => Pair.mul_self hP (ht i hi).1, fun i hi => ?_, fun i j hij hj => ?_⟩, ht⟩
  · have hi' : i < m := by omega
    refine Pair.mul_mul_eq hP (ht i hi').1 (ht (i + 1) hi).1 fun hcomm => ?_
    apply adjSwap_mul_succ_ne hi
    apply ψ.injective
    rw [map_mul, map_mul, ← (ht i hi').2, ← (ht (i + 1) hi).2, ← map_mul, ← map_mul, hcomm]
  · have hi' : i < m := by omega
    have himg : π (t i) * π (t j) = π (t j) * π (t i) := by
      rw [(ht i hi').2, (ht j hj).2, ← map_mul, ← map_mul,
        (isCoxeterA_adjSwap m).comm i j hij hj]
    rcases comm_or_eq_of_map hP π (ht i hi').1 (ht j hj).1 himg with h | h
    · exact h
    · refine absurd (ψ.injective ?_) (adjSwap_ne_of_add_two_le hij hj)
      rw [← (ht i hi').2, ← (ht j hj).2, h]

theorem exists_hom_lift {G : Type} [Group G] {D : Set G} (hP : Pair G D) {m : ℕ}
    (ψ : Perm (Fin (m + 1)) ≃* (G ⧸ Subgroup.center G))
    (hψ : ψ '' {σ | σ.IsSwap} = QuotientGroup.mk' (Subgroup.center G) '' D) :
    ∃ Ψ₀ : Perm (Fin (m + 1)) →* G,
      (∀ x, QuotientGroup.mk' (Subgroup.center G) (Ψ₀ x) = ψ x) ∧
        ∀ i, i < m → Ψ₀ (adjSwap m i) ∈ D := by
  obtain ⟨t, hcox, ht⟩ := exists_coxeter_lift hP ψ hψ
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_hom_perm m t hcox
  refine ⟨Ψ₀, fun x => ?_, fun i hi => ?_⟩
  · have h := MonoidHom.eq_of_eqOn_dense (f := (QuotientGroup.mk' (Subgroup.center G)).comp Ψ₀)
      (g := ψ.toMonoidHom) (closure_adjSwap m) (by
        rintro _ ⟨i, hi, rfl⟩
        have hi' : i < m := hi
        show QuotientGroup.mk' (Subgroup.center G) (Ψ₀ (adjSwap m i)) = ψ (adjSwap m i)
        rw [hΨ₀ i hi', (ht i hi').2])
    exact DFunLike.congr_fun h x
  · rw [hΨ₀ i hi]
    exact (ht i hi).1

theorem exists_mulEquiv_of_center_quotient {G : Type} [Group G] [Finite G] {D : Set G}
    (hP : Pair G D) (hnc : ∀ x ∈ D, x ∉ Subgroup.center G) (m : ℕ)
    (ψ : Perm (Fin (m + 1)) ≃* (G ⧸ Subgroup.center G))
    (hψ : ψ '' {σ | σ.IsSwap} = QuotientGroup.mk' (Subgroup.center G) '' D) :
    ∃ Ψ : Perm (Fin (m + 1)) ≃* G, Ψ '' {σ | σ.IsSwap} = D := by
  obtain ⟨Ψ₀, hcomp, hmem⟩ := exists_hom_lift hP ψ hψ
  generalize hπ : QuotientGroup.mk' (Subgroup.center G) = π at hψ hcomp
  have hπ1 : ∀ g : G, π g = 1 ↔ g ∈ Subgroup.center G := fun g => by
    rw [← hπ]
    exact QuotientGroup.eq_one_iff g
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exfalso
      obtain ⟨d, hd⟩ := Pair.nonempty hP
      have hd' : π d ∈ ψ '' {σ | σ.IsSwap} := hψ ▸ ⟨d, hd, rfl⟩
      obtain ⟨σ, ⟨x, y, hxy, _⟩, _⟩ := hd'
      exact hxy (Fin.ext (by have := x.2; have := y.2; omega))
    · exact hm
  have hinj : Function.Injective Ψ₀ := fun x y hxy =>
    ψ.injective (by rw [← hcomp, ← hcomp, hxy])
  have hA : ∀ s : Perm (Fin (m + 1)), s.IsSwap → Ψ₀ s ∈ D := by
    rintro _ ⟨x, y, hxy, rfl⟩
    obtain ⟨a, b, hab, h0⟩ := isSwap_adjSwap hm
    have hc : IsConj (Ψ₀ (swap a b)) (Ψ₀ (swap x y)) := Ψ₀.map_isConj (isConj_swap hab hxy)
    rw [← h0] at hc
    exact Pair.mem_of_isConj hP (hmem 0 hm) hc
  have hB : ∀ x ∈ D, ∃ s : Perm (Fin (m + 1)), s.IsSwap ∧ Ψ₀ s = x := by
    intro x hx
    have hxmem : π x ∈ ψ '' {σ | σ.IsSwap} := hψ ▸ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hxmem
    refine ⟨s, hs, ?_⟩
    have hy := hA s hs
    have hπy : π (Ψ₀ s) = π x := by rw [hcomp]; exact hsx
    have hz : x * Ψ₀ s ∈ Subgroup.center G := by
      rw [← hπ1, map_mul, ← hπy, ← map_mul, Pair.mul_self hP hy, map_one]
    have hnc' : ∃ e ∈ D, x * e ≠ e * x := by
      by_contra! hall
      exact hnc x hx ((Pair.mem_center_iff hP).2 fun e he => (hall e he).symm)
    exact (Pair.eq_of_mul_mem_center hP hx hy hz hnc').symm
  have hsurj : Function.Surjective Ψ₀ := by
    have hD : D ⊆ (Ψ₀.range : Set G) := fun x hx => by
      obtain ⟨s, _, hs⟩ := hB x hx
      exact ⟨s, hs⟩
    have htop : Ψ₀.range = ⊤ := by
      rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
      exact hD
    exact MonoidHom.range_eq_top.1 htop
  refine ⟨MulEquiv.ofBijective Ψ₀ ⟨hinj, hsurj⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hA s hs
  · intro hx
    obtain ⟨s, hs, hsx⟩ := hB x hx
    exact ⟨s, hs, hsx⟩

end CFSG.RankThree.PartOne.FIS
