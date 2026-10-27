module

public import CFSG.RankThree.PartOne.K133.ResData

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree.GroupTheory CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_pullback_inner {X : Type*} [Group X] {p : ℕ} (hZ : Subgroup.center X = ⊥)
    {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E) (hle : E ≤ inner X) :
    ∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = Nat.card E ∧
      E = A.map (MulAut.conj : X →* MulAut X) := by
  set f : X →* MulAut X := MulAut.conj with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := DFunLike.congr_fun hg z
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * g = g * z * g⁻¹ * g * 1 := by rw [h1]; group
        _ = g * z := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  have hmap : (E.comap f).map f = E := Subgroup.map_comap_eq_self (by
    intro x hx
    exact hle hx)
  refine ⟨E.comap f, ?_, ?_, hmap.symm⟩
  · refine
      { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_ }
    · apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val
        (hE.is_comm.comm ⟨f (x : X), x.2⟩ ⟨f (y : X), y.2⟩)
      simpa using this
    · apply Subtype.ext
      apply hinj
      have h1 : (⟨f (x : X), x.2⟩ : ↥E) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p E) _
      have h2 := congrArg Subtype.val h1
      simpa using h2
  · have h1 : Nat.card ((E.comap f).map f) = Nat.card (E.comap f) :=
      Subgroup.card_map_of_injective hinj
    rw [hmap] at h1
    exact h1.symm

theorem noRankThree_of_inner_rank_el {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ E : Subgroup (MulAut X), IsElementaryAbelian p E → E ≤ inner X)
    (hX : ∀ A : Subgroup X, IsElementaryAbelian p A → Nat.card A ≠ p ^ 3) : NoRankThree p X := by
  rintro ⟨E, hE, hc⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA, hAc, -⟩ := exists_pullback_inner hZ hE (hOut E hE)
  exact hX A hA (hAc.trans hc)

theorem noRankThree_of_inner_rank {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ E : Subgroup (MulAut X), IsPGroup p E → E ≤ inner X)
    (hX : ∀ A : Subgroup X, IsElementaryAbelian p A → Nat.card A ≠ p ^ 3) : NoRankThree p X := by
  have : Fact p.Prime := ⟨hp⟩
  exact noRankThree_of_inner_rank_el hp hZ (fun E hE => hOut E (IsElementaryAbelian.isPGroup p E)) hX

theorem dead_of_inner_el {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ E : Subgroup (MulAut X), IsElementaryAbelian p E → E ≤ inner X)
    (hX : ∀ A : Subgroup X, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      ∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set X)) :
    Dead p X := by
  intro E hE hc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA, hAc, hEA⟩ := exists_pullback_inner hZ hE (hOut E hE)
  obtain ⟨S, hS1, hS2, hAS⟩ := hX A hA (hAc.trans hc)
  refine ⟨S, hS1, hS2, ?_⟩
  intro φ hφ s hs
  rw [hEA] at hφ
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
  have := (Subgroup.mem_normalizer_iff.1 (hAS ha) s).1 hs
  simpa [MulAut.conj_apply] using this

theorem goodRes_of_inner_noConfig_el {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ E : Subgroup (MulAut X), IsElementaryAbelian p E → E ≤ inner X)
    (hnc : ∀ C : Subgroup X, IsElementaryAbelian p C → Nat.card C = p ^ 2 →
      ∀ Kb : Subgroup X, IsSimpleGroup Kb → (∃ a b : Kb, a * b ≠ b * a) → p ∣ Nat.card Kb →
        ¬ ∀ c ∈ C, ∀ k ∈ Kb, c * k = k * c) : GoodRes p X := by
  intro Ē hE hc ⟨Cb, hCĒ, hCc, Kb, hKs, hKn, hpK, hfix⟩
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hC : IsElementaryAbelian p Cb := isElementaryAbelian_of_le hE hCĒ
  obtain ⟨C, hCe, hCcard, hCmap⟩ := exists_pullback_inner hZ hC (hCĒ.trans (hOut Ē hE))
  refine hnc C hCe (hCcard.trans hCc) Kb hKs hKn hpK fun c hc k hk => ?_
  have h1 := hfix (MulAut.conj c) (by rw [hCmap]; exact Subgroup.mem_map_of_mem _ hc) k hk
  rw [MulAut.conj_apply] at h1
  calc c * k = c * k * c⁻¹ * c := by group
    _ = k * c := by rw [h1]

theorem goodRes_of_inner_noConfig {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ E : Subgroup (MulAut X), IsPGroup p E → E ≤ inner X)
    (hnc : ∀ C : Subgroup X, IsElementaryAbelian p C → Nat.card C = p ^ 2 →
      ∀ Kb : Subgroup X, IsSimpleGroup Kb → (∃ a b : Kb, a * b ≠ b * a) → p ∣ Nat.card Kb →
        ¬ ∀ c ∈ C, ∀ k ∈ Kb, c * k = k * c) : GoodRes p X := by
  have : Fact p.Prime := ⟨hp⟩
  exact goodRes_of_inner_noConfig_el hp hZ (fun E hE => hOut E (IsElementaryAbelian.isPGroup p E)) hnc

end CFSG.RankThree.PartOne.K133
