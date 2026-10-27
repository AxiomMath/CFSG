module

public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem herm_comm_zero (hσ : ∀ c, σ (σ c) = c) {x y : Fin 6 → F} :
    herm σ x y = 0 ↔ herm σ y x = 0 :=
  ⟨herm_eq_zero_comm σ hσ, herm_eq_zero_comm σ hσ⟩

private theorem herm_sum_smul_left {n : ℕ} (t : Finset (Fin n)) (c : Fin n → F)
    (x : Fin n → Fin 6 → F) (y : Fin 6 → F) :
    herm σ (∑ i ∈ t, c i • x i) y = ∑ i ∈ t, σ (c i) * herm σ (x i) y := by
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, herm_smul_left, ih]

theorem nonDeg_top (hσ : ∀ c, σ (σ c) = c) : NonDeg σ (⊤ : Submodule F (Fin 6 → F)) := by
  intro x _ hx
  apply eq_zero_of_herm σ
  intro y
  exact (herm_comm_zero hσ).mpr (hx y Submodule.mem_top)

theorem finrank_inf_orth (hσ : ∀ c, σ (σ c) = c) {U L : Submodule F (Fin 6 → F)}
    (hU : NonDeg σ U) (hL : L ≤ U) :
    finrank F ↥(U ⊓ orth σ L) + finrank F L = finrank F U := by
  let b : Basis (Fin (finrank F L)) F L := Module.finBasis F L
  let s : Fin (finrank F L) → (Fin 6 → F) := fun i => (b i : Fin 6 → F)
  have hli : LinearIndependent F s :=
    b.linearIndependent.map' L.subtype (by simp)
  have hsL : ∀ i, s i ∈ L := fun i => (b i).2
  have hrep : ∀ w ∈ L, ∃ c : Fin (finrank F L) → F, w = ∑ i, c i • s i := by
    intro w hw
    refine ⟨fun i => b.repr ⟨w, hw⟩ i, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hkey : ∀ v : Fin 6 → F, (∀ i, herm σ (s i) v = 0) ↔ v ∈ orth σ L := by
    intro v
    rw [mem_orth]
    constructor
    · intro h w hw
      obtain ⟨c, rfl⟩ := hrep w hw
      rw [herm_sum_smul_left]
      exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
    · intro h i
      exact h (s i) (hsL i)
  obtain ⟨T, hT⟩ : ∃ T : U →ₗ[F] (Fin (finrank F L) → F),
      ∀ (y : U) (i : Fin (finrank F L)), T y i = herm σ (s i) (y : Fin 6 → F) :=
    ⟨LinearMap.pi (fun i => (hermL σ (s i)).comp U.subtype), fun y i => rfl⟩
  have hTy0 : ∀ y : U, T y = 0 ↔ (y : Fin 6 → F) ∈ orth σ L := by
    intro y
    rw [← hkey]
    constructor
    · intro h i
      have h' := congrFun h i
      rw [hT] at h'
      exact h'
    · intro h
      funext i
      rw [hT]
      exact h i
  have hK : (LinearMap.ker T).map U.subtype = U ⊓ orth σ L := by
    ext v
    rw [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (hTy0 z).mp (LinearMap.mem_ker.mp hz)⟩
    · rintro ⟨hvU, hvL⟩
      exact ⟨⟨v, hvU⟩, LinearMap.mem_ker.mpr ((hTy0 ⟨v, hvU⟩).mpr hvL), rfl⟩
  have hsurj : LinearMap.range T = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_le_ker_of_lt_top (LinearMap.range T) (lt_top_iff_ne_top.mpr hne)
    obtain ⟨c, hc⟩ : ∃ c : Fin (finrank F L) → F,
        ∀ i, c i = φ (fun j => if i = j then 1 else 0) :=
      ⟨fun i => φ (fun j => if i = j then 1 else 0), fun i => rfl⟩
    have hφeq : ∀ x : Fin (finrank F L) → F, φ x = ∑ i, x i * c i := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, smul_eq_mul]
    have hc_ne : ∃ i, c i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hφ0
      apply LinearMap.ext
      intro x
      rw [hφeq x]
      simp [hall]
    have hTsum : ∀ y : U, ∑ i, herm σ (s i) (y : Fin 6 → F) * c i = 0 := by
      intro y
      have h1 : φ (T y) = 0 := LinearMap.mem_ker.mp (hφ (LinearMap.mem_range_self T y))
      rw [hφeq] at h1
      simpa only [hT] using h1
    obtain ⟨l, hl⟩ : ∃ l : Fin 6 → F, l = ∑ i, σ (c i) • s i := ⟨_, rfl⟩
    have hlL : l ∈ L := by
      rw [hl]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsL i)
    have hperp : ∀ y ∈ U, herm σ l y = 0 := by
      intro y hy
      have h2 := hTsum ⟨y, hy⟩
      have h3 : ∀ i, σ (σ (c i)) * herm σ (s i) y = herm σ (s i) y * c i := by
        intro i
        rw [hσ, mul_comm]
      rw [hl, herm_sum_smul_left]
      simp only [h3]
      exact h2
    have hl0 : l = 0 := hU l (hL hlL) fun y hy => (herm_comm_zero hσ).mpr (hperp y hy)
    have hsum : ∑ i, σ (c i) • s i = 0 := by
      rw [← hl]
      exact hl0
    have hcs : ∀ i, σ (c i) = 0 := Fintype.linearIndependent_iff.mp hli (fun i => σ (c i)) hsum
    obtain ⟨i, hi⟩ := hc_ne
    apply hi
    calc c i = σ (σ (c i)) := (hσ _).symm
      _ = 0 := by rw [hcs i, map_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hfin : finrank F ↥((LinearMap.ker T).map U.subtype) = finrank F ↥(LinearMap.ker T) :=
    (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective U.subtype Subtype.val_injective (LinearMap.ker T))).symm
  rw [hK] at hfin
  omega

theorem finrank_orth (hσ : ∀ c, σ (σ c) = c) (S : Submodule F (Fin 6 → F)) :
    finrank F (orth σ S) + finrank F S = 6 := by
  have h := finrank_inf_orth hσ (nonDeg_top hσ) (le_top : S ≤ ⊤)
  rw [top_inf_eq, finrank_top, Module.finrank_fin_fun] at h
  exact h

theorem orth_eq_of_isTotIso (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) : orth σ W = W := by
  have hle : W ≤ orth σ W := by
    intro v hv
    rw [mem_orth]
    intro w hw
    exact hti w hw v hv
  have hd := finrank_orth hσ W
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem mem_of_orth (hσ : ∀ c, σ (σ c) = c) {W : Submodule F (Fin 6 → F)}
    (hti : IsTotIso σ W) (h3 : finrank F W = 3) {v : Fin 6 → F}
    (hv : ∀ w ∈ W, herm σ w v = 0) : v ∈ W := by
  have hmem : v ∈ orth σ W := by
    rw [mem_orth]
    exact hv
  rwa [orth_eq_of_isTotIso hσ hti h3] at hmem

end CFSG.RankThree.GF2n.Smith81.S81V
