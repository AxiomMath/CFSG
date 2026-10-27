module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3

open Matrix CFSG.SectionRank.OddCover

variable {K : Type} [Field K]

theorem index_eq_of_card_eq {G : Type*} [Group G] [Finite G] (N : Subgroup G) {i : ℕ}
    (h : Nat.card G = Nat.card N * i) : N.index = i :=
  Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N)) ((Subgroup.card_mul_index N).trans h)

@[expose] noncomputable def diagM (M : Subgroup Kˣ) : (Fin 3 → M) →* GL (Fin 3) K :=
  (diagHom 3).comp (MonoidHom.compLeft M.subtype (Fin 3))

theorem diagM_injective (M : Subgroup Kˣ) : Function.Injective (diagM (K := K) M) := by
  intro x y h
  have h' := diagHom_injective 3 h
  funext i
  exact Subtype.ext (congrFun h' i)

@[expose] noncomputable def diagSub (M : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) :=
  (diagM M).range

theorem mem_diagSub {M : Subgroup Kˣ} {g : GL (Fin 3) K} :
    g ∈ diagSub M ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ∈ M) ∧ g = diagHom 3 d := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => (x i : Kˣ), fun i => (x i).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨fun i => ⟨d i, hd i⟩, rfl⟩

theorem diagHom_mem_diagSub {M : Subgroup Kˣ} {d : Fin 3 → Kˣ} (hd : ∀ i, d i ∈ M) :
    diagHom 3 d ∈ diagSub (K := K) M :=
  mem_diagSub.mpr ⟨d, hd, rfl⟩

theorem card_diagSub [Finite K] (M : Subgroup Kˣ) :
    Nat.card (diagSub (K := K) M) = Nat.card M ^ 3 := by
  rw [diagSub, ← Nat.card_congr (MonoidHom.ofInjective (diagM_injective M)).toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

theorem cycGL_conj_mem_diagSub (M : Subgroup Kˣ) {x : GL (Fin 3) K} (hx : x ∈ diagSub M) :
    cycGL * x * cycGL⁻¹ ∈ diagSub M := by
  obtain ⟨d, hdM, rfl⟩ := mem_diagSub.mp hx
  rw [cycGL_conj_diagHom]
  refine diagHom_mem_diagSub fun i => ?_
  fin_cases i <;> simp [hdM]

theorem cycGL_mem_normalizer_of_conj_mem {S : Subgroup (GL (Fin 3) K)}
    (hS : ∀ x ∈ S, cycGL * x * cycGL⁻¹ ∈ S) :
    (cycGL : GL (Fin 3) K) ∈ Subgroup.normalizer (S : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hS x
  · intro hx
    have h := hS _ (hS _ hx)
    rw [show cycGL * (cycGL * (cycGL * x * cycGL⁻¹) * cycGL⁻¹) * cycGL⁻¹ =
        (cycGL * cycGL * cycGL) * x * (cycGL * cycGL * cycGL)⁻¹ by group] at h
    have h3' : (cycGL : GL (Fin 3) K) * cycGL * cycGL = 1 := by
      calc (cycGL : GL (Fin 3) K) * cycGL * cycGL = cycGL ^ 3 := by rw [pow_three, mul_assoc]
        _ = 1 := cycGL_pow_three
    rw [h3', one_mul, inv_one, mul_one] at h
    exact h

theorem cycGL_mem_normalizer_diagSub (M : Subgroup Kˣ) :
    (cycGL : GL (Fin 3) K) ∈ Subgroup.normalizer (diagSub (K := K) M : Set (GL (Fin 3) K)) :=
  cycGL_mem_normalizer_of_conj_mem fun _ hx => cycGL_conj_mem_diagSub M hx

theorem zpow_cycGL_mem_diagSub (M : Subgroup Kˣ) {k : ℤ}
    (hk : (cycGL : GL (Fin 3) K) ^ k ∈ diagSub M) : (cycGL : GL (Fin 3) K) ^ k = 1 := by
  have h3 : (cycGL : GL (Fin 3) K) ^ k = cycGL ^ ((k % 3).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    have h := zpow_mod_orderOf (cycGL : GL (Fin 3) K) k
    rw [orderOf_cycGL] at h
    exact h.symm
  rw [h3] at hk ⊢
  have hlt : (k % 3).toNat < 3 := by omega
  obtain ⟨d, -, hd⟩ := mem_diagSub.mp hk
  interval_cases h : (k % 3).toNat
  · rw [pow_zero]
  · exfalso
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hd) 1) 0
    simp [coe_cycGL, cycMat, coe_diagHom] at this
  · exfalso
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hd) 2) 0
    simp [coe_cycGL, cycMat, coe_diagHom, sq, Matrix.mul_apply, Fin.sum_univ_three] at this

theorem card_diagSub_sup_cyc [Finite K] (M : Subgroup Kˣ) :
    Nat.card ↥(diagSub (K := K) M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K)) =
      3 * Nat.card M ^ 3 := by
  rw [card_sup_zpowers_of_normalizer (cycGL_mem_normalizer_diagSub M)
    (fun k hk => zpow_cycGL_mem_diagSub M hk), card_diagSub, orderOf_cycGL, mul_comm]

@[expose] def signDiag : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ d : Fin 3 → Kˣ, g = diagHom 3 d ∧ (∀ i, d i ^ 2 = 1) ∧ d 0 * d 1 * d 2 = 1}
  mul_mem' := by
    rintro _ _ ⟨d, rfl, hd, hd'⟩ ⟨e, rfl, he, he'⟩
    refine ⟨d * e, (map_mul _ _ _).symm, fun i => ?_, ?_⟩
    · rw [Pi.mul_apply, mul_pow, hd, he, one_mul]
    · simp only [Pi.mul_apply]
      calc d 0 * e 0 * (d 1 * e 1) * (d 2 * e 2) = (d 0 * d 1 * d 2) * (e 0 * e 1 * e 2) := by
            ac_rfl
        _ = 1 := by rw [hd', he', one_mul]
  one_mem' := ⟨1, (map_one _).symm, fun i => by simp, by simp⟩
  inv_mem' := by
    rintro _ ⟨d, rfl, hd, hd'⟩
    refine ⟨d⁻¹, (map_inv _ _).symm, fun i => ?_, ?_⟩
    · rw [Pi.inv_apply, inv_pow, hd, inv_one]
    · simp only [Pi.inv_apply]
      rw [← mul_inv, ← mul_inv, hd', inv_one]

theorem sq_eq_one_of_mem_signDiag {g : GL (Fin 3) K} (hg : g ∈ signDiag) : g ^ 2 = 1 := by
  obtain ⟨d, rfl, hd, -⟩ := hg
  rw [← map_pow]
  have : d ^ 2 = 1 := funext fun i => by rw [Pi.pow_apply, hd i, Pi.one_apply]
  rw [this, map_one]

theorem cycGL_conj_mem_signDiag {x : GL (Fin 3) K} (hx : x ∈ signDiag) :
    cycGL * x * cycGL⁻¹ ∈ signDiag := by
  obtain ⟨d, rfl, hd, hd'⟩ := hx
  rw [cycGL_conj_diagHom]
  refine ⟨_, rfl, fun i => ?_, ?_⟩
  · fin_cases i <;> simp [hd]
  · show d 2 * d 0 * d 1 = 1
    rw [← hd']
    ac_rfl

theorem cycGL_mem_normalizer_signDiag :
    (cycGL : GL (Fin 3) K) ∈ Subgroup.normalizer (signDiag (K := K) : Set (GL (Fin 3) K)) :=
  cycGL_mem_normalizer_of_conj_mem fun _ hx => cycGL_conj_mem_signDiag hx

theorem diagHom_conj_signDiag (e : Fin 3 → Kˣ) {y : GL (Fin 3) K} (hy : y ∈ signDiag) :
    diagHom 3 e * y * (diagHom 3 e)⁻¹ = y := by
  obtain ⟨d, rfl, -, -⟩ := hy
  rw [← map_inv, ← map_mul, ← map_mul, mul_comm e d, mul_inv_cancel_right]

theorem diagHom_mem_normalizer_signDiag (e : Fin 3 → Kˣ) :
    diagHom 3 e ∈ Subgroup.normalizer (signDiag (K := K) : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [diagHom_conj_signDiag e hx]
    exact hx
  · intro hx
    have h := diagHom_conj_signDiag e⁻¹ hx
    rw [map_inv, inv_inv] at h
    rw [show (diagHom 3 e)⁻¹ * (diagHom 3 e * x * (diagHom 3 e)⁻¹) * diagHom 3 e = x by group]
      at h
    rw [h]
    exact hx

theorem diagSub_sup_cyc_le_normalizer_signDiag (M : Subgroup Kˣ) :
    diagSub (K := K) M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K) ≤
      Subgroup.normalizer (signDiag (K := K) : Set (GL (Fin 3) K)) := by
  refine sup_le ?_ ?_
  · intro g hg
    obtain ⟨e, -, rfl⟩ := mem_diagSub.mp hg
    exact diagHom_mem_normalizer_signDiag e
  · rw [Subgroup.zpowers_le]
    exact cycGL_mem_normalizer_signDiag

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3
