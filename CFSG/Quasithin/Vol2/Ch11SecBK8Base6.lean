module

public import CFSG.Quasithin.Background.HSL3Rank
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

theorem dgHom_mulVec (g : GL (Fin 3) K) (v : I6 → K) :
    ((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ v =
      Sum.elim ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inl))
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inr)) := by
  funext i
  rcases i with i | i
  · exact congrFun (dgHom_mulVec_inl g v) i
  · exact congrFun (dgHom_mulVec_inr g v) i

theorem dgHom_injective : Function.Injective (dgHom : GL (Fin 3) K →* GL I6 K) := by
  intro g g' h
  apply Units.ext
  ext i j
  have h1 := congrArg (fun x : GL I6 K => (x : Matrix I6 I6 K) (Sum.inl i) (Sum.inl j)) h
  simpa [coe_dgHom, tensMat] using h1

theorem matAut_dgHom_injective {g g' : GL (Fin 3) K}
    (h : matAut (dgHom g) = matAut (dgHom g')) : g = g' :=
  dgHom_injective (matHom_injective h)

theorem matAut_dgHom_one : matAut (dgHom (1 : GL (Fin 3) K)) = 1 := by
  rw [map_one]
  exact map_one (matHom : GL I6 K →* MulAut (StdMod I6 K))

theorem matAut_dgHom_pow (g : GL (Fin 3) K) (k : ℕ) :
    matAut (dgHom (g ^ k)) = matAut (dgHom g) ^ k := by
  rw [map_pow]
  exact map_pow (matHom : GL I6 K →* MulAut (StdMod I6 K)) _ k

theorem card_fix_dg (A : GL (Fin 3) K) :
    Nat.card (FixW (matAut (dgHom A))) =
      Nat.card {u : Fin 3 → K // (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u} ^ 2 := by
  rw [sq, ← Nat.card_prod]
  have hfix : ∀ v : I6 → K, toAddMap (matAut (dgHom A)) v = v ↔
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inl) = v ∘ Sum.inl ∧
        (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inr) = v ∘ Sum.inr := by
    intro v
    rw [toAddMap_matAut, dgHom_mulVec]
    constructor
    · intro h
      exact ⟨by funext j; exact congrFun h (Sum.inl j), by funext j; exact congrFun h (Sum.inr j)⟩
    · rintro ⟨h1, h2⟩
      funext i
      rcases i with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
  refine Nat.card_congr
    { toFun := fun v => (⟨v.1 ∘ Sum.inl, ((hfix v.1).mp v.2).1⟩,
        ⟨v.1 ∘ Sum.inr, ((hfix v.1).mp v.2).2⟩)
      invFun := fun p => ⟨Sum.elim p.1.1 p.2.1, (hfix _).mpr ⟨p.1.2, p.2.2⟩⟩
      left_inv := fun v => Subtype.ext (by funext i; rcases i with i | i <;> rfl)
      right_inv := fun p => rfl }

@[expose] noncomputable def fixSub (A : GL (Fin 3) K) : Submodule K (Fin 3 → K) :=
  LinearMap.ker (Matrix.toLin' ((A : Matrix (Fin 3) (Fin 3) K) - 1))

theorem mem_fixSub {A : GL (Fin 3) K} {u : Fin 3 → K} :
    u ∈ fixSub A ↔ (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u := by
  rw [fixSub, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]

theorem card_fixSub [Finite K] (A : GL (Fin 3) K) :
    Nat.card {u : Fin 3 → K // (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u} =
      Nat.card K ^ Module.finrank K (fixSub A) := by
  rw [← Module.natCard_eq_pow_finrank (K := K) (V := fixSub A)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => mem_fixSub.symm)

theorem eq_one_of_fix {A : GL (Fin 3) K} (h : ∀ u, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u) :
    A = 1 := by
  apply Units.ext
  rw [Units.val_one]
  have := SL3Pair.matrix_eq_one_add (A := (A : Matrix (Fin 3) (Fin 3) K)) (N := 0)
    (fun v => by rw [h, Matrix.zero_mulVec, add_zero])
  rw [this, add_zero]

theorem finrank_fixSub_lt {A : GL (Fin 3) K} (hA : A ≠ 1) : Module.finrank K (fixSub A) < 3 := by
  have hne : fixSub A ≠ ⊤ := by
    intro h
    exact hA (eq_one_of_fix fun u => mem_fixSub.mp (h ▸ Submodule.mem_top))
  have := Submodule.finrank_lt hne
  rwa [Module.finrank_fin_fun] at this

theorem card_fix_lin_le [Finite K] {A : GL (Fin 3) K} (hA : A ≠ 1) :
    Nat.card {u : Fin 3 → K // (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u} ≤ Nat.card K ^ 2 := by
  rw [card_fixSub]
  exact Nat.pow_le_pow_right Nat.card_pos (by have := finrank_fixSub_lt hA; omega)

theorem card_fix_le_of_ne_one [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K) (h1 : x ≠ 1) :
    Nat.card (FixW x) ≤ Nat.card K ^ 4 := by
  by_contra hlt
  push Not at hlt
  have h3 : Nat.card K ^ 3 < Nat.card (FixW x) :=
    lt_of_le_of_lt (Nat.pow_le_pow_right Nat.card_pos (by norm_num)) hlt
  obtain ⟨A, rfl⟩ := exists_dg_of_lt_card_fix hx h3
  have hA : A ≠ 1 := by
    rintro rfl
    exact h1 matAut_dgHom_one
  rw [card_fix_dg] at hlt
  have h4 := Nat.pow_le_pow_left (card_fix_lin_le hA) 2
  rw [← pow_mul] at h4
  exact absurd hlt (not_lt.mpr h4)

omit [Field K] in
theorem card_I6 : Fintype.card I6 = 6 := by
  simp

theorem exists_rkIdx_fix [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (x : MulAut (W6 K)) :
    ∃ j ≤ 6 * n, Nat.card (FixW x) = 2 ^ j ∧
      rkIdx (fixV (Subgroup.zpowers x)) = 6 * n - j := by
  have hdvd := Subgroup.card_subgroup_dvd_card (fixV (Subgroup.zpowers x))
  rw [card_stdMod, card_I6, hK, ← pow_mul] at hdvd
  obtain ⟨j, hj, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨j, by omega, ?_, ?_⟩
  · rw [← card_fixV_zpowers]
    exact hcard
  · have := rkIdx_fixV_of_card hK x (j := j) (by rw [card_I6]; omega) hcard
    rw [this, card_I6, mul_comm]

theorem two_mul_le_rkIdx [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) {x : MulAut (W6 K)}
    (h : Nat.card (FixW x) ≤ Nat.card K ^ 4) : 2 * n ≤ rkIdx (fixV (Subgroup.zpowers x)) := by
  obtain ⟨j, hj, hcard, hrk⟩ := exists_rkIdx_fix hK x
  rw [hcard, hK, ← pow_mul] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  omega

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
