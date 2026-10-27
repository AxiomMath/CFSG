module

public import CFSG.Quasithin.Background.SmithB45U3Curtis
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred

public section

namespace CFSG.Quasithin.B45U3

open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {s : ℕ}
variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

@[expose] noncomputable def TJ (a b : Fin s → Bool) :
    suJ K s →* Matrix (TIdx s a b) (TIdx s a b) k :=
  (tensorRep (F := K) k a b).comp (suJ K s).subtype

theorem TJ_apply (a b : Fin s → Bool) (g : suJ K s) :
    TJ k a b g = tensorRep (F := K) k a b (g : SL(3, K)) := rfl

omit [Finite K] [CharP K 2] in
theorem prod_frK_eq' (P : K) :
    ∏ i : Fin s, frK k (i : ℕ) P = algebraMap K k (P ^ (2 ^ s - 1)) := by
  simp only [frK_apply, map_pow]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) s,
    Nat.geomSum_eq (le_refl 2)]
  simp

theorem LJ_corner_eq_zero {g : suJ K s} {x y : K}
    (hxy : y + y ^ 2 ^ s = x * x ^ 2 ^ s) (he : (g : SL(3, K)) = u3 x y (x ^ 2 ^ s))
    (hy : y = 0) : g = 1 := by
  subst hy
  have ha : x * x ^ 2 ^ s = 0 := by rw [← hxy]; simp
  have hx0 : x = 0 := by
    rcases mul_eq_zero.mp ha with h | h
    · exact h
    · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h
  subst hx0
  refine Subtype.ext ?_
  rw [he, zero_pow (pow_ne_zero _ two_ne_zero), u3_zero]
  rfl

@[expose] def w7J (s : ℕ) : TIdx s (ones s) (ones s) :=
  fun _ => (⟨7, by decide⟩ : Fin (locDim true true))

theorem norm_coeff_fullJ (hK : Nat.card K = (2 ^ s) ^ 2) [Fintype (LJ K s)] :
    ∑ g : LJ K s, ((TJ k (ones s) (ones s) (g : suJ K s)).mulVec
      (hw k (ones s) (ones s))) (w7J s) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = (2 ^ s) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs := one_le_s hK
  have hq2 : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hterm : ∀ g : LJ K s, ((TJ k (ones s) (ones s) (g : suJ K s)).mulVec
      (hw k (ones s) (ones s))) (w7J s) = if g = 1 then 0 else 1 := by
    intro g
    obtain ⟨x, y, hxy, hg⟩ := exists_of_mem_LJ g.2
    rw [TJ_apply, hg, tensorRep_u3_orbit]
    have hloc : ∀ i : Fin s, locCoord (ones s i) (ones s i) (w7J s i) x y (x ^ 2 ^ s) =
        y ^ (2 ^ s + 1) := by
      intro i
      show y ^ 2 + x * y * x ^ 2 ^ s = y ^ (2 ^ s + 1)
      linear_combination (-y) * hxy + y ^ 2 * h2
    simp_rw [hloc]
    rw [prod_frK_eq', ← pow_mul]
    by_cases hg1 : g = 1
    · have hy : y = 0 := by
        have h1 : ((g : suJ K s) : SL(3, K)) = 1 := by rw [hg1]; rfl
        rw [hg, ← u3_zero] at h1
        exact (u3_inj h1).2.1
      rw [ite_eq_left hg1, hy, zero_pow (Nat.mul_ne_zero (by omega) (by omega)), map_zero]
    · have hy : y ≠ 0 := fun hy => hg1 (Subtype.ext (LJ_corner_eq_zero hxy hg hy))
      rw [ite_eq_right hg1]
      have he : (2 ^ s + 1) * (2 ^ s - 1) = Fintype.card K - 1 := by
        rw [hcardK]
        zify [Nat.one_le_two_pow, Nat.one_le_pow 2 (2 ^ s) (by positivity)]
        ring
      rw [he, FiniteField.pow_card_sub_one_eq_one y hy, map_one]
  have hsum : ∑ g : LJ K s, (if g = 1 then (0 : k) else 1) =
      ((Fintype.card (LJ K s) - 1 : ℕ) : k) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 1), ite_eq_left rfl, add_zero,
      Finset.sum_congr rfl (fun g hg => ite_eq_right (Finset.ne_of_mem_erase hg)),
      Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul, mul_one]
  simp_rw [hterm]
  rw [hsum, Fintype.card_eq_nat_card, card_LJ hK]
  have h1 : 1 ≤ (2 ^ s) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero,
    zero_pow (by omega), zero_pow (by norm_num), Nat.cast_one, zero_sub, CharTwo.neg_eq]

theorem fullOrbit_basisJ (hK : Nat.card K = (2 ^ s) ^ 2) [Fintype (LJ K s)] :
    ∃ b : Module.Basis (LJ K s) k (TIdx s (ones s) (ones s) → k), ∀ u : LJ K s,
      b u = (TJ k (ones s) (ones s) (u : suJ K s)).mulVec (hw k (ones s) (ones s)) := by
  classical
  let ρ : LJ K s →* ((TIdx s (ones s) (ones s) → k) →ₗ[k] (TIdx s (ones s) (ones s) → k)) :=
    (matRep (TJ (K := K) k (ones s) (ones s))).comp (LJ K s).subtype
  have hP : IsPGroup 2 (LJ K s) := isPGroup_LJ hK
  have hv : ∑ g : LJ K s, ρ g (hw k (ones s) (ones s)) ≠ 0 := by
    intro h
    have h2 := norm_coeff_fullJ k hK
    have h3 : ∑ g : LJ K s, ((TJ k (ones s) (ones s) (g : suJ K s)).mulVec
        (hw k (ones s) (ones s))) (w7J s) = 0 := by
      have := congrFun h (w7J s)
      rw [Finset.sum_apply] at this
      exact this
    exact zero_ne_one (h3.symm.trans h2)
  have hdim : Module.finrank k (TIdx s (ones s) (ones s) → k) = Fintype.card (LJ K s) := by
    rw [Module.finrank_fintype_fun_eq_card, card_TIdx_ones, Fintype.card_eq_nat_card,
      card_LJ hK, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨b, hb, -, -⟩ := orbit_regular_of_norm_ne_zero k Nat.prime_two hP ρ
    (hw k (ones s) (ones s)) hv hdim
  exact ⟨b, fun u => by rw [hb]; rfl⟩

theorem fullOrbit_spanJ (hK : Nat.card K = (2 ^ s) ^ 2) :
    Submodule.span k (Set.range fun u : LJ K s =>
      matRep (TJ k (ones s) (ones s)) (u : suJ K s) (hw k (ones s) (ones s))) = ⊤ := by
  have := Fintype.ofFinite (LJ K s)
  obtain ⟨b, hb⟩ := fullOrbit_basisJ k hK
  have : (fun u : LJ K s => matRep (TJ (K := K) k (ones s) (ones s)) (u : suJ K s)
      (hw k (ones s) (ones s))) = ⇑b := funext fun u => (hb u).symm
  rw [this]
  exact b.span_eq

theorem fullCoords_liJ (hK : Nat.card K = (2 ^ s) ^ 2) :
    LinearIndependent k (fun x : TIdx s (ones s) (ones s) => fun u : LJ K s =>
      ((TJ k (ones s) (ones s) (u : suJ K s)).mulVec (hw k (ones s) (ones s))) x) :=
  coords_linearIndependent_of_span (TJ k (ones s) (ones s)) (LJ K s)
    (hw k (ones s) (ones s)) (fullOrbit_spanJ k hK)

theorem coord_eq_embJ (a b : Fin s → Bool) (x' : TIdx s a b) (u : LJ K s) :
    ((TJ k a b (u : suJ K s)).mulVec (hw k a b)) x' =
      ((TJ k (ones s) (ones s) (u : suJ K s)).mulVec (hw k (ones s) (ones s)))
        (embIdx a b x') :=
  coord_eq_emb k a b x' ⟨((u : suJ K s) : SL(3, K)), u.2⟩

theorem mixed_spanJ (hK : Nat.card K = (2 ^ s) ^ 2) (a b : Fin s → Bool) :
    Submodule.span k (Set.range fun u : LJ K s =>
      matRep (TJ k a b) (u : suJ K s) (hw k a b)) = ⊤ := by
  refine span_orbit_eq_top_of_coords _ _ _ ?_
  have h := (fullCoords_liJ k hK).comp (embIdx a b) (embIdx_injective a b)
  convert h using 1
  funext x' u
  exact coord_eq_embJ k a b x' u

theorem dualMat_TJ (a b : Fin s → Bool) :
    dualMat (TJ (K := K) k a b) = (dualMat (tensorRep (F := K) k a b)).comp (suJ K s).subtype :=
  MonoidHom.ext fun _ => rfl

theorem mixed_hlineJ (hK : Nat.card K = (2 ^ s) ^ 2) (a b : Fin s → Bool) :
    ∃ n ∈ fixedSub (matRep (TJ (K := K) k a b)) (LJ K s),
      ∀ w ∈ fixedSub (matRep (TJ (K := K) k a b)) (LJ K s), ∃ c : k, w = c • n := by
  have h := (tensorRep_dual_iso (F := K) k a b).comp (suJ K s).subtype
  rw [← dualMat_TJ] at h
  exact hline_of_cocyclic (TJ k a b) (LJ K s) _
    (h.span_orbit_top (LJ K s) (hw k b a) (mixed_spanJ k hK b a))

theorem TJ_fixed_irreducible (hK : Nat.card K = (2 ^ s) ^ 2) (a b : Fin s → Bool) :
    fixedSub (matRep (TJ (K := K) k a b)) (UJ K s) = Submodule.span k {hw k a b} ∧
      (matRep (TJ (K := K) k a b)).IsIrreducible := by
  refine fixedSub_eq_span_and_irreducible k Nat.prime_two (matRep (TJ k a b)) (LJ K s) (UJ K s)
    (isPGroup_UJ hK) wJs (fun u hu => wJs_conj_LJ hu) (hw k a b) (hw_ne_zero k a b) ?_
    (mixed_spanJ k hK a b) (mixed_hlineJ k hK a b)
  intro h hh
  obtain ⟨x, y, z, hxyz⟩ := mem_upperUni.mp (mem_UJ.mp hh)
  rw [matRep_apply, TJ_apply, hxyz]
  exact tensorRep_up3_fixed k a b x y z

theorem TJ_hJ_hw (hK : Nat.card K = (2 ^ s) ^ 2) (a b : Fin s → Bool) (r : Kˣ) :
    (TJ k a b (hJ hK r)).mulVec (hw k a b) =
      algebraMap K k (r : K) ^ (mBits a + 2 ^ s * mBits b) • hw k a b := by
  rw [TJ_apply, coe_hJ, tensorRep_dT_hw]
  congr 1
  rw [Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_add]
  congr 1
  have hq : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  zify [hq]
  ring

end CFSG.Quasithin.B45U3
