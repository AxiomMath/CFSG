module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import Mathlib.LinearAlgebra.Matrix.Rank
public import CFSG.LinearAlgebra.IntegralRankOne
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6

open scoped Matrix

theorem finrank_range_eq_one_of_card_bounds {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (r : ℕ)
    (hV : Module.finrank K V = r) (f : V →ₗ[K] V)
    (hge : Fintype.card K ^ (r - 1) ≤ Nat.card {z : V // f z = 0})
    (hlt : Nat.card {z : V // f z = 0} < Fintype.card K ^ r) :
    Module.finrank K (LinearMap.range f) = 1 := by
  have hS : Nat.card {z : V // f z = 0} = Nat.card (LinearMap.ker f) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    rw [LinearMap.mem_ker]
  have hcard : Nat.card (LinearMap.ker f) = Nat.card K ^ Module.finrank K (LinearMap.ker f) :=
    Module.natCard_eq_pow_finrank (K := K)
  have hKn : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hkge : r - 1 ≤ Module.finrank K (LinearMap.ker f) := by
    have h := hge
    rw [hS, hcard, hKn] at h
    exact (Nat.pow_le_pow_iff_right (Fintype.one_lt_card)).mp h
  have hklt : Module.finrank K (LinearMap.ker f) < r := by
    have h := hlt
    rw [hS, hcard, hKn] at h
    exact (Nat.pow_lt_pow_iff_right (Fintype.one_lt_card)).mp h
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hV] at hrn
  omega

section Rank


theorem linearIndependent_rat_of_zmod_linearIndependent {p : ℕ} (hp : p.Prime) {k m : ℕ}
    {w : Fin k → (Fin m → ℤ)}
    (h : LinearIndependent (ZMod p) (fun i => fun a => (w i a : ZMod p))) :
    LinearIndependent ℚ (fun i => fun a => (w i a : ℚ)) := by
  rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  have hrel : ∑ j ∈ s, g j • w j = 0 := by
    funext a
    have hthis := congrFun hg a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hthis
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    exact_mod_cast (show ((∑ j ∈ s, g j * w j a : ℤ) : ℚ) = 0 by
      push_cast
      simpa using hthis)
  obtain ⟨g', hg', hgcd⟩ := Finset.extract_gcd (s := s) g ⟨i, hi⟩
  have hrel' : ∑ j ∈ s, g' j • w j = 0 := by
    have hgg : ∑ j ∈ s, g j • w j = s.gcd g • (∑ j ∈ s, g' j • w j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hg' j hj, smul_smul]
    rw [hgg] at hrel
    have hgne : s.gcd g ≠ 0 := by
      intro h0
      exact hgi (by have := (Finset.gcd_eq_zero_iff.mp h0) i hi; simpa using this)
    exact (smul_eq_zero.mp hrel).resolve_left hgne
  have hrelmod : ∑ j ∈ s, (g' j : ZMod p) • (fun a => (w j a : ZMod p)) = 0 := by
    funext a
    have hthis := congrFun (congrArg (fun v : Fin m → ℤ => fun a => (v a : ZMod p)) hrel') a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hthis ⊢
    push_cast
    simpa using hthis
  have hex : ∃ j ∈ s, (g' j : ZMod p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hdvd : ∀ j ∈ s, (p : ℤ) ∣ g' j := by
      intro j hj
      have hj0 : ((g' j : ZMod p) = 0) := hcon j hj
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj0
    have hpg : (p : ℤ) ∣ s.gcd g' := Finset.dvd_gcd hdvd
    rw [hgcd] at hpg
    have : (p : ℤ) ∣ (1 : ℤ) := by simpa using hpg
    have : p ∣ 1 := by exact_mod_cast this
    exact hp.not_dvd_one this
  obtain ⟨j, hj, hjne⟩ := hex
  exact hjne ((linearIndependent_iff'.mp h) s (fun j => (g' j : ZMod p)) hrelmod j hj)

theorem rank_map_zmod_le_rank_map_rat {p : ℕ} (hp : p.Prime) {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℤ) :
    (X.map (Int.castRingHom (ZMod p))).rank ≤ (X.map (Int.castRingHom ℚ)).rank := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Xp := X.map (Int.castRingHom (ZMod p))
  let Xq := X.map (Int.castRingHom ℚ)
  let s : Set (Fin m → ZMod p) := Set.range Xp.col
  let W : Submodule (ZMod p) (Fin m → ZMod p) := Submodule.span (ZMod p) s
  haveI hfinW : Module.Finite (ZMod p) W := by
    haveI : Module.Finite (ZMod p) (Fin m → ZMod p) := inferInstance
    exact Module.Finite.of_injective W.subtype W.subtype_injective
  let k := Module.finrank (ZMod p) W
  obtain ⟨f, hf_mem, hf_span, hf_ind⟩ :=
    @Submodule.exists_fun_fin_finrank_span_eq (ZMod p) (Fin m → ZMod p)
      (inferInstance : DivisionRing (ZMod p)) (inferInstance : AddCommGroup (Fin m → ZMod p))
      (inferInstance : Module (ZMod p) (Fin m → ZMod p)) s hfinW
  choose σ hσ using hf_mem
  let w : Fin k → (Fin m → ℤ) := fun i => X.col (σ i)
  have hfp : f = (fun i => fun a => (w i a : ZMod p)) := by
    funext i a
    have h1 := hσ i
    rw [← h1]
    simp [Xp, w, Matrix.col_apply]
  rw [hfp] at hf_ind
  have hindq : LinearIndependent ℚ (fun i => fun a => (w i a : ℚ)) :=
    linearIndependent_rat_of_zmod_linearIndependent hp hf_ind
  have hfun : (fun i => fun a => (w i a : ℚ)) = Xq.col ∘ σ := by
    funext i a
    show (X a (σ i) : ℚ) = Xq a (σ i)
    rfl
  rw [hfun] at hindq
  have hk_le : k ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range Xq.col)) := by
    have hcard := finrank_span_eq_card hindq
    have hle : Submodule.span ℚ (Set.range (Xq.col ∘ σ)) ≤
        Submodule.span ℚ (Set.range Xq.col) := by
      apply Submodule.span_mono
      rintro y ⟨i, rfl⟩
      exact ⟨σ i, rfl⟩
    calc k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (Xq.col ∘ σ))) := hcard.symm
      _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range Xq.col)) := Submodule.finrank_mono hle
  rw [Matrix.rank_eq_finrank_span_cols Xp, Matrix.rank_eq_finrank_span_cols Xq]
  exact hk_le

theorem matrix_rank_add_le {r : ℕ} {R : Type*} [Field R]
    (A B : Matrix (Fin r) (Fin r) R) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  refine (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans ?_
  rw [← Submodule.finrank_sup_add_finrank_inf_eq]
  exact Nat.le_add_right _ _

theorem matrix_rank_neg {r : ℕ} {R : Type*} [Field R]
    (A : Matrix (Fin r) (Fin r) R) : (-A).rank = A.rank := by
  rw [show (-A : Matrix (Fin r) (Fin r) R) = (-1 : R) • A by ext; simp]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors A (by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact neg_ne_zero.mpr one_ne_zero)

theorem matrix_rank_two_smul_one {r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ((2 : ZMod p) • (1 : Matrix (Fin r) (Fin r) (ZMod p))).rank = r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have hunit : IsUnit (2 : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).mpr hcop
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors (1 : Matrix (Fin r) (Fin r) (ZMod p))
    hunit.mem_nonZeroDivisors]
  show (1 : Matrix (Fin r) (Fin r) (ZMod p)).rank = r
  rw [Matrix.rank_one, Fintype.card_fin]

theorem exists_primitive_rank_one_of_involution {r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : M * M = 1)
    (hge : p ^ (r - 1) ≤ Nat.card {z : Fin r → ZMod p //
      (M.map (Int.castRingHom (ZMod p)))ᵀ *ᵥ z = (-1 : ZMod p) • z})
    (hlt : Nat.card {z : Fin r → ZMod p //
      (M.map (Int.castRingHom (ZMod p)))ᵀ *ᵥ z = (-1 : ZMod p) • z} < p ^ r) :
    ∃ u c : Fin r → ℤ, u ≠ 0 ∧ c ≠ 0 ∧ (∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1) ∧
      ∀ x, M *ᵥ x = -x + (c ⬝ᵥ x) • u := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Matrix (Fin r) (Fin r) (ZMod p) := M.map (Int.castRingHom (ZMod p))
  let T : Matrix (Fin r) (Fin r) ℤ := M + 1
  let Tp : Matrix (Fin r) (Fin r) (ZMod p) := T.map (Int.castRingHom (ZMod p))
  let MQ : Matrix (Fin r) (Fin r) ℚ := M.map (Int.castRingHom ℚ)
  let TQ : Matrix (Fin r) (Fin r) ℚ := T.map (Int.castRingHom ℚ)
  have hN : N * N = 1 := by
    change M.map (Int.castRingHom (ZMod p)) * M.map (Int.castRingHom (ZMod p)) = 1
    rw [← Matrix.map_mul, hM]
    exact Matrix.map_one (Int.castRingHom (ZMod p)) (by simp) (by simp)
  have hMQ : MQ * MQ = 1 := by
    change M.map (Int.castRingHom ℚ) * M.map (Int.castRingHom ℚ) = 1
    rw [← Matrix.map_mul, hM]
    exact Matrix.map_one (Int.castRingHom ℚ) (by simp) (by simp)
  have hTp_eq : Tp = N + 1 := by
    ext i j
    by_cases h : i = j <;> simp [Tp, T, N, Matrix.map_apply, Matrix.add_apply,
      Matrix.one_apply, h]
  have hTQ_eq : TQ = MQ + 1 := by
    ext i j
    by_cases h : i = j <;> simp [TQ, T, MQ, Matrix.map_apply, Matrix.add_apply,
      Matrix.one_apply, h]
  let L : (Fin r → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p) := (Nᵀ + 1).mulVecLin
  have hSset : Nat.card {z : Fin r → ZMod p // Nᵀ *ᵥ z = (-1 : ZMod p) • z} =
      Nat.card {z : Fin r → ZMod p // L z = 0} := by
    have h1 : Nat.card {z : Fin r → ZMod p // Nᵀ *ᵥ z = (-1 : ZMod p) • z} =
        Nat.card (LinearMap.ker L) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      change (Nᵀ *ᵥ z = (-1 : ZMod p) • z) ↔ (Nᵀ + 1) *ᵥ z = 0
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      have hneg : (-1 : ZMod p) • z = -z := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
        exact neg_one_mul (z i)
      constructor
      · intro hz
        rw [hz, hneg]
        abel
      · intro hz
        rw [← eq_neg_iff_add_eq_zero] at hz
        rwa [hneg]
    have h2 : Nat.card {z : Fin r → ZMod p // L z = 0} = Nat.card (LinearMap.ker L) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
      rw [LinearMap.mem_ker]
    rw [h1, h2]
  have hL_rank : Module.finrank (ZMod p) (LinearMap.range L) = 1 := by
    have hge' : Fintype.card (ZMod p) ^ (r - 1) ≤
        Nat.card {z : Fin r → ZMod p // L z = 0} := by
      rw [← hSset, show Fintype.card (ZMod p) = p from ZMod.card p]
      exact hge
    have hlt' : Nat.card {z : Fin r → ZMod p // L z = 0} < Fintype.card (ZMod p) ^ r := by
      rw [← hSset, show Fintype.card (ZMod p) = p from ZMod.card p]
      exact hlt
    have hV : Module.finrank (ZMod p) (Fin r → ZMod p) = r := Module.finrank_fin_fun (ZMod p)
    exact @finrank_range_eq_one_of_card_bounds (ZMod p) (Fin r → ZMod p)
      inferInstance inferInstance inferInstance
      (inferInstance : Module (ZMod p) (Fin r → ZMod p))
      (inferInstance : Module.Finite (ZMod p) (Fin r → ZMod p)) r hV L hge' hlt'
  have hTp_rank : Tp.rank = 1 := by
    rw [hTp_eq, ← Matrix.rank_transpose (N + 1)]
    have ht : (N + 1)ᵀ = Nᵀ + 1 := by rw [Matrix.transpose_add, Matrix.transpose_one]
    rw [ht]
    change Module.finrank (ZMod p) (LinearMap.range L) = 1
    exact hL_rank
  have hTp_prod : Tp * (Tp - 2) = 0 := by
    rw [hTp_eq]
    have h : (N + 1) * (N + 1 - (2 : Matrix (Fin r) (Fin r) (ZMod p))) = N * N - 1 := by
      noncomm_ring
    rw [h, hN]
    simp
  have hTp2_rank : (Tp - 2).rank = r - 1 := by
    have hlower : r ≤ Tp.rank + (Tp - 2).rank := by
      have h1 : (Tp + (2 - Tp)).rank ≤ Tp.rank + (2 - Tp).rank :=
        matrix_rank_add_le Tp (2 - Tp)
      have heq : Tp + (2 - Tp) = (2 : ZMod p) • 1 := by
        rw [show Tp + (2 - Tp) = (2 : Matrix (Fin r) (Fin r) (ZMod p)) by abel]
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.ofNat_apply, h]
      rw [heq, matrix_rank_two_smul_one hp hp2] at h1
      have h2 : (2 - Tp).rank = (Tp - 2).rank := by
        rw [show (2 : Matrix (Fin r) (Fin r) (ZMod p)) - Tp = -(Tp - 2) by abel]
        exact matrix_rank_neg (Tp - 2)
      rwa [h2] at h1
    have hupper : Tp.rank + (Tp - 2).rank ≤ r := by
      have := Matrix.rank_add_rank_le_card_of_mul_eq_zero hTp_prod (R := ZMod p)
      simpa using this
    rw [hTp_rank] at hlower hupper
    omega
  have hTQ_prod : TQ * (TQ - 2) = 0 := by
    rw [hTQ_eq]
    have h : (MQ + 1) * (MQ + 1 - (2 : Matrix (Fin r) (Fin r) ℚ)) = MQ * MQ - 1 := by
      noncomm_ring
    rw [h, hMQ]
    simp
  have hT_sub_p : (T - 2).map (Int.castRingHom (ZMod p)) = Tp - 2 := by
    ext i j
    by_cases h : i = j <;>
      simp [Tp, Matrix.map_apply, Pi.sub_apply, Matrix.ofNat_apply, Matrix.one_apply, h] <;>
      try ring
  have hT_sub_q : (T - 2).map (Int.castRingHom ℚ) = TQ - 2 := by
    ext i j
    by_cases h : i = j <;>
      simp [TQ, Matrix.map_apply, Pi.sub_apply, Matrix.ofNat_apply, Matrix.one_apply, h] <;>
      try ring
  have hTQ2_rank_ge : r - 1 ≤ (TQ - 2).rank := by
    have hr := rank_map_zmod_le_rank_map_rat hp (T - 2)
    rw [hT_sub_p, hT_sub_q] at hr
    rw [hTp2_rank] at hr
    exact hr
  have hTQ_rank_le : TQ.rank ≤ 1 := by
    have hupper : TQ.rank + (TQ - 2).rank ≤ r := by
      have := Matrix.rank_add_rank_le_card_of_mul_eq_zero hTQ_prod (R := ℚ)
      simpa using this
    omega
  have hT_ne : T ≠ 0 := by
    intro h
    have h0 : Tp = 0 := by ext i j; simp [Tp, h]
    rw [h0, Matrix.rank_zero] at hTp_rank
    exact Nat.zero_ne_one hTp_rank
  obtain ⟨u, c, hu, hc, hprim, hTuv⟩ :=
    exists_vecMulVec_of_rank_rat_le_one T hT_ne hTQ_rank_le
  refine ⟨u, c, hu, hc, hprim, fun x => ?_⟩
  have hM_eq : M = T - 1 := by
    rw [show T = M + 1 from rfl]
    abel
  rw [hM_eq, Matrix.sub_mulVec, Matrix.one_mulVec, hTuv,
    vecMulVec_mulVec_eq_dotProduct_smul]
  abel

theorem iform_mul_dotProduct_eq_two_mul {τ : Tag}
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hM : ∀ x y, iform (M *ᵥ x) (M *ᵥ y) = iform x y) {u c : Fin τ.rank → ℤ} (hu : u ≠ 0)
    (hc : c ≠ 0) (h : ∀ x, M *ᵥ x = -x + (c ⬝ᵥ x) • u) (x : Fin τ.rank → ℤ) :
    iform u u * (c ⬝ᵥ x) = 2 * iform u x := by
  have hkey : ∀ y, (c ⬝ᵥ y) * (iform u u * (c ⬝ᵥ y) - 2 * iform u y) = 0 := by
    intro y
    have hy := hM y y
    rw [h y] at hy
    rw [neg_add_eq_sub, iform_sub_left, iform_sub_right, iform_sub_right,
        iform_smul_left, iform_smul_right, iform_smul_left, iform_smul_right,
        iform_comm y u] at hy
    nlinarith [hy]
  have hadd : ∀ y z, iform u u * (c ⬝ᵥ (y + z)) - 2 * iform u (y + z) =
      (iform u u * (c ⬝ᵥ y) - 2 * iform u y) + (iform u u * (c ⬝ᵥ z) - 2 * iform u z) := by
    intro y z
    rw [dotProduct_add, iform_add_right]
    ring
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext fun j => hcon j)
  have hxsingle : c ⬝ᵥ Pi.single j 1 ≠ 0 := by
    rw [dotProduct_single]; simpa using hj
  by_cases hax : c ⬝ᵥ x = 0
  · have hP1 : iform u u * (c ⬝ᵥ Pi.single j 1) - 2 * iform u (Pi.single j 1) = 0 := by
      refine (mul_eq_zero.mp (hkey (Pi.single j 1))).resolve_left hxsingle
    have hP2 : iform u u * (c ⬝ᵥ (x + Pi.single j 1)) - 2 * iform u (x + Pi.single j 1) = 0 := by
      refine (mul_eq_zero.mp (hkey (x + Pi.single j 1))).resolve_left ?_
      rw [dotProduct_add, hax, zero_add]; exact hxsingle
    have h3 := hadd x (Pi.single j 1)
    rw [hP2, hP1, add_zero] at h3
    linarith [h3.symm]
  · have hPx : iform u u * (c ⬝ᵥ x) - 2 * iform u x = 0 :=
      (mul_eq_zero.mp (hkey x)).resolve_left hax
    linarith [hPx]

end Rank

end ExcFramesHalf

end CFSG.StandardType
