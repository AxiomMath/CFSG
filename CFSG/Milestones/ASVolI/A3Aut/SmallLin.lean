module

public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.Milestones.ASVolI.A2OddAut

public section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped Pointwise

section SmallLin

variable {K : Type} [Field K] [Finite K]

theorem burnsideAut_det_eq_one_of_mul_eq_one (hK : Nat.card K = 2) {m : ℕ}
    {M N : Matrix (Fin m) (Fin m) K} (h : M * N = 1) : M.det = 1 := by
  have h1 : M.det * N.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact (eq_zero_or_eq_one_of_card_two hK _).resolve_left (left_ne_zero_of_mul_eq_one h1)

@[expose] noncomputable def burnsideAut_blkHom (hK : Nat.card K = 2) {n : ℕ}
    (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) (h : a + m ≤ n)
    (hL : BlockLeft H a m) (hR : BlockRight H a m) :
    ↥H →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨blkMon H a m h hL hR g, burnsideAut_det_eq_one_of_mul_eq_one hK
    (N := blkMon H a m h hL hR g⁻¹) (by rw [← map_mul, mul_inv_cancel, map_one])⟩
  map_one' := Subtype.ext (map_one (blkMon H a m h hL hR))
  map_mul' g g' := Subtype.ext (map_mul (blkMon H a m h hL hR) g g')

theorem burnsideAut_blkHom_coe (hK : Nat.card K = 2) {n : ℕ}
    (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) (h : a + m ≤ n)
    (hL : BlockLeft H a m) (hR : BlockRight H a m) (g : ↥H) :
    ((burnsideAut_blkHom hK H a m h hL hR g : SpecialLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K) =
      blkAt a m h ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem burnsideAut_blkAt_entry {n a m : ℕ} (h : a + m ≤ n) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin m) (k l : Fin n) (hk : (k : ℕ) = a + i) (hl : (l : ℕ) = a + j) :
    blkAt a m h A i j = A k l := by
  rw [blkAt_apply]
  congr 1
  · exact Fin.ext hk.symm
  · exact Fin.ext hl.symm

@[expose] def burnsideAut_liftMat {n : ℕ} (a m : ℕ) (X : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if hi : a ≤ (i : ℕ) ∧ (i : ℕ) < a + m then
      if hj : a ≤ (j : ℕ) ∧ (j : ℕ) < a + m then
        X ⟨(i : ℕ) - a, by omega⟩ ⟨(j : ℕ) - a, by omega⟩
      else 0
    else if i = j then 1 else 0

theorem burnsideAut_blkAt_liftMat {n : ℕ} (a m : ℕ) (h : a + m ≤ n)
    (X : Matrix (Fin m) (Fin m) K) : blkAt a m h (burnsideAut_liftMat (n := n) a m X) = X := by
  ext i j
  rw [blkAt_apply]
  simp only [burnsideAut_liftMat, Matrix.of_apply]
  rw [dif_pos ⟨Nat.le_add_right a i, by have := i.isLt; omega⟩,
    dif_pos ⟨Nat.le_add_right a j, by have := j.isLt; omega⟩]
  congr 1
  · exact Fin.ext (by simp)
  · exact Fin.ext (by simp)

theorem burnsideAut_liftMat_unitri {n : ℕ} (a m : ℕ) {X : Matrix (Fin m) (Fin m) K}
    (hX1 : ∀ i j : Fin m, j < i → X i j = 0) (hX2 : ∀ i : Fin m, X i i = 1) :
    (∀ i j : Fin n, j < i → burnsideAut_liftMat a m X i j = 0) ∧
      ∀ i : Fin n, burnsideAut_liftMat a m X i i = 1 := by
  constructor
  · intro i j hij
    have hij' : (j : ℕ) < i := hij
    simp only [burnsideAut_liftMat, Matrix.of_apply]
    split_ifs with hi hj he
    · apply hX1
      show (j : ℕ) - a < (i : ℕ) - a
      omega
    · rfl
    · exact absurd he (fun e => by rw [e] at hij'; exact lt_irrefl _ hij')
    · rfl
  · intro i
    simp only [burnsideAut_liftMat, Matrix.of_apply]
    split_ifs
    · exact hX2 _
    · rfl

theorem burnsideAut_det_liftMat {n : ℕ} (a m : ℕ) {X : Matrix (Fin m) (Fin m) K}
    (hX1 : ∀ i j : Fin m, j < i → X i j = 0) (hX2 : ∀ i : Fin m, X i i = 1) :
    (burnsideAut_liftMat (n := n) a m X).det = 1 := by
  obtain ⟨h1, h2⟩ := burnsideAut_liftMat_unitri (n := n) a m hX1 hX2
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => h1 i j hij)]
  exact Finset.prod_eq_one fun i _ => h2 i

@[expose] noncomputable def burnsideAut_liftU {n : ℕ} (a m : ℕ) (X : ↥(unitriangular m K)) :
    SpecialLinearGroup (Fin n) K :=
  ⟨burnsideAut_liftMat a m ((X : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K),
    burnsideAut_det_liftMat a m X.2.1 X.2.2⟩

theorem burnsideAut_liftU_mem {n : ℕ} (a m : ℕ) (X : ↥(unitriangular m K)) :
    burnsideAut_liftU (n := n) a m X ∈ unitriangular n K :=
  burnsideAut_liftMat_unitri a m X.2.1 X.2.2

theorem burnsideAut_unitriangular_of_blocks {n d : ℕ} (hdn : d ≤ n)
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ stabilizer (flagSpace n K d))
    (h1 : blkAt 0 d (by omega) (g : Matrix (Fin n) (Fin n) K) = 1)
    (h2 : blkAt d (n - d) (by omega) (g : Matrix (Fin n) (Fin n) K) = 1) :
    g ∈ unitriangular n K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    by_cases hi : (i : ℕ) < d
    · have e := congrFun (congrFun h1 ⟨i, hi⟩) ⟨j, by omega⟩
      rw [burnsideAut_blkAt_entry _ _ _ _ i j (by simp) (by simp),
        Matrix.one_apply_ne (fun e' => by
          have := congrArg Fin.val e'
          simp at this
          omega)] at e
      exact e
    · by_cases hj : (j : ℕ) < d
      · exact stabilizer_entries hg hj (by omega)
      · have e := congrFun (congrFun h2 ⟨(i : ℕ) - d, by omega⟩) ⟨(j : ℕ) - d, by omega⟩
        rw [burnsideAut_blkAt_entry _ _ _ _ i j (by simp; omega) (by simp; omega),
          Matrix.one_apply_ne (fun e' => by
            have := congrArg Fin.val e'
            simp at this
            omega)] at e
        exact e
  · by_cases hi : (i : ℕ) < d
    · have e := congrFun (congrFun h1 ⟨i, hi⟩) ⟨i, hi⟩
      rw [burnsideAut_blkAt_entry _ _ _ _ i i (by simp) (by simp), Matrix.one_apply_eq] at e
      exact e
    · have e := congrFun (congrFun h2 ⟨(i : ℕ) - d, by omega⟩) ⟨(i : ℕ) - d, by omega⟩
      rw [burnsideAut_blkAt_entry _ _ _ _ i i (by simp; omega) (by simp; omega),
        Matrix.one_apply_eq] at e
      exact e

theorem burnsideAut_image_three {n m : ℕ} {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (f : ↥H →* SpecialLinearGroup (Fin m) K) {S B : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hBH : B ≤ H) (hSH : S ≤ H) (hS : IsPGroup 2 ↥S) (hB : Odd (Nat.card ↥B))
    (hBc : IsMulCommutative ↥B ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥B)
    (hperm : (B : Set (SpecialLinearGroup (Fin n) K)) * (S : Set (SpecialLinearGroup (Fin n) K)) =
      (S : Set (SpecialLinearGroup (Fin n) K)) * (B : Set (SpecialLinearGroup (Fin n) K)))
    (hUm : unitriangular m K ≤ (S.subgroupOf H).map f)
    (ih : ∀ S' B' : Subgroup (SpecialLinearGroup (Fin m) K), IsPGroup 2 ↥S' →
      unitriangular m K ≤ S' → Odd (Nat.card ↥B') →
      (IsMulCommutative ↥B' ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥B') →
      (B' : Set (SpecialLinearGroup (Fin m) K)) * (S' : Set (SpecialLinearGroup (Fin m) K)) =
        (S' : Set (SpecialLinearGroup (Fin m) K)) * (B' : Set (SpecialLinearGroup (Fin m) K)) →
      IsPGroup 3 ↥B') :
    IsPGroup 3 ↥((B.subgroupOf H).map f) := by
  have eB : ↥(B.subgroupOf H) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBH
  have eS : ↥(S.subgroupOf H) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSH
  refine ih _ _ ((hS.of_equiv eS.symm).map f) hUm ?_ ?_ ?_
  · refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd (B.subgroupOf H) f)
    rw [Nat.card_congr eB.toEquiv]
    exact hB
  · rcases hBc with hab | ⟨r, hr, hBr⟩
    · left
      haveI : IsMulCommutative ↥(B.subgroupOf H) := ⟨⟨fun a b => by
        apply eB.injective
        rw [map_mul, map_mul]
        exact hab.is_comm.comm _ _⟩⟩
      infer_instance
    · right
      exact ⟨r, hr, (hBr.of_equiv eB.symm).map f⟩
  · have h1 := burnsideA315x_subgroupOf_permute (K := S) hBH hperm
    rw [inf_eq_left.2 hSH] at h1
    exact burnsideA315x_map_permute f h1

theorem burnsideAut_sl_three (hK : Nat.card K = 2) :
    ∀ (n : ℕ), 1 ≤ n → ∀ S B : Subgroup (SpecialLinearGroup (Fin n) K), IsPGroup 2 ↥S →
      unitriangular n K ≤ S → Odd (Nat.card ↥B) →
      (IsMulCommutative ↥B ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥B) →
      (B : Set (SpecialLinearGroup (Fin n) K)) * (S : Set (SpecialLinearGroup (Fin n) K)) =
        (S : Set (SpecialLinearGroup (Fin n) K)) * (B : Set (SpecialLinearGroup (Fin n) K)) →
      IsPGroup 3 ↥B := by
  haveI : CharP K 2 := burnsideA26_charP_two (n := 1) (by rw [hK]; rfl)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn S B hS hUS hB hBc hperm
  by_cases hn2 : n ≤ 2
  ·
    have hcard : Nat.card (SpecialLinearGroup (Fin n) K) ∣ 3 * 2 := by
      rw [card_SL_eq hn, hK]
      interval_cases n <;> decide
    have h3 : Nat.card ↥B ∣ 3 :=
      (Nat.coprime_two_right.2 hB).dvd_of_dvd_mul_right
        ((Subgroup.card_subgroup_dvd_card B).trans hcard)
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; rfl)
  · have hn3 : 3 ≤ n := by omega
    by_contra h3
    have hU : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular n K) ⊤ := by
      obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) hn
      rw [← hP]
      exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
    have hSsyl : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
      refine ⟨le_top, hS, fun h2 => hU.2.2 ?_⟩
      change 2 ∣ (unitriangular n K).relIndex ⊤
      change 2 ∣ S.relIndex ⊤ at h2
      rw [Subgroup.relIndex_top_right] at h2 ⊢
      exact h2.trans (Subgroup.index_dvd_of_le hUS)
    have hc : burnsideA315x_Config (SpecialLinearGroup (Fin n) K) S B :=
      ⟨hSsyl, hB, h3, hBc, hperm⟩
    have hnil : Group.IsNilpotent ↥B := by
      rcases hBc with hab | ⟨r, hr, hBr⟩
      · haveI := hab
        infer_instance
      · haveI : Fact r.Prime := ⟨hr⟩
        exact hBr.isNilpotent
    have hsolv : Group.IsSolvable ↥(B ⊔ S) := hc.sup_solvable hnil
    have hne : B ⊔ S ≠ ⊤ := by
      intro htop
      haveI := sl_isSimple_of_card_two hK hn3
      obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two hK hn3
      rw [htop] at hsolv
      haveI := hsolv
      have : Group.IsSolvable (SpecialLinearGroup (Fin n) K) :=
        solvable_of_surjective (f := (Subgroup.topEquiv :
          ↥(⊤ : Subgroup (SpecialLinearGroup (Fin n) K)) ≃* _).toMonoidHom)
          Subgroup.topEquiv.surjective
      exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 this) a b)
    have hBor : upperTriangular n K ≤ B ⊔ S :=
      (upperTriangular_le_unitriangular hK).trans (hUS.trans le_sup_right)
    obtain ⟨hAI, -⟩ := borel_overgroups (B ⊔ S) hBor
    obtain ⟨d, hdI⟩ : (borelOvergroupCuts (B ⊔ S)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      apply hne
      rw [hAI, hemp, flagStabilizer_empty]
    obtain ⟨hd1, hdn, -⟩ := id hdI
    have hHle : B ⊔ S ≤ stabilizer (flagSpace n K d) := fun g hg =>
      mem_flagStabilizer.mp (hAI.le hg) d hdI
    set H := stabilizer (flagSpace n K d) with hHdef
    have hBH : B ≤ H := le_sup_left.trans hHle
    have hSH : S ≤ H := le_sup_right.trans hHle
    have hUH : unitriangular n K ≤ H := hUS.trans hSH
    have hLA : BlockLeft H 0 d := blockLeft_zero H d
    have hRA : BlockRight H 0 d := fun g hg k c hk _ hc =>
      stabilizer_entries (k := k) (l := c) hg (by omega) (by omega)
    have hLD : BlockLeft H d (n - d) := fun g hg r l hr _ hl => stabilizer_entries hg hl hr
    have hRD : BlockRight H d (n - d) := blockRight_top H (by omega)
    set fA := burnsideAut_blkHom hK H 0 d (by omega) hLA hRA with hfA
    set fD := burnsideAut_blkHom hK H d (n - d) (by omega) hLD hRD with hfD
    have hUA : unitriangular d K ≤ (S.subgroupOf H).map fA := by
      intro X hX
      refine ⟨⟨burnsideAut_liftU 0 d ⟨X, hX⟩, hUH (burnsideAut_liftU_mem 0 d ⟨X, hX⟩)⟩,
        Subgroup.mem_subgroupOf.2 (hUS (burnsideAut_liftU_mem 0 d ⟨X, hX⟩)), ?_⟩
      apply Subtype.ext
      rw [hfA, burnsideAut_blkHom_coe]
      exact burnsideAut_blkAt_liftMat 0 d (by omega) _
    have hUD : unitriangular (n - d) K ≤ (S.subgroupOf H).map fD := by
      intro X hX
      refine ⟨⟨burnsideAut_liftU d (n - d) ⟨X, hX⟩,
        hUH (burnsideAut_liftU_mem d (n - d) ⟨X, hX⟩)⟩,
        Subgroup.mem_subgroupOf.2 (hUS (burnsideAut_liftU_mem d (n - d) ⟨X, hX⟩)), ?_⟩
      apply Subtype.ext
      rw [hfD, burnsideAut_blkHom_coe]
      exact burnsideAut_blkAt_liftMat d (n - d) (by omega) _
    have h3A : IsPGroup 3 ↥((B.subgroupOf H).map fA) :=
      burnsideAut_image_three fA hBH hSH hS hB hBc hperm hUA (ih d hdn hd1)
    have h3D : IsPGroup 3 ↥((B.subgroupOf H).map fD) :=
      burnsideAut_image_three fD hBH hSH hS hB hBc hperm hUD (ih (n - d) (by omega) (by omega))
    apply h3
    intro b
    set x : ↥H := ⟨(b : SpecialLinearGroup (Fin n) K), hBH b.2⟩ with hx
    have hxB : x ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 b.2
    obtain ⟨i, hi⟩ := h3A ⟨fA x, x, hxB, rfl⟩
    obtain ⟨j, hj⟩ := h3D ⟨fD x, x, hxB, rfl⟩
    have hi' : fA x ^ 3 ^ i = 1 := by
      have := congrArg Subtype.val hi
      simpa using this
    have hj' : fD x ^ 3 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hA1 : fA (x ^ 3 ^ (i + j)) = 1 := by
      rw [map_pow, pow_add, pow_mul, hi', one_pow]
    have hD1 : fD (x ^ 3 ^ (i + j)) = 1 := by
      rw [map_pow, pow_add, mul_comm, pow_mul, hj', one_pow]
    have hUy : ((x ^ 3 ^ (i + j) : ↥H) : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K := by
      refine burnsideAut_unitriangular_of_blocks hdn.le (x ^ 3 ^ (i + j)).2 ?_ ?_
      · have e1 : ((fA (x ^ 3 ^ (i + j)) : SpecialLinearGroup (Fin d) K) :
            Matrix (Fin d) (Fin d) K) = blkAt 0 d (by omega)
              (((x ^ 3 ^ (i + j) : ↥H) : SpecialLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K) := rfl
        rw [hA1] at e1
        rw [← e1]
        rfl
      · have e1 : ((fD (x ^ 3 ^ (i + j)) : SpecialLinearGroup (Fin (n - d)) K) :
            Matrix (Fin (n - d)) (Fin (n - d)) K) = blkAt d (n - d) (by omega)
              (((x ^ 3 ^ (i + j) : ↥H) : SpecialLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K) := rfl
        rw [hD1] at e1
        rw [← e1]
        rfl
    obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := K) hn ⟨_, hUy⟩
    refine ⟨i + j, ?_⟩
    have hk' : (b ^ 3 ^ (i + j)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa [hx] using this
    have hord : orderOf (b ^ 3 ^ (i + j)) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.2 hB).pow_left k)
        (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_natCard _)
    exact orderOf_eq_one_iff.1 hord

end SmallLin

theorem burnsideAut_a315_Ln_two {n : ℕ} (hn : 3 ≤ n) (G : Type) [Group G]
    (L T B : Subgroup G) (h : CFSG.Quasithin.A315Hyp L T B)
    (hL : CFSG.Quasithin.IsPSL n 2 1 ↥L) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hL
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : CharP K 2 := burnsideA26_charP_two (n := 1) (by rw [hK2]; rfl)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : ∀ α : MulAut ↥L, Odd (orderOf α) → ∃ l : ↥L, α = MulAut.conj l := by
    intro α hα
    obtain ⟨l, hl⟩ := burnsideA26_l45 hn hK2 e α hα
    exact ⟨l, hl.symm⟩
  obtain ⟨-, hc⟩ := burnsideA315x_config_of_hyp h hOut
  let e' : ↥L ≃* SpecialLinearGroup (Fin n) K := e.trans (slEquivStatedProj hK2 n).symm
  have hc' := hc.map e'
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) (by omega)
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hc'.sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) K) (h1.toSylow h2) P
  have hc'' := hc'.map (MulAut.conj g)
  have hUS : unitriangular n K ≤ ((((T ⊓ L).subgroupOf L).map e'.toMonoidHom).map
      (MulAut.conj g).toMonoidHom) := by
    intro x hx
    rw [← hP, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  exact hc''.not3 (burnsideAut_sl_three hK2 n (by omega) _ _ hc''.sylow.2.1 hUS hc''.odd
    hc''.cases hc''.perm)

theorem burnsideAut_a315_L3two : ∀ (G : Type) [Group G] (L T B : Subgroup G),
    CFSG.Quasithin.A315Hyp L T B → CFSG.Quasithin.IsPSL 3 2 1 ↥L → False :=
  fun G _ L T B h hL => burnsideAut_a315_Ln_two (le_refl 3) G L T B h hL

theorem burnsideAut_a315_L4two : ∀ (G : Type) [Group G] (L T B : Subgroup G),
    CFSG.Quasithin.A315Hyp L T B → CFSG.Quasithin.IsPSL 4 2 1 ↥L → False :=
  fun G _ L T B h hL => burnsideAut_a315_Ln_two (by norm_num) G L T B h hL

theorem burnsideAut_a315_L5two : ∀ (G : Type) [Group G] (L T B : Subgroup G),
    CFSG.Quasithin.A315Hyp L T B → CFSG.Quasithin.IsPSL 5 2 1 ↥L → False :=
  fun G _ L T B h hL => burnsideAut_a315_Ln_two (by norm_num) G L T B h hL

end CFSG.ASVolI
