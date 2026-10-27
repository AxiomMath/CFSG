module

public import CFSG.Quasithin.Background.HSL3Rank

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

theorem le_rkIdx_of_card_mul_le {V : Type*} [Group V] [Finite V] {m : ℕ}
    (hV : Nat.card V = 2 ^ m) (U : Subgroup V) {k : ℕ} (h : Nat.card U * 2 ^ k ≤ 2 ^ m) :
    k ≤ rkIdx U := by
  obtain ⟨j, -, hUj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hV ▸ U.card_subgroup_dvd_card)
  rw [hUj, ← pow_add] at h
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have h2 := le_rkIdx_of_card_le hV (le_of_eq hUj)
  omega

theorem card_eq_two_pow_sub_rkIdx {V : Type*} [Group V] [Finite V] {m : ℕ}
    (hV : Nat.card V = 2 ^ m) (U : Subgroup V) : Nat.card U = 2 ^ (m - rkIdx U) := by
  obtain ⟨j, hjm, hUj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hV ▸ U.card_subgroup_dvd_card)
  have h1 := U.card_mul_index
  rw [hUj, hV] at h1
  have h2 : U.index = 2 ^ (m - j) := by
    have h3 : 2 ^ m = 2 ^ j * 2 ^ (m - j) := by rw [← pow_add]; congr 1; omega
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have h4 : rkIdx U = m - j := by
    unfold rkIdx
    rw [h2, padicValNat.prime_pow]
  rw [hUj, h4]
  congr 1
  omega

theorem card_le_of_le_rkIdx {V : Type*} [Group V] [Finite V] {m : ℕ}
    (hV : Nat.card V = 2 ^ m) (U : Subgroup V) {k : ℕ} (h : k ≤ rkIdx U) :
    Nat.card U ≤ 2 ^ (m - k) := by
  rw [card_eq_two_pow_sub_rkIdx hV U]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_pairMod : Nat.card (PairMod K) = Nat.card K ^ 6 := by
  rw [Nat.card_prod, card_stdMod, Fintype.card_fin, ← pow_add]

omit [Finite K] [CharP K 2] in
theorem card_fix_eq_card_fixV (g : MulAut (StdMod (Fin 3) K)) :
    Nat.card {v : StdMod (Fin 3) K // g v = v} = Nat.card ↥(fixV (Subgroup.zpowers g)) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixV_zpowers_iff.symm)

omit [CharP K 2] in
theorem card_fix_le_sq {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g : MulAut (StdMod (Fin 3) K)} (hg : g ∈ natNorm (StatedSL 3 K)) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) : Nat.card {v : StdMod (Fin 3) K // g v = v} ≤ Nat.card K ^ 2 := by
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  have hsl := isSemilinear_fieldAut hΓ ⟨g, hg⟩
  have hk : n ≤ rkIdx (fixV (Subgroup.zpowers g)) := by
    by_cases hσ : fieldAut hΓ ⟨g, hg⟩ = RingEquiv.refl K
    · rw [hσ] at hsl
      exact le_rkIdx_fixV_of_linear hK hsl hg1
    · obtain ⟨-, h⟩ := rkIdx_fixV_of_semilinear_two hn hK hsl hσ hg2
      simp only [Fintype.card_fin] at h
      omega
  have hV : Nat.card (StdMod (Fin 3) K) = 2 ^ (3 * n) := by
    rw [card_stdMod, hK, Fintype.card_fin, ← pow_mul, mul_comm]
  rw [card_fix_eq_card_fixV]
  have := card_le_of_le_rkIdx hV _ hk
  rw [hK, ← pow_mul]
  exact this.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

omit [CharP K 2] in
theorem card_fix_sq_of_semilinear {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K} (hg : IsSemilinear g σ)
    (hσ : σ ≠ RingEquiv.refl K) (hg2 : g ^ 2 = 1) :
    Nat.card {v : StdMod (Fin 3) K // g v = v} ^ 2 = Nat.card K ^ 3 := by
  obtain ⟨-, h⟩ := rkIdx_fixV_of_semilinear_two hn hK hg hσ hg2
  simp only [Fintype.card_fin] at h
  have hV : Nat.card (StdMod (Fin 3) K) = 2 ^ (3 * n) := by
    rw [card_stdMod, hK, Fintype.card_fin, ← pow_mul, mul_comm]
  rw [card_fix_eq_card_fixV, card_eq_two_pow_sub_rkIdx hV, hK, ← pow_mul, ← pow_mul]
  congr 1
  omega

omit [CharP K 2] in
theorem card_fix_pairAut_le (a b : MulAut (StdMod (Fin 3) K)) (A : Subgroup (MulAut (PairMod K)))
    (hab : pairAut a b ∈ A) :
    Nat.card ↥(fixV A) ≤
      Nat.card {v : StdMod (Fin 3) K // a v = v} * Nat.card {w : StdMod (Fin 3) K // b w = w} := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun v => (⟨(v : PairMod K).1, ?_⟩, ⟨(v : PairMod K).2, ?_⟩))
    fun v w h => ?_
  · have := v.2 _ hab
    exact congrArg Prod.fst this
  · have := v.2 _ hab
    exact congrArg Prod.snd this
  · have h1 := congrArg (fun p => (p.1 : StdMod (Fin 3) K)) h
    have h2 := congrArg (fun p => (p.2 : StdMod (Fin 3) K)) h
    exact Subtype.ext (Prod.ext h1 h2)

theorem card_mul_le_of_swap {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    {y : MulAut (PairMod K)} (hyA : y ∈ A) (hy : y ∉ pairSub K) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 6 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hyeq⟩ := exists_swap_decomp (hAN hyA) hy
  have hF := card_fstSub_le_of_swap hAN hA2 (by omega) hK hyA hy
  have h5 := card_le_two_mul_card_inf_pairSub hAN
  have h1 := card_le_card_fstSub hAN hA2
  have hfix : Nat.card ↥(fixV A) ≤
      Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨(v : PairMod K).1, ?_⟩) fun v w h => ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply] at this
      exact congrArg Prod.fst this
    · have h' : (v : PairMod K).1 = (w : PairMod K).1 := congrArg Subtype.val h
      have hv := v.2 _ hyA
      have hw := w.2 _ hyA
      rw [hyeq] at hv hw
      have hv2 : (v : PairMod K).2 = fstHom K s (v : PairMod K).1 :=
        (congrArg Prod.snd hv).symm
      have hw2 : (w : PairMod K).2 = fstHom K s (w : PairMod K).1 :=
        (congrArg Prod.snd hw).symm
      exact Subtype.ext (Prod.ext h' (by rw [hv2, hw2, h']))
  have hq3 : Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} ≤ Nat.card K ^ 3 :=
    calc _ ≤ Nat.card (StdMod (Fin 3) K) := Finite.card_subtype_le _
      _ = Nat.card K ^ 3 := by rw [card_stdMod, Fintype.card_fin]
  by_cases hF1 : fstSub A = ⊥
  · have hF1' : Nat.card (fstSub A) = 1 := by rw [hF1, Subgroup.card_bot]
    have hA : Nat.card A ≤ 2 := by omega
    have h8 : 8 ≤ Nat.card K ^ 3 :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc 4 * Nat.card A * Nat.card ↥(fixV A) ≤ 4 * 2 * Nat.card K ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hA) (hfix.trans hq3)
      _ ≤ Nat.card K ^ 3 * Nat.card K ^ 3 := Nat.mul_le_mul_right _ h8
      _ = Nat.card K ^ 6 := by ring
  · obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
    have hf2 : (f : MulAut (StdMod (Fin 3) K)) ^ 2 = 1 := (isElemAbelian2_fstSub hA2).2 _ hf
    have hfN := fstSub_le_natNorm hAN hf
    have hq2 : Nat.card {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} ≤ Nat.card K ^ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun v : {v : StdMod (Fin 3) K // ∀ f ∈ fstSub A, f v = v} =>
          (⟨v.1, v.2 _ hf⟩ : {v : StdMod (Fin 3) K // (f : MulAut _) v = v}))
        fun v w h => Subtype.ext ?_) ?_
      · exact congrArg (fun z : {v : StdMod (Fin 3) K // (f : MulAut _) v = v} => z.1) h
      · exact card_fix_le_sq (by omega) hK hfN hf2 (fun h => hf1 (Subtype.ext h))
    have hA : Nat.card A ≤ 4 * Nat.card K := by omega
    have h16 : 16 ≤ Nat.card K ^ 3 :=
      calc 16 ≤ 4 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq4 3
    calc 4 * Nat.card A * Nat.card ↥(fixV A) ≤ 4 * (4 * Nat.card K) * Nat.card K ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hA) (hfix.trans hq2)
      _ = 16 * Nat.card K ^ 3 := by ring
      _ ≤ Nat.card K ^ 3 * Nat.card K ^ 3 := Nat.mul_le_mul_right _ h16
      _ = Nat.card K ^ 6 := by ring

theorem card_transpose_fix_le {F : Type} [Field F] [Finite F] (E : Subgroup (GL (Fin 3) F)) :
    Nat.card {w : Fin 3 → F // ∀ A ∈ E, (A : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w} ≤
      Nat.card F ^ (3 - Module.finrank F (commSp E)) := by
  let D : Submodule F (Fin 3 → F) :=
    { carrier := {w | ∀ A ∈ E, (A : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w}
      add_mem' := fun {v w} hv hw A hA => by rw [Matrix.mulVec_add, hv A hA, hw A hA]
      zero_mem' := fun A _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv A hA => by rw [Matrix.mulVec_smul, hv A hA] }
  let B : LinearMap.BilinForm F (Fin 3 → F) := Matrix.toBilin' 1
  have hB : B.Nondegenerate := by
    refine (Matrix.nondegenerate_toBilin'_iff).mpr (Matrix.nondegenerate_of_det_ne_zero ?_)
    rw [Matrix.det_one]
    exact one_ne_zero
  have hB' : ∀ u w, B u w = u ⬝ᵥ w := fun u w => by
    simp [B, Matrix.toBilin'_apply']
  have hDR : D ≤ B.orthogonal (commSp E) := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [hB']
    have hle : commSp E ≤ LinearMap.ker (B.flip w) := by
      rw [commSp, iSup_le_iff]
      rintro A _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      change B (nOf (A : GL (Fin 3) F) v) w = 0
      rw [hB', nOf_apply, sub_dotProduct,
        dotProduct_comm (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) w,
        ← Matrix.dotProduct_transpose_mulVec, hw A A.2, sub_self]
    have := hle hu
    rw [LinearMap.mem_ker] at this
    change B u w = 0 at this
    rwa [hB'] at this
  have h1 := Submodule.finrank_mono hDR
  rw [LinearMap.BilinForm.finrank_orthogonal hB, Module.finrank_fin_fun] at h1
  have h2 : Nat.card {w : Fin 3 → F // ∀ A ∈ E, (A : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w} =
      Nat.card D := rfl
  rw [h2, Module.natCard_eq_pow_finrank (K := F) (V := D)]
  exact Nat.pow_le_pow_right Nat.card_pos h1

theorem card_mul_le_of_linear {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) (hsub : A ≤ pairSub K) (hlin : fstSub A ≤ linSub) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 6 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hF2 := isElemAbelian2_fstSub hA2
  set E := linMat (fstSub A) with hEdef
  have hEcard : Nat.card E = Nat.card (fstSub A) := by
    rw [hEdef, card_linMat, inf_eq_left.mpr hlin]
  have h1 := card_le_card_fstSub hAN hA2
  rw [inf_eq_left.mpr hsub] at h1
  obtain ⟨hRC, hcard⟩ := card_le_of_elemAbelian_GL3' E (linMat_sq hF2) (linMat_comm hF2)
  have hfix : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixSp E) *
      Nat.card {w : Fin 3 → K // ∀ B ∈ E, (B : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = w} := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun v => (⟨Multiplicative.toAdd (v : PairMod K).1, ?_⟩,
        ⟨Multiplicative.toAdd (v : PairMod K).2, ?_⟩)) fun v w h => ?_
    · refine (Submodule.mem_iInf _).mpr fun B => ?_
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := B.2
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply, hxB] at h
      have h' : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (v : PairMod K).1 =
          Multiplicative.toAdd (v : PairMod K).1 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.1) h
      rw [LinearMap.mem_ker, nOf_apply, h', sub_self]
    · intro B hB
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := hB
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
        rw [← sq]
        exact hA2.2 _ hxA
      obtain ⟨-, hT⟩ := snd_eq_transpose (hAN hxA) hx2 hxB
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply] at h
      have h' : toAddMap (sndHom K x) (Multiplicative.toAdd (v : PairMod K).2) =
          Multiplicative.toAdd (v : PairMod K).2 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.2) h
      rw [← hT]
      exact h'
    · have h1 := congrArg (fun p => (p.1 : Fin 3 → K)) h
      have h2 := congrArg (fun p => (p.2 : Fin 3 → K)) h
      exact Subtype.ext (Prod.ext h1 h2)
  have hD := card_transpose_fix_le E
  have hC : Nat.card ↥(fixSp E) = Nat.card K ^ Module.finrank K (fixSp E) :=
    Module.natCard_eq_pow_finrank (K := K) (V := fixSp E)
  have hc3 : Module.finrank K (fixSp E) ≤ 3 := by
    have := Submodule.finrank_le (fixSp E)
    rwa [Module.finrank_fin_fun] at this
  have hrc := Submodule.finrank_mono hRC
  have hA2' : 2 ≤ Nat.card A := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have := (Finite.one_lt_card_iff_nontrivial (α := ↥A)).mpr ⟨⟨⟨a, ha⟩, 1, ha1⟩⟩
    omega
  have hpos : 1 ≤ (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) := by
    by_contra h
    push Not at h
    have h0 : (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) = 0 := by omega
    rw [h0, pow_zero] at hcard
    omega
  have hexp : Module.finrank K (fixSp E) + (3 - Module.finrank K (commSp E)) +
      (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) ≤ 5 := by
    generalize Module.finrank K (fixSp E) = c at hc3 hrc hpos ⊢
    generalize Module.finrank K (commSp E) = r at hrc hpos ⊢
    interval_cases c <;> interval_cases r <;> omega
  have hA : Nat.card A ≤
      Nat.card K ^ ((3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) := by
    rw [← hEcard] at h1
    exact h1.trans hcard
  have hfix' : Nat.card ↥(fixV A) ≤ Nat.card K ^ Module.finrank K (fixSp E) *
      Nat.card K ^ (3 - Module.finrank K (commSp E)) := by
    rw [← hC]
    exact hfix.trans (Nat.mul_le_mul_left _ hD)
  calc 4 * Nat.card A * Nat.card ↥(fixV A)
      ≤ 4 * Nat.card K ^ ((3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) *
          (Nat.card K ^ Module.finrank K (fixSp E) *
            Nat.card K ^ (3 - Module.finrank K (commSp E))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 hA) hfix'
    _ = 4 * Nat.card K ^ (Module.finrank K (fixSp E) + (3 - Module.finrank K (commSp E)) +
          (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) := by
        ring
    _ ≤ 4 * Nat.card K ^ 5 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) hexp)
    _ ≤ Nat.card K * Nat.card K ^ 5 := Nat.mul_le_mul_right _ hq4
    _ = Nat.card K ^ 6 := by ring

theorem card_mul_le_of_field {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    (hsub : A ≤ pairSub K) (hlin : ¬ fstSub A ≤ linSub) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 6 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hF2 := isElemAbelian2_fstSub hA2
  have h1 := card_le_card_fstSub hAN hA2
  rw [inf_eq_left.mpr hsub] at h1
  have h2 := card_le_of_le_natNorm (by omega) hK (fstSub_le_natNorm hAN) hF2
  obtain ⟨f, hf, hfl⟩ : ∃ f ∈ fstSub A, f ∉ linSub := by
    by_contra h
    push Not at h
    exact hlin h
  obtain ⟨x, hx, rfl⟩ := hf
  have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
  have hxN := hAN hxA
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  obtain ⟨h₁, -⟩ := fstHom_mem_natNorm hxN
  set σ := fieldAut hΓ ⟨_, h₁⟩
  have hsl : IsSemilinear (fstHom K x) σ := isSemilinear_fieldAut hΓ ⟨_, h₁⟩
  have hσ : σ ≠ RingEquiv.refl K := by
    intro h
    apply hfl
    have := hsl
    rw [h] at this
    exact this
  have hsl₂ : IsSemilinear (sndHom K x) σ := by
    have := hxN
    rw [eq_pairAut x] at this
    exact rel_semilinear this hsl
  have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
    rw [← sq]
    exact hA2.2 _ hxA
  rw [eq_pairAut x, pairAut_mul] at hx2
  obtain ⟨ha, hb⟩ := pairAut_injective (hx2.trans pairAut_one.symm)
  have e1 := card_fix_sq_of_semilinear (by omega) hK hsl hσ (by rw [sq]; exact ha)
  have e2 := card_fix_sq_of_semilinear (by omega) hK hsl₂ hσ (by rw [sq]; exact hb)
  have hfix := card_fix_pairAut_le (fstHom K x) (sndHom K x) A (by rw [← eq_pairAut x]; exact hxA)
  have hprod : (Nat.card {v : StdMod (Fin 3) K // (fstHom K x) v = v} *
      Nat.card {w : StdMod (Fin 3) K // (sndHom K x) w = w}) ^ 2 = (Nat.card K ^ 3) ^ 2 := by
    rw [mul_pow, e1, e2, ← pow_two]
  have hprod' := (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) hprod
  calc 4 * Nat.card A * Nat.card ↥(fixV A) ≤ 4 * Nat.card K ^ 2 * Nat.card K ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 (h1.trans h2)) (hprod' ▸ hfix)
    _ = 4 * Nat.card K ^ 5 := by ring
    _ ≤ Nat.card K * Nat.card K ^ 5 := Nat.mul_le_mul_right _ hq4
    _ = Nat.card K ^ 6 := by ring

theorem rk_add_two_le_rkIdx_fixV {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) : rk ↥A + 2 ≤ rkIdx (fixV A) := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hmain : 4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 6 := by
    by_cases hsub : A ≤ pairSub K
    · by_cases hlin : fstSub A ≤ linSub
      · exact card_mul_le_of_linear hn hK hAN hA2 hA1 hsub hlin
      · exact card_mul_le_of_field hn hK hAN hA2 hsub hlin
    · obtain ⟨y, hyA, hy⟩ : ∃ y ∈ A, y ∉ pairSub K := by
        by_contra h
        push Not at h
        exact hsub h
      exact card_mul_le_of_swap hn hK hAN hA2 hyA hy
  have hV : Nat.card (PairMod K) = 2 ^ (6 * n) := by
    rw [card_pairMod, hK, ← pow_mul, mul_comm]
  have hAcard : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA2)
  refine le_rkIdx_of_card_mul_le hV _ ?_
  rw [pow_add, ← hAcard, ← hV, card_pairMod]
  calc Nat.card ↥(fixV A) * (Nat.card A * 2 ^ 2) = 4 * Nat.card A * Nat.card ↥(fixV A) := by
        ring
    _ ≤ Nat.card K ^ 6 := hmain

theorem not_isFOneModule {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hXN : X ≤ pairNorm K) : ¬ IsFOneModule X := by
  rintro ⟨A, ⟨hAX, hA1, hAel⟩, hoff⟩
  have := rk_add_two_le_rkIdx_fixV hn hK (hAX.trans hXN) hAel hA1
  omega

theorem alphaH_eq_one {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hXN : X ≤ pairNorm K) : alphaH X = 1 :=
  alphaH_eq_one_of_not_isFOneModule (not_isFOneModule hn hK hXN)

end SL3Pair

end H

end CFSG.Quasithin
