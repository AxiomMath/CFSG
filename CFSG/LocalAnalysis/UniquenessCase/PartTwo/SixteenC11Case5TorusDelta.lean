module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def s16c11_case5_Delta : Subgroup (MulAut (VM K)) where
  carrier := Set.range (fun x : K => s16c11_case5_rhoU x x)
  one_mem' := ⟨0, s16c11_case5_rhoU_one⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, (s16c11_case5_rhoU_mul x x y y).symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, (s16c11_case5_rhoU_inv x x).symm⟩

private theorem s16c11_case5_sa_eq_def [CharP K 2] (a : K) :
    s16c11_case5_sa a = s16c11_case5_rhoU a a * s16c11_case5_sigma := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  show Multiplicative.toAdd (s16c11_case5_sa a
      (Multiplicative.ofAdd (Multiplicative.toAdd X))) =
    Multiplicative.toAdd ((s16c11_case5_rhoU a a * s16c11_case5_sigma (K := K))
      (Multiplicative.ofAdd (Multiplicative.toAdd X)))
  rw [MulAut.mul_apply, s16c11_case5_sigma_ofAdd, s16c11_case5_rhoU_toAdd,
    s16c11_case5_sa_toAdd]

private theorem s16c11_case5_rhoU_sigma_mul_sa [CharP K 2] (p q a : K) :
    s16c11_case5_rhoU p q * s16c11_case5_sigma * s16c11_case5_sa a =
      s16c11_case5_rhoU (p + a) (q + a) := by
  rw [s16c11_case5_sa_eq_def]
  calc s16c11_case5_rhoU p q * s16c11_case5_sigma *
        (s16c11_case5_rhoU a a * s16c11_case5_sigma)
      = s16c11_case5_rhoU p q *
          (s16c11_case5_sigma * s16c11_case5_rhoU a a * s16c11_case5_sigma) := by
        simp only [mul_assoc]
    _ = s16c11_case5_rhoU p q * s16c11_case5_rhoU a a := by
        rw [s16c11_case5_sigma_conj_rhoU]
    _ = s16c11_case5_rhoU (p + a) (q + a) := s16c11_case5_rhoU_mul p q a a

private theorem s16c11_case5_rhoU_sigma_mul_sa_mem_V [CharP K 2] (p q a : K) :
    s16c11_case5_rhoU p q * s16c11_case5_sigma * s16c11_case5_sa a ∈
      s16c11_case5_V := by
  rw [s16c11_case5_mem_V]
  exact ⟨(p + a, q + a), s16c11_case5_rhoU_sigma_mul_sa p q a⟩

private theorem s16c11_case5_sigma_notMem_V [CharP K 2] :
    s16c11_case5_sigma (K := K) ∉ s16c11_case5_V := by
  intro h
  rw [s16c11_case5_mem_V] at h
  obtain ⟨⟨p, q⟩, hpq⟩ := h
  have h1 : s16c11_case5_sigma
        (Multiplicative.ofAdd (Matrix.single (0 : Fin 2) 1 (1 : K))) =
      s16c11_case5_rhoU p q
        (Multiplicative.ofAdd (Matrix.single (0 : Fin 2) 1 (1 : K))) := by
    rw [hpq]
  have h2 := congrArg Multiplicative.toAdd h1
  rw [s16c11_case5_sigma_ofAdd, s16c11_case5_rhoU_toAdd] at h2
  have h2' : (Matrix.single (0 : Fin 2) 1 (1 : K))ᵀ =
      (s16c11_case5_u p : Matrix (Fin 2) (Fin 2) K) *
        Matrix.single (0 : Fin 2) 1 (1 : K) *
        (s16c11_case5_u q : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    simpa using h2
  have h3 := congrFun (congrFun h2' 0) 1
  rw [Matrix.transpose_apply, s16c11_case5_act_entry_01] at h3
  simp [Matrix.single_apply] at h3

private theorem s16c11_case5_sa_notMem_V [CharP K 2] (a : K) :
    s16c11_case5_sa a ∉ s16c11_case5_V := by
  intro h
  apply s16c11_case5_sigma_notMem_V (K := K)
  have h1 : (s16c11_case5_rhoU a a)⁻¹ * s16c11_case5_sa a = s16c11_case5_sigma := by
    rw [s16c11_case5_sa_eq_def]; group
  rw [← h1]
  exact s16c11_case5_V.mul_mem
    (s16c11_case5_V.inv_mem (s16c11_case5_rhoU_mem_V a a)) h

private def s16c11_case5_Z (a : K) : Matrix (Fin 2) (Fin 2) K := !![0, a; 0, 1]

private theorem s16c11_case5_Z_01 (a : K) : s16c11_case5_Z a 0 1 = a := by
  simp [s16c11_case5_Z]

private theorem s16c11_case5_Z_10 (a : K) : s16c11_case5_Z a 1 0 = 0 := by
  simp [s16c11_case5_Z]

private theorem s16c11_case5_Z_11 (a : K) : s16c11_case5_Z a 1 1 = 1 := by
  simp [s16c11_case5_Z]

private theorem s16c11_case5_Z_mem_fixV_sa [CharP K 2] (a : K) :
    Multiplicative.ofAdd (s16c11_case5_Z a) ∈
      fixV (Subgroup.zpowers (s16c11_case5_sa a)) := by
  rw [s16c11_case5_mem_fixV_sa_iff, s16c11_case5_sa_conds]
  constructor
  · rw [s16c11_case5_Z_01, s16c11_case5_Z_10, s16c11_case5_Z_11, add_zero, mul_one]
    exact CharTwo.add_self_eq_zero (a * a)
  · rw [s16c11_case5_Z_01, s16c11_case5_Z_10, s16c11_case5_Z_11, mul_one, add_zero]
    exact CharTwo.add_self_eq_zero a

private theorem s16c11_case5_Z_notMem_fixV_rhoU (x : K) (hx : x ≠ 0) (a : K) :
    Multiplicative.ofAdd (s16c11_case5_Z a) ∉
      fixV (Subgroup.zpowers (s16c11_case5_rhoU x x)) := by
  intro h
  rw [s16c11_case5_mem_fixV_rhoU_iff, s16c11_case5_fix_conds] at h
  exact hx (by
    have h1 := h.1
    rwa [s16c11_case5_Z_11, mul_one] at h1)

theorem s16c11_case5_mem_Delta {x : MulAut (VM K)} :
    x ∈ s16c11_case5_Delta (K := K) ↔ ∃ a : K, x = s16c11_case5_rhoU a a := by
  have h : x ∈ s16c11_case5_Delta (K := K) ↔
      ∃ a : K, s16c11_case5_rhoU a a = x := Iff.rfl
  rw [h]
  exact exists_congr fun a => eq_comm

theorem s16c11_case5_card_Delta (hK : Nat.card K = 4) :
    Nat.card ↥(s16c11_case5_Delta (K := K)) = 4 := by
  haveI := s16c11_case5_charP hK
  have hinj : Function.Injective (fun a : K => s16c11_case5_rhoU a a) :=
    fun _ _ h => (s16c11_case5_rhoU_injective h).1
  change Nat.card (Set.range (fun a : K => s16c11_case5_rhoU a a)) = 4
  rw [Nat.card_range_of_injective hinj, hK]

theorem s16c11_case5_exists_sa_mem (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) (hAV : ¬ A ≤ s16c11_case5_V) :
    ∃ a : K, s16c11_case5_sa a ∈ A := by
  haveI := s16c11_case5_charP hK
  have hx : ∃ x : MulAut (VM K), x ∈ A ∧ x ∉ s16c11_case5_V := by
    by_contra h
    exact hAV fun x hxA => by
      by_contra hxV
      exact h ⟨x, hxA, hxV⟩
  obtain ⟨x, hxA, hxV⟩ := hx
  have hxS0 : x ∈ s16c11_case5_S0 := hA.1 hxA
  rw [s16c11_case5_mem_S0] at hxS0
  obtain ⟨a, b, hx' | hx'⟩ := hxS0
  · exact absurd (by rw [hx']; exact s16c11_case5_rhoU_mem_V a b) hxV
  · have hx2 : x ^ 2 = 1 := hA.2.2.1.2 x hxA
    have hsq : (s16c11_case5_rhoU a b * s16c11_case5_sigma) *
        (s16c11_case5_rhoU a b * s16c11_case5_sigma) =
        s16c11_case5_rhoU (a + b) (a + b) := by
      calc (s16c11_case5_rhoU a b * s16c11_case5_sigma) *
            (s16c11_case5_rhoU a b * s16c11_case5_sigma)
          = s16c11_case5_rhoU a b *
              (s16c11_case5_sigma * s16c11_case5_rhoU a b *
                s16c11_case5_sigma) := by
            simp only [mul_assoc]
        _ = s16c11_case5_rhoU a b * s16c11_case5_rhoU b a := by
            rw [s16c11_case5_sigma_conj_rhoU]
        _ = s16c11_case5_rhoU (a + b) (b + a) := s16c11_case5_rhoU_mul a b b a
        _ = s16c11_case5_rhoU (a + b) (a + b) := by rw [add_comm b a]
    have hsum : a + b = 0 := by
      have h1 : s16c11_case5_rhoU (a + b) (a + b) = s16c11_case5_rhoU 0 0 := by
        rw [← hsq, ← hx', ← pow_two, hx2, s16c11_case5_rhoU_one]
      exact (s16c11_case5_rhoU_injective h1).1
    have hb : b = a := by
      rw [CharTwo.add_eq_zero] at hsum
      exact hsum.symm
    refine ⟨a, ?_⟩
    have hsa : s16c11_case5_sa a = x := by
      rw [s16c11_case5_sa_eq_def, hx', hb]
    rwa [hsa]

theorem s16c11_case5_inf_V_le_Delta (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) {a : K}
    (hsa : s16c11_case5_sa a ∈ A) :
    A ⊓ s16c11_case5_V ≤ s16c11_case5_Delta := by
  haveI := s16c11_case5_charP hK
  rintro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyA, hyV⟩ := hy
  rw [s16c11_case5_mem_V] at hyV
  obtain ⟨⟨p, q⟩, rfl⟩ := hyV
  rw [s16c11_case5_mem_Delta]
  have hcomm := hA.2.2.1.1 (s16c11_case5_rhoU p q) hyA (s16c11_case5_sa a) hsa
  have hleft : s16c11_case5_rhoU p q * s16c11_case5_sa a =
      s16c11_case5_rhoU (p + a) (q + a) * s16c11_case5_sigma := by
    rw [s16c11_case5_sa_eq_def]
    rw [← mul_assoc, s16c11_case5_rhoU_mul]
  have hright : s16c11_case5_sa a * s16c11_case5_rhoU p q =
      s16c11_case5_rhoU (a + q) (a + p) * s16c11_case5_sigma := by
    rw [s16c11_case5_sa_eq_def, mul_assoc]
    rw [show s16c11_case5_sigma * s16c11_case5_rhoU p q =
        s16c11_case5_rhoU q p * s16c11_case5_sigma by
      calc s16c11_case5_sigma * s16c11_case5_rhoU p q
          = (s16c11_case5_sigma * s16c11_case5_rhoU p q *
              s16c11_case5_sigma) * s16c11_case5_sigma := by
            rw [mul_assoc, s16c11_case5_sigma_mul_self, mul_one]
        _ = s16c11_case5_rhoU q p * s16c11_case5_sigma := by
            rw [s16c11_case5_sigma_conj_rhoU]]
    rw [← mul_assoc, s16c11_case5_rhoU_mul]
  have heq : s16c11_case5_rhoU (p + a) (q + a) * s16c11_case5_sigma =
      s16c11_case5_rhoU (a + q) (a + p) * s16c11_case5_sigma := by
    rw [← hleft, ← hright]
    exact hcomm
  have hpq : p + a = a + q := (s16c11_case5_rhoU_injective (mul_right_cancel heq)).1
  refine ⟨p, ?_⟩
  have hq : q = p := by
    have h' : p + a = q + a := by rwa [add_comm a q] at hpq
    exact (add_right_cancel h').symm
  rw [hq]

theorem s16c11_case5_card_eq_two_mul (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) (hAV : ¬ A ≤ s16c11_case5_V) :
    Nat.card ↥A = 2 * Nat.card ↥(A ⊓ s16c11_case5_V) := by
  haveI := s16c11_case5_charP hK
  obtain ⟨a, hsa⟩ := s16c11_case5_exists_sa_mem hK hA hAV
  have hindex : (A ⊓ s16c11_case5_V).relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨s16c11_case5_sa a, hsa, ?_, ?_⟩
    · intro hmem
      exact s16c11_case5_sa_notMem_V a (Subgroup.mem_inf.mp hmem).2
    · intro b hb
      have hbS0 : b ∈ s16c11_case5_S0 := hA.1 hb
      rw [s16c11_case5_mem_S0] at hbS0
      obtain ⟨p, q, hb' | hb'⟩ := hbS0
      · exact Or.inr (Subgroup.mem_inf.mpr ⟨hb, by
          rw [hb']; exact s16c11_case5_rhoU_mem_V p q⟩)
      · refine Or.inl (Subgroup.mem_inf.mpr ⟨A.mul_mem hb hsa, ?_⟩)
        rw [hb']
        exact s16c11_case5_rhoU_sigma_mul_sa_mem_V p q a
  have h := Subgroup.relIndex_mul_card (H := A ⊓ s16c11_case5_V) (K := A)
  rw [inf_eq_left.mpr inf_le_left, hindex] at h
  exact h.symm

theorem s16c11_case5_Delta_le (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) (hAV : ¬ A ≤ s16c11_case5_V) :
    s16c11_case5_Delta ≤ A := by
  haveI := s16c11_case5_charP hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, hsa⟩ := s16c11_case5_exists_sa_mem hK hA hAV
  have hinf_le : A ⊓ s16c11_case5_V ≤ s16c11_case5_Delta :=
    s16c11_case5_inf_V_le_Delta hK hA hsa
  have hcard2 := s16c11_case5_card_eq_two_mul hK hA hAV
  have hcardA : 4 ≤ Nat.card ↥A := by
    have hP : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
    have hm : 2 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
    have h := E3.card_eq_two_pow_mul hP (bot_le : (⊥ : Subgroup (MulAut (VM K))) ≤ A)
    rw [Subgroup.card_bot, mul_one] at h
    rw [h]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num) hm
  have hle4 : Nat.card ↥(A ⊓ s16c11_case5_V) ≤ 4 := by
    have h := Subgroup.card_dvd_of_le hinf_le
    rw [s16c11_case5_card_Delta hK] at h
    exact Nat.le_of_dvd (by norm_num) h
  have hge2 : 2 ≤ Nat.card ↥(A ⊓ s16c11_case5_V) := by
    rw [hcard2] at hcardA
    omega
  have hdvd : Nat.card ↥(A ⊓ s16c11_case5_V) ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hinf_le
    rwa [s16c11_case5_card_Delta hK] at h
  obtain ⟨c, hc⟩ : ∃ c : ℕ, Nat.card ↥(A ⊓ s16c11_case5_V) = c := ⟨_, rfl⟩
  rw [hc] at hcard2 hle4 hge2 hdvd
  interval_cases c
  · exfalso
    have hcardA4 : Nat.card ↥A = 4 := by
      norm_num at hcard2
      exact hcard2
    have hne : A ⊓ s16c11_case5_V ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hc
      omega
    have hy_exists : ∃ y ∈ A ⊓ s16c11_case5_V, y ≠ 1 := by
      by_contra h
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hz1
      exact h ⟨z, hz, hz1⟩
    obtain ⟨y, hy, hy1⟩ := hy_exists
    have hxy : y ∈ s16c11_case5_Delta := hinf_le hy
    rw [s16c11_case5_mem_Delta] at hxy
    obtain ⟨x, hxy⟩ := hxy
    have hyA : y ∈ A := (Subgroup.mem_inf.mp hy).1
    have hx : x ≠ 0 := by
      intro hx0
      apply hy1
      rw [hxy, hx0, s16c11_case5_rhoU_one]
    have hBcard : Nat.card ↥(Subgroup.zpowers (s16c11_case5_sa a)) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact s16c11_case5_sa_sq a)
        (fun h => s16c11_case5_sa_notMem_V a (h.symm ▸ s16c11_case5_V.one_mem))
    have hBA : Subgroup.zpowers (s16c11_case5_sa a) ≤ A :=
      Subgroup.zpowers_le.mpr hsa
    have hrelB : (Subgroup.zpowers (s16c11_case5_sa a)).relIndex A = 2 := by
      have h := Subgroup.relIndex_mul_card
        (H := Subgroup.zpowers (s16c11_case5_sa a)) (K := A)
      rw [inf_eq_left.mpr hBA, hBcard, hcardA4] at h
      omega
    have hmB : E3.mQuot A (Subgroup.zpowers (s16c11_case5_sa a)) = 1 := by
      unfold E3.mQuot
      rw [hrelB]
      exact padicValNat_self
    have hfix : fixV (Subgroup.zpowers (s16c11_case5_sa a)) = fixV A :=
      hA.2.2.2 (Subgroup.zpowers (s16c11_case5_sa a)) hBA (by rw [hmB]; norm_num)
    have hZ : Multiplicative.ofAdd (s16c11_case5_Z a) ∈
        fixV (Subgroup.zpowers (s16c11_case5_sa a)) := s16c11_case5_Z_mem_fixV_sa a
    have hZA : Multiplicative.ofAdd (s16c11_case5_Z a) ∈ fixV A := hfix ▸ hZ
    have hyZ : y (Multiplicative.ofAdd (s16c11_case5_Z a)) =
        Multiplicative.ofAdd (s16c11_case5_Z a) :=
      CFSG.Quasithin.mem_fixV.mp hZA y hyA
    have hnot : s16c11_case5_rhoU x x (Multiplicative.ofAdd (s16c11_case5_Z a)) ≠
        Multiplicative.ofAdd (s16c11_case5_Z a) := by
      intro heq
      exact s16c11_case5_Z_notMem_fixV_rhoU x hx a
        (CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr heq)
    rw [hxy] at hyZ
    exact hnot hyZ
  · exact absurd hdvd (by norm_num)
  · have hEq : A ⊓ s16c11_case5_V = s16c11_case5_Delta :=
      Subgroup.eq_of_le_of_card_ge hinf_le (le_of_eq (by
        rw [s16c11_case5_card_Delta hK, hc]))
    rw [← hEq]
    exact inf_le_left

theorem s16c11_case5_eq_Delta_sup_sigma (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) (hAV : ¬ A ≤ s16c11_case5_V) :
    A = s16c11_case5_Delta ⊔ Subgroup.zpowers (s16c11_case5_sigma (K := K)) := by
  haveI := s16c11_case5_charP hK
  obtain ⟨a, hsa⟩ := s16c11_case5_exists_sa_mem hK hA hAV
  have hDelta : s16c11_case5_Delta ≤ A := s16c11_case5_Delta_le hK hA hAV
  have hinf : A ⊓ s16c11_case5_V ≤ s16c11_case5_Delta :=
    s16c11_case5_inf_V_le_Delta hK hA hsa
  have hsigma : s16c11_case5_sigma ∈ A := by
    have h1 : s16c11_case5_rhoU a a ∈ A :=
      hDelta (s16c11_case5_mem_Delta.mpr ⟨a, rfl⟩)
    have h2 : (s16c11_case5_rhoU a a)⁻¹ * s16c11_case5_sa a =
        s16c11_case5_sigma := by
      rw [s16c11_case5_sa_eq_def]; group
    rw [← h2]
    exact A.mul_mem (A.inv_mem h1) hsa
  refine le_antisymm ?_ (sup_le hDelta (Subgroup.zpowers_le.mpr hsigma))
  intro x hx
  have hxS0 : x ∈ s16c11_case5_S0 := hA.1 hx
  rw [s16c11_case5_mem_S0] at hxS0
  obtain ⟨p, q, hx' | hx'⟩ := hxS0
  · have hxV : x ∈ s16c11_case5_V := by
      rw [hx']; exact s16c11_case5_rhoU_mem_V p q
    exact Subgroup.mem_sup_left (hinf (Subgroup.mem_inf.mpr ⟨hx, hxV⟩))
  · have hxV : x * s16c11_case5_sigma ∈ s16c11_case5_V := by
      rw [hx', mul_assoc, s16c11_case5_sigma_mul_self, mul_one]
      exact s16c11_case5_rhoU_mem_V p q
    have hxA : x * s16c11_case5_sigma ∈ A := A.mul_mem hx hsigma
    have hmem := hinf (Subgroup.mem_inf.mpr ⟨hxA, hxV⟩)
    have hx_eq : x = (x * s16c11_case5_sigma) * s16c11_case5_sigma := by
      rw [mul_assoc, s16c11_case5_sigma_mul_self, mul_one]
    rw [hx_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s16c11_case5_sigma))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
