module

public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.L139L42

open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Ch1Four
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (projectiveSpecialLinearEquivProjectiveSL)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

theorem false_of_lt {j c : ℕ} (h : 20160 * 2 ^ j = c) (hc : c < 20160) : False := by
  have := Nat.one_le_two_pow (n := j)
  omega

theorem false_of_two_pow_eq {j a q : ℕ} (hq : Odd q) (hq1 : 1 < q) (h : 2 ^ j = q * a) : False := by
  have hcop : Nat.Coprime q (2 ^ j) := (Nat.coprime_two_right.mpr hq).pow_right j
  have := Nat.Coprime.eq_one_of_dvd hcop ⟨a, h⟩
  omega

theorem prime_eq_of_dvd {p k : ℕ} (hp : p.Prime) (h : p ∣ 20160 * 2 ^ k) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ (6 + k) * 3 ^ 2 * 5 * 7 := by
    have e : 20160 * 2 ^ k = 2 ^ (6 + k) * 3 ^ 2 * 5 * 7 := by ring
    rwa [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h2)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)))

theorem false_of_np {p k n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : Odd n)
    (h : 20160 * 2 ^ k = n * (p * (p ^ 2 - 1))) : False := by
  have hdvd : p ∣ 20160 * 2 ^ k := h ▸ (dvd_mul_right p _).mul_left n
  obtain ⟨m, rfl⟩ := hn
  rcases prime_eq_of_dvd hp hdvd with rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
    omega
  · norm_num at h
    omega

theorem false_of_p {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : 20160 * 2 ^ k = p * (p ^ 2 - 1)) :
    False :=
  false_of_np hp hp5 odd_one (by rw [one_mul]; exact h)

theorem false_of_p3 {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : 20160 * 2 ^ k = p ^ 3 * (p ^ 2 - 1)) : False := by
  have hdvd : p ∣ 20160 * 2 ^ k := h ▸ (dvd_pow_self p (by norm_num)).mul_right _
  have := Nat.one_le_two_pow (n := k)
  rcases prime_eq_of_dvd hp hdvd with rfl | rfl | rfl | rfl
  · omega
  · omega
  · norm_num at h
    omega
  · norm_num at h
    omega

theorem false_of_l2 {n : ℕ} (h : 20160 = 2 ^ n * (4 ^ n - 1)) : False := by
  by_cases hn : n ≤ 6
  · interval_cases n <;> norm_num at h
  · have h1 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 4 ^ 7 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 7 * (4 ^ 7 - 1) ≤ 2 ^ n * (4 ^ n - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    norm_num at h3
    omega

section Order

variable {B : Type} [Group B] [Finite B]

theorem exists_of_card (h20 : Nat.card (B ⧸ CFSG.pCore 2 B) = 20160) :
    ∃ j, 20160 * 2 ^ j = Nat.card B := by
  obtain ⟨j, hj⟩ := card_modO2_mul (H := B)
  exact ⟨j, by rw [← h20]; exact hj⟩

theorem exists_of_ext (h20 : Nat.card (B ⧸ CFSG.pCore 2 B) = 20160)
    {PV PY : ∀ (V : Type) [Group V], Prop} {c : ℕ}
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V)
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) (h : IsExt B PV PY) :
    ∃ j, 20160 * 2 ^ j = c := by
  obtain ⟨V, hVn, hPV, hPY⟩ := h
  obtain ⟨j, hj⟩ := card_modO2_mul_of_le (H := B) (hV _ hPV)
  exact ⟨j, by rw [← h20, ← hY _ hPY]; exact hj⟩

theorem false_of_ext_lt (h20 : Nat.card (B ⧸ CFSG.pCore 2 B) = 20160)
    {PV PY : ∀ (V : Type) [Group V], Prop} {c : ℕ}
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V)
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) (h : IsExt B PV PY) (hc : c < 20160) :
    False := by
  obtain ⟨j, hj⟩ := exists_of_ext h20 hV hY h
  exact false_of_lt hj hc

theorem false_of_card_lt (h20 : Nat.card (B ⧸ CFSG.pCore 2 B) = 20160) {c : ℕ}
    (h : Nat.card B = c) (hc : c < 20160) : False := by
  obtain ⟨j, hj⟩ := exists_of_card h20
  exact false_of_lt (hj.trans h) hc

theorem false_of_l34 (h3 : IsPSL 3 2 2 B) (h4 : IsPSL 4 2 1 (B ⧸ CFSG.pCore 2 B)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := (CFSG.LieType.Simplicity.fam_PSL_simplicity B 3 2 2 h3).2
  have hc := card_of_isPSL_three_four h3
  have hbot : CFSG.pCore 2 B = ⊥ := by
    rcases (CFSG.pCore_normal (p := 2) (G := B)).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)).exists_card_eq
      rw [ht, Subgroup.card_top, hc] at hk
      exact false_of_two_pow_eq (j := k) (q := 315) (a := 64) (by decide) (by norm_num)
        (by rw [← hk])
  let eB : (B ⧸ CFSG.pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  obtain ⟨-, K₄, _, _, hK₄, ⟨e₄⟩⟩ := h3
  obtain ⟨-, K₂, _, _, hK₂, ⟨e₂⟩⟩ := h4
  let f₄ : B ≃* projectiveSL 3 K₄ :=
    (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K₄).symm).trans
      (projectiveSpecialLinearEquivProjectiveSL 3 K₄)
  let f₂ : B ≃* projectiveSL 4 K₂ :=
    eB.symm.trans ((e₂.trans (projectiveSpecialLinearGroupEquivStatedProj 4 K₂).symm).trans
      (projectiveSpecialLinearEquivProjectiveSL 4 K₂))
  exact (CFSG.ComponentClassification.SymmetricLocal.projectiveSL_three_four_not_equiv
    (by rw [hK₄]; norm_num) (by rw [hK₂]; norm_num)).false (f₄.symm.trans f₂)

end Order

theorem cases_of_psl42
    {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}
    (h4 : IsPSL 4 2 1 (ModO2 B)) (h : A312Case B L) :
    (IsPSL 5 2 1 ↥L ∧ ∃ P, IsParabolic2 L P ∧ B = perfectCore P) ∨
      (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 4 2 1 Y) ∧ IsSporadic .M24 ↥L) ∨
      IsSporadic .J4 ↥L := by
  have h20 : Nat.card (ModO2 B) = 20160 := card_of_isPSL_four_two h4
  have hE2 : ∀ k, ∀ (V : Type) [Group V], IsE2 k V → IsPGroup 2 V := fun k V _ h =>
    isPGroup_of_isE2 h
  have hX2 : ∀ k, ∀ (V : Type) [Group V], IsExtraspecial2 k V → IsPGroup 2 V := fun k V _ h =>
    isPGroup_of_isExtraspecial2 h
  have hA5 : ∀ (Y : Type) [Group Y], IsAlt 5 Y → Nat.card Y = 60 := fun Y _ h => card_alt5 h
  have hA6 : ∀ (Y : Type) [Group Y], IsAlt 6 Y → Nat.card Y = 360 := fun Y _ h => card_alt6 h
  have hA7 : ∀ (Y : Type) [Group Y], IsAlt 7 Y → Nat.card Y = 2520 := fun Y _ h => card_alt7 h
  have hH6 : ∀ (Y : Type) [Group Y], IsHat Y (alternatingGroup (Fin 6)) → Nat.card Y = 1080 :=
    fun Y _ h => card_hat6 h
  have hL32 : ∀ (Y : Type) [Group Y], IsPSL 3 2 1 Y → Nat.card Y = 168 := fun Y _ h =>
    card_of_isPSL_three_two h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨n, hn⟩, -, -⟩ := h
    obtain ⟨-, hc⟩ := card_of_isPSL_two_two hn
    exact (false_of_l2 (h20.symm.trans hc)).elim
  ·
    obtain ⟨f, hf, -, -⟩ := h
    exact (not_three_dvd_card_of_isSz' hf (by rw [h20]; norm_num)).elim
  ·
    have := hL32 _ h.1
    rw [h20] at this
    omega
  ·
    exact Or.inl ⟨h.2.1, h.2.2⟩
  ·
    rcases h.1 with h | h
    · exact (false_of_card_lt h20 (hA5 _ h) (by norm_num)).elim
    · exact (false_of_card_lt h20 (hL32 _ h) (by norm_num)).elim
  ·
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact (false_of_card_lt h20 (hA6 _ h) (by norm_num)).elim
    · exact (false_of_card_lt h20 (hH6 _ h) (by norm_num)).elim
  ·
    rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨h, -⟩
    · obtain ⟨j, hj⟩ := exists_of_card h20
      have hc := card_of_isPSL_two_odd hp (by omega) hB
      exact (false_of_p (k := j + 1) hp (five_le_of_prime hp hp3)
        (by rw [pow_succ, ← mul_assoc, hj, mul_comm, hc])).elim
    · exact (false_of_card_lt h20 (hA5 _ h) (by norm_num)).elim
  ·
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨j, hj⟩ := exists_of_card h20
      exact (false_of_p hp (five_le_of_prime hp hp3) (hj.trans (card_of_isSL2' hp hB))).elim
    · exact (false_of_card_lt h20 (hA6 _ h) (by norm_num)).elim
    · exact (false_of_card_lt h20 (hH6 _ h) (by norm_num)).elim
  ·
    obtain ⟨p, hp, hp3, ⟨V, hVn, ⟨eV⟩, hY⟩, -⟩ := h
    have hp5 := five_le_of_prime hp hp3
    have hV2 : Nat.card V = p ^ 2 := by
      rw [Nat.card_congr eV.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      have : NeZero p := ⟨hp.ne_zero⟩
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    obtain ⟨j, hj⟩ := exists_of_card h20
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, card_of_isSL2' hp hY, hV2] at hj
    exact (false_of_p3 hp hp5 (by rw [hj]; ring)).elim
  ·
    exact (false_of_card_lt h20 (hA6 _ h.1) (by norm_num)).elim
  ·
    rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩
    · exact (false_of_ext_lt h20 (hE2 4) hA5 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 4) hA6 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 4) hA5 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 4) hH6 h (by norm_num)).elim
  ·
    rcases h.1 with h | h | h | h | h | h | h
    · obtain ⟨j, hj⟩ := exists_of_card h20
      rw [card_of_isSporadic_M22' h] at hj
      exact (false_of_two_pow_eq (j := j) (q := 11) (a := 2) (by decide) (by norm_num)
        (by omega)).elim
    · exact (false_of_l34 h h4).elim
    · exact (false_of_ext_lt h20 (hE2 4) hA7 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 4) hL32 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 3) hL32 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 4) hA6 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 4) hA5 h (by norm_num)).elim
  ·
    rcases h with ⟨h | h | h | h, hM⟩
    · exact Or.inr (Or.inl ⟨h, hM⟩)
    · exact (false_of_ext_lt h20 (hE2 6) hL32 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hX2 3) hL32 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 6) hH6 h (by norm_num)).elim
  ·
    exact (false_of_card_lt h20 (hA5 _ h.1) (by norm_num)).elim
  ·
    exact (false_of_ext_lt h20 (hX2 2) hA5 h.1 (by norm_num)).elim
  ·
    exact Or.inr (Or.inr h.1)
  ·
    rcases h.1 with h | h
    · exact (false_of_ext_lt h20 (fun V _ h => isPGroup_of_isZ4StarExtra2 h) hA5 h
        (by norm_num)).elim
    · exact (false_of_ext_lt h20 (fun V _ h => isPGroup_of_isZ4Cubed h) hL32 h
        (by norm_num)).elim
  ·
    rcases h.1 with h | h
    · exact (false_of_ext_lt h20 (hX2 3) hL32 h (by norm_num)).elim
    · exact (false_of_ext_lt h20 (hE2 6) hH6 h (by norm_num)).elim
  ·
    rcases h.1 with h | h
    · have := hA5 _ h
      rw [h20] at this
      omega
    · have := hL32 _ h
      rw [h20] at this
      omega

theorem false_of_nonquasi_psl42 {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (hBL : B ≤ L)
    (hperf : Group.IsPerfect ↥B) (h4 : IsPSL 4 2 1 (ModO2 B)) (h : A312Nonquasi B L) : False := by
  have h20 : Nat.card (ModO2 B) = 20160 := card_of_isPSL_four_two h4
  set OL : Subgroup Q := (CFSG.oddCore ↥L).map L.subtype with hOL
  have hsub : OL.subgroupOf L = CFSG.oddCore ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hLO : L ≤ Subgroup.normalizer (OL : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    rw [hsub]
    infer_instance
  have hBO : B ≤ Subgroup.normalizer (OL : Set Q) := hBL.trans hLO
  have : (OL.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBO
  set V := OL.subgroupOf B with hV
  have hVodd : Odd (Nat.card V) := by
    have h1 : Nat.card V = Nat.card ↥(OL ⊓ B) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective B.subtype_injective]
    have h2 : Nat.card ↥(OL ⊓ B) ∣ Nat.card OL := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card OL = Nat.card (CFSG.oddCore ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h1]
    exact (h3 ▸ A312.odd_card_oddCore ↥L).of_dvd_nat h2
  have : (OL.subgroupOf (B ⊔ OL)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBO
  have hφ : Nat.card (↥B ⧸ V) = (OL.subgroupOf (B ⊔ OL)).index :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B OL hBO).toEquiv
  obtain ⟨p, hp, hp5, hcard⟩ : ∃ p, p.Prime ∧ 5 ≤ p ∧ Nat.card (↥B ⧸ V) = p * (p ^ 2 - 1) := by
    have hpq : Group.IsPerfect (↥B ⧸ V) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' V) (QuotientGroup.mk'_surjective _)
    unfold A312Nonquasi at h
    dsimp only at h
    rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, rfl, hSL⟩
    · have hc : Nat.card (↥B ⧸ V) = p * (p ^ 2 - 1) := by
        rw [hφ, ← hLB, hsub]
        exact card_of_isSL2' hp hSL
      have hp5 : 5 ≤ p := by
        by_contra hlt
        have hp3 : p = 3 := by
          have := hp.two_le
          interval_cases p <;> first | rfl | exact absurd rfl hp2 | exact absurd hp (by decide)
        subst hp3
        exact false_of_perfect_card_24 hpq (hc.trans (by norm_num))
      exact ⟨p, hp, hp5, hc⟩
    · refine ⟨5, by norm_num, le_rfl, ?_⟩
      rw [hφ]
      exact card_of_isSL2' (by norm_num) hSL
  obtain ⟨j, hj⟩ := exists_of_card h20
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hcard] at hj
  exact false_of_np hp hp5 hVodd (by rw [hj]; ring)

end CFSG.Quasithin.L139L42
