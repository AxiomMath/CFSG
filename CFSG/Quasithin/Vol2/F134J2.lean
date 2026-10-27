module

public import CFSG.Quasithin.Vol2.F134J2Check
public import CFSG.Quasithin.Vol2.F134J2Dec
public import CFSG.Walter.W67.W1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Quasithin.Vol2.F134Basic

public section

namespace CFSG.Quasithin.F134

open CFSG.Sporadic.Bridge.J2 CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

theorem glCode_j2Word (w : List ℕ) : glCode (j2Word w) = j2WordC w := by
  induction w with
  | nil => exact j2_code_one
  | cons c w ih =>
    by_cases hc : c = 0
    · simp only [j2Word, j2WordC, hc, ite_true, glCode_mul, ih, j2_code_a]
    · simp only [j2Word, j2WordC, hc, ite_false, glCode_mul, ih, j2_code_b]

theorem j2Word_mem (w : List ℕ) : j2Word w ∈ seedGroup := by
  induction w with
  | nil => exact one_mem _
  | cons c w ih =>
    refine mul_mem ?_ ih
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem eq_of_glCode {u v : GL (Fin 14) (ZMod 5)} (h : glCode u = glCode v) : u = v :=
  glCode_injective h

@[expose] noncomputable def j2TGen (k : ℕ) : GL (Fin 14) (ZMod 5) := j2Word (j2TGenW.getD k [])

@[expose] noncomputable def j2T : Subgroup (GL (Fin 14) (ZMod 5)) :=
  Subgroup.closure {x | ∃ k < 3, j2TGen k = x}

theorem glCode_j2TGen {k : ℕ} (hk : k < 3) : glCode (j2TGen k) = j2TG k := by
  rw [j2TGen, glCode_j2Word]
  exact j2_tgen_check k hk

theorem j2T_le : j2T ≤ seedGroup := by
  rw [j2T, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact j2Word_mem _

theorem j2T_sub {x : GL (Fin 14) (ZMod 5)} (hx : x ∈ j2T) : ∃ i < 128, glCode x = j2Tel i := by
  refine closure_subset_of_right_closed (S := {x | ∃ k < 3, j2TGen k = x})
    (P := {x | ∃ i < 128, glCode x = j2Tel i})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, by norm_num, by rw [j2_code_one, j2_tel_zero]⟩ ?_ hx
  rintro p ⟨i, hi, hp⟩ s ⟨k, hk, rfl⟩
  obtain ⟨h1, h2⟩ := j2_nxt_check i hi k hk
  exact ⟨_, h1, by rw [glCode_mul, hp, glCode_j2TGen hk, h2]⟩

theorem j2T_sup : ∀ i < 128, ∃ x ∈ j2T, glCode x = j2Tel i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [j2_code_one, j2_tel_zero]⟩
    · obtain ⟨h1, h2, h3⟩ := j2_par_check i hi hpos
      obtain ⟨y, hy, hyc⟩ := ih _ h1 (h1.trans hi)
      refine ⟨y * j2TGen (j2Par i % 4), mul_mem hy (Subgroup.subset_closure ⟨_, h2, rfl⟩), ?_⟩
      rw [glCode_mul, hyc, glCode_j2TGen h2, h3]

@[expose] noncomputable def j2TelE (i : ℕ) : GL (Fin 14) (ZMod 5) :=
  if h : i < 128 then Classical.choose (j2T_sup i h) else 1

theorem j2TelE_mem (i : ℕ) : j2TelE i ∈ j2T := by
  unfold j2TelE
  split_ifs with h
  · exact (Classical.choose_spec (j2T_sup i h)).1
  · exact one_mem _

theorem glCode_j2TelE {i : ℕ} (hi : i < 128) : glCode (j2TelE i) = j2Tel i := by
  unfold j2TelE
  rw [dite_eq_left hi]
  exact (Classical.choose_spec (j2T_sup i hi)).2

theorem j2TelE_zero : j2TelE 0 = 1 :=
  eq_of_glCode (by rw [glCode_j2TelE (by norm_num), j2_tel_zero, j2_code_one])

theorem card_j2T : Nat.card j2T = 128 := by
  let f : Fin 128 → j2T := fun i => ⟨j2TelE i, j2TelE_mem i⟩
  have hinj : Function.Injective f := by
    intro i j h
    have hv : j2TelE i = j2TelE j := congrArg Subtype.val h
    have hc := congrArg glCode hv
    rw [glCode_j2TelE i.2, glCode_j2TelE j.2] at hc
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact j2_tel_ne j j.2 i hlt hc.symm
    · exact j2_tel_ne i i.2 j hlt hc
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, hc⟩ := j2T_sub hx
    exact ⟨⟨i, hi⟩, Subtype.ext (eq_of_glCode ((glCode_j2TelE hi).trans hc.symm))⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_fin]

@[expose] noncomputable def j2DP (j : ℕ) : GL (Fin 14) (ZMod 5) := j2Word (j2DW.getD j [])

theorem glCode_j2DP {j : ℕ} (hj : j < 72) : glCode (j2DP j) = j2D j := by
  rw [j2DP, glCode_j2Word]
  exact j2_d_check j hj

theorem j2DP_zero : j2DP 0 = 1 := by
  rw [j2DP, j2_dw_zero]
  rfl

@[expose] def j2U : Set (GL (Fin 14) (ZMod 5)) :=
  {x | ∃ j < 72, ∃ t ∈ j2T, ∃ t' ∈ j2T, x = t * j2DP j * t'}

theorem one_mem_j2U : (1 : GL (Fin 14) (ZMod 5)) ∈ j2U :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [j2DP_zero]; group⟩

theorem j2U_mul_T {x s : GL (Fin 14) (ZMod 5)} (hx : x ∈ j2U) (hs : s ∈ j2T) : x * s ∈ j2U := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem j2U_mul_b {x : GL (Fin 14) (ZMod 5)} (hx : x ∈ j2U) : x * uB ∈ j2U := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨i, hi, hc⟩ := j2T_sub ht'
  obtain ⟨hk, heq⟩ := j2_dec_spec hj hi
  have key : j2DP j * (t' * uB) =
      j2TelE (j2Dec j i / 128 % 128) * j2DP (j2Dec j i / 16384) * j2TelE (j2Dec j i % 128) := by
    apply eq_of_glCode
    rw [glCode_mul, glCode_mul, glCode_mul, glCode_mul, glCode_j2DP hj, hc, j2_code_b,
      glCode_j2TelE (Nat.mod_lt _ (by norm_num)), glCode_j2TelE (Nat.mod_lt _ (by norm_num)),
      glCode_j2DP hk]
    exact heq
  refine ⟨_, hk, t * j2TelE (j2Dec j i / 128 % 128), mul_mem ht (j2TelE_mem _),
    j2TelE (j2Dec j i % 128), j2TelE_mem _, ?_⟩
  calc t * j2DP j * t' * uB = t * (j2DP j * (t' * uB)) := by group
    _ = _ := by rw [key]
    _ = _ := by group

@[expose] noncomputable def j2AWE : List ℕ → GL (Fin 14) (ZMod 5)
  | [] => 1
  | c :: w => (if c = 3 then uB else j2TGen c) * j2AWE w

theorem glCode_j2AWE : ∀ w : List ℕ, (∀ c ∈ w, c < 4) → glCode (j2AWE w) = j2AWC w
  | [], _ => j2_code_one
  | c :: w, hw => by
    have hc := hw c List.mem_cons_self
    rw [j2AWE, j2AWC, glCode_mul, glCode_j2AWE w fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')]
    by_cases h3 : c = 3
    · rw [ite_eq_left h3, ite_eq_left h3, j2_code_b]
    · rw [ite_eq_right h3, ite_eq_right h3, glCode_j2TGen (by omega)]

theorem j2U_mul_AWE : ∀ w : List ℕ, (∀ c ∈ w, c < 4) → ∀ x ∈ j2U, x * j2AWE w ∈ j2U
  | [], _, x, hx => by rw [j2AWE, mul_one]; exact hx
  | c :: w, hw, x, hx => by
    have hc := hw c List.mem_cons_self
    rw [j2AWE, ← mul_assoc]
    refine j2U_mul_AWE w (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) _ ?_
    by_cases h3 : c = 3
    · rw [ite_eq_left h3]
      exact j2U_mul_b hx
    · rw [ite_eq_right h3]
      exact j2U_mul_T hx (Subgroup.subset_closure ⟨c, by omega, rfl⟩)

theorem j2U_mul_a {x : GL (Fin 14) (ZMod 5)} (hx : x ∈ j2U) : x * uA ∈ j2U := by
  have h : uA = j2AWE j2AW :=
    eq_of_glCode (j2_code_a.trans (j2_a_check.1.symm.trans (glCode_j2AWE _ j2_a_check.2).symm))
  rw [h]
  exact j2U_mul_AWE _ j2_a_check.2 x hx

theorem seedGroup_subset_j2U : (seedGroup : Set (GL (Fin 14) (ZMod 5))) ⊆ j2U := by
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_j2U ?_
  rintro p hp s (rfl | rfl)
  · exact j2U_mul_a hp
  · exact j2U_mul_b hp

@[expose] def j2CJ (s : ℕ) : ℕ := if s ≤ 3 then s else (s + 3) / 2

@[expose] def j2CR (s : ℕ) : ℕ := if s = 4 ∨ s = 6 ∨ s = 8 then 3 else 0

@[expose] noncomputable def j2CP (s : ℕ) : GL (Fin 14) (ZMod 5) := j2TelE (j2CR s) * j2DP (j2CJ s)

theorem glCode_j2CP {s : ℕ} (hs : s < 9) : glCode (j2CP s) = j2CC s := by
  have hr : j2CR s < 128 := by unfold j2CR; split_ifs <;> norm_num
  have hj : j2CJ s < 72 := by unfold j2CJ; split_ifs <;> omega
  rw [j2CP, glCode_mul, glCode_j2TelE hr, glCode_j2DP hj]
  rfl

theorem j2CP_eq {j b : ℕ} (hj : j < 6) (hb : b < (if j < 3 then 1 else 2)) :
    j2CP (if j < 3 then j else 2 * j - 3 + b) = j2TelE (if b = 0 then 0 else 3) * j2DP j := by
  have h : j2CR (if j < 3 then j else 2 * j - 3 + b) = (if b = 0 then 0 else 3) ∧
      j2CJ (if j < 3 then j else 2 * j - 3 + b) = j := by
    have hb2 : b < 2 := by split_ifs at hb <;> omega
    unfold j2CR j2CJ
    interval_cases j <;> interval_cases b <;> simp_all
  rw [j2CP, h.1, h.2]

theorem j2_good_of_mem {H : Subgroup (GL (Fin 14) (ZMod 5))} (hTH : j2T ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) {j : ℕ} (hj : j < 72) (hj6 : 6 ≤ j)
    (hD : j2DP j ∈ H) : False := by
  obtain ⟨hp', hi, hpow, hne⟩ := j2_bad_check j hj hj6
  set p := j2Bad j % 16 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(j2DP j * j2TelE (j2Bad j / 256)) ^ (j2Bad j / 16 % 16),
    pow_mem (mul_mem hD (hTH (j2TelE_mem _))) _⟩
  have hcode : glCode (x : GL (Fin 14) (ZMod 5)) = powC14 j2oneC (j2Bad j / 16 % 16)
      (mul14 (j2D j) (j2Tel (j2Bad j / 256))) := by
    show glCode ((j2DP j * j2TelE (j2Bad j / 256)) ^ (j2Bad j / 16 % 16)) = _
    rw [glCode_pow, glCode_mul, glCode_j2DP hj, glCode_j2TelE hi, j2_code_one]
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_glCode
    rw [Subgroup.coe_pow, glCode_pow, hcode, Subgroup.coe_one, j2_code_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, j2_code_one]
  have hdvd : p ∣ Nat.card H := orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x
  rcases hp' with h | h
  · rw [h] at hdvd
    exact h5 hdvd
  · rw [h] at hdvd
    exact h7 hdvd

theorem j2_cover {H : Subgroup (GL (Fin 14) (ZMod 5))} (hTH : j2T ≤ H) (hH : H ≤ seedGroup)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) :
    ∀ h ∈ H, ∃ s < 9, ∃ t ∈ j2T, h = j2CP s * t := by
  intro h hh
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := seedGroup_subset_j2U (hH hh)
  have hD : j2DP j ∈ H := by
    have e : j2DP j = t⁻¹ * (t * j2DP j * t') * t'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · obtain ⟨i, hi, htc⟩ := j2T_sub ht
    obtain ⟨hb, hcos⟩ := j2_cos_check j hj6 i hi
    have key : t * j2DP j =
        j2TelE (if j2Cos j i / 128 = 0 then 0 else 3) * j2DP j * j2TelE (j2Cos j i % 128) := by
      apply eq_of_glCode
      have hr : (if j2Cos j i / 128 = 0 then 0 else 3) < 128 := by split_ifs <;> norm_num
      rw [glCode_mul, glCode_mul, glCode_mul, htc, glCode_j2TelE hr,
        glCode_j2TelE (Nat.mod_lt _ (by norm_num)), glCode_j2DP hj]
      exact hcos
    refine ⟨if j < 3 then j else 2 * j - 3 + j2Cos j i / 128, by split_ifs at hb ⊢ <;> omega,
      j2TelE (j2Cos j i % 128) * t', mul_mem (j2TelE_mem _) ht', ?_⟩
    rw [j2CP_eq hj6 hb, ← mul_assoc, ← key]
  · exact (j2_good_of_mem hTH h5 h7 hj hj6 hD).elim

theorem j2_card_le {H : Subgroup (GL (Fin 14) (ZMod 5))} (hTH : j2T ≤ H) (hH : H ≤ seedGroup)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) : Nat.card H ≤ 9 * Nat.card j2T := by
  choose s hs t ht hst using fun h : H => j2_cover hTH hH h5 h7 h h.2
  have hinj : Function.Injective fun h : H => ((⟨s h, hs h⟩, ⟨t h, ht h⟩) : Fin 9 × j2T) := by
    intro h h' e
    simp only [Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at e
    exact Subtype.ext ((hst h).trans (e.1 ▸ e.2 ▸ (hst h').symm))
  calc Nat.card H ≤ Nat.card (Fin 9 × j2T) := Nat.card_le_card_of_injective _ hinj
    _ = 9 * Nat.card j2T := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def j2H0 : Set (GL (Fin 14) (ZMod 5)) := {x | ∃ s < 9, ∃ t ∈ j2T, x = j2CP s * t}

theorem j2H0_eq_range :
    j2H0 = Set.range fun q : Fin 9 × Fin 128 => j2CP q.1 * j2TelE q.2 := by
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    obtain ⟨i, hi, hc⟩ := j2T_sub ht
    refine ⟨(⟨s, hs⟩, ⟨i, hi⟩), ?_⟩
    show j2CP s * j2TelE i = j2CP s * t
    rw [eq_of_glCode ((glCode_j2TelE hi).trans hc.symm)]
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.1.2, j2TelE q.2, j2TelE_mem _, rfl⟩

theorem ncard_j2H0_le : j2H0.ncard ≤ 1152 := by
  rw [j2H0_eq_range, ← Set.image_univ]
  calc _ ≤ (Set.univ : Set (Fin 9 × Fin 128)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 1152 := by rw [Set.ncard_univ]; simp

theorem j2_eq_H0 {H : Subgroup (GL (Fin 14) (ZMod 5))} (hTH : j2T ≤ H) (hH : H ≤ seedGroup)
    (h5 : ¬ 5 ∣ Nat.card H) (h7 : ¬ 7 ∣ Nat.card H) (hcard : Nat.card H = 1152) :
    (H : Set (GL (Fin 14) (ZMod 5))) = j2H0 := by
  have hH' : (H : Set (GL (Fin 14) (ZMod 5))).ncard = 1152 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  refine Set.eq_of_subset_of_ncard_le (fun h hh => j2_cover hTH hH h5 h7 h hh) ?_
    (Set.toFinite _)
  rw [hH']
  exact ncard_j2H0_le

@[expose] noncomputable def j2Cnt (K : Subgroup (GL (Fin 14) (ZMod 5))) (z : GL (Fin 14) (ZMod 5)) :
    ℕ :=
  Nat.card ↥(K ⊓ Subgroup.centralizer ({z} : Set (GL (Fin 14) (ZMod 5))))

theorem j2_card_cent {K : Subgroup (GL (Fin 14) (ZMod 5))}
    (hK : (K : Set (GL (Fin 14) (ZMod 5))) = j2H0) (hcard : Nat.card K = 1152)
    (z : GL (Fin 14) (ZMod 5)) : j2Cnt K z = j2CentCount (glCode z) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin 9 × Fin 128 → GL (Fin 14) (ZMod 5),
      Φ = fun q => j2CP q.1 * j2TelE q.2 := ⟨_, rfl⟩
  have hrange : Set.range Φ = (K : Set (GL (Fin 14) (ZMod 5))) := by rw [hK, j2H0_eq_range, hΦ]
  have hinj : Function.Injective Φ := by
    have e1 : (K : Set (GL (Fin 14) (ZMod 5))).ncard = 1152 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard
    have h1 : (Φ '' Set.univ).ncard = (Set.univ : Set (Fin 9 × Fin 128)).ncard := by
      rw [Set.image_univ, hrange, Set.ncard_univ, e1]
      simp
    exact Set.injOn_univ.mp (Set.injOn_of_ncard_image_eq h1)
  have hcode : ∀ q : Fin 9 × Fin 128, glCode (Φ q) = mul14 (j2CC q.1) (j2Tel q.2) := by
    intro q
    rw [hΦ]
    show glCode (j2CP q.1 * j2TelE q.2) = _
    rw [glCode_mul, glCode_j2CP q.1.2, glCode_j2TelE q.2.2]
  set S : Finset (Fin 9 × Fin 128) := (Finset.univ : Finset (Fin 9 × Fin 128)).filter fun q =>
    mul14 (mul14 (j2CC q.1) (j2Tel q.2)) (glCode z) =
      mul14 (glCode z) (mul14 (j2CC q.1) (j2Tel q.2)) with hS
  have hP : ∀ q, q ∈ S ↔ Φ q * z = z * Φ q := by
    intro q
    rw [hS, Finset.mem_filter, ← hcode q]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      apply eq_of_glCode
      rw [glCode_mul (Φ q) z, glCode_mul z (Φ q)]
      exact h
    · intro h
      have := congrArg glCode h
      rw [glCode_mul (Φ q) z, glCode_mul z (Φ q)] at this
      exact this
  let f : ↥S → ↥(K ⊓ Subgroup.centralizer ({z} : Set (GL (Fin 14) (ZMod 5)))) :=
    fun q => ⟨Φ q.1, Subgroup.mem_inf.mpr ⟨by
      rw [← SetLike.mem_coe, ← hrange]
      exact ⟨q.1, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ((hP q.1).mp q.2)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q q' h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
      have hx' : x ∈ Set.range Φ := by rw [hrange]; exact hxK
      obtain ⟨q, rfl⟩ := hx'
      exact ⟨⟨q, (hP q).mpr (Subgroup.mem_centralizer_singleton_iff.mp hxC)⟩, rfl⟩
  rw [j2Cnt, ← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_finsetCard]
  rfl

theorem exists_pow_of_mem_zpowers {x v : GL (Fin 14) (ZMod 5)} (hx : orderOf x = 3)
    (hv : v ∈ Subgroup.zpowers x) : ∃ a < 3, x ^ a = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hv
  simpa using hv

theorem card_inf_centralizer_conj {G : Type*} [Group G] {K : Subgroup G} {h : G} (hh : h ∈ K)
    (z : G) : Nat.card ↥(K ⊓ Subgroup.centralizer ({h * z * h⁻¹} : Set G)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hmap : (K ⊓ Subgroup.centralizer ({z} : Set G)).map (MulAut.conj h).toMonoidHom =
      K ⊓ Subgroup.centralizer ({h * z * h⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hyK, hyz⟩, rfl⟩
      refine ⟨K.mul_mem (K.mul_mem hh hyK) (K.inv_mem hh), ?_⟩
      calc h * y * h⁻¹ * (h * z * h⁻¹) = h * (y * z) * h⁻¹ := by group
        _ = h * (z * y) * h⁻¹ := by rw [hyz]
        _ = _ := by group
    · rintro ⟨hxK, hxz⟩
      refine ⟨h⁻¹ * x * h, ⟨K.mul_mem (K.mul_mem (K.inv_mem hh) hxK) hh, ?_⟩, by group⟩
      calc h⁻¹ * x * h * z = h⁻¹ * (x * (h * z * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * z * h⁻¹) * x) * h := by rw [hxz]
        _ = _ := by group
  rw [← hmap]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).toEquiv).symm

theorem centralizer_inv_singleton {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer ({z⁻¹} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * z = z * (z⁻¹ * x) * z := by group
      _ = z * (x * z⁻¹) * z := by rw [h]
      _ = z * x := by group
  · intro h
    calc x * z⁻¹ = z⁻¹ * (z * x) * z⁻¹ := by group
      _ = z⁻¹ * (x * z) * z⁻¹ := by rw [h]
      _ = z⁻¹ * x := by group

theorem j2_P0 {K : Subgroup (GL (Fin 14) (ZMod 5))}
    (hK : (K : Set (GL (Fin 14) (ZMod 5))) = j2H0) (hcard : Nat.card K = 1152) :
    ∃ x1 x2 : GL (Fin 14) (ZMod 5), x1 ∈ K ∧ x2 ∈ K ∧ orderOf x1 = 3 ∧ orderOf x2 = 3 ∧
      Subgroup.zpowers x2 ≤ Subgroup.normalizer (Subgroup.zpowers x1 : Set (GL (Fin 14) (ZMod 5))) ∧
      Nat.card (Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 : Subgroup (GL (Fin 14) (ZMod 5))) = 9 ∧
      j2Cnt K x1 = 72 ∧ ∀ a < 3, ∀ b < 3, 0 < b → j2Cnt K (x1 ^ a * x2 ^ b) ≠ 72 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x1, hx1def⟩ : ∃ x : GL (Fin 14) (ZMod 5), x = j2DP 1 * j2TelE 3 := ⟨_, rfl⟩
  obtain ⟨x2, hx2def⟩ : ∃ x : GL (Fin 14) (ZMod 5), x = j2DP 3 * j2TelE 9 := ⟨_, rfl⟩
  have hc1 : glCode x1 = j2X1 := by
    rw [hx1def, glCode_mul, glCode_j2DP (by norm_num), glCode_j2TelE (by norm_num)]
    rfl
  have hc2 : glCode x2 = j2X2 := by
    rw [hx2def, glCode_mul, glCode_j2DP (by norm_num), glCode_j2TelE (by norm_num)]
    rfl
  obtain ⟨h13, h1ne, h23, hcomm, hdis⟩ := j2_x_check
  have hmemK : ∀ {s i : ℕ}, s < 9 → i < 128 → j2CP s * j2TelE i ∈ K := by
    intro s i hs hi
    rw [← SetLike.mem_coe, hK]
    exact ⟨s, hs, j2TelE i, j2TelE_mem i, rfl⟩
  have hx1K : x1 ∈ K := by
    have h := hmemK (s := 1) (i := 3) (by norm_num) (by norm_num)
    rwa [j2CP, show j2CR 1 = 0 from rfl, show j2CJ 1 = 1 from rfl, j2TelE_zero, one_mul,
      ← hx1def] at h
  have hx2K : x2 ∈ K := by
    have h := hmemK (s := 3) (i := 9) (by norm_num) (by norm_num)
    rwa [j2CP, show j2CR 3 = 0 from rfl, show j2CJ 3 = 3 from rfl, j2TelE_zero, one_mul,
      ← hx2def] at h
  have hcodePow : ∀ (u : GL (Fin 14) (ZMod 5)) (n : ℕ),
      glCode (u ^ n) = powC14 j2oneC n (glCode u) := fun u n => by
    rw [glCode_pow, j2_code_one]
  have hpow1 : x1 ^ 3 = 1 := eq_of_glCode (by rw [hcodePow, hc1, j2_code_one]; exact h13)
  have hne1 : x1 ≠ 1 := fun h => h1ne (by rw [← hc1, h, j2_code_one])
  have ho1 : orderOf x1 = 3 := orderOf_eq_prime hpow1 hne1
  have hpow2 : x2 ^ 3 = 1 := eq_of_glCode (by rw [hcodePow, hc2, j2_code_one]; exact h23)
  have hne2 : x2 ≠ 1 := by
    intro h
    apply hdis 0 (by norm_num) 1 (by norm_num) (by norm_num)
    rw [← hc1, ← hc2, ← hcodePow, ← hcodePow, h, pow_zero, one_pow]
  have ho2 : orderOf x2 = 3 := orderOf_eq_prime hpow2 hne2
  have hcp : ∀ a < 3, x1 ^ a * x2 = x2 * x1 ^ a := fun a ha =>
    eq_of_glCode (by
      rw [glCode_mul (x1 ^ a) x2, glCode_mul x2 (x1 ^ a), hcodePow, hc1, hc2]
      exact hcomm a ha)
  have hnorm : Subgroup.zpowers x2 ≤
      Subgroup.normalizer (Subgroup.zpowers x1 : Set (GL (Fin 14) (ZMod 5))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨a, ha, rfl⟩ := exists_pow_of_mem_zpowers ho1 hh
    exact hcp a ha
  have hdisj : Disjoint (Subgroup.zpowers x1) (Subgroup.zpowers x2) := by
    rw [Subgroup.disjoint_def]
    intro v h1 h2
    obtain ⟨a, ha, rfl⟩ := exists_pow_of_mem_zpowers ho1 h1
    obtain ⟨b, hb, hb'⟩ := exists_pow_of_mem_zpowers ho2 h2
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [pow_zero] at hb'
      exact hb'.symm
    · exact absurd (by rw [← hc1, ← hc2, ← hcodePow, ← hcodePow, hb']) (hdis a ha b hb hb0)
  have hP0 : Nat.card (Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 :
      Subgroup (GL (Fin 14) (ZMod 5))) = 9 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm
      hdisj, Nat.card_zpowers, Nat.card_zpowers, ho1, ho2]
  have hcntinv : ∀ z, j2Cnt K z⁻¹ = j2Cnt K z := fun z => by
    simp only [j2Cnt, centralizer_inv_singleton]
  have hcx1 : j2Cnt K x1 = 72 := by rw [j2_card_cent hK hcard, hc1]; exact j2_cent_check₁
  have hcx2 : j2Cnt K x2 = 36 := by rw [j2_card_cent hK hcard, hc2]; exact j2_cent_check₂
  have hcx3 : j2Cnt K (x1 * x2) = 9 := by
    rw [j2_card_cent hK hcard, glCode_mul x1 x2, hc1, hc2]; exact j2_cent_check₃
  have hcx4 : j2Cnt K (x1 * (x2 * x2)) = 36 := by
    rw [j2_card_cent hK hcard, glCode_mul x1 (x2 * x2), glCode_mul x2 x2, hc1, hc2]
    exact j2_cent_check₄
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := j2_rel_check
  have hzc : ∀ a b : ℕ, glCode (x1 ^ a * x2 ^ b) = j2ZC a b := fun a b => by
    rw [glCode_mul, hcodePow, hcodePow, hc1, hc2]
    rfl
  refine ⟨x1, x2, hx1K, hx2K, ho1, ho2, hnorm, hP0, hcx1, fun a ha b hb hb0 => ?_⟩
  have hinv : ∀ w, glCode (x1 ^ a * x2 ^ b) = glCode w → j2Cnt K (x1 ^ a * x2 ^ b) = j2Cnt K w :=
    fun w h => by rw [eq_of_glCode h]
  have hinv' : ∀ w, mul14 (j2ZC a b) (glCode w) = j2oneC →
      j2Cnt K (x1 ^ a * x2 ^ b) = j2Cnt K w := fun w h => by
    have e : x1 ^ a * x2 ^ b * w = 1 :=
      eq_of_glCode (by rw [glCode_mul (x1 ^ a * x2 ^ b) w, hzc, j2_code_one]; exact h)
    have e' : x1 ^ a * x2 ^ b = w⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [e', hcntinv]
  interval_cases b
  · interval_cases a
    · rw [hinv x2 (by rw [hzc, hc2]; exact r1), hcx2]
      omega
    · rw [hinv (x1 * x2) (by rw [hzc, glCode_mul x1 x2, hc1, hc2]; exact r3), hcx3]
      omega
    · rw [hinv' (x1 * (x2 * x2))
        (by rw [glCode_mul x1 (x2 * x2), glCode_mul x2 x2, hc1, hc2]; exact r6), hcx4]
      omega
  · interval_cases a
    · rw [hinv' x2 (by rw [hc2]; exact r2), hcx2]
      omega
    · rw [hinv (x1 * (x2 * x2))
        (by rw [hzc, glCode_mul x1 (x2 * x2), glCode_mul x2 x2, hc1, hc2]; exact r5), hcx4]
      omega
    · rw [hinv' (x1 * x2) (by rw [glCode_mul x1 x2, hc1, hc2]; exact r4), hcx3]
      omega

theorem j2_model_key {K : Subgroup (GL (Fin 14) (ZMod 5))}
    (hK : (K : Set (GL (Fin 14) (ZMod 5))) = j2H0) (hcard : Nat.card K = 1152)
    {Q : Subgroup (GL (Fin 14) (ZMod 5))} (hQK : Q ≤ K) (hQ : Nat.card Q = 9) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ j2Cnt K y₀ = 72 ∧
      ∀ y ∈ Q, j2Cnt K y = 72 → y ∈ Subgroup.zpowers y₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x1, x2, hx1K, hx2K, ho1, ho2, hnorm, hP0, hcx1, hbad⟩ := j2_P0 hK hcard
  obtain ⟨P0, hP0def⟩ : ∃ R : Subgroup (GL (Fin 14) (ZMod 5)),
      R = Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2 := ⟨_, rfl⟩
  rw [← hP0def] at hP0
  have hP0K : P0 ≤ K := by
    rw [hP0def]
    exact sup_le (Subgroup.zpowers_le.mpr hx1K) (Subgroup.zpowers_le.mpr hx2K)
  have hsyl : ∀ {R : Subgroup (GL (Fin 14) (ZMod 5))}, R ≤ K → Nat.card R = 9 →
      IsPGroup 3 (R.subgroupOf K) ∧ ¬ 3 ∣ (R.subgroupOf K).index := by
    intro R hRK hR
    have hc : Nat.card (R.subgroupOf K) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hR]
    refine ⟨IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), ?_⟩
    have h := (R.subgroupOf K).card_mul_index
    rw [hc, hcard] at h
    omega
  obtain ⟨hQp, hQi⟩ := hsyl hQK hQ
  obtain ⟨hPp, hPi⟩ := hsyl hP0K hP0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) (hPp.toSylow hPi) (hQp.toSylow hQi)
  have hmemQ : ∀ x : K, x ∈ Q.subgroupOf K ↔ (MulAut.conj g)⁻¹ x ∈ P0.subgroupOf K := by
    intro x
    have h : x ∈ ((g • hPp.toSylow hPi : Sylow 3 K) : Subgroup K) ↔ x ∈ Q.subgroupOf K := by
      rw [hg]
      rfl
    rw [← h, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hgQ : ∀ y ∈ P0, (g : GL (Fin 14) (ZMod 5)) * y * (g : GL (Fin 14) (ZMod 5))⁻¹ ∈ Q := by
    intro y hy
    have h := (hmemQ (MulAut.conj g ⟨y, hP0K hy⟩)).mpr (by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      exact hy)
    exact h
  have hgQ' : ∀ y ∈ Q, (g : GL (Fin 14) (ZMod 5))⁻¹ * y * (g : GL (Fin 14) (ZMod 5)) ∈ P0 := by
    intro y hy
    have h := (hmemQ ⟨y, hQK hy⟩).mp hy
    rw [MulAut.conj_inv_apply] at h
    exact h
  have hcntg : ∀ z, j2Cnt K ((g : GL (Fin 14) (ZMod 5)) * z * (g : GL (Fin 14) (ZMod 5))⁻¹) =
      j2Cnt K z := fun z => card_inf_centralizer_conj g.2 z
  have hP0max : ∀ z ∈ P0, j2Cnt K z = 72 → z ∈ Subgroup.zpowers x1 := by
    intro z hz hcz
    rw [hP0def] at hz
    obtain ⟨u, hu, v, hv, rfl⟩ := (CFSG.Walter.W67.mem_sup_iff_of_le_normalizer hnorm).mp hz
    obtain ⟨a, ha, rfl⟩ := exists_pow_of_mem_zpowers ho1 hu
    obtain ⟨b, hb, rfl⟩ := exists_pow_of_mem_zpowers ho2 hv
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [pow_zero, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · exact absurd hcz (hbad a ha b hb hb0)
  refine ⟨(g : GL (Fin 14) (ZMod 5)) * x1 * (g : GL (Fin 14) (ZMod 5))⁻¹,
    hgQ x1 (by rw [hP0def]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x1)), ?_, ?_, ?_⟩
  · rw [← ho1]
    exact MulEquiv.orderOf_eq (MulAut.conj (g : GL (Fin 14) (ZMod 5))) x1
  · rw [hcntg, hcx1]
  · intro y hy hcy
    have hz := hgQ' y hy
    have hcz : j2Cnt K ((g : GL (Fin 14) (ZMod 5))⁻¹ * y * (g : GL (Fin 14) (ZMod 5))) = 72 := by
      have e := hcntg ((g : GL (Fin 14) (ZMod 5))⁻¹ * y * (g : GL (Fin 14) (ZMod 5)))
      rw [show (g : GL (Fin 14) (ZMod 5)) * ((g : GL (Fin 14) (ZMod 5))⁻¹ * y *
          (g : GL (Fin 14) (ZMod 5))) * (g : GL (Fin 14) (ZMod 5))⁻¹ = y by group] at e
      rw [← e]
      exact hcy
    have hm : (MulAut.conj (g : GL (Fin 14) (ZMod 5))).toMonoidHom
        ((g : GL (Fin 14) (ZMod 5))⁻¹ * y * (g : GL (Fin 14) (ZMod 5))) ∈
          (Subgroup.zpowers x1).map (MulAut.conj (g : GL (Fin 14) (ZMod 5))).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (hP0max _ hz hcz)
    rw [MonoidHom.map_zpowers] at hm
    have e : (MulAut.conj (g : GL (Fin 14) (ZMod 5))).toMonoidHom
        ((g : GL (Fin 14) (ZMod 5))⁻¹ * y * (g : GL (Fin 14) (ZMod 5))) = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e] at hm
    exact hm

@[expose] noncomputable def carrierJ2Equiv : NativeSporadic.Carrier .J2 ≃* NativeSporadic.J2 :=
  MulEquiv.refl _

theorem card_inf_centralizer_map {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (hφ : Function.Injective φ) (H : Subgroup X) (y : X) :
    Nat.card ↥(H.map φ ⊓ Subgroup.centralizer ({φ y} : Set Y)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({y} : Set X)) := by
  have hmap : (H ⊓ Subgroup.centralizer ({y} : Set X)).map φ =
      H.map φ ⊓ Subgroup.centralizer ({φ y} : Set Y) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxH, hxy⟩, rfl⟩
      exact ⟨⟨x, hxH, rfl⟩, by rw [← map_mul, hxy, map_mul]⟩
    · rintro ⟨⟨x, hxH, rfl⟩, hxy⟩
      refine ⟨x, ⟨hxH, hφ ?_⟩, rfl⟩
      rw [map_mul, map_mul, hxy]
  rw [← hmap]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hφ).toEquiv).symm

theorem card_inf_centralizer_conj' {G : Type*} [Group G] {H : Subgroup G} {t : G}
    (ht : ∀ x ∈ H, t * x * t⁻¹ ∈ H) (ht' : ∀ x ∈ H, t⁻¹ * x * t ∈ H) (z : G) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t * z * t⁻¹} : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hmap : (H ⊓ Subgroup.centralizer ({z} : Set G)).map (MulAut.conj t).toMonoidHom =
      H ⊓ Subgroup.centralizer ({t * z * t⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hyH, hyz⟩, rfl⟩
      refine ⟨ht y hyH, ?_⟩
      calc t * y * t⁻¹ * (t * z * t⁻¹) = t * (y * z) * t⁻¹ := by group
        _ = t * (z * y) * t⁻¹ := by rw [hyz]
        _ = _ := by group
    · rintro ⟨hxH, hxz⟩
      refine ⟨t⁻¹ * x * t, ⟨ht' x hxH, ?_⟩, by group⟩
      calc t⁻¹ * x * t * z = t⁻¹ * (x * (t * z * t⁻¹)) * t := by group
        _ = t⁻¹ * ((t * z * t⁻¹) * x) * t := by rw [hxz]
        _ = _ := by group
  rw [← hmap]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj t).injective).toEquiv).symm

theorem j2_embedding {X : Type} [Group X] (e : X ≃* NativeSporadic.Carrier .J2) :
    ∃ φ : X →* GL (Fin 14) (ZMod 5), Function.Injective φ ∧ (∀ x, φ x ∈ seedGroup) ∧
      ∀ y ∈ seedGroup, ∃ x, φ x = y := by
  obtain ⟨ψ, -⟩ : ∃ ψ : X ≃* ↥seedGroup, ψ = (e.trans carrierJ2Equiv).trans nativeEquiv :=
    ⟨_, rfl⟩
  refine ⟨(Subgroup.subtype _).comp (ψ : X →* ↥seedGroup), fun a b h => ψ.injective
    (Subgroup.subtype_injective _ h), fun x => (ψ x).2, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem noE9Config_j2 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ₀, hφ₀, hφ₀mem, hφ₀surj⟩ := j2_embedding e
  have hHL : P ⊔ (T ⊓ L) ≤ L := E9Config.sup_inf_le hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨TL, hTLdef⟩ : ∃ R : Subgroup ↥L, R = j2T.comap φ₀ := ⟨_, rfl⟩
  have hTLmap : TL.map φ₀ = j2T := by
    rw [hTLdef]
    refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφ₀surj y (j2T_le hy)
    exact ⟨x, hy, rfl⟩
  have hTLc : Nat.card TL = 128 := by
    rw [← card_j2T, ← hTLmap]
    exact Nat.card_congr (TL.equivMapOfInjective _ hφ₀).toEquiv
  have hTLp : IsPGroup 2 TL := IsPGroup.of_card (n := 7) (by rw [hTLc]; norm_num)
  have hUp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨Q, hQ⟩ := hTLp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) (hUp.toSylow hS.2.2) Q
  have hQU : ∀ x ∈ (Q : Subgroup ↥L), (MulAut.conj g)⁻¹ x ∈ (T ⊓ L).subgroupOf L := by
    intro x hx
    have hx' : x ∈ ((g • hUp.toSylow hS.2.2 : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hcardQ : Nat.card ((T ⊓ L).subgroupOf L) = Nat.card (Q : Subgroup ↥L) := by
    have := congrArg (fun R : Sylow 2 ↥L => Nat.card (R : Subgroup ↥L)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow] at this
    rw [← this, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _
      (MulAut.conj g).injective).toEquiv
  obtain ⟨φ, hφdef⟩ : ∃ φ : ↥L →* GL (Fin 14) (ZMod 5),
      φ = φ₀.comp (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hφ : Function.Injective φ := by
    rw [hφdef]
    exact hφ₀.comp (MulAut.conj g).injective
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (GL (Fin 14) (ZMod 5)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  have hTK : j2T ≤ K := by
    intro y hy
    rw [← hTLmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hu := hQU x (hQ hx)
    rw [hKdef]
    refine ⟨(MulAut.conj g)⁻¹ x, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hu)), ?_⟩
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply,
      mul_inv_cancel, MulAut.one_apply]
  have hKM : K ≤ seedGroup := by
    rw [hKdef, hφdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφ₀mem _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hHc := E9Config.card_sup_inf hcfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have h5 : ¬ 5 ∣ Nat.card K := by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow (Or.inl rfl)
  have h7 : ¬ 7 ∣ Nat.card K := by
    rw [hKc, hHc, hk]
    exact not_dvd_nine_mul_two_pow (Or.inr (Or.inl rfl))
  have hle := j2_card_le hTK hKM h5 h7
  have hTU : 128 ≤ Nat.card (T ⊓ L : Subgroup A) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hcardQ, ← hTLc]
    exact Subgroup.card_le_of_le hQ
  have hK1152 : Nat.card K = 1152 := by
    rw [card_j2T] at hle
    rw [hKc, hHc] at hle ⊢
    omega
  have hKset := j2_eq_H0 hTK hKM h5 h7 hK1152
  obtain ⟨PK, hPKdef⟩ : ∃ R : Subgroup (GL (Fin 14) (ZMod 5)), R = (P.subgroupOf L).map φ :=
    ⟨_, rfl⟩
  have hPKK : PK ≤ K := by
    rw [hPKdef, hKdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_left)
  have hPKc : Nat.card PK = 9 := by
    rw [hPKdef, ← Nat.card_congr ((P.subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  obtain ⟨y₀', hy₀'P, hy₀'o, hy₀'c, hy₀'max⟩ := j2_model_key hKset hK1152 hPKK hPKc
  rw [hPKdef] at hy₀'P
  obtain ⟨x₀, hx₀P, rfl⟩ := hy₀'P
  have hx₀P' : (x₀ : A) ∈ P := Subgroup.mem_subgroupOf.mp hx₀P
  have hcA : ∀ y : ↥L, Nat.card ↥((P ⊔ (T ⊓ L)) ⊓ Subgroup.centralizer ({(y : A)} : Set A)) =
      j2Cnt K (φ y) := by
    intro y
    have h1 := card_inf_centralizer_map L.subtype L.subtype_injective
      ((P ⊔ (T ⊓ L)).subgroupOf L) y
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHL] at h1
    rw [show (y : A) = L.subtype y from rfl, h1, j2Cnt, hKdef,
      card_inf_centralizer_map φ hφ]
  have hL := hcfg.normal
  have htH : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ P ⊔ (T ⊓ L),
      t * x * t⁻¹ ∈ P ⊔ (T ⊓ L) := by
    intro t ht
    refine conj_mem_sup (fun p hp => Subgroup.mem_sup_left ?_)
      (fun s hs => Subgroup.mem_sup_right ?_)
    · exact (Subgroup.mem_normalizer_iff.mp ht.2 p).1 hp
    · exact ⟨T.mul_mem (T.mul_mem ht.1 hs.1) (T.inv_mem ht.1), hL.conj_mem s hs.2 t⟩
  have hinvT : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t⁻¹ ∈ T ⊓ Subgroup.normalizer (P : Set A) :=
    fun t ht => (T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht
  have hconj : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t * (x₀ : A) * t⁻¹ ∈ Subgroup.zpowers (x₀ : A) := by
    intro t ht
    have hyP : t * (x₀ : A) * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp ht.2 _).1 hx₀P'
    have hyL : t * (x₀ : A) * t⁻¹ ∈ L := hcfg.le hyP
    have hc : j2Cnt K (φ ⟨t * (x₀ : A) * t⁻¹, hyL⟩) = 72 := by
      rw [← hcA, ← hy₀'c, ← hcA]
      exact card_inf_centralizer_conj' (H := P ⊔ (T ⊓ L)) (htH t ht)
        (fun x hx => by simpa using htH t⁻¹ (hinvT t ht) x hx) (x₀ : A)
    have hmem : φ ⟨t * (x₀ : A) * t⁻¹, hyL⟩ ∈ PK := by
      rw [hPKdef]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hyP, rfl⟩
    have hz := hy₀'max _ hmem hc
    rw [← MonoidHom.map_zpowers] at hz
    obtain ⟨z, hz, hzφ⟩ := hz
    have hz' : (z : A) = t * (x₀ : A) * t⁻¹ := by rw [hφ hzφ]
    rw [← hz']
    have := Subgroup.mem_map_of_mem L.subtype hz
    rwa [MonoidHom.map_zpowers] at this
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers (x₀ : A) : Set A) := by
    intro t ht
    have hpow : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ n ∈ Subgroup.zpowers (x₀ : A),
        s * n * s⁻¹ ∈ Subgroup.zpowers (x₀ : A) := by
      intro s hs n hn
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have e1 : s * (x₀ : A) ^ m * s⁻¹ = (s * (x₀ : A) * s⁻¹) ^ m := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      rw [e1]
      exact Subgroup.zpow_mem _ (hconj s hs) m
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hpow t ht n
    · intro hn
      have := hpow t⁻¹ (hinvT t ht) _ hn
      rwa [show t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n by group] at this
  have hord : orderOf (x₀ : A) = 3 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφ x₀]
    exact hy₀'o
  rcases hcfg.irred _ (Subgroup.zpowers_le.mpr hx₀P') hnorm with h | h
  · have h1 : (x₀ : A) = 1 := by
      have := Subgroup.mem_zpowers (x₀ : A)
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [h1, orderOf_one] at hord
    omega
  · have := Nat.card_zpowers (x₀ : A)
    rw [h, hcfg.card, hord] at this
    omega

theorem orderThree_j2 :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  intro X _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : ↥seedGroup := ⟨uB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply eq_of_glCode
    rw [Subgroup.coe_pow, glCode_pow, Subgroup.coe_one, j2_code_one]
    show powC14 j2oneC 3 (glCode uB) = j2oneC
    rw [j2_code_b]
    exact j2_three_check.1
  have hx1 : x ≠ 1 := by
    intro h
    apply j2_three_check.2
    have := congrArg (fun y : ↥seedGroup => glCode (y : GL (Fin 14) (ZMod 5))) h
    simp only [Subgroup.coe_one] at this
    rw [← j2_code_b, ← j2_code_one]
    exact this
  rw [Nat.card_congr ((e.trans carrierJ2Equiv).trans nativeEquiv).toEquiv,
    ← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard x

end CFSG.Quasithin.F134
