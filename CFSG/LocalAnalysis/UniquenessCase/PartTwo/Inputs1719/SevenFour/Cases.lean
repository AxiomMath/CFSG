module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.ModelPGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.ModelGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.ModelAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81 (dihedralDeg)
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {p e : ℕ}

private theorem mem_normalizer_of_forall_conj_eq_pow {E : Subgroup (MulAut W)} {n : MulAut W}
    {k : ℕ} (hn : ∀ x ∈ E, n * x * n⁻¹ = x ^ k) :
    n ∈ normalizer (E : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : E.map (MulAut.conj n).toMonoidHom ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (MulAut.conj n).toMonoidHom x = x ^ k := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hn x hx
    rw [hx']
    exact E.pow_mem hx k
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj n).injective).symm)

private theorem pow_mod_four_eq_one_of_even {p e : ℕ} (hp : Odd p) (he : Even e) :
    p ^ e % 4 = 1 := by
  have h4 : 4 ∣ 2 * (p - 1) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by omega⟩
  have h : 4 ∣ p ^ e - 1 := h4.trans (two_mul_sub_one_dvd_pow_sub_one hp he)
  obtain ⟨m, hm⟩ := h
  have hppos : 0 < p := by obtain ⟨k, hk⟩ := hp; omega
  have hpos : 0 < p ^ e := pow_pos hppos e
  have hpe : p ^ e = 4 * m + 1 := by omega
  rw [hpe]
  omega

private theorem eleven_le_of_nine_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : 9 < p) :
    11 ≤ p := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  omega

omit [Finite W] in
private theorem ne_bot_of_card_eq_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    {E : Subgroup (MulAut W)} (hcard : Nat.card E = p ^ e) : E ≠ ⊥ := by
  intro h
  have h1 : Nat.card E = 1 := by rw [h, Subgroup.card_bot]
  have h2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  omega

theorem dParam_mul_orbLen_le_rk (hW : ∀ w : W, w ^ 2 = 1) (hM : LieModel ↥L .PSL 2 p e)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsSylowIn p E L) :
    dParam p * orbLen p e ≤ rk ↥(commSub ⊤ E) := by
  have hp : p.Prime := hM.admissible.1
  have he : 0 < e := hM.admissible.2.1
  obtain ⟨hElem, hcard⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  have hE1 : E ≠ ⊥ := ne_bot_of_card_eq_prime_pow hp he hcard
  have hS : orbLen p e ≤ (hypSupp p E).ncard :=
    le_ncard_hypSupp hW hp hp2 hElem hE1 (N := L ⊓ normalizer (E : Set (MulAut W)))
      inf_le_right fun D hD => orbLen_le_ncard_hypOrbit hM hp2 hE hD
  refine (Nat.mul_le_mul_left (dParam p) hS).trans ?_
  exact mul_ncard_hypSupp_le hW hp hp2 hElem
    fun D hD => dParam_le_rk_hypPart hW hp hp2 hElem hD

theorem dihedralDeg_mul_orbLen_le_rk (hW : ∀ w : W, w ^ 2 = 1) (hM : LieModel ↥L .PSL 2 p e)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsSylowIn p E L) {g : MulAut W}
    (hinv : ∀ x ∈ E, g * x * g⁻¹ = x⁻¹) :
    dihedralDeg p * orbLen p e ≤ rk ↥(commSub ⊤ E) := by
  have hp : p.Prime := hM.admissible.1
  have he : 0 < e := hM.admissible.2.1
  obtain ⟨hElem, hcard⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  have hE1 : E ≠ ⊥ := ne_bot_of_card_eq_prime_pow hp he hcard
  have hS : orbLen p e ≤ (hypSupp p E).ncard :=
    le_ncard_hypSupp hW hp hp2 hElem hE1 (N := L ⊓ normalizer (E : Set (MulAut W)))
      inf_le_right fun D hD => orbLen_le_ncard_hypOrbit hM hp2 hE hD
  refine (Nat.mul_le_mul_left (dihedralDeg p) hS).trans ?_
  exact mul_ncard_hypSupp_le hW hp hp2 hElem
    fun D hD => dihedralDeg_le_rk_hypPart hW hp hp2 hElem hD hinv

theorem dParam_mul_le_rk_of_isPGL2 (hW : ∀ w : W, w ^ 2 = 1) (hM : LieModel ↥L .PSL 2 p e)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hLA : L ≤ A) (hA : F6.IsPGL2 (p ^ e) ↥A)
    {E : Subgroup (MulAut W)} (hE : IsSylowIn p E L) :
    dParam p * ((p ^ e - 1) / (p - 1)) ≤ rk ↥(commSub ⊤ E) := by
  have hp : p.Prime := hM.admissible.1
  have he : 0 < e := hM.admissible.2.1
  obtain ⟨hElem, hcard⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  have hE1 : E ≠ ⊥ := ne_bot_of_card_eq_prime_pow hp he hcard
  have hS : (p ^ e - 1) / (p - 1) ≤ (hypSupp p E).ncard :=
    le_ncard_hypSupp hW hp hp2 hElem hE1 (N := A ⊓ normalizer (E : Set (MulAut W)))
      inf_le_right fun D hD => ncard_hypOrbit_of_isPGL2 hM hp2 hLA hA hE hD
  refine (Nat.mul_le_mul_left (dParam p) hS).trans ?_
  exact mul_ncard_hypSupp_le hW hp hp2 hElem
    fun D hD => dParam_le_rk_hypPart hW hp hp2 hElem hD

theorem dihedralDeg_mul_le_rk_of_isPGL2 (hW : ∀ w : W, w ^ 2 = 1)
    (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hA : F6.IsPGL2 (p ^ e) ↥A) {E : Subgroup (MulAut W)} (hE : IsSylowIn p E L)
    {g : MulAut W} (hinv : ∀ x ∈ E, g * x * g⁻¹ = x⁻¹) :
    dihedralDeg p * ((p ^ e - 1) / (p - 1)) ≤ rk ↥(commSub ⊤ E) := by
  have hp : p.Prime := hM.admissible.1
  have he : 0 < e := hM.admissible.2.1
  obtain ⟨hElem, hcard⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  have hE1 : E ≠ ⊥ := ne_bot_of_card_eq_prime_pow hp he hcard
  have hS : (p ^ e - 1) / (p - 1) ≤ (hypSupp p E).ncard :=
    le_ncard_hypSupp hW hp hp2 hElem hE1 (N := A ⊓ normalizer (E : Set (MulAut W)))
      inf_le_right fun D hD => ncard_hypOrbit_of_isPGL2 hM hp2 hLA hA hE hD
  refine (Nat.mul_le_mul_left (dihedralDeg p) hS).trans ?_
  exact mul_ncard_hypSupp_le hW hp hp2 hElem
    fun D hD => dihedralDeg_le_rk_hypPart hW hp hp2 hElem hD hinv

theorem rk_commSub_le_two_mul_of_inverts (hW : ∀ w : W, w ^ 2 = 1) (hM : LieModel ↥L .PSL 2 p e)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsSylowIn p E L) {t : MulAut W}
    (ht : orderOf t = 2) (hinv : ∀ x ∈ E, t * x * t⁻¹ = x⁻¹) :
    rk ↥(commSub ⊤ E) ≤ 2 * rkIdx (fixV (zpowers t)) :=
  rk_commSub_le_two_mul_rkIdx hW hM.admissible.1 hp2
    (isElemAbelian_of_isSylowIn hM hp2 hE).1 ht hinv

theorem rk_commSub_le_three_mul_of_induces
    (hW : ∀ w : W, w ^ 2 = 1) (_hLY : L ≤ Y) (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2)
    (hq : 9 < p ^ e) {t : MulAut W} (ht : orderOf t = 2)
    (hind : InducesPGL2Involution (p ^ e) Y L t) {E : Subgroup (MulAut W)}
    (hE : IsSylowIn p E L) :
    rk ↥(commSub ⊤ E) ≤ 3 * rkIdx (fixV (zpowers t)) := by
  have hp : p.Prime := hM.admissible.1
  have hElem : IsElemAbelian p E := (isElemAbelian_of_isSylowIn hM hp2 hE).1
  have hEL : E ≤ L := hE.le
  by_cases htL : t ∈ L
  · obtain ⟨x, hx, y, hy, z, hz, hcl⟩ := exists_three_conj_closure_eq hM hp2 hq htL ht
    have hEH : E ≤ closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)) := by
      rw [hcl]; exact hEL
    exact (rk_commSub_le_rkIdx_fixV hW hp hp2 hElem hEH).trans
      (rkIdx_fixV_closure_le_three_mul hW ht)
  · rcases hind with h | ⟨A, -, hLA, htA, hA⟩
    · exact absurd h htL
    obtain ⟨x, hx, y, hy, z, hz, hcl⟩ :=
      exists_three_conj_closure_eq_of_isPGL2 hM hp2 hq hLA hA htA htL ht
    have hEH : E ≤ closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)) := by
      rw [hcl]; exact hEL.trans le_sup_left
    exact (rk_commSub_le_rkIdx_fixV hW hp hp2 hElem hEH).trans
      (rkIdx_fixV_closure_le_three_mul hW ht)

private theorem eq_five_and_two_of_pow_eq_twentyFive {p e : ℕ} (hp : p.Prime)
    (h : p ^ e = 25) : p = 5 ∧ e = 2 := by
  have h25 : p ^ e = 5 ^ 2 := by rw [h]; norm_num
  have h5 : p = 5 := by
    refine Nat.prime_eq_prime_of_dvd_pow (m := 2) hp Nat.prime_five ?_
    rw [← h25]
    exact dvd_pow_self p (by rintro rfl; norm_num at h)
  have h2 : p ^ e = p ^ 2 := by simpa [h5] using h25
  exact ⟨h5, Nat.pow_right_injective hp.two_le h2⟩

theorem four_le_of_four_primes (hW : ∀ w : W, w ^ 2 = 1)
    (hLY : L ≤ Y) (hM : LieModel ↥L .PSL 2 p e) (he1 : e = 1)
    (hp4 : p = 17 ∨ p = 31 ∨ p = 73 ∨ p = 127) {t : MulAut W} (ht : orderOf t = 2)
    (hind : InducesPGL2Involution (p ^ e) Y L t)
    (hns : ¬ ∃ E : Subgroup (MulAut W), IsSylowIn p E L ∧ ∀ x ∈ E, t * x * t⁻¹ = x⁻¹) :
    4 ≤ rkIdx (fixV (zpowers t)) := by
  subst he1
  have hp : p.Prime := hM.admissible.1
  have hp2 : p ≠ 2 := by rcases hp4 with rfl | rfl | rfl | rfl <;> norm_num
  suffices h : ¬ rkIdx (fixV (zpowers t)) ≤ 3 by omega
  intro hmle
  obtain ⟨E, hE⟩ := exists_isSylowIn hM
  obtain ⟨hElem, hcardE⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  have hcardE' : Nat.card E = p := by simpa using hcardE
  have hcardE1 : Nat.card E = p ^ 1 := by simpa using hcardE
  have hE1 : E ≠ ⊥ := ne_bot_of_card_eq_prime_pow (e := 1) hp (by omega) hcardE1
  have hMbot : commSub ⊤ E ≠ ⊥ := by
    intro hbot
    have htop : fixV E = ⊤ := top_le_iff.mp (commSub_eq_bot_iff.mp hbot)
    refine hE1 ((Subgroup.eq_bot_iff_forall E).mpr ?_)
    intro e he
    ext w
    have hw : w ∈ fixV E := by rw [htop]; exact Subgroup.mem_top w
    simpa using (mem_fixV.mp hw) e he
  obtain hEbot | ⟨x, hxE, hx1⟩ := Subgroup.bot_or_exists_ne_one E
  · exact absurd hEbot hE1
  have hxord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := by
      have := Subgroup.orderOf_dvd_natCard E hxE
      rwa [hcardE'] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  have hzE : zpowers x = E := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxE) ?_
    rw [Nat.card_zpowers, hxord, hcardE']
  have hfix : commSub ⊤ E ⊓ fixV (zpowers x) = ⊥ := by
    rw [hzE]
    exact commSub_inf_fixV_eq_bot hW hp hp2 hElem
  have hMx : ∀ m ∈ commSub ⊤ E, x m ∈ commSub ⊤ E := fun m hm =>
    mem_commSub_of_mem_normalizer (Subgroup.le_normalizer hxE) hm
  have hq9 : 9 < p ^ 1 := by rcases hp4 with rfl | rfl | rfl | rfl <;> norm_num
  have hle3 := rk_commSub_le_three_mul_of_induces hW hLY hM hp2 hq9 ht hind hE
  have hd : 9 < 2 * dParam p := by
    rcases hp4 with rfl | rfl | rfl | rfl
    · have := dParam_eq_of_small.2.2.2.1; omega
    · have := dParam_eq_of_small.2.2.2.2.1; omega
    · have := dParam_eq_of_small.2.2.2.2.2.1; omega
    · have := dParam_eq_of_small.2.2.2.2.2.2; omega
  have hlt : rk ↥(commSub ⊤ E) < 2 * dParam p := by omega
  rcases hp4 with rfl | rfl | rfl | rfl
  ·
    have hq4 : 17 ^ 1 % 4 = 1 := by norm_num
    have htL : t ∉ L := by
      intro htL
      obtain ⟨E', hE', hinv'⟩ := exists_inverted_isSylowIn hM hp2 hq4 htL ht
      exact hns ⟨E', hE', hinv'⟩
    rcases hind with h | ⟨A, hAY, hLA, htA, hA⟩
    · exact absurd h htL
    obtain ⟨n, -, hnpow⟩ :=
      exists_conj_eq_pow_of_isPGL2 hM hp2 hLA hA hE (c := 3) (by norm_num)
    refine false_of_conj_eq_pow hW hp hp2 hxord hMbot hMx ?_ hfix hlt (hnpow x hxE) ?_
    · exact fun m hm =>
        mem_commSub_of_mem_normalizer (mem_normalizer_of_forall_conj_eq_pow (k := 3) hnpow) hm
    · simpa using not_two_pow_eq.2.2.2
  ·
    obtain ⟨n, -, hnpow⟩ := exists_conj_eq_pow_sq hM hp2 hE (c := 3) (by norm_num)
    have hnpow' : ∀ y ∈ E, n * y * n⁻¹ = y ^ 9 := by
      intro y hy
      have h := hnpow y hy
      rwa [show (3 : ℕ) ^ 2 = 9 by norm_num] at h
    refine false_of_conj_eq_pow hW hp hp2 hxord hMbot hMx ?_ hfix hlt (hnpow' x hxE) ?_
    · exact fun m hm =>
        mem_commSub_of_mem_normalizer (mem_normalizer_of_forall_conj_eq_pow (k := 9) hnpow') hm
    · simpa using not_two_pow_eq.1
  ·
    obtain ⟨n, -, hnpow⟩ := exists_conj_eq_pow_sq hM hp2 hE (c := 3) (by norm_num)
    have hnpow' : ∀ y ∈ E, n * y * n⁻¹ = y ^ 9 := by
      intro y hy
      have h := hnpow y hy
      rwa [show (3 : ℕ) ^ 2 = 9 by norm_num] at h
    refine false_of_conj_eq_pow hW hp hp2 hxord hMbot hMx ?_ hfix hlt (hnpow' x hxE) ?_
    · exact fun m hm =>
        mem_commSub_of_mem_normalizer (mem_normalizer_of_forall_conj_eq_pow (k := 9) hnpow') hm
    · simpa using not_two_pow_eq.2.1
  ·
    obtain ⟨n, -, hnpow⟩ := exists_conj_eq_pow_sq hM hp2 hE (c := 3) (by norm_num)
    have hnpow' : ∀ y ∈ E, n * y * n⁻¹ = y ^ 9 := by
      intro y hy
      have h := hnpow y hy
      rwa [show (3 : ℕ) ^ 2 = 9 by norm_num] at h
    refine false_of_conj_eq_pow hW hp hp2 hxord hMbot hMx ?_ hfix hlt (hnpow' x hxE) ?_
    · exact fun m hm =>
        mem_commSub_of_mem_normalizer (mem_normalizer_of_forall_conj_eq_pow (k := 9) hnpow') hm
    · simpa using not_two_pow_eq.2.2.1

omit [Finite W] in
private theorem mul_ncard_le_sum_rk_hypPart {c : ℕ} {E : Subgroup (MulAut W)}
    (T : Set (Subgroup (MulAut W))) (hTfin : T.Finite)
    (hrank : ∀ D ∈ T, c ≤ rk ↥(hypPart E D)) :
    c * T.ncard ≤ ∑ D ∈ hTfin.toFinset, rk ↥(hypPart E D) := by
  have hconst : ∑ D ∈ hTfin.toFinset, c = hTfin.toFinset.card * c :=
    Finset.sum_const_nat fun _ _ => rfl
  have h1 : hTfin.toFinset.card * c ≤ ∑ D ∈ hTfin.toFinset, rk ↥(hypPart E D) := by
    rw [← hconst]
    exact Finset.sum_le_sum fun D hD => hrank D (hTfin.mem_toFinset.mp hD)
  have hcard : hTfin.toFinset.card = T.ncard := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  rwa [hcard, Nat.mul_comm] at h1

theorem field_bounds (hW : ∀ w : W, w ^ 2 = 1) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hF : UC22.Fstar Y = L) (hM : LieModel ↥L .PSL 2 p e) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 9 < p ^ e) {t : MulAut W} (htY : t ∈ Y) (ht : orderOf t = 2)
    (hnind : ¬ InducesPGL2Involution (p ^ e) Y L t) :
    4 ≤ rkIdx (fixV (zpowers t)) ∧ (p ^ e ≠ 25 → 8 ≤ rkIdx (fixV (zpowers t))) := by
  unfold InducesPGL2Involution at hnind
  rw [not_or] at hnind
  obtain ⟨htL, hA⟩ := hnind
  obtain ⟨hev, E, hE, htE, hC⟩ := field_type_of_not_mem hLY hLn hF hM hp2 htY ht htL hA
  have he0 : 0 < e := hM.admissible.2.1
  obtain ⟨f, hf⟩ := hev
  have hf2 : e = 2 * f := by omega
  have hfpos : 0 < f := by omega
  have hfe : e / 2 = f := by omega
  obtain ⟨hElem, hcardE0⟩ := isElemAbelian_of_isSylowIn hM hp2 hE
  have hE1 : E ≠ ⊥ := ne_bot_of_card_eq_prime_pow hp he0 hcardE0
  have hcardE : Nat.card E = p ^ (2 * f) := by rw [← hf2]; exact hcardE0
  have hC' : Nat.card ↥(E ⊓ centralizer {t}) = p ^ f := by rw [hC, hfe]
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have htodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq2 : 9 < (p ^ f) ^ 2 := by
    rw [hf2] at hq
    rwa [mul_comm 2 f, pow_mul] at hq
  have hrge4 : 4 ≤ p ^ f := by
    by_contra h
    push Not at h
    nlinarith
  set S : Set (Subgroup (MulAut W)) := hypSupp p E with hSdef
  set F : Set (Subgroup (MulAut W)) := fixedHyp p E t with hFdef
  set T : Set (Subgroup (MulAut W)) := S \ F with hTdef
  have hSfin : S.Finite := by
    rw [hSdef]
    exact (finite_hyperplanes p E).subset fun D hD => hD.1
  have hFfin : F.Finite := by
    rw [hFdef]
    exact (finite_hyperplanes p E).subset fun D hD => hD.1
  have hTfin : T.Finite := hSfin.subset Set.diff_subset
  have horb : orbLen p e ≤ S.ncard := by
    rw [hSdef]
    exact le_ncard_hypSupp hW hp hp2 hElem hE1 (N := L ⊓ normalizer (E : Set (MulAut W)))
      inf_le_right fun D hD => orbLen_le_ncard_hypOrbit hM hp2 hE hD
  have hfixle : F.ncard ≤ 2 * ((p ^ f - 1) / (p - 1)) := by
    rw [hFdef]
    exact ncard_fixedHyp_le hp hp2 hElem hcardE ht2 htE hC'
  have hTle : (p ^ (2 * f) - 1) / (2 * (p - 1)) - 2 * ((p ^ f - 1) / (p - 1)) ≤ T.ncard := by
    have h1 : S.ncard - F.ncard ≤ T.ncard := by
      rw [hTdef]
      exact Set.le_ncard_sdiff (s := F) (t := S) hFfin
    have h2 : orbLen p e = (p ^ (2 * f) - 1) / (2 * (p - 1)) := by
      rw [orbLen, if_pos (show Even e from ⟨f, hf⟩), hf2]
    omega
  have hTgood : ∀ D ∈ T, D ∈ hyperplanes p E ∧ D.map (MulAut.conj t).toMonoidHom ≠ D := by
    intro D hD
    rw [hTdef] at hD
    have hDS : D ∈ hypSupp p E := by
      rw [← hSdef]
      exact hD.1
    have hDF : D ∉ F := hD.2
    refine ⟨hDS.1, ?_⟩
    intro hmap
    exact hDF (by rw [hFdef]; exact ⟨hDS.1, hmap⟩)
  have hsum_le : ∑ D ∈ hTfin.toFinset, rk ↥(hypPart E D) ≤
      2 * rkIdx (fixV (zpowers t)) :=
    sum_moved_le hW hp hp2 hElem ht htE hTfin.toFinset
      fun D hD => hTgood D (hTfin.mem_toFinset.mp hD)
  have hmain_dp : dParam p * T.ncard ≤ 2 * rkIdx (fixV (zpowers t)) := by
    have hrank : ∀ D ∈ T, dParam p ≤ rk ↥(hypPart E D) := by
      intro D hD
      rw [hTdef] at hD
      have hDS : D ∈ hypSupp p E := by
        rw [← hSdef]
        exact hD.1
      exact dParam_le_rk_hypPart hW hp hp2 hElem hDS
    exact (mul_ncard_le_sum_rk_hypPart T hTfin hrank).trans hsum_le
  rcases lt_or_ge (p ^ f) 9 with hlt | hge
  ·
    have h57 : p ^ f = 5 ∨ p ^ f = 7 := by
      obtain ⟨k, hk⟩ := htodd
      have h4 : 4 ≤ p ^ f := hrge4
      have hk2 : k = 2 ∨ k = 3 := by omega
      rcases hk2 with rfl | rfl
      · left; omega
      · right; omega
    rcases h57 with h5 | h7
    ·
      have hp5 : p = 5 := by
        have hdvd : p ∣ 5 := by
          have hpe : p ∣ p ^ f := dvd_pow_self p (by omega)
          rwa [h5] at hpe
        rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h1
        · exact absurd h1 hp.ne_one
        · exact h1
      have hf1 : f = 1 := by
        have h2 : p ^ f = p ^ 1 := by rw [h5, hp5]; norm_num
        exact Nat.pow_right_injective hp.two_le h2
      have hT1 : 1 ≤ T.ncard := by
        have h := hTle
        rw [hp5, hf1] at h
        norm_num at h
        omega
      obtain ⟨D, hD⟩ := (Set.ncard_pos hTfin).mp (show 0 < T.ncard by omega)
      have hne : D.map (MulAut.conj t).toMonoidHom ≠ D := (hTgood D hD).2
      have hDmapS : D.map (MulAut.conj t).toMonoidHom ∈ S := by
        rw [hSdef]
        refine map_conj_mem_hypSupp htE ?_
        rw [← hSdef]
        exact hD.1
      have hDmapF : D.map (MulAut.conj t).toMonoidHom ∉ F := by
        intro hFmem
        rw [hFdef] at hFmem
        have hdouble : (D.map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj t).toMonoidHom = D := by
          rw [Subgroup.map_map]
          have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
              MonoidHom.id _ := by
            refine MonoidHom.ext fun x => ?_
            rw [MonoidHom.comp_apply]
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact ht2)
            have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
            rw [htinv]
            show t * (t * x) * t * t = x
            calc t * (t * x) * t * t = (t * t) * x * (t * t) := by group
              _ = x := by rw [ht2']; group
          rw [hcomp, Subgroup.map_id]
        have hmapF := hFmem.2
        rw [hdouble] at hmapF
        exact hne hmapF.symm
      have hT2 : 2 ≤ T.ncard := by
        have hsub : ({D, D.map (MulAut.conj t).toMonoidHom} :
            Set (Subgroup (MulAut W))) ⊆ T := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hD
          · exact ⟨hDmapS, hDmapF⟩
        have hcard : ({D, D.map (MulAut.conj t).toMonoidHom} :
            Set (Subgroup (MulAut W))).ncard = 2 :=
          Set.ncard_pair (Ne.symm hne)
        calc 2 = _ := hcard.symm
          _ ≤ T.ncard := Set.ncard_le_ncard hsub hTfin
      have hdp4 : dParam p = 4 := by rw [hp5]; exact dParam_eq_of_small.2.1
      have h4T : 4 * T.ncard ≤ 2 * rkIdx (fixV (zpowers t)) := by
        rw [hdp4] at hmain_dp
        exact hmain_dp
      have hq25 : p ^ e = 25 := by rw [hf2, hf1, hp5]; norm_num
      refine ⟨by omega, fun hne25 => absurd hq25 hne25⟩
    ·
      have hp7 : p = 7 := by
        have hdvd : p ∣ 7 := by
          have hpe : p ∣ p ^ f := dvd_pow_self p (by omega)
          rwa [h7] at hpe
        rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h1
        · exact absurd h1 hp.ne_one
        · exact h1
      have hf1 : f = 1 := by
        have h2 : p ^ f = p ^ 1 := by rw [h7, hp7]; norm_num
        exact Nat.pow_right_injective hp.two_le h2
      have hS4 : 4 ≤ S.ncard := by
        have h2 : orbLen p e = 4 := by
          rw [orbLen, if_pos (show Even e from ⟨f, hf⟩), hf2, hf1, hp7]
          exact field_counts_small.2.2.1
        omega
      have hFs : F.ncard ≤ 2 := by
        have h := hfixle
        rw [hf1, hp7] at h
        norm_num at h
        exact h
      have hq49 : p ^ e = 49 := by rw [hf2, hf1, hp7]; norm_num
      have hq4 : p ^ e % 4 = 1 := by rw [hq49]
      obtain ⟨s, -, -, hinv⟩ := exists_inverting_of_isSylowIn hM hp2 hq4 hE
      have hdd : dihedralDeg p = 6 := by
        rw [hp7]
        exact field_counts_small.2.2.2.2
      have hrank6 : ∀ D ∈ T, 6 ≤ rk ↥(hypPart E D) := by
        intro D hD
        have hDS : D ∈ hypSupp p E := by
          rw [← hSdef]
          exact hD.1
        have h := dihedralDeg_le_rk_hypPart hW hp hp2 hElem hDS hinv
        rwa [hdd] at h
      have hsum6 : 6 * T.ncard ≤ ∑ D ∈ hTfin.toFinset, rk ↥(hypPart E D) :=
        mul_ncard_le_sum_rk_hypPart T hTfin hrank6
      by_cases hone : (S ∩ F).ncard ≤ 1
      ·
        have hT3 : 3 ≤ T.ncard := by
          have hdiff : S \ F = S \ (S ∩ F) := by ext x; simp
          have h1 : S.ncard - (S ∩ F).ncard ≤ T.ncard := by
            rw [hTdef, hdiff]
            exact Set.le_ncard_sdiff (s := S ∩ F) (t := S) (hSfin.subset Set.inter_subset_left)
          omega
        have h18 : 18 ≤ 2 * rkIdx (fixV (zpowers t)) := by
          have h1 : 18 ≤ 6 * T.ncard := by omega
          have h2 : 6 * T.ncard ≤ 2 * rkIdx (fixV (zpowers t)) := hsum6.trans hsum_le
          omega
        exact ⟨by omega, fun _ => by omega⟩
      ·
        push Not at hone
        have hSF_eq : S ∩ F = F := by
          refine Set.eq_of_subset_of_ncard_le Set.inter_subset_right ?_ hFfin
          omega
        obtain ⟨D₀, hD₀F, X, hXE, hXp, hXD, hXinv⟩ :=
          exists_fixedHyp_inverted hp hp2 hfpos hElem hcardE ht2 htE hC'
        have hD₀F' : D₀ ∈ fixedHyp p E t := by rw [← hFdef]; exact hD₀F
        have hD₀S : D₀ ∈ S := by
          have h : D₀ ∈ S ∩ F := by rw [hSF_eq]; exact hD₀F
          exact h.1
        have hD₀hyp : D₀ ∈ hypSupp p E := by rw [← hSdef]; exact hD₀S
        have hD₀T : D₀ ∉ T := by
          rw [hTdef]
          exact fun h => h.2 hD₀F
        have hsumadd := sum_moved_add_le hW hp hp2 hElem ht htE hTfin.toFinset
          (fun D hD => hTgood D (hTfin.mem_toFinset.mp hD)) D₀ hD₀F'.1 hD₀F'.2
          (by intro hmem; exact hD₀T (hTfin.mem_toFinset.mp hmem))
        have hdi := dihedralDeg_le_two_mul_rk_commSub_hypPart hW hp hp2 hElem hD₀hyp
          hXE hXp hXD ht hXinv hD₀F'.2
        rw [hdd] at hdi
        have hT2 : 2 ≤ T.ncard := by
          have h1 : S.ncard - F.ncard ≤ T.ncard := by
            rw [hTdef]
            exact Set.le_ncard_sdiff (s := F) (t := S) hFfin
          omega
        have h18 : 18 ≤ 2 * rkIdx (fixV (zpowers t)) := by
          have h1 : 12 ≤ ∑ D ∈ hTfin.toFinset, rk ↥(hypPart E D) := by omega
          omega
        exact ⟨by omega, fun _ => by omega⟩
  ·
    have h16 := sixteen_le_dParam_mul_field hp hp2 hge
    have h2m : 16 ≤ 2 * rkIdx (fixV (zpowers t)) :=
      h16.trans ((Nat.mul_le_mul_left (dParam p) hTle).trans hmain_dp)
    exact ⟨by omega, fun _ => by omega⟩

theorem four_le_rkIdx (hW : ∀ w : W, w ^ 2 = 1) (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : UC22.Fstar Y = L) (hM : LieModel ↥L .PSL 2 p e)
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) (hq : 9 < p ^ e) {t : MulAut W} (htY : t ∈ Y)
    (ht : orderOf t = 2) : 4 ≤ rkIdx (fixV (zpowers t)) := by
  by_cases hinds : InducesPGL2Involution (p ^ e) Y L t
  · by_cases hinv : ∃ E : Subgroup (MulAut W), IsSylowIn p E L ∧
        ∀ x ∈ E, t * x * t⁻¹ = x⁻¹
    ·
      obtain ⟨E, hE, hinvE⟩ := hinv
      have hlow := dihedralDeg_mul_orbLen_le_rk hW hM hp2 hE hinvE
      have hup := rk_commSub_le_two_mul_of_inverts hW hM hp2 hE ht hinvE
      by_cases he1 : e = 1
      · have horb : orbLen p e = 1 := by rw [he1]; exact orbLen_one hp
        have hp11 : 11 ≤ p := by
          refine eleven_le_of_nine_lt hp hp2 ?_
          rw [he1] at hq
          simpa using hq
        have h8 : 8 ≤ dihedralDeg p * orbLen p e := by
          rw [horb, mul_one]
          exact eight_le_dihedralDeg hp hp11
        omega
      · have he2 : 1 < e := by omega
        by_cases hq25 : p ^ e = 25
        · have h12 : dihedralDeg p * orbLen p e = 12 := by
            obtain ⟨hp5, he5⟩ := eq_five_and_two_of_pow_eq_twentyFive hp hq25
            rw [hp5, he5]
            exact dihedralDeg_mul_orbLen_twentyFive
          rw [h12] at hlow
          omega
        · have h16 := sixteen_le_dihedralDeg_mul_orbLen hp hp2 he2 hq hq25
          omega
    ·
      obtain ⟨E, hE⟩ := exists_isSylowIn hM
      have hup := rk_commSub_le_three_mul_of_induces hW hLY hM hp2 hq ht hinds hE
      by_cases htL : t ∈ L
      · have hq4 : p ^ e % 4 ≠ 1 := by
          intro h4
          obtain ⟨E', hE', hinv'⟩ := exists_inverted_isSylowIn hM hp2 h4 htL ht
          exact hinv ⟨E', hE', hinv'⟩
        have heodd : ¬ Even e := fun hev =>
          hq4 (pow_mod_four_eq_one_of_even (hp.odd_of_ne_two hp2) hev)
        have horb : orbLen p e = (p ^ e - 1) / (p - 1) := by rw [orbLen, if_neg heodd]
        have hlow := dParam_mul_orbLen_le_rk hW hM hp2 hE
        rw [horb] at hlow
        by_cases he1 : e = 1
        · have hp11 : 11 ≤ p := by
            refine eleven_le_of_nine_lt hp hp2 ?_
            rw [he1] at hq
            simpa using hq
          have hq1 : (p ^ e - 1) / (p - 1) = 1 := by
            rw [he1, pow_one]
            exact Nat.div_self (by omega)
          rw [hq1, mul_one] at hlow
          by_cases hp4 : p = 17 ∨ p = 31 ∨ p = 73 ∨ p = 127
          · exact four_le_of_four_primes hW hLY hM he1 hp4 ht hinds hinv
          · push Not at hp4
            obtain ⟨h17, h31, h73, h127⟩ := hp4
            have h10 := ten_le_dParam hp hp11 h17 h31 h73 h127
            omega
        · have he2 : 1 < e := by omega
          have h24 := twentyFour_le_dParam_mul hp hp2 he2 hq
          omega
      · have hinds' := hinds
        rcases hinds with h | ⟨A, hAY, hLA, htA, hA⟩
        · exact absurd h htL
        have hlow := dParam_mul_le_rk_of_isPGL2 hW hM hp2 hLA hA hE
        by_cases he1 : e = 1
        · have hp11 : 11 ≤ p := by
            refine eleven_le_of_nine_lt hp hp2 ?_
            rw [he1] at hq
            simpa using hq
          have hq1 : (p ^ e - 1) / (p - 1) = 1 := by
            rw [he1, pow_one]
            exact Nat.div_self (by omega)
          rw [hq1, mul_one] at hlow
          by_cases hp4 : p = 17 ∨ p = 31 ∨ p = 73 ∨ p = 127
          · exact four_le_of_four_primes hW hLY hM he1 hp4 ht hinds' hinv
          · push Not at hp4
            obtain ⟨h17, h31, h73, h127⟩ := hp4
            have h10 := ten_le_dParam hp hp11 h17 h31 h73 h127
            omega
        · have he2 : 1 < e := by omega
          have h24 := twentyFour_le_dParam_mul hp hp2 he2 hq
          omega
  · exact (field_bounds hW hLY hLn hF hM hp hp2 hq htY ht hinds).1

theorem eight_le_rkIdx (hW : ∀ w : W, w ^ 2 = 1) (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : UC22.Fstar Y = L) (hM : LieModel ↥L .PSL 2 p e)
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 < e) (hq : 9 < p ^ e) (hq25 : p ^ e ≠ 25)
    {t : MulAut W} (htY : t ∈ Y) (ht : orderOf t = 2) : 8 ≤ rkIdx (fixV (zpowers t)) := by
  by_cases hinds : InducesPGL2Involution (p ^ e) Y L t
  · obtain ⟨E, hE⟩ := exists_isSylowIn hM
    by_cases hinv : ∃ E : Subgroup (MulAut W), IsSylowIn p E L ∧
        ∀ x ∈ E, t * x * t⁻¹ = x⁻¹
    · obtain ⟨E, hE, hinvE⟩ := hinv
      have hlow := dihedralDeg_mul_orbLen_le_rk hW hM hp2 hE hinvE
      have hup := rk_commSub_le_two_mul_of_inverts hW hM hp2 hE ht hinvE
      have h16 := sixteen_le_dihedralDeg_mul_orbLen hp hp2 he hq hq25
      omega
    · have hup := rk_commSub_le_three_mul_of_induces hW hLY hM hp2 hq ht hinds hE
      by_cases htL : t ∈ L
      · have hq4 : p ^ e % 4 ≠ 1 := by
          intro h4
          obtain ⟨E', hE', hinv'⟩ := exists_inverted_isSylowIn hM hp2 h4 htL ht
          exact hinv ⟨E', hE', hinv'⟩
        have heodd : ¬ Even e := fun hev =>
          hq4 (pow_mod_four_eq_one_of_even (hp.odd_of_ne_two hp2) hev)
        have horb : orbLen p e = (p ^ e - 1) / (p - 1) := by rw [orbLen, if_neg heodd]
        have hlow := dParam_mul_orbLen_le_rk hW hM hp2 hE
        rw [horb] at hlow
        have h24 := twentyFour_le_dParam_mul hp hp2 he hq
        omega
      · rcases hinds with h | ⟨A, -, hLA, htA, hA⟩
        · exact absurd h htL
        have hlow := dParam_mul_le_rk_of_isPGL2 hW hM hp2 hLA hA hE
        have h24 := twentyFour_le_dParam_mul hp hp2 he hq
        omega
  · exact (field_bounds hW hLY hLn hF hM hp hp2 hq htY ht hinds).2 hq25

theorem six_le_rkIdx_of_mem (hW : ∀ w : W, w ^ 2 = 1) (hM : LieModel ↥L .PSL 2 p e)
    (hp2 : p ≠ 2) (hq25 : p ^ e = 25) {t : MulAut W} (htL : t ∈ L) (ht : orderOf t = 2) :
    6 ≤ rkIdx (fixV (zpowers t)) := by
  have hp : p.Prime := hM.admissible.1
  obtain ⟨hp5, he2⟩ := eq_five_and_two_of_pow_eq_twentyFive hp hq25
  have hq4 : p ^ e % 4 = 1 := by rw [hq25]
  obtain ⟨E, hE, hinv⟩ := exists_inverted_isSylowIn hM hp2 hq4 htL ht
  have hlow := dihedralDeg_mul_orbLen_le_rk hW hM hp2 hE hinv
  have hup := rk_commSub_le_two_mul_of_inverts hW hM hp2 hE ht hinv
  have h12 : dihedralDeg p * orbLen p e = 12 := by
    rw [hp5, he2]
    exact dihedralDeg_mul_orbLen_twentyFive
  rw [h12] at hlow
  omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
