module

public import CFSG.Quasithin.Vol2.Ch3B513NOff
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank Matrix

section Groups

variable {X : Type*} [Group X] [Finite X]

theorem card_le_of_card_eq {a m : ℕ} (hm : Odd m) (hX : Nat.card X = 2 ^ a * m)
    {E : Subgroup X} (hE2 : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hE2 e e.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 ^ a * m := by
    rw [← hk, ← hX]
    exact Subgroup.card_subgroup_dvd_card E
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 hm)
  have h1 : 2 ^ k ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd (by positivity) h1

theorem card_le_four_of_orderOf {m : ℕ} (hm : Odd m) (hX : Nat.card X = 8 * m) {x : X}
    (hx : orderOf x = 4) {E : Subgroup X} (hE2 : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : Nat.card E ≤ 2 ^ 3 := card_le_of_card_eq hm (by rw [hX]; norm_num) hE2
  have hEp : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hE2 e e.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  rw [hk] at h8 ⊢
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h8
  rcases Nat.lt_or_ge k 3 with hk2 | hk3'
  · calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  · exfalso
    have hk3e : k = 3 := le_antisymm hk3 hk3'
    have hm0 : m ≠ 0 := fun h => by simp [h] at hm
    have hfact : (Nat.card X).factorization 2 = 3 := by
      rw [hX, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
        show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by
          rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])]
    let P : Sylow 2 X := Sylow.ofCard E (by rw [hk, hk3e, hfact])
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
    obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
    have hxQ : x ∈ ((g • P : Sylow 2 X) : Set X) := by
      rw [hg]
      exact hQ (Subgroup.mem_zpowers x)
    rw [Sylow.coe_smul] at hxQ
    obtain ⟨e, he, hex⟩ := hxQ
    have he2 : e ^ 2 = 1 := hE2 e he
    have hx2 : x ^ 2 = 1 := by
      rw [← hex]
      show (MulAut.conj g e) ^ 2 = 1
      rw [← map_pow, he2, map_one]
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at this
    norm_num at this

end Groups

variable {W : Type} [CommGroup W] [Finite W]

theorem hasGood_of_card_le_four (hW : ∀ w : W, w ^ 2 = 1) {G D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) (hcard : Nat.card D ≤ 4) : HasGood G :=
  hasGood_of_isFFStarMin hW hD ((index_fixV_le_card hD.1).trans hcard)

omit [Finite W] in
theorem card_le_of_equiv {H D : Subgroup (MulAut W)} (hDH : D ≤ H) {X : Type*} [Group X]
    (e : ↥H ≃* X) {c : ℕ}
    (hX : ∀ E : Subgroup X, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ c)
    (hD2 : ∀ d ∈ D, d ^ 2 = 1) : Nat.card D ≤ c := by
  have h1 : Nat.card D = Nat.card ((D.subgroupOf H).map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).symm
  rw [h1]
  refine hX _ ?_
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_pow]
  have : d ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hD2 _ (Subgroup.mem_subgroupOf.1 hd))
  rw [this, map_one]

theorem orderOf_cycle4 :
    orderOf (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2 * Equiv.swap 2 3) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun k hk hk0 => ?_⟩
  interval_cases k <;> decide

theorem card_le_four_perm5 (E : Subgroup (Equiv.Perm (Fin 5))) (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    Nat.card E ≤ 4 :=
  card_le_four_of_orderOf (m := 15) (by decide)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide)
    orderOf_cycle4 hE2

@[expose] def uniM (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 0, 1, 1; 0, 0, 1]

theorem det_uniM (K : Type) [Field K] : (uniM K).det = 1 := by
  simp [uniM, det_fin_three]

@[expose] noncomputable def uniSL (K : Type) [Field K] : ↥(StatedSL 3 K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (uniM K) (by rw [det_uniM]; exact one_ne_zero),
    Subgroup.subset_closure (show (uniM K).det = 1 from det_uniM K)⟩

theorem coe_uniSL_pow (K : Type) [Field K] (k : ℕ) :
    (((uniSL K ^ k : ↥(StatedSL 3 K)) : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = uniM K ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, pow_succ]
    rfl

theorem orderOf_uniSL (K : Type) [Field K] [CharP K 2] : orderOf (uniSL K) = 4 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hsq : uniM K ^ 2 = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uniM, Matrix.mul_apply, Fin.sum_univ_three, h2]
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, fun k hk hk0 => ?_⟩
  · apply Subtype.ext
    apply Units.ext
    rw [coe_uniSL_pow, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h2]
  · intro h1
    have h1' := congrArg (fun g : ↥(StatedSL 3 K) =>
      ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [coe_uniSL_pow] at h1'
    interval_cases k
    · have := congrFun (congrFun h1' 0) 1
      simp [uniM] at this
    · have := congrFun (congrFun h1' 0) 2
      rw [hsq] at this
      simp at this
    · have := congrFun (congrFun h1' 0) 2
      rw [pow_succ, hsq] at this
      simp [uniM, Matrix.mul_apply, Fin.sum_univ_three] at this

theorem card_le_four_sl3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (E : Subgroup ↥(StatedSL 3 K)) (hE2 : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 4 := by
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hKf, pow_one])
  refine card_le_four_of_orderOf (m := 21) (by decide) ?_ (orderOf_uniSL K) hE2
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK]
  norm_num

theorem card_le_four_sl2 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : n ≤ 2) (E : Subgroup ↥(StatedSL 2 K)) (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  have hcard := card_statedSL_two1527d (F := K)
  rw [hK] at hcard
  have hpos : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    have := Finite.one_lt_card (α := K)
    rw [hK] at this
    norm_num at this
  interval_cases n
  · calc Nat.card E ≤ 2 ^ 1 := card_le_of_card_eq (m := 3) (by decide)
          (by rw [hcard]; norm_num) hE2
      _ ≤ 4 := by norm_num
  · calc Nat.card E ≤ 2 ^ 2 := card_le_of_card_eq (m := 15) (by decide)
          (by rw [hcard]; norm_num) hE2
      _ = 4 := by norm_num

end CFSG.Quasithin.B513N
