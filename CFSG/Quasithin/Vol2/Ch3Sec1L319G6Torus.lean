module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Num
public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.SL2MinimalFaithful Matrix

private theorem exists_prime_cop6_G6Torus {e : ℕ} (he : 3 ≤ e) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ e - 1 ∧ Nat.Coprime p 6 := by
  have hn : 2 ≤ e := by omega
  obtain ⟨d, hd, hdv, hd3⟩ : ∃ d : ℕ, d.Prime ∧ d ∣ 2 ^ e - 1 ∧ d ≠ 3 := by
    by_contra hcon
    push Not at hcon
    have h2 : e = 2 := cartan_three_power_of_primes hn (fun hd hdv => hcon _ hd hdv)
    omega
  have hd2 : d ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  refine ⟨d, hd, hdv, ?_⟩
  have h2 : Nat.Coprime d 2 := (Nat.coprime_primes hd Nat.prime_two).mpr hd2
  have h3 : Nat.Coprime d 3 := (Nat.coprime_primes hd Nat.prime_three).mpr hd3
  have h6 : Nat.Coprime d (2 * 3) := Nat.Coprime.mul_right h2 h3
  exact h6

section SL2G6

variable {K : Type} [Field K]

private def torusDiagG6 (c : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

private theorem coe_torusDiagG6 (c : Kˣ) :
    ((torusDiagG6 c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] := rfl

private theorem torusDiagG6_mul (c d : Kˣ) : torusDiagG6 c * torusDiagG6 d = torusDiagG6 (c * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusDiagG6, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem torusDiagG6_one : torusDiagG6 (1 : Kˣ) = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusDiagG6]

private theorem torusDiagG6_inv (c : Kˣ) : (torusDiagG6 c)⁻¹ = torusDiagG6 c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, torusDiagG6_mul, mul_inv_cancel, torusDiagG6_one]

private theorem torusDiagG6_pow (c : Kˣ) (n : ℕ) : (torusDiagG6 c) ^ n = torusDiagG6 (c ^ n) := by
  induction n with
  | zero => simp [torusDiagG6_one]
  | succ n ih => rw [pow_succ, ih, torusDiagG6_mul, pow_succ]

private theorem torusDiagG6_conj_unipotent (c : Kˣ) (t : K) :
    torusDiagG6 c * unipotent t * (torusDiagG6 c)⁻¹ = unipotent ((c : K) ^ 2 * t) := by
  rw [torusDiagG6_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_torusDiagG6, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem torusDiagG6_inv_conj_unipotent (c : Kˣ) (t : K) :
    (torusDiagG6 c)⁻¹ * unipotent t * torusDiagG6 c = unipotent (((c⁻¹ : Kˣ) : K) ^ 2 * t) := by
  have := torusDiagG6_conj_unipotent c⁻¹ t
  rwa [← torusDiagG6_inv c, inv_inv] at this

private theorem mulVec_unipotentG6 (t : K) (w : Fin 2 → K) :
    (unipotent t : Matrix (Fin 2) (Fin 2) K).mulVec w = ![w 0 + t * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [coe_unipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem mulVec_torusDiagG6 (c : Kˣ) (w : Fin 2 → K) :
    (torusDiagG6 c : Matrix (Fin 2) (Fin 2) K).mulVec w = ![(c : K) * w 0, ((c⁻¹ : Kˣ) : K) * w 1] := by
  ext i
  fin_cases i <;> simp [coe_torusDiagG6, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem torus_core_pow [Finite K] {e : ℕ} (hK : Nat.card K = 2 ^ e)
    {Q : Subgroup (SpecialLinearGroup (Fin 2) K)} (hQ : Nat.card Q = Nat.card K)
    (c : Kˣ) (hc1 : c ≠ 1) {p : ℕ} (hcp : c ^ p = 1) :
    ∃ δ : SpecialLinearGroup (Fin 2) K, δ ^ p = 1 ∧
      δ ∈ Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 2) K)) ∧
      ∀ w : Fin 2 → K, (∀ γ ∈ Q, (γ : Matrix (Fin 2) (Fin 2) K).mulVec w = w) →
        (δ : Matrix (Fin 2) (Fin 2) K).mulVec w = w → w = 0 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hK hQ
  let f : K → Q := fun t => ⟨g * unipotent t * g⁻¹, hg t⟩
  have hfinj : Function.Injective f := by
    intro s t hst
    have h1 := Subtype.mk.inj hst
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact unipotent_injective h2
  have hfbij : Function.Bijective f := by
    refine hfinj.bijective_of_nat_card_le ?_
    rw [hQ]
  have hQmem : ∀ γ ∈ Q, ∃ t : K, γ = g * unipotent t * g⁻¹ := by
    intro γ hγ
    obtain ⟨t, ht⟩ := hfbij.2 ⟨γ, hγ⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  have hpow : (g * torusDiagG6 c * g⁻¹) ^ p = 1 := by
    rw [conj_pow, torusDiagG6_pow, hcp, torusDiagG6_one]
    simp
  have hnorm : g * torusDiagG6 c * g⁻¹ ∈ Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 2) K)) := by
    apply CFSG.Quasithin.B6.mem_normalizer_of_forall_mem
    · intro x hx
      obtain ⟨t, rfl⟩ := hQmem x hx
      have e1 : (g * torusDiagG6 c * g⁻¹) * (g * unipotent t * g⁻¹) * (g * torusDiagG6 c * g⁻¹)⁻¹ =
          g * (torusDiagG6 c * unipotent t * (torusDiagG6 c)⁻¹) * g⁻¹ := by group
      rw [torusDiagG6_conj_unipotent] at e1
      rw [e1]
      exact hg _
    · intro x hx
      obtain ⟨t, rfl⟩ := hQmem x hx
      have e1 : (g * torusDiagG6 c * g⁻¹)⁻¹ * (g * unipotent t * g⁻¹) * (g * torusDiagG6 c * g⁻¹) =
          g * ((torusDiagG6 c)⁻¹ * unipotent t * torusDiagG6 c) * g⁻¹ := by group
      rw [torusDiagG6_inv_conj_unipotent] at e1
      rw [e1]
      exact hg _
  refine ⟨g * torusDiagG6 c * g⁻¹, hpow, hnorm, ?_⟩
  intro w hw hδw
  have mv_mul : ∀ (a b : SpecialLinearGroup (Fin 2) K) (z : Fin 2 → K),
      (↑(a * b) : Matrix (Fin 2) (Fin 2) K).mulVec z =
        (a : Matrix (Fin 2) (Fin 2) K).mulVec ((b : Matrix (Fin 2) (Fin 2) K).mulVec z) := by
    intro a b z
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  have mv_one : ∀ z : Fin 2 → K, (↑(1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec z = z := by
    intro z
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  set w' := ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w with hw'
  have hww' : ((g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec w' = w := by
    rw [hw', ← mv_mul, mul_inv_cancel, mv_one]
  have hw'u : ∀ t : K, (unipotent t : Matrix (Fin 2) (Fin 2) K).mulVec w' = w' := by
    intro t
    have h1 := hw (g * unipotent t * g⁻¹) (hg t)
    have e1 : g⁻¹ * (g * unipotent t * g⁻¹) = unipotent t * g⁻¹ := by group
    calc (unipotent t : Matrix (Fin 2) (Fin 2) K).mulVec w'
        = (↑(unipotent t * g⁻¹) : Matrix (Fin 2) (Fin 2) K).mulVec w := (mv_mul _ _ _).symm
      _ = (↑(g⁻¹ * (g * unipotent t * g⁻¹)) : Matrix (Fin 2) (Fin 2) K).mulVec w := by rw [e1]
      _ = ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            ((↑(g * unipotent t * g⁻¹) : Matrix (Fin 2) (Fin 2) K).mulVec w) := mv_mul _ _ _
      _ = w' := by rw [h1]
  have hw'1 : w' 1 = 0 := by
    have := congrFun (hw'u 1) 0
    rw [mulVec_unipotentG6] at this
    simpa using this
  have hδw' : (torusDiagG6 c : Matrix (Fin 2) (Fin 2) K).mulVec w' = w' := by
    have e1 : g⁻¹ * (g * torusDiagG6 c * g⁻¹) = torusDiagG6 c * g⁻¹ := by group
    calc (torusDiagG6 c : Matrix (Fin 2) (Fin 2) K).mulVec w'
        = (↑(torusDiagG6 c * g⁻¹) : Matrix (Fin 2) (Fin 2) K).mulVec w := (mv_mul _ _ _).symm
      _ = (↑(g⁻¹ * (g * torusDiagG6 c * g⁻¹)) : Matrix (Fin 2) (Fin 2) K).mulVec w := by rw [e1]
      _ = ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            ((↑(g * torusDiagG6 c * g⁻¹) : Matrix (Fin 2) (Fin 2) K).mulVec w) := mv_mul _ _ _
      _ = w' := by rw [hδw]
  have hw'0 : w' 0 = 0 := by
    have h1 := congrFun hδw' 0
    rw [mulVec_torusDiagG6] at h1
    simp only [Matrix.cons_val_zero] at h1
    have h2 : ((c : K) - 1) * w' 0 = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Units.ext (sub_eq_zero.mp h)) hc1
    · exact h
  have hw'z : w' = 0 := by
    ext i
    fin_cases i
    · exact hw'0
    · exact hw'1
  rw [← hww', hw'z]
  simp

end SL2G6

theorem exists_torus_of_natBlock_pow {V : Type} [CommGroup V] {H Q : Subgroup (MulAut V)}
    {U : Subgroup V} {e : ℕ} (he : 2 ≤ e) {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ 2 ^ e - 1)
    (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hN : CFSG.Quasithin.Ch3z.NatBlockData H U e) (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q H) :
    ∃ d ∈ H, d ∈ Subgroup.normalizer (Q : Set (MulAut V)) ∧ d ^ p = 1 ∧
      ∀ v ∈ U, (∀ q ∈ Q, q v = v) → d v = v → v = 1 := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hact : ∀ (γ : SpecialLinearGroup (Fin 2) K) (u : ↥U),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ =
        Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u))) :=
    fun γ u => hβeq γ u _
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply CFSG.Quasithin.Ch3z.sl2_eq_one_of_mulVec
    intro w
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd w)
    have h1 := hact γ u
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ : ↥U) = u := by
      apply Subtype.ext
      rw [hγ]
      rfl
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa using h3.symm
  have hQH : Q ≤ H := hQ.1
  have hcardH : Nat.card H = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπs⟩),
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have : Finite H := Finite.of_surjective π hπs
  have : Finite Q := Finite.of_injective (Subgroup.inclusion hQH) (Subgroup.inclusion_injective hQH)
  have hQcard : Nat.card Q = Nat.card K := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ.2.1
    have hidx : Odd (Q.subgroupOf H).index :=
      Nat.not_even_iff_odd.mp (fun h => hQ.2.2 (even_iff_two_dvd.mp h))
    have h1 : Nat.card (Q.subgroupOf H) * (Q.subgroupOf H).index = Nat.card H :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (Q.subgroupOf H) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    rw [h2, hk, hcardH, hK] at h1
    have hm : Odd ((2 ^ e) ^ 2 - 1) := by
      have h2e : Even ((2 ^ e) ^ 2) := (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩,
        two_ne_zero⟩)
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) h2e odd_one
    have hc1 : Nat.Coprime (2 ^ k) ((2 ^ e) ^ 2 - 1) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    have hc2 : Nat.Coprime (2 ^ e) (Q.subgroupOf H).index :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hidx)
    have hd1 : 2 ^ k ∣ 2 ^ e := hc1.dvd_of_dvd_mul_right ⟨_, h1.symm⟩
    have hd2 : 2 ^ e ∣ 2 ^ k := by
      have : 2 ^ e ∣ 2 ^ k * (Q.subgroupOf H).index := ⟨_, h1⟩
      exact hc2.dvd_of_dvd_mul_right this
    have : k = e := le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd1)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2)
    rw [hk, hK, this]
  let Q'' : Subgroup (SpecialLinearGroup (Fin 2) K) := (Q.subgroupOf H).comap π
  have hQ''card : Nat.card Q'' = Nat.card K := by
    have : Nat.card Q'' = Nat.card (Q.subgroupOf H) :=
      Nat.card_congr (Equiv.subtypeEquiv (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).toEquiv
        (fun γ => Iff.rfl))
    rw [this, ← hQcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units (α := K), hK]
    exact hpdvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    exact hp.one_lt.ne hc
  have hcp : c ^ p = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  obtain ⟨δ, hδp, hδnorm, hδvec⟩ := torus_core_pow hK hQ''card c hc1 hcp
  have hmemQ : ∀ γ : SpecialLinearGroup (Fin 2) K, γ ∈ Q'' ↔ ((π γ : ↥H) : MulAut V) ∈ Q := by
    intro γ
    exact Subgroup.mem_subgroupOf
  refine ⟨((π δ : ↥H) : MulAut V), (π δ).2, ?_, ?_, ?_⟩
  · apply CFSG.Quasithin.B6.mem_normalizer_of_forall_mem
    · intro x hx
      obtain ⟨γ, hγ⟩ := hπs ⟨x, hQH hx⟩
      have hγQ : γ ∈ Q'' := (hmemQ γ).mpr (by rw [hγ]; exact hx)
      have := (hmemQ _).mp ((Subgroup.mem_normalizer_iff.mp hδnorm γ).mp hγQ)
      have e1 : ((π (δ * γ * δ⁻¹) : ↥H) : MulAut V) =
          ((π δ : ↥H) : MulAut V) * x * ((π δ : ↥H) : MulAut V)⁻¹ := by
        simp only [map_mul, map_inv, hγ]
        rfl
      rwa [e1] at this
    · intro x hx
      obtain ⟨γ, hγ⟩ := hπs ⟨x, hQH hx⟩
      have hγQ : γ ∈ Q'' := (hmemQ γ).mpr (by rw [hγ]; exact hx)
      have hδ' : δ⁻¹ ∈ Subgroup.normalizer (Q'' : Set (SpecialLinearGroup (Fin 2) K)) :=
        Subgroup.inv_mem _ hδnorm
      have := (hmemQ _).mp ((Subgroup.mem_normalizer_iff.mp hδ' γ).mp hγQ)
      have e1 : ((π (δ⁻¹ * γ * δ⁻¹⁻¹) : ↥H) : MulAut V) =
          ((π δ : ↥H) : MulAut V)⁻¹ * x * ((π δ : ↥H) : MulAut V) := by
        simp only [map_mul, map_inv, inv_inv, hγ]
        rfl
      rwa [e1] at this
  · have h1 : (π δ : ↥H) ^ p = 1 := by rw [← map_pow, hδp, map_one]
    have h2 : ((π δ : ↥H) : MulAut V) ^ p = 1 := by
      have := congrArg (fun x : ↥H => (x : MulAut V)) h1
      simpa using this
    exact h2
  · intro v hv hQv hdv
    set u : ↥U := ⟨v, hv⟩ with hu
    have hfix : ∀ γ ∈ Q'', (γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)) =
        Multiplicative.toAdd (β u) := by
      intro γ hγ
      have h1 := hact γ u
      have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ : ↥U) = u :=
        Subtype.ext (hQv _ ((hmemQ γ).mp hγ))
      rw [h2] at h1
      have h3 := congrArg Multiplicative.toAdd h1
      simpa using h3.symm
    have hfixδ : (δ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)) =
        Multiplicative.toAdd (β u) := by
      have h1 := hact δ u
      have h2 : (⟨((π δ : ↥H) : MulAut V) (u : V), hUinv _ (π δ).2 _ u.2⟩ : ↥U) = u :=
        Subtype.ext hdv
      rw [h2] at h1
      have h3 := congrArg Multiplicative.toAdd h1
      simpa using h3.symm
    have h0 := hδvec _ hfix hfixδ
    have : β u = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h0
    have h4 : u = 1 := hβ.1 (this.trans (map_one β).symm)
    simpa [hu] using congrArg Subtype.val h4

theorem exists_torus_of_natBlock_cop6 {V : Type} [CommGroup V] {H Q : Subgroup (MulAut V)}
    {U : Subgroup V} {e : ℕ} (he : 3 ≤ e) (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hN : CFSG.Quasithin.Ch3z.NatBlockData H U e) (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q H) :
    ∃ d ∈ H, d ∈ Subgroup.normalizer (Q : Set (MulAut V)) ∧ Nat.Coprime (orderOf d) 6 ∧
      ∀ v ∈ U, (∀ q ∈ Q, q v = v) → d v = v → v = 1 := by
  obtain ⟨p, hp, hpdvd, hpcop⟩ := exists_prime_cop6_G6Torus he
  obtain ⟨d, hdH, hdN, hdp, hdv⟩ := exists_torus_of_natBlock_pow (by omega) hp hpdvd hUinv hN hQ
  exact ⟨d, hdH, hdN, Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hdp) hpcop, hdv⟩

end CFSG.Quasithin.H13.L319
