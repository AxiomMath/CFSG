module

public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin

open CFSG.SL2MinimalFaithful Matrix

namespace Ch3z

section SL2

variable {K : Type} [Field K]

private def torusDiag (c : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

private theorem coe_torusDiag (c : Kˣ) :
    ((torusDiag c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] := rfl

private theorem torusDiag_mul (c d : Kˣ) : torusDiag c * torusDiag d = torusDiag (c * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusDiag, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem torusDiag_one : torusDiag (1 : Kˣ) = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusDiag]

private theorem torusDiag_inv (c : Kˣ) : (torusDiag c)⁻¹ = torusDiag c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, torusDiag_mul, mul_inv_cancel, torusDiag_one]

private theorem torusDiag_pow (c : Kˣ) (n : ℕ) : (torusDiag c) ^ n = torusDiag (c ^ n) := by
  induction n with
  | zero => simp [torusDiag_one]
  | succ n ih => rw [pow_succ, ih, torusDiag_mul, pow_succ]

private theorem torusDiag_conj_unipotent (c : Kˣ) (t : K) :
    torusDiag c * unipotent t * (torusDiag c)⁻¹ = unipotent ((c : K) ^ 2 * t) := by
  rw [torusDiag_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_torusDiag, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem torusDiag_inv_conj_unipotent (c : Kˣ) (t : K) :
    (torusDiag c)⁻¹ * unipotent t * torusDiag c = unipotent (((c⁻¹ : Kˣ) : K) ^ 2 * t) := by
  have := torusDiag_conj_unipotent c⁻¹ t
  rwa [← torusDiag_inv c, inv_inv] at this

private theorem mulVec_unipotent (t : K) (w : Fin 2 → K) :
    (unipotent t : Matrix (Fin 2) (Fin 2) K).mulVec w = ![w 0 + t * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [coe_unipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem mulVec_torusDiag (c : Kˣ) (w : Fin 2 → K) :
    (torusDiag c : Matrix (Fin 2) (Fin 2) K).mulVec w = ![(c : K) * w 0, ((c⁻¹ : Kˣ) : K) * w 1] := by
  ext i
  fin_cases i <;> simp [coe_torusDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem torus_core [Finite K] {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    {Q : Subgroup (SpecialLinearGroup (Fin 2) K)} (hQ : Nat.card Q = Nat.card K) :
    ∃ δ : SpecialLinearGroup (Fin 2) K, Odd (orderOf δ) ∧
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
  obtain ⟨c, hc1⟩ : ∃ c : Kˣ, c ≠ 1 := by
    have h4 : 4 ≤ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
      have := Finset.card_le_two (a := (0 : K)) (b := 1)
      rw [Finset.card_univ]
      omega
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have ha0 : a ≠ 0 := fun h => ha (by simp [h])
    have ha1 : a ≠ 1 := fun h => ha (by simp [h])
    exact ⟨Units.mk0 a ha0, fun h => ha1 (by simpa using congrArg Units.val h)⟩
  have hcK : Fintype.card K = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  have hodd : Odd (orderOf (g * torusDiag c * g⁻¹)) := by
    have hpow : (g * torusDiag c * g⁻¹) ^ (Fintype.card K - 1) = 1 := by
      rw [conj_pow, torusDiag_pow]
      have : c ^ (Fintype.card K - 1) = 1 := by
        rw [← Fintype.card_units]
        exact pow_card_eq_one
      rw [this, torusDiag_one]
      simp
    have h2 : Even (2 ^ e : ℕ) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have h3 : Odd (Fintype.card K - 1) := by
      rw [hcK]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 odd_one
    exact h3.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  have hnorm : g * torusDiag c * g⁻¹ ∈ Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 2) K)) := by
    apply B6.mem_normalizer_of_forall_mem
    · intro x hx
      obtain ⟨t, rfl⟩ := hQmem x hx
      have e1 : (g * torusDiag c * g⁻¹) * (g * unipotent t * g⁻¹) * (g * torusDiag c * g⁻¹)⁻¹ =
          g * (torusDiag c * unipotent t * (torusDiag c)⁻¹) * g⁻¹ := by group
      rw [torusDiag_conj_unipotent] at e1
      rw [e1]
      exact hg _
    · intro x hx
      obtain ⟨t, rfl⟩ := hQmem x hx
      have e1 : (g * torusDiag c * g⁻¹)⁻¹ * (g * unipotent t * g⁻¹) * (g * torusDiag c * g⁻¹) =
          g * ((torusDiag c)⁻¹ * unipotent t * torusDiag c) * g⁻¹ := by group
      rw [torusDiag_inv_conj_unipotent] at e1
      rw [e1]
      exact hg _
  refine ⟨g * torusDiag c * g⁻¹, hodd, hnorm, ?_⟩
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
    rw [mulVec_unipotent] at this
    simpa using this
  have hδw' : (torusDiag c : Matrix (Fin 2) (Fin 2) K).mulVec w' = w' := by
    have e1 : g⁻¹ * (g * torusDiag c * g⁻¹) = torusDiag c * g⁻¹ := by group
    calc (torusDiag c : Matrix (Fin 2) (Fin 2) K).mulVec w'
        = (↑(torusDiag c * g⁻¹) : Matrix (Fin 2) (Fin 2) K).mulVec w := (mv_mul _ _ _).symm
      _ = (↑(g⁻¹ * (g * torusDiag c * g⁻¹)) : Matrix (Fin 2) (Fin 2) K).mulVec w := by rw [e1]
      _ = ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            ((↑(g * torusDiag c * g⁻¹) : Matrix (Fin 2) (Fin 2) K).mulVec w) := mv_mul _ _ _
      _ = w' := by rw [hδw]
  have hw'0 : w' 0 = 0 := by
    have h1 := congrFun hδw' 0
    rw [mulVec_torusDiag] at h1
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



end SL2

section Natural

variable {V : Type} [CommGroup V]

theorem exists_torus_of_natBlock {H Q : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ}
    (he : 2 ≤ e) (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hN : NatBlockData H U e)
    (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q H) :
    ∃ d ∈ H, d ∈ Subgroup.normalizer (Q : Set (MulAut V)) ∧ Odd (orderOf d) ∧
      ∀ v ∈ U, (∀ q ∈ Q, q v = v) → d v = v → v = 1 := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have hact : ∀ (γ : SpecialLinearGroup (Fin 2) K) (u : ↥U),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hUinv _ (π γ).2 _ u.2⟩ =
        Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u))) :=
    fun γ u => hβeq γ u _
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply sl2_eq_one_of_mulVec
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
  obtain ⟨δ, hδodd, hδnorm, hδvec⟩ := torus_core he hK hQ''card
  have hmemQ : ∀ γ : SpecialLinearGroup (Fin 2) K, γ ∈ Q'' ↔ ((π γ : ↥H) : MulAut V) ∈ Q := by
    intro γ
    exact Subgroup.mem_subgroupOf
  refine ⟨((π δ : ↥H) : MulAut V), (π δ).2, ?_, ?_, ?_⟩
  · apply B6.mem_normalizer_of_forall_mem
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
  · have hdvd : orderOf (π δ : ↥H) ∣ orderOf δ := orderOf_map_dvd π δ
    have : orderOf ((π δ : ↥H) : MulAut V) = orderOf (π δ : ↥H) := Subgroup.orderOf_coe _
    rw [this]
    exact hδodd.of_dvd_nat hdvd
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

variable {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

@[expose] def TorusProp (T H₀ : Subgroup (MulAut V)) (d : MulAut V) : Prop :=
  d ∈ H₀ ∧ Odd (orderOf d) ∧
    ∀ v ∈ commV H₀, (∀ q ∈ T ⊓ H₀, q v = v) → d v = v → v = 1

theorem TorusProp.conj {T H₀ : Subgroup (MulAut V)} {d : MulAut V} (hd : TorusProp T H₀ d)
    {t : MulAut V} (ht : t ∈ T) : TorusProp T (B6.conjSub t H₀) (t * d * t⁻¹) := by
  obtain ⟨hdH, hdo, hdv⟩ := hd
  refine ⟨?_, ?_, ?_⟩
  · rw [B6.mem_conjSub]
    have : t⁻¹ * (t * d * t⁻¹) * t = d := by group
    rw [this]
    exact hdH
  · have : orderOf (t * d * t⁻¹) = orderOf d :=
      orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective d
    rw [this]
    exact hdo
  · intro v hv hq hdv'
    have hcomm : commV (B6.conjSub t H₀) = (commV H₀).map t.toMonoidHom := B19.commV_map_conj t H₀
    rw [hcomm] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    have hv₀' : t.toMonoidHom v₀ = t v₀ := rfl
    refine congrArg t.toMonoidHom (hdv v₀ hv₀ ?_ ?_) |>.trans (map_one _)
    · intro q hqT
      have h1 : t * q * t⁻¹ ∈ T ⊓ B6.conjSub t H₀ := by
        refine ⟨T.mul_mem (T.mul_mem ht hqT.1) (T.inv_mem ht), ?_⟩
        refine B6.mem_conjSub.mpr ?_
        have : t⁻¹ * (t * q * t⁻¹) * t = q := by group
        rw [this]
        exact hqT.2
      have h2 := hq _ h1
      have h3 : (t * q * t⁻¹) (t v₀) = t v₀ := h2
      simpa [MulAut.mul_apply] using h3
    · have h3 : (t * d * t⁻¹) (t v₀) = t v₀ := hdv'
      simpa [MulAut.mul_apply] using h3


theorem BlkCtx.eq_one_of_fixed (h : BlkCtx X T M 𝓗) {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ 𝓗)
    {d₀ : MulAut V} (hd₀ : TorusProp T H₀ d₀) (hdM : d₀ ∈ M) {v : V}
    (hvT : ∀ t ∈ T, t v = v) (hvM : ∀ d ∈ M, Odd (orderOf d) → d v = v) : v = 1 := by
  classical
  have hTM : T ≤ M := h.mp.le
  have key : ∀ 𝓕 : Finset (Subgroup (MulAut V)), 𝓕 ⊆ 𝓗 → ∀ w ∈ ⨆ H ∈ 𝓕, commV H,
      (∀ t ∈ T, t w = w) → (∀ d ∈ M, Odd (orderOf d) → d w = w) → w = 1 := by
    intro 𝓕
    induction 𝓕 using Finset.induction_on with
    | empty =>
      intro _ w hw _ _
      simpa using hw
    | insert H₁ 𝓕' hH₁ ih =>
      intro hsub w hw hwT hwM
      have hH₁𝓗 : H₁ ∈ 𝓗 := hsub (Finset.mem_insert_self _ _)
      have hsub' : 𝓕' ⊆ 𝓗 := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hw
      obtain ⟨a, ha, r, hr, rfl⟩ := Subgroup.mem_sup.mp hw
      obtain ⟨t, htT, hconj⟩ := h.trans hH₀ hH₁𝓗
      have hd₁ : TorusProp T H₁ (t * d₀ * t⁻¹) := hconj ▸ hd₀.conj htT
      have hd₁M : t * d₀ * t⁻¹ ∈ M := M.mul_mem (M.mul_mem (hTM htT) hdM) (M.inv_mem (hTM htT))
      have hrfix : r ∈ fixV H₁ := by
        have : (⨆ H ∈ 𝓕', commV H) ≤ fixV H₁ := by
          refine iSup₂_le fun H hH => ?_
          intro v hv x hx
          have hne : H ≠ H₁ := fun heq => hH₁ (heq ▸ hH)
          exact h.act_commV_of_ne (hsub' hH) hH₁𝓗 hne hx hv
        exact this hr
      have hfixr : ∀ x ∈ H₁, x r = r := fun x hx => hrfix x hx
      have ha1 : a = 1 := by
        refine hd₁.2.2 a ha (fun q hq => ?_) ?_
        · have h1 := hwT q hq.1
          rw [map_mul, hfixr q hq.2] at h1
          exact mul_right_cancel h1
        · have h1 := hwM _ hd₁M hd₁.2.1
          rw [map_mul, hfixr _ hd₁.1] at h1
          exact mul_right_cancel h1
      subst ha1
      rw [one_mul] at hwT hwM ⊢
      exact ih hsub' r hr hwT hwM
  refine key 𝓗 le_rfl v ?_ hvT hvM
  rw [h.iSup_comm]
  trivial

end Natural

end Ch3z

end CFSG.Quasithin
