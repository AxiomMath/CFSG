module

public import CFSG.Walter.J1Recog.Assemble
public import CFSG.Walter.J1Recog.Bridge

public section

namespace CFSG.Walter.J1Recog

open Word
open scoped commutatorElement

theorem abel_gen_eq_one : ∀ i : Fin 5,
    Abelianization.of (PresentedGroup.of i : Pres .O1a) = 1 := by
  set f : Fin 5 → Abelianization (Pres .O1a) := fun i => Abelianization.of (PresentedGroup.of i)
  have hrel : ∀ x ∈ relVals .O1a (f 0) (f 1) (f 2) (f 3) (f 4), x = 1 := by
    rw [← forall_ev_rels_iff]
    intro w hw
    have h1 := congrArg Abelianization.of (ev_of_mem hw)
    rw [map_ev, map_one] at h1
    exact h1
  simp only [relVals, p1Vals, hVals, ctVals, extraVal, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hrel
  obtain ⟨ht2, -, hm3, hmn, -, -, -, hn3, -, -, hs2, -, -, hts, hu2, hum, -, -, hct, -⟩ := hrel
  have hn : f 1 = 1 := by
    rw [inv_mul_cancel_comm] at hmn
    have : f 1 * (f 1)⁻¹ ^ 2 = (f 1)⁻¹ := by group
    rw [this] at hmn
    exact inv_eq_one.mp hmn
  have ht : f 0 = 1 := by
    rw [hn, inv_one, one_pow, one_mul, mul_one, one_pow, mul_one] at hn3
    have h3 : f 0 ^ 3 = 1 := by rw [pow_succ, pow_two]; exact hn3
    calc f 0 = f 0 ^ 3 * (f 0 ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, ht2, inv_one, one_mul]
  have hu : f 4 = 1 := by
    rw [ht, hn] at hct
    simp only [mul_one, inv_one] at hct
    calc f 4 = f 4 ^ 5 * (f 4 ^ 2)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hct, hu2, inv_one, one_pow, one_mul]
  have hm : f 2 = 1 := by
    rw [hu, one_mul] at hum
    calc f 2 = f 2 ^ 3 * (f 2 ^ 2)⁻¹ := by group
      _ = 1 := by rw [hm3, hum, inv_one, one_mul]
  have hs : f 3 = 1 := by
    rw [ht, one_mul] at hts
    calc f 3 = f 3 ^ 5 * (f 3 ^ 2)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hts, hs2, inv_one, one_pow, one_mul]
  intro i
  fin_cases i
  · exact ht
  · exact hn
  · exact hm
  · exact hs
  · exact hu

theorem abel_eq_one (x : Pres .O1a) : Abelianization.of x = 1 := by
  induction x using PresentedGroup.induction_on with
  | H z =>
    induction z using FreeGroup.induction_on with
    | one => exact map_one _
    | of i => exact abel_gen_eq_one i
    | inv_of i _ =>
      rw [map_inv, map_inv]
      exact inv_eq_one.mpr (abel_gen_eq_one i)
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy, one_mul]

theorem pres_perfect : commutator (Pres .O1a) = ⊤ := by
  rw [← Abelianization.ker_of, eq_top_iff]
  intro x _
  rw [MonoidHom.mem_ker]
  exact abel_eq_one x

@[expose] def diagT : Fin 7 → ZMod 11 := ![10, 1, 10, 10, 10, 1, 1]

theorem matT_eq : matT = Matrix.diagonal diagT := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matN_eq : matN = Matrix.of fun i k => if k = i + 1 then (1 : ZMod 11) else 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem shift_exists : ∀ i j : Fin 7, i ≠ j →
    ∃ k : Fin 7, diagT ((fun x => x + 1)^[k.val] i) ≠ diagT ((fun x => x + 1)^[k.val] j) := by
  decide

theorem shift_zero : ∀ i : Fin 7, ∃ k : Fin 7, (fun x => x + 1)^[k.val] i = 0 := by
  decide

theorem commutant {X : Matrix (Fin 7) (Fin 7) (ZMod 11)} (hT : X * matT = matT * X)
    (hN : X * matN = matN * X) : X = X 0 0 • (1 : Matrix (Fin 7) (Fin 7) (ZMod 11)) := by
  have hcirc : ∀ i j : Fin 7, X i j = X (i + 1) (j + 1) := by
    intro i j
    have h := congrFun (congrFun hN i) (j + 1)
    rw [matN_eq, Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    have h' : ∀ k : Fin 7, (j + 1 = k + 1) ↔ (k = j) := fun k => by
      constructor
      · intro h; exact (add_right_cancel h).symm
      · rintro rfl; rfl
    simp only [h', Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  have hshift : ∀ (c : ℕ) (i j : Fin 7),
      X i j = X ((fun x => x + 1)^[c] i) ((fun x => x + 1)^[c] j) := by
    intro c
    induction c with
    | zero => intro i j; rfl
    | succ c ih =>
      intro i j
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih, hcirc]
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hzero : ∀ i j : Fin 7, diagT i ≠ diagT j → X i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hT i) j
    rw [matT_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h2 : X i j * (diagT j - diagT i) = 0 := by rw [mul_sub, h, mul_comm]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3).symm hij
  ext i j
  rw [Matrix.smul_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, smul_eq_mul, mul_one]
    obtain ⟨k, hk⟩ := shift_zero i
    rw [hshift k.val i i, hk]
  · rw [Matrix.one_apply_ne hij, smul_zero]
    obtain ⟨k, hk⟩ := shift_exists i j hij
    rw [hshift k.val i j]
    exact hzero _ _ hk

theorem card_pres : Nat.card (Pres .O1a) = 175560 := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  refine le_antisymm hcard ?_
  calc 175560 ≤ Nat.card CFSG.Open.walterJ1 := le_card_walterJ1
    _ ≤ Nat.card toMat.range := Subgroup.card_le_of_le walterJ1_le_range
    _ ≤ Nat.card (Pres .O1a) :=
      Nat.card_le_card_of_surjective _ toMat.rangeRestrict_surjective

theorem toMat_bijective : Function.Bijective toMat.rangeRestrict := by
  have := finite_card_le.1
  refine (toMat.rangeRestrict_surjective).bijective_of_nat_card_le ?_
  rw [card_pres]
  calc 175560 ≤ Nat.card CFSG.Open.walterJ1 := le_card_walterJ1
    _ ≤ Nat.card toMat.range := Subgroup.card_le_of_le walterJ1_le_range

theorem toMat_injective : Function.Injective toMat := fun _ _ h =>
  toMat_bijective.1 (Subtype.ext h)

theorem toMat_range_eq : toMat.range = CFSG.Open.walterJ1 := by
  have := finite_card_le.1
  refine (Subgroup.eq_of_le_of_card_ge walterJ1_le_range ?_).symm
  calc Nat.card toMat.range = Nat.card (Pres .O1a) :=
        (Nat.card_congr (Equiv.ofBijective _ toMat_bijective)).symm
    _ = 175560 := card_pres
    _ ≤ Nat.card CFSG.Open.walterJ1 := le_card_walterJ1

noncomputable def presEquiv : Pres .O1a ≃* CFSG.Open.walterJ1 :=
  (MulEquiv.ofBijective toMat.rangeRestrict toMat_bijective).trans
    (MulEquiv.subgroupCongr toMat_range_eq)

theorem eq_one_of_central {z : Pres .O1a} (hz : ∀ g, g * z = z * g) {p : ℕ}
    (hp : Nat.Coprime p 10) (hzp : z ^ p = 1) : z = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set Z := toMat z with hZ
  have hcomm : ∀ i : Fin 5, ((Z : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) *
      mat i = mat i * Z := by
    intro i
    have hof : toMat (PresentedGroup.of i) = unit i := by
      have := toMat_ev (gen i)
      rwa [ev_gen, ev_gen] at this
    have h := congrArg (fun g => ((toMat g : GL (Fin 7) (ZMod 11)) :
      Matrix (Fin 7) (Fin 7) (ZMod 11))) (hz (PresentedGroup.of i))
    simp only [map_mul, Units.val_mul, hof] at h
    exact h.symm
  have hscal := commutant (hcomm 0) (hcomm 1)
  set c := ((Z : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) 0 0
  have hc : c ≠ 0 := by
    intro h0
    have h1 := Z.val_inv
    rw [hscal, h0, zero_smul, zero_mul] at h1
    have := congrFun (congrFun h1 0) 0
    simp at this
  have h10 : Z ^ 10 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hscal, smul_pow, one_pow,
      show (10 : ℕ) = 11 - 1 from rfl, ZMod.pow_card_sub_one_eq_one hc, one_smul, Units.val_one]
  have hZp : Z ^ p = 1 := by rw [hZ, ← map_pow, hzp, map_one]
  have hZ1 : Z = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one h10
    have h2 := orderOf_dvd_of_pow_eq_one hZp
    have := Nat.dvd_gcd h2 h1
    rw [hp] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  exact toMat_injective (by rw [← hZ, hZ1, map_one])

theorem central_of_normal {Q : Subgroup (Pres .O1a)} [hQ : Q.Normal] {p : ℕ} (hp : p.Prime)
    (hQp : Nat.card Q = p) {z : Pres .O1a} (hzQ : z ∈ Q) : ∀ g, g * z = z * g := by
  by_cases hz1 : z = 1
  · intro g; rw [hz1, mul_one, one_mul]
  have hQz : Q = Subgroup.zpowers z := by
    have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQp]; exact hp.ne_zero)
    have hdvd : orderOf z ∣ p := hQp ▸ Subgroup.orderOf_dvd_natCard Q hzQ
    have hne1 : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.mp h1)
    have hord : orderOf z = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne1
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzQ) ?_).symm
    rw [Nat.card_zpowers, hord, hQp]
  have hpow : ∀ a : Pres .O1a, ∃ k : ℤ, a * z * a⁻¹ = z ^ k := by
    intro a
    have : a * z * a⁻¹ ∈ Q := hQ.conj_mem z hzQ a
    rw [hQz] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk.symm⟩
  have hcomm : ∀ a b : Pres .O1a, ⁅a, b⁆ * z = z * ⁅a, b⁆ := by
    intro a b
    obtain ⟨i, hi⟩ := hpow a⁻¹
    obtain ⟨j, hj⟩ := hpow b⁻¹
    have hab : (a⁻¹ * b⁻¹) * z * (a⁻¹ * b⁻¹)⁻¹ = (b⁻¹ * a⁻¹) * z * (b⁻¹ * a⁻¹)⁻¹ := by
      calc (a⁻¹ * b⁻¹) * z * (a⁻¹ * b⁻¹)⁻¹ = a⁻¹ * (b⁻¹ * z * b⁻¹⁻¹) * a⁻¹⁻¹ := by group
        _ = z ^ (j * i) := by rw [hj, ← conj_zpow, hi, ← zpow_mul, mul_comm]
        _ = b⁻¹ * (a⁻¹ * z * a⁻¹⁻¹) * b⁻¹⁻¹ := by rw [hi, ← conj_zpow, hj, ← zpow_mul]
        _ = (b⁻¹ * a⁻¹) * z * (b⁻¹ * a⁻¹)⁻¹ := by group
    rw [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ * z = (b⁻¹ * a⁻¹)⁻¹ * ((a⁻¹ * b⁻¹) * z * (a⁻¹ * b⁻¹)⁻¹) *
        (a⁻¹ * b⁻¹) := by group
      _ = (b⁻¹ * a⁻¹)⁻¹ * ((b⁻¹ * a⁻¹) * z * (b⁻¹ * a⁻¹)⁻¹) * (a⁻¹ * b⁻¹) := by rw [hab]
      _ = z * (a * b * a⁻¹ * b⁻¹) := by group
  have hle : commutator (Pres .O1a) ≤ Subgroup.centralizer {z} := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a b)
  intro g
  have hg : g ∈ Subgroup.centralizer {z} := hle (pres_perfect ▸ Subgroup.mem_top g)
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

theorem false_of_normal {Q : Subgroup (Pres .O1a)} [Q.Normal] {p : ℕ} (hp : p.Prime)
    (hp10 : Nat.Coprime p 10) (hQp : Nat.card Q = p) : False := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQp]; exact hp.ne_zero)
  obtain ⟨z, hz1⟩ : ∃ z : Q, z ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton Q := ⟨fun a b => by rw [h a, h b]⟩
    rw [Nat.card_unique] at hQp
    exact hp.one_lt.ne hQp
  have hzc := central_of_normal hp hQp z.2
  have hzp : (z : Pres .O1a) ^ p = 1 := by
    have h1 : orderOf z ∣ p := hQp ▸ orderOf_dvd_natCard z
    rw [← Subgroup.orderOf_coe] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  exact hz1 (Subtype.ext (eq_one_of_central hzc hp10 hzp))

theorem exists_normal_nineteen {N : Subgroup (Pres .O1a)} [N.Normal] (hN : Nat.card N = 209) :
    ∃ Q : Subgroup (Pres .O1a), Q.Normal ∧ Nat.card Q = 19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  obtain ⟨P19⟩ : Nonempty (Sylow 19 N) := inferInstance
  have hmul := (P19 : Subgroup N).card_mul_index
  rw [hN] at hmul
  have hcard : Nat.card (P19 : Subgroup N) = 19 := by
    obtain ⟨k, hk⟩ := P19.isPGroup'.exists_card_eq
    have hdvd : 19 ^ k ∣ 209 := ⟨_, by rw [← hk, hmul]⟩
    have hk1 : k ≤ 1 := by
      by_contra h
      have : 19 ^ 2 ∣ 209 := dvd_trans (pow_dvd_pow 19 (by omega)) hdvd
      norm_num at this
    have hidx := P19.not_dvd_index
    interval_cases k
    · exfalso
      apply hidx
      rw [hk, pow_zero, one_mul] at hmul
      rw [hmul]
      norm_num
    · rw [hk, pow_one]
  have hidx : (P19 : Subgroup N).index = 11 := by rw [hcard] at hmul; omega
  have hn := card_sylow_modEq_one 19 N
  have hdiv := P19.card_dvd_index
  rw [hidx] at hdiv
  have h1 : Nat.card (Sylow 19 N) = 1 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hdiv with h | h
    · exact h
    · rw [h] at hn; exact absurd hn (by decide)
  have : Subsingleton (Sylow 19 N) := (Nat.card_eq_one_iff_unique.mp h1).1
  refine ⟨(P19 : Subgroup N).map N.subtype, inferInstance, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective, hcard]

theorem injective_of_dvd {G : Type} [Group G] (φ : Pres .O1a →* G)
    (h840 : 840 ∣ Nat.card φ.range) : Function.Injective φ := by
  have := finite_card_le.1
  have hrange : Nat.card φ.range = φ.ker.index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  have hmul := φ.ker.card_mul_index
  rw [card_pres, ← hrange] at hmul
  obtain ⟨d, hd⟩ := h840
  have hk : Nat.card φ.ker * d = 209 := by
    rw [hd] at hmul
    have : 840 * (Nat.card φ.ker * d) = 840 * 209 := by
      calc 840 * (Nat.card φ.ker * d) = Nat.card φ.ker * (840 * d) := by ring
        _ = 840 * 209 := by rw [hmul]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hdvd : Nat.card φ.ker ∣ 209 := ⟨d, hk.symm⟩
  have hcases : Nat.card φ.ker = 1 ∨ Nat.card φ.ker = 11 ∨ Nat.card φ.ker = 19 ∨
      Nat.card φ.ker = 209 := by
    have hmem : Nat.card φ.ker ∈ Nat.divisors 209 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 209 = {1, 11, 19, 209} := by decide
    rw [hdiv] at hmem
    simpa using hmem
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hcases with h1 | h11 | h19 | h209
  · exact Subgroup.card_eq_one.mp h1
  · exact (false_of_normal (Q := φ.ker) (by norm_num) (by norm_num) h11).elim
  · exact (false_of_normal (Q := φ.ker) (by norm_num) (by norm_num) h19).elim
  · obtain ⟨Q, hQ, hQ19⟩ := exists_normal_nineteen h209
    exact (false_of_normal (Q := Q) (by norm_num) (by norm_num) hQ19).elim

theorem nonempty_mulEquiv_of_config {G : Type} [Group G] [Finite G] (hG : Nat.card G = 175560)
    (c : Case) (f : Fin 5 → G) (hf : ∀ w ∈ rels c, ev f w = 1)
    (hs : f 3 ∉ Subgroup.closure {f 0, f 1, f 2})
    (h840 : 840 ∣ Nat.card (Subgroup.closure (Set.range f))) :
    Nonempty (G ≃* CFSG.Open.walterJ1) := by
  set φ := lift (rels c) f hf
  have hmap : (tnm c).map φ = Subgroup.closure {f 0, f 1, f 2} := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, φ]
  have hs' : PresentedGroup.of 3 ∉ tnm c := fun h3 => hs (by
    rw [← hmap, ← lift_of (rels c) f hf 3]
    exact Subgroup.mem_map_of_mem _ h3)
  cases c with
  | O1b => exact absurd (tnm_eq_top_O1b ▸ Subgroup.mem_top _) hs'
  | O2a => exact absurd (tnm_eq_top_O2a ▸ Subgroup.mem_top _) hs'
  | O2b => exact absurd (tnm_eq_top_O2b ▸ Subgroup.mem_top _) hs'
  | O1a =>
    have := finite_card_le.1
    have hrange : φ.range = Subgroup.closure (Set.range f) := by
      rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
        ← Set.range_comp]
      congr 1
      exact congrArg Set.range (funext fun i => lift_of _ _ _ i)
    have hinj : Function.Injective φ := injective_of_dvd φ (hrange ▸ h840)
    have hbij : Function.Bijective φ :=
      hinj.bijective_of_nat_card_le (by rw [hG, card_pres])
    exact ⟨(MulEquiv.ofBijective φ hbij).symm.trans presEquiv⟩

end CFSG.Walter.J1Recog
