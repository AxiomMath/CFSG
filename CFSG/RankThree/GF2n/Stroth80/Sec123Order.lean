module

public import CFSG.RankThree.GF2n.Stroth80.Sec123Aux
public import CFSG.RankThree.GF2n.Stroth80.Sec12LBFlag
public import CFSG.RankThree.GF2n.Stroth80.Sec12MixedRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Satz5Omega
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_QB_of_mem_normalizer (hc : Ctx M Q Z B) {a s : G}
    (ha : a ∈ Subgroup.normalizer (B : Set G)) (hs : s ∈ QB B) : a * s * a⁻¹ ∈ QB B := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨hN, hQB⟩ := Ctx.QB_eq hc hg
  rw [hN, mem_conjSubgroup] at ha
  rw [hQB, mem_conjSubgroup] at hs ⊢
  have h1 : g⁻¹ * a * g ∈ M := ha
  have h2 : (g⁻¹ * a * g) * (g⁻¹ * s * g) * (g⁻¹ * a * g)⁻¹ ∈ Q :=
    (hc.conj_mem_Q_of_mem_M h1).1 _ hs
  have e : g⁻¹ * (a * s * a⁻¹) * g = (g⁻¹ * a * g) * (g⁻¹ * s * g) * (g⁻¹ * a * g)⁻¹ := by
    group
  rw [e]
  exact h2

theorem Ctx.comm_LB_mem_inf (hc : Ctx M Q Z B) {r x : G} (hr : r ∈ LB M Q B) (hxQ : x ∈ Q)
    (hxB : x ∈ Subgroup.centralizer (B : Set G)) : ⁅r, x⁆ ∈ Q ⊓ QB B := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hr
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
  have hsQB : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
  have hZD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q (hc.Z_le_QB).1
  have e : ⁅s * y, x⁆ = (s * ⁅y, x⁆ * s⁻¹) * ⁅s, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have h1 : ⁅y, x⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy hxQ
  have h2 : s * ⁅y, x⁆ * s⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsM) _).mp h1
  have hxN : x ∈ Subgroup.normalizer (B : Set G) :=
    (Subgroup.centralizer_le_normalizer (B : Set G)) hxB
  have h3 : ⁅s, x⁆ ∈ Q ⊓ QB B := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have : s * x * s⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hsM).1 x hxQ
      rw [commutatorElement_def]
      have e2 : s * x * s⁻¹ * x⁻¹ = (s * x * s⁻¹) * x⁻¹ := rfl
      rw [e2]
      exact Q.mul_mem this (Q.inv_mem hxQ)
    · have hxs : x * s⁻¹ * x⁻¹ ∈ QB B := hc.conj_QB_of_mem_normalizer hxN ((QB B).inv_mem hsQB)
      have e2 : ⁅s, x⁆ = s * (x * s⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e2]
      exact (QB B).mul_mem hsQB hxs
  exact (Q ⊓ QB B).mul_mem (hZD h2) h3


section Eichler

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.LB_eichler_of_prod (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hb0 : b ≠ 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (hD : ∀ d ∈ Q ⊓ QB B, ∃ z ∈ Z, ∃ b' ∈ B, d = z * b') {r : G} (hr : r ∈ LB M Q B)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x))
    (hiso : ∀ e, M₀.Qf (T e) = M₀.Qf e) :
    ∃ v : M₀.E, M₀.B v b = 0 ∧ ∀ y : M₀.E,
      T y = y + M₀.B y b • v + M₀.B y v • b + (M₀.Qf v * M₀.B y b) • b := by
  refine eichler_of_isometry M₀ hiso hb0 (hc.LB_act_fix_line h hB hr hT).1 fun y hy => ?_
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj y
  have hxC : x ∈ Subgroup.centralizer (B : Set G) := (hcent x hxQ).mpr hy
  have hcomm : ⁅r, x⁆ ∈ Q ⊓ QB B := hc.comm_LB_mem_inf hr hxQ hxC
  obtain ⟨z, hz, b', hb', hzb⟩ := hD _ hcomm
  have hrQ : ⁅r, x⁆ ∈ Q := (Subgroup.mem_inf.mp hcomm).1
  have hzQ : z ∈ Q := hc.Z_le_Q hz
  have hb'Q : b' ∈ Q := hc.le hb'
  have e : r * x * r⁻¹ = ⁅r, x⁆ * x := by
    rw [commutatorElement_def]
    group
  have hπ : M₀.π (r * x * r⁻¹) = M₀.π b' + M₀.π x := by
    rw [e, M₀.π_mul _ hrQ _ hxQ, hzb, M₀.π_mul _ hzQ _ hb'Q,
      (M₀.π_ker z hzQ).mpr hz, zero_add]
  obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hb' hb'Q)
  refine ⟨s, ?_⟩
  rw [← hT x hxQ, hπ, hs, add_comm]

end Eichler

section PartOne

open CFSG.ClassicalGroups.Orthogonal

theorem polarBilin_toQuadraticForm_nondegenerate {QF V : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel QF V K γ) :
    (QuadraticMap.polarBilin M₀.toQuadraticForm).Nondegenerate := by
  have hpolar : ∀ x y, QuadraticMap.polar M₀.toQuadraticForm x y = M₀.B x y :=
    Tim79.QuadModel.polar_toQuadraticForm M₀
  have hBeq : QuadraticMap.polarBilin M₀.toQuadraticForm = M₀.B := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [QuadraticMap.polarBilin_apply_apply, hpolar]
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]
  rw [hBeq]
  exact hnd

theorem Ctx.card_LB_lt_of_width_two (hc : Ctx M Q Z B) (hw : Width Q Z 2) :
    Nat.card (LB M Q B) < Nat.card Q * Nat.card Z ^ 2 := by
  classical
  by_contra hge
  push Not at hge
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hKcard : Nat.card K = Nat.card Z := h.card
  have hK1 : 1 < Nat.card K := by omega
  have hdim : Module.finrank K M₀.E = 4 := h.finrank_E hw hK1
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  obtain ⟨Φ, hΦπ, hΦker, hΦiso⟩ := hc.exists_actionHom_LB h
  have hBcard : Nat.card B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hZD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q (hc.Z_le_QB).1
  have hBD : B ≤ Q ⊓ QB B := le_inf hc.le hc.B_le_QB
  have hDle := card_mul_le_of_inf_eq_bot hZD hBD hc.inf_eq_bot
  rw [hBcard] at hDle
  have hmul := hc.card_LB_mul hw
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hLpos : 0 < Nat.card (LB M Q B) := Nat.card_pos
  have hD2 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ 2 := by
    have h1 : Nat.card Z ^ 2 ≤ Nat.card ↥(Q ⊓ QB B) := by nlinarith
    by_contra hne
    have h3 : Nat.card Z ^ 2 < Nat.card ↥(Q ⊓ QB B) := lt_of_le_of_ne h1 (Ne.symm hne)
    have h4 : Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 <
        Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) :=
      calc Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2
          ≤ Nat.card (LB M Q B) * Nat.card Z ^ 2 := Nat.mul_le_mul_right _ hge
        _ < Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) := Nat.mul_lt_mul_of_pos_left h3 hLpos
    have e : Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 = Nat.card Q * Nat.card Z ^ (2 * 2) := by
      ring
    rw [hmul, e] at h4
    exact lt_irrefl _ h4
  have hL2 : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ 2 := by
    have h5 : Nat.card (LB M Q B) * Nat.card Z ^ 2 =
        Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 :=
      calc Nat.card (LB M Q B) * Nat.card Z ^ 2
          = Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) := by rw [hD2]
        _ = Nat.card Q * Nat.card Z ^ (2 * 2) := hmul
        _ = Nat.card Q * Nat.card Z ^ 2 * Nat.card Z ^ 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h5
  have hprod : ∀ d ∈ Q ⊓ QB B, ∃ z ∈ Z, ∃ b' ∈ B, d = z * b' :=
    exists_mul_of_card_eq hZD hBD hc.inf_eq_bot (by rw [hD2, hBcard]; ring)
  have hpolar : ∀ x y, QuadraticMap.polar M₀.toQuadraticForm x y = M₀.B x y :=
    Tim79.QuadModel.polar_toQuadraticForm M₀
  have hQ'b : M₀.toQuadraticForm b = 0 := hbs
  have hmem : ∀ r : ↥(LB M Q B), Φ r ∈ rootGroup M₀.toQuadraticForm b := by
    intro r
    obtain ⟨v, hvb, hv⟩ := hc.LB_eichler_of_prod h hb0 hB hcent hprod r.2
      (T := (Φ r).toLinearMap) (hΦπ r) (hΦiso r)
    refine mem_rootGroup_of_formula (v := v) h2 hQ'b ?_ (Φ r) fun y => ?_
    · rw [hpolar, Tim79.QuadModel.B_comm, hvb, neg_zero]
    · rw [hpolar, hpolar]
      exact hv y
  have hrange : Φ.range ≤ rootGroup M₀.toQuadraticForm b := by
    rintro _ ⟨r, rfl⟩
    exact hmem r
  have hcardroot : Nat.card (rootGroup M₀.toQuadraticForm b) = Nat.card Z ^ 2 := by
    rw [card_rootGroup (polarBilin_toQuadraticForm_nondegenerate M₀) hQ'b hb0, hdim, hKcard]
  have hcardrange : Nat.card Φ.range = Nat.card Z ^ 2 := by
    have h6 := card_eq_card_mul_range (H := LB M Q B) le_sup_left Φ hΦker
    rw [hL2] at h6
    exact (Nat.eq_of_mul_eq_mul_left hQpos h6).symm
  haveI : Finite (rootGroup M₀.toQuadraticForm b) :=
    Nat.finite_of_card_ne_zero (by rw [hcardroot]; positivity)
  have hreq : Φ.range = rootGroup M₀.toQuadraticForm b :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardroot, hcardrange])
  obtain ⟨S₁, S₂, hS, hS₁, hS₂⟩ := h.hyperbolic
  obtain ⟨v₁, w₁, w₂, hqv₁, hqw₁, hqw₂, b11, b22, b12, b21, vv, ww⟩ :=
    Satz5.exists_hyperbolic_triple_of_singular M₀ hS hS₁ hS₂ (by omega) hb0 hbs
  have S : Satz5.Setting M₀ (LB M Q B) v₁ b w₁ w₂ :=
    { reg := h.reg
      two := h2
      b11 := b11
      b22 := b22
      b12 := b12
      b21 := b21
      vv := vv
      ww := ww
      norm := fun g hg x hx => (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hg)).1 x hx
      cent := fun g hg z hz => hc.LB_centralizes_Z hg z hz
      faith := fun g hg htriv => by
        have hΦ1 : Φ ⟨g, hg⟩ = 1 := by
          refine LinearEquiv.ext fun e => ?_
          obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
          rw [← hΦπ ⟨g, hg⟩ y hyQ, htriv y hyQ]
          rfl
        exact ⟨g, (hΦker ⟨g, hg⟩).mp hΦ1, fun x _ => rfl⟩ }
  obtain ⟨ν, hν0, hν1⟩ := Satz5.exists_ne_zero_one (by omega : 2 < Nat.card K)
  refine S.false_of_rootLifts hν0 hν1 (fun l _ => ?_) (fun m _ => ?_)
  · have hpol : QuadraticMap.polar M₀.toQuadraticForm b (l • w₁) = 0 := by
      rw [hpolar, map_smul, smul_eq_mul, b21, mul_zero]
    have hg : eichler M₀.toQuadraticForm b (l • w₁) ∈ rootGroup M₀.toQuadraticForm b :=
      mem_rootGroup.mpr ⟨l • w₁, hpol, rfl⟩
    rw [← hreq] at hg
    obtain ⟨r, hr⟩ := hg
    refine ⟨r, r.2, fun x hx => ?_⟩
    rw [hΦπ r x hx, hr, S.rootA_eq_eichler hbs hqw₁]
  · have hpol : QuadraticMap.polar M₀.toQuadraticForm b (m • v₁) = 0 := by
      rw [hpolar, map_smul, smul_eq_mul, Tim79.QuadModel.B_comm, vv, neg_zero, mul_zero]
    have hg : eichler M₀.toQuadraticForm b (m • v₁) ∈ rootGroup M₀.toQuadraticForm b :=
      mem_rootGroup.mpr ⟨m • v₁, hpol, rfl⟩
    rw [← hreq] at hg
    obtain ⟨r, hr⟩ := hg
    refine ⟨r, r.2, fun x hx => ?_⟩
    rw [hΦπ r x hx, hr, S.rootB_eq_eichler hbs hqv₁]

end PartOne

@[expose] def Stroth123FixedPointFreeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → Width Q Z 2 →
    ∃ τ : G, τ ∈ M ∧ orderOf τ = Nat.card Z - 1 ∧ (∀ l ∈ LB M Q B, τ * l * τ⁻¹ ∈ LB M Q B) ∧
      ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
        τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q

@[expose] def Stroth123SL2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → Width Q Z 2 →
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z →
    QuotSat (Lgen M (LB M Q B)) Q (IsSLModel 2 (Nat.card Z))

theorem Ctx.card_LB_eq_of_fpf (hc : Ctx M Q Z B) (hw : Width Q Z 2) {τ : G} (hτ : τ ∈ M)
    (hord : orderOf τ = Nat.card Z - 1) (hτL : ∀ l ∈ LB M Q B, τ * l * τ⁻¹ ∈ LB M Q B)
    (hfree : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
      τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q) :
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z := by
  classical
  obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
  have hlt := hc.card_LB_lt_of_width_two hw
  have hge := hc.card_LB_ge hw (by norm_num : 1 ≤ 2)
  have hmul := hc.card_LB_mul hw
  have hQ : Nat.card Q = Nat.card Z ^ 5 := hw
  have hτQ : ∀ x ∈ Q, τ * x * τ⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hτ).1
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hfree' : ∀ i : ℕ, 0 < i → i < orderOf τ → ∀ l ∈ LB M Q B,
      τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q := by
    rw [hord]
    exact hfree
  have hcount := card_conj_free_dvd (le_sup_left : Q ≤ LB M Q B) hτL hτQ hfree'
  rw [hord] at hcount
  have hr2 : 2 ≤ r := by
    by_contra hcon
    have : r ≤ 1 := by omega
    have h4 : Nat.card Z ≤ 2 := by
      rw [hr]
      calc 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 := by norm_num
    omega
  have hdvd : Nat.card (LB M Q B) ∣ 2 ^ (9 * r) := by
    refine Dvd.intro _ (hmul.trans ?_)
    rw [hQ, hr, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hQ' : Nat.card Q = 2 ^ (5 * r) := by rw [hQ, hr, ← pow_mul, mul_comm]
  have hge' : 2 ^ (6 * r) ≤ 2 ^ m := by
    rw [← hm]
    calc 2 ^ (6 * r) = Nat.card Q * Nat.card Z := by
          rw [hQ', hr, ← pow_add]
          congr 1
          ring
      _ = Nat.card Q * Nat.card Z ^ (2 - 1) := by norm_num
      _ ≤ Nat.card (LB M Q B) := hge
  have hlt' : 2 ^ m < 2 ^ (7 * r) := by
    rw [← hm]
    calc Nat.card (LB M Q B) < Nat.card Q * Nat.card Z ^ 2 := hlt
      _ = 2 ^ (7 * r) := by
          rw [hQ', hr, ← pow_mul, ← pow_add]
          congr 1
          ring
  have h6 : 6 * r ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge'
  have h7 : m < 7 * r := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt'
  obtain ⟨k, hk⟩ : ∃ k, m = 5 * r + k := ⟨m - 5 * r, by omega⟩
  have hdiv : 2 ^ r - 1 ∣ 2 ^ (5 * r) * (2 ^ k - 1) := by
    have h8 : Nat.card (LB M Q B) - Nat.card Q = 2 ^ (5 * r) * (2 ^ k - 1) := by
      rw [hm, hQ', hk, pow_add, Nat.mul_sub, mul_one]
    rw [← h8, ← hr]
    exact hcount
  have hodd : Odd (2 ^ r - 1) := by
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have h2 : Even (2 ^ r) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨c, hc'⟩ := h2
    exact ⟨c - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ r - 1) (2 ^ (5 * r)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hdiv' : 2 ^ r - 1 ∣ 2 ^ k - 1 := hcop.dvd_of_dvd_mul_left hdiv
  have hkr : k = r :=
    eq_of_two_pow_bounds (by omega) hdiv' (Nat.pow_le_pow_right (by norm_num) (by omega))
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [hm, hQ', hr, hk, hkr, ← pow_add]

theorem stroth123Order_of_fpf (hF : Stroth123FixedPointFreeStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → Width Q Z 2 →
      Nat.card (LB M Q B) = Nat.card Q * Nat.card Z := by
  intro G _ _ M Q Z B hc hw
  obtain ⟨τ, hτM, hord, hτL, hfree⟩ := hF G M Q Z B hc hw
  exact hc.card_LB_eq_of_fpf hw hτM hord hτL hfree

theorem stroth123_of_fpf_sl2 (hF : Stroth123FixedPointFreeStatement)
    (hS : Stroth123SL2Statement) : Stroth123Statement := by
  intro G _ _ M Q Z B hc hw
  exact hS G M Q Z B hc hw (stroth123Order_of_fpf hF G M Q Z B hc hw)

end CFSG.RankThree.GF2n.Stroth80
