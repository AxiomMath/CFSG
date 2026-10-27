module

public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.Lin26Frattini
public import CFSG.RankThree.GF2n.Stroth80.Sec36

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

section Scalar

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private theorem exists_pi_ne_zero (H : StrothHyp M Q Z) : ∃ e : M₀.E, e ≠ 0 := by
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hne : Q ≠ Z := H.toHyp79.ne
  obtain ⟨x, hxQ, hxZ⟩ : ∃ x ∈ Q, x ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hcon hZQ)
  exact ⟨M₀.π x, fun h => hxZ ((M₀.π_ker x hxQ).mp h)⟩

private theorem exists_B_eq (e : M₀.E) (he : e ≠ 0) (s : K) : ∃ f : M₀.E, M₀.B e f = s := by
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, M₀.B e f₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he (M₀.nondeg e hcon)
  refine ⟨(s / M₀.B e f₀) • f₀, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf₀]

private theorem eq_one_of_sq_eq_one {x : K} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (x - 1) ^ 2 = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

private theorem exists_prime_power_ne_one {ν : Kˣ} (hν : ν ≠ 1) :
    ∃ (p : ℕ), p.Prime ∧ ∃ j : ℕ, p ≠ 2 ∧ (ν ^ j) ^ p = 1 ∧ ν ^ j ≠ 1 := by
  have hr1 : orderOf ν ≠ 1 := fun h => hν (orderOf_eq_one_iff.mp h)
  have hrpos : 0 < orderOf ν := orderOf_pos ν
  have hp : (orderOf ν).minFac.Prime := Nat.minFac_prime hr1
  have hpd : (orderOf ν).minFac ∣ orderOf ν := Nat.minFac_dvd _
  have hj0 : orderOf ν / (orderOf ν).minFac ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hrpos hpd) hp.pos).ne'
  have hjlt : orderOf ν / (orderOf ν).minFac < orderOf ν :=
    Nat.div_lt_self hrpos hp.one_lt
  have hne : ν ^ (orderOf ν / (orderOf ν).minFac) ≠ 1 := pow_ne_one_of_lt_orderOf hj0 hjlt
  have hpow : (ν ^ (orderOf ν / (orderOf ν).minFac)) ^ (orderOf ν).minFac = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hpd, pow_orderOf_eq_one]
  obtain ⟨p, hpdef⟩ : ∃ p, p = (orderOf ν).minFac := ⟨_, rfl⟩
  rw [← hpdef] at hp hpd hj0 hjlt hne hpow
  refine ⟨p, hp, orderOf ν / p, ?_, hpow, hne⟩
  intro h2
  subst h2
  apply hne
  apply Units.ext
  rw [Units.val_one]
  refine eq_one_of_sq_eq_one ?_
  have h3 := congrArg Units.val hpow
  rw [Units.val_pow_eq_pow_val, Units.val_one] at h3
  exact h3

private theorem perm_pow_apply {E : Type*} [AddCommGroup E] [Module K E] (f : Equiv.Perm E)
    (μ : K) (hf : ∀ e, f e = μ • e) (j : ℕ) (e : E) : (f ^ j) e = μ ^ j • e := by
  induction j generalizing e with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, hf, ih, smul_smul, pow_succ]

private theorem hactZ_aux (H : StrothHyp M Q Z) (gm : GlobalModelData M Q Z γ M₀)
    (Φ : ↥M →* Equiv.Perm M₀.E)
    (hΦπ : ∀ (m : ↥M) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = Φ m (M₀.π x))
    {ν' : K} (w : ↥M) (hw : ∀ e, Φ w e = ν' • e) (z : G) (hz : z ∈ Z) :
    γ ((w : G) * z * (w : G)⁻¹) = ν' ^ 2 * γ z := by
  obtain ⟨e₀, he₀⟩ := exists_pi_ne_zero (M₀ := M₀) H
  obtain ⟨f, hf⟩ := exists_B_eq (M₀ := M₀) e₀ he₀ (γ z)
  obtain ⟨x₀, hx₀Q, hx₀⟩ := M₀.π_surj e₀
  obtain ⟨x₁, hx₁Q, hx₁⟩ := M₀.π_surj f
  have hzc : ⁅x₀, x₁⁆ = z := by
    refine gm.reg.eq_of_γ_eq (comm_mem_Z H hx₀Q hx₁Q) hz ?_
    rw [M₀.comm_eq x₀ hx₀Q x₁ hx₁Q, hx₀, hx₁, hf]
  have hconj : (w : G) * z * (w : G)⁻¹ =
      ⁅(w : G) * x₀ * (w : G)⁻¹, (w : G) * x₁ * (w : G)⁻¹⁆ := by
    rw [← hzc]
    simp only [commutatorElement_def]
    group
  rw [hconj, M₀.comm_eq _ (conj_mem_Q H w.2 hx₀Q) _ (conj_mem_Q H w.2 hx₁Q),
    hΦπ w x₀ hx₀Q, hΦπ w x₁ hx₁Q, hx₀, hx₁, hw, hw]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hf]
  ring

theorem exists_scalar_normal_of_scalar (H : StrothHyp M Q Z) (gm : GlobalModelData M Q Z γ M₀)
    {S : Subgroup G} (hS : S ≤ H0 M Z) {c : G} (hcM : c ∈ M) {ν : Kˣ} (hν : ν ≠ 1)
    (hc : ∀ x ∈ Q, M₀.π (c * x * c⁻¹) = (ν : K) • M₀.π x) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ A : Subgroup G, Q ≤ A ∧ A ≤ M ∧
      M ≤ Subgroup.normalizer (A : Set G) ∧ (∀ a ∈ A, ∃ k : ℕ, a ^ p ^ k ∈ Q) ∧
      (∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ * s⁻¹ ∈ Q) ∧
      ∃ c' ∈ A, ∀ u ∈ Q, ∀ y ∈ Q, y * (c' * u) = c' * u * y → y = 1 := by
  classical
  have hQM : Q ≤ M := H.Q_normal.1
  obtain ⟨Φ, hΦπ, hΦker, hΦadd, hΦσ⟩ := exists_actionHom_M H gm
  set c₀ : ↥M := ⟨c, hcM⟩ with hc₀
  have hΦc : ∀ e, Φ c₀ e = (ν : K) • e := by
    intro e
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    rw [← hΦπ c₀ x hx]
    exact hc x hx
  obtain ⟨p, hp, j, hp2, hνp, hνj⟩ := exists_prime_power_ne_one (K := K) hν
  haveI : Fact p.Prime := ⟨hp⟩
  set ν' : K := ((ν ^ j : Kˣ) : K) with hν'
  have hν'1 : ν' ≠ 1 := fun h => hνj (Units.ext h)
  have hν'p : ν' ^ p = 1 := by
    have := congrArg Units.val hνp
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hΦcj : ∀ e, Φ (c₀ ^ j) e = ν' • e := by
    intro e
    rw [map_pow, perm_pow_apply (Φ c₀) (ν : K) hΦc j e, hν', Units.val_pow_eq_pow_val]
  let A₀ : Subgroup ↥M :=
    { carrier := {m | ∃ μ : K, μ ^ p = 1 ∧ ∀ e, Φ m e = μ • e}
      mul_mem' := by
        rintro a b ⟨μ₁, h₁, hμ₁⟩ ⟨μ₂, h₂, hμ₂⟩
        refine ⟨μ₁ * μ₂, by rw [mul_pow, h₁, h₂, one_mul], fun e => ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hμ₂, hμ₁, smul_smul]
      one_mem' := ⟨1, one_pow _, fun e => by simp⟩
      inv_mem' := by
        rintro a ⟨μ, h₁, hμ⟩
        have hμ0 : μ ≠ 0 := fun h0 => by
          rw [h0, zero_pow hp.ne_zero] at h₁
          exact zero_ne_one h₁
        refine ⟨μ⁻¹, by rw [inv_pow, h₁, inv_one], fun e => ?_⟩
        have h3 : Φ a (Φ a⁻¹ e) = e := by
          rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        rw [hμ] at h3
        exact ((inv_smul_eq_iff₀ hμ0).mpr h3.symm).symm }
  have hAmem : ∀ a, a ∈ A₀ ↔ ∃ μ : K, μ ^ p = 1 ∧ ∀ e, Φ a e = μ • e := fun a => Iff.rfl
  haveI hAn : A₀.Normal := ⟨fun a ha g => by
    obtain ⟨μ, h₁, hμ⟩ := (hAmem a).mp ha
    obtain ⟨σ, hσ⟩ := hΦσ g
    refine (hAmem _).mpr ⟨σ μ, by rw [← map_pow, h₁, map_one], fun e => ?_⟩
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hμ, hσ,
      ← Equiv.Perm.mul_apply (Φ g) (Φ g⁻¹) e, ← map_mul, mul_inv_cancel, map_one]
    rfl⟩
  have hkA : Φ.ker ≤ A₀ := fun m hm => (hAmem m).mpr ⟨1, one_pow _, fun e => by
    rw [MonoidHom.mem_ker.mp hm]; simp⟩
  have hAp : ∀ a ∈ A₀, Φ a ^ p = 1 := by
    intro a ha
    obtain ⟨μ, h₁, hμ⟩ := (hAmem a).mp ha
    ext e
    rw [perm_pow_apply (Φ a) μ hμ p e, h₁, one_smul]
    rfl
  have hcjA : c₀ ^ j ∈ A₀ := (hAmem _).mpr ⟨ν', hν'p, hΦcj⟩
  have hΦlin : ∀ (s : ↥M), (s : G) ∈ H0 M Z → ∀ (a : K) (e : M₀.E), Φ s (a • e) = a • Φ s e := by
    intro s hs a e
    obtain ⟨T, hT1, -, -⟩ := gm.linear_of_centralizes s.2 (fun z hz => by
      have := Subgroup.mem_centralizer_iff.mp hs.2 z hz
      rw [← this]; group)
    have hTΦ : ∀ e, Φ s e = T e := fun e =>
      congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (s : G)) (S₁ := Φ s) (S₂ := T)
        (hΦπ s) hT1) e
    rw [hTΦ, hTΦ, map_smul]
  have hfpf : ∀ w : ↥M, Φ w = Φ (c₀ ^ j) → ∀ y ∈ Φ.ker, w * y = y * w → y = 1 := by
    intro w hw y hy hwy
    have hyQ : (y : G) ∈ Q := (hΦker y).mp hy
    have hΦw : ∀ e, Φ w e = ν' • e := fun e => by rw [hw]; exact hΦcj e
    have hwx : (w : G) * (y : G) * (w : G)⁻¹ = (y : G) := by
      have := congrArg Subtype.val hwy
      simp only [Subgroup.coe_mul] at this
      rw [this]
      group
    have h1 : M₀.π (y : G) = ν' • M₀.π (y : G) := by
      conv_lhs => rw [← hwx, hΦπ w (y : G) hyQ, hΦw]
    have h2' : M₀.π (y : G) = 0 := by
      have h3 : (1 - ν') • M₀.π (y : G) = 0 := by
        rw [sub_smul, one_smul, ← h1, sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4).symm hν'1
      · exact h4
    have hyZ : (y : G) ∈ Z := (M₀.π_ker (y : G) hyQ).mp h2'
    have h5 : γ (y : G) = ν' ^ 2 * γ (y : G) := by
      conv_lhs => rw [← hwx]
      exact hactZ_aux H gm Φ hΦπ w hΦw (y : G) hyZ
    have h6 : (ν' ^ 2 - 1) * γ (y : G) = 0 := by linear_combination -h5
    have h7 : ν' ^ 2 - 1 ≠ 0 := fun h => hν'1 (eq_one_of_sq_eq_one (sub_eq_zero.mp h))
    have h8 : γ (y : G) = 0 := (mul_eq_zero.mp h6).resolve_left h7
    have h9 : (y : G) = 1 := gm.reg.inj _ hyZ h8
    exact Subtype.ext h9
  refine ⟨p, hp, hp2, A₀.map M.subtype, ?_, Subgroup.map_subtype_le A₀, ?_, ?_, ?_,
    ((c₀ ^ j : ↥M) : G), ⟨c₀ ^ j, hcjA, rfl⟩, ?_⟩
  · intro x hx
    exact ⟨⟨x, hQM hx⟩, hkA ((hΦker ⟨x, hQM hx⟩).mpr hx), rfl⟩
  · intro m hm
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact ⟨⟨m, hm⟩ * a₀ * ⟨m, hm⟩⁻¹, hAn.conj_mem a₀ ha₀ ⟨m, hm⟩, by simp⟩
  · rintro a ⟨a₀, ha₀, rfl⟩
    refine ⟨1, ?_⟩
    rw [pow_one]
    have h1 : Φ (a₀ ^ p) = 1 := by rw [map_pow]; exact hAp a₀ ha₀
    have := (hΦker (a₀ ^ p)).mp h1
    simpa using this
  · rintro a ⟨a₀, ha₀, rfl⟩ s hs'
    have hsH := hS hs'
    set s₀ : ↥M := ⟨s, hsH.1⟩ with hs₀
    obtain ⟨μ, h₁, hμ⟩ := (hAmem a₀).mp ha₀
    have hμ0 : μ ≠ 0 := fun h0 => by
      rw [h0, zero_pow hp.ne_zero] at h₁
      exact zero_ne_one h₁
    have hinv : ∀ e, Φ a₀⁻¹ e = μ⁻¹ • e := fun e => by
      have h3 : Φ a₀ (Φ a₀⁻¹ e) = e := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [hμ] at h3
      exact ((inv_smul_eq_iff₀ hμ0).mpr h3.symm).symm
    have h4 : Φ (a₀ * s₀ * a₀⁻¹ * s₀⁻¹) = 1 := by
      refine Equiv.ext fun e => ?_
      have hlin := hΦlin s₀ hsH
      have h5 : Φ s₀ (Φ s₀⁻¹ e) = e := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      simp only [map_mul, Equiv.Perm.mul_apply]
      rw [hinv, hlin, h5, hμ, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      rfl
    have := (hΦker _).mp h4
    simpa using this
  · intro u hu y hy hyc
    have hu' : Φ ⟨u, hQM hu⟩ = 1 := (hΦker ⟨u, hQM hu⟩).mpr hu
    have hw : Φ (c₀ ^ j * ⟨u, hQM hu⟩) = Φ (c₀ ^ j) := by rw [map_mul, hu', mul_one]
    refine congrArg Subtype.val (hfpf (c₀ ^ j * ⟨u, hQM hu⟩) hw ⟨y, hQM hy⟩
      ((hΦker ⟨y, hQM hy⟩).mpr hy) ?_)
    apply Subtype.ext
    exact hyc.symm

end Scalar

@[expose] def Lin26ScalarStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 2 ≤ n →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
        ∃ c ∈ M, ∃ ν : Kˣ, ν ≠ 1 ∧ ∀ x ∈ Q, M₀.π (c * x * c⁻¹) = (ν : K) • M₀.π x

theorem lin26Statement_of_scalar (h : Lin26ScalarStatement) :
    Lin26Statement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn
  obtain ⟨K, _, _, _, γ, M₀, gm, c, hcM, ν, hν, hcπ⟩ := h G M Q Z B n V₁ V₂ hb hc hS hn
  obtain ⟨p, hp, hp2, A, hQA, hAM, hAn, hpow, -, c', hc'A, hfpf⟩ :=
    exists_scalar_normal_of_scalar hc.hyp gm (S := ⊥) bot_le hcM hν hcπ
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  obtain ⟨K', hK'M, hK'Q, hK's, -⟩ := exists_compl_mem_of_frattini hp2 hQ2 hQA hAM
    hc.hyp.Q_normal.2 hAn hpow hc'A hfpf (x := 1) M.one_mem fun a _ => ⟨1, Q.one_mem, by simp⟩
  exact ⟨K', hK'M, hK'Q, hK's⟩

end CFSG.RankThree.GF2n.Smith81
