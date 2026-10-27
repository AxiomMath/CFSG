module

public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Assembly (IsElemAbelian)

@[expose] def HasFusionTarget (X : Type) [Group X] : Prop :=
  ∃ A₀ : Subgroup X, IsElemAbelian 3 A₀ ∧
    ∀ B : Subgroup X, IsElemAbelian 3 B → ∃ x : X, B.map (MulAut.conj x).toMonoidHom ≤ A₀

section Basic

variable {X Y : Type} [Group X] [Group Y]

theorem isElemAbelian_map (f : X →* Y) {B : Subgroup X} (hB : IsElemAbelian 3 B) :
    IsElemAbelian 3 (B.map f) := CFSG.Open.IsElemAbelian.map hB _

theorem isPGroup_of_isElemAbelian {B : Subgroup X} (hB : IsElemAbelian 3 B) : IsPGroup 3 B :=
  CFSG.Open.IsElemAbelian.isPGroup hB

theorem map_conj_map_conj (B : Subgroup X) (x y : X) :
    (B.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      B.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem HasFusionTarget.of_mulEquiv (e : X ≃* Y) (h : HasFusionTarget X) : HasFusionTarget Y := by
  obtain ⟨A₀, hA₀, hfuse⟩ := h
  refine ⟨A₀.map e.toMonoidHom, isElemAbelian_map _ hA₀, fun B hB => ?_⟩
  obtain ⟨x, hx⟩ := hfuse (B.map e.symm.toMonoidHom) (isElemAbelian_map _ hB)
  refine ⟨e x, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨x * e.symm b * x⁻¹, hx ⟨e.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
  simp

end Basic

theorem elemAbelianFusedIntoJ_of_hasFusionTarget {X : Type} [Group X] [Finite X]
    (h : HasFusionTarget X) : ElemAbelianFusedIntoJ X := by
  obtain ⟨A₀, hA₀, hfuse⟩ := h
  intro P B _ hB
  obtain ⟨Q, hQ⟩ := (isPGroup_of_isElemAbelian hA₀).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X Q P
  set A₁ := A₀.map (MulAut.conj h).toMonoidHom with hA₁def
  have hA₁P : A₁ ≤ (P : Subgroup X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj h)⁻¹ • (MulAut.conj h).toMonoidHom a = a := by
      rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]
    rw [this]
    exact hQ ha
  have hA₁ : IsElemAbelian 3 A₁ := isElemAbelian_map _ hA₀
  have hcardA₁ : Nat.card A₁ = Nat.card A₀ :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hA₀).exists_card_eq
  set E := A₁.subgroupOf (P : Subgroup X) with hEdef
  have hcardE : Nat.card E = Nat.card A₀ := by
    rw [← hcardA₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁P).toEquiv
  have hEab : CFSG.IsElementaryAbelian 3 E := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply Subtype.ext
      show ((a : P) : X) * ((b : P) : X) = ((b : P) : X) * ((a : P) : X)
      have := hA₁.1.is_comm.comm ⟨((a : P) : X), a.2⟩ ⟨((b : P) : X), b.2⟩
      exact congrArg Subtype.val this
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact hA₁.2 _ a.2
  have hrank : CFSG.pRank 3 (P : Subgroup X) = n := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨E, hEab, by rw [hcardE, hn]⟩, ?_⟩
    rintro r ⟨F, hF, hFcard⟩
    have hF' : IsElemAbelian 3 (F.map (P : Subgroup X).subtype) := by
      refine isElemAbelian_map _ ⟨hF.toIsMulCommutative, fun x hx => ?_⟩
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
    obtain ⟨x, hx⟩ := hfuse _ hF'
    have hle := Subgroup.card_le_of_le hx
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
      Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective, hFcard, hn] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hEJ : E ≤ CFSG.elemThompson (P : Subgroup X) 3 :=
    le_sSup ⟨hEab, by rw [hcardE, hn, hrank]⟩
  have hA₁J : A₁ ≤ (CFSG.elemThompson (P : Subgroup X) 3).map (P : Subgroup X).subtype := by
    have := Subgroup.map_mono (f := (P : Subgroup X).subtype) hEJ
    rwa [hEdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA₁P] at this
  obtain ⟨x, hx⟩ := hfuse B hB
  refine ⟨h * x, le_trans ?_ hA₁J⟩
  rw [← map_conj_map_conj]
  exact Subgroup.map_mono hx

section Torus

variable {X : Type} [Group X] {V : Type} [AddCommGroup V]

theorem pow_mul_tau {σ : V →+ V} {τ : Multiplicative V →* X} {w : X}
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (n : ℕ) (v : V) :
    w ^ n * τ (.ofAdd v) = τ (.ofAdd (σ^[n] v)) * w ^ n := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    calc w ^ (n + 1) * τ (.ofAdd v) = w ^ n * (w * τ (.ofAdd v)) := by rw [pow_succ, mul_assoc]
      _ = (w ^ n * τ (.ofAdd (σ v))) * w := by rw [hwτ, mul_assoc]
      _ = τ (.ofAdd (σ^[n + 1] v)) * w ^ (n + 1) := by
        rw [ih, Function.iterate_succ_apply, mul_assoc, ← pow_succ]

@[expose] def torusExt (σ : V →+ V) (τ : Multiplicative V →* X) (w : X) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) : Subgroup X where
  carrier := {x | ∃ (v : V) (j : ℕ), x = τ (.ofAdd v) * w ^ j}
  mul_mem' := by
    rintro _ _ ⟨v, i, rfl⟩ ⟨v', j, rfl⟩
    refine ⟨v + σ^[i] v', i + j, ?_⟩
    calc τ (.ofAdd v) * w ^ i * (τ (.ofAdd v') * w ^ j)
        = τ (.ofAdd v) * (w ^ i * τ (.ofAdd v')) * w ^ j := by simp only [mul_assoc]
      _ = τ (.ofAdd (v + σ^[i] v')) * w ^ (i + j) := by
        rw [pow_mul_tau hwτ, ofAdd_add, map_mul, pow_add]
        simp only [mul_assoc]
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨v, i, rfl⟩
    refine ⟨σ^[2 * i] (-v), 2 * i, ?_⟩
    have hwi : (w ^ i)⁻¹ = w ^ (2 * i) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hw3, one_pow]
    rw [mul_inv_rev, hwi, ← map_inv, ← ofAdd_neg, pow_mul_tau hwτ]

@[expose] def torusOmega (τ : Multiplicative V →* X) : Subgroup X where
  carrier := {x | ∃ a : V, 3 • a = 0 ∧ τ (.ofAdd a) = x}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, by rw [smul_add, ha, hb, add_zero], by rw [ofAdd_add, map_mul]⟩
  one_mem' := ⟨0, smul_zero _, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, by rw [smul_neg, ha, neg_zero], by rw [ofAdd_neg, map_inv]⟩

theorem isElemAbelian_torusOmega (τ : Multiplicative V →* X) :
    IsElemAbelian 3 (torusOmega τ) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a', -, rfl⟩⟩ := a
    obtain ⟨_, ⟨b', -, rfl⟩⟩ := b
    apply Subtype.ext
    change τ (.ofAdd a') * τ (.ofAdd b') = τ (.ofAdd b') * τ (.ofAdd a')
    rw [← map_mul τ, ← map_mul τ, ← ofAdd_add, ← ofAdd_add, add_comm]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, ← ofAdd_nsmul, ha, ofAdd_zero, map_one]

variable {σ : V →+ V} {τ : Multiplicative V →* X} {w : X}

theorem iterate_three (hτ : Function.Injective τ) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (v : V) : σ^[3] v = v := by
  have h := pow_mul_tau hwτ 3 v
  rw [hw3, one_mul, mul_one] at h
  exact (Multiplicative.ofAdd.injective (hτ h)).symm

theorem iterate_eq_of_fixed {c : V} (hc : σ c = c) (n : ℕ) : σ^[n] c = c :=
  Function.iterate_fixed hc n

theorem pow_ne_tau (hτ : Function.Injective τ) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (hσ : ∃ v, σ v ≠ v) {d : ℕ}
    (hd : d = 1 ∨ d = 2) (u : V) : w ^ d ≠ τ (.ofAdd u) := by
  intro h
  have hfix : ∀ v, σ^[d] v = v := by
    intro v
    have h1 := pow_mul_tau hwτ d v
    rw [h, ← map_mul τ, ← map_mul τ] at h1
    have h2 := congrArg Multiplicative.toAdd (hτ h1)
    simp only [toAdd_mul, toAdd_ofAdd] at h2
    rw [add_comm] at h2
    exact (add_right_cancel h2).symm
  obtain ⟨v, hv⟩ := hσ
  rcases hd with rfl | rfl
  · exact hv (hfix v)
  · apply hv
    have h3 := iterate_three hτ hw3 hwτ v
    rw [Function.iterate_succ_apply', hfix] at h3
    exact h3

theorem w_mul_tau_mul (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (v : V) (y : X) :
    w * (τ (.ofAdd v) * y) = τ (.ofAdd (σ v)) * (w * y) := by
  rw [← mul_assoc, hwτ, mul_assoc]

theorem tau_mul_pow_three (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (u : V) :
    (τ (.ofAdd u) * w) ^ 3 = τ (.ofAdd (u + σ u + σ (σ u))) * w ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, w_mul_tau_mul hwτ, ofAdd_add, map_mul]

theorem fixed_of_commute (hτ : Function.Injective τ)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) {c : V} (hc : σ c = c) (u : V)
    (i : ℕ) (h : τ (.ofAdd u) * w ^ i * (τ (.ofAdd c) * w) =
      τ (.ofAdd c) * w * (τ (.ofAdd u) * w ^ i)) : σ u = u := by
  have e1 : τ (.ofAdd u) * w ^ i * (τ (.ofAdd c) * w) =
      τ (.ofAdd (u + c)) * w ^ (i + 1) := by
    calc τ (.ofAdd u) * w ^ i * (τ (.ofAdd c) * w)
        = τ (.ofAdd u) * (w ^ i * τ (.ofAdd c)) * w := by simp only [mul_assoc]
      _ = τ (.ofAdd (u + c)) * w ^ (i + 1) := by
        rw [pow_mul_tau hwτ, iterate_eq_of_fixed hc, ofAdd_add, map_mul, pow_succ]
        simp only [mul_assoc]
  have e2 : τ (.ofAdd c) * w * (τ (.ofAdd u) * w ^ i) =
      τ (.ofAdd (c + σ u)) * w ^ (i + 1) := by
    calc τ (.ofAdd c) * w * (τ (.ofAdd u) * w ^ i)
        = τ (.ofAdd c) * (w * τ (.ofAdd u)) * w ^ i := by simp only [mul_assoc]
      _ = τ (.ofAdd (c + σ u)) * w ^ (i + 1) := by
        rw [hwτ, ofAdd_add, map_mul, pow_succ']
        simp only [mul_assoc]
  rw [e1, e2, mul_left_inj] at h
  have h' := congrArg Multiplicative.toAdd (hτ h)
  simp only [toAdd_ofAdd] at h'
  rw [add_comm u c] at h'
  exact (add_left_cancel h').symm

theorem tau_mul_pow_pow_three (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) {u : V} (hu : σ u = u) (i : ℕ) :
    (τ (.ofAdd u) * w ^ i) ^ 3 = τ (.ofAdd (3 • u)) := by
  have hc : Commute (τ (.ofAdd u)) (w ^ i) := by
    have := pow_mul_tau hwτ i u
    rw [iterate_eq_of_fixed hu] at this
    exact this.symm
  rw [hc.mul_pow, ← pow_mul, mul_comm i 3, pow_mul, hw3, one_pow, mul_one, ← map_pow,
    ← ofAdd_nsmul]

theorem tau_mul_sq_sq (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w)
    (v : V) : (τ (.ofAdd v) * w ^ 2) ^ 2 = τ (.ofAdd (v + σ (σ v))) * w := by
  have h4 : w * (w * (w * w)) = w := by
    have h := hw3
    simp only [pow_succ, pow_zero, one_mul] at h
    rw [← mul_assoc, ← mul_assoc, h, one_mul]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, w_mul_tau_mul hwτ, ofAdd_add, map_mul, h4]

theorem tau_conj_tau_mul (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (s v : V) :
    τ (.ofAdd s) * (τ (.ofAdd v) * w) * (τ (.ofAdd s))⁻¹ = τ (.ofAdd (s + v - σ s)) * w := by
  rw [← map_inv τ, ← ofAdd_neg]
  simp only [mul_assoc, hwτ, map_neg, sub_eq_add_neg, ofAdd_add, map_mul]

theorem exists_conj_le_torusOmega (hτ : Function.Injective τ) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    {g : X} (hgc : ∀ c, σ c = c → 3 • c = 0 → g * τ (.ofAdd c) * g⁻¹ ∈ torusOmega τ)
    (hgw : g * w * g⁻¹ ∈ torusOmega τ) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hBP : B ≤ torusExt σ τ w hw3 hwτ) :
    ∃ y : X, B.map (MulAut.conj y).toMonoidHom ≤ torusOmega τ := by
  by_cases hT : ∃ b ∈ B, ∀ v, b ≠ τ (.ofAdd v)
  · obtain ⟨b, hbB, hbT⟩ := hT
    obtain ⟨v, j, rfl⟩ := hBP hbB
    have hwj : w ^ j = w ^ (j % 3) := pow_eq_pow_mod j hw3
    obtain ⟨v', hv'B⟩ : ∃ v', τ (.ofAdd v') * w ∈ B := by
      have hj : j % 3 = 1 ∨ j % 3 = 2 := by
        have hj0 : j % 3 ≠ 0 := by
          intro h0
          apply hbT v
          rw [hwj, h0, pow_zero, mul_one]
        omega
      rcases hj with h1 | h2
      · exact ⟨v, by rw [hwj, h1, pow_one] at hbB; exact hbB⟩
      · refine ⟨v + σ (σ v), ?_⟩
        have hsq := B.pow_mem hbB 2
        rwa [hwj, h2, tau_mul_sq_sq hw3 hwτ] at hsq
    have hx3 := hB.2 _ hv'B
    rw [tau_mul_pow_three hwτ, hw3, mul_one, ← map_one τ, ← ofAdd_zero] at hx3
    obtain ⟨s, c, hv', hc, hc3⟩ := hN v' (Multiplicative.ofAdd.injective (hτ hx3))
    have hy₀P : τ (.ofAdd s) ∈ torusExt σ τ w hw3 hwτ := ⟨s, 0, by rw [pow_zero, mul_one]⟩
    have hx' : τ (.ofAdd s) * (τ (.ofAdd v') * w) * (τ (.ofAdd s))⁻¹ = τ (.ofAdd c) * w := by
      rw [tau_conj_tau_mul hwτ]
      congr 3
      rw [hv']
      abel
    refine ⟨g * τ (.ofAdd s), fun z hz => ?_⟩
    obtain ⟨z₀, hz₀B, rfl⟩ := hz
    have hz₁P : τ (.ofAdd s) * z₀ * (τ (.ofAdd s))⁻¹ ∈ torusExt σ τ w hw3 hwτ :=
      (torusExt σ τ w hw3 hwτ).mul_mem ((torusExt σ τ w hw3 hwτ).mul_mem hy₀P (hBP hz₀B))
        ((torusExt σ τ w hw3 hwτ).inv_mem hy₀P)
    obtain ⟨u, i, hui⟩ := hz₁P
    have hcomm0 : z₀ * (τ (.ofAdd v') * w) = τ (.ofAdd v') * w * z₀ := by
      have := hB.1.is_comm.comm ⟨z₀, hz₀B⟩ ⟨_, hv'B⟩
      exact congrArg Subtype.val this
    have hcomm : ∀ r, z₀ * (τ (.ofAdd v') * (w * r)) = τ (.ofAdd v') * (w * (z₀ * r)) := by
      intro r
      calc z₀ * (τ (.ofAdd v') * (w * r)) = z₀ * (τ (.ofAdd v') * w) * r := by
            simp only [mul_assoc]
        _ = τ (.ofAdd v') * w * z₀ * r := by rw [hcomm0]
        _ = τ (.ofAdd v') * (w * (z₀ * r)) := by simp only [mul_assoc]
    have hcomm' : τ (.ofAdd u) * w ^ i * (τ (.ofAdd c) * w) =
        τ (.ofAdd c) * w * (τ (.ofAdd u) * w ^ i) := by
      rw [← hui, ← hx']
      simp only [mul_assoc, inv_mul_cancel_left, hcomm]
    have hu := fixed_of_commute hτ hwτ hc u i hcomm'
    have hz3 : (τ (.ofAdd u) * w ^ i) ^ 3 = 1 := by
      rw [← hui, conj_pow, hB.2 z₀ hz₀B, mul_one, mul_inv_cancel]
    rw [tau_mul_pow_pow_three hw3 hwτ hu, ← map_one τ, ← ofAdd_zero] at hz3
    have hu3 : 3 • u = 0 := Multiplicative.ofAdd.injective (hτ hz3)
    have hconj : (MulAut.conj (g * τ (.ofAdd s))).toMonoidHom z₀ =
        (g * τ (.ofAdd u) * g⁻¹) * (g * w * g⁻¹) ^ i := by
      rw [conj_pow, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      calc g * τ (.ofAdd s) * z₀ * ((τ (.ofAdd s))⁻¹ * g⁻¹)
          = g * (τ (.ofAdd s) * z₀ * (τ (.ofAdd s))⁻¹) * g⁻¹ := by simp only [mul_assoc]
        _ = g * τ (.ofAdd u) * g⁻¹ * (g * w ^ i * g⁻¹) := by
          rw [hui]; simp only [mul_assoc, inv_mul_cancel_left]
    rw [hconj]
    exact (torusOmega τ).mul_mem (hgc u hu hu3) ((torusOmega τ).pow_mem hgw i)
  · push Not at hT
    refine ⟨1, fun z hz => ?_⟩
    obtain ⟨z₀, hz₀B, rfl⟩ := hz
    obtain ⟨v, hv⟩ := hT z₀ hz₀B
    have h3 := hB.2 z₀ hz₀B
    rw [hv, ← map_pow, ← ofAdd_nsmul, ← map_one τ, ← ofAdd_zero] at h3
    refine ⟨v, Multiplicative.ofAdd.injective (hτ h3), ?_⟩
    rw [hv, map_one]
    rfl

theorem card_torusExt [Finite V] (hτ : Function.Injective τ) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (hσ : ∃ v, σ v ≠ v) :
    Nat.card (torusExt σ τ w hw3 hwτ) = 3 * Nat.card V := by
  let f : V × Fin 3 → torusExt σ τ w hw3 hwτ := fun p =>
    ⟨τ (.ofAdd p.1) * w ^ (p.2 : ℕ), p.1, p.2, rfl⟩
  have hne : ∀ (u : V) (d : ℕ), (d = 1 ∨ d = 2) → w ^ d ≠ τ (.ofAdd u) :=
    fun u d hd => pow_ne_tau hτ hw3 hwτ hσ hd u
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, i⟩ ⟨v', j⟩ hvw
      have h : τ (.ofAdd v) * w ^ (i : ℕ) = τ (.ofAdd v') * w ^ (j : ℕ) := congrArg Subtype.val hvw
      have key : ∀ (a b : V) (m n : ℕ), m < n → n < 3 →
          τ (.ofAdd a) * w ^ m ≠ τ (.ofAdd b) * w ^ n := by
        intro a b m n hmn hn3 hab
        apply hne (a - b) (n - m) (by omega)
        have hnm : w ^ n = w ^ (n - m) * w ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn.le]
        rw [hnm, ← mul_assoc, mul_left_inj] at hab
        rw [sub_eq_neg_add, ofAdd_add, ofAdd_neg, map_mul, map_inv, hab, inv_mul_cancel_left]
      rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
      · exact absurd h (key v v' i j hij j.2)
      · have hij' : i = j := Fin.ext hij
        subst hij'
        rw [mul_left_inj] at h
        rw [Multiplicative.ofAdd.injective (hτ h)]
      · exact absurd h.symm (key v' v j i hij i.2)
    · rintro ⟨_, v, j, rfl⟩
      refine ⟨⟨v, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩⟩, Subtype.ext ?_⟩
      change τ (.ofAdd v) * w ^ (j % 3) = τ (.ofAdd v) * w ^ j
      rw [← pow_eq_pow_mod j hw3]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_fin, mul_comm]

theorem hasFusionTarget_of_torus [Finite X] [Finite V] (hτ : Function.Injective τ)
    (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w)
    (hσ : ∃ v, σ v ≠ v) {e k : ℕ} (hV : Nat.card V = 3 ^ e)
    (hX : Nat.card X = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    (g : X) (hgc : ∀ c, σ c = c → 3 • c = 0 → g * τ (.ofAdd c) * g⁻¹ ∈ torusOmega τ)
    (hgw : g * w * g⁻¹ ∈ torusOmega τ) : HasFusionTarget X := by
  refine ⟨torusOmega τ, isElemAbelian_torusOmega τ, fun B hB => ?_⟩
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero 3)
  have hcard : Nat.card (torusExt σ τ w hw3 hwτ) = 3 ^ (Nat.card X).factorization 3 := by
    rw [card_torusExt hτ hw3 hwτ hσ, hV, hX, Nat.factorization_mul (by positivity) hk0,
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hk, add_zero, Finsupp.single_eq_same, pow_succ,
      mul_comm]
  let P₀ : Sylow 3 X := Sylow.ofCard _ hcard
  have hP₀ : (P₀ : Subgroup X) = torusExt σ τ w hw3 hwτ := rfl
  obtain ⟨Q, hQ⟩ := (isPGroup_of_isElemAbelian hB).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X P₀ Q
  have hB₁ : B.map (MulAut.conj h⁻¹).toMonoidHom ≤ torusExt σ τ w hw3 hwτ := by
    rintro _ ⟨b, hb, rfl⟩
    have hbQ := hQ hb
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP₀] at hbQ
    convert hbQ using 1
    simp
  obtain ⟨y, hy⟩ := exists_conj_le_torusOmega hτ hw3 hwτ hN hgc hgw
    (isElemAbelian_map _ hB) hB₁
  refine ⟨y * h⁻¹, ?_⟩
  rw [← map_conj_map_conj]
  exact hy

theorem hasFusionTarget_of_torus_hom {G₀ : Type} [Group G₀] [Finite X] [Finite V]
    (ι : G₀ →* X) (hι : Function.Injective ι) {τ₁ : Multiplicative V →* G₀}
    (hτ₁ : Function.Injective τ₁) {w₀ : G₀} (hw3 : w₀ ^ 3 = 1)
    (hwτ : ∀ v, w₀ * τ₁ (.ofAdd v) = τ₁ (.ofAdd (σ v)) * w₀) (hσ : ∃ v, σ v ≠ v) {e k : ℕ}
    (hV : Nat.card V = 3 ^ e) (hX : Nat.card X = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    {g₀ : G₀} (hgc : ∀ c, σ c = c → 3 • c = 0 → g₀ * τ₁ (.ofAdd c) = τ₁ (.ofAdd c) * g₀)
    {δ : V} (hδ : 3 • δ = 0) (hgw : g₀ * w₀ = τ₁ (.ofAdd δ) * g₀) : HasFusionTarget X := by
  refine hasFusionTarget_of_torus (σ := σ) (τ := ι.comp τ₁) (w := ι w₀) (hι.comp hτ₁)
    (by rw [← map_pow, hw3, map_one]) (fun v => ?_) hσ hV hX hk hN (ι g₀)
    (fun c hc hc3 => ⟨c, hc3, ?_⟩) ⟨δ, hδ, ?_⟩
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul, hwτ]
  · rw [MonoidHom.comp_apply, ← map_mul ι g₀, hgc c hc hc3, map_mul, mul_inv_cancel_right]
  · rw [MonoidHom.comp_apply, ← map_mul ι g₀ w₀, hgw, map_mul, mul_inv_cancel_right]

theorem hasFusionTarget_of_torus_sub {G₀ Y : Type} [Group G₀] [Group Y] {S : Subgroup Y}
    [Finite S] [Finite V] (ι : G₀ →* Y) (hι : Function.Injective ι)
    {τ₁ : Multiplicative V →* G₀} (hτ₁ : Function.Injective τ₁) (hτS : ∀ v, ι (τ₁ v) ∈ S)
    {w₀ : G₀} (hwS : ι w₀ ∈ S) (hw3 : w₀ ^ 3 = 1)
    (hwτ : ∀ v, w₀ * τ₁ (.ofAdd v) = τ₁ (.ofAdd (σ v)) * w₀) (hσ : ∃ v, σ v ≠ v) {e k : ℕ}
    (hV : Nat.card V = 3 ^ e) (hX : Nat.card S = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    {g₀ : G₀} (hgS : ι g₀ ∈ S)
    (hgc : ∀ c, σ c = c → 3 • c = 0 → g₀ * τ₁ (.ofAdd c) = τ₁ (.ofAdd c) * g₀)
    {δ : V} (hδ : 3 • δ = 0) (hgw : g₀ * w₀ = τ₁ (.ofAdd δ) * g₀) : HasFusionTarget S := by
  let G₁ : Subgroup G₀ := S.comap ι
  let ι₁ : G₁ →* S := (ι.comp G₁.subtype).codRestrict S (fun x => x.2)
  have hι₁ : Function.Injective ι₁ := fun x y h => Subtype.ext (hι (congrArg Subtype.val h))
  let τ₂ : Multiplicative V →* G₁ := τ₁.codRestrict G₁ hτS
  have hτ₂ : Function.Injective τ₂ := fun x y h => hτ₁ (congrArg Subtype.val h)
  refine hasFusionTarget_of_torus_hom ι₁ hι₁ (τ₁ := τ₂) hτ₂ (w₀ := ⟨w₀, hwS⟩) (Subtype.ext ?_)
    (fun v => Subtype.ext ?_) hσ hV hX hk hN (g₀ := ⟨g₀, hgS⟩) (fun c hc hc3 => Subtype.ext ?_)
    hδ (Subtype.ext ?_)
  · exact hw3
  · exact hwτ v
  · exact hgc c hc hc3
  · exact hgw

end Torus

end CFSG.RankThree.PartTwo.KFacts.KS21
