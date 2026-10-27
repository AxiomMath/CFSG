module

public import CFSG.Walter.W67.W1Basic
public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Walter.W67

namespace Prop31

variable {X : Type*} [Group X]

theorem inv_eq_self {x : X} (hx : x * x = 1) : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx

theorem conj_mul_eq_inv {a b : X} (ha : a * a = 1) (hb : b * b = 1) :
    a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
  rw [inv_eq_self ha, mul_inv_rev, inv_eq_self ha, inv_eq_self hb, ← mul_assoc, ha, one_mul]

theorem conj_mul_eq_inv' {a b : X} (ha : a * a = 1) (hb : b * b = 1) :
    b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
  rw [inv_eq_self hb, mul_inv_rev, inv_eq_self ha, inv_eq_self hb]
  calc b * (a * b) * b = b * a * (b * b) := by group
    _ = b * a := by rw [hb, mul_one]

theorem pow_conj_eq_or {w x : X} (hw : w * x * w⁻¹ = x⁻¹) (m : ℕ) :
    w ^ m * x * (w ^ m)⁻¹ = x ∨ w ^ m * x * (w ^ m)⁻¹ = x⁻¹ := by
  induction m with
  | zero => left; simp
  | succ m ih =>
    have hw' : w * x⁻¹ * w⁻¹ = x := by
      have := congrArg (·⁻¹) hw
      simpa [mul_assoc] using this
    rw [pow_succ', mul_inv_rev]
    rcases ih with h | h
    · right
      calc w * w ^ m * x * ((w ^ m)⁻¹ * w⁻¹) = w * (w ^ m * x * (w ^ m)⁻¹) * w⁻¹ := by group
        _ = x⁻¹ := by rw [h, hw]
    · left
      calc w * w ^ m * x * ((w ^ m)⁻¹ * w⁻¹) = w * (w ^ m * x * (w ^ m)⁻¹) * w⁻¹ := by group
        _ = x := by rw [h, hw']

theorem even_central {a b : X} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hk : orderOf (a * b) = 2 * k) (hk0 : 0 < k) :
    (a * b) ^ k ≠ 1 ∧ (a * b) ^ k * (a * b) ^ k = 1 ∧ a * (a * b) ^ k = (a * b) ^ k * a ∧
      b * (a * b) ^ k = (a * b) ^ k * b := by
  set w := a * b
  set K := w ^ k
  have hK2 : K * K = 1 := by rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
  have hKinv : K⁻¹ = K := inv_eq_self hK2
  have hK1 : K ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one hk0 h1
    omega
  have haK : a * K * a⁻¹ = K := by
    rw [show a * K * a⁻¹ = (a * w * a⁻¹) ^ k by rw [conj_pow], conj_mul_eq_inv ha hb, inv_pow,
      hKinv]
  have hbK : b * K * b⁻¹ = K := by
    rw [show b * K * b⁻¹ = (b * w * b⁻¹) ^ k by rw [conj_pow], conj_mul_eq_inv' ha hb, inv_pow,
      hKinv]
  refine ⟨hK1, hK2, ?_, ?_⟩
  · calc a * K = (a * K * a⁻¹) * a := by group
      _ = K * a := by rw [haK]
  · calc b * K = (b * K * b⁻¹) * b := by group
      _ = K * b := by rw [hbK]

theorem odd_conj {a b : X} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hk : orderOf (a * b) = 2 * k + 1) : (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := by
  set w := a * b
  have haw : ∀ m : ℕ, a * w ^ m * a⁻¹ = (w ^ m)⁻¹ := by
    intro m
    rw [← conj_pow, conj_mul_eq_inv ha hb, inv_pow]
  have h1 : w ^ k * a * (w ^ k)⁻¹ = w ^ (2 * k) * a := by
    have := haw k
    calc w ^ k * a * (w ^ k)⁻¹ = w ^ k * (a * (w ^ k)⁻¹ * a⁻¹) * a := by group
      _ = w ^ k * (a * w ^ k * a⁻¹)⁻¹ * a := by group
      _ = w ^ k * w ^ k * a := by rw [this, inv_inv]
      _ = w ^ (2 * k) * a := by rw [← pow_add, two_mul]
  have h2 : w ^ (2 * k) = w⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, ← hk, pow_orderOf_eq_one]
  rw [h1, h2]
  change (a * b)⁻¹ * a = b
  rw [mul_inv_rev, inv_eq_self ha, inv_eq_self hb, mul_assoc, ha, mul_one]

section Counting

variable {G₁ : Type*} [Group G₁] [Finite G₁]

@[reducible, expose] def conjOn (A : Subgroup G₁) : MulAction A G₁ where
  smul a x := a * x * (a : G₁)⁻¹
  one_smul x := by
    change ((1 : A) : G₁) * x * ((1 : A) : G₁)⁻¹ = x
    simp
  mul_smul a b x := by
    change ((a * b : A) : G₁) * x * ((a * b : A) : G₁)⁻¹ =
      (a : G₁) * ((b : G₁) * x * (b : G₁)⁻¹) * (a : G₁)⁻¹
    simp only [Subgroup.coe_mul]
    group

omit [Finite G₁] in
theorem card_conj_orbit (A : Subgroup G₁) (J : G₁) :
    Set.ncard {x : G₁ | ∃ a ∈ A, a * J * a⁻¹ = x} *
      Nat.card (A ⊓ Subgroup.centralizer ({J} : Set G₁) : Subgroup G₁) = Nat.card A := by
  let _ := conjOn A
  have horbit : MulAction.orbit A J = {x : G₁ | ∃ a ∈ A, a * J * a⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hstab : MulAction.stabilizer A J = (Subgroup.centralizer ({J} : Set G₁)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    change (a : G₁) * J * (a : G₁)⁻¹ = J ↔ _
    constructor
    · intro h
      calc (a : G₁) * J = ((a : G₁) * J * (a : G₁)⁻¹) * a := by group
        _ = J * a := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have h1 := (MulAction.stabilizer A J).card_mul_index
  rw [MulAction.index_stabilizer, horbit, hstab, ← Subgroup.inf_subgroupOf_right, inf_comm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [mul_comm]
  exact h1

theorem exists_conj_sylow (M : Subgroup G₁) (P Q : Sylow 2 G₁) (hP : (P : Subgroup G₁) ≤ M)
    (hQ : (Q : Subgroup G₁) ≤ M) :
    ∃ y ∈ M, (∀ x ∈ (P : Subgroup G₁), y * x * y⁻¹ ∈ (Q : Subgroup G₁)) ∧
      ∀ x ∈ (Q : Subgroup G₁), y⁻¹ * x * y ∈ (P : Subgroup G₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ R : Sylow 2 G₁, (R : Subgroup G₁) ≤ M → ∃ R' : Sylow 2 M,
      (R' : Subgroup M) = (R : Subgroup G₁).subgroupOf M := by
    intro R hR
    have h2 : IsPGroup 2 ((R : Subgroup G₁).subgroupOf M) :=
      R.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
    have hidx : ¬ 2 ∣ ((R : Subgroup G₁).subgroupOf M).index := fun h =>
      R.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hR))
    exact ⟨h2.toSylow hidx, h2.toSylow_coe hidx⟩
  obtain ⟨P', hP'⟩ := hsyl P hP
  obtain ⟨Q', hQ'⟩ := hsyl Q hQ
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq M P' Q'
  refine ⟨y, y.2, fun x hx => ?_, fun x hx => ?_⟩
  · have hxP : (⟨x, hP hx⟩ : M) ∈ (P' : Subgroup M) := by
      rw [hP']
      exact hx
    have : (MulAut.conj y) • (⟨x, hP hx⟩ : M) ∈ ((y • P' : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hxP
    rw [hy, hQ', Subgroup.mem_subgroupOf] at this
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · have hxQ : (⟨x, hQ hx⟩ : M) ∈ ((y • P' : Sylow 2 M) : Subgroup M) := by
      rw [hy, hQ']
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP',
      Subgroup.mem_subgroupOf] at hxQ
    simpa [MulAut.smul_def, MulAut.conj_apply, MulAut.inv_def] using hxQ

end Counting

end Prop31

open Prop31 in
theorem prop_3_1 :
    ∀ {G₁ : Type} [Group G₁] [Finite G₁] (M : Subgroup G₁), M ≠ ⊤ →
      (∀ u ∈ M, orderOf u = 2 → Subgroup.centralizer ({u} : Set G₁) ≤ M) →
      (∃ P : Sylow 2 G₁, Subgroup.normalizer ((P : Subgroup G₁) : Set G₁) ≤ M) → ∀ (S : Sylow 2 G₁),
      (S : Subgroup G₁) ≤ M → ∀ {J : G₁}, orderOf J = 2 → J ∈ (S : Subgroup G₁) →
      (∀ s ∈ (S : Subgroup G₁), s * J = J * s) →
      ∃ D : Subgroup G₁, D ≤ M ∧ Odd (Nat.card D) ∧
        ∀ x ∈ M, ∃ d ∈ D, ∃ c ∈ M ⊓ Subgroup.centralizer ({J} : Set G₁), x = d * c := by
  intro G₁ _ _ M hM hcent hnorm S hSM J hJ hJS hJZ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype G₁ := Fintype.ofFinite G₁
  set C := Subgroup.centralizer ({J} : Set G₁) with hCdef
  have hJM : J ∈ M := hSM hJS
  have hCM : C ≤ M := hcent J hJM hJ
  have hinv2 : ∀ {x : G₁}, orderOf x = 2 → x * x = 1 := fun hx => by
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hne1 : ∀ {x : G₁}, orderOf x = 2 → x ≠ 1 := fun hx h1 => by
    rw [h1, orderOf_one] at hx
    omega
  have hJJ : J * J = 1 := hinv2 hJ
  have hcent' : ∀ {u x : G₁}, u ∈ M → orderOf u = 2 → x * u = u * x → x ∈ M := by
    intro u x hu hu2 hxu
    exact hcent u hu hu2 (Subgroup.mem_centralizer_singleton_iff.mpr hxu)
  have hNS : Subgroup.normalizer ((S : Subgroup G₁) : Set G₁) ≤ M := by
    obtain ⟨P, hPM⟩ := hnorm
    have hPM' : (P : Subgroup G₁) ≤ M := Subgroup.le_normalizer.trans hPM
    obtain ⟨y, hyM, hy1, hy2⟩ := exists_conj_sylow M P S hPM' hSM
    intro n hn
    have hyny : y⁻¹ * n * y ∈ Subgroup.normalizer ((P : Subgroup G₁) : Set G₁) := by
      refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
      have h1 : n * (y * x * y⁻¹) * n⁻¹ ∈ (S : Subgroup G₁) :=
        (Subgroup.mem_normalizer_iff.mp hn _).mp (hy1 x hx)
      have := hy2 _ h1
      rwa [show y⁻¹ * (n * (y * x * y⁻¹) * n⁻¹) * y = y⁻¹ * n * y * x * (y⁻¹ * n * y)⁻¹ by
        group] at this
    have := hPM hyny
    have hn' : n = y * (y⁻¹ * n * y) * y⁻¹ := by group
    rw [hn']
    exact M.mul_mem (M.mul_mem hyM this) (M.inv_mem hyM)
  have hconjM : ∀ X : G₁, X * J * X⁻¹ ∈ M → X ∈ M := by
    intro X hX
    have hu2 : orderOf (X * J * X⁻¹) = 2 := by rw [orderOf_conj_mul, hJ]
    have hSX : ((X • S : Sylow 2 G₁) : Subgroup G₁) ≤ M := by
      intro z hz
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
      have hz' : X⁻¹ * z * X ∈ (S : Subgroup G₁) := by
        simpa [MulAut.smul_def, MulAut.conj_apply, MulAut.inv_def] using hz
      refine hcent' hX hu2 ?_
      have hc := hJZ _ hz'
      calc z * (X * J * X⁻¹) = X * ((X⁻¹ * z * X) * J) * X⁻¹ := by group
        _ = X * (J * (X⁻¹ * z * X)) * X⁻¹ := by rw [hc]
        _ = X * J * X⁻¹ * z := by group
    obtain ⟨y, hyM, hy1, -⟩ := exists_conj_sylow M (X • S) S hSX hSM
    have hyX : y * X ∈ Subgroup.normalizer ((S : Subgroup G₁) : Set G₁) := by
      refine JT.mem_normalizer_of_conj_mem fun s hs => ?_
      have hXs : X * s * X⁻¹ ∈ ((X • S : Sylow 2 G₁) : Subgroup G₁) := by
        rw [Sylow.coe_subgroup_smul]
        have := Subgroup.smul_mem_pointwise_smul s (MulAut.conj X) (S : Subgroup G₁) hs
        simpa [MulAut.smul_def, MulAut.conj_apply] using this
      have := hy1 _ hXs
      rwa [show y * (X * s * X⁻¹) * y⁻¹ = y * X * s * (y * X)⁻¹ by group] at this
    have : X = y⁻¹ * (y * X) := by group
    rw [this]
    exact M.mul_mem (M.inv_mem hyM) (hNS hyX)
  set Cl : Set G₁ := {x | ∃ a ∈ (⊤ : Subgroup G₁), a * J * a⁻¹ = x} with hCl
  set ClM : Set G₁ := {x | ∃ a ∈ M, a * J * a⁻¹ = x} with hClM
  have hcardCl := card_conj_orbit (⊤ : Subgroup G₁) J
  have hcardClM := card_conj_orbit M J
  rw [top_inf_eq, Subgroup.card_top] at hcardCl
  rw [inf_eq_right.mpr hCM] at hcardClM
  have hClM_eq : ∀ x, x ∈ Cl ∧ x ∈ M ↔ x ∈ ClM := by
    intro x
    constructor
    · rintro ⟨⟨a, -, rfl⟩, hx⟩
      exact ⟨a, hconjM a hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_top a, rfl⟩, M.mul_mem (M.mul_mem ha hJM) (M.inv_mem ha)⟩
  set Q := G₁ ⧸ M
  have : Fintype Q := Fintype.ofFinite Q
  set ClF : Finset G₁ := Cl.toFinset
  set fiber : Q → Finset G₁ := fun q => ClF.filter (fun x => (x : Q) = q)
  have hsum : ClF.card = ∑ q, (fiber q).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  set a := ClM.ncard with ha
  have hClF : ClF.card = Cl.ncard := (Set.ncard_eq_toFinset_card' Cl).symm
  have hfib1 : (fiber (1 : G₁)).card = a := by
    rw [ha, Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp only [fiber, ClF, Finset.mem_filter, Set.mem_toFinset]
    rw [← hClM_eq x]
    constructor
    · rintro ⟨hx, hx1⟩
      refine ⟨hx, ?_⟩
      have := QuotientGroup.eq.mp hx1
      simpa using this
    · rintro ⟨hx, hxM⟩
      refine ⟨hx, QuotientGroup.eq.mpr ?_⟩
      simpa using hxM
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hnQ : Nat.card Q * Nat.card M = Nat.card G₁ := by
    rw [mul_comm]
    exact M.card_mul_index
  have hClQ : Cl.ncard = Fintype.card Q * a := by
    have h1 : Cl.ncard * Nat.card C = Fintype.card Q * a * Nat.card C := by
      rw [hcardCl, mul_assoc, hcardClM, Fintype.card_eq_nat_card, hnQ]
    exact Nat.eq_of_mul_eq_mul_right hCpos h1
  have hQ2 : 2 ≤ Fintype.card Q := by
    rw [Fintype.card_eq_nat_card]
    have h1 : Nat.card Q ≠ 1 := fun h1 => hM (Subgroup.index_eq_one.mp h1)
    have h0 : Nat.card Q ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hnQ
      exact Nat.card_pos.ne' hnQ.symm
    omega
  have ha1 : 1 ≤ a := by
    rw [ha, Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Set.toFinite _)]
    intro h0
    have : J ∈ ClM := ⟨1, M.one_mem, by group⟩
    rw [h0] at this
    exact this
  obtain ⟨q₁, hq₁, hq₁a⟩ : ∃ q₁ : Q, q₁ ≠ ((1 : G₁) : Q) ∧ a ≤ (fiber q₁).card := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ q ∈ Finset.univ.erase ((1 : G₁) : Q), (fiber q).card ≤
        (Finset.univ.erase ((1 : G₁) : Q)).card • (a - 1) :=
      Finset.sum_le_card_nsmul _ _ _ fun q hq => by
        have := hcon q (Finset.ne_of_mem_erase hq)
        omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ((1 : G₁) : Q))] at hsum
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul] at hle
    rw [hClF, hClQ, hfib1] at hsum
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card Q = n + 2 := ⟨Fintype.card Q - 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [hn, hb] at hsum hle
    rw [show n + 2 - 1 = n + 1 by omega, show b + 1 - 1 = b by omega] at hle
    nlinarith
  set T := fiber q₁ with hTdef
  have hTmem : ∀ x ∈ T, x ∈ Cl ∧ (x : Q) = q₁ := by
    intro x hx
    simp only [hTdef, fiber, ClF, Finset.mem_filter, Set.mem_toFinset] at hx
    exact hx
  have hTnotM : ∀ x ∈ T, x ∉ M := by
    intro x hx hxM
    apply hq₁
    rw [← (hTmem x hx).2]
    exact QuotientGroup.eq.mpr (by simpa using hxM)
  have hT2 : ∀ x ∈ T, orderOf x = 2 := by
    intro x hx
    obtain ⟨⟨c, -, rfl⟩, -⟩ := hTmem x hx
    rw [orderOf_conj_mul, hJ]
  have hTsame : ∀ x ∈ T, ∀ y ∈ T, x⁻¹ * y ∈ M := by
    intro x hx y hy
    exact QuotientGroup.eq.mp ((hTmem x hx).2.trans (hTmem y hy).2.symm)
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨T₁, hT₁⟩ := hTne
  have hT₁inv : T₁⁻¹ = T₁ := inv_eq_self (hinv2 (hT2 T₁ hT₁))
  set D := Subgroup.closure ((fun x => T₁ * x) '' (T : Set G₁)) with hDdef
  have hgenM : ∀ x ∈ T, T₁ * x ∈ M := fun x hx => by
    have := hTsame T₁ hT₁ x hx
    rwa [hT₁inv] at this
  have hDM : D ≤ M := by
    rw [hDdef, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hgenM x hx
  have hT₁N : ∀ d ∈ D, T₁ * d * T₁⁻¹ ∈ D := by
    intro d hd
    induction hd using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      have hxinv : x⁻¹ = x := inv_eq_self (hinv2 (hT2 x hx))
      have : T₁ * (T₁ * x) * T₁⁻¹ = (T₁ * x)⁻¹ := by
        rw [mul_inv_rev, hxinv, hT₁inv, ← mul_assoc, hinv2 (hT2 T₁ hT₁), one_mul]
      rw [this]
      exact D.inv_mem (Subgroup.subset_closure ⟨x, hx, rfl⟩)
    | one => simp
    | mul y z _ _ hy hz =>
      have : T₁ * (y * z) * T₁⁻¹ = (T₁ * y * T₁⁻¹) * (T₁ * z * T₁⁻¹) := by group
      rw [this]
      exact D.mul_mem hy hz
    | inv y _ hy =>
      have : T₁ * y⁻¹ * T₁⁻¹ = (T₁ * y * T₁⁻¹)⁻¹ := by group
      rw [this]
      exact D.inv_mem hy
  have hDodd : Odd (Nat.card D) := by
    set A := Subgroup.zpowers T₁
    have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hT2 T₁ hT₁, pow_one])
    have hAN : A ≤ Subgroup.normalizer (D : Set G₁) := by
      rw [Subgroup.zpowers_le]
      exact JT.mem_normalizer_of_conj_mem hT₁N
    let := JT.conjAct A D hAN
    have hmod := hA2.card_modEq_card_fixedPoints D
    have hfix : Nat.card (MulAction.fixedPoints A D) =
        Nat.card (D ⊓ Subgroup.centralizer ({T₁} : Set G₁) : Subgroup G₁) := by
      refine Nat.card_congr
        { toFun := fun d => ⟨d.1, d.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          invFun := fun z => ⟨⟨z, z.2.1⟩, fun g => ?_⟩
          left_inv := fun d => rfl
          right_inv := fun z => rfl }
      · have := congrArg Subtype.val (d.2 ⟨T₁, Subgroup.mem_zpowers T₁⟩)
        change T₁ * (d.1 : G₁) * T₁⁻¹ = d.1 at this
        calc (d.1 : G₁) * T₁ = (T₁ * (d.1 : G₁) * T₁⁻¹) * T₁ := by rw [this]
          _ = T₁ * d.1 := by group
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
        apply Subtype.ext
        change (g : G₁) * z * (g : G₁)⁻¹ = z
        have hc : Commute T₁ (z : G₁) :=
          (Subgroup.mem_centralizer_singleton_iff.mp z.2.2).symm
        rw [← hk, (hc.zpow_left k).eq, mul_inv_cancel_right]
    rw [Nat.odd_iff]
    by_contra h2
    have h2f : 2 ∣ Nat.card (D ⊓ Subgroup.centralizer ({T₁} : Set G₁) : Subgroup G₁) := by
      rw [← hfix]
      apply Nat.dvd_of_mod_eq_zero
      have hm : Nat.card D % 2 = Nat.card (MulAction.fixedPoints A D) % 2 := hmod
      omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2f
    have hu2 : orderOf (u : G₁) = 2 := by rw [Subgroup.orderOf_coe, hu]
    exact hTnotM T₁ hT₁ (hcent' (hDM u.2.1) hu2
      (Subgroup.mem_centralizer_singleton_iff.mp u.2.2).symm)
  have hodd : ∀ x ∈ T, ∃ k : ℕ, orderOf (J * x) = 2 * k + 1 := by
    intro x hx
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd (orderOf (J * x))
    · exfalso
      have hk0 : 0 < k := by
        have hpos := orderOf_pos (J * x)
        omega
      have hk' : orderOf (J * x) = 2 * k := by omega
      obtain ⟨hK1, hK2, hJK, hxK⟩ := even_central hJJ (hinv2 (hT2 x hx)) hk' hk0
      have hK2' : orderOf ((J * x) ^ k) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hK2) hK1
      have hKM : (J * x) ^ k ∈ M := hCM (Subgroup.mem_centralizer_singleton_iff.mpr hJK.symm)
      exact hTnotM x hx (hcent' hKM hK2' hxK)
    · exact ⟨k, hk⟩
  have hdist : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ C → x = y := by
    intro x hx y hy hxy
    by_contra hne
    set X := x * y
    have hxx := hinv2 (hT2 x hx)
    have hyy := hinv2 (hT2 y hy)
    have hJX : J * X = X * J := (Subgroup.mem_centralizer_singleton_iff.mp hxy).symm
    have hxX : x * X * x⁻¹ = X⁻¹ := conj_mul_eq_inv hxx hyy
    obtain ⟨k, hk⟩ := hodd x hx
    set w := J * x
    have hwX : w * X * w⁻¹ = X⁻¹ := by
      calc w * X * w⁻¹ = J * (x * X * x⁻¹) * J⁻¹ := by simp only [w]; group
        _ = J * X⁻¹ * J⁻¹ := by rw [hxX]
        _ = X⁻¹ := by
          have : J * X⁻¹ = X⁻¹ * J := (Commute.inv_right (hJX : Commute J X)).eq
          rw [this, mul_inv_cancel_right]
    have hw'X : w⁻¹ * X * w⁻¹⁻¹ = X⁻¹ := by
      calc w⁻¹ * X * w⁻¹⁻¹ = (w⁻¹ * X⁻¹ * w)⁻¹ := by group
        _ = (w⁻¹ * (w * X * w⁻¹) * w)⁻¹ := by rw [hwX]
        _ = X⁻¹ := by group
    have hxconj : w ^ k * J * (w ^ k)⁻¹ = x := odd_conj hJJ hxx hk
    have hY := pow_conj_eq_or hw'X k
    have hJY : J * ((w⁻¹) ^ k * X * ((w⁻¹) ^ k)⁻¹) = ((w⁻¹) ^ k * X * ((w⁻¹) ^ k)⁻¹) * J := by
      rcases hY with hY | hY <;> rw [hY]
      · exact hJX
      · exact (Commute.inv_right (hJX : Commute J X)).eq
    have hxX' : x * X * x⁻¹ = X := by
      rw [← hxconj]
      have hwk : (w⁻¹) ^ k = (w ^ k)⁻¹ := inv_pow w k
      rw [hwk, inv_inv] at hJY
      calc w ^ k * J * (w ^ k)⁻¹ * X * (w ^ k * J * (w ^ k)⁻¹)⁻¹ =
          w ^ k * (J * ((w ^ k)⁻¹ * X * w ^ k)) * J⁻¹ * (w ^ k)⁻¹ := by group
        _ = w ^ k * (((w ^ k)⁻¹ * X * w ^ k) * J) * J⁻¹ * (w ^ k)⁻¹ := by rw [hJY]
        _ = X := by group
    have hX2 : X = X⁻¹ := hxX'.symm.trans hxX
    have hXM : X ∈ M := hCM hxy
    by_cases hX1 : X = 1
    · apply hne
      have : x * y = 1 := hX1
      rw [← inv_eq_self hyy]
      exact eq_inv_of_mul_eq_one_left this
    · have hXX : X * X = 1 := by
        calc X * X = X * X⁻¹ := by rw [← hX2]
          _ = 1 := mul_inv_cancel X
      have hXo : orderOf X = 2 := orderOf_eq_prime (by rw [pow_two]; exact hXX) hX1
      apply hTnotM x hx
      refine hcent' hXM hXo ?_
      calc x * X = (x * X * x⁻¹) * x := by group
        _ = X * x := by rw [hxX']
  refine ⟨D, hDM, hDodd, fun m hm => ?_⟩
  set CM := C.subgroupOf M
  have hCMcard : Nat.card CM = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv
  have hidx : Nat.card (M ⧸ CM) = a := by
    have h1 := CM.card_mul_index
    rw [hCMcard, ← hcardClM, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right hCpos h1
  let φ : {x // x ∈ T} → M ⧸ CM := fun x =>
    QuotientGroup.mk (⟨T₁ * x, hgenM x x.2⟩ : M)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 := QuotientGroup.eq.mp hxy
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (x : G₁) * y ∈ C := by
      have h3 : (((⟨T₁ * x, hgenM x x.2⟩ : M)⁻¹ * ⟨T₁ * y, hgenM y y.2⟩ : M) : G₁) =
          (x : G₁)⁻¹ * y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3, inv_eq_self (hinv2 (hT2 x x.2))] at h1
      exact h1
    exact Subtype.ext (hdist x x.2 y y.2 h2)
  have hbij : Function.Bijective φ := by
    refine hφ.bijective_of_nat_card_le ?_
    rw [hidx, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hq₁a
  obtain ⟨x, hx⟩ := hbij.2 (QuotientGroup.mk (⟨m, hm⟩ : M))
  have h1 := QuotientGroup.eq.mp hx
  rw [Subgroup.mem_subgroupOf] at h1
  refine ⟨T₁ * x, Subgroup.subset_closure ⟨x, x.2, rfl⟩, (T₁ * x)⁻¹ * m, ⟨?_, ?_⟩, by group⟩
  · exact M.mul_mem (M.inv_mem (hgenM x x.2)) hm
  · simpa using h1

end CFSG.Walter.W67
