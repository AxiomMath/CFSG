module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.SmallDimension
public import Mathlib.LinearAlgebra.Center
import CFSG.Walter.ReeOrder.JT.Section7ZA

public section

namespace CFSG.Quasithin.SteinbergCD

open Module Module.End CFSG.UnitaryInvolutionIndex

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem exists_eq_smul_one_add_smul_of_commute (hV : finrank k V = 2) {f g : End k V}
    (hf : ∀ c : k, f ≠ c • 1) (hfg : Commute g f) : ∃ a b : k, g = a • 1 + b • f := by
  have : Module.Finite k V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨v, hv⟩ : ∃ v, LinearIndependent k ![v, f v] := by
    by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
    exact hf a ha
  have hcard : Fintype.card (Fin 2) = finrank k V := by rw [Fintype.card_fin, hV]
  set b := basisOfLinearIndependentOfCardEqFinrank hv hcard with hb
  have hb0 : b 0 = v := by rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hb1 : b 1 = f v := by rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  obtain ⟨α, β, hgv⟩ : ∃ α β : k, g v = α • v + β • f v := by
    refine ⟨b.repr (g v) 0, b.repr (g v) 1, ?_⟩
    conv_lhs => rw [← b.sum_repr (g v)]
    rw [Fin.sum_univ_two, hb0, hb1]
  refine ⟨α, β, b.ext fun i => ?_⟩
  fin_cases i
  · show g (b 0) = (α • 1 + β • f) (b 0)
    rw [hb0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, one_apply, hgv]
  · show g (b 1) = (α • 1 + β • f) (b 1)
    rw [hb1, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, one_apply,
      ← mul_apply, hfg.eq, mul_apply, hgv, map_add, map_smul, map_smul]

theorem commute_of_commute_of_finrank_eq_two (hV : finrank k V = 2) {f g h : End k V}
    (hf : ∀ c : k, f ≠ c • 1) (hg : Commute g f) (hh : Commute h f) : Commute g h := by
  obtain ⟨a, b, rfl⟩ := exists_eq_smul_one_add_smul_of_commute hV hf hg
  obtain ⟨c, d, rfl⟩ := exists_eq_smul_one_add_smul_of_commute hV hf hh
  have h1 : Commute (a • (1 : End k V) + b • f) (1 : End k V) := Commute.one_right _
  have h2 : Commute (a • (1 : End k V) + b • f) f :=
    ((Commute.one_left f).smul_left a).add_left ((Commute.refl f).smul_left b)
  exact (h1.smul_right c).add_right (h2.smul_right d)

theorem exists_eq_smul_of_commute_of_sq (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2)
    {f g : End k V} (hf : ∀ c : k, f ≠ c • 1) {s : k} (hfs : f * f = s • 1)
    (hg : ∀ c : k, g ≠ c • 1) {t : k} (hgt : g * g = t • 1) (hfg : Commute g f) :
    ∃ b : k, g = b • f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_smul_one_add_smul_of_commute hV hf hfg
  have hab : a * b = 0 := by
    by_contra hab
    apply hf ((2 * a * b)⁻¹ * (t - a * a - b * b * s))
    have e : (a • (1 : End k V) + b • f) * (a • 1 + b • f) =
        (a * a + b * b * s) • 1 + (2 * a * b) • f := by
      rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
        smul_mul_smul_comm, one_mul, mul_one, one_mul, hfs, smul_smul]
      module
    rw [e] at hgt
    have h3 : (2 * a * b) • f = (t - a * a - b * b * s) • (1 : End k V) := by
      calc (2 * a * b) • f = ((a * a + b * b * s) • (1 : End k V) + (2 * a * b) • f) -
            (a * a + b * b * s) • 1 := by abel
        _ = (t - a * a - b * b * s) • (1 : End k V) := by rw [hgt]; module
    have h4 : (2 * a * b) ≠ 0 := mul_ne_zero (mul_ne_zero h2 (left_ne_zero_of_mul hab))
      (right_ne_zero_of_mul hab)
    rw [← smul_smul, ← h3, smul_smul, inv_mul_cancel₀ h4, one_smul]
  rcases mul_eq_zero.mp hab with ha | hb
  · exact ⟨b, by rw [ha, zero_smul, zero_add]⟩
  · exact absurd (by rw [hb, zero_smul, add_zero]) (hg a)

theorem commute_of_finrank_eq_one (hV : finrank k V = 1) (f g : End k V) : Commute f g := by
  obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV f
  rw [ha]
  exact (Commute.one_left g).smul_left a

theorem commute_of_commute_of_mul_eq_one {M : Type*} [Monoid M] {a b c : M} (hab : Commute a b)
    (hbc : b * c = 1) (hcb : c * b = 1) : Commute a c := by
  calc a * c = c * b * a * c := by rw [hcb, one_mul]
    _ = c * a * (b * c) := by rw [mul_assoc c b a, ← hab.eq]; simp only [mul_assoc]
    _ = c * a := by rw [hbc, mul_one]

@[expose] def scalarElements {G : Type*} [Group G] (ρ : G →* End k V) : Subgroup G where
  carrier := {g | ∃ c : k, ρ g = c • 1}
  one_mem' := ⟨1, by rw [map_one, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [map_mul, hc, hd, smul_mul_smul_comm, one_mul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    have h1 : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hc, mul_smul_comm, mul_one] at h1
    by_cases h0 : c = 0
    · rw [h0, zero_smul] at h1
      exact ⟨0, (subsingleton_of_zero_eq_one h1).elim _ _⟩
    · exact ⟨c⁻¹, by rw [← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

instance {G : Type*} [Group G] (ρ : G →* End k V) : (scalarElements ρ).Normal where
  conj_mem g := by
    rintro ⟨c, hc⟩ h
    refine ⟨c, ?_⟩
    rw [map_mul, map_mul, hc, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel,
      map_one]

theorem exists_central_involution_mod {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    {Q : Subgroup G} [Finite Q] (hQ : IsPGroup 2 Q) (hQS : ¬ Q ≤ S) :
    ∃ z ∈ Q, z ∉ S ∧ z * z ∈ S ∧ ∀ q ∈ Q, q * z * q⁻¹ * z⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := S.subgroupOf Q with hN
  have : Nontrivial (Q ⧸ N) := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    apply hQS
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ N := h ▸ Subgroup.mem_top _
    exact this
  have hQ' : IsPGroup 2 (Q ⧸ N) := hQ.to_quotient N
  have := hQ'.center_nontrivial
  have h2 : 2 ∣ Nat.card (Subgroup.center (Q ⧸ N)) := by
    obtain ⟨n, hn, hcard⟩ :=
      ((hQ'.to_subgroup (Subgroup.center (Q ⧸ N))).nontrivial_iff_card).mp inferInstance
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (x : Q ⧸ N)
  have hx2 : (x : Q ⧸ N) * x = 1 := by
    rw [← pow_two, ← hx, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  have hx1 : (x : Q ⧸ N) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  refine ⟨z, z.2, fun hzS => hx1 ?_, ?_, fun q hq => ?_⟩
  · rw [← hz]
    exact (QuotientGroup.eq_one_iff z).mpr hzS
  · have h1 : ((z * z : Q) : Q ⧸ N) = 1 := by rw [QuotientGroup.mk_mul, hz, hx2]
    have h3 := (QuotientGroup.eq_one_iff (N := N) (z * z)).mp h1
    exact h3
  · have hc := Subgroup.mem_center_iff.mp x.2 ((⟨q, hq⟩ : Q) : Q ⧸ N)
    have h1 : ((⟨q, hq⟩ * z * (⟨q, hq⟩ : Q)⁻¹ * z⁻¹ : Q) : Q ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hz, hc, mul_inv_cancel_right, mul_inv_cancel]
    have h3 := (QuotientGroup.eq_one_iff (N := N) (⟨q, hq⟩ * z * (⟨q, hq⟩ : Q)⁻¹ * z⁻¹)).mp h1
    exact h3

theorem rep_commute_of_finrank_eq_two (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2) {G : Type*}
    [Group G] (ρ : G →* End k V) {Q : Subgroup G} [Finite Q] (hQ : IsPGroup 2 Q) {u : G}
    (hu : u ∈ Subgroup.normalizer (Q : Set G)) {N : ℕ} (hN : Nat.Coprime N 6)
    (huN : u ^ N = 1) : ∀ q ∈ Q, Commute (ρ u) (ρ q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  have hN2 : Nat.Coprime N 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hN
  have hN3 : Nat.Coprime N 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hN
  set S := scalarElements ρ with hS
  have hne0 : ∀ g, ρ g ≠ 0 := by
    intro g h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (eq_zero_of_apply_eq_zero ρ g (by rw [h]; rfl))
  have hnotS : ∀ g, g ∉ S → ∀ c : k, ρ g ≠ c • 1 := fun g hg c hc => hg ⟨c, hc⟩
  by_cases hQS : Q ≤ S
  · intro q hq
    obtain ⟨c, hc⟩ := hQS hq
    rw [hc]
    exact (Commute.one_right _).smul_right c
  obtain ⟨z, hzQ, hzS, hzz, hzc⟩ := exists_central_involution_mod hQ hQS
  set Z : G → Prop := fun y => y ∈ Q ∧ y ∉ S ∧ y * y ∈ S ∧ ∀ q ∈ Q, q * y * q⁻¹ * y⁻¹ ∈ S
    with hZ
  have hZz : Z z := ⟨hzQ, hzS, hzz, hzc⟩
  set π := QuotientGroup.mk' S with hπdef
  have hπ : ∀ g, g ∈ S ↔ π g = 1 := fun g => (QuotientGroup.eq_one_iff g).symm
  have hF1 : ∀ y y', Z y → Z y' → Commute (ρ y') (ρ y) → π y = π y' := by
    rintro y y' ⟨-, hyS, hyy, -⟩ ⟨-, hy'S, hy'y', -⟩ hc
    obtain ⟨s, hs⟩ := hyy
    obtain ⟨t, ht⟩ := hy'y'
    rw [map_mul] at hs ht
    obtain ⟨b, hb⟩ := exists_eq_smul_of_commute_of_sq h2 hV (hnotS y hyS) hs (hnotS y' hy'S) ht hc
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine ⟨b, ?_⟩
    rw [map_mul, hb, mul_smul_comm, ← map_mul, inv_mul_cancel, map_one]
  have hF2 : ∀ y y', Z y → Z y' → π y ≠ π y' → ρ y' * ρ y = -(ρ y * ρ y') := by
    intro y y' hy hy' hne
    obtain ⟨c, hc⟩ := hy.2.2.2 y' hy'.1
    have h1 : ρ y' * ρ y = c • (ρ y * ρ y') := by
      have e : y' * y = (y' * y * y'⁻¹ * y⁻¹) * (y * y') := by group
      rw [← map_mul, e, map_mul, hc, smul_mul_assoc, one_mul, map_mul]
    obtain ⟨s, hs⟩ := hy.2.2.1
    rw [map_mul] at hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_smul, ← map_mul] at hs
      exact hne0 _ hs
    have hc2 : c * c = 1 := by
      have h3 : ρ y' * (ρ y * ρ y) = (c * c) • ((ρ y * ρ y) * ρ y') := by
        calc ρ y' * (ρ y * ρ y) = (ρ y' * ρ y) * ρ y := by rw [mul_assoc]
          _ = (c • (ρ y * ρ y')) * ρ y := by rw [h1]
          _ = c • (ρ y * (ρ y' * ρ y)) := by rw [smul_mul_assoc, mul_assoc]
          _ = c • (ρ y * (c • (ρ y * ρ y'))) := by rw [h1]
          _ = (c * c) • ((ρ y * ρ y) * ρ y') := by
            rw [mul_smul_comm, smul_smul, ← mul_assoc]
      rw [hs, mul_smul_comm, mul_one, smul_mul_assoc, one_mul, smul_smul] at h3
      have h4 : (s - c * c * s) • ρ y' = 0 := by rw [sub_smul, h3, sub_self]
      have h5 := (smul_eq_zero.mp h4).resolve_right (hne0 y')
      have h6 : (1 - c * c) * s = 0 := by rw [sub_mul, one_mul]; exact h5
      exact (sub_eq_zero.mp ((mul_eq_zero.mp h6).resolve_right hs0)).symm
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [one_smul] at h1
      exact hne (hF1 y y' hy hy' h1)
    have hcm : c = -1 := by
      have h7 : (c - 1) * (c + 1) = 0 := by linear_combination hc2
      rcases mul_eq_zero.mp h7 with h | h
      · exact absurd (sub_eq_zero.mp h) hc1
      · exact eq_neg_of_add_eq_zero_left h
    rw [h1, hcm, neg_one_smul]
  have hcomm : ∀ q ∈ Q, ∀ x, (∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ S) → π q * π x = π x * π q := by
    intro q hq x hx
    have h := (hπ _).mp (hx q hq)
    simp only [map_mul, map_inv] at h
    calc π q * π x = π q * π x * (π q)⁻¹ * (π x)⁻¹ * (π x * π q) := by group
      _ = π x * π q := by rw [h, one_mul]
  have hF3 : ∀ y y', Z y → Z y' → π y ≠ π y' → Z (y * y') := by
    rintro y y' ⟨hyQ, hyS, hyy, hyc⟩ ⟨hy'Q, hy'S, hy'y', hy'c⟩ hne
    have hyy' := (hπ _).mp hyy
    have hy'y'' := (hπ _).mp hy'y'
    rw [map_mul] at hyy' hy'y''
    refine ⟨mul_mem hyQ hy'Q, fun h => hne ?_, ?_, fun q hq => ?_⟩
    · have h1 := (hπ _).mp h
      rw [map_mul] at h1
      calc π y = π y * (π y * π y') := by rw [h1, mul_one]
        _ = (π y * π y) * π y' := by rw [mul_assoc]
        _ = π y' := by rw [hyy', one_mul]
    · rw [hπ]
      have hc := hcomm y' hy'Q y hyc
      rw [map_mul, map_mul]
      calc π y * π y' * (π y * π y') = π y * (π y' * π y) * π y' := by group
        _ = π y * (π y * π y') * π y' := by rw [hc]
        _ = (π y * π y) * (π y' * π y') := by group
        _ = 1 := by rw [hyy', hy'y'', one_mul]
    · rw [hπ]
      have h1 := hcomm q hq y hyc
      have h2' := hcomm q hq y' hy'c
      simp only [map_mul, map_inv]
      calc π q * (π y * π y') * (π q)⁻¹ * (π y * π y')⁻¹
          = (π q * π y) * π y' * (π q)⁻¹ * (π y * π y')⁻¹ := by group
        _ = (π y * π q) * π y' * (π q)⁻¹ * (π y * π y')⁻¹ := by rw [h1]
        _ = π y * (π q * π y') * (π q)⁻¹ * (π y * π y')⁻¹ := by group
        _ = π y * (π y' * π q) * (π q)⁻¹ * (π y * π y')⁻¹ := by rw [h2']
        _ = 1 := by group
  have hF4 : ∀ y₀ y₁ y₂, Z y₀ → Z y₁ → Z y₂ → π y₀ ≠ π y₁ → π y₀ ≠ π y₂ → π y₁ ≠ π y₂ →
      π (y₁ * y₂) = π y₀ := by
    intro y₀ y₁ y₂ h₀ h₁ h₂ h01 h02 h12
    have a1 := hF2 y₀ y₁ h₀ h₁ h01
    have a2 := hF2 y₀ y₂ h₀ h₂ h02
    have hc : Commute (ρ (y₁ * y₂)) (ρ y₀) := by
      show ρ (y₁ * y₂) * ρ y₀ = ρ y₀ * ρ (y₁ * y₂)
      rw [map_mul]
      calc ρ y₁ * ρ y₂ * ρ y₀ = ρ y₁ * (ρ y₂ * ρ y₀) := by rw [mul_assoc]
        _ = -(ρ y₁ * (ρ y₀ * ρ y₂)) := by rw [a2, mul_neg]
        _ = -((ρ y₁ * ρ y₀) * ρ y₂) := by rw [mul_assoc]
        _ = ρ y₀ * (ρ y₁ * ρ y₂) := by rw [a1, neg_mul, neg_neg, mul_assoc]
    exact (hF1 y₀ (y₁ * y₂) h₀ (hF3 y₁ y₂ h₁ h₂ h12) hc).symm
  have hconjZ : ∀ y, Z y → Z (u * y * u⁻¹) := by
    rintro y ⟨hyQ, hyS, hyy, hyc⟩
    have huQ : ∀ g, g ∈ Q ↔ u * g * u⁻¹ ∈ Q := fun g => Subgroup.mem_normalizer_iff.mp hu g
    have hSn : ∀ g, g ∈ S → u * g * u⁻¹ ∈ S := fun g hg =>
      (inferInstance : S.Normal).conj_mem g hg u
    refine ⟨(huQ y).mp hyQ, fun h => hyS ?_, ?_, fun q hq => ?_⟩
    · have h1 := (inferInstance : S.Normal).conj_mem _ h u⁻¹
      have e : u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y := by group
      rwa [e] at h1
    · have e : u * y * u⁻¹ * (u * y * u⁻¹) = u * (y * y) * u⁻¹ := by group
      rw [e]
      exact hSn _ hyy
    · have hq' : u⁻¹ * q * u ∈ Q := by
        refine (huQ _).mpr ?_
        have e : u * (u⁻¹ * q * u) * u⁻¹ = q := by group
        rw [e]
        exact hq
      have e : q * (u * y * u⁻¹) * q⁻¹ * (u * y * u⁻¹)⁻¹ =
          u * ((u⁻¹ * q * u) * y * (u⁻¹ * q * u)⁻¹ * y⁻¹) * u⁻¹ := by group
      rw [e]
      exact hSn _ (hyc _ hq')
  set w : ℕ → G := fun i => u ^ i * z * (u ^ i)⁻¹ with hw
  have hwZ : ∀ i, Z (w i) := by
    intro i
    induction i with
    | zero => simpa [hw] using hZz
    | succ i ih =>
      have e : w (i + 1) = u * w i * u⁻¹ := by
        simp only [hw, pow_succ']
        group
      rw [e]
      exact hconjZ _ ih
  have hπw : ∀ i j, i ≤ j → π (w i) = π (w j) → π z = π (w (j - i)) := by
    intro i j hij h
    have e1 : w j = u ^ i * w (j - i) * (u ^ i)⁻¹ := by
      simp only [hw]
      have hj : j = i + (j - i) := by omega
      conv_lhs => rw [hj, pow_add]
      group
    have e0 : w i = u ^ i * z * (u ^ i)⁻¹ := rfl
    rw [e0, e1] at h
    simp only [map_mul, map_inv] at h
    exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨d, hd1, hd3, hd⟩ : ∃ d, 1 ≤ d ∧ d ≤ 3 ∧ π z = π (w d) := by
    by_contra hcon
    push Not at hcon
    have hne : ∀ i j, i < j → j ≤ 3 → π (w i) ≠ π (w j) := fun i j hij hj h =>
      hcon (j - i) (by omega) (by omega) (hπw i j hij.le h)
    have h1 := hF4 (w 0) (w 1) (w 2) (hwZ 0) (hwZ 1) (hwZ 2) (hne 0 1 (by omega) (by omega))
      (hne 0 2 (by omega) (by omega)) (hne 1 2 (by omega) (by omega))
    have h2' := hF4 (w 0) (w 1) (w 3) (hwZ 0) (hwZ 1) (hwZ 3) (hne 0 1 (by omega) (by omega))
      (hne 0 3 (by omega) (by omega)) (hne 1 3 (by omega) (by omega))
    rw [map_mul] at h1 h2'
    exact hne 2 3 (by omega) le_rfl (mul_left_cancel (h1.trans h2'.symm))
  set T := (Subgroup.centralizer {π z}).comap π with hT
  have hmemT : ∀ g, g ∈ T ↔ π (g * z * g⁻¹) = π z := by
    intro g
    rw [hT, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul,
      map_inv, mul_inv_eq_iff_eq_mul]
  have huT : u ∈ T := by
    have hd' : u ^ d ∈ T := by
      rw [hmemT]
      exact hd.symm
    have hN' : u ^ N ∈ T := by
      rw [huN]
      exact one_mem _
    have hcop : Nat.Coprime d N := by
      interval_cases d
      · exact Nat.coprime_one_left N
      · exact hN2.symm
      · exact hN3.symm
    exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime hd' hN' hcop
  have huz : Commute (ρ u) (ρ z) := by
    have h1 := (hmemT u).mp huT
    have hδS : z⁻¹ * (u * z * u⁻¹) ∈ S := by
      have h1' := h1.symm
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1'
      exact h1'
    obtain ⟨c, hc⟩ := hδS
    have hδQ : z⁻¹ * (u * z * u⁻¹) ∈ Q :=
      mul_mem (inv_mem hzQ) ((Subgroup.mem_normalizer_iff.mp hu z).mp hzQ)
    have h2' : ρ (u * z * u⁻¹) = c • ρ z := by
      have e : u * z * u⁻¹ = z * (z⁻¹ * (u * z * u⁻¹)) := by group
      rw [e, map_mul, hc, mul_smul_comm, mul_one]
    have h3 : ∀ n : ℕ, ρ (u ^ n * z * (u ^ n)⁻¹) = c ^ n • ρ z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : u ^ (n + 1) * z * (u ^ (n + 1))⁻¹ = u * (u ^ n * z * (u ^ n)⁻¹) * u⁻¹ := by
          rw [pow_succ']
          group
        rw [e, map_mul, map_mul, ih, mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, h2',
          smul_smul, ← pow_succ]
    have hcN : c ^ N = 1 := by
      have h4 := h3 N
      rw [huN, inv_one, one_mul, mul_one] at h4
      have h5 : (c ^ N - 1) • ρ z = 0 := by rw [sub_smul, ← h4, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right (hne0 z))
    obtain ⟨m, hm⟩ := hQ ⟨_, hδQ⟩
    have hc2 : c ^ 2 ^ m = 1 := by
      have h5 : ρ ((z⁻¹ * (u * z * u⁻¹)) ^ 2 ^ m) = 1 := by
        have h6 : (z⁻¹ * (u * z * u⁻¹)) ^ 2 ^ m = 1 := congrArg Subtype.val hm
        rw [h6, map_one]
      rw [map_pow, hc, smul_pow, one_pow] at h5
      by_contra hne
      have h6 : (c ^ 2 ^ m - 1) • (1 : End k V) = 0 := by rw [sub_smul, h5, one_smul, sub_self]
      rcases smul_eq_zero.mp h6 with h7 | h7
      · exact hne (sub_eq_zero.mp h7)
      · exact one_ne_zero h7
    have hc1 : c = 1 := by
      have hdvd1 : orderOf c ∣ N := orderOf_dvd_of_pow_eq_one hcN
      have hdvd2 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hc2
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right m hN2) hdvd1 hdvd2)
    rw [hc1, one_smul] at h2'
    show ρ u * ρ z = ρ z * ρ u
    calc ρ u * ρ z = ρ (u * z * u⁻¹) * ρ u := by
          rw [← map_mul, ← map_mul, inv_mul_cancel_right]
      _ = ρ z * ρ u := by rw [h2']
  intro q hq
  have hzns := hnotS z hzS
  by_cases hqz : Commute (ρ q) (ρ z)
  · exact commute_of_commute_of_finrank_eq_two hV hzns huz hqz
  obtain ⟨c', hc'⟩ := hzc q hq
  have h1 : ρ (q * z * q⁻¹) = c' • ρ z := by
    have e : q * z * q⁻¹ = (q * z * q⁻¹ * z⁻¹) * z := by group
    rw [e, map_mul, hc', smul_mul_assoc, one_mul]
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h1
    exact hne0 _ h1
  have hvz : Commute (ρ (q * u * q⁻¹)) (ρ z) := by
    have h2' : ρ (q * u * q⁻¹) * ρ (q * z * q⁻¹) = ρ (q * z * q⁻¹) * ρ (q * u * q⁻¹) := by
      rw [← map_mul, ← map_mul]
      have e1 : q * u * q⁻¹ * (q * z * q⁻¹) = q * (u * z) * q⁻¹ := by group
      have e2 : q * z * q⁻¹ * (q * u * q⁻¹) = q * (z * u) * q⁻¹ := by group
      rw [e1, e2]
      simp only [map_mul]
      rw [huz.eq]
    rw [h1, mul_smul_comm, smul_mul_assoc] at h2'
    exact smul_right_injective (End k V) hc'0 h2'
  have huv : Commute (ρ u) (ρ (q * u * q⁻¹)) :=
    commute_of_commute_of_finrank_eq_two hV hzns huz hvz
  have hwQ : u * (q * u * q⁻¹)⁻¹ ∈ Q := by
    have e : u * (q * u * q⁻¹)⁻¹ = (u * q * u⁻¹) * q⁻¹ := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hu q).mp hq) (inv_mem hq)
  have hker : u * (q * u * q⁻¹)⁻¹ ∈ ρ.ker := by
    have hinv : Commute (ρ u) (ρ (q * u * q⁻¹)⁻¹) :=
      commute_of_commute_of_mul_eq_one huv (by rw [← map_mul, mul_inv_cancel, map_one])
        (by rw [← map_mul, inv_mul_cancel, map_one])
    have hN1 : (u * (q * u * q⁻¹)⁻¹) ^ N ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul, hinv.mul_pow, ← map_pow, ← map_pow, huN,
        map_one, one_mul, inv_pow, conj_pow, huN, mul_one, mul_inv_cancel, inv_one, map_one]
    obtain ⟨m, hm⟩ := hQ ⟨_, hwQ⟩
    have hm1 : (u * (q * u * q⁻¹)⁻¹) ^ 2 ^ m ∈ ρ.ker := by
      have h6 : (u * (q * u * q⁻¹)⁻¹) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      rw [h6]
      exact one_mem _
    exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime hN1 hm1 (Nat.Coprime.pow_right m hN2)
  rw [MonoidHom.mem_ker, map_mul] at hker
  have h3 : ρ u = ρ (q * u * q⁻¹) := by
    calc ρ u = ρ u * ρ (q * u * q⁻¹)⁻¹ * ρ (q * u * q⁻¹) := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      _ = ρ (q * u * q⁻¹) := by rw [hker, one_mul]
  show ρ u * ρ q = ρ q * ρ u
  calc ρ u * ρ q = ρ (q * u * q⁻¹) * ρ q := by rw [← h3]
    _ = ρ q * ρ u := by rw [← map_mul, ← map_mul, inv_mul_cancel_right]

theorem rep_commute_of_finrank_le_two [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    (hV : finrank k V ≤ 2) {G : Type*} [Group G] (ρ : G →* End k V) {Q : Subgroup G} [Finite Q]
    (hQ : IsPGroup 2 Q) {u : G} (hu : u ∈ Subgroup.normalizer (Q : Set G)) {N : ℕ}
    (hN : Nat.Coprime N 6) (huN : u ^ N = 1) : ∀ q ∈ Q, Commute (ρ u) (ρ q) := by
  intro q hq
  rcases (by omega : finrank k V = 0 ∨ finrank k V = 1 ∨ finrank k V = 2) with h | h | h
  · have : Subsingleton V := Module.finrank_zero_iff.mp h
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  · exact commute_of_finrank_eq_one h _ _
  · exact rep_commute_of_finrank_eq_two h2 h ρ hQ hu hN huN q hq

theorem isCompl_ker_sub_one_ker_add_one_of_mul_self (h2 : (2 : k) ≠ 0) {x : End k V}
    (hx : x * x = 1) : IsCompl (LinearMap.ker (x - 1)) (LinearMap.ker (x + 1)) := by
  have hxx : ∀ v, x (x v) = v := fun v => by rw [← mul_apply, hx, one_apply]
  refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_,
    Submodule.codisjoint_iff_exists_add_eq.mpr fun v => ?_⟩
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, one_apply, sub_eq_zero] at hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, one_apply, hv] at hv'
    have h3 : (2 : k) • v = 0 := by rw [two_smul]; exact hv'
    exact (smul_eq_zero.mp h3).resolve_left h2
  · refine ⟨(2 : k)⁻¹ • (v + x v), (2 : k)⁻¹ • (v - x v), ?_, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, one_apply, map_smul, map_add, hxx,
        add_comm (x v), sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, one_apply, map_smul, map_sub, hxx,
        ← smul_add, sub_add_sub_cancel', sub_self, smul_zero]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul k v, smul_smul, inv_mul_cancel₀ h2,
        one_smul]

theorem det_eq_neg_one_pow_of_mul_self [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    {x : End k V} (hx : x * x = 1) :
    LinearMap.det x = (-1) ^ finrank k (LinearMap.ker (x + 1)) := by
  have hc := isCompl_ker_sub_one_ker_add_one_of_mul_self h2 hx
  set A := LinearMap.ker (x - 1) with hA
  set B := LinearMap.ker (x + 1) with hB
  set e := Submodule.prodEquivOfIsCompl A B hc with he
  have hxe : x = (e : (A × B) →ₗ[k] V) ∘ₗ (LinearMap.prodMap LinearMap.id (-LinearMap.id)) ∘ₗ
      (e.symm : V →ₗ[k] (A × B)) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    have ha : x a = a := by
      have h3 : (a : V) ∈ LinearMap.ker (x - 1) := a.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, one_apply, sub_eq_zero] at h3
      exact h3
    have hb : x b = -b := by
      have h3 : (b : V) ∈ LinearMap.ker (x + 1) := b.2
      rw [LinearMap.mem_ker, LinearMap.add_apply, one_apply] at h3
      exact eq_neg_of_add_eq_zero_left h3
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.neg_apply]
    rw [he, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl']
    simp only [map_add, ha, hb, Submodule.coe_neg]
  have hneg : (-LinearMap.id : B →ₗ[k] B) = (-1 : k) • LinearMap.id := by
    ext v
    simp
  rw [hxe, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hneg,
    LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem finrank_ker_of_mul_self_of_det (h2 : (2 : k) ≠ 0) (hV : finrank k V = 3)
    {x : End k V} (hx : x * x = 1) (hdet : LinearMap.det x = 1) (hx1 : x ≠ 1) :
    finrank k (LinearMap.ker (x - 1)) = 1 ∧ finrank k (LinearMap.ker (x + 1)) = 2 := by
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  have hc := isCompl_ker_sub_one_ker_add_one_of_mul_self h2 hx
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hpow := det_eq_neg_one_pow_of_mul_self h2 hx
  rw [hdet] at hpow
  have hne : (-1 : k) ≠ 1 := by
    intro h
    apply h2
    calc (2 : k) = 1 + 1 := by norm_num
      _ = 1 + -1 := by rw [h]
      _ = 0 := by ring
  have heven : Even (finrank k (LinearMap.ker (x + 1))) :=
    (neg_one_pow_eq_one_iff_even hne).mp hpow.symm
  have hpos : finrank k (LinearMap.ker (x + 1)) ≠ 0 := by
    intro h0
    apply hx1
    have hbot : LinearMap.ker (x + 1) = ⊥ := Submodule.finrank_eq_zero.mp h0
    have htop : LinearMap.ker (x - 1) = ⊤ := by
      have h3 := codisjoint_iff.mp hc.codisjoint
      rwa [hbot, sup_bot_eq] at h3
    refine LinearMap.ext fun v => ?_
    have h3 : v ∈ LinearMap.ker (x - 1) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, one_apply, sub_eq_zero] at h3
    rw [h3, one_apply]
  obtain ⟨t, ht⟩ := heven
  omega

theorem eq_mul_of_commute_of_mul_self_of_det (h2 : (2 : k) ≠ 0) (hV : finrank k V = 3)
    {a b c : End k V} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hda : LinearMap.det a = 1) (hdb : LinearMap.det b = 1) (hdc : LinearMap.det c = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hc1 : c ≠ 1) (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c) : c = a * b := by
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  set L := LinearMap.ker (a - 1) with hL
  set W := LinearMap.ker (a + 1) with hW
  have hLW := isCompl_ker_sub_one_ker_add_one_of_mul_self h2 ha
  have hdimL := (finrank_ker_of_mul_self_of_det h2 hV ha hda ha1).1
  have hmemL : ∀ v, v ∈ L ↔ a v = v := fun v => by
    rw [hL, LinearMap.mem_ker, LinearMap.sub_apply, one_apply, sub_eq_zero]
  have hmemW : ∀ v, v ∈ W ↔ a v = -v := fun v => by
    rw [hW, LinearMap.mem_ker, LinearMap.add_apply, one_apply, add_eq_zero_iff_eq_neg]
  have hmemfix : ∀ (x : End k V) v, v ∈ LinearMap.ker (x - 1) ↔ x v = v := fun x v => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, one_apply, sub_eq_zero]
  have hpresL : ∀ x : End k V, Commute a x → ∀ v ∈ L, x v ∈ L := by
    intro x hx v hv
    rw [hmemL] at hv ⊢
    rw [← mul_apply, hx.eq, mul_apply, hv]
  have hpresW : ∀ x : End k V, Commute a x → ∀ v ∈ W, x v ∈ W := by
    intro x hx v hv
    rw [hmemW] at hv ⊢
    rw [← mul_apply, hx.eq, mul_apply, hv, map_neg]
  have hxx : ∀ x : End k V, x * x = 1 → ∀ v, x (x v) = v := fun x hx v => by
    rw [← mul_apply, hx, one_apply]
  have hS1 : ∀ x : End k V, x * x = 1 → LinearMap.det x = 1 → x ≠ 1 → Commute a x →
      (∀ v ∈ L, x v = v) → x = a := by
    intro x hx hdx hx1 hax hxL
    have hdimx := (finrank_ker_of_mul_self_of_det h2 hV hx hdx hx1).1
    have hLx : L ≤ LinearMap.ker (x - 1) := fun v hv => (hmemfix x v).mpr (hxL v hv)
    have hLeq : L = LinearMap.ker (x - 1) :=
      Submodule.eq_of_le_of_finrank_eq hLx (by rw [hdimL, hdimx])
    have hxW : ∀ w ∈ W, x w = -w := by
      intro w hw
      have h1 : w + x w ∈ LinearMap.ker (x - 1) := by
        rw [hmemfix, map_add, hxx x hx, add_comm]
      have h3 : w + x w ∈ W := W.add_mem hw (hpresW x hax w hw)
      rw [← hLeq] at h1
      have h4 : w + x w = 0 := (Submodule.disjoint_def.mp hLW.disjoint) _ h1 h3
      exact eq_neg_of_add_eq_zero_right h4
    refine LinearMap.ext fun v => ?_
    obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (codisjoint_iff.mp hLW.codisjoint ▸ Submodule.mem_top : v ∈ L ⊔ W)
    rw [map_add, map_add, hxL l hl, hxW w hw, (hmemL l).mp hl, (hmemW w).mp hw]
  have hS2 : ∀ x : End k V, x * x = 1 → LinearMap.det x = 1 → x ≠ 1 → Commute a x → x ≠ a →
      ∀ v ∈ L, x v = -v := by
    intro x hx hdx hx1 hax hxa v hv
    have hdisj : L ⊓ LinearMap.ker (x - 1) = ⊥ := by
      by_contra hne
      have hle : L ⊓ LinearMap.ker (x - 1) ≤ L := inf_le_left
      have hpos : finrank k ↥(L ⊓ LinearMap.ker (x - 1)) ≠ 0 :=
        (Submodule.finrank_eq_zero.not).mpr hne
      have heq : L ⊓ LinearMap.ker (x - 1) = L :=
        Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle)
          (by rw [hdimL]; omega))
      apply hxa
      refine hS1 x hx hdx hx1 hax fun w hw => ?_
      have hw' : w ∈ L ⊓ LinearMap.ker (x - 1) := by rw [heq]; exact hw
      exact (hmemfix x w).mp (Submodule.mem_inf.mp hw').2
    have h1 : v + x v ∈ L ⊓ LinearMap.ker (x - 1) := by
      refine Submodule.mem_inf.mpr ⟨L.add_mem hv (hpresL x hax v hv), ?_⟩
      rw [hmemfix, map_add, hxx x hx, add_comm]
    rw [hdisj, Submodule.mem_bot] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hbL := hS2 b hb hdb hb1 hab hab'.symm
  have hcL := hS2 c hc hdc hc1 hac hac'.symm
  have hbc1 : b * c ≠ 1 := by
    intro h
    apply hbc'
    calc b = b * (b * c) := by rw [h, mul_one]
      _ = c := by rw [← mul_assoc, hb, one_mul]
  have hbcbc : b * c * (b * c) = 1 := by
    calc b * c * (b * c) = b * (c * b) * c := by simp only [mul_assoc]
      _ = b * (b * c) * c := by rw [hbc.eq]
      _ = 1 := by rw [← mul_assoc, hb, one_mul, hc]
  have hdbc : LinearMap.det (b * c) = 1 := by rw [map_mul, hdb, hdc, one_mul]
  have habc : Commute a (b * c) := hab.mul_right hac
  have hbcL : ∀ v ∈ L, (b * c) v = v := by
    intro v hv
    rw [mul_apply, hcL v hv, map_neg, hbL v hv, neg_neg]
  have h := hS1 (b * c) hbcbc hdbc hbc1 habc hbcL
  calc c = b * (b * c) := by rw [← mul_assoc, hb, one_mul]
    _ = b * a := by rw [h]
    _ = a * b := hab.eq.symm

theorem rep_commute_of_finrank_eq_three_of_det (h2 : (2 : k) ≠ 0) (hV : finrank k V = 3)
    {G : Type*} [Group G] (ρ : G →* End k V) {Q : Subgroup G} [Finite Q] (hQ : IsPGroup 2 Q)
    (hdet : ∀ q ∈ Q, LinearMap.det (ρ q) = 1) {u : G}
    (hu : u ∈ Subgroup.normalizer (Q : Set G)) {N : ℕ} (hN : Nat.Coprime N 6)
    (huN : u ^ N = 1) : ∀ q ∈ Q, Commute (ρ u) (ρ q) := by
  classical
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  have hN2 : Nat.Coprime N 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hN
  have hN3 : Nat.Coprime N 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hN
  set K := ρ.ker with hK
  by_cases hQK : Q ≤ K
  · intro q hq
    rw [MonoidHom.mem_ker.mp (hQK hq)]
    exact Commute.one_right _
  obtain ⟨z, hzQ, hzK, hzz, hzc⟩ := exists_central_involution_mod hQ hQK
  set π := QuotientGroup.mk' K with hπdef
  have hπρ : ∀ y y', π y = π y' ↔ ρ y = ρ y' := by
    intro y y'
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      MonoidHom.mem_ker, map_mul]
    constructor
    · intro h
      calc ρ y = ρ y * (ρ y⁻¹ * ρ y') := by rw [h, mul_one]
        _ = ρ y' := by rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    · intro h
      rw [← h, ← map_mul, inv_mul_cancel, map_one]
  set A : G → Prop := fun y => y ∈ Q ∧ y ∉ K ∧ y * y ∈ K ∧ ∀ q ∈ Q, q * y * q⁻¹ * y⁻¹ ∈ K
    with hA
  have hAz : A z := ⟨hzQ, hzK, hzz, hzc⟩
  have hAinv : ∀ y, A y → ρ y * ρ y = 1 := fun y hy => by
    rw [← map_mul]
    exact MonoidHom.mem_ker.mp hy.2.2.1
  have hAne1 : ∀ y, A y → ρ y ≠ 1 := fun y hy h => hy.2.1 (MonoidHom.mem_ker.mpr h)
  have hAcomm : ∀ y y', A y → A y' → Commute (ρ y) (ρ y') := by
    intro y y' hy hy'
    have h1 := MonoidHom.mem_ker.mp (hy.2.2.2 y' hy'.1)
    have e : y' * y = (y' * y * y'⁻¹ * y⁻¹) * (y * y') := by group
    have h3 : ρ (y' * y) = ρ (y * y') := by rw [e, map_mul, h1, one_mul]
    rw [map_mul, map_mul] at h3
    exact h3.symm
  have hconjA : ∀ y, A y → A (u * y * u⁻¹) := by
    rintro y ⟨hyQ, hyK, hyy, hyc⟩
    have huQ : ∀ g, g ∈ Q ↔ u * g * u⁻¹ ∈ Q := fun g => Subgroup.mem_normalizer_iff.mp hu g
    have hKn : ∀ g, g ∈ K → u * g * u⁻¹ ∈ K := fun g hg =>
      (inferInstance : K.Normal).conj_mem g hg u
    refine ⟨(huQ y).mp hyQ, fun h => hyK ?_, ?_, fun q hq => ?_⟩
    · have h1 := (inferInstance : K.Normal).conj_mem _ h u⁻¹
      have e : u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y := by group
      rwa [e] at h1
    · have e : u * y * u⁻¹ * (u * y * u⁻¹) = u * (y * y) * u⁻¹ := by group
      rw [e]
      exact hKn _ hyy
    · have hq' : u⁻¹ * q * u ∈ Q := by
        refine (huQ _).mpr ?_
        have e : u * (u⁻¹ * q * u) * u⁻¹ = q := by group
        rw [e]
        exact hq
      have e : q * (u * y * u⁻¹) * q⁻¹ * (u * y * u⁻¹)⁻¹ =
          u * ((u⁻¹ * q * u) * y * (u⁻¹ * q * u)⁻¹ * y⁻¹) * u⁻¹ := by group
      rw [e]
      exact hKn _ (hyc _ hq')
  set w : ℕ → G := fun i => u ^ i * z * (u ^ i)⁻¹ with hw
  have hwA : ∀ i, A (w i) := by
    intro i
    induction i with
    | zero => simpa [hw] using hAz
    | succ i ih =>
      have e : w (i + 1) = u * w i * u⁻¹ := by
        simp only [hw, pow_succ']
        group
      rw [e]
      exact hconjA _ ih
  have hπw : ∀ i j, i ≤ j → π (w i) = π (w j) → π z = π (w (j - i)) := by
    intro i j hij h
    have e1 : w j = u ^ i * w (j - i) * (u ^ i)⁻¹ := by
      simp only [hw]
      have hj : j = i + (j - i) := by omega
      conv_lhs => rw [hj, pow_add]
      group
    have e0 : w i = u ^ i * z * (u ^ i)⁻¹ := rfl
    rw [e0, e1] at h
    simp only [map_mul, map_inv] at h
    exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨d, hd1, hd3, hd⟩ : ∃ d, 1 ≤ d ∧ d ≤ 3 ∧ π z = π (w d) := by
    by_contra hcon
    push Not at hcon
    have hne : ∀ i j, i < j → j ≤ 3 → ρ (w i) ≠ ρ (w j) := fun i j hij hj h =>
      hcon (j - i) (by omega) (by omega) (hπw i j hij.le ((hπρ _ _).mpr h))
    have hthree : ∀ j, 2 ≤ j → j ≤ 3 → ρ (w j) = ρ (w 0) * ρ (w 1) := fun j hj2 hj3 =>
      eq_mul_of_commute_of_mul_self_of_det h2 hV (hAinv _ (hwA 0)) (hAinv _ (hwA 1))
        (hAinv _ (hwA j)) (hdet _ (hwA 0).1) (hdet _ (hwA 1).1) (hdet _ (hwA j).1)
        (hAcomm _ _ (hwA 0) (hwA 1)) (hAcomm _ _ (hwA 0) (hwA j)) (hAcomm _ _ (hwA 1) (hwA j))
        (hAne1 _ (hwA 0)) (hAne1 _ (hwA 1)) (hAne1 _ (hwA j)) (hne 0 1 (by omega) (by omega))
        (hne 0 j (by omega) hj3) (hne 1 j (by omega) hj3)
    exact hne 2 3 (by omega) le_rfl ((hthree 2 le_rfl (by omega)).trans
      (hthree 3 (by omega) le_rfl).symm)
  set T := (Subgroup.centralizer {π z}).comap π with hT
  have hmemT : ∀ g, g ∈ T ↔ π (g * z * g⁻¹) = π z := by
    intro g
    rw [hT, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul,
      map_inv, mul_inv_eq_iff_eq_mul]
  have huT : u ∈ T := by
    have hd' : u ^ d ∈ T := by
      rw [hmemT]
      exact hd.symm
    have hN' : u ^ N ∈ T := by
      rw [huN]
      exact one_mem _
    have hcop : Nat.Coprime d N := by
      interval_cases d
      · exact Nat.coprime_one_left N
      · exact hN2.symm
      · exact hN3.symm
    exact CFSG.Walter.JT.mem_of_pow_mem_of_coprime hd' hN' hcop
  have huz : Commute (ρ u) (ρ z) := by
    have h1 := (hπρ _ _).mp ((hmemT u).mp huT)
    show ρ u * ρ z = ρ z * ρ u
    calc ρ u * ρ z = ρ (u * z * u⁻¹) * ρ u := by
          rw [← map_mul, ← map_mul, inv_mul_cancel_right]
      _ = ρ z * ρ u := by rw [h1]
  have hdims := finrank_ker_of_mul_self_of_det h2 hV (hAinv z hAz) (hdet z hzQ) (hAne1 z hAz)
  have hcompl := isCompl_ker_sub_one_ker_add_one_of_mul_self h2 (hAinv z hAz)
  set H := (Subgroup.centralizer {ρ.toHomUnits z}).comap ρ.toHomUnits with hH
  have hmemH : ∀ g, g ∈ H ↔ Commute (ρ g) (ρ z) := by
    intro g
    rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Units.ext_iff,
      Units.val_mul, Units.val_mul, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits]
    rfl
  have hQz : ∀ q ∈ Q, Commute (ρ q) (ρ z) := by
    intro q hq
    have h1 := MonoidHom.mem_ker.mp (hzc q hq)
    have e : q * z = (q * z * q⁻¹ * z⁻¹) * (z * q) := by group
    have h3 : ρ (q * z) = ρ (z * q) := by rw [e, map_mul, h1, one_mul]
    rw [map_mul, map_mul] at h3
    exact h3
  have hQH : Q ≤ H := fun q hq => (hmemH q).mpr (hQz q hq)
  have huH : u ∈ H := (hmemH u).mpr huz
  set Q' := Q.subgroupOf H with hQ'
  have : Finite Q' :=
    Finite.of_injective (fun x : Q' => (⟨(x : H), x.2⟩ : Q)) fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun t : Q => (t : G)) hxy))
  have hQ'2 : IsPGroup 2 Q' := hQ.comap_subtype
  set u' : H := ⟨u, huH⟩ with hu'
  have hu'n : u' ∈ Subgroup.normalizer (Q' : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQ', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have e : ((u' * h * u'⁻¹ : H) : G) = u * (h : G) * u⁻¹ := rfl
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hu h
  have hu'N : u' ^ N = 1 := Subtype.ext (by rw [Subgroup.coe_pow, huN, Subgroup.coe_one])
  have hinv : ∀ W : Submodule k V, finrank k W ≤ 2 →
      (∀ g : End k V, Commute g (ρ z) → ∀ v ∈ W, g v ∈ W) →
      ∀ q ∈ Q, ∀ v ∈ W, ρ u (ρ q v) = ρ q (ρ u v) := by
    intro W hdimW hWinv q hq v hv
    have hW : ∀ h : H, ∀ v ∈ W, (ρ.comp H.subtype) h v ∈ W := fun h v hv =>
      hWinv _ ((hmemH h).mp h.2) v hv
    have hc := rep_commute_of_finrank_le_two h2 hdimW (restrictRep (ρ.comp H.subtype) W hW)
      hQ'2 hu'n hN hu'N ⟨q, hQH hq⟩ (show (⟨q, hQH hq⟩ : H) ∈ Q' from hq)
    exact apply_apply_comm_of_commute_restrictRep (ρ.comp H.subtype) W hW hc v hv
  have hplus : ∀ g : End k V, Commute g (ρ z) → ∀ v ∈ LinearMap.ker (ρ z - 1),
      g v ∈ LinearMap.ker (ρ z - 1) := by
    intro g hg v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 : Commute g (ρ z - 1) := hg.sub_right (Commute.one_right g)
    rw [← mul_apply, ← h1.eq, mul_apply, hv, map_zero]
  have hminus : ∀ g : End k V, Commute g (ρ z) → ∀ v ∈ LinearMap.ker (ρ z + 1),
      g v ∈ LinearMap.ker (ρ z + 1) := by
    intro g hg v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 : Commute g (ρ z + 1) := hg.add_right (Commute.one_right g)
    rw [← mul_apply, ← h1.eq, mul_apply, hv, map_zero]
  intro q hq
  refine commute_of_sup_eq_top (codisjoint_iff.mp hcompl.codisjoint) (fun v hv => ?_)
    (fun v hv => ?_)
  · exact hinv _ (by rw [hdims.1]; norm_num) hplus q hq v hv
  · exact hinv _ (by rw [hdims.2]) hminus q hq v hv

theorem exists_two_pow_dvd_three_mul_add_one (n : ℕ) : ∃ a : ℕ, 2 ^ n ∣ 3 * a + 1 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · obtain ⟨c, hc⟩ := Nat.sub_dvd_pow_sub_pow 4 1 m
    have h4 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    rw [one_pow] at hc
    have h2n : 2 ^ n = 4 ^ m := by rw [hm, pow_mul]; norm_num
    exact ⟨c, ⟨1, by omega⟩⟩
  · obtain ⟨c, hc⟩ := Nat.sub_dvd_pow_sub_pow 4 1 (m + 1)
    have h4 : 1 ≤ 4 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    rw [one_pow] at hc
    have h2n : 2 * 2 ^ n = 4 ^ (m + 1) := by
      rw [hm, ← pow_succ', show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
      norm_num
    exact ⟨c, ⟨2, by omega⟩⟩

theorem rep_commute_of_finrank_eq_three (h2 : (2 : k) ≠ 0) (hV : finrank k V = 3)
    {G : Type*} [Group G] (ρ : G →* End k V) {Q : Subgroup G} [Finite Q] (hQ : IsPGroup 2 Q)
    {u : G} (hu : u ∈ Subgroup.normalizer (Q : Set G)) {N : ℕ} (hN : Nat.Coprime N 6)
    (huN : u ^ N = 1) : ∀ q ∈ Q, Commute (ρ u) (ρ q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨a, ha⟩ := exists_two_pow_dvd_three_mul_add_one n
  set ρ' : G →* End k V :=
    { toFun := fun g => (LinearMap.det (ρ g)) ^ a • ρ g
      map_one' := by rw [map_one, map_one, one_pow, one_smul]
      map_mul' := fun g h => by
        rw [map_mul, map_mul, mul_pow, smul_mul_smul_comm] } with hρ'
  have hρ'g : ∀ g, ρ' g = (LinearMap.det (ρ g)) ^ a • ρ g := fun _ => rfl
  have hdet0 : ∀ g, LinearMap.det (ρ g) ≠ 0 := by
    intro g h
    have h1 : LinearMap.det (ρ g) * LinearMap.det (ρ g⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hdet' : ∀ q ∈ Q, LinearMap.det (ρ' q) = 1 := by
    intro q hq
    have hq1 : LinearMap.det (ρ q) ^ 2 ^ n = 1 := by
      have h1 : (⟨q, hq⟩ : Q) ^ 2 ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
      have h3 : q ^ 2 ^ n = 1 := congrArg Subtype.val h1
      rw [← map_pow, ← map_pow, h3, map_one, map_one]
    obtain ⟨t, ht⟩ := ha
    rw [hρ'g, LinearMap.det_smul, hV, ← pow_mul, ← pow_succ, mul_comm a 3, ht, pow_mul, hq1,
      one_pow]
  intro q hq
  have hc := rep_commute_of_finrank_eq_three_of_det h2 hV ρ' hQ hdet' hu hN huN q hq
  rw [hρ'g, hρ'g] at hc
  have hc' : ((LinearMap.det (ρ u)) ^ a * (LinearMap.det (ρ q)) ^ a) • (ρ u * ρ q) =
      ((LinearMap.det (ρ u)) ^ a * (LinearMap.det (ρ q)) ^ a) • (ρ q * ρ u) := by
    have h1 := hc.eq
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (LinearMap.det (ρ q) ^ a)] at h1
    exact h1
  exact smul_right_injective (End k V)
    (mul_ne_zero (pow_ne_zero a (hdet0 u)) (pow_ne_zero a (hdet0 q))) hc'

theorem rep_commute_of_finrank_le_three [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    (hV : finrank k V ≤ 3) {G : Type*} [Group G] (ρ : G →* End k V) {Q : Subgroup G}
    [Finite Q] (hQ : IsPGroup 2 Q) {u : G} (hu : u ∈ Subgroup.normalizer (Q : Set G)) {N : ℕ}
    (hN : Nat.Coprime N 6) (huN : u ^ N = 1) : ∀ q ∈ Q, Commute (ρ u) (ρ q) := by
  rcases Nat.lt_or_ge (finrank k V) 3 with h | h
  · exact rep_commute_of_finrank_le_two h2 (by omega) ρ hQ hu hN huN
  · exact rep_commute_of_finrank_eq_three h2 (by omega) ρ hQ hu hN huN

theorem odd_characteristic_degree_three_large_prime_normalizers_centralize_two_subgroups
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {n : ℕ} (hn : n ≤ 3)
    {Q P : Subgroup (GL (Fin n) k)} [Finite Q] (hQ : IsPGroup 2 Q) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hP : IsPGroup p P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (GL (Fin n) k))) : ⁅P, Q⁆ = ⊥ := by
  set ρ : GL (Fin n) k →* End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin n) (Fin n) k)) with hρ
  have hρinj : Function.Injective ρ := fun x y h =>
    Units.ext ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective h)
  have hp6 : Nat.Coprime p 6 := by
    have h2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
    exact Nat.Coprime.mul_right h2' h3'
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨m, hm⟩ := hP ⟨u, hu⟩
  have huN : u ^ p ^ m = 1 := congrArg Subtype.val hm
  have h := rep_commute_of_finrank_le_three h2 (by rw [Module.finrank_fin_fun]; exact hn) ρ hQ
    (hPQ hu) (Nat.Coprime.pow_left m hp6) huN q hq
  exact (hρinj (by rw [map_mul, map_mul]; exact h.eq)).symm

end CFSG.Quasithin.SteinbergCD
