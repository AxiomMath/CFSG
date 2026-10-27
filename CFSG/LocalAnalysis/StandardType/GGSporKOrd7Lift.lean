module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.ChevTwo.OppCl.Toolkit

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.LieType.ChevTwo.OppCl

private theorem lr2ol_pow_semilin {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (r : Equiv.Perm V) (σ : F ≃+* F)
    (hσ : ∀ (c : F) (v : V), r (c • v) = σ c • r v) :
    ∀ (m : ℕ) (c : F) (v : V), (r ^ m) (c • v) = (σ ^ m) c • (r ^ m) v := by
  intro m
  induction m with
  | zero => intro c v; simp
  | succ m ih =>
      intro c v
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, hσ, ih]
      simp

theorem ord7_linear_of_isPGroup {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] (Rh : Subgroup (Equiv.Perm V)) (hle : Rh ≤ semilinGroup F V) (hp : IsPGroup 7 Rh)
    (h7 : ¬ 7 ∣ Nat.card (F ≃+* F)) :
    ∀ r ∈ Rh, ∀ (c : F) (v : V), r (c • v) = c • r v := by
  intro r hr c v
  obtain ⟨_, σ, hσ⟩ : (∀ u v, r (u + v) = r u + r v) ∧
      ∃ σ : F ≃+* F, ∀ (c : F) (v : V), r (c • v) = σ c • r v := hle hr
  obtain ⟨k, hk⟩ := hp ⟨r, hr⟩
  have hpow : r ^ (7 ^ k) = 1 := by
    have h := congrArg (fun x : Rh => (x : Equiv.Perm V)) hk
    simpa using h
  have hsig : σ ^ (7 ^ k) = 1 := by
    ext c
    change (σ ^ (7 ^ k)) c = c
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h := lr2ol_pow_semilin r σ hσ (7 ^ k) c v
    rw [hpow] at h
    simp only [OneMemClass.coe_one, Equiv.Perm.one_apply] at h
    exact ((smul_left_injective F hv) h).symm
  have hcop7 : Nat.Coprime 7 (Nat.card (F ≃+* F)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr h7
  have hdiv : orderOf σ ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one hsig
  have hcop : Nat.Coprime (orderOf σ) (Nat.card (F ≃+* F)) :=
    (hcop7.pow_left k).coprime_dvd_left hdiv
  have horder : orderOf σ = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_natCard σ)
  have hsigma1 : σ = 1 := orderOf_eq_one_iff.mp horder
  rw [hsigma1] at hσ
  simpa using hσ c v

private lemma lr2olb_induces_functional {F V H K : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group H] [Group K] (π : H →* K) (ρ : H →* Module.End F V)
    (hπ : Function.Surjective π) (hρ : Function.Injective ρ)
    {r : Equiv.Perm V} {α β : MulAut K} (hα : Induces π ρ r α) (hβ : Induces π ρ r β) :
    α = β := by
  apply MulEquiv.ext
  intro k
  obtain ⟨h, rfl⟩ := hπ k
  obtain ⟨h', hh', hα'⟩ := hα.1 h
  obtain ⟨h'', hh'', hβ'⟩ := hβ.1 h
  have hρeq : ρ h' = ρ h'' := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := r.surjective v
    rw [← hh' w, ← hh'' w]
  have hh : h' = h'' := hρ hρeq
  rw [hα', hβ', hh]

private lemma lr2olb_card_eq {H K : Type} [Group H] [Group K] (π : H →* K)
    (hπ : Function.Surjective π) :
    Nat.card H = Nat.card K * Nat.card π.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv

private lemma lr2olb_card_rh_dvd {F V H : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group H] (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (Rh : Subgroup (Equiv.Perm V))
    (hlin : ∀ r ∈ Rh, ∃ h : H, ∀ v, r v = ρ h v) :
    Nat.card Rh ∣ Nat.card H := by
  classical
  let hOf : Rh → H := fun r => Classical.choose (hlin r r.2)
  have hOf_spec : ∀ r : Rh, ∀ v, (r : Equiv.Perm V) v = ρ (hOf r) v :=
    fun r => Classical.choose_spec (hlin r r.2)
  let Hr : Subgroup H :=
    { carrier := {h : H | ∃ r ∈ Rh, ∀ v, r v = ρ h v}
      one_mem' := ⟨1, Subgroup.one_mem Rh, fun v => by simp⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨r, hr, hrv⟩ := ha
        obtain ⟨s, hs, hsv⟩ := hb
        exact ⟨r * s, mul_mem hr hs, fun v => by
          rw [Equiv.Perm.mul_apply, hrv (s v), hsv v, map_mul]
          rfl⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨r, hr, hrv⟩ := ha
        refine ⟨r⁻¹, inv_mem hr, fun v => ?_⟩
        rw [Equiv.Perm.inv_def]
        apply r.injective
        rw [Equiv.apply_symm_apply, hrv (ρ a⁻¹ v)]
        change v = (ρ a * ρ a⁻¹) v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  have hf_mem : ∀ r : Rh, hOf r ∈ Hr := fun r => ⟨r, r.2, hOf_spec r⟩
  let f : Rh → Hr := fun r => ⟨hOf r, hf_mem r⟩
  have hf_inj : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro v
    have hhs : hOf r = hOf s := congrArg Subtype.val hrs
    rw [hOf_spec r v, hhs, ← hOf_spec s v]
  have hf_surj : Function.Surjective f := by
    intro h
    obtain ⟨r, hr, hrv⟩ := h.2
    refine ⟨⟨r, hr⟩, ?_⟩
    apply Subtype.ext
    apply hρ
    apply LinearMap.ext
    intro v
    rw [← hOf_spec ⟨r, hr⟩ v]
    exact hrv v
  have hcard : Nat.card Rh = Nat.card Hr :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [hcard]
  exact Subgroup.card_subgroup_dvd_card Hr

theorem ord7_factorization_le_of_lift {F V H K : Type} [Field F] [AddCommGroup V]
    [Module F V] [Finite V] [Nontrivial V] [Group H] [Group K] [Finite K] (π : H →* K)
    (hπ : Function.Surjective π) (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (P : Equiv.Perm V → Prop) (hP1 : P 1) (hPm : ∀ r s, P r → P s → P (r * s))
    (hPi : ∀ r, P r → P r⁻¹) (h7F : ¬ 7 ∣ Nat.card (F ≃+* F)) (h7k : ¬ 7 ∣ Nat.card π.ker)
    (hind : ∀ R : Subgroup (MulAut K), IsPGroup 7 R → ∀ α ∈ R, ∃ r : Equiv.Perm V,
      r ∈ semilinGroup F V ∧ P r ∧ Induces π ρ r α)
    (hlin : ∀ r : Equiv.Perm V, r ∈ semilinGroup F V → P r →
      (∀ (c : F) (v : V), r (c • v) = c • r v) → IsPGroup 7 (Subgroup.zpowers r) →
        ∃ h : H, ∀ v, r v = ρ h v) :
    (Nat.card (MulAut K)).factorization 7 ≤ (Nat.card K).factorization 7 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite (MulAut K) := inferInstance
  obtain ⟨S⟩ : Nonempty (Sylow 7 (MulAut K)) := Sylow.nonempty
  let R : Subgroup (MulAut K) := S
  have hR : IsPGroup 7 R := by simpa only [R] using S.isPGroup'
  have hS : Nat.card R = 7 ^ (Nat.card (MulAut K)).factorization 7 := by
    simpa only [R] using Sylow.card_eq_multiplicity S
  obtain ⟨Rh, hRh_le, hRh_P, hRh_p, hRh_norm, hInd, hInd'⟩ :=
    autLift_of_induced (P := P) hP1 hPm hPi 7 R hR (hind R hR)
  haveI : Finite Rh := inferInstance
  have hchoose : ∀ α : R, ∃ r ∈ Rh, Induces π ρ r (α : MulAut K) :=
    fun α => hInd α α.2
  let rOf : R → Rh := fun α =>
    ⟨Classical.choose (hchoose α), (Classical.choose_spec (hchoose α)).1⟩
  have hrOf_spec : ∀ α : R,
      Induces π ρ (rOf α) (α : MulAut K) :=
    fun α => (Classical.choose_spec (hchoose α)).2
  have hle_card : Nat.card R ≤ Nat.card Rh := by
    refine Nat.card_le_card_of_injective rOf ?_
    intro α β hαβ
    apply Subtype.ext
    have h1 : Induces π ρ (rOf α) (α : MulAut K) := hrOf_spec α
    have h2 : Induces π ρ (rOf β) (β : MulAut K) := hrOf_spec β
    have hEq : (rOf α : Equiv.Perm V) = (rOf β : Equiv.Perm V) := congrArg Subtype.val hαβ
    rw [← hEq] at h2
    exact lr2olb_induces_functional π ρ hπ hρ h1 h2
  have hlin_all : ∀ r ∈ Rh, ∃ h : H, ∀ v, r v = ρ h v := by
    intro r hr
    refine hlin r (hRh_le hr) (hRh_P r hr) ?_ ?_
    · exact ord7_linear_of_isPGroup Rh hRh_le hRh_p h7F r hr
    · exact hRh_p.to_le (Subgroup.zpowers_le.mpr hr)
  have hdvd : Nat.card Rh ∣ Nat.card H := lr2olb_card_rh_dvd ρ hρ Rh hlin_all
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRh_p
  have hcardH : Nat.card H = Nat.card K * Nat.card π.ker := lr2olb_card_eq π hπ
  have h7cop : Nat.Coprime 7 (Nat.card π.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr h7k
  have hpow_dvd : 7 ^ n ∣ Nat.card K := by
    have hd : 7 ^ n ∣ Nat.card H := by rw [← hn]; exact hdvd
    rw [hcardH] at hd
    have hcop : Nat.Coprime (7 ^ n) (Nat.card π.ker) := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · rw [hn0]; simp
      · exact (Nat.coprime_pow_left_iff hnpos 7 (Nat.card π.ker)).mpr h7cop
    exact (Nat.Coprime.dvd_mul_right hcop).mp hd
  have hKne : Nat.card K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hn_le : n ≤ (Nat.card K).factorization 7 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_seven hKne).mp hpow_dvd
  have ha_le : (Nat.card (MulAut K)).factorization 7 ≤ n := by
    have hle : 7 ^ (Nat.card (MulAut K)).factorization 7 ≤ 7 ^ n := by
      rw [← hS, ← hn]
      exact hle_card
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < (7 : ℕ))).mp hle
  exact le_trans ha_le hn_le

end CFSG.StandardType.SporadicShape
