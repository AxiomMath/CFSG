module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryC1.Commute
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryC1.Normal
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

open UnitaryFrame UnitaryHeisenberg NearSolvable


section Prime

variable {Y : Type*} [Group Y]

theorem UnitaryHeisenberg.exists_abelian_normalized_pGroup [Finite Y] {C N : Subgroup Y} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓN : ℓ ∣ Nat.card N) (hCN : C ≤ Subgroup.normalizer (N : Set Y))
    (hCsolv : Group.IsSolvable C) (hCcop : Nat.Coprime (Nat.card C) (Nat.card N)) :
    ∃ V : Subgroup Y, V ≤ N ∧ V ≠ ⊥ ∧ IsPGroup ℓ V ∧ (∀ x ∈ V, ∀ y ∈ V, Commute x y) ∧
      ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let _inst := CFSG.SignalizerFunctor.Helpers.conjugationAction C N hCN
  obtain ⟨R, hR⟩ := CFSG.exists_invariant_sylow_of_solvable_operator_coprime (G := N) (A := C)
    hCcop (p := ℓ)
  set R₁ : Subgroup Y := (R : Subgroup N).map N.subtype with hR₁
  have hR₁p : IsPGroup ℓ R₁ := R.isPGroup'.map N.subtype
  have hR₁ne : R₁ ≠ ⊥ := by
    intro h
    have h1 : Nat.card R₁ = 1 := Subgroup.card_eq_one.mpr h
    rw [hR₁, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity] at h1
    have h2 : 0 < (Nat.card N).factorization ℓ :=
      hℓ.factorization_pos_of_dvd (Nat.card_pos.ne') hℓN
    have : ℓ ^ (Nat.card N).factorization ℓ ≠ 1 := by
      intro h3
      exact (Nat.one_lt_pow h2.ne' hℓ.one_lt).ne' h3
    exact this h1
  have hR₁le : R₁ ≤ N := Subgroup.map_subtype_le _
  have hCR : ∀ c ∈ C, ∀ x ∈ R₁, c * x * c⁻¹ ∈ R₁ := by
    rintro c hc _ ⟨n, hn, rfl⟩
    have := (hR.invariant ⟨c, hc⟩ n).mp hn
    exact ⟨_, this, rfl⟩
  refine ⟨R₁ ⊓ Subgroup.centralizer (R₁ : Set Y), inf_le_left.trans hR₁le, ?_, ?_, ?_, ?_⟩
  · have hnt : Nontrivial R₁ := (Subgroup.nontrivial_iff_ne_bot R₁).mpr hR₁ne
    have hz := hR₁p.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center R₁)
    intro hbot
    apply hz1
    have hzV : ((z : R₁) : Y) ∈ R₁ ⊓ Subgroup.centralizer (R₁ : Set Y) := by
      refine ⟨(z : R₁).2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have := Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩
      exact congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at hzV
    apply Subtype.ext
    apply Subtype.ext
    exact hzV
  · exact hR₁p.to_le inf_le_left
  · intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  · intro c hc v hv
    refine ⟨hCR c hc v hv.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : c⁻¹ * w * c ∈ R₁ := by simpa using hCR c⁻¹ (inv_mem hc) w hw
    have := Subgroup.mem_centralizer_iff.mp hv.2 _ hw'
    calc w * (c * v * c⁻¹) = c * ((c⁻¹ * w * c) * v) * c⁻¹ := by group
      _ = c * (v * (c⁻¹ * w * c)) * c⁻¹ := by rw [this]
      _ = c * v * c⁻¹ * w := by group

end Prime

theorem UnitaryFrame.exists_prime_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ p - 1 ∧ r ∣ Nat.card (PSU3 2 p) ∧ Nat.Coprime r 6 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h32 : 2 ^ p % 3 = 2 := two_pow_mod_three hodd
  have h2p : 2 ^ 5 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h5
  have heven : 2 ^ p % 2 = 0 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, hp.ne_zero⟩)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ p - 1 ≠ 1 by omega)
  have hr2 : ¬ r ∣ 2 := by
    intro h
    have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h
    subst this
    omega
  have hr3 : ¬ r ∣ 3 := by
    intro h
    have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
    subst this
    omega
  refine ⟨r, hr, hrd, ?_, ?_⟩
  · have hmul := card_psu3_mul_gcd hp.one_le
    have h3 : Nat.gcd 3 (2 ^ p + 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [h3] at hmul
    have hdvd : r ∣ Nat.card (PSU3 2 p) * 3 := by
      rw [hmul]
      refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
      rw [show (2 ^ p) ^ 2 - 1 = (2 ^ p + 1) * (2 ^ p - 1) by rw [← Nat.sq_sub_sq, one_pow]]
      exact hrd.mul_left _
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
    · exact h
    · exact absurd h hr3
  · have h2 : Nat.Coprime r 2 := (Nat.Prime.coprime_iff_not_dvd hr).mpr hr2
    have h3 : Nat.Coprime r 3 := (Nat.Prime.coprime_iff_not_dvd hr).mpr hr3
    simpa using Nat.Coprime.mul_right h2 h3

variable {p : ℕ}

theorem UnitaryFrame.eq_top_of_overgroup_psu3
    {r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (inp : HeisenbergInput p)
    {C P C₁ H : Subgroup (PSU3 2 p)} (hF : FixedData C P) (hPC₁ : P ≤ C₁) (hC₁C : C₁ ≤ C)
    (ht : ∃ t ∈ C₁, orderOf t = 2) (hC₁H : C₁ ≤ H) (hr : r.Prime) (hrd : r ∣ 2 ^ p - 1)
    (hy : ∃ y ∈ H, orderOf y = r) : H = ⊤ := by
  by_contra hH
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h32 : 2 ^ p % 3 = 2 := two_pow_mod_three hodd
  have h2p : 2 ^ 5 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h5
  have heven : 2 ^ p % 2 = 0 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, hp.ne_zero⟩)
  have hr2 : ¬ r ∣ 2 := by
    intro h
    have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h
    subst this
    omega
  have hr3 : ¬ r ∣ 3 := by
    intro h
    have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
    subst this
    omega
  have hr6 : Nat.Coprime r 6 := by
    have h2 : Nat.Coprime r 2 := (Nat.Prime.coprime_iff_not_dvd hr).mpr hr2
    have h3 : Nat.Coprime r 3 := (Nat.Prime.coprime_iff_not_dvd hr).mpr hr3
    simpa using Nat.Coprime.mul_right h2 h3
  obtain ⟨t, htC₁, ht2⟩ := ht
  obtain ⟨N, hNH, hHN, hN6, hNall⟩ := exists_normal_coprime_six_of_overgroup hp h5 hnear inp hF
    (hPC₁.trans hC₁H) ⟨t, ⟨hC₁H htC₁, hC₁C htC₁⟩, ht2⟩ hH
  obtain ⟨y, hyH, hyr⟩ := hy
  have hyN : y ∈ N := hNall y hyH (by rw [hyr]; exact hr6)
  have hrN : r ∣ Nat.card N := by
    rw [← hyr]
    exact Subgroup.orderOf_dvd_natCard N hyN
  have hC₁N : C₁ ≤ Subgroup.normalizer (N : Set (PSU3 2 p)) := hC₁H.trans hHN
  have hC72 : Nat.card C₁ ∣ 72 := hF.card_C ▸ Subgroup.card_dvd_of_le hC₁C
  have hN72 : Nat.Coprime (Nat.card N) 72 := by
    have h2 : Nat.Coprime (Nat.card N) 2 := hN6.coprime_dvd_right (by norm_num)
    have h36 : Nat.Coprime (Nat.card N) (6 ^ 2) := hN6.pow_right 2
    simpa using h36.mul_right h2
  have hcop : Nat.Coprime (Nat.card C₁) (Nat.card N) := (hN72.symm).coprime_dvd_left hC72
  have hsolv : Group.IsSolvable C₁ := isSolvable_of_card_dvd_seventy_two hC72
  obtain ⟨V, hVN, hV1, hVp, hVcomm, hCV⟩ :=
    exists_abelian_normalized_pGroup hr hrN hC₁N hsolv hcop
  have hPV : P ≤ Subgroup.normalizer (V : Set (PSU3 2 p)) := fun c hc =>
    mem_normalizer_of_forall (fun x hx => hCV c (hPC₁ hc) x hx) (fun x hx => by
      simpa using hCV c⁻¹ (inv_mem (hPC₁ hc)) x hx)
  have hN3 : Nat.Coprime 3 (Nat.card N) := (hN6.symm).coprime_dvd_left (by norm_num)
  have hVcop : Nat.Coprime 3 (Nat.card V) :=
    hN3.coprime_dvd_right (Subgroup.card_dvd_of_le hVN)
  have hgen := iSup_centralizer_nonidentity Nat.prime_three hF.isElemAbelian
    (by simp [hF.card_P]) hPV hVcop
  obtain ⟨u₀, hu₀, hu₀1, hne⟩ : ∃ u₀ ∈ P, u₀ ≠ 1 ∧
      V ⊓ Subgroup.centralizer ({u₀} : Set (PSU3 2 p)) ≠ ⊥ := by
    by_contra! hall
    apply hV1
    rw [← hgen]
    exact iSup_eq_bot.mpr fun a => iSup_eq_bot.mpr fun ha => iSup_eq_bot.mpr fun ha1 =>
      hall a ha ha1
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (Subtype.ext h)
  have hx₀V : x₀ ∈ V := hx₀.1
  have hx₀u : u₀ * x₀ = x₀ * u₀ := (Subgroup.mem_centralizer_singleton_iff.mp hx₀.2).symm
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hVp) (⟨x₀, hx₀V⟩ : V)
  have hord : orderOf x₀ = r ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hx₀1 (orderOf_eq_one_iff.mp (by simpa using hord))
  have hrdvd : r ∣ orderOf x₀ := by
    rw [hord]
    exact dvd_pow_self r hk1
  have hxr : orderOf (x₀ ^ (orderOf x₀ / r)) = r :=
    orderOf_pow_orderOf_div (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x₀)).ne' hrdvd
  exact not_commute_of_orderOf_prime_dvd hp h5 hF hr hrd hu₀ hu₀1 hxr
    (((Commute.pow_left (show Commute x₀ u₀ from hx₀u.symm) _)).eq)


open scoped commutatorElement in
theorem exists_prime_overgroup_psu3
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card (PSU3 2 p) ∧ ¬ r ∣ Nat.card (fixedNormalizer f) ∧
      ∀ H : Subgroup (PSU3 2 p), fixedCore1 f ≤ H → (∃ y ∈ H, orderOf y = r) → H = ⊤ := by
  have h5 := five_le_of_coprime hp hcop
  have inp := heisenbergInput_psu3 hp h5
  obtain ⟨P, hF⟩ := exists_fixedData (order72_fixedSubgroup hp h5 hcop f hf)
  have hFit : fixedFitting f = P := hF.fitting
  obtain ⟨r, hr, hrd, hrY, hr6⟩ := exists_prime_dvd_two_pow_sub_one hp h5
  have hM : Nat.card (fixedNormalizer f) = 72 := by
    rw [fixedNormalizer_psu3 hp hcop f hf]
    exact card_fixedSubgroup hp hcop f hf
  refine ⟨r, hr, hrY, ?_, ?_⟩
  · rw [hM]
    have h2 : Nat.Coprime r 2 := hr6.coprime_dvd_right (by norm_num)
    have h36 : Nat.Coprime r (6 ^ 2) := hr6.pow_right 2
    have h72 : Nat.Coprime r 72 := by simpa using h36.mul_right h2
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp h72
  · intro H hC₁H hy
    have hPC₁ : P ≤ fixedCore1 f := by
      intro x hx
      refine ⟨hF.le hx, fun c hc => ?_⟩
      rw [hFit]
      have : ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact P.mul_mem hx (hF.normalizes c hc x⁻¹ (P.inv_mem hx))
    have hC₁C : fixedCore1 f ≤ signalizerFixedSubgroup f := fun c hc => hc.1
    have ht : ∃ t ∈ fixedCore1 f, orderOf t = 2 := by
      obtain ⟨z, hzC, hzP, hz⟩ := hF.exists_central
      have hzC₁ : z ∈ fixedCore1 f := ⟨hzC, fun x hx => by rw [hFit]; exact hz x hx⟩
      have h2 : 2 ∣ orderOf z := hF.two_dvd_orderOf z hzC hzP
      refine ⟨z ^ (orderOf z / 2), Subgroup.pow_mem _ hzC₁ _, ?_⟩
      exact orderOf_pow_orderOf_div (orderOf_pos_iff.mpr (isOfFinOrder_of_finite z)).ne' h2
    exact eq_top_of_overgroup_psu3 hp h5 hnear inp hF hPC₁ hC₁C ht hC₁H hr hrd hy

end CFSG.SignalizerFunctorTheorem.McBride
