module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIb

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129KEh

theorem isHeisThree_sup_zpowers {H : Type} [Group H] [Finite H] {F : Subgroup H} {b c : H}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) (hb3 : b ^ 3 = 1)
    (hbN : b ∈ Subgroup.normalizer (F : Set H)) (hcF : c ∈ F)
    (hcomm : ∀ f ∈ F, b * f * b⁻¹ * f⁻¹ ∈ Subgroup.zpowers c)
    (hne : ∃ f ∈ F, b * f * b⁻¹ * f⁻¹ ≠ 1) :
    b ∉ F ∧ Nat.card (F ⊔ Subgroup.zpowers b : Subgroup H) = 27 ∧
      Sec4.IsHeisThree ↥(F ⊔ Subgroup.zpowers b) ∧
      ∀ u ∈ F ⊔ Subgroup.zpowers b, u * c = c * u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f₀, hf₀F, hf₀⟩ := hne
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := fun x hx => hF.2 x hx
  have hbF : b ∉ F := by
    intro hbF
    apply hf₀
    rw [hFc b hbF f₀ hf₀F]
    group
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hf₀
    simp
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hbmod : ∀ i : ℤ, b ^ i = b ^ (i % 3) := by
    intro i
    have h := zpow_mod_orderOf b i
    rw [hord, Nat.cast_ofNat] at h
    exact h.symm
  have hbnat : ∀ i : ℤ, b ^ i = b ^ (i % 3).toNat := by
    intro i
    rw [hbmod i, ← zpow_natCast, Int.toNat_of_nonneg (show (0 : ℤ) ≤ i % 3 by omega)]
  have hinf : F ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxb
    rw [Subgroup.mem_bot]
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · rw [hbmod k, h, zpow_zero]
    · exfalso
      rw [hbmod k, h, zpow_one] at hxF
      exact hbF hxF
    · exfalso
      have h2 : b ^ k * b ^ k ∈ F := mul_mem hxF hxF
      rw [← zpow_add, hbmod (k + k)] at h2
      have h4 : (k + k) % 3 = 1 := by omega
      rw [h4, zpow_one] at h2
      exact hbF h2
  have hLE : Subgroup.zpowers b ≤ Subgroup.normalizer (F : Set H) :=
    Subgroup.zpowers_le.mpr hbN
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left F (Subgroup.zpowers b) hLE
  have hdecomp : ∀ u ∈ F ⊔ Subgroup.zpowers b, ∃ f ∈ F, ∃ i : ℤ, u = f * b ^ i := by
    intro u hu
    open scoped Pointwise in
    have hu' : u ∈ (F : Set H) * (Subgroup.zpowers b : Set H) := by
      rw [← hset]
      exact hu
    obtain ⟨f, hf, x, hx, rfl⟩ := hu'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨f, hf, i, rfl⟩
  have hcard : Nat.card (F ⊔ Subgroup.zpowers b : Subgroup H) = 27 := by
    let φ : F × Subgroup.zpowers b → (F ⊔ Subgroup.zpowers b : Subgroup H) := fun p =>
      ⟨p.1.1 * p.2.1, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
    have hφ : Function.Bijective φ := by
      constructor
      · rintro ⟨⟨f1, hf1⟩, ⟨x1, hx1⟩⟩ ⟨⟨f2, hf2⟩, ⟨x2, hx2⟩⟩ h
        have h' : f1 * x1 = f2 * x2 := congrArg Subtype.val h
        have key1 : f2⁻¹ * f1 = x2 * x1⁻¹ := by
          calc f2⁻¹ * f1 = f2⁻¹ * (f1 * x1) * x1⁻¹ := by group
            _ = f2⁻¹ * (f2 * x2) * x1⁻¹ := by rw [h']
            _ = x2 * x1⁻¹ := by group
        have hmem : f2⁻¹ * f1 ∈ F ⊓ Subgroup.zpowers b := by
          refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hf2) hf1, ?_⟩
          rw [key1]
          exact mul_mem hx2 (inv_mem hx1)
        rw [hinf, Subgroup.mem_bot] at hmem
        have e1 : f1 = f2 := (inv_mul_eq_one.mp hmem).symm
        have e2 : x2 = x1 := by
          have hx : x2 * x1⁻¹ = 1 := by
            rw [← key1]
            exact hmem
          exact mul_inv_eq_one.mp hx
        subst e1
        subst e2
        rfl
      · rintro ⟨u, hu⟩
        obtain ⟨f, hf, i, rfl⟩ := hdecomp u hu
        exact ⟨(⟨f, hf⟩, ⟨b ^ i, Subgroup.zpow_mem_zpowers b i⟩), rfl⟩
    have hcongr := Nat.card_congr (Equiv.ofBijective φ hφ)
    rw [Nat.card_prod, hF9, hcardb] at hcongr
    omega
  have hc1 : c ≠ 1 := by
    intro h
    apply hf₀
    have h' := hcomm f₀ hf₀F
    rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h'
    exact h'
  have hc3 : c ^ 3 = 1 := hF3 c hcF
  have hordc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have key : ∀ x : ℤ, (3 : ℤ) ∣ x ^ 3 - 1 → x % 3 = 1 := by
    intro x hx
    have h0 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    rcases h0 with h0 | h0 | h0
    · exfalso
      have h7 : (x ^ 3 - 1) % 3 = 2 := by
        simp [pow_three', Int.sub_emod, Int.mul_emod, h0]
      generalize x ^ 3 = y at hx h7
      omega
    · exact h0
    · exfalso
      have h7 : (x ^ 3 - 1) % 3 = 1 := by
        simp [pow_three', Int.sub_emod, Int.mul_emod, h0]
      generalize x ^ 3 = y at hx h7
      omega
  have hbc : b * c = c * b := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcomm c hcF)
    obtain ⟨a, ha⟩ : ∃ a : ℤ, b * c * b⁻¹ = c ^ a :=
      ⟨k + 1, by rw [zpow_add_one, hk]; group⟩
    have hpow : ∀ n : ℕ, b ^ n * c * (b ^ n)⁻¹ = c ^ (a ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc b ^ (n + 1) * c * (b ^ (n + 1))⁻¹ = b ^ n * (b * c * b⁻¹) * (b ^ n)⁻¹ := by
              group
          _ = b ^ n * c ^ a * (b ^ n)⁻¹ := by rw [ha]
          _ = (b ^ n * c * (b ^ n)⁻¹) ^ a := by rw [conj_zpow]
          _ = (c ^ (a ^ n)) ^ a := by rw [ih]
          _ = c ^ (a ^ (n + 1)) := by rw [← zpow_mul, pow_succ]
    have h3c : c = c ^ (a ^ 3) := by
      have h := hpow 3
      rw [hb3] at h
      simpa using h
    have hdvd : (3 : ℤ) ∣ a ^ 3 - 1 := by
      have h4 : c ^ (a ^ 3 - 1) = 1 := by
        rw [zpow_sub_one, ← h3c, mul_inv_cancel]
      have h5 := orderOf_dvd_iff_zpow_eq_one.mpr h4
      rw [hordc] at h5
      exact_mod_cast h5
    have ha1 : a % 3 = 1 := key a hdvd
    have hca : c ^ a = c := by
      have h6 := zpow_mod_orderOf c a
      rw [hordc, Nat.cast_ofNat, ha1, zpow_one] at h6
      exact h6.symm
    rw [hca] at ha
    exact mul_inv_eq_iff_eq_mul.mp ha
  have hbc_comm : Commute b c := hbc
  have hconjF : ∀ f ∈ F, ∃ s : ℤ, b * f = f * c ^ s * b := by
    intro f hf
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hcomm f hf)
    refine ⟨s, ?_⟩
    have h1 : b * f = c ^ s * f * b := by
      rw [hs]
      group
    rw [h1, hFc (c ^ s) (zpow_mem hcF s) f hf]
  have hE : ∀ f : H, ∀ s : ℤ, b * f = f * c ^ s * b → ∀ n : ℕ,
      b ^ n * f = f * c ^ ((n : ℤ) * s) * b ^ n := by
    intro f s hs n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : b ^ n * c ^ s = c ^ s * b ^ n := ((hbc_comm.pow_left n).zpow_right s).eq
      have hcc : c ^ ((n : ℤ) * s) * c ^ s = c ^ (((n + 1 : ℕ) : ℤ) * s) := by
        rw [← zpow_add]
        congr 1
        push_cast
        ring
      calc b ^ (n + 1) * f = b ^ n * (b * f) := by rw [pow_succ, mul_assoc]
        _ = b ^ n * (f * c ^ s * b) := by rw [hs]
        _ = b ^ n * f * c ^ s * b := by group
        _ = f * c ^ ((n : ℤ) * s) * b ^ n * c ^ s * b := by rw [ih]
        _ = f * c ^ ((n : ℤ) * s) * (b ^ n * c ^ s) * b := by group
        _ = f * c ^ ((n : ℤ) * s) * (c ^ s * b ^ n) * b := by rw [hcn]
        _ = f * (c ^ ((n : ℤ) * s) * c ^ s) * b ^ n * b := by group
        _ = f * c ^ (((n + 1 : ℕ) : ℤ) * s) * b ^ n * b := by rw [hcc]
        _ = f * c ^ (((n + 1 : ℕ) : ℤ) * s) * b ^ (n + 1) := by rw [pow_succ]; group
  have hexp : ∀ f ∈ F, ∀ n : ℕ, (f * b ^ n) ^ 3 = 1 := by
    intro f hf n
    obtain ⟨s, hs⟩ := hconjF f hf
    have h1 := hE f s hs n
    have h2 := hE f s hs (n + n)
    have hfm : c ^ ((n : ℤ) * s) * f = f * c ^ ((n : ℤ) * s) :=
      hFc _ (zpow_mem hcF _) f hf
    have hmm : c ^ ((n : ℤ) * s) * c ^ (((n + n : ℕ) : ℤ) * s) = 1 := by
      rw [← zpow_add]
      refine orderOf_dvd_iff_zpow_eq_one.mp ?_
      rw [hordc]
      exact ⟨(n : ℤ) * s, by push_cast; ring⟩
    have hb2 : b ^ (n + n) * b ^ n = 1 := by
      rw [← pow_add, show n + n + n = 3 * n by ring, pow_mul, hb3, one_pow]
    have hfff : f * f * f = 1 := by
      rw [← pow_three']
      exact hF3 f hf
    calc (f * b ^ n) ^ 3 = f * (b ^ n * f) * b ^ n * f * b ^ n := by
          rw [pow_three']
          group
      _ = f * (f * c ^ ((n : ℤ) * s) * b ^ n) * b ^ n * f * b ^ n := by rw [h1]
      _ = f * f * c ^ ((n : ℤ) * s) * (b ^ n * b ^ n) * f * b ^ n := by group
      _ = f * f * c ^ ((n : ℤ) * s) * (b ^ (n + n) * f) * b ^ n := by
          simp only [pow_add, mul_assoc]
      _ = f * f * c ^ ((n : ℤ) * s) * (f * c ^ (((n + n : ℕ) : ℤ) * s) * b ^ (n + n)) * b ^ n := by
          rw [h2]
      _ = f * f * (c ^ ((n : ℤ) * s) * f) * c ^ (((n + n : ℕ) : ℤ) * s) *
            (b ^ (n + n) * b ^ n) := by group
      _ = f * f * (f * c ^ ((n : ℤ) * s)) * c ^ (((n + n : ℕ) : ℤ) * s) * 1 := by
          rw [hfm, hb2]
      _ = f * f * f * (c ^ ((n : ℤ) * s) * c ^ (((n + n : ℕ) : ℤ) * s)) := by group
      _ = 1 := by rw [hfff, hmm, mul_one]
  have hU3 : ∀ u ∈ F ⊔ Subgroup.zpowers b, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨f, hf, i, rfl⟩ := hdecomp u hu
    rw [hbnat i]
    exact hexp f hf _
  have hU3' : ∀ x : ↥(F ⊔ Subgroup.zpowers b : Subgroup H), x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hU3 x.1 x.2
  have hcentral : ∀ u ∈ F ⊔ Subgroup.zpowers b, u * c = c * u := by
    intro u hu
    obtain ⟨f, hf, i, rfl⟩ := hdecomp u hu
    have hfc : Commute f c := hFc f hf c hcF
    have hbi : Commute (b ^ i) c := hbc_comm.zpow_left i
    exact (hfc.mul_left hbi).eq
  have hnc : ¬ IsMulCommutative ↥(F ⊔ Subgroup.zpowers b : Subgroup H) := by
    intro h
    have hbU : b ∈ F ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hfU : f₀ ∈ F ⊔ Subgroup.zpowers b := Subgroup.mem_sup_left hf₀F
    have hc := h.is_comm.comm ⟨b, hbU⟩ ⟨f₀, hfU⟩
    have hc' : b * f₀ = f₀ * b := congrArg Subtype.val hc
    apply hf₀
    rw [hc']
    group
  exact ⟨hbF, hcard, Sec4.isHeisThree_of _ hcard hU3' hnc, hcentral⟩

end Hering129KEh

end CFSG.RankThree.PartTwo.Sec12
