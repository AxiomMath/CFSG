module

public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaFunctor

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem commutator_zpowers_inverted {P : Subgroup Γ} {z : Γ} (hz2 : z * z = 1)
    (hzP : z ∈ Subgroup.normalizer (P : Set Γ)) :
    ⁅P, Subgroup.zpowers z⁆ = Subgroup.closure {y | ∃ p ∈ P, y = ⁅p, z⁆} ∧
      ∀ p ∈ P, z * ⁅p, z⁆ * z⁻¹ = (⁅p, z⁆)⁻¹ := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hpow : ∀ n : ℤ, z ^ n = 1 ∨ z ^ n = z := by
    intro n
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
    have key : z ^ n = z ^ (n % 2) := by
      have hn : n = n % 2 + 2 * (n / 2) := by omega
      conv_lhs => rw [hn]
      rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [key, h, zpow_zero]
    · right; rw [key, h, zpow_one]
  refine ⟨le_antisymm ?_ ?_, fun p hp => ?_⟩
  · rw [Subgroup.commutator_le]
    intro p hp w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases hpow n with h | h
    · rw [h, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.subset_closure ⟨p, hp, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers z)
  · have hzz : z⁻¹ * z⁻¹ = 1 := by rw [hzinv, hz2]
    calc z * ⁅p, z⁆ * z⁻¹ = z * p * z * p⁻¹ * (z⁻¹ * z⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = z * p * z * p⁻¹ := by rw [hzz, mul_one]
      _ = z * p * z⁻¹ * p⁻¹ := by rw [hzinv]
      _ = (⁅p, z⁆)⁻¹ := by simp only [commutatorElement_def]; group

theorem not_isCyclic_commutator_cyc {P : Subgroup Γ} {c z : Γ} (hP : IsPGroup 5 P)
    (hz2 : z * z = 1) (hc3 : c ^ 3 = 1) (hzP : z ∈ Subgroup.normalizer (P : Set Γ))
    (hcP : c ∈ Subgroup.normalizer (P : Set Γ)) (hzc : z * c = c * z)
    (hperf : ⁅P, Subgroup.zpowers c⁆ = P) (hz : ∃ p ∈ P, z * p ≠ p * z) :
    ¬ IsCyclic ↥⁅P, Subgroup.zpowers z⁆ := by
  intro hK
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a₀, ha₀⟩ := IsPGroup.iff_card.mp hP
  have hzP' : Subgroup.zpowers z ≤ Subgroup.normalizer (P : Set Γ) := Subgroup.zpowers_le.mpr hzP
  have hKP : ⁅P, Subgroup.zpowers z⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hzP'
  have hdvd : Nat.card ↥⁅P, Subgroup.zpowers z⁆ ∣ 5 ^ a₀ := by
    rw [← ha₀]
    exact Subgroup.card_dvd_of_le hKP
  obtain ⟨j, -, hKj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  have h3cop : Nat.Coprime 3 (Nat.totient (Nat.card ↥⁅P, Subgroup.zpowers z⁆)) := by
    rw [hKj]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp
    · rw [Nat.totient_prime_pow (by norm_num) hjpos]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num)) (by norm_num)
  have key : ∀ a : Γ, a ∈ Subgroup.normalizer (P : Set Γ) → a * z = z * a →
      ∀ k ∈ ⁅P, Subgroup.zpowers z⁆, a * k * a⁻¹ ∈ ⁅P, Subgroup.zpowers z⁆ := by
    intro a ha haz
    have hazn : ∀ n : ℤ, a * z ^ n * a⁻¹ = z ^ n := by
      intro n
      have h1 : a * z * a⁻¹ = z := by rw [haz, mul_assoc, mul_inv_cancel, mul_one]
      rw [← conj_zpow, h1]
    have hle : ⁅P, Subgroup.zpowers z⁆ ≤
        (⁅P, Subgroup.zpowers z⁆).comap (MulEquiv.toMonoidHom (MulAut.conj a)) := by
      rw [Subgroup.commutator_le]
      intro p hp w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [Subgroup.mem_comap]
      have e : a * ⁅p, z ^ n⁆ * a⁻¹ = ⁅a * p * a⁻¹, z ^ n⁆ := by
        have hX := hazn n
        calc a * ⁅p, z ^ n⁆ * a⁻¹
            = (a * p * a⁻¹) * (a * z ^ n * a⁻¹) * (a * p * a⁻¹)⁻¹ * (a * z ^ n * a⁻¹)⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = ⁅a * p * a⁻¹, z ^ n⁆ := by rw [hX, commutatorElement_def]
      show a * ⁅p, z ^ n⁆ * a⁻¹ ∈ ⁅P, Subgroup.zpowers z⁆
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp ha p).1 hp)
        (zpow_mem (Subgroup.mem_zpowers z) n)
    intro k hk
    exact hle hk
  have hc'z : c⁻¹ * z = z * c⁻¹ := by
    calc c⁻¹ * z = c⁻¹ * (z * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * z) * c⁻¹ := by rw [hzc]
      _ = z * c⁻¹ := by group
  have hcK : ∀ k ∈ ⁅P, Subgroup.zpowers z⁆, c * k * c⁻¹ ∈ ⁅P, Subgroup.zpowers z⁆ :=
    key c hcP hzc.symm
  have hcK' : ∀ k ∈ ⁅P, Subgroup.zpowers z⁆, c⁻¹ * k * c ∈ ⁅P, Subgroup.zpowers z⁆ := by
    intro k hk
    simpa using key c⁻¹ (inv_mem hcP) hc'z k hk
  let ψ : MulAut ↥⁅P, Subgroup.zpowers z⁆ :=
    { toFun := fun x => ⟨c * x * c⁻¹, hcK x x.2⟩
      invFun := fun x => ⟨c⁻¹ * x * c, hcK' x x.2⟩
      left_inv := fun x => Subtype.ext (by show c⁻¹ * (c * (x : Γ) * c⁻¹) * c = x; group)
      right_inv := fun x => Subtype.ext (by show c * (c⁻¹ * (x : Γ) * c) * c⁻¹ = x; group)
      map_mul' := fun x y => Subtype.ext (by
        show c * ((x : Γ) * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹); group) }
  have hψ3 : ψ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
    apply Subtype.ext
    show c * (c * (c * (x : Γ) * c⁻¹) * c⁻¹) * c⁻¹ = x
    have hc3' : c * (c * c) = 1 := by rw [← pow_three]; exact hc3
    calc c * (c * (c * (x : Γ) * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * x * (c * (c * c))⁻¹ := by
          group
      _ = x := by rw [hc3', inv_one, mul_one, one_mul]
  have hord : orderOf ψ ∣ 3 := orderOf_dvd_of_pow_eq_one hψ3
  have hcard : orderOf ψ ∣ Nat.totient (Nat.card ↥⁅P, Subgroup.zpowers z⁆) := by
    rw [← IsCyclic.card_mulAut ↥⁅P, Subgroup.zpowers z⁆]
    exact orderOf_dvd_natCard ψ
  have hψ1 : ψ = 1 := by
    have h1 : orderOf ψ ∣ Nat.gcd 3 (Nat.totient (Nat.card ↥⁅P, Subgroup.zpowers z⁆)) :=
      Nat.dvd_gcd hord hcard
    rw [Nat.Coprime.gcd_eq_one h3cop] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hcent : ∀ k ∈ ⁅P, Subgroup.zpowers z⁆, c * k = k * c := by
    intro k hk
    have h2 : ((ψ ⟨k, hk⟩ : ↥⁅P, Subgroup.zpowers z⁆) : Γ) =
        ((1 : MulAut ↥⁅P, Subgroup.zpowers z⁆) ⟨k, hk⟩ : Γ) := by rw [hψ1]
    rw [MulAut.one_apply] at h2
    have h' : c * k * c⁻¹ = k := h2
    calc c * k = c * k * c⁻¹ * c := by group
      _ = k * c := by rw [h']
  have hA : ⁅⁅P, Subgroup.zpowers z⁆, Subgroup.zpowers c⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hck : Commute c k := hcent k hk
    exact (hck.zpow_left n).eq
  have hB : ⁅⁅Subgroup.zpowers z, Subgroup.zpowers c⁆, P⁆ = ⊥ := by
    have hcomm : ⁅Subgroup.zpowers z, Subgroup.zpowers c⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hcz : Commute c z := hzc.symm
      exact (hcz.zpow_left n).eq
    rw [hcomm, Subgroup.commutator_bot_left]
  have hC : ⁅⁅Subgroup.zpowers c, P⁆, Subgroup.zpowers z⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hA hB
  have hPK : ⁅P, Subgroup.zpowers z⁆ = ⊥ := by
    have e : ⁅Subgroup.zpowers c, P⁆ = P := by rw [Subgroup.commutator_comm, hperf]
    rw [e] at hC
    exact hC
  obtain ⟨p, hp, hzp⟩ := hz
  have hmem : ⁅p, z⁆ ∈ ⁅P, Subgroup.zpowers z⁆ :=
    Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers z)
  rw [hPK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hzp hmem.symm

theorem not_isCyclic_commutator_q8 {P Q : Subgroup Γ} {z : Γ} (hP : IsPGroup 5 P)
    (hz2 : z * z = 1) (hQP : Q ≤ Subgroup.normalizer (P : Set Γ))
    (hzP : z ∈ Subgroup.normalizer (P : Set Γ)) (hzQ : ∀ q ∈ Q, q * z = z * q)
    (hzcomm : z ∈ ⁅Q, Q⁆) (hz : ∃ p ∈ P, z * p ≠ p * z) :
    ¬ IsCyclic ↥⁅P, Subgroup.zpowers z⁆ := by
  intro hK
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a₀, ha₀⟩ := IsPGroup.iff_card.mp hP
  have keyQ : ∀ a : Γ, a ∈ Q → ∀ k ∈ ⁅P, Subgroup.zpowers z⁆,
      a * k * a⁻¹ ∈ ⁅P, Subgroup.zpowers z⁆ := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (P : Set Γ) := hQP ha
    have haz : a * z = z * a := hzQ a ha
    have hazn : ∀ n : ℤ, a * z ^ n * a⁻¹ = z ^ n := by
      intro n
      have h1 : a * z * a⁻¹ = z := by rw [haz, mul_assoc, mul_inv_cancel, mul_one]
      rw [← conj_zpow, h1]
    have hle : ⁅P, Subgroup.zpowers z⁆ ≤
        (⁅P, Subgroup.zpowers z⁆).comap (MulEquiv.toMonoidHom (MulAut.conj a)) := by
      rw [Subgroup.commutator_le]
      intro p hp w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [Subgroup.mem_comap]
      have e : a * ⁅p, z ^ n⁆ * a⁻¹ = ⁅a * p * a⁻¹, z ^ n⁆ := by
        have hX := hazn n
        calc a * ⁅p, z ^ n⁆ * a⁻¹
            = (a * p * a⁻¹) * (a * z ^ n * a⁻¹) * (a * p * a⁻¹)⁻¹ * (a * z ^ n * a⁻¹)⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = ⁅a * p * a⁻¹, z ^ n⁆ := by rw [hX, commutatorElement_def]
      show a * ⁅p, z ^ n⁆ * a⁻¹ ∈ ⁅P, Subgroup.zpowers z⁆
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp haN p).1 hp)
        (zpow_mem (Subgroup.mem_zpowers z) n)
    intro k hk
    exact hle hk
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥⁅P, Subgroup.zpowers z⁆)
  have hgen : ∀ x ∈ ⁅P, Subgroup.zpowers z⁆, ∃ n : ℤ, (g : Γ) ^ n = x := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩
  have hcommute : ∀ a ∈ Q, ∀ b ∈ Q, ∀ k ∈ ⁅P, Subgroup.zpowers z⁆,
      a * (b * k * b⁻¹) * a⁻¹ = b * (a * k * a⁻¹) * b⁻¹ := by
    intro a ha b hb k hk
    obtain ⟨α, hα⟩ := hgen _ (keyQ a ha _ g.2)
    obtain ⟨β, hβ⟩ := hgen _ (keyQ b hb _ g.2)
    obtain ⟨n, hn⟩ := hgen k hk
    have e1 : ∀ m : ℤ, b * (g : Γ) ^ m * b⁻¹ = (g : Γ) ^ (β * m) := by
      intro m
      rw [← conj_zpow, ← hβ, ← zpow_mul]
    have e2 : ∀ m : ℤ, a * (g : Γ) ^ m * a⁻¹ = (g : Γ) ^ (α * m) := by
      intro m
      rw [← conj_zpow, ← hα, ← zpow_mul]
    rw [← hn]
    simp only [e1, e2]
    congr 1
    ring
  have hcentral : ∀ a ∈ Q, ∀ b ∈ Q, ∀ k ∈ ⁅P, Subgroup.zpowers z⁆,
      ⁅a, b⁆ * k = k * ⁅a, b⁆ := by
    intro a ha b hb k hk
    have hu : a⁻¹ * (b⁻¹ * k * b) * a ∈ ⁅P, Subgroup.zpowers z⁆ := by
      have h1 := keyQ b⁻¹ (inv_mem hb) k hk
      have h2 := keyQ a⁻¹ (inv_mem ha) _ h1
      simpa using h2
    have E := hcommute a ha b hb _ hu
    have E1 : a * (b * (a⁻¹ * (b⁻¹ * k * b) * a) * b⁻¹) * a⁻¹ = ⁅a, b⁆ * k * ⁅a, b⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    have E2 : b * (a * (a⁻¹ * (b⁻¹ * k * b) * a) * a⁻¹) * b⁻¹ = k := by group
    rw [E1, E2] at E
    calc ⁅a, b⁆ * k = ⁅a, b⁆ * k * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by group
      _ = k * ⁅a, b⁆ := by rw [E]
  have hQQ : ⁅Q, Q⁆ ≤ Subgroup.centralizer ((⁅P, Subgroup.zpowers z⁆ : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcentral a ha b hb k hk).symm
  have hzK : ∀ k ∈ ⁅P, Subgroup.zpowers z⁆, k * z = z * k :=
    Subgroup.mem_centralizer_iff.mp (hQQ hzcomm)
  have hKz : ⁅⁅P, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hzk : Commute z k := (hzK k hk).symm
    exact (hzk.zpow_left n).eq
  have hzP' : Subgroup.zpowers z ≤ Subgroup.normalizer (P : Set Γ) := Subgroup.zpowers_le.mpr hzP
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers z)) (Nat.card P) := by
    rw [Nat.card_zpowers]
    have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
    have hcopP : Nat.Coprime 2 (Nat.card P) := by
      rw [ha₀]
      exact Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.Coprime.coprime_dvd_left h2 hcopP
  have hcc := CFSG.HardMathSupport.Solomon.Coordinator.coprime_commutator_commutator_eq' hzP' hcop
  have hPK : ⁅P, Subgroup.zpowers z⁆ = ⊥ := hcc.symm.trans hKz
  obtain ⟨p, hp, hzp⟩ := hz
  have hmem : ⁅p, z⁆ ∈ ⁅P, Subgroup.zpowers z⁆ :=
    Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers z)
  rw [hPK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hzp hmem.symm

theorem inf_centralizer_eq_bot_of_O2 {Y : Type} [Group Y] [Finite Y] {Γ P S : Subgroup Y}
    (hP : IsPGroup 5 P) (hS : IsPGroup 2 S) (hPΓ : P ≤ Γ) (hSΓ : S ≤ Γ) (hΓ : P ⊔ S = Γ)
    (hn : Γ ≤ Subgroup.normalizer (P : Set Y))
    (hO2 : ∀ N : Subgroup Y, N ≤ Γ → Γ ≤ Subgroup.normalizer (N : Set Y) → IsPGroup 2 N → N = ⊥) :
    ∀ s ∈ S, (∀ p ∈ P, s * p = p * s) → s = 1 := by
  intro s hs hsc
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSN : S ≤ Subgroup.normalizer (P : Set Y) := hSΓ.trans hn
  have hdecomp : ∀ γ ∈ Γ, ∃ p ∈ P, ∃ t ∈ S, p * t = γ := by
    intro γ hγ
    have hmem : γ ∈ (P : Set Y) * (S : Set Y) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left P S hSN, hΓ]
      exact hγ
    obtain ⟨p, hp, t, ht, hpt⟩ := Set.mem_mul.mp hmem
    exact ⟨p, hp, t, ht, hpt⟩
  have hpow2 : ∀ γ ∈ Γ, ∃ k : ℕ, γ ^ (2 ^ k) ∈ P := by
    intro γ hγ
    obtain ⟨p, hp, t, ht, rfl⟩ := hdecomp γ hγ
    obtain ⟨k, hk⟩ := hS ⟨t, ht⟩
    have hk' : t ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, ?_⟩
    have main : ∀ n : ℕ, ∃ q ∈ P, (p * t) ^ n = q * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, P.one_mem, by simp⟩
      | succ m ih =>
        obtain ⟨q, hq, hqe⟩ := ih
        have htmΓ : t ^ m ∈ Γ := hSΓ (pow_mem ht m)
        have hconj : t ^ m * p * (t ^ m)⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hn htmΓ) p).1 hp
        refine ⟨q * (t ^ m * p * (t ^ m)⁻¹), P.mul_mem hq hconj, ?_⟩
        simp only [pow_succ]
        rw [hqe]
        group
    obtain ⟨q, hq, hqe⟩ := main (2 ^ k)
    rw [hqe, hk', mul_one]
    exact hq
  obtain ⟨C, hC⟩ : ∃ C : Subgroup Y, C = Γ ⊓ Subgroup.centralizer (P : Set Y) := ⟨_, rfl⟩
  have hmemC : ∀ x : Y, x ∈ C ↔ x ∈ Γ ∧ ∀ p ∈ P, p * x = x * p := by
    intro x
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hCΓ : C ≤ Γ := fun x hx => ((hmemC x).1 hx).1
  obtain ⟨H, hH⟩ : ∃ H : Subgroup Y, H = P ⊓ C := ⟨_, rfl⟩
  have hmemH : ∀ x : Y, x ∈ H ↔ x ∈ P ∧ x ∈ C := by
    intro x
    rw [hH, Subgroup.mem_inf]
  have hCconj : ∀ γ ∈ Γ, ∀ x ∈ C, γ * x * γ⁻¹ ∈ C := by
    intro γ hγ x hx
    obtain ⟨hxΓ, hxc⟩ := (hmemC x).1 hx
    rw [hmemC]
    refine ⟨mul_mem (mul_mem hγ hxΓ) (inv_mem hγ), ?_⟩
    intro p hp
    have hp' : γ⁻¹ * p * γ ∈ P := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hn (inv_mem hγ)) p).1 hp
      rwa [inv_inv] at h1
    have h' := hxc (γ⁻¹ * p * γ) hp'
    calc p * (γ * x * γ⁻¹) = γ * (γ⁻¹ * p * γ * x) * γ⁻¹ := by group
      _ = γ * (x * (γ⁻¹ * p * γ)) * γ⁻¹ := by rw [h']
      _ = γ * x * γ⁻¹ * p := by group
  haveI hNnormal : (H.subgroupOf C).Normal := by
    refine ⟨fun n hn0 g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn0 ⊢
    have hnP : ((n : C) : Y) ∈ P := ((hmemH _).1 hn0).1
    have hc : ((n : C) : Y) * ((g : C) : Y) = ((g : C) : Y) * ((n : C) : Y) :=
      ((hmemC (g : Y)).1 g.2).2 _ hnP
    have hval : ((g * n * g⁻¹ : C) : Y) = ((n : C) : Y) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hc]
      group
    rw [hval]
    exact hn0
  have hH5 : IsPGroup 5 (H.subgroupOf C) := by
    intro x
    have hxP : ((x : C) : Y) ∈ P := ((hmemH _).1 (Subgroup.mem_subgroupOf.mp x.2)).1
    obtain ⟨k, hk⟩ := hP ⟨((x : C) : Y), hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hH5
  have hQ2 : IsPGroup 2 (↥C ⧸ H.subgroupOf C) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hpow2 (c : Y) (hCΓ c.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hmemH]
    refine ⟨?_, (c ^ 2 ^ k).2⟩
    simpa using hk
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hQ2
  have hcop : Nat.Coprime (Nat.card (H.subgroupOf C)) (H.subgroupOf C).index := by
    rw [Subgroup.index_eq_card, ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨T', hT'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  obtain ⟨T, hT⟩ : ∃ T : Subgroup Y, T = T'.map C.subtype := ⟨_, rfl⟩
  have hdecompC : ∀ x : Y, x ∈ C → ∃ h ∈ H, ∃ t ∈ T, h * t = x := by
    intro x hx
    obtain ⟨⟨⟨n, hn0⟩, ⟨t, ht⟩⟩, hnt, -⟩ := (Subgroup.isComplement_iff_existsUnique.mp hT') ⟨x, hx⟩
    refine ⟨(n : Y), Subgroup.mem_subgroupOf.mp hn0, (t : Y), ?_, ?_⟩
    · rw [hT]
      exact Subgroup.mem_map_of_mem C.subtype ht
    · have := congrArg Subtype.val hnt
      simpa using this
  have hHT : ∀ x : Y, x ∈ H → x ∈ T → x = 1 := by
    intro x hxH hxT
    have hxC : x ∈ C := ((hmemH x).1 hxH).2
    rw [hT, Subgroup.mem_map] at hxT
    obtain ⟨t', ht', hte⟩ := hxT
    have hdisj := hT'.disjoint
    rw [disjoint_iff] at hdisj
    have hmem : (⟨x, hxC⟩ : C) ∈ H.subgroupOf C ⊓ T' := by
      refine ⟨Subgroup.mem_subgroupOf.mpr hxH, ?_⟩
      have heq : (⟨x, hxC⟩ : C) = t' := Subtype.ext hte.symm
      rw [heq]
      exact ht'
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hTC : T ≤ C := by
    intro y hy
    rw [hT, Subgroup.mem_map] at hy
    obtain ⟨t', -, rfl⟩ := hy
    exact t'.2
  have hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := hpow2 t (hCΓ (hTC ht))
    refine ⟨k, hHT _ ?_ (pow_mem ht _)⟩
    rw [hmemH]
    exact ⟨hk, pow_mem (hTC ht) _⟩
  have hF6 : ∀ x : Y, x ∈ C → (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ T := by
    intro x hxC hx2
    obtain ⟨k, hk⟩ := hx2
    obtain ⟨h, hhH, t, htT, hht⟩ := hdecompC x hxC
    have hhP : h ∈ P := ((hmemH h).1 hhH).1
    have hcomm : Commute h t := ((hmemC t).1 (hTC htT)).2 h hhP
    have hxk : h ^ (2 ^ k) * t ^ (2 ^ k) = 1 := by
      rw [← hcomm.mul_pow, hht]
      exact hk
    have hh2 : h ^ (2 ^ k) = 1 := by
      apply hHT _ (pow_mem hhH _)
      rw [eq_inv_of_mul_eq_one_left hxk]
      exact inv_mem (pow_mem htT _)
    obtain ⟨j, hj⟩ := hP ⟨h, hhP⟩
    have hj' : h ^ (5 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hord1 : orderOf h ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hh2
    have hord2 : orderOf h ∣ 5 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have hcop25 : Nat.Coprime (2 ^ k) (5 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
    have hh1 : h = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop25 hord1 hord2)
    rw [← hht, hh1, one_mul]
    exact htT
  have hTΓ : T ≤ Γ := hTC.trans hCΓ
  have hconj2 : ∀ γ ∈ Γ, ∀ t ∈ T, γ * t * γ⁻¹ ∈ T := by
    intro γ hγ t ht
    obtain ⟨k, hk⟩ := hT2 t ht
    apply hF6 _ (hCconj γ hγ t (hTC ht))
    exact ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hTnorm : Γ ≤ Subgroup.normalizer (T : Set Y) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact hconj2 γ hγ t ht
    · intro ht
      have h' := hconj2 γ⁻¹ (inv_mem hγ) _ ht
      have e : γ⁻¹ * (γ * t * γ⁻¹) * γ⁻¹⁻¹ = t := by group
      rwa [e] at h'
  have hT2grp : IsPGroup 2 T := by
    intro t
    obtain ⟨k, hk⟩ := hT2 t.1 t.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hTbot : T = ⊥ := hO2 T hTΓ hTnorm hT2grp
  have hsC : s ∈ C := (hmemC s).2 ⟨hSΓ hs, fun p hp => (hsc p hp).symm⟩
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hsT : s ∈ T := hF6 s hsC ⟨k, hk'⟩
  rw [hTbot, Subgroup.mem_bot] at hsT
  exact hsT

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
