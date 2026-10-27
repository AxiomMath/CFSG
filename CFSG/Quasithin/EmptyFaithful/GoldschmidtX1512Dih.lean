module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace X1512

variable {K : Type*} [Group K]

theorem eq_one_of_pow_two_pow_of_pow_odd {w : K} {k m : ℕ} (hm : Odd m) (h1 : w ^ 2 ^ k = 1)
    (h2 : w ^ m = 1) : w = 1 := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h4 : orderOf w = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.mp h4

structure DihData (y : K) (A A₀ : Subgroup K) (a₁ : K) : Prop where
  odd : Odd (orderOf y)
  ne_one : y ≠ 1
  elem : IsElemAbelian 2 A
  le : A₀ ≤ A
  mem : a₁ ∈ A
  not_mem : a₁ ∉ A₀
  cover : ∀ a ∈ A, a ∈ A₀ ∨ a₁⁻¹ * a ∈ A₀
  cent : ∀ a ∈ A₀, a * y * a⁻¹ = y
  inv : a₁ * y * a₁⁻¹ = y⁻¹

namespace DihData

variable {y : K} {A A₀ : Subgroup K} {a₁ : K} (h : DihData y A A₀ a₁)

include h

theorem conj_eq_inv {a : K} (ha : a ∈ A) (ha0 : a ∉ A₀) : a * y * a⁻¹ = y⁻¹ := by
  rcases h.cover a ha with h0 | h1
  · exact absurd h0 ha0
  · obtain ⟨b, hb, rfl⟩ : ∃ b ∈ A₀, a = a₁ * b := ⟨a₁⁻¹ * a, h1, by group⟩
    calc a₁ * b * y * (a₁ * b)⁻¹ = a₁ * (b * y * b⁻¹) * a₁⁻¹ := by group
      _ = a₁ * y * a₁⁻¹ := by rw [h.cent b hb]
      _ = y⁻¹ := h.inv

theorem normalizes {a : K} (ha : a ∈ A) (i : ℤ) : a * y ^ i * a⁻¹ ∈ Subgroup.zpowers y := by
  by_cases ha0 : a ∈ A₀
  · rw [← conj_zpow, h.cent a ha0]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i
  · rw [← conj_zpow, h.conj_eq_inv ha ha0]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) i

theorem exists_mul {z : K} (hz : z ∈ A ⊔ Subgroup.zpowers y) :
    ∃ a ∈ A, ∃ i : ℤ, z = a * y ^ i := by
  rw [Subgroup.sup_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, by simp⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨1, A.one_mem, i, by simp⟩
  | one => exact ⟨1, A.one_mem, 0, by simp⟩
  | mul x z _ _ ihx ihz =>
    obtain ⟨a, ha, i, rfl⟩ := ihx
    obtain ⟨b, hb, j, rfl⟩ := ihz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.normalizes (A.inv_mem hb) i)
    refine ⟨a * b, A.mul_mem ha hb, k + j, ?_⟩
    have e : b⁻¹ * y ^ i * b = y ^ k := by simpa using hk.symm
    calc a * y ^ i * (b * y ^ j) = a * b * (b⁻¹ * y ^ i * b) * y ^ j := by group
      _ = a * b * y ^ (k + j) := by rw [e, zpow_add]; group
  | inv x _ ih =>
    obtain ⟨a, ha, i, rfl⟩ := ih
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.normalizes ha (-i))
    refine ⟨a⁻¹, A.inv_mem ha, k, ?_⟩
    have e : a * y ^ (-i) * a⁻¹ = y ^ k := hk.symm
    calc (a * y ^ i)⁻¹ = a⁻¹ * (a * y ^ (-i) * a⁻¹) := by rw [zpow_neg]; group
      _ = a⁻¹ * y ^ k := by rw [e]

theorem sq_eq_one {a : K} (ha : a ∈ A) : a * a = 1 := by
  simpa [pow_two] using h.elem.2 a ha

theorem comm {a b : K} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  B2F.isElemAbelian_comm h.elem ha hb

omit h in
theorem pow_orderOf_of_mem {t : K} (ht : t ∈ Subgroup.zpowers y) : t ^ orderOf y = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

variable [Finite K]

theorem eq_one_of_mem_inf {w : K} (hw : w ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y))
    (hwy : w ∈ Subgroup.zpowers y) : w = 1 := by
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (A ⊔ Subgroup.zpowers y)) ⟨w, hw⟩
  have h1 : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact eq_one_of_pow_two_pow_of_pow_odd h.odd h1 (pow_orderOf_of_mem hwy)

omit [Finite K] in
theorem le_pCoreOf : A₀ ≤ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := by
  refine le_pCoreOf_of_le_normalizer 2 (h.le.trans le_sup_left) ?_
    (B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono h.le h.elem))
  have hA : A ≤ Subgroup.centralizer (A₀ : Set K) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.comm (h.le hb) ha
  have hy : Subgroup.zpowers y ≤ Subgroup.centralizer (A₀ : Set K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro b hb
    have e := h.cent b hb
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [e]
  exact (sup_le hA hy).trans (Subgroup.centralizer_le_normalizer (A₀ : Set K))

theorem mem_of_mem_pCoreOf {a : K} (ha : a ∈ A) (haO : a ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y)) :
    a ∈ A₀ := by
  by_contra ha0
  have hnorm := le_normalizer_pCoreOf 2 (A ⊔ Subgroup.zpowers y)
  have hy : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rcases h.cover a ha with h0 | h1
  · exact ha0 h0
  have ha1 : a₁ ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := by
    have hb : a₁⁻¹ * a ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := h.le_pCoreOf h1
    have := (pCoreOf 2 (A ⊔ Subgroup.zpowers y)).mul_mem haO
      ((pCoreOf 2 (A ⊔ Subgroup.zpowers y)).inv_mem hb)
    simpa [mul_assoc] using this
  have hc : y * a₁ * y⁻¹ * a₁⁻¹ ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := by
    have h1' : y * a₁ * y⁻¹ ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hy) a₁).mp ha1
    exact (pCoreOf 2 (A ⊔ Subgroup.zpowers y)).mul_mem h1'
      ((pCoreOf 2 (A ⊔ Subgroup.zpowers y)).inv_mem ha1)
  have hyy : y * a₁ * y⁻¹ * a₁⁻¹ = y ^ 2 := by
    have : a₁ * y⁻¹ * a₁⁻¹ = y := by
      have := congrArg (fun t => t⁻¹) h.inv
      simpa [mul_assoc] using this
    calc y * a₁ * y⁻¹ * a₁⁻¹ = y * (a₁ * y⁻¹ * a₁⁻¹) := by group
      _ = y * y := by rw [this]
      _ = y ^ 2 := (pow_two y).symm
  rw [hyy] at hc
  have hy2 : y ^ 2 = 1 := h.eq_one_of_mem_inf hc (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2)
  exact h.ne_one (eq_one_of_pow_two_pow_of_pow_odd (k := 1) h.odd (by simpa using hy2)
    (pow_orderOf_eq_one y))

theorem pCoreOf_le_left {o : K} (ho : o ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y)) : o ∈ A := by
  have hnorm := le_normalizer_pCoreOf 2 (A ⊔ Subgroup.zpowers y)
  have hoX : o ∈ A ⊔ Subgroup.zpowers y := pCoreOf_le 2 _ ho
  have hy : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  obtain ⟨a, ha, i, rfl⟩ := h.exists_mul hoX
  have hcO : (a * y ^ i) * y * (a * y ^ i)⁻¹ * y⁻¹ ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm hy) _).mp
      ((pCoreOf 2 (A ⊔ Subgroup.zpowers y)).inv_mem ho)
    have e : (a * y ^ i) * y * (a * y ^ i)⁻¹ * y⁻¹ = (a * y ^ i) * (y * (a * y ^ i)⁻¹ * y⁻¹) := by
      group
    rw [e]
    exact (pCoreOf 2 (A ⊔ Subgroup.zpowers y)).mul_mem ho h1
  have hay : a * y * a⁻¹ ∈ Subgroup.zpowers y := by
    simpa using h.normalizes ha 1
  have hcZ : (a * y ^ i) * y * (a * y ^ i)⁻¹ * y⁻¹ ∈ Subgroup.zpowers y := by
    have e : (a * y ^ i) * y * (a * y ^ i)⁻¹ * y⁻¹ = (a * y * a⁻¹) * y⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hay (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  have hc1 := h.eq_one_of_mem_inf hcO hcZ
  have hay' : a * y * a⁻¹ = y := by
    have e : (a * y ^ i) * y * (a * y ^ i)⁻¹ * y⁻¹ = (a * y * a⁻¹) * y⁻¹ := by group
    rw [e] at hc1
    exact mul_inv_eq_one.mp hc1
  have hai : a * y ^ i = y ^ i * a := by
    have : a * y ^ i * a⁻¹ = y ^ i := by rw [← conj_zpow, hay']
    calc a * y ^ i = (a * y ^ i * a⁻¹) * a := by group
      _ = y ^ i * a := by rw [this]
  have hsq : (a * y ^ i) * (a * y ^ i) = y ^ i * y ^ i := by
    calc (a * y ^ i) * (a * y ^ i) = a * (y ^ i * a) * y ^ i := by group
      _ = a * (a * y ^ i) * y ^ i := by rw [← hai]
      _ = (a * a) * y ^ i * y ^ i := by group
      _ = y ^ i * y ^ i := by rw [h.sq_eq_one ha, one_mul]
  have hyiO : y ^ i * y ^ i ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := by
    rw [← hsq]
    exact (pCoreOf 2 (A ⊔ Subgroup.zpowers y)).mul_mem ho ho
  have hyiZ : y ^ i ∈ Subgroup.zpowers y := Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i
  have h2 : y ^ i * y ^ i = 1 :=
    h.eq_one_of_mem_inf hyiO (Subgroup.mul_mem _ hyiZ hyiZ)
  have h3 : y ^ i = 1 :=
    eq_one_of_pow_two_pow_of_pow_odd (k := 1) h.odd (by simpa [pow_two] using h2)
      (pow_orderOf_of_mem hyiZ)
  rw [h3, mul_one]
  exact ha

omit [Finite K] in
theorem exists_mul_mem_pCoreOf {N : Subgroup K} {a : K} (ha : a ∈ A) (haN : a ∈ N)
    (haO : a ∉ pCoreOf 2 (A ⊔ Subgroup.zpowers y)) (hyN : y * a * y⁻¹ ∈ N) :
    ∀ z ∈ A ⊔ Subgroup.zpowers y, ∃ n ∈ N, n⁻¹ * z ∈ pCoreOf 2 (A ⊔ Subgroup.zpowers y) := by
  have ha0 : a ∉ A₀ := fun h0 => haO (h.le_pCoreOf h0)
  have hinv := h.conj_eq_inv ha ha0
  have hy2 : y ^ 2 ∈ N := by
    have e : y * a * y⁻¹ * a⁻¹ = y ^ 2 := by
      have : a * y⁻¹ * a⁻¹ = y := by
        have := congrArg (fun t => t⁻¹) hinv
        simpa [mul_assoc] using this
      calc y * a * y⁻¹ * a⁻¹ = y * (a * y⁻¹ * a⁻¹) := by group
        _ = y * y := by rw [this]
        _ = y ^ 2 := (pow_two y).symm
    rw [← e]
    exact N.mul_mem hyN (N.inv_mem haN)
  have hyN' : y ∈ N := by
    obtain ⟨s, hs⟩ := h.odd
    have : y = (y ^ 2) ^ (s + 1) := by
      have h1 : y ^ (2 * s + 1) = 1 := hs ▸ pow_orderOf_eq_one y
      calc y = y ^ (2 * s + 1) * y := by rw [h1, one_mul]
        _ = (y ^ 2) ^ (s + 1) := by rw [← pow_mul, ← pow_succ]; ring_nf
    rw [this]
    exact N.pow_mem hy2 _
  have hyiN : ∀ i : ℤ, y ^ i ∈ N := fun i => N.zpow_mem hyN' i
  have hcommA0 : ∀ b ∈ A₀, ∀ i : ℤ, b * y ^ i = y ^ i * b := by
    intro b hb i
    have : b * y ^ i * b⁻¹ = y ^ i := by rw [← conj_zpow, h.cent b hb]
    calc b * y ^ i = (b * y ^ i * b⁻¹) * b := by group
      _ = y ^ i * b := by rw [this]
  intro z hz
  obtain ⟨a', ha', i, rfl⟩ := h.exists_mul hz
  rcases h.cover a' ha' with h0 | h1
  · refine ⟨y ^ i, hyiN i, ?_⟩
    have hcm := hcommA0 a' h0 i
    have : (y ^ i)⁻¹ * (a' * y ^ i) = a' := by rw [hcm]; group
    rw [this]
    exact h.le_pCoreOf h0
  · have hb : a⁻¹ * a' ∈ A₀ := by
      rcases h.cover a ha with h0 | h2
      · exact absurd h0 ha0
      · have := A₀.mul_mem (A₀.inv_mem h2) h1
        simpa [mul_assoc] using this
    refine ⟨a * y ^ i, N.mul_mem haN (hyiN i), ?_⟩
    have e : (a * y ^ i)⁻¹ * (a' * y ^ i) = (y ^ i)⁻¹ * (a⁻¹ * a') * y ^ i := by group
    have hcm := hcommA0 _ hb i
    have : (y ^ i)⁻¹ * (a⁻¹ * a') * y ^ i = a⁻¹ * a' := by
      calc (y ^ i)⁻¹ * (a⁻¹ * a') * y ^ i = (y ^ i)⁻¹ * ((a⁻¹ * a') * y ^ i) := by group
        _ = a⁻¹ * a' := by rw [hcm]; group
    rw [e, this]
    exact h.le_pCoreOf hb

end DihData

end X1512

end CFSG.Quasithin
