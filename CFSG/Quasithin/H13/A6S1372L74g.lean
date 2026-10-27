module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S1372L19b
public import CFSG.Quasithin.H13.A6S1372L74e
public import CFSG.Quasithin.H13.A6Set14
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {N Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ Q) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) : x ∈ N := by
  rw [sup_comm] at hx
  obtain ⟨q, hq, n, hn, rfl⟩ := (A6L19.mem_sup_iff hQN).1 hx
  have hn' : q * n * q⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hQN hq) n).mp hn
  have e : q * n = (q * n * q⁻¹) * q := by group
  rw [e] at hxm ⊢
  obtain ⟨a, ha⟩ := hQ ⟨q, hq⟩
  have hqa : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨n', hn'', he⟩ := U3.pow_mem_mul_of_normalizes' hn' (hQN hq) (2 ^ a)
  rw [hqa, mul_one] at he
  have hcop : Nat.Coprime (2 ^ a) (orderOf (q * n * q⁻¹ * q)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxm)
      ((Odd.coprime_two_left hm).pow_left a)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk, he]
  exact N.pow_mem hn'' k

omit [Finite G] in
theorem inf_le_pCoreOf {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) : K ⊓ Q ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun k hk => mem_normalizer_inf_of (Subgroup.le_normalizer hk) (hKQ hk)) (hQ.to_le inf_le_right)

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Setting

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz)
include hNS h13315 h1356two hH

omit hNS h13315 h1356two hH in
theorem pCase {H : Subgroup G} {C : Subgroup G} (hCH : C ≤ H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K₁ : Subgroup G} (hQK₁ : pCoreOf 2 H ≤ K₁) (hK₁C : K₁ ≤ C)
    (hHK₁ : H ≤ Subgroup.normalizer (K₁ : Set G)) (hK₁Q : ¬ K₁ ≤ pCoreOf 2 H)
    (hexp : ∀ k ∈ K₁, k ^ p ∈ pCoreOf 2 H)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₁, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H)
    (hmin : ∀ N : Subgroup G, pCoreOf 2 H ≤ N → N ≤ K₁ →
      H ≤ Subgroup.normalizer (N : Set G) → N = pCoreOf 2 H ∨ N = K₁) :
    oTwoRes K₁ ≤ H ∧ H ≤ Subgroup.normalizer (oTwoRes K₁ : Set G) ∧
      oTwoRes (oTwoRes K₁) = oTwoRes K₁ ∧ oTwoRes K₁ ≤ C ∧ ¬ oTwoRes K₁ ≤ pCoreOf 2 H ∧
      (∀ k ∈ oTwoRes K₁, k ^ p ∈ pCoreOf 2 (oTwoRes K₁)) ∧
      (∀ a ∈ oTwoRes K₁, ∀ b ∈ oTwoRes K₁, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (oTwoRes K₁)) ∧
      ∀ N : Subgroup G, pCoreOf 2 (oTwoRes K₁) ≤ N → N ≤ oTwoRes K₁ →
        H ≤ Subgroup.normalizer (N : Set G) → N = pCoreOf 2 (oTwoRes K₁) ∨ N = oTwoRes K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoRes K₁ with hKdef
  have hKK₁ : K ≤ K₁ := oTwoRes_le _
  have hKH : K ≤ H := (hKK₁.trans hK₁C).trans hCH
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hHK₁
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hKQ : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K :=
    A6L74.inf_le_pCoreOf hQ2 (hKH.trans (le_normalizer_pCoreOf 2 H))
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  refine ⟨hKH, hHK, S14.oTwoRes_idem K₁, hKK₁.trans hK₁C, ?_, fun k hk => ?_,
    fun a ha b hb => ?_, fun N hON hNK hHN => ?_⟩
  ·
    intro hle
    apply hK₁Q
    intro k hk
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
    have h1 : k ^ 2 ^ a ∈ pCoreOf 2 H := hle (Subgroup.subset_closure ⟨K₁.pow_mem hk _, m, hm, by
      rw [← pow_mul, ← hn, pow_orderOf_eq_one]⟩)
    have h2 := hexp k hk
    have hcop : Nat.Coprime (2 ^ a) p :=
      Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : k = (k ^ 2 ^ a) ^ u * (k ^ p) ^ v := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
        mul_comm ((2 ^ a : ℕ) : ℤ) u, mul_comm (p : ℤ) v, huv, zpow_one]
    rw [e]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).zpow_mem h1 u) ((pCoreOf 2 H).zpow_mem h2 v)
  · exact hKQ ⟨K.pow_mem hk p, hexp k (hKK₁ hk)⟩
  · refine hKQ ⟨K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb),
      hcomm a (hKK₁ ha) b (hKK₁ hb)⟩
  ·
    have hNH : N ≤ H := hNK.trans hKH
    have hHNQ : H ≤ Subgroup.normalizer ((N ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
      intro h hh
      refine A6L19.mem_normalizer_of_conj fun y hy => ?_
      obtain ⟨n, hn, q, hq, rfl⟩ :=
        (A6L19.mem_sup_iff (hNH.trans (le_normalizer_pCoreOf 2 H))).1 hy
      have e : h * (n * q) * h⁻¹ = (h * n * h⁻¹) * (h * q * h⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hHN hh) n).mp hn))
        (Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq))
    rcases hmin (N ⊔ pCoreOf 2 H) le_sup_right (sup_le (hNK.trans hKK₁) hQK₁) hHNQ with h | h
    · left
      refine le_antisymm (fun x hx => hKQ ⟨hNK hx, ?_⟩) hON
      rw [← h]
      exact Subgroup.mem_sup_left hx
    · right
      refine le_antisymm hNK ?_
      rw [hKdef, oTwoRes, Subgroup.closure_le]
      rintro x ⟨hx, m, hm, hxm⟩
      rw [← h] at hx
      exact A6L74.mem_of_odd_of_mem_sup hQ2 ((pCoreOf_le 2 H).trans hHN) hx hm hxm

omit hNS h13315 h1356two hH in
theorem inf_centralizer_U0_le_of_minimal {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : ∀ N : Subgroup G, pCoreOf 2 K ≤ N → N ≤ K → H ≤ Subgroup.normalizer (N : Set G) →
      N = pCoreOf 2 K ∨ N = K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hQU : pCoreOf 2 H ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := fun q hq => by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp hu.2 q hq).symm
  have hHN : H ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_inf_of (hHK hh)
      (InternalSec.le_normalizer_centralizer S.le_normalizer_U0 hh)
  rcases hmin _ (le_inf (pCoreOf_le 2 K) (hOQ.trans hQU)) inf_le_left hHN with h | h
  · exact h.le
  · exact absurd (h ▸ inf_le_right) hKU

omit hNS h13315 h1356two in
theorem comm_L1_mem_of_card_three {K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3) :
    ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K := by
  have hL1N : S.L1 ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hH.1.1).trans hHK
  have hker : ∀ l (hl : l ∈ Subgroup.normalizer (K : Set G)), l ∈ S.L1 →
      actModO2_614 K ⟨l, hl⟩ = 1 := by
    intro l hl hlL
    have hle : S.L1 ≤ ((actModO2_614 K).ker).map (Subgroup.normalizer (K : Set G)).subtype := by
      show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
      rw [oTwoRes, Subgroup.closure_le]
      rintro x ⟨hx, m, hm, hxm⟩
      have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
      refine ⟨⟨x, hL1N hxL1⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      have hpow : (actModO2_614 K ⟨x, hL1N hxL1⟩) ^ m = 1 := by
        rw [← map_pow]
        have : (⟨x, hL1N hxL1⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ m = 1 :=
          Subtype.ext (by simpa using hxm)
        rw [this, map_one]
      rcases CFSG.GorensteinWalter.mulAut_eq_one_or_apply_eq_inv_of_card_eq_three h3
        (actModO2_614 K ⟨x, hL1N hxL1⟩) with h1 | h1
      · exact h1
      · exfalso
        have hinv : ∀ n : ℕ, ∀ y : ModO2 K,
            ((actModO2_614 K ⟨x, hL1N hxL1⟩) ^ (2 * n + 1)) y = y⁻¹ := by
          intro n
          induction n with
          | zero => intro y; simp [h1]
          | succ n ih =>
            intro y
            rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, MulAut.mul_apply, sq,
              MulAut.mul_apply, h1, h1, inv_inv, ih]
        obtain ⟨j, rfl⟩ := hm
        obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ModO2 K) 3 (by rw [h3])
        have h2 := hinv j y
        rw [hpow, MulAut.one_apply] at h2
        have h3y : y * y = 1 := by
          calc y * y = y * y⁻¹ := by rw [← h2]
            _ = 1 := mul_inv_cancel y
        have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h3y)
        rw [hy] at this
        omega
    obtain ⟨n, hn, hnl⟩ := hle hlL
    have e : n = ⟨l, hl⟩ := Subtype.ext hnl
    rw [e] at hn
    exact hn
  intro k hk l hlL
  have h1 := hker l (hL1N hlL) hlL
  have h2 := congrArg (fun σ : MulAut (ModO2 K) => σ ((⟨k, hk⟩ : ↥K) : ModO2 K)) h1
  simp only [actModO2_614_mk, MulAut.one_apply] at h2
  rw [QuotientGroup.eq] at h2
  have h3' : ((⟨l * k * l⁻¹, (Subgroup.mem_normalizer_iff.mp (hL1N hlL) k).mp hk⟩ : ↥K)⁻¹ *
      ⟨k, hk⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := h2
  have h4 := (A6L74.mem_pCoreOf_iff (H := K) _).2 h3'
  have e : k * l * k⁻¹ * l⁻¹ = k * ((((⟨l * k * l⁻¹, (Subgroup.mem_normalizer_iff.mp
      (hL1N hlL) k).mp hk⟩ : ↥K)⁻¹ * ⟨k, hk⟩ : ↥K) : G)) * k⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  have hOn : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  exact (Subgroup.mem_normalizer_iff.mp (hOn hk) _).mp h4

end Setting

end Setting4

end CFSG.Quasithin.H13.A6
