module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KStage
import all CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec21.Item2119End9ProofShare

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

variable {G : Type} [Group G] [Finite G]

theorem eq_of_index_three {P S Q : Subgroup G} (hSP : S ≤ P) (hQS : Q ≤ S) (hne : Q ≠ S)
    (hQ : Nat.card Q = 243) (hP : Nat.card P = 729) : S = P := by
  have h1 : Nat.card Q ∣ Nat.card S := Subgroup.card_dvd_of_le hQS
  have h2 : Nat.card S ∣ Nat.card P := Subgroup.card_dvd_of_le hSP
  have h3 : Nat.card Q < Nat.card S := Subgroup.card_lt_of_lt (lt_of_le_of_ne hQS hne)
  rw [hQ] at h1 h3
  rw [hP] at h2
  obtain ⟨k, hk⟩ := h1
  have hk3 : k ∣ 3 := by
    have : 243 * k ∣ 243 * 3 := by rw [← hk]; exact h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hk4 : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3
  have hS : Nat.card S = 729 := by
    interval_cases k <;> omega
  exact Subgroup.eq_of_le_of_card_ge hSP (by rw [hP, hS])

namespace LineSetup

variable {A Q D M Y : Subgroup G} {d a₀ a₁ f₀ f₁ e t₀ t x : G}
  (h : LineSetup A Q D M Y d a₀ a₁ f₀ f₁ e t₀ t x)

include h

theorem hP'NQ : Q ⊔ D ≤ NQ Q d := by
  intro p hp
  refine ⟨h.hT.hP'N hp, ?_⟩
  have hc : p ∈ Subgroup.centralizer ({d} : Set G) := by
    refine (sup_le (fun q hq => ?_) (fun u hu => ?_) :
      Q ⊔ D ≤ Subgroup.centralizer ({d} : Set G)) hp
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := h.hT.hdc q hq
      calc q * d = q * d * q⁻¹ * q := by group
        _ = d * q := by rw [this]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.hT.hDc u hu d h.hT.hdD
  apply mem_normalizer_zpowers_of_mem
  have := Subgroup.mem_centralizer_singleton_iff.mp hc
  have e1 : p * d * p⁻¹ = d := by rw [this]; group
  rw [e1]; exact Subgroup.mem_zpowers d

theorem Mg_cyc {p : G} (hp : p ∈ Q ⊔ D) :
    ∃ k : ℕ, Mg d a₀ a₁ f₀ f₁ p = (Mg d a₀ a₁ f₀ f₁ x) ^ k := by
  have hS := h.hS
  set X := Mg d a₀ a₁ f₀ f₁ x with hX
  have hX3 : X ^ 3 = 1 := by rw [pow_three']; exact h.xi_cube
  let S : Subgroup G :=
    { carrier := {p | p ∈ Q ⊔ D ∧ ∃ k : ℕ, Mg d a₀ a₁ f₀ f₁ p = X ^ k}
      mul_mem' := by
        rintro p p' ⟨hp, k, hk⟩ ⟨hp', k', hk'⟩
        refine ⟨(Q ⊔ D).mul_mem hp hp', k + k', ?_⟩
        rw [hS.Mg_mul (h.hP'NQ hp).1 (NQ_conj_d (h.hP'NQ hp)) (h.hP'NQ hp').1, hk, hk', pow_add]
      one_mem' := ⟨(Q ⊔ D).one_mem, 0, by rw [hS.Mg_one, pow_zero]⟩
      inv_mem' := by
        rintro p ⟨hp, k, hk⟩
        refine ⟨(Q ⊔ D).inv_mem hp, 2 * k, ?_⟩
        have e1 : Mg d a₀ a₁ f₀ f₁ p⁻¹ * Mg d a₀ a₁ f₀ f₁ p = 1 := by
          rw [← hS.Mg_mul (h.hP'NQ ((Q ⊔ D).inv_mem hp)).1
            (NQ_conj_d (h.hP'NQ ((Q ⊔ D).inv_mem hp))) (h.hP'NQ hp).1, inv_mul_cancel, hS.Mg_one]
        rw [hk] at e1
        have e2 : X ^ k * X ^ (2 * k) = 1 := by
          rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hX3, one_pow]
        calc Mg d a₀ a₁ f₀ f₁ p⁻¹ = Mg d a₀ a₁ f₀ f₁ p⁻¹ * (X ^ k * X ^ (2 * k)) := by
              rw [e2, mul_one]
          _ = (Mg d a₀ a₁ f₀ f₁ p⁻¹ * X ^ k) * X ^ (2 * k) := by rw [mul_assoc]
          _ = X ^ (2 * k) := by rw [e1, one_mul] }
  have hSle : S ≤ Q ⊔ D := fun p hp => hp.1
  have hQS : Q ≤ S := fun q hq => ⟨Subgroup.mem_sup_left hq, 0, by rw [hS.Mg_Q hq, pow_zero]⟩
  have hxS : x ∈ S := ⟨Subgroup.mem_sup_right h.hxD, 1, by rw [pow_one]⟩
  have hSeq : S = Q ⊔ D := eq_of_index_three hSle hQS (fun hQeq => h.hxQ (hQeq ▸ hxS))
    h.hT.hQ243 h.hT.card_QD.1
  have : p ∈ S := by rw [hSeq]; exact hp
  exact this.2


theorem Mg_pow {n : ℕ} : Mg d a₀ a₁ f₀ f₁ (x ^ n) = (Mg d a₀ a₁ f₀ f₁ x) ^ n :=
  map_pow h.hS.MgHom (⟨x, h.hxNQ⟩ : NQ Q d) n

theorem P_eq {P : Subgroup G} (hP : IsSylowOf 3 P Y) (hQP : Q ≤ P)
    (hD : D = CFSG.Open.thompsonSubgroup P) : P = Q ⊔ D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Q ⊔ D ≤ P := sup_le hQP (hD ▸ Item2119End8Proof.thompsonSubgroup_le P)
  exact h.hT.sylow_P'.eq_of_le hle hP.le hP.isPGroup

end LineSetup

theorem partner_sylow {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G}
    {Di Dj Mi Mj Yi Yj : Subgroup G} {ei ej t₀i t₀j ti tj xi xj : G}
    (hLi : LineSetup A Q Di Mi Yi d a₀ a₁ f₀ f₁ ei t₀i ti xi)
    (hLj : LineSetup A Q Dj Mj Yj d a₀ a₁ f₀ f₁ ej t₀j tj xj)
    {Pi Pj : Subgroup G} (hPi : IsSylowOf 3 Pi Yi) (hPj : IsSylowOf 3 Pj Yj)
    (hQPi : Q ≤ Pi) (hQPj : Q ≤ Pj) (hDi : Di = CFSG.Open.thompsonSubgroup Pi)
    (hDj : Dj = CFSG.Open.thompsonSubgroup Pj)
    (hKYj : ∀ κ ∈ NQ Q d, Mg d a₀ a₁ f₀ f₁ κ = 1 → ∀ y ∈ Yj, κ * y * κ⁻¹ ∈ Yj)
    (hcyc : SameCyc (Mg d a₀ a₁ f₀ f₁ xi) (Mg d a₀ a₁ f₀ f₁ xj)) :
    IsSylowOf 3 Pi Yj := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hLi.hS
  have hPieq := hLi.P_eq hPi hQPi hDi
  have hPjeq := hLj.P_eq hPj hQPj hDj
  have hXi3 : Mg d a₀ a₁ f₀ f₁ xi * Mg d a₀ a₁ f₀ f₁ xi * Mg d a₀ a₁ f₀ f₁ xi = 1 := hLi.xi_cube
  have hXj3 : Mg d a₀ a₁ f₀ f₁ xj * Mg d a₀ a₁ f₀ f₁ xj * Mg d a₀ a₁ f₀ f₁ xj = 1 := hLj.xi_cube
  have hPiN : Pi ≤ NQ Q d := hPieq ▸ hLi.hP'NQ
  have hPjN : Pj ≤ NQ Q d := hPjeq ▸ hLj.hP'NQ
  have hxiPi : ∀ n : ℕ, xi ^ n ∈ Pi := fun n => by
    rw [hPieq]; exact Subgroup.mem_sup_right (Subgroup.pow_mem _ hLi.hxD n)
  have hxjPj : ∀ n : ℕ, xj ^ n ∈ Pj := fun n => by
    rw [hPjeq]; exact Subgroup.mem_sup_right (Subgroup.pow_mem _ hLj.hxD n)
  have h1 : ∀ p ∈ Pj, ∃ p' ∈ Pi, Mg d a₀ a₁ f₀ f₁ p = Mg d a₀ a₁ f₀ f₁ p' := by
    intro p hp
    rw [hPjeq] at hp
    obtain ⟨k, hk⟩ := hLj.Mg_cyc hp
    rcases hcyc with hc | hc
    · refine ⟨xi ^ k, hxiPi k, ?_⟩
      rw [hk, hLi.Mg_pow, hc]
    · refine ⟨xi ^ (2 * k), hxiPi _, ?_⟩
      rw [hk, hLi.Mg_pow, hc, pow_mul, sq]
  have h2 : ∀ p' ∈ Pi, ∃ p ∈ Pj, Mg d a₀ a₁ f₀ f₁ p' = Mg d a₀ a₁ f₀ f₁ p := by
    intro p hp
    rw [hPieq] at hp
    obtain ⟨k, hk⟩ := hLi.Mg_cyc hp
    rcases hcyc with hc | hc
    · refine ⟨xj ^ k, hxjPj k, ?_⟩
      rw [hk, hLj.Mg_pow, hc]
    · refine ⟨xj ^ (2 * k), hxjPj _, ?_⟩
      have hX : Mg d a₀ a₁ f₀ f₁ xj * Mg d a₀ a₁ f₀ f₁ xj = Mg d a₀ a₁ f₀ f₁ xi := by
        rw [hc]
        calc Mg d a₀ a₁ f₀ f₁ xi * Mg d a₀ a₁ f₀ f₁ xi * (Mg d a₀ a₁ f₀ f₁ xi *
              Mg d a₀ a₁ f₀ f₁ xi)
            = (Mg d a₀ a₁ f₀ f₁ xi * Mg d a₀ a₁ f₀ f₁ xi * Mg d a₀ a₁ f₀ f₁ xi) *
              Mg d a₀ a₁ f₀ f₁ xi := by simp only [mul_assoc]
          _ = Mg d a₀ a₁ f₀ f₁ xi := by rw [hXi3, one_mul]
      rw [hk, hLj.Mg_pow, pow_mul, sq, hX]
  obtain ⟨κ, hκ, hκM, hκP⟩ := hS.sylow_conj_K hPjN hPiN hPj.isPGroup hPi.isPGroup hQPj hQPi h1 h2
  have hPiYj : Pi ≤ Yj := by
    intro y hy
    have h3 := (hκP y).mp hy
    have h4 := hKYj κ hκ hκM _ (hPj.le h3)
    have e : κ * (κ⁻¹ * y * κ) * κ⁻¹ = y := by group
    rwa [e] at h4
  have hcard : Nat.card Pi = 3 ^ (Nat.card Yj).factorization 3 := by
    rw [← hPj.card_eq, hPieq, hPjeq, hLi.hT.card_QD.1, hLj.hT.card_QD.1]
  exact isSylowOf_of_card hPiYj hcard


theorem omega4_nondeg : ∀ u : V4, (∀ w : V4, omega4 u w = 0) → u = 0 := by decide +kernel

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem mem_zpowers_of_centralizes {c : G} (hc : c ∈ Q) (hcQ : ∀ q ∈ Q, c * q = q * c) :
    c ∈ Subgroup.zpowers d := by
  apply h.Phi_ker hc
  apply omega4_nondeg
  intro w
  have hq := h.rep_mem w
  rw [← h.Phi_rep w, h.omega4_Phi hc hq]
  exact h.hC.om_zero_of_comm (hcQ _ hq)

end SympBasis

def Tsub {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (hS : SympBasis A Q d a₀ a₁ f₀ f₁)
    (W : Subgroup G) (hWQ : W ≤ Q) : Subgroup G where
  carrier := {n | n ∈ NQ Q d ∧
    (∀ b ∈ W, (Mg d a₀ a₁ f₀ f₁ n).mulVec (Phi d a₀ a₁ f₀ f₁ b) = Phi d a₀ a₁ f₀ f₁ b) ∧
    ∀ q ∈ Q, ∃ b ∈ W, (Mg d a₀ a₁ f₀ f₁ n).mulVec (Phi d a₀ a₁ f₀ f₁ q) =
      Phi d a₀ a₁ f₀ f₁ q + Phi d a₀ a₁ f₀ f₁ b}
  mul_mem' := by
    rintro n n' ⟨hn, hn1, hn2⟩ ⟨hn', hn1', hn2'⟩
    refine ⟨(NQ Q d).mul_mem hn hn', fun b hb => ?_, fun q hq => ?_⟩
    · rw [hS.Mg_mul hn.1 (NQ_conj_d hn) hn'.1, ← Matrix.mulVec_mulVec, hn1' b hb, hn1 b hb]
    · obtain ⟨b', hb'W, hb'⟩ := hn2' q hq
      obtain ⟨b, hbW, hb⟩ := hn2 q hq
      refine ⟨b * b', W.mul_mem hbW hb'W, ?_⟩
      rw [hS.Mg_mul hn.1 (NQ_conj_d hn) hn'.1, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_add,
        hn1 b' hb'W, hb, hS.Phi_mul (hWQ hbW) (hWQ hb'W), add_assoc]
  one_mem' := by
    refine ⟨(NQ Q d).one_mem, fun b hb => ?_, fun q hq => ⟨1, W.one_mem, ?_⟩⟩
    · rw [hS.Mg_one, Matrix.one_mulVec]
    · rw [hS.Mg_one, Matrix.one_mulVec, hS.Phi_one, add_zero]
  inv_mem' := by
    rintro n ⟨hn, hn1, hn2⟩
    have hn' : n⁻¹ ∈ NQ Q d := (NQ Q d).inv_mem hn
    have e1 : Mg d a₀ a₁ f₀ f₁ n⁻¹ * Mg d a₀ a₁ f₀ f₁ n = 1 := by
      rw [← hS.Mg_mul hn'.1 (NQ_conj_d hn') hn.1, inv_mul_cancel, hS.Mg_one]
    refine ⟨hn', fun b hb => ?_, fun q hq => ?_⟩
    · calc (Mg d a₀ a₁ f₀ f₁ n⁻¹).mulVec (Phi d a₀ a₁ f₀ f₁ b)
          = (Mg d a₀ a₁ f₀ f₁ n⁻¹).mulVec ((Mg d a₀ a₁ f₀ f₁ n).mulVec (Phi d a₀ a₁ f₀ f₁ b)) := by
            rw [hn1 b hb]
        _ = (Mg d a₀ a₁ f₀ f₁ n⁻¹ * Mg d a₀ a₁ f₀ f₁ n).mulVec (Phi d a₀ a₁ f₀ f₁ b) := by
            rw [Matrix.mulVec_mulVec]
        _ = Phi d a₀ a₁ f₀ f₁ b := by rw [e1, Matrix.one_mulVec]
    · have hq' : n⁻¹ * q * n⁻¹⁻¹ ∈ Q := hS.conj_mem hn'.1 hq
      obtain ⟨b, hbW, hb⟩ := hn2 _ hq'
      rw [← hS.Mg_apply hn.1 (NQ_conj_d hn) hq'] at hb
      have e : n * (n⁻¹ * q * n⁻¹⁻¹) * n⁻¹ = q := by group
      rw [e] at hb
      refine ⟨b⁻¹, W.inv_mem hbW, ?_⟩
      rw [← hS.Mg_apply hn'.1 (NQ_conj_d hn') hq, hS.Phi_inv (hWQ hbW)]
      rw [hb]
      abel

section Tsub

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (hS : SympBasis A Q d a₀ a₁ f₀ f₁)
  {W : Subgroup G} (hWQ : W ≤ Q)

include hS

theorem mem_Tsub {n : G} : n ∈ Tsub hS W hWQ ↔ n ∈ NQ Q d ∧
    (∀ b ∈ W, (Mg d a₀ a₁ f₀ f₁ n).mulVec (Phi d a₀ a₁ f₀ f₁ b) = Phi d a₀ a₁ f₀ f₁ b) ∧
    ∀ q ∈ Q, ∃ b ∈ W, (Mg d a₀ a₁ f₀ f₁ n).mulVec (Phi d a₀ a₁ f₀ f₁ q) =
      Phi d a₀ a₁ f₀ f₁ q + Phi d a₀ a₁ f₀ f₁ b := Iff.rfl

theorem Q_le_Tsub : Q ≤ Tsub hS W hWQ := by
  intro q hq
  rw [mem_Tsub]
  refine ⟨Q_le_NQ hS.hdc hq, fun b hb => ?_, fun q' hq' => ⟨1, W.one_mem, ?_⟩⟩
  · rw [hS.Mg_Q hq, Matrix.one_mulVec]
  · rw [hS.Mg_Q hq, Matrix.one_mulVec, hS.Phi_one, add_zero]

theorem Tsub_commute {n n' : G} (hn : n ∈ Tsub hS W hWQ) (hn' : n' ∈ Tsub hS W hWQ) :
    Mg d a₀ a₁ f₀ f₁ n * Mg d a₀ a₁ f₀ f₁ n' = Mg d a₀ a₁ f₀ f₁ n' * Mg d a₀ a₁ f₀ f₁ n := by
  rw [mem_Tsub] at hn hn'
  apply matrix_eq_of_mulVec
  intro v
  obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, Phi d a₀ a₁ f₀ f₁ q = v := ⟨_, hS.rep_mem v, hS.Phi_rep v⟩
  obtain ⟨b, hbW, hb⟩ := hn.2.2 q hq
  obtain ⟨b', hb'W, hb'⟩ := hn'.2.2 q hq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb', hb, Matrix.mulVec_add,
    Matrix.mulVec_add, hn.2.1 b' hb'W, hn'.2.1 b hbW, hb, hb']
  abel

theorem Tsub_conj {n : G} (hn : n ∈ Tsub hS W hWQ) (hdW : d ∈ W) {q : G} (hq : q ∈ Q) :
    n * q * n⁻¹ * q⁻¹ ∈ W := by
  rw [mem_Tsub] at hn
  obtain ⟨b, hbW, hb⟩ := hn.2.2 q hq
  have hbQ := hWQ hbW
  have hz : (q * b)⁻¹ * (n * q * n⁻¹) ∈ Subgroup.zpowers d := by
    refine hS.Phi_eq (Q.mul_mem hq hbQ) (hS.conj_mem hn.1.1 hq) ?_
    rw [hS.Phi_mul hq hbQ, ← hb, hS.Mg_apply hn.1.1 (NQ_conj_d hn.1) hq]
  have hcm := hS.hC.hcm b hbQ q hq
  have hzd : Subgroup.zpowers d ≤ W := Subgroup.zpowers_le.mpr hdW
  set z := (q * b)⁻¹ * (n * q * n⁻¹) with hzdef
  have hqz : n * q * n⁻¹ = q * b * z := by rw [hzdef]; group
  have h1 : z * q⁻¹ = q⁻¹ * z := (hS.hC.hzc z hz q⁻¹ (Q.inv_mem hq)).symm
  have hcm' : cm q b = b⁻¹ * (q * b * q⁻¹) := rfl
  have e : n * q * n⁻¹ * q⁻¹ = b * cm q b * z := by
    calc n * q * n⁻¹ * q⁻¹ = (q * b * z) * q⁻¹ := by rw [hqz]
      _ = q * b * (z * q⁻¹) := by group
      _ = q * b * (q⁻¹ * z) := by rw [h1]
      _ = b * (b⁻¹ * (q * b * q⁻¹)) * z := by group
      _ = b * cm q b * z := by rw [hcm']
  rw [e]
  exact W.mul_mem (W.mul_mem hbW (hzd hcm)) (hzd hz)

theorem Tsub_fixW {n : G} (hn : n ∈ Tsub hS W hWQ) {m : G} (hm : m ∈ W) :
    m⁻¹ * (n * m * n⁻¹) ∈ Subgroup.zpowers d := by
  rw [mem_Tsub] at hn
  refine hS.Phi_eq (hWQ hm) (hS.conj_mem hn.1.1 (hWQ hm)) ?_
  rw [hS.Mg_apply hn.1.1 (NQ_conj_d hn.1) (hWQ hm)]
  exact (hn.2.1 m hm).symm

end Tsub

namespace LineSetup

variable {A Q D M Y : Subgroup G} {d a₀ a₁ f₀ f₁ e t₀ t x : G}
  (h : LineSetup A Q D M Y d a₀ a₁ f₀ f₁ e t₀ t x)

include h

theorem D_le_Tsub {W : Subgroup G} (hW : D ⊓ Q = W) (hWQ : W ≤ Q) : D ≤ Tsub h.hS W hWQ := by
  intro n hn
  rw [mem_Tsub]
  have hnNQ : n ∈ NQ Q d := h.hP'NQ (Subgroup.mem_sup_right hn)
  refine ⟨hnNQ, fun b hb => ?_, fun q hq => ?_⟩
  · have hbD : b ∈ D := by rw [← hW] at hb; exact hb.1
    rw [← h.hS.Mg_apply hnNQ.1 (NQ_conj_d hnNQ) (hWQ hb)]
    have : n * b * n⁻¹ = b := by rw [h.hT.hDc n hn b hbD]; group
    rw [this]
  · have hqn : q * n⁻¹ * q⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (h.hT.hQD hq) n⁻¹).mp
      (D.inv_mem hn)
    have hbD : n * q * n⁻¹ * q⁻¹ ∈ D := by
      have : n * q * n⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) := by group
      rw [this]; exact D.mul_mem hn hqn
    have hbQ : n * q * n⁻¹ * q⁻¹ ∈ Q :=
      Q.mul_mem (h.hS.conj_mem hnNQ.1 hq) (Q.inv_mem hq)
    have hbW : n * q * n⁻¹ * q⁻¹ ∈ W := by rw [← hW]; exact ⟨hbD, hbQ⟩
    refine ⟨_, hbW, ?_⟩
    have e1 : n * q * n⁻¹ = (n * q * n⁻¹ * q⁻¹) * q := by group
    have hb2 : Phi d a₀ a₁ f₀ f₁ (n * q * n⁻¹) =
        Phi d a₀ a₁ f₀ f₁ (n * q * n⁻¹ * q⁻¹) + Phi d a₀ a₁ f₀ f₁ q := by
      calc Phi d a₀ a₁ f₀ f₁ (n * q * n⁻¹) = Phi d a₀ a₁ f₀ f₁ ((n * q * n⁻¹ * q⁻¹) * q) := by
            rw [← e1]
        _ = _ := h.hS.Phi_mul hbQ hq
    rw [← h.hS.Mg_apply hnNQ.1 (NQ_conj_d hnNQ) hq, hb2, add_comm]

end LineSetup


theorem construct_y {A Q D D' M M' Y Y' : Subgroup G} {d a₀ a₁ f₀ f₁ e t₀ t x e' t₀' t' x' : G}
    (h : LineSetup A Q D M Y d a₀ a₁ f₀ f₁ e t₀ t x)
    (h' : LineSetup A Q D' M' Y' d a₀ a₁ f₀ f₁ e' t₀' t' x')
    (hW : D' ⊓ Q = D ⊓ Q)
    (hne : ¬ (Mg d a₀ a₁ f₀ f₁ x' = 1 ∨ Mg d a₀ a₁ f₀ f₁ x' = Mg d a₀ a₁ f₀ f₁ x ∨
      Mg d a₀ a₁ f₀ f₁ x' = Mg d a₀ a₁ f₀ f₁ x * Mg d a₀ a₁ f₀ f₁ x)) :
    ∃ y : G, y ^ 3 = 1 ∧ y ∈ Subgroup.normalizer (D : Set G) ∧ y ∉ D ∧
      (∀ z ∈ D, z * y * z⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) ∧
      y * e * y⁻¹ * e⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := h.hS
  set W : Subgroup G := D ⊓ Q with hWdef
  have hWQ : W ≤ Q := inf_le_right
  have hWD : W ≤ D := inf_le_left
  have hdW : d ∈ W := ⟨h.hT.hdD, hS.hdQ⟩
  have hdz : Subgroup.zpowers d ≤ W := Subgroup.zpowers_le.mpr hdW
  have hWD' : W ≤ D' := fun m hm => by
    have : m ∈ D' ⊓ Q := by rw [hW]; exact hm
    exact this.1
  have hdD' : Subgroup.zpowers d ≤ D' := Subgroup.zpowers_le.mpr h'.hT.hdD
  have hDT : D ≤ Tsub hS W hWQ := h.D_le_Tsub rfl hWQ
  have hD'T : D' ≤ Tsub hS W hWQ := h'.D_le_Tsub hW hWQ
  have hQT : Q ≤ Tsub hS W hWQ := Q_le_Tsub hS hWQ
  have hP3 : IsPGroup 3 (Q ⊔ D : Subgroup G) := h.hT.hP'3
  have hHT : (Q ⊔ D) ⊔ Subgroup.zpowers x' ≤ Tsub hS W hWQ :=
    sup_le (sup_le hQT hDT) (Subgroup.zpowers_le.mpr (hD'T h'.hxD))
  have hZ3 : IsPGroup 3 (Subgroup.zpowers x') :=
    isPGroup_zpowers_of_pow (n := 1) (by simpa using h'.hx3)
  obtain ⟨R, hR, hPR⟩ := exists_sylowOf_ge hP3
    (le_sup_left : Q ⊔ D ≤ (Q ⊔ D) ⊔ Subgroup.zpowers x')
  obtain ⟨R₂, hR₂, hZR₂⟩ := exists_sylowOf_ge hZ3
    (le_sup_right : Subgroup.zpowers x' ≤ (Q ⊔ D) ⊔ Subgroup.zpowers x')
  obtain ⟨g, hgH, hg⟩ := hR.exists_mem_conj hR₂
  have hgT : g ∈ Tsub hS W hWQ := hHT hgH
  have hx'T : x' ∈ Tsub hS W hWQ := hD'T h'.hxD
  set y := g⁻¹ * x' * g with hydef
  have hyR : y ∈ R := (hg x').mp (hZR₂ (Subgroup.mem_zpowers x'))
  have hyT : y ∈ Tsub hS W hWQ :=
    (Tsub hS W hWQ).mul_mem ((Tsub hS W hWQ).mul_mem ((Tsub hS W hWQ).inv_mem hgT) hx'T) hgT
  have hyc : ∀ m ∈ W, y * m * y⁻¹ = m := by
    intro m hm
    have hz := Tsub_fixW hS hWQ hgT hm
    set u := g * m * g⁻¹ with hu
    set z := m⁻¹ * u with hzdef
    have hu' : u = m * z := by rw [hzdef]; group
    have huD' : u ∈ D' := by rw [hu']; exact D'.mul_mem (hWD' hm) (hdD' hz)
    have hcomm : x' * u * x'⁻¹ = u := by rw [h'.hT.hDc x' h'.hxD u huD']; group
    calc y * m * y⁻¹ = g⁻¹ * (x' * (g * m * g⁻¹) * x'⁻¹) * g := by rw [hydef]; group
      _ = g⁻¹ * u * g := by rw [← hu, hcomm]
      _ = m := by rw [hu]; group
  have hgNQ : g ∈ NQ Q d := hgT.1
  have hgiNQ : g⁻¹ ∈ NQ Q d := (NQ Q d).inv_mem hgNQ
  have hx'NQ : x' ∈ NQ Q d := h'.hxNQ
  have hMgy : Mg d a₀ a₁ f₀ f₁ y = Mg d a₀ a₁ f₀ f₁ x' := by
    have hcomm := Tsub_commute hS hWQ hgT hx'T
    have hginv : Mg d a₀ a₁ f₀ f₁ g⁻¹ * Mg d a₀ a₁ f₀ f₁ g = 1 := by
      rw [← hS.Mg_mul hgiNQ.1 (NQ_conj_d hgiNQ) hgNQ.1, inv_mul_cancel, hS.Mg_one]
    calc Mg d a₀ a₁ f₀ f₁ (g⁻¹ * x' * g)
        = Mg d a₀ a₁ f₀ f₁ g⁻¹ * Mg d a₀ a₁ f₀ f₁ x' * Mg d a₀ a₁ f₀ f₁ g := by
          rw [hS.Mg_mul ((NQ Q d).mul_mem hgiNQ hx'NQ).1 (NQ_conj_d ((NQ Q d).mul_mem hgiNQ hx'NQ))
            hgNQ.1, hS.Mg_mul hgiNQ.1 (NQ_conj_d hgiNQ) hx'NQ.1]
      _ = Mg d a₀ a₁ f₀ f₁ g⁻¹ * (Mg d a₀ a₁ f₀ f₁ x' * Mg d a₀ a₁ f₀ f₁ g) := by rw [mul_assoc]
      _ = Mg d a₀ a₁ f₀ f₁ g⁻¹ * (Mg d a₀ a₁ f₀ f₁ g * Mg d a₀ a₁ f₀ f₁ x') := by rw [hcomm]
      _ = (Mg d a₀ a₁ f₀ f₁ g⁻¹ * Mg d a₀ a₁ f₀ f₁ g) * Mg d a₀ a₁ f₀ f₁ x' := by
          rw [← mul_assoc]
      _ = Mg d a₀ a₁ f₀ f₁ x' := by rw [hginv, one_mul]
  have key : ∀ z ∈ D, z * y * z⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
    intro z hz
    have hzT : z ∈ Tsub hS W hWQ := hDT hz
    have hcommQ : ∀ q ∈ Q, z * y * q * (z * y)⁻¹ = y * z * q * (y * z)⁻¹ := by
      intro q hq
      have hwy := Tsub_conj hS hWQ hyT hdW hq
      have hwz := Tsub_conj hS hWQ hzT hdW hq
      set wy := y * q * y⁻¹ * q⁻¹ with hwydef
      set wz := z * q * z⁻¹ * q⁻¹ with hwzdef
      have e1 : y * q * y⁻¹ = wy * q := by rw [hwydef]; group
      have e2 : z * q * z⁻¹ = wz * q := by rw [hwzdef]; group
      have hzc : z * wy * z⁻¹ = wy := by rw [h.hT.hDc z hz wy (hWD hwy)]; group
      have hyc' : y * wz * y⁻¹ = wz := hyc wz hwz
      have hwcomm : wy * wz = wz * wy := h.hT.hDc wy (hWD hwy) wz (hWD hwz)
      calc z * y * q * (z * y)⁻¹ = z * (y * q * y⁻¹) * z⁻¹ := by group
        _ = z * (wy * q) * z⁻¹ := by rw [e1]
        _ = (z * wy * z⁻¹) * (z * q * z⁻¹) := by group
        _ = wy * (wz * q) := by rw [hzc, e2]
        _ = (wy * wz) * q := (mul_assoc wy wz q).symm
        _ = (wz * wy) * q := by rw [hwcomm]
        _ = wz * (wy * q) := mul_assoc wz wy q
        _ = (y * wz * y⁻¹) * (y * q * y⁻¹) := by rw [hyc', e1]
        _ = y * (wz * q) * y⁻¹ := by group
        _ = y * (z * q * z⁻¹) * y⁻¹ := by rw [e2]
        _ = y * z * q * (y * z)⁻¹ := by group
    have hyzT : y * z ∈ Tsub hS W hWQ := (Tsub hS W hWQ).mul_mem hyT hzT
    have hyzN : (y * z)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      ((Tsub hS W hWQ).inv_mem hyzT).1.1
    set c := z * y * z⁻¹ * y⁻¹ with hc
    have hcQ : ∀ q ∈ Q, c * q * c⁻¹ = q := by
      intro q hq
      set q₁ := (y * z)⁻¹ * q * (y * z)⁻¹⁻¹ with hq₁
      have hq₁Q : q₁ ∈ Q := hS.conj_mem hyzN hq
      have e : c * q * c⁻¹ = z * y * q₁ * (z * y)⁻¹ := by rw [hq₁, hc]; group
      rw [e, hcommQ q₁ hq₁Q, hq₁]; group
    have hcN : c ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.mem_normalizer_fintype fun q hq => by rw [hcQ q hq]; exact hq
    have hcNQ : c ∈ NQ Q d := ⟨hcN, mem_normalizer_zpowers_of_mem (by
      rw [hcQ d hS.hdQ]; exact Subgroup.mem_zpowers d)⟩
    have hMc : Mg d a₀ a₁ f₀ f₁ c = 1 := by
      apply matrix_eq_of_mulVec
      intro v
      obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, Phi d a₀ a₁ f₀ f₁ q = v := ⟨_, hS.rep_mem v, hS.Phi_rep v⟩
      rw [← hS.Mg_apply hcN (NQ_conj_d hcNQ) hq, hcQ q hq, Matrix.one_mulVec]
    have hzR : z ∈ R := hPR (Subgroup.mem_sup_right hz)
    have hcR : c ∈ R := by
      rw [hc]
      exact R.mul_mem (R.mul_mem (R.mul_mem hzR hyR) (R.inv_mem hzR)) (R.inv_mem hyR)
    obtain ⟨n, hn⟩ := hR.isPGroup ⟨c, hcR⟩
    have hn' : c ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hcQm : c ∈ Q := hS.mem_Q_of_Mg_one hcNQ hMc hn'
    exact hS.mem_zpowers_of_centralizes hcQm (fun q hq => by
      have := hcQ q hq
      calc c * q = c * q * c⁻¹ * c := by group
        _ = q * c := by rw [this])
  refine ⟨y, ?_, ?_, ?_, key, ?_⟩
  · have e : y = g⁻¹ * x' * g⁻¹⁻¹ := by rw [hydef]; group
    rw [e, conj_pow, h'.hx3]; group
  · refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have h1 := key z⁻¹ (D.inv_mem hz)
    have e : y * z * y⁻¹ = z * (z⁻¹ * y * z⁻¹⁻¹ * y⁻¹) := by group
    rw [e]
    exact D.mul_mem hz ((Subgroup.zpowers_le.mpr h.hT.hdD) h1)
  · intro hyD
    obtain ⟨k, hk⟩ := h.Mg_cyc (Subgroup.mem_sup_right hyD)
    have hX3 : (Mg d a₀ a₁ f₀ f₁ x) ^ 3 = 1 := by rw [pow_three']; exact h.xi_cube
    rw [hMgy, pow_eq_pow_mod k hX3] at hk
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h0 | h0
    · rw [h0, pow_zero] at hk; exact hne (Or.inl hk)
    · rw [h0, pow_one] at hk; exact hne (Or.inr (Or.inl hk))
    · rw [h0, sq] at hk; exact hne (Or.inr (Or.inr hk))
  · have heQ : e ∈ Q := h.heQ
    have hw := Tsub_conj hS hWQ hyT hdW heQ
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => h.hT.hDc u hu _ (hWD hw)


namespace LineSetup

variable {A Q D M Y D' M' Y' : Subgroup G} {d a₀ a₁ f₀ f₁ e t₀ t x e' t₀' t' x' : G}

theorem DQ_le (h : LineSetup A Q D M Y d a₀ a₁ f₀ f₁ e t₀ t x)
    (h' : LineSetup A Q D' M' Y' d a₀ a₁ f₀ f₁ e' t₀' t' x')
    (hfix : ∀ v, (Mg d a₀ a₁ f₀ f₁ x).mulVec v = v → (Mg d a₀ a₁ f₀ f₁ x').mulVec v = v) :
    D ⊓ Q ≤ D' ⊓ Q := by
  intro b hb
  obtain ⟨b', hb', hbb⟩ := (h'.fix_iff _).mp (hfix _ ((h.fix_iff _).mpr ⟨b, hb, rfl⟩))
  have hz := h.hS.Phi_eq hb'.2 hb.2 hbb
  have hzD : b'⁻¹ * b ∈ D' ⊓ Q :=
    ⟨Subgroup.zpowers_le.mpr h'.hT.hdD hz, Subgroup.zpowers_le.mpr h.hS.hdQ hz⟩
  have e1 : b = b' * (b'⁻¹ * b) := by group
  rw [e1]
  exact (D' ⊓ Q).mul_mem hb' hzD

theorem DQ_eq (h : LineSetup A Q D M Y d a₀ a₁ f₀ f₁ e t₀ t x)
    (h' : LineSetup A Q D' M' Y' d a₀ a₁ f₀ f₁ e' t₀' t' x')
    (hfix : ∀ v, (Mg d a₀ a₁ f₀ f₁ x).mulVec v = v ↔ (Mg d a₀ a₁ f₀ f₁ x').mulVec v = v) :
    D' ⊓ Q = D ⊓ Q :=
  le_antisymm (h'.DQ_le h fun v => (hfix v).mpr) (h.DQ_le h' fun v => (hfix v).mp)

end LineSetup

theorem neg_smul_V4 : ∀ (c : F3) (v : V4), -(c • v) = (-c) • v := by decide +kernel

theorem not_mem_sup_zpowers {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ e e' : G}
    (hS : SympBasis A Q d a₀ a₁ f₀ f₁) (heQ : e ∈ Q)
    (hv : ∀ c : F3, Phi d a₀ a₁ f₀ f₁ e' ≠ c • Phi d a₀ a₁ f₀ f₁ e) :
    e' ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ∃ c : F3, Phi d a₀ a₁ f₀ f₁ x = c • Phi d a₀ a₁ f₀ f₁ e}
      mul_mem' := by
        rintro x y ⟨hx, c, hc⟩ ⟨hy, c', hc'⟩
        exact ⟨Q.mul_mem hx hy, c + c', by rw [hS.Phi_mul hx hy, hc, hc', add_smul]⟩
      one_mem' := ⟨Q.one_mem, 0, by rw [hS.Phi_one, zero_smul]⟩
      inv_mem' := by
        rintro x ⟨hx, c, hc⟩
        exact ⟨Q.inv_mem hx, -c, by rw [hS.Phi_inv hx, hc]; exact neg_smul_V4 c _⟩ }
  have heS : e ∈ S := ⟨heQ, 1, by rw [one_smul]⟩
  have hdS : d ∈ S := ⟨hS.hdQ, 0, by rw [hS.Phi_z0 (Subgroup.mem_zpowers d), zero_smul]⟩
  have hle : Subgroup.zpowers e ⊔ Subgroup.zpowers d ≤ S :=
    sup_le (Subgroup.zpowers_le.mpr heS) (Subgroup.zpowers_le.mpr hdS)
  intro he'
  obtain ⟨-, c, hc⟩ := hle he'
  exact hv c hc

theorem lineVec_ne : ∀ i j : Fin 4, i ≠ j → ∀ c : F3, lineVec j ≠ c • lineVec i := by decide

theorem lineVec_ne_zero : ∀ i : Fin 4, lineVec i ≠ 0 := by decide

end CFSG.RankThree.PartTwo.Sec21.Hering2119S

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec21.Hering2119S
open CFSG.ABGLocalTools (IsSylowOf)

theorem item2119EndShare_of_k (hK : Item2119EndShareK) : Item2119EndShare := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := q2127Of A d F with hQdef
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hd3' : d ^ 3 = 1 := hAe.2 d hdA
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hQN : Q ≤ Subgroup.normalizer (A : Set G) := hQ.1.le
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQ.2.2.1] at hmem
    have h := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3' hd1]
  obtain ⟨a₀, ha₀, ha₀d⟩ : ∃ a₀ ∈ A, a₀ ∉ Subgroup.zpowers d := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers d from hall)
    omega
  have hAQ : A ≤ Q := le_sup_left.trans (hAFQ a₀ ha₀ ha₀d)
  obtain ⟨a₁, ha₁, ha₁d⟩ : ∃ a₁ ∈ A, a₁ ∉ Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d := by
    by_contra hall
    push Not at hall
    have hcard := Subgroup.card_le_of_le
      (show A ≤ Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d from hall)
    have ha₀1 : a₀ ≠ 1 := fun h1 => ha₀d (h1 ▸ Subgroup.one_mem _)
    have ha₀3 : Nat.card (Subgroup.zpowers a₀) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hAe.2 a₀ ha₀) ha₀1]
    have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers a₀ : Set G) :=
      Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_mem (g := d) (d := a₀) (by
        have : d * a₀ * d⁻¹ = a₀ := by rw [hAc d hdA a₀ ha₀]; group
        rw [this]; exact Subgroup.mem_zpowers a₀))
    have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [ha₀3, hd3] at hm
    have hpos : 1 ≤ Nat.card (Subgroup.zpowers a₀ ⊓ Subgroup.zpowers d : Subgroup G) :=
      Nat.card_pos
    have h9 : Nat.card (Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d : Subgroup G) ≤ 9 := by
      calc Nat.card (Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d : Subgroup G)
          = Nat.card (Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d : Subgroup G) * 1 := (mul_one _).symm
        _ ≤ Nat.card (Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d : Subgroup G) *
            Nat.card (Subgroup.zpowers a₀ ⊓ Subgroup.zpowers d : Subgroup G) :=
            Nat.mul_le_mul_left _ hpos
        _ = 9 := by rw [hm]
    omega
  have hQD : QData A Q d a₀ a₁ :=
    { hAe := hAe, hA27 := hA27, hdA := hdA, hd1 := hd1, hQX := hQX, hQS := hQ.1, hAQ := hAQ
      hQC := hQ.2.1, hdc := hdc, ha₀ := ha₀, ha₁ := ha₁, ha₀d := ha₀d, ha₁d := ha₁d }
  obtain ⟨f₀, hf₀, f₁, hf₁, o00, o10, o01, o11, off⟩ := hQD.exists_f
  have hS : SympBasis A Q d a₀ a₁ f₀ f₁ :=
    { toQData := hQD, hf₀ := hf₀, hf₁ := hf₁, o00 := o00, o10 := o10, o01 := o01, o11 := o11,
      off := off }
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → G, e = ![a₀, a₁, a₀ * a₁, a₀ * a₁⁻¹] := ⟨_, rfl⟩
  have hei : ∀ i, e i ∈ A := by
    intro i
    rw [he]
    fin_cases i
    · exact ha₀
    · exact ha₁
    · exact A.mul_mem ha₀ ha₁
    · exact A.mul_mem ha₀ (A.inv_mem ha₁)
  have hlv : ∀ i, Phi d a₀ a₁ f₀ f₁ (e i) = lineVec i := by
    intro i
    rw [he]
    fin_cases i
    · exact hS.Phi_a₀
    · exact hS.Phi_a₁
    · show Phi d a₀ a₁ f₀ f₁ (a₀ * a₁) = lineVec 2
      rw [hS.Phi_mul hS.ha₀Q hS.ha₁Q, hS.Phi_a₀, hS.Phi_a₁]
      decide
    · show Phi d a₀ a₁ f₀ f₁ (a₀ * a₁⁻¹) = lineVec 3
      rw [hS.Phi_mul hS.ha₀Q (Q.inv_mem hS.ha₁Q), hS.Phi_inv hS.ha₁Q, hS.Phi_a₀, hS.Phi_a₁]
      decide
  have hed : ∀ i, e i ∉ Subgroup.zpowers d := fun i hz =>
    lineVec_ne_zero i (by rw [← hlv i]; exact hS.Phi_z0 hz)
  have hline : ∀ i : Fin 4, ∃ P : Subgroup G,
      IsSylowOf 3 P (y2128Of (Lf (e i)) (F (e i)) Q) ∧ Q ≤ P ∧
      ∃ t₀ t x : G, LineSetup A Q (CFSG.Open.thompsonSubgroup P) (F (e i) ⊓ Lf (e i))
        (y2128Of (Lf (e i)) (F (e i)) Q) d a₀ a₁ f₀ f₁ (e i) t₀ t x ∧
        ∀ κ ∈ NQ Q d, Mg d a₀ a₁ f₀ f₁ κ = 1 → ∀ y ∈ y2128Of (Lf (e i)) (F (e i)) Q,
          κ * y * κ⁻¹ ∈ y2128Of (Lf (e i)) (F (e i)) Q := by
    intro i
    obtain ⟨P, hP, hQP⟩ := exists_sylowOf_ge hQ.1.isPGroup
      (le_sup_right : Q ≤ y2128Of (Lf (e i)) (F (e i)) Q)
    obtain ⟨t₀, t, x, hLS, hKY⟩ := stage_line hE h23 h24 hLf h26 hF h27 hQ hQX h28 hL hS (hei i)
      (hed i) hP
    exact ⟨P, hP, hQP, t₀, t, x, hLS, hKY⟩
  choose P hPS hQP t₀ t x hLS hKY using hline
  have hitem : ∀ i, IsItem (lineVec i) (Mg d a₀ a₁ f₀ f₁ (x i)) (Mg d a₀ a₁ f₀ f₁ (t i)) := by
    intro i
    have := (hLS i).isItem
    rwa [hlv i] at this
  have hcompat := compat_of_lines hS hLS hlv
  obtain ⟨hfixall, σ, hcyc01, -, hnc⟩ := hK (fun i => Mg d a₀ a₁ f₀ f₁ (x i))
    (fun i => Mg d a₀ a₁ f₀ f₁ (t i)) hitem hcompat
  have hij : σ 0 ≠ σ 1 := fun h => by have := σ.injective h; revert this; decide
  have hPj : IsSylowOf 3 (P (σ 0)) (y2128Of (Lf (e (σ 1))) (F (e (σ 1))) Q) :=
    partner_sylow (hLS (σ 0)) (hLS (σ 1)) (hPS (σ 0)) (hPS (σ 1)) (hQP (σ 0)) (hQP (σ 1)) rfl
      rfl (hKY (σ 1)) hcyc01
  have hW := (hLS (σ 0)).DQ_eq (hLS (σ 2)) (fun v => hfixall (σ 0) (σ 2) v)
  have hne : ¬ (Mg d a₀ a₁ f₀ f₁ (x (σ 2)) = 1 ∨
      Mg d a₀ a₁ f₀ f₁ (x (σ 2)) = Mg d a₀ a₁ f₀ f₁ (x (σ 0)) ∨
      Mg d a₀ a₁ f₀ f₁ (x (σ 2)) = Mg d a₀ a₁ f₀ f₁ (x (σ 0)) * Mg d a₀ a₁ f₀ f₁ (x (σ 0))) :=
    fun h => h.elim (hLS (σ 2)).xi_ne_one hnc
  obtain ⟨y, hy3, hyN, hyD, hyc, hye⟩ := construct_y (hLS (σ 0)) (hLS (σ 2)) hW hne
  have hnot : e (σ 1) ∉ Subgroup.zpowers (e (σ 0)) ⊔ Subgroup.zpowers d :=
    not_mem_sup_zpowers hS (hS.hAQ (hei (σ 0))) (fun c => by
      rw [hlv, hlv]; exact lineVec_ne (σ 0) (σ 1) hij c)
  exact ⟨e (σ 0), hei (σ 0), hed (σ 0), e (σ 1), hei (σ 1), hnot, P (σ 0), P (σ 0), hPS (σ 0), hPj,
    rfl, y, hy3, hyN, hyD, hyc, hye⟩

end CFSG.RankThree.PartTwo.Sec21
