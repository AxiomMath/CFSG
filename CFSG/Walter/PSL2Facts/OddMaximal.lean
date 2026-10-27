module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

public section

namespace CFSG.Walter

open scoped MatrixGroups
open CFSG.GorensteinWalter

universe u

theorem alternatingGroup_five_pow_eq_one :
    ∀ g : alternatingGroup (Fin 5), g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem sq_mod_sixteen_of_mod_eight {q : ℕ} (h8 : q % 8 = 3 ∨ q % 8 = 5) : q ^ 2 % 16 = 9 := by
  rw [Nat.pow_mod]
  have h : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
  rcases h with h | h | h | h <;> rw [h]

section Field

variable (K : Type u) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem psl2_centralizer_involution_isCoatom (hK : Nat.card K = p ^ f)
    (hp : Odd p)
    (hf : 0 < f) (h11 : 11 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    {t : PSL(2, K)} (ht : orderOf t = 2) :
    IsCoatom (Subgroup.centralizer ({t} : Set PSL(2, K))) := by
  classical
  set C := Subgroup.centralizer ({t} : Set PSL(2, K)) with hC
  set q := p ^ f with hq
  have hpodd : p ≠ 2 := fun h => by subst h; exact (Nat.not_odd_iff_even.mpr even_two) hp
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨n, hnlo, hnhi, hn6, hcn, ⟨e⟩⟩ : ∃ n : ℕ, (q - 1) / 2 ≤ n ∧ n ≤ (q + 1) / 2 ∧ 6 ≤ n ∧
      Nat.card C = 2 * n ∧ Nonempty (C ≃* DihedralGroup n) := by
    obtain ⟨h1, h3⟩ := psl2_centralizer_involution K hK hp hf ht
    have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hq4 with hq4 | hq4
    · obtain ⟨hc, he⟩ := h1 hq4
      exact ⟨(q - 1) / 2, le_rfl, by omega, by omega, by rw [hc]; omega, he⟩
    · obtain ⟨hc, he⟩ := h3 hq4
      exact ⟨(q + 1) / 2, by omega, le_rfl, by omega, by rw [hc]; omega, he⟩
  have hCnc : ¬ ∀ a b : C, a * b = b * a := by
    intro hcomm
    have : IsMulCommutative (DihedralGroup n) := ⟨⟨fun x y => e.symm.injective (by
      rw [map_mul, map_mul]; exact hcomm _ _)⟩⟩
    rcases DihedralGroup.commutative_iff.mp this with h | h <;> omega
  have hcop : Nat.Coprime (2 * n) p := by
    rw [← hcn]
    obtain ⟨h1, h3⟩ := psl2_centralizer_involution K hK hp hf ht
    have hpq : p ∣ q := dvd_pow_self p hf.ne'
    have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    rcases hq4 with hq4 | hq4
    · rw [(h1 hq4).1] at hdvd
      have h1' := Nat.dvd_sub hpq hdvd
      rw [show q - (q - 1) = 1 by omega] at h1'
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1')
    · rw [(h3 hq4).1] at hdvd
      have := (Nat.dvd_add_right hpq).mp hdvd
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  refine ⟨?_, fun H hCH => ?_⟩
  ·
    intro htop
    have htZ : t ∈ Subgroup.center PSL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.eq_top_iff' C).mp htop g)
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at htZ
    rw [htZ, orderOf_one] at ht
    omega
  have hle : C ≤ H := hCH.le
  have hdvd : 2 * n ∣ Nat.card H := hcn ▸ Subgroup.card_dvd_of_le hle
  have hlt : 2 * n < Nat.card H := by
    rcases (Nat.le_of_dvd Nat.card_pos hdvd).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hcn, h])) hCH.ne
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rw [hK]
    obtain ⟨k, hk⟩ := hp.pow (n := f)
    exact ⟨k, by omega⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hHz, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, s, -, hs, N, D, hN, hNel, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmf, ⟨eP⟩⟩ |
      ⟨m, -, hmf, -⟩
  ·
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hk] at hdvd
    have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (dvd_mul_right 2 n) hdvd)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h2).symm hpodd
  ·
    refine absurd (fun (a b : C) => ?_) hCnc
    have h := congrArg (fun x : H => (x : PSL(2, K))) (mul_comm' (⟨a, hle a.2⟩ : H) ⟨b, hle b.2⟩)
    exact Subtype.ext h
  ·
    rw [hgcd, hK] at hz
    have hzle : z ≤ (q + 1) / 2 := by
      rcases hz with hz | hz
      · exact (Nat.le_of_dvd (by omega) hz).trans (by omega)
      · exact Nat.le_of_dvd (by omega) hz
    rw [hHz] at hdvd hlt
    obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have : 2 * n ≤ z := by rw [hk]; exact Nat.mul_le_mul_left n hk2 |>.trans_eq' (by ring)
    omega
  ·
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr eA4.toEquiv, Nat.card_eq_fintype_card]
      rfl
    omega
  ·
    rw [pow_mul', ← hq] at h16
    have := sq_mod_sixteen_of_mod_eight h8
    omega
  ·
    let x : C := e.symm (DihedralGroup.r 1)
    have hx : orderOf x = n := by rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hy : orderOf (eA5 ⟨x, hle x.2⟩) = n := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx]
    rcases alternatingGroup_five_pow_eq_one (eA5 ⟨x, hle x.2⟩) with h | h | h <;>
    · have := Nat.le_of_dvd (by norm_num) (hy ▸ orderOf_dvd_of_pow_eq_one h)
      omega
  ·
    have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hHcard : Nat.card H = p ^ m * s := by
      rw [← hcompl.card_mul_card, hNcard, hDcard]
    rw [hHcard] at hdvd
    have hds : 2 * n ∣ s := (Nat.Coprime.pow_right m hcop).dvd_of_dvd_mul_left hdvd
    have hgcd' : Nat.gcd (p ^ f - 1) 2 = 2 := by rw [← hq, ← hK, hgcd]
    rw [hgcd'] at hs
    have := Nat.le_of_dvd (by omega) (dvd_trans hds hs)
    omega
  ·
    have hcardH : Nat.card H = p ^ m * (p ^ m * p ^ m - 1) / 2 := by
      rw [Nat.card_congr eP.toEquiv,
        psl2_card_formula _ (isOddPrimePower_of_card (GaloisField.card p m hm) hp
          (Nat.pos_of_ne_zero hm)), GaloisField.card p m hm, pow_two]
    by_cases hmf' : m = f
    · subst hmf'
      apply Subgroup.eq_top_of_card_eq
      rw [hcardH, psl2_card_formula K (isOddPrimePower_of_card hK hp hf), hK, pow_two]
    · exfalso
      obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · omega
        · exfalso
          apply hmf'
          omega
        · omega
      set q0 := p ^ m with hq0
      have hq0odd : Odd q0 := hp.pow
      have hq0sq : q0 * q0 ≤ q := by
        rw [hq, hq0, ← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by rw [hk]; nlinarith)
      have h2 : 2 ∣ q0 * q0 - 1 := by
        obtain ⟨a, ha⟩ := hq0odd
        exact ⟨2 * a * a + 2 * a, by rw [ha]; ring_nf; omega⟩
      rw [hcardH, Nat.mul_div_assoc _ h2] at hdvd
      have hcop0 : Nat.Coprime (2 * n) q0 := Nat.Coprime.pow_right m hcop
      have hq03 : 3 ≤ q0 := by
        have : 1 < q0 := Nat.one_lt_pow (by omega) hp1
        obtain ⟨a, ha⟩ := hq0odd
        omega
      have hq09 : 9 ≤ q0 * q0 := Nat.mul_le_mul hq03 hq03
      have := Nat.le_of_dvd (by omega) (hcop0.dvd_of_dvd_mul_left hdvd)
      omega
  ·
    exact absurd (odd_of_pow_mod_eight hp h8) (Nat.not_odd_iff_even.mpr
      (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_right 2 m) hmf)))

end Field

theorem psl2_odd_centralizer_involution_isCoatom {p f : ℕ}
    [Fact p.Prime] (hp : Odd p)
    (hf : 0 < f) (h11 : 11 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    {t : PSL(2, GaloisField p f)} (ht : orderOf t = 2) :
    IsCoatom (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f))) :=
  psl2_centralizer_involution_isCoatom _ (GaloisField.card p f hf.ne') hp hf h11 h8 ht

end CFSG.Walter
