module

public import CFSG.Quasithin.EmptyFaithful.E22PDick
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenCoatom

public section

namespace CFSG.Quasithin.RonanE114.L2

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Walter CFSG.Quasithin.E22L2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem psl2_centralizer_involution_isCoatom_seven
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf3 : 3 ≤ f) (hfodd : Odd f)
    (h8 : p ^ f % 8 = 7) {z : PSL2 K} (hz : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set (PSL2 K))) := by
  classical
  set C := Subgroup.centralizer ({z} : Set PSL(2, K)) with hC
  set q := p ^ f with hq
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hp2 : p ≠ 2 := fun h => by subst h; exact (Nat.not_odd_iff_even.mpr even_two) hp
  have hf0 : 0 < f := by omega
  have hodd : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK hp hf0
  have hq343 : 343 ≤ q := by
    have h7 : 7 ≤ p := by
      have : p ^ f % 8 = 7 := h8
      by_contra hlt
      have : p ≤ 6 := by omega
      have hp3 : p = 3 ∨ p = 5 := by
        rcases (by omega : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6) with h | h | h | h
        · exact Or.inl h
        · exact absurd h (fun h => by subst h; exact (by decide : ¬ Nat.Prime 4) (Fact.out))
        · exact Or.inr h
        · exact absurd h (fun h => by subst h; exact (by decide : ¬ Nat.Prime 6) (Fact.out))
      rcases hp3 with rfl | rfl
      · have h3 : 3 ^ f % 8 = 3 ∨ 3 ^ f % 8 = 1 := by
          rcases Nat.even_or_odd f with ⟨g, hg⟩ | ⟨g, hg⟩
          · right; rw [hg, ← two_mul, pow_mul, Nat.pow_mod]; norm_num
          · left; rw [hg, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
        omega
      · have h5 : 5 ^ f % 8 = 5 ∨ 5 ^ f % 8 = 1 := by
          rcases Nat.even_or_odd f with ⟨g, hg⟩ | ⟨g, hg⟩
          · right; rw [hg, ← two_mul, pow_mul, Nat.pow_mod]; norm_num
          · left; rw [hg, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
        omega
    calc 343 = 7 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left h7 3
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf3
  have hq4 : q % 4 = 3 := by omega
  obtain ⟨n, hnq, hn8, hcn, ⟨e⟩⟩ : ∃ n : ℕ, 2 * n = q + 1 ∧ 8 ≤ n ∧
      Nat.card C = 2 * n ∧ Nonempty (C ≃* DihedralGroup n) := by
    obtain ⟨-, h3⟩ := psl2_centralizer_involution K hK hp hf0 hz
    obtain ⟨hc, he⟩ := h3 hq4
    exact ⟨(q + 1) / 2, by omega, by omega, by rw [hc]; omega, he⟩
  have hCnc : ¬ ∀ a b : C, a * b = b * a := by
    intro hcomm
    have : IsMulCommutative (DihedralGroup n) := ⟨⟨fun x y => e.symm.injective (by
      rw [map_mul, map_mul]; exact hcomm _ _)⟩⟩
    rcases DihedralGroup.commutative_iff.mp this with h | h <;> omega
  have hcop : Nat.Coprime (2 * n) p := by
    rw [hnq, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    have hpq : p ∣ q := dvd_pow_self p (by omega)
    have := (Nat.dvd_add_right hpq).mp hdvd
    have := Nat.le_of_dvd (by omega) this
    omega
  refine ⟨?_, fun H hCH => ?_⟩
  ·
    intro htop
    have hzZ : z ∈ Subgroup.center PSL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.eq_top_iff' C).mp htop g)
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at hzZ
    rw [hzZ, orderOf_one] at hz
    omega
  have hle : C ≤ H := hCH.le
  have hdvd : 2 * n ∣ Nat.card H := hcn ▸ Subgroup.card_dvd_of_le hle
  have hlt : 2 * n < Nat.card H := by
    rcases (Nat.le_of_dvd Nat.card_pos hdvd).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hcn, h])) hCH.ne
  have hgcd : Nat.gcd (q - 1) 2 = 2 := Nat.gcd_eq_right (by omega)
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨k, -, -, hcyc⟩ | ⟨k, hk, hHk, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, s, hs, hs2, N, D, hN, hNel, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmf, ⟨eP⟩⟩ |
      ⟨m, hm, hmf, -⟩
  ·
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hk] at hdvd
    have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (dvd_mul_right 2 n) hdvd)
    exact (hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h2).symm).elim
  ·
    refine absurd (fun (a b : C) => ?_) hCnc
    have h := congrArg (fun x : H => (x : PSL(2, K))) (mul_comm' (⟨a, hle a.2⟩ : H) ⟨b, hle b.2⟩)
    exact Subtype.ext h
  ·
    rw [hK, hgcd] at hk
    have hkle : k ≤ (q + 1) / 2 := by
      rcases hk with hk | hk
      · exact (Nat.le_of_dvd (by omega) hk).trans (by omega)
      · exact Nat.le_of_dvd (by omega) hk
    rw [hHk] at hdvd hlt
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
    have hj2 : 2 ≤ j := by
      rcases j with _ | _ | j
      · omega
      · omega
      · omega
    have : 2 * n ≤ k := by
      calc 2 * n = n * 2 := by ring
        _ ≤ n * j := Nat.mul_le_mul_left n hj2
        _ = k := hj.symm
    omega
  ·
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr eA4.toEquiv, Nat.card_eq_fintype_card]
      rfl
    omega
  ·
    have h24 : Nat.card H = 24 := by
      rw [Nat.card_congr eS4.toEquiv]
      exact e22pd_card_perm_four
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
    rw [hgcd] at hs2
    have := Nat.le_of_dvd (by omega) (dvd_trans hds hs2)
    omega
  ·
    by_cases hmf' : m = f
    · subst hmf'
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_congr eP.toEquiv,
        psl2_card_formula _ (isOddPrimePower_of_card (GaloisField.card p m hm) hp
          (Nat.pos_of_ne_zero hm)),
        GaloisField.card p m hm, psl2_card_formula K hodd, hK]
    · exfalso
      obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · omega
        · simp at hk; exact absurd hk.symm hmf'
        · omega
      have hkodd : Odd k := by
        have : Odd (m * k) := hk ▸ hfodd
        exact (Nat.odd_mul.mp this).2
      have hk3 : 3 ≤ k := by
        rcases hkodd with ⟨a, ha⟩
        omega
      have hcardH : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
        rw [Nat.card_congr eP.toEquiv,
          psl2_card_formula _ (isOddPrimePower_of_card (GaloisField.card p m hm) hp
            (Nat.pos_of_ne_zero hm)),
          GaloisField.card p m hm]
      have h3m : p ^ (3 * m) ≤ q := by
        rw [hq]
        exact Nat.pow_le_pow_right hp.pos (by nlinarith)
      have hlt3 : Nat.card H < p ^ (3 * m) := by
        rw [hcardH]
        have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
        have : p ^ (3 * m) = p ^ m * (p ^ m) ^ 2 := by ring
        rw [this]
        have h1 : p ^ m * ((p ^ m) ^ 2 - 1) / 2 ≤ p ^ m * ((p ^ m) ^ 2 - 1) := Nat.div_le_self _ _
        have h2 : p ^ m * ((p ^ m) ^ 2 - 1) < p ^ m * (p ^ m) ^ 2 := by
          apply Nat.mul_lt_mul_of_pos_left _ (by omega)
          have : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
          omega
        omega
      have := Nat.le_of_dvd Nat.card_pos hdvd
      omega
  ·
    obtain ⟨k, hk⟩ := hmf
    have : Even f := ⟨m * k, by rw [hk]; ring⟩
    exact absurd hfodd (Nat.not_odd_iff_even.mpr this)

theorem psl2_centralizer_involution_isCoatom_gen
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 2 ≤ f) (h27 : 27 ≤ p ^ f)
    {z : PSL2 K} (hz : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set (PSL2 K))) := by
  have hp2 : p ≠ 2 := fun h => by subst h; exact (Nat.not_odd_iff_even.mpr even_two) hp
  have hq : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.pow (n := f))
  by_cases h4 : p ^ f % 4 = 1
  · exact ComponentClassification.AutL2Facts.isCoatom_centralizer_involution (Fact.out : p.Prime)
      hp2 hK h4 (by omega) hz
  · by_cases h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5
    · exact psl2_centralizer_involution_isCoatom K hK hp (by omega) (by omega) h8 hz
    · have h78 : p ^ f % 8 = 7 := by omega
      have hfodd : Odd f := by
        by_contra hfe
        obtain ⟨g, hg⟩ := Nat.not_odd_iff_even.mp hfe
        have : p ^ f % 4 = 1 := by
          rw [hg, ← two_mul, pow_mul, Nat.pow_mod]
          have hpodd : p % 2 = 1 := Nat.odd_iff.mp hp
          have : p ^ 2 % 4 = 1 := by
            rcases hp with ⟨c, hc⟩
            rw [hc]
            ring_nf
            omega
          rw [this]
          simp
        omega
      exact psl2_centralizer_involution_isCoatom_seven hK hp (by
        rcases hfodd with ⟨a, ha⟩; omega) hfodd h78 hz

end CFSG.Quasithin.RonanE114.L2
