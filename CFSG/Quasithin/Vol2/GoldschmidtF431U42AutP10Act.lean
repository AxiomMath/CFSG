module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Hs

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

structure RhoData (G : Type) [Group G] where
  ι : Ah →* G
  ρ : G
  inj : Function.Injective ι
  not_mem : ρ ∉ ι.range
  sq : ρ ^ 2 = ι fhatA
  conj : ∀ a ∈ [p10sA 0, p10sA 2, p10sA 4, p10sA 5, p10tA], ρ * ι a * ρ⁻¹ = ι a * ι fhatA

@[expose] def cntE (w : List ℕ) : ℕ := (w.filter fun k => k < 5).length

theorem parE_eq (w : List ℕ) : parE w = cntE w % 2 := rfl

theorem cntE_cons (k : ℕ) (w : List ℕ) : cntE (k :: w) = (if k < 5 then 1 else 0) + cntE w := by
  by_cases h : k < 5
  · simp [cntE, h, Nat.add_comm]
  · simp [cntE, h]

namespace RhoData

variable {G : Type} [Group G] (d : RhoData G)

@[expose] def F : G := d.ι fhatA

theorem F_mul_F : d.F * d.F = 1 := by
  rw [F, ← map_mul, ← pow_two, fhatA_sq, map_one]

theorem F_pow_two : d.F ^ 2 = 1 := by rw [pow_two, d.F_mul_F]

theorem F_pow (n : ℕ) : d.F ^ n = d.F ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, d.F_pow_two, one_pow, mul_one]

theorem rho_comm : d.ρ * d.F = d.F * d.ρ := by
  have : d.F = d.ρ ^ 2 := d.sq.symm
  rw [this]
  group

theorem rho_F : d.ρ * d.F * d.ρ⁻¹ = d.F := by rw [d.rho_comm]; group

theorem eSym_comm (k : ℕ) (hk : k < 6) : d.ι (p10eSymA k) * d.F = d.F * d.ι (p10eSymA k) := by
  have h : p10eSymA k * fhatA = fhatA * p10eSymA k := by
    refine comm_of_comp_comm (v := fhatA) repL_p10fL (repL_eSym k) ?_
    exact p10_K_check.2.2.2.2.2.2.2.2.2.2 k hk
  rw [F, ← map_mul, ← map_mul, h]

theorem eSym_conj (k : ℕ) (hk : k < 6) :
    d.ρ * d.ι (p10eSymA k) * d.ρ⁻¹ = d.ι (p10eSymA k) * d.F ^ (if k < 5 then 1 else 0) := by
  have hc := d.conj
  interval_cases k
  · simpa [p10eSymA, F] using hc (p10sA 0) (by simp)
  · simpa [p10eSymA, F] using hc (p10sA 2) (by simp)
  · simpa [p10eSymA, F] using hc (p10sA 4) (by simp)
  · simpa [p10eSymA, F] using hc (p10sA 5) (by simp)
  · simpa [p10eSymA, F] using hc p10tA (by simp)
  · simpa [p10eSymA, F] using d.rho_F

theorem word_conj (w : List ℕ) (hw : ∀ k ∈ w, k < 6) :
    d.ρ * d.ι (aE w) * d.ρ⁻¹ = d.ι (aE w) * d.F ^ cntE w ∧
      d.ι (aE w) * d.F = d.F * d.ι (aE w) := by
  induction w with
  | nil => simp [aE, cntE]
  | cons k w ih =>
    have hk : k < 6 := hw k List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := ih fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')
    have e1 : aE (k :: w) = p10eSymA k * aE w := by simp [aE]
    have hcomm : ∀ e : ℕ, d.F ^ e * d.ι (aE w) = d.ι (aE w) * d.F ^ e := fun e =>
      (Commute.pow_right (show Commute (d.ι (aE w)) d.F from ih2) e).eq.symm
    rw [e1, map_mul, cntE_cons]
    refine ⟨?_, ?_⟩
    · calc d.ρ * (d.ι (p10eSymA k) * d.ι (aE w)) * d.ρ⁻¹
          = (d.ρ * d.ι (p10eSymA k) * d.ρ⁻¹) * (d.ρ * d.ι (aE w) * d.ρ⁻¹) := by group
        _ = (d.ι (p10eSymA k) * d.F ^ (if k < 5 then 1 else 0)) * (d.ι (aE w) * d.F ^ cntE w) := by
          rw [d.eSym_conj k hk, ih1]
        _ = d.ι (p10eSymA k) * (d.F ^ (if k < 5 then 1 else 0) * d.ι (aE w)) * d.F ^ cntE w := by
          simp only [mul_assoc]
        _ = d.ι (p10eSymA k) * (d.ι (aE w) * d.F ^ (if k < 5 then 1 else 0)) * d.F ^ cntE w := by
          rw [hcomm]
        _ = d.ι (p10eSymA k) * d.ι (aE w) * d.F ^ ((if k < 5 then 1 else 0) + cntE w) := by
          rw [pow_add]; simp only [mul_assoc]
    · calc d.ι (p10eSymA k) * d.ι (aE w) * d.F
          = d.ι (p10eSymA k) * (d.ι (aE w) * d.F) := by rw [mul_assoc]
        _ = d.ι (p10eSymA k) * (d.F * d.ι (aE w)) := by rw [ih2]
        _ = (d.ι (p10eSymA k) * d.F) * d.ι (aE w) := by rw [mul_assoc]
        _ = d.F * d.ι (p10eSymA k) * d.ι (aE w) := by rw [d.eSym_comm k hk]
        _ = d.F * (d.ι (p10eSymA k) * d.ι (aE w)) := by rw [mul_assoc]

theorem conj_Kh {k : Ah}
    (hk : k ∈ p10Kh) {l : PL} (hl : RepL l (k : P45)) :
    ∃ p : ℕ, RepL (phiL l) ((k * fhatA ^ p : Ah) : P45) ∧
      d.ρ * d.ι k * d.ρ⁻¹ = d.ι (k * fhatA ^ p) := by
  obtain ⟨l0, hl0, hrep0⟩ := rep_mem_Kh k hk
  obtain rfl : l0 = l := repL_unique hrep0 hl
  obtain ⟨i, hi, hil⟩ := List.mem_iff_getElem.1 hl0
  have hlen : p10Kl.length = p10Kw.length := by rw [p10Kl_eq]; simp
  have hiw : i < p10Kw.length := hlen ▸ hi
  set w := p10Kw[i] with hw
  have hwmem : w ∈ p10Kw := List.getElem_mem hiw
  have hw6 : ∀ k ∈ w, k < 6 := p10_K_check.2.2.1 w hwmem
  have hlw : l0 = evalEL w := by
    rw [← hil, hw]
    simp [p10Kl_eq]
  have hkw : k = aE w := Subtype.ext (eq_of_repL hl (hlw ▸ repL_aE w))
  have hpar : p10Kp.getD (p10Kl.idxOf l0) 0 = parE w := by
    rw [← hil, p10_K_check.1.idxOf_getElem i hi]
    simp [p10Kp, hw, List.getD_eq_getElem?_getD, hiw]
  obtain ⟨hc1, -⟩ := d.word_conj w hw6
  refine ⟨parE w, ?_, ?_⟩
  · unfold phiL
    rw [hpar]
    have hp2 : parE w = 0 ∨ parE w = 1 := by rw [parE_eq]; omega
    rcases hp2 with h0 | h1
    · rw [h0]
      simpa using hl
    · rw [h1]
      have h' : RepL (comp l0 p10fL) ((k * fhatA : Ah) : P45) := repL_mul hl repL_p10fL
      simpa using h'
  · rw [hkw, hc1, map_mul, map_pow, ← F, d.F_pow]
    rfl

theorem alpha_step {k : Ah}
    (hk : k ∈ p10Kh) {l : PL} (hl : RepL l (k : P45)) :
    ∃ k' ∈ p10Kh, RepL (alphaL l) (k' : P45) ∧
      (d.ρ * d.ι p10hA) * d.ι k * (d.ρ * d.ι p10hA)⁻¹ = d.ι k' := by
  have hnor : p10hA * k * p10hA⁻¹ ∈ p10Kh := by
    have h1 : (⟨k, p10Kh_le_Nh hk⟩ : p10Nh) ∈ p10Kh.subgroupOf p10Nh := hk
    exact normal_Kh.conj_mem _ h1 ⟨p10hA, p10hA_mem_Nh⟩
  have hrep1 : RepL (comp (comp p10hL l) p10hiL) ((p10hA * k * p10hA⁻¹ : Ah) : P45) :=
    repL_mul (repL_mul repL_p10hA hl) repL_p10hiL
  obtain ⟨p, hrep', hconj⟩ := d.conj_Kh hnor hrep1
  refine ⟨p10hA * k * p10hA⁻¹ * fhatA ^ p,
    p10Kh.mul_mem hnor (p10Kh.pow_mem fhatA_mem_Kh _), hrep', ?_⟩
  rw [← hconj, map_mul, map_mul, map_inv]
  group

end RhoData

end CFSG.Quasithin.H13.F431.U42Aut
