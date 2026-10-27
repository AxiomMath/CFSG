module

public import CFSG.Quasithin.EmptyFaithful.S146zJNum
public import CFSG.Quasithin.EmptyFaithful.S146zISwQ
public import CFSG.Quasithin.EmptyFaithful.S146zJAlg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Dih

theorem dih_invol_sr {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {b : DihedralGroup p}
    (hb : b * b = 1) (hb1 : b ≠ 1) : ∃ c : ZMod p, b = DihedralGroup.sr c := by
  cases b with
  | r i =>
    exfalso
    apply hb1
    have h2 : DihedralGroup.r (i + i) = DihedralGroup.r 0 := by
      rw [← DihedralGroup.r_mul_r]
      exact hb.trans DihedralGroup.one_def
    have h3 := DihedralGroup.r.inj h2
    have h4 : (2 : ZMod p) * i = 0 := by rw [two_mul]; exact h3
    have h5 : i = 0 := (mul_eq_zero.mp h4).resolve_left hp2
    rw [h5]
    rfl
  | sr i => exact ⟨i, rfl⟩

theorem dih_refl_inv_rot {p : ℕ} [NeZero p] (c : ZMod p) :
    DihedralGroup.r 1 * DihedralGroup.sr c * DihedralGroup.r 1 * (DihedralGroup.sr c)⁻¹ = (1 : DihedralGroup p) := by
  rw [DihedralGroup.inv_sr, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
    DihedralGroup.one_def]
  congr 1
  ring

end Dih

section Idx

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem Wsub_index_eq
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) {DH : Subgroup G}
    (hDU : DH ≤ conjClosure (VZ T M) H) (hZD : quasithinOmegaOneCenter T ≤ DH) :
    (Wsub h91 DH).index = DH.relIndex (conjClosure (VZ T M) H) := by
  have hrange : (valW h91).range =
      tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact w.val_mem
    · intro hx
      exact ⟨IntMod.mk h91.isElemAbelian_tilde ⟨x, hx⟩, rfl⟩
  unfold Wsub
  rw [Subgroup.index_comap, hrange]
  exact relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) hZD hDU (U_le_normalizer h91)

end Idx

section Num2

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_DH_inf_noncomm (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 16) {x : G} (hx₁ : x ∈ H₁)
    (hxQ : x ∉ pCoreOf 2 H) (hx2 : x * x = 1) {DH : Subgroup G}
    (hDU : DH ≤ conjClosure (VZ T M) H) (hZD : quasithinOmegaOneCenter T ≤ DH)
    (hidx : DH.relIndex (conjClosure (VZ T M) H) ≤ 2) :
    ∃ d ∈ DH ⊓ uHi T M H H₁, x * d * x⁻¹ * d⁻¹ ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hp2
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hxH : x ∈ H := hH₁H hx₁
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨a, ha⟩ := hφs (DihedralGroup.r 1)
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  have hφx1 : φ ⟨x, hx₁⟩ ≠ 1 := fun e => hxQ ((hker _).mp e)
  have hφx2 : φ ⟨x, hx₁⟩ * φ ⟨x, hx₁⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hx₁⟩ : ↥H₁) * ⟨x, hx₁⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  obtain ⟨c, hc⟩ := dih_invol_sr h2 hφx2 hφx1
  have haxa : (a : G) * x * (a : G) * x⁻¹ ∈ pCoreOf 2 H := by
    have h1 : φ (a * ⟨x, hx₁⟩ * a * ⟨x, hx₁⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [ha, hc]
      exact dih_refl_inv_rot c
    simpa using (hker _).mp h1
  have hρ : rhoH h91 (⟨(a : G), haH⟩ * ⟨x, hxH⟩ * ⟨(a : G), haH⟩ * ⟨x, hxH⟩⁻¹) = 1 := by
    rw [rhoH_eq_one_iff]
    simpa using haxa
  have hαinv : conjSub (a : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ a.2))
  have hαW : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
    fun w hw => rhoH_mem_Wsub h91 ⟨(a : G), haH⟩ hi₁ hαinv hw
  have hpow : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      (⇑(rhoH h91 ⟨(a : G), haH⟩))^[p] w = w := by
    intro w _
    have hapQ : (a : G) ^ p ∈ pCoreOf 2 H := by
      have h1 : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
      simpa using (hker _).mp h1
    rw [iterate_eq_pow_mulAut, ← map_pow]
    have h1 : rhoH h91 ((⟨(a : G), haH⟩ : ↥H) ^ p) = 1 :=
      (rhoH_eq_one_iff h91 _).mpr (by simpa using hapQ)
    rw [h1]
    rfl
  have hα2 : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ (rhoH h91 ⟨(a : G), haH⟩ w) = w → w = 1 := by
    intro w hw hww
    have hP2 : Function.IsPeriodicPt (⇑(rhoH h91 ⟨(a : G), haH⟩)) 2 w := hww
    have hPp : Function.IsPeriodicPt (⇑(rhoH h91 ⟨(a : G), haH⟩)) p w := hpow w hw
    have hg := hP2.gcd hPp
    have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    rw [hcop] at hg
    exact h.eq_one_of_fix S hred h91 φ hker ha hw hg
  have hinv : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ (rhoH h91 ⟨x, hxH⟩ (rhoH h91 ⟨(a : G), haH⟩ w)) =
        rhoH h91 ⟨x, hxH⟩ w := by
    intro w _
    simp only [map_mul, map_inv] at hρ
    have h3 := mul_inv_eq_one.mp hρ
    have h4 := congrArg (fun f : MulAut (UMod h91) => f w) h3
    simpa [MulAut.mul_apply] using h4
  have hsq := card_fix_sq_le (rhoH h91 ⟨(a : G), haH⟩) (rhoH h91 ⟨x, hxH⟩)
    (Wsub h91 (uHi T M H H₁)) hαW hα2 hinv
  rw [hcard] at hsq
  have h4 : Nat.card ↥(fixSubOf (rhoH h91 ⟨x, hxH⟩) ⊓ Wsub h91 (uHi T M H H₁)) ≤ 4 := by
    by_contra hgt
    push Not at hgt
    nlinarith
  have hle : Wsub h91 DH ⊓ Wsub h91 (uHi T M H H₁) ≤
      fixSubOf (rhoH h91 ⟨x, hxH⟩) ⊓ Wsub h91 (uHi T M H H₁) := by
    intro w hw
    refine ⟨?_, hw.2⟩
    obtain ⟨d, hd, hdD, rfl⟩ := exists_clsU_of_mem_Wsub h91 hDU hw.1
    have hdU1 : d ∈ uHi T M H H₁ :=
      (clsU_mem_Wsub_iff h91 hi₁ (Z_le_uHi T M H H₁) hd).mp hw.2
    have h5 := hall d ⟨hdD, hdU1⟩
    show rhoH h91 ⟨x, hxH⟩ (clsU h91 hd) = clsU h91 hd
    rw [rhoH_clsU_eq_iff]
    rw [h5]
    exact (quasithinOmegaOneCenter T).one_mem
  have h5 : Nat.card ↥(Wsub h91 DH ⊓ Wsub h91 (uHi T M H H₁)) ≤ 4 :=
    (Subgroup.card_le_of_le hle).trans h4
  have hindex : (Wsub h91 DH).index ≤ 2 := by
    rw [Wsub_index_eq h91 hDU hZD]
    exact hidx
  have hrel : (Wsub h91 DH).relIndex (Wsub h91 (uHi T M H H₁)) ≤ 2 := by
    have h6 : (Wsub h91 DH).relIndex (Wsub h91 (uHi T M H H₁)) ∣ (Wsub h91 DH).index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    have h7 : (Wsub h91 DH).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h7) h6).trans hindex
  have h8 := Subgroup.relIndex_mul_card (Wsub h91 DH) (Wsub h91 (uHi T M H H₁))
  rw [hcard] at h8
  have h9 : 16 ≤ 2 * Nat.card ↥(Wsub h91 DH ⊓ Wsub h91 (uHi T M H H₁)) := by
    calc 16 = (Wsub h91 DH).relIndex (Wsub h91 (uHi T M H H₁)) *
          Nat.card ↥(Wsub h91 DH ⊓ Wsub h91 (uHi T M H H₁)) := h8.symm
      _ ≤ 2 * Nat.card ↥(Wsub h91 DH ⊓ Wsub h91 (uHi T M H H₁)) :=
          Nat.mul_le_mul_right _ hrel
  omega

end Num2

end CFSG.Quasithin
