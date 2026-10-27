module

public import Certificates.Certificate4219
public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.Quasithin.J4Seven

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

theorem chkSeven_parts :
    eqRows (powRows sevenR 7) idRows = true ∧ eqRows sevenR idRows = false ∧
    (sevenR.size = 112 ∧ ∀ v ∈ sevenR, v.wf = true) ∧
    vorbOK locTabsS rep5S orbS5 15180 = true ∧
    (∀ v, v ∈ fixedS sevenR orbS5 ↔ v ∈ sevenFix) ∧ (∀ v ∈ sevenFix, v.wf = true) ∧
    rootV.wf = true ∧ (∀ v ∈ sevenFix, v.beq rootV = false) ∧
    (∀ i < 4, ∀ j < 4, i ≠ j →
      (sevenFix.getD i rootV).beq (sevenFix.getD j rootV) = false) ∧
    (∀ c < 2048, actMask c = actX c ∧ actMask c < 2048) ∧
    (∀ k ∈ List.range' 1 6, cntF k ≠ cntFs k) :=
  Certificates.certificate4219

@[expose] noncomputable def sevenElt : J := xJ 2 ^ 3

theorem sevenElt_mem_Hj : sevenElt ∈ Hj :=
  Subgroup.pow_mem _ (xJ_mem (by norm_num)) 3

theorem Mx_x2 (hM : MatFacts) : Mx (xJ 2) = rowsMatrix x2R := by
  have h := locMats_spec hM 2
  rw [Mx_apply]
  have hs : 2 < (locMats ()).size := by rw [hM.locSize]; norm_num
  rw [x2R, locM, getElem!_pos _ 2 hs, ← Option.getD_some (a := (locMats ())[2]) (b := idRows),
    ← Array.getElem?_eq_getElem hs]
  exact h.symm

theorem Mx_sevenElt (hM : MatFacts) : Mx sevenElt = rowsMatrix sevenR := by
  rw [sevenElt, map_pow, Mx_x2 hM, sevenR, rowsMatrix_powRows]

theorem orderOf_sevenElt (hM : MatFacts) : orderOf sevenElt = 7 := by
  obtain ⟨h1, h2, ⟨hs, hw⟩, -⟩ := chkSeven_parts
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Mx_injective
    rw [map_pow, Mx_sevenElt hM, ← rowsMatrix_powRows, map_one]
    rw [eqRows_iff.1 h1, rowsMatrix_idRows]
  · intro h
    have := congrArg Mx h
    rw [Mx_sevenElt hM, map_one, ← rowsMatrix_idRows] at this
    exact rowsMatrix_ne_of_eqRows_false hs idRows_size hw idRows_wf h2 this

theorem three_mem_letters : (3 : ℤ) ∈ letters := by simp [letters]

theorem conj_xJ_two_eta (hM : MatFacts) (c : ℕ) :
    xJ 2 * eta uJ 11 c * (xJ 2)⁻¹ = eta uJ 11 (act 3 c) := by
  rw [← XJ_three]
  exact hX_all hM three_mem_letters c

theorem conj_sevenElt_eta (hM : MatFacts) (c : ℕ) :
    sevenElt * eta uJ 11 c * sevenElt⁻¹ = eta uJ 11 (actX c) := by
  have h := conj_xJ_two_eta hM
  have hL : sevenElt = xJ 2 * (xJ 2 * xJ 2) := by rw [sevenElt, pow_three]
  have e : sevenElt * eta uJ 11 c * sevenElt⁻¹ =
      xJ 2 * (xJ 2 * (xJ 2 * eta uJ 11 c * (xJ 2)⁻¹) * (xJ 2)⁻¹) * (xJ 2)⁻¹ := by
    rw [hL]; group
  rw [e, h, h, h]
  rfl

theorem conj_sevenElt_pow_eta
    (hM : MatFacts) {c : ℕ} (hc : c < 2048) (j : ℕ) :
    sevenElt ^ j * eta uJ 11 c * (sevenElt ^ j)⁻¹ = eta uJ 11 (actIter j c) ∧
      actIter j c < 2048 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := chkSeven_parts
  induction j with
  | zero => simp [actIter, hc]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := h10 _ ih2
    refine ⟨?_, ?_⟩
    · have e : sevenElt ^ (j + 1) * eta uJ 11 c * (sevenElt ^ (j + 1))⁻¹ =
          sevenElt * (sevenElt ^ j * eta uJ 11 c * (sevenElt ^ j)⁻¹) * sevenElt⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih1, conj_sevenElt_eta hM]
      show eta uJ 11 (actX (actIter j c)) = eta uJ 11 (actMask (actIter j c))
      rw [h1]
    · exact h2

theorem sevenElt_pow_mem
    (hM : MatFacts) (n : ℕ) {e : J} (he : e ∈ Eg uJ 11) :
    sevenElt ^ n * e * (sevenElt ^ n)⁻¹ ∈ Eg uJ 11 := by
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 he
  have hc' : c < 2048 := by simpa using hc
  rw [(conj_sevenElt_pow_eta hM hc' n).1]
  exact eta_mem_Eg 11 le_rfl _

theorem eta_mul_eta' (hM : MatFacts) (c d : ℕ) :
    eta uJ 11 c * eta uJ 11 d = eta uJ 11 (c ^^^ d) :=
  (eta_xor (elem_uJ hM) le_rfl c d).symm

theorem ncard_maskSet (p : ℕ → Bool) :
    {c : ℕ | c < 2048 ∧ p c = true}.ncard = ((List.range 2048).filter p).length := by
  have : {c : ℕ | c < 2048 ∧ p c = true} = ↑(((List.range 2048).filter p).toFinset) := by
    ext c
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup (List.nodup_range.filter p)]

theorem ncard_kerSet
    (hM : MatFacts) (i j : ℕ) :
    {e : J | e ∈ Eg uJ 11 ∧ (sevenElt ^ i * e * (sevenElt ^ i)⁻¹) *
        (sevenElt ^ j * e * (sevenElt ^ j)⁻¹) * e = 1}.ncard =
      ((List.range 2048).filter fun c => (actIter i c ^^^ actIter j c ^^^ c) == 0).length := by
  have hset : {e : J | e ∈ Eg uJ 11 ∧ (sevenElt ^ i * e * (sevenElt ^ i)⁻¹) *
        (sevenElt ^ j * e * (sevenElt ^ j)⁻¹) * e = 1} =
      eta uJ 11 '' {c : ℕ | c < 2048 ∧ ((actIter i c ^^^ actIter j c ^^^ c) == 0) = true} := by
    ext e
    constructor
    · rintro ⟨heE, hprod⟩
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 heE
      have hc' : c < 2048 := by simpa using hc
      obtain ⟨hi, hi'⟩ := conj_sevenElt_pow_eta hM hc' i
      obtain ⟨hj, hj'⟩ := conj_sevenElt_pow_eta hM hc' j
      rw [hi, hj, eta_mul_eta' hM, eta_mul_eta' hM] at hprod
      refine ⟨c, ⟨hc', ?_⟩, rfl⟩
      have hlt : actIter i c ^^^ actIter j c ^^^ c < 2 ^ 11 :=
        Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hi' hj') hc
      rw [beq_iff_eq]
      by_contra hne
      exact eta_ne_one hM hne hlt hprod
    · rintro ⟨c, ⟨hc, h0⟩, rfl⟩
      refine ⟨eta_mem_Eg 11 le_rfl c, ?_⟩
      obtain ⟨hi, hi'⟩ := conj_sevenElt_pow_eta hM hc i
      obtain ⟨hj, hj'⟩ := conj_sevenElt_pow_eta hM hc j
      rw [hi, hj, eta_mul_eta' hM, eta_mul_eta' hM, beq_iff_eq.1 h0, eta_zero]
  rw [hset, Set.InjOn.ncard_image, ncard_maskSet]
  intro c hc d hd h
  exact eta_inj hM c hc.1 d hd.1 h

end CFSG.Quasithin.J4Seven
