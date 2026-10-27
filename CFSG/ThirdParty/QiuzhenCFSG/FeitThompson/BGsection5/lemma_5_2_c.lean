module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.lemma_5_2_b

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 5.2(c) from BG Section 5 -/

section

public theorem CFSG.lemma_5_2_c
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R) :
    (CΩ₁Z₂ p R).Characteristic ∧ (CΩ₁Z₂ p R).index = p := by
  classical
  let W : Subgroup R := Ω₁Z₂ p R
  let T : Subgroup R := CΩ₁Z₂ p R
  obtain ⟨_hZcard, hWmem⟩ := lemma_5_2_b (p := p) hpodd (R := R) hpR hR hE hEmax
  have hWchar : W.Characteristic := by
    simpa [W, Ω₁Z₂] using z2OmegaCandidate_characteristic (G := R) (p := p)
  letI : W.Characteristic := hWchar
  have hTchar : T.Characteristic := by
    simpa [T, CΩ₁Z₂] using (inferInstance : T.Characteristic)
  have hWcard : Nat.card W = p ^ 2 := hWmem.1
  have hWelem : IsElementaryAbelian p W := hWmem.2
  letI : IsElementaryAbelian p W := hWelem
  letI : W.Normal := by infer_instance
  let φ : R →* MulAut W := (MulAut.conjNormal (H := W))
  have hker : φ.ker = T := by
    ext r
    change (φ r = 1) ↔ r ∈ T
    constructor
    · intro hr
      change r ∈ Subgroup.centralizer (W : Set R)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      let wW : W := ⟨w, hw⟩
      have hfix : φ r wW = wW := by
        simpa using congrArg (fun f : MulAut W => f wW) hr
      have hconj : r * w * r⁻¹ = w := by
        simpa [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
      have hmul : w * r = r * w := by
        simpa [mul_assoc] using (congrArg (fun t : R => t * r) hconj).symm
      exact hmul
    · intro hr
      ext w
      have hrcent : r ∈ Subgroup.centralizer (W : Set R) := hr
      have hmul : ((w : W) : R) * r = r * ((w : W) : R) :=
        (Subgroup.mem_centralizer_iff.mp hrcent) ((w : W) : R) w.2
      have hconj : r * ((w : W) : R) * r⁻¹ = ((w : W) : R) := by
        calc
          r * ((w : W) : R) * r⁻¹ = ((w : W) : R) * r * r⁻¹ := by
            rw [hmul]
          _ = ((w : W) : R) := by simp [mul_assoc]
      simpa [φ, MulAut.conjNormal_apply] using hconj
  have hQp : IsPGroup p (R ⧸ φ.ker) := hpR.to_quotient (φ.ker)
  haveI : Fact (IsPGroup p (R ⧸ φ.ker)) := ⟨hQp⟩
  have hQodd : Odd (Nat.card (R ⧸ φ.ker)) := by
    rcases hQp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (show Odd p from (Fact.out : Nat.Prime p).odd_of_ne_two hpodd).pow
  have hQle : Nat.card (R ⧸ T) ≤ p := by
    simpa [hker] using
      quotient_centralizer_card_le_p_of_elementaryAbelian_rank_two
        (p := p) (E := W) (Q := R ⧸ φ.ker) hWcard hQodd
        (i := QuotientGroup.kerLift φ) (hi := QuotientGroup.kerLift_injective (φ := φ))
  haveI : T.Normal := by
    rw [← hker]
    infer_instance
  have hT_ne_top : T ≠ ⊤ := by
    intro hTtop
    have hE_le_T : E ≤ T := by
      rw [hTtop]
      exact le_top
    exact lemma_5_2_a (p := p) hpodd (R := R) hpR hR hE hEmax hE_le_T
  have hQ_nontrivial : Nontrivial (R ⧸ T) := by
    simpa using (QuotientGroup.nontrivial_iff (G := R) (N := T)).2 hT_ne_top
  have hQcard_eq_p : Nat.card (R ⧸ T) = p := by
    have hQp' : IsPGroup p (R ⧸ T) := hpR.to_quotient T
    rcases hQp'.exists_card_eq with ⟨k, hk⟩
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      have hcard_one : Nat.card (R ⧸ T) = 1 := by simpa [hk0] using hk
      haveI : Nontrivial (R ⧸ T) := hQ_nontrivial
      exact Nat.ne_of_gt Finite.one_lt_card hcard_one
    have hk_le_one : k ≤ 1 := by
      rw [hk] at hQle
      have hpow : p ^ k ≤ p ^ 1 := by simpa using hQle
      exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
    have hk_one : k = 1 := by omega
    simpa [hk_one] using hk
  exact ⟨hTchar, by rw [Subgroup.index_eq_card]; exact hQcard_eq_p⟩

end
