module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Fit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Gl2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Mult
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Pure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_isSL2Prime_of_cover {Y B : Type} [Group Y] [Finite Y]
    [Group B] (hY : commutator Y = ⊤) (Z : Subgroup Y) [Z.Normal] (hZ : Z ≤ Subgroup.center Y)
    (hq : IsAlt (Y ⧸ Z) 5) (f : Y →* B) (hf : Function.Surjective f) (hB : IsSL2Prime B 5) :
    IsSL2Prime Y 5 := by
  obtain ⟨K, hKf, hKfin, hK5, ⟨e⟩⟩ := hB
  have hBcard : Nat.card B = 120 := by
    letI : Field K := hKf
    letI : Finite K := hKfin
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hK5]
    norm_num
  have hZcard : Nat.card Z ≤ 2 := a5_central_card_le_two Z hZ hY hq
  have hqcard : Nat.card (Y ⧸ Z) = 60 := by
    obtain ⟨eZ⟩ := hq
    rw [Nat.card_congr eZ.toEquiv, CFSG.Quasithin.Dickson.card_alt_five]
  have hYcard : Nat.card Y = Nat.card (Y ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hYle : Nat.card Y ≤ 120 := by
    calc Nat.card Y = Nat.card (Y ⧸ Z) * Nat.card Z := hYcard
      _ = 60 * Nat.card Z := by rw [hqcard]
      _ ≤ 60 * 2 := Nat.mul_le_mul_left 60 hZcard
      _ = 120 := by norm_num
  have hYB : Nat.card Y ≤ Nat.card B := by rw [hBcard]; exact hYle
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le hYB
  exact ⟨K, hKf, hKfin, hK5, ⟨(MulEquiv.ofBijective f hbij).trans e⟩⟩

private lemma r925_orderOf_eq_two_pow_of_mem {G : Type} [Group G] {Y : Subgroup G}
    {Z : Subgroup Y} (hZ : IsPGroup 2 Z) {z : Y} (hz : z ∈ Z) :
    ∃ k : ℕ, orderOf (z : G) = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ (⟨z, hz⟩ : Z)
  refine ⟨k, ?_⟩
  calc orderOf (z : G) = orderOf z := Subgroup.orderOf_coe (H := Y) z
    _ = orderOf (⟨z, hz⟩ : Z) := (Subgroup.orderOf_mk (H := Z) z hz).symm
    _ = 2 ^ k := hk

private lemma r925_not_three_dvd_orderOf_of_two {G : Type} [Group G] {Z : Subgroup G}
    (hZ : IsPGroup 2 Z) : ∀ z ∈ Z, ¬ 3 ∣ orderOf z := by
  intro z hz hdiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ (⟨z, hz⟩ : Z)
  have hk' : orderOf z = 2 ^ k := (Subgroup.orderOf_mk z hz).symm.trans hk
  rw [hk'] at hdiv
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hdiv) (by norm_num)

theorem r925_im_o2_central {Γ : Type} [Group Γ] [Finite Γ]
    {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hbot : Y ⊓ centralizer (r925PCoreGe5 Γ : Set Γ) = ⊥) (Z : Subgroup ↥Y) [Z.Normal]
    (hZ : IsPGroup 2 Z) (hq : IsAlt (↥Y ⧸ Z) 5) : Z ≤ Subgroup.center ↥Y := by
  obtain ⟨ψ, hψ⟩ := r925_pcore_reps h.rank_gt_three
  have hW : ∀ w ∈ Z, ¬ 3 ∣ orderOf w := r925_not_three_dvd_orderOf_of_two hZ
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  let c : ↥Y := z * y * z⁻¹ * y⁻¹
  have hcZ : c ∈ Z := by
    have hconj : y * z * y⁻¹ ∈ Z := (inferInstance : Z.Normal).conj_mem z hz y
    have h2 : z * (y * z * y⁻¹)⁻¹ ∈ Z := mul_mem hz (inv_mem hconj)
    rwa [show z * (y * z * y⁻¹)⁻¹ = z * y * z⁻¹ * y⁻¹ by group] at h2
  have hcenter : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      ∀ x ∈ CFSG.pCore p.1 Γ, (c : Γ) * x = x * (c : Γ) := by
    intro p x hx
    haveI : Fact p.1.Prime := ⟨p.2.1⟩
    let ψp : ↥Y →* GL (Fin 2) (ZMod p.1) := (ψ p).comp Y.subtype
    have hcommGL : ψp z * ψp y = ψp y * ψp z := by
      rcases r925_gl2_of_a5 h.y_cover.1 Z hW hq p.1 p.2.2 ψp with h1 | ⟨-, hcent⟩
      · rw [h1]; simp
      · exact hcent z hz y
    have hψc : ψ p (c : Γ) = 1 := by
      have hmap : ψp c = ψ p (c : Γ) := rfl
      rw [← hmap]
      show ψp (z * y * z⁻¹ * y⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommGL]
      group
    obtain ⟨k, hk⟩ := r925_orderOf_eq_two_pow_of_mem hZ hcZ
    have hnotp : ¬ p.1 ∣ orderOf (c : Γ) := by
      rw [hk]
      intro hdiv
      have hp2 : p.1 ∣ 2 := p.2.1.dvd_of_dvd_pow hdiv
      rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h1 | h1
      · exact p.2.1.ne_one h1
      · omega
    exact (hψ p).1 (c : Γ) hψc hnotp x hx
  have hA : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a ∈ Subgroup.zpowers (c : Γ),
      ∀ x ∈ CFSG.pCore p Γ, a * x = x * a := by
    intro p hp h5 a ha x hx
    haveI : Fact p.Prime := ⟨hp⟩
    have hmem : (c : Γ) ∈ Subgroup.centralizer (CFSG.pCore p Γ : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcenter ⟨p, ⟨hp, h5⟩⟩ x hx).symm)
    have hle : Subgroup.zpowers (c : Γ) ≤
        Subgroup.centralizer (CFSG.pCore p Γ : Set Γ) := Subgroup.zpowers_le.mpr hmem
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) x hx).symm
  have hcentZ : ∀ a ∈ Subgroup.zpowers (c : Γ), ∀ x ∈ r925PCoreGe5 Γ, a * x = x * a :=
    r925_centralizes_pCoreGe5 (Subgroup.zpowers (c : Γ)) hA
  have hc1 : c = 1 := by
    have hmem : (c : Γ) ∈ Y ⊓ centralizer (r925PCoreGe5 Γ : Set Γ) :=
      Subgroup.mem_inf.mpr ⟨c.2, Subgroup.mem_centralizer_iff.mpr
        (fun x hx => (hcentZ (c : Γ) (Subgroup.mem_zpowers _) x hx).symm)⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hzy : z * y = y * z := by
    have hc' : z * y * z⁻¹ * y⁻¹ = 1 := hc1
    calc z * y = z * y * z⁻¹ * y⁻¹ * (y * z) := by group
      _ = 1 * (y * z) := by rw [hc']
      _ = y * z := one_mul _
  exact hzy.symm

theorem r925_im_sl2_image {Γ : Type} [Group Γ] [Finite Γ]
    {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hbot : Y ⊓ centralizer (r925PCoreGe5 Γ : Set Γ) = ⊥) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ψ : ↥Y →* GL (Fin 2) (ZMod p)), IsSL2Prime ↥ψ.range 5 := by
  obtain ⟨Z, hZn, hZ2, hZq⟩ := h.y_cover.2
  haveI := hZn
  obtain ⟨ψ, hψ⟩ := r925_pcore_reps h.rank_gt_three
  have hW : ∀ w ∈ Z, ¬ 3 ∣ orderOf w := r925_not_three_dvd_orderOf_of_two hZ2
  have hex : ∃ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
      IsSL2Prime ↥((ψ p).comp Y.subtype).range 5 := by
    by_contra hnone
    push Not at hnone
    have htriv : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (ψ p).comp Y.subtype = 1 := by
      intro p
      haveI : Fact p.1.Prime := ⟨p.2.1⟩
      rcases r925_gl2_of_a5 h.y_cover.1 Z hW hZq p.1 p.2.2
        ((ψ p).comp Y.subtype) with h1 | ⟨hsl, -⟩
      · exact h1
      · exact absurd hsl (hnone p)
    have hall : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a ∈ Y, ∀ x ∈ CFSG.pCore p Γ, a * x = x * a := by
      intro p hp h5 a ha x hx
      haveI : Fact p.Prime := ⟨hp⟩
      have hcomp := htriv ⟨p, ⟨hp, h5⟩⟩
      have h1 : ∀ b ∈ Y, ψ ⟨p, ⟨hp, h5⟩⟩ b = 1 := by
        intro b hb
        have hbx := DFunLike.congr_fun hcomp ⟨b, hb⟩
        simpa using hbx
      exact r925_pcore_centralized_of_rep p h5 h.y_cover.isThreeGen
        (hψ ⟨p, ⟨hp, h5⟩⟩).1 h1 a ha x hx
    have hYcent : Y ≤ Subgroup.centralizer (r925PCoreGe5 Γ : Set Γ) := by
      intro a ha
      exact Subgroup.mem_centralizer_iff.mpr
        (fun x hx => (r925_centralizes_pCoreGe5 Y hall a ha x hx).symm)
    have hYbot : Y = ⊥ := by
      have h := inf_eq_left.mpr hYcent
      rw [hbot] at h
      exact h.symm
    have h3 : 3 ∣ Nat.card ↥Y := by
      obtain ⟨D, hD⟩ := h.y_cover.exists_card_three
      have hdvd := Subgroup.card_dvd_of_le (le_top : D ≤ ⊤)
      rw [Subgroup.card_top, hD] at hdvd
      exact hdvd
    rw [hYbot, Subgroup.card_bot] at h3
    norm_num at h3
  obtain ⟨p, hp⟩ := hex
  exact ⟨p.1, ⟨p.2.1⟩, (ψ p).comp Y.subtype, hp⟩

theorem r925_im_sl2 {Γ : Type}
    [Group Γ] [Finite Γ] {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hbot : Y ⊓ centralizer (r925PCoreGe5 Γ : Set Γ) = ⊥) : IsSL2Prime ↥Y 5 := by
  obtain ⟨Z, hZn, hZ2, hZq⟩ := h.y_cover.2
  obtain ⟨p, hp, ψ, hψ⟩ := r925_im_sl2_image h hbot
  exact r925_isSL2Prime_of_cover h.y_cover.1 Z (r925_im_o2_central h hbot Z hZ2 hZq) hZq
    ψ.rangeRestrict ψ.rangeRestrict_surjective hψ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
