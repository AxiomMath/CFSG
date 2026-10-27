module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGWeylCartan
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTriplePair
import CFSG.LocalAnalysis.StandardType.GGKGPosRootPairs

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.OfCartan

private theorem ggWeylTriAux_conj_simple_sq {ι : Type} (M : CoxeterMatrix ι) (w : M.Group) (i : ι) :
    (w * M.simple i * w⁻¹) ^ 2 = 1 := by
  rw [conj_pow, show M.simple i ^ 2 = 1 from M.toCoxeterSystem.simple_sq i, mul_one,
    mul_inv_cancel]

private theorem ggWeylTriAux_symmetrizer_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hCart : GGIntCartan (coxeterMatrix hC) C)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hC)) (i j : ι) :
    symmetrizer hC i = symmetrizer hC j := by
  have hedge : ∀ {a b : ι}, (coxeterMatrix hC).M a b = 3 →
      symmetrizer hC a = symmetrizer hC b := by
    intro a b hab
    have hab_ne : a ≠ b := by
      rintro rfl
      rw [CoxeterMatrix.diagonal] at hab
      norm_num at hab
    have hsym : symmetrizer hC a * (C a b : ℚ) = symmetrizer hC b * (C b a : ℚ) := by
      have h := form_comm hC (Pi.single a 1) (Pi.single b 1)
      have h1 : form hC (Pi.single a 1) (Pi.single b 1) =
          symmetrizer hC a * (C a b : ℚ) := by
        rw [form_single_left]; congr 1; simp [Pi.single_apply]
      have h2 : form hC (Pi.single b 1) (Pi.single a 1) =
          symmetrizer hC b * (C b a : ℚ) := by
        rw [form_single_left]; congr 1; simp [Pi.single_apply]
      rwa [h1, h2] at h
    rcases hCart.2 a b hab_ne with ⟨hm, -, -⟩ | ⟨hm, h1, h2⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
    · rw [hm] at hab; norm_num at hab
    · have h' : symmetrizer hC a * (-1 : ℚ) = symmetrizer hC b * (-1 : ℚ) := by
        simpa [h1, h2] using hsym
      linarith
    · rw [hm] at hab; norm_num at hab
    · rw [hm] at hab; norm_num at hab
  have hpath := hconn.2 i j
  induction hpath with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hedge hstep)

private theorem ggWeylTriAux_root_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) {d : ℚ}
    (hd : ∀ k, symmetrizer hC k = d) (g : (coxeterMatrix hC).Group) (i : ι) :
    form hC (toRat (CoxTriple.coxRoot hC g i)) (toRat (CoxTriple.coxRoot hC g i)) = 2 * d := by
  rw [CoxTriple.coxRoot, form_weylAction_single_self hC g i, hd i]

private theorem ggWeylTriAux_form_eq_coxPairing_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) {d : ℚ}
    (hd : ∀ k, symmetrizer hC k = d) (hd0 : 0 < d)
    (g h : (coxeterMatrix hC).Group) (i j : ι) :
    form hC (toRat (CoxTriple.coxRoot hC g i)) (toRat (CoxTriple.coxRoot hC h j)) =
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g i) (CoxTriple.coxRoot hC h j) * d := by
  rw [CoxTriple.coxPairing, ggWeylTriAux_root_norm hC hd h j]
  field_simp [ne_of_gt hd0]

private theorem ggWeylTriAux_coxPairing_comm {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) {d : ℚ}
    (hd : ∀ k, symmetrizer hC k = d)
    (g h : (coxeterMatrix hC).Group) (i j : ι) :
    CoxTriple.coxPairing hC (CoxTriple.coxRoot hC h j) (CoxTriple.coxRoot hC g i) =
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g i) (CoxTriple.coxRoot hC h j) := by
  have hdeni := ggWeylTriAux_root_norm hC hd g i
  have hdenj := ggWeylTriAux_root_norm hC hd h j
  rw [CoxTriple.coxPairing, CoxTriple.coxPairing, hdeni, hdenj]
  rw [form_comm hC (toRat (CoxTriple.coxRoot hC g i)) (toRat (CoxTriple.coxRoot hC h j))]

private theorem ggWeylTriAux_coxPairing_mul_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hC))
    (g h : (coxeterMatrix hC).Group) (i j : ι)
    (hnc : ¬ Commute (CoxTriple.coxRefl hC g i) (CoxTriple.coxRefl hC h j)) :
    CoxTriple.coxPairing hC (CoxTriple.coxRoot hC h j) (CoxTriple.coxRoot hC g i) *
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g i) (CoxTriple.coxRoot hC h j) = 1 := by
  have hnp : ¬ ∃ q : ℚ, toRat (CoxTriple.coxRoot hC h j) =
      q • toRat (CoxTriple.coxRoot hC g i) := by
    rintro ⟨q, hq⟩
    exact hnc (by rw [CoxTriple.coxRefl_eq_of_proportional hC g h i j q hq])
  have h3 : (CoxTriple.coxRefl hC g i * CoxTriple.coxRefl hC h j) ^ 3 = 1 := by
    simpa only [CoxTriple.coxRefl] using
      ggWeyl_refl_order3 hC hconn g h i j (by simpa only [CoxTriple.coxRefl] using hnc)
  have hdvd : orderOf (CoxTriple.coxRefl hC g i * CoxTriple.coxRefl hC h j) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr h3
  have hord : orderOf (CoxTriple.coxRefl hC g i * CoxTriple.coxRefl hC h j) = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3'
    · exfalso
      rw [orderOf_eq_one_iff] at h1
      exact hnc (show CoxTriple.coxRefl hC g i * CoxTriple.coxRefl hC h j =
          CoxTriple.coxRefl hC h j * CoxTriple.coxRefl hC g i by
        rw [h1, show CoxTriple.coxRefl hC h j * CoxTriple.coxRefl hC g i = 1 by
          rw [← inv_eq_of_mul_eq_one_right h1]
          exact inv_mul_cancel _])
    · exact h3'
  have hA4 := CoxTriple.orderOf_coxRefl_mul hC g h i j hnp
  rcases CoxTriple.coxPairing_mul_cases hC g h i j hnp with h0 | h1 | h2 | h3s
  · exfalso; have := hA4.1 h0; omega
  · exact h1
  · exfalso; have := hA4.2.2.1 h2; omega
  · exfalso; have := hA4.2.2.2 h3s; omega

private theorem ggWeylTriAux_coxPairing_sq_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hC))
    (g h : (coxeterMatrix hC).Group) (i j : ι)
    (hnc : ¬ Commute (CoxTriple.coxRefl hC g i) (CoxTriple.coxRefl hC h j)) :
    CoxTriple.coxPairing hC (CoxTriple.coxRoot hC h j) (CoxTriple.coxRoot hC g i) *
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC h j) (CoxTriple.coxRoot hC g i) = 1 := by
  have hprod := ggWeylTriAux_coxPairing_mul_eq_one hC hconn g h i j hnc
  obtain ⟨p, hp⟩ := CoxTriple.exists_int_coxPairing hC g i (CoxTriple.coxRoot hC h j)
  obtain ⟨q, hq⟩ := CoxTriple.exists_int_coxPairing hC h j (CoxTriple.coxRoot hC g i)
  have hpq : p * q = 1 := by
    have : (p : ℚ) * (q : ℚ) = 1 := by rw [hp, hq]; exact hprod
    exact_mod_cast this
  have hpp : p * p = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hpq with h | h <;> rw [h] <;> norm_num
  rw [← hp]
  exact_mod_cast hpp

private theorem ggWeylTriAux_pairing_arith {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hsymm : ∀ x y, B x y = B y x)
    (hpos : ∀ x : V, B x x = 0 → x = 0)
    {L p a b : ℚ} {α β γ : V}
    (hα : B α α = L) (hβ : B β β = L) (hγ : B γ γ = L)
    (hp : B α β = p * L / 2) (hp2 : p * p = 1)
    (ha : B γ α = a * L / 2) (ha2 : a * a = 1)
    (hb : B γ β = b * L / 2) (hb2 : b * b = 1) :
    B γ (β - p • α) = 0 ∨ γ = β - p • α ∨ γ = -(β - p • α) := by
  have hpv : p = 1 ∨ p = -1 := by
    have h : (p - 1) * (p + 1) = 0 := by nlinarith [hp2]
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    · right; linarith
  have hav : a = 1 ∨ a = -1 := by
    have h : (a - 1) * (a + 1) = 0 := by nlinarith [ha2]
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    · right; linarith
  have hbv : b = 1 ∨ b = -1 := by
    have h : (b - 1) * (b + 1) = 0 := by nlinarith [hb2]
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    · right; linarith
  have hs : b - p * a = 0 ∨ b - p * a = 2 ∨ b - p * a = -2 := by
    rcases hpv with rfl | rfl <;> rcases hav with rfl | rfl <;> rcases hbv with rfl | rfl <;>
      norm_num
  set δ : V := β - p • α with hδ
  have hcenter : B γ δ = (b - p * a) * L / 2 := by
    rw [hδ]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hb, ha]; ring
  have hnormδ : B δ δ = L := by
    rw [hδ]
    have hexp : B (β - p • α) (β - p • α) =
        B β β - p * B β α - p * B α β + p * p * B α α := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hexp, hβ, hα, hsymm β α, hp]
    nlinarith [hp2]
  have hquad : B (γ - δ) (γ - δ) = 2 * L - 2 * B γ δ := by
    have hexp : B (γ - δ) (γ - δ) = B γ γ - B γ δ - B δ γ + B δ δ := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [hexp, hγ, hnormδ, hsymm δ γ]
    ring
  have hquad' : B (γ + δ) (γ + δ) = 2 * L + 2 * B γ δ := by
    have hexp : B (γ + δ) (γ + δ) = B γ γ + B γ δ + B δ γ + B δ δ := by
      simp only [map_add, LinearMap.add_apply]
      ring
    rw [hexp, hγ, hnormδ, hsymm δ γ]
    ring
  rcases hs with hs | hs | hs
  · left
    rw [hcenter, hs]; ring
  · right; left
    have hz : B (γ - δ) (γ - δ) = 0 := by rw [hquad, hcenter, hs]; ring
    exact sub_eq_zero.mp (hpos (γ - δ) hz)
  · right; right
    have hz : B (γ + δ) (γ + δ) = 0 := by rw [hquad', hcenter, hs]; ring
    exact eq_neg_of_add_eq_zero_left (hpos (γ + δ) hz)

private theorem ggWeylTriAux_fourth_root {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hC))
    {d : ℚ} (hd : ∀ k, symmetrizer hC k = d) (hd0 : 0 < d)
    (g₁ g₂ g₄ : (coxeterMatrix hC).Group) (i₁ i₂ i₄ : ι)
    (hnc₁₂ : ¬ Commute (CoxTriple.coxRefl hC g₁ i₁) (CoxTriple.coxRefl hC g₂ i₂))
    (hnc₁₄ : ¬ Commute (CoxTriple.coxRefl hC g₁ i₁) (CoxTriple.coxRefl hC g₄ i₄))
    (hnc₂₄ : ¬ Commute (CoxTriple.coxRefl hC g₂ i₂) (CoxTriple.coxRefl hC g₄ i₄)) :
    form hC (toRat (CoxTriple.coxRoot hC g₄ i₄))
        (toRat (CoxTriple.coxRoot hC (CoxTriple.coxRefl hC g₁ i₁ * g₂) i₂)) = 0 ∨
      CoxTriple.coxRefl hC g₄ i₄ =
        CoxTriple.coxRefl hC (CoxTriple.coxRefl hC g₁ i₁ * g₂) i₂ := by
  set α : ι → ℚ := toRat (CoxTriple.coxRoot hC g₁ i₁) with hαdef
  set β : ι → ℚ := toRat (CoxTriple.coxRoot hC g₂ i₂) with hβdef
  set γ : ι → ℚ := toRat (CoxTriple.coxRoot hC g₄ i₄) with hγdef
  set u₃ : ι → ℤ := CoxTriple.coxRoot hC (CoxTriple.coxRefl hC g₁ i₁ * g₂) i₂ with hu₃def
  have hp2 : CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₂ i₂)
      (CoxTriple.coxRoot hC g₁ i₁) *
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₂ i₂) (CoxTriple.coxRoot hC g₁ i₁) = 1 :=
    ggWeylTriAux_coxPairing_sq_eq_one hC hconn g₁ g₂ i₁ i₂ hnc₁₂
  have ha2 : CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄)
      (CoxTriple.coxRoot hC g₁ i₁) *
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄) (CoxTriple.coxRoot hC g₁ i₁) = 1 :=
    ggWeylTriAux_coxPairing_sq_eq_one hC hconn g₁ g₄ i₁ i₄ hnc₁₄
  have hb2 : CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄)
      (CoxTriple.coxRoot hC g₂ i₂) *
      CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄) (CoxTriple.coxRoot hC g₂ i₂) = 1 :=
    ggWeylTriAux_coxPairing_sq_eq_one hC hconn g₂ g₄ i₂ i₄ hnc₂₄
  have hformα : form hC α α = 2 * d := ggWeylTriAux_root_norm hC hd g₁ i₁
  have hformβ : form hC β β = 2 * d := ggWeylTriAux_root_norm hC hd g₂ i₂
  have hformγ : form hC γ γ = 2 * d := ggWeylTriAux_root_norm hC hd g₄ i₄
  have hpform : form hC α β = CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₂ i₂)
      (CoxTriple.coxRoot hC g₁ i₁) * (2 * d) / 2 := by
    rw [show CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₂ i₂) (CoxTriple.coxRoot hC g₁ i₁) *
        (2 * d) / 2 = CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₂ i₂)
          (CoxTriple.coxRoot hC g₁ i₁) * d by ring,
      ggWeylTriAux_coxPairing_comm hC hd g₁ g₂ i₁ i₂]
    rw [hαdef, hβdef]
    exact ggWeylTriAux_form_eq_coxPairing_mul hC hd hd0 g₁ g₂ i₁ i₂
  have haform : form hC γ α = CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄)
      (CoxTriple.coxRoot hC g₁ i₁) * (2 * d) / 2 := by
    rw [show CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄) (CoxTriple.coxRoot hC g₁ i₁) *
        (2 * d) / 2 = CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄)
          (CoxTriple.coxRoot hC g₁ i₁) * d by ring,
      hγdef, hαdef]
    exact ggWeylTriAux_form_eq_coxPairing_mul hC hd hd0 g₄ g₁ i₄ i₁
  have hbform : form hC γ β = CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄)
      (CoxTriple.coxRoot hC g₂ i₂) * (2 * d) / 2 := by
    rw [show CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄) (CoxTriple.coxRoot hC g₂ i₂) *
        (2 * d) / 2 = CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₄ i₄)
          (CoxTriple.coxRoot hC g₂ i₂) * d by ring,
      hγdef, hβdef]
    exact ggWeylTriAux_form_eq_coxPairing_mul hC hd hd0 g₄ g₂ i₄ i₂
  have hρ₃ : toRat u₃ = β - CoxTriple.coxPairing hC (CoxTriple.coxRoot hC g₂ i₂)
      (CoxTriple.coxRoot hC g₁ i₁) • α := by
    have hmul : u₃ = weylAction hC (CoxTriple.coxRefl hC g₁ i₁)
        (CoxTriple.coxRoot hC g₂ i₂) := by
      rw [hu₃def]
      simpa only [CoxTriple.coxRoot] using
        weylAction_mul_apply hC (CoxTriple.coxRefl hC g₁ i₁) g₂ (Pi.single i₂ 1)
    rw [hmul, CoxTriple.toRat_weylAction_coxRefl hC g₁ i₁ (CoxTriple.coxRoot hC g₂ i₂),
      ← hβdef, ← hαdef]
  rcases ggWeylTriAux_pairing_arith (form hC) (form_comm hC) (fun x hx => by
      by_contra hx0
      exact (lt_irrefl 0) (hx ▸ form_pos hC hx0))
      hformα hformβ hformγ hpform hp2 haform ha2 hbform hb2 with h | h | h
  · left
    rw [hρ₃]
    exact h
  · right
    refine CoxTriple.coxRefl_eq_of_proportional hC
      (CoxTriple.coxRefl hC g₁ i₁ * g₂) g₄ i₂ i₄ 1 ?_
    rw [one_smul]
    rw [← hρ₃, hγdef] at h
    exact h
  · right
    refine CoxTriple.coxRefl_eq_of_proportional hC
      (CoxTriple.coxRefl hC g₁ i₁ * g₂) g₄ i₂ i₄ (-1) ?_
    rw [neg_one_smul]
    rw [← hρ₃, hγdef] at h
    exact h

theorem ggWeyl_triple_of_pairwise_noncomm {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (R : Set M.Group) (hR : ∀ t ∈ R, ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (hcl : ∀ t ∈ R, ∀ t' ∈ R, t * t' * t⁻¹ ∈ R)
    (hnc : ∀ t ∈ R, ∀ t' ∈ R, t ≠ t' → t * t' ≠ t' * t) :
    R = ∅ ∨ ∃ t₁ ∈ R, ∃ t₂ ∈ R, R ⊆ {t₁, t₂, t₁ * t₂ * t₁} := by
  classical
  rcases Set.eq_empty_or_nonempty R with h | ⟨t₁, ht₁⟩
  · exact Or.inl h
  · by_cases hsingle : ∀ t ∈ R, t = t₁
    · refine Or.inr ⟨t₁, ht₁, t₁, ht₁, ?_⟩
      intro x hx
      rw [hsingle x hx]
      exact Or.inl rfl
    · push Not at hsingle
      obtain ⟨t₂, ht₂, ht₂ne⟩ := hsingle
      haveI : Finite ι := ggIsWeylMatrix_finite hM
      haveI : Fintype ι := Fintype.ofFinite ι
      obtain ⟨C, hC, hCart, rfl⟩ := ggWeylCartan hM hle3
      have hconn : GGSimplyLacedConnected (coxeterMatrix hC) :=
        ggSimplyLacedConnected_of_weyl hM hle3
      obtain ⟨g₁, i₁, ht₁eq⟩ := hR t₁ ht₁
      obtain ⟨g₂, i₂, ht₂eq⟩ := hR t₂ ht₂
      have hT₁ : CoxTriple.coxRefl hC g₁ i₁ = t₁ := by rw [ht₁eq]; rfl
      have hT₂ : CoxTriple.coxRefl hC g₂ i₂ = t₂ := by rw [ht₂eq]; rfl
      have ht₁sq : t₁ * t₁ = 1 := by
        have h := ggWeylTriAux_conj_simple_sq (coxeterMatrix hC) g₁ i₁
        rw [ht₁eq]
        simpa [pow_two] using h
      have hinv₁ : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁sq
      let t₃ : (coxeterMatrix hC).Group := t₁ * t₂ * t₁
      have ht₃ : t₃ ∈ R := by
        have := hcl t₁ ht₁ t₂ ht₂
        simpa [t₃, hinv₁] using this
      have hT₃ : CoxTriple.coxRefl hC (CoxTriple.coxRefl hC g₁ i₁ * g₂) i₂ = t₃ := by
        have hcc : CoxTriple.coxRefl hC (CoxTriple.coxRefl hC g₁ i₁ * g₂) i₂ =
            CoxTriple.coxRefl hC g₁ i₁ * CoxTriple.coxRefl hC g₂ i₂ *
              (CoxTriple.coxRefl hC g₁ i₁)⁻¹ := by
          simp only [CoxTriple.coxRefl]
          group
        rw [hcc, hT₁, hT₂, hinv₁]
      refine Or.inr ⟨t₁, ht₁, t₂, ht₂, ?_⟩
      intro t₄ ht₄
      by_contra hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      obtain ⟨ht₄ne₁, ht₄ne₂, ht₄ne₃⟩ := hmem
      obtain ⟨g₄, i₄, ht₄eq⟩ := hR t₄ ht₄
      have hT₄ : CoxTriple.coxRefl hC g₄ i₄ = t₄ := by rw [ht₄eq]; rfl
      have hnc₁₂ : ¬ Commute (CoxTriple.coxRefl hC g₁ i₁) (CoxTriple.coxRefl hC g₂ i₂) := by
        rw [hT₁, hT₂]
        exact hnc t₁ ht₁ t₂ ht₂ (Ne.symm ht₂ne)
      have hnc₁₄ : ¬ Commute (CoxTriple.coxRefl hC g₁ i₁) (CoxTriple.coxRefl hC g₄ i₄) := by
        rw [hT₁, hT₄]
        exact fun hc => hnc t₄ ht₄ t₁ ht₁ ht₄ne₁ hc.symm
      have hnc₂₄ : ¬ Commute (CoxTriple.coxRefl hC g₂ i₂) (CoxTriple.coxRefl hC g₄ i₄) := by
        rw [hT₂, hT₄]
        exact fun hc => hnc t₄ ht₄ t₂ ht₂ ht₄ne₂ hc.symm
      have hd : ∀ k, symmetrizer hC k = symmetrizer hC i₁ :=
        fun k => ggWeylTriAux_symmetrizer_eq hC hCart hconn k i₁
      have hd0 : 0 < symmetrizer hC i₁ := symmetrizer_pos hC i₁
      rcases ggWeylTriAux_fourth_root hC hconn hd hd0 g₁ g₂ g₄ i₁ i₂ i₄
        hnc₁₂ hnc₁₄ hnc₂₄ with hf | heq
      · have hcomm := CoxTriple.commute_coxRefl_of_form_eq_zero hC g₄
          (CoxTriple.coxRefl hC g₁ i₁ * g₂) i₄ i₂ hf
        rw [hT₄, hT₃] at hcomm
        exact hnc t₄ ht₄ t₃ ht₃ ht₄ne₃ hcomm
      · rw [hT₄, hT₃] at heq
        exact ht₄ne₃ heq

end CFSG.StandardType

end
