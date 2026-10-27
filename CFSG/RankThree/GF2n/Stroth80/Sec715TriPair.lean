module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriBil
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriDescent
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriKegel

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small CFSG.StandardType.Triality

section Spin

variable {N : ℕ}

theorem tri_spin_parity_unique {b₀ : ZMod N} (hb : b₀ ≠ -b₀) {e e' : ℕ} (he : e < 2)
    (he' : e' < 2) (h : ∀ a, IsSpinWt b₀ e a ↔ IsSpinWt b₀ e' a) : e = e' := by
  have h1 := h (bilSpinW b₀ ∅)
  rw [bil_isSpinWt_spinW hb, bil_isSpinWt_spinW hb, Finset.card_empty] at h1
  omega

theorem tri_not_isSpinWt_single {b₀ : ZMod N} (hb : b₀ ≠ 0) (e : ℕ) :
    ¬ IsSpinWt b₀ e (Pi.single (0 : Fin 4) (1 : ZMod N)) := by
  intro h
  have h1 := h.1 1
  rw [Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 0)] at h1
  rcases h1 with h1 | h1
  · exact hb h1.symm
  · exact hb (neg_eq_zero.mp h1.symm)

end Spin

section Transport

variable {G : Type*} [Group G] {K : Type*} [Field K] {D : D4Datum G K} {X Z : Type*}
  [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module K Z] {ρX : Representation K G X}
  {ρZ : Representation K G Z} {j : ℕ} {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
  {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X}

theorem NF.map_equiv (hNF : NF D ρX j C b) (e : X ≃ₗ[K] Z)
    (he : ∀ (g : G) (x : X), e (ρX g x) = ρZ g (e x)) : NF D ρZ j C (fun a => e (b a)) where
  ne_zero a ha := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact hNF.ne_zero a ha
  mem_wtSpace a ha := by
    have h1 : b a ∈ D.wtSpace ρX a := hNF.mem_wtSpace a ha
    change ∀ t : Fin 4 → Kˣ, ρX (D.h t) (b a) = _ at h1
    change ∀ t : Fin 4 → Kˣ, ρZ (D.h t) (e (b a)) = _
    intro t
    rw [← he, h1 t, map_smul]
  span_eq := by
    rw [← Set.image_image, Submodule.span_image_linearEquiv, hNF.span_eq, Submodule.map_top,
      LinearEquiv.range]
  root α hα c a ha := by
    rw [← he, hNF.root α hα c a ha, map_add]
    congr 1
    split_ifs <;> simp

theorem tri_bil_ext {Y V : Type*} [AddCommGroup Y] [Module K Y] [AddCommGroup V] [Module K V]
    {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y} {CY : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    (hX : Submodule.span K (b '' (C : Set _)) = ⊤)
    (hY : Submodule.span K (bY '' (CY : Set _)) = ⊤) {β₁ β₂ : X →ₗ[K] Y →ₗ[K] V}
    (h : ∀ a ∈ C, ∀ y ∈ CY, β₁ (b a) (bY y) = β₂ (b a) (bY y)) : β₁ = β₂ := by
  refine LinearMap.ext_on hX ?_
  rintro _ ⟨a, ha, rfl⟩
  exact LinearMap.ext_on hY (by rintro _ ⟨y, hy, rfl⟩; exact h a ha y hy)

end Transport

section Pair

variable {K : Type} [Field K] {X Y : Type} [AddCommGroup X] [Module K X] [AddCommGroup Y]
  [Module K Y]

@[expose] def IsEquivBil (σX : Representation K (Om8 K) X) (σY : Representation K (Om8 K) Y)
    (β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) : Prop :=
  ∀ (g : Om8 K) (x : X) (y : Y), β (σX g x) (σY g y) = natRep K g (β x y)

theorem tri_nf_of_irr8 (hA : SmallNFStatement) [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    [FiniteDimensional K X] {σ : Representation K (Om8 K) X} (h : Om8Irr8 σ) :
    ∃ (j : ℕ) (C : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
      (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X),
      2 ^ j < Nat.card Kˣ ∧ NFType j C ∧ NF (om8Datum K) σ j C b :=
  hA (om8Datum K) hK σ h.irreducible h.exists_ne_one (by rw [h.finrank_eq]; norm_num)

variable [Finite K] [CharP K 2] (hA : SmallNFStatement) (hK : 4 ≤ Nat.card K)
  [FiniteDimensional K X] [FiniteDimensional K Y]
  {σX : Representation K (Om8 K) X} {σY : Representation K (Om8 K) Y}

include hA hK

theorem tri_no_nonzero_sq (hX : Om8Irr8 σX) (β' : X →ₗ[K] X →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hβ' : IsEquivBil σX σX β') : β' = 0 := by
  by_contra hne
  obtain ⟨j, C, b, hj, hXt, hNF⟩ := tri_nf_of_irr8 hA hK hX
  obtain ⟨-, -, b₀, e, hb₀, he, hC1, hC2, -⟩ := bil_of_nf hK (om8Datum K) hNF hXt hj hNF hXt hj
    (nf_natRep hK) (fun a => mem_natWts) β' hβ' hne
  obtain ⟨h3, -⟩ := bil_card_facts hK
  have hb : b₀ ≠ -b₀ := bil_ne_neg h3 (by rw [hb₀]; exact isUnit_one)
  have := tri_spin_parity_unique hb he (by omega) fun a => (hC1 a).symm.trans (hC2 a)
  omega

theorem tri_no_equiv_pair (hX : Om8Irr8 σX) {β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hβ : IsEquivBil σX σY β) (hβ0 : β ≠ 0) :
    ¬ ∃ e : X ≃ₗ[K] Y, ∀ (g : Om8 K) (x : X), e (σX g x) = σY g (e x) := by
  rintro ⟨e, he⟩
  have h2 : IsEquivBil σX σX (β.compl₂ (e : X →ₗ[K] Y)) := by
    intro g x x'
    simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
    rw [he, hβ]
  refine hβ0 ?_
  have h3 := tri_no_nonzero_sq hA hK hX _ h2
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨x', rfl⟩ := e.surjective y
  have h4 := LinearMap.congr_fun₂ h3 x x'
  simpa using h4

theorem tri_no_equiv_nat_left (hY : Om8Irr8 σY) {β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hβ : IsEquivBil σX σY β) (hβ0 : β ≠ 0) :
    ¬ ∃ e : X ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      ∀ (g : Om8 K) (x : X), e (σX g x) = natRep K g (e x) := by
  rintro ⟨e, he⟩
  obtain ⟨jY, CY, bY, hjY, hYt, hYNF⟩ := tri_nf_of_irr8 hA hK hY
  obtain ⟨h3, -⟩ := bil_card_facts hK
  have hNFX : NF (om8Datum K) σX 0 natWts (fun a => e.symm (natBasis a)) :=
    (nf_natRep hK).map_equiv e.symm fun g v => by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
  obtain ⟨-, -, b₀, e', hb₀, he', hC1, -⟩ := bil_of_nf hK (om8Datum K) hNFX nfType_natWts
    (by rw [pow_zero]; omega) hYNF hYt hjY (nf_natRep hK) (fun a => mem_natWts) β hβ hβ0
  have hmem : (Pi.single (0 : Fin 4) (1 : ZMod (Nat.card Kˣ))) ∈ natWts (K := K) :=
    mem_natWts.2 ⟨0, Or.inl rfl⟩
  exact tri_not_isSpinWt_single (bil_ne_zero_of_isUnit_two_mul h3
    (by rw [hb₀]; exact isUnit_one)) e' ((hC1 _).1 hmem)

theorem tri_no_equiv_nat_right (hX : Om8Irr8 σX) {β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hβ : IsEquivBil σX σY β) (hβ0 : β ≠ 0) :
    ¬ ∃ e : Y ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      ∀ (g : Om8 K) (y : Y), e (σY g y) = natRep K g (e y) := by
  rintro ⟨e, he⟩
  obtain ⟨jX, CX, bX, hjX, hXt, hXNF⟩ := tri_nf_of_irr8 hA hK hX
  obtain ⟨h3, -⟩ := bil_card_facts hK
  have hNFY : NF (om8Datum K) σY 0 natWts (fun a => e.symm (natBasis a)) :=
    (nf_natRep hK).map_equiv e.symm fun g v => by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
  obtain ⟨-, -, b₀, e', hb₀, he', -, hC2, -⟩ := bil_of_nf hK (om8Datum K) hXNF hXt hjX hNFY
    nfType_natWts (by rw [pow_zero]; omega) (nf_natRep hK) (fun a => mem_natWts) β hβ hβ0
  have hmem : (Pi.single (0 : Fin 4) (1 : ZMod (Nat.card Kˣ))) ∈ natWts (K := K) :=
    mem_natWts.2 ⟨0, Or.inl rfl⟩
  exact tri_not_isSpinWt_single (bil_ne_zero_of_isUnit_two_mul h3
    (by rw [hb₀]; exact isUnit_one)) (1 - e') ((hC2 _).1 hmem)

theorem tri_hom_scalar (hX : Om8Irr8 σX) (hY : Om8Irr8 σY)
    {β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} (hβ : IsEquivBil σX σY β) (hβ0 : β ≠ 0)
    (β' : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (hβ' : IsEquivBil σX σY β') :
    ∃ c : K, β' = c • β := by
  by_cases hz : β' = 0
  · exact ⟨0, by rw [hz, zero_smul]⟩
  obtain ⟨jX, CX, bX, hjX, hXt, hXNF⟩ := tri_nf_of_irr8 hA hK hX
  obtain ⟨jY, CY, bY, hjY, hYt, hYNF⟩ := tri_nf_of_irr8 hA hK hY
  obtain ⟨-, -, -, -, -, -, -, -, l, hl, hβl⟩ := bil_of_nf hK (om8Datum K) hXNF hXt hjX hYNF hYt
    hjY (nf_natRep hK) (fun a => mem_natWts) β hβ hβ0
  obtain ⟨-, -, -, -, -, -, -, -, l', hl', hβl'⟩ := bil_of_nf hK (om8Datum K) hXNF hXt hjX hYNF
    hYt hjY (nf_natRep hK) (fun a => mem_natWts) β' hβ' hz
  refine ⟨l' / l, tri_bil_ext hXNF.span_eq hYNF.span_eq fun a ha y hy => ?_⟩
  rw [hβl' a ha y hy, LinearMap.smul_apply, LinearMap.smul_apply, hβl a ha y hy]
  split_ifs
  · rw [smul_smul, div_mul_cancel₀ _ hl]
  · rw [smul_zero]

theorem tri_pair_data (hX : Om8Irr8 σX) (hY : Om8Irr8 σY)
    {β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} (hβ : IsEquivBil σX σY β) (hβ0 : β ≠ 0) :
    ∃ (CX CY : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
      (bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X) (bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y)
      (b₀ : ZMod (Nat.card Kˣ)) (e : ℕ) (l : K),
      NF (om8Datum K) σX 0 CX bX ∧ NF (om8Datum K) σY 0 CY bY ∧ 2 * b₀ = 1 ∧ e < 2 ∧
      (∀ a, a ∈ CX ↔ IsSpinWt b₀ e a) ∧ (∀ a, a ∈ CY ↔ IsSpinWt b₀ (1 - e) a) ∧ l ≠ 0 ∧
      ∀ a ∈ CX, ∀ b ∈ CY,
        β (bX a) (bY b) = if a + b ∈ natWts then l • natBasis (a + b) else 0 := by
  obtain ⟨jX, CX, bX, hjX, hXt, hXNF⟩ := tri_nf_of_irr8 hA hK hX
  obtain ⟨jY, CY, bY, hjY, hYt, hYNF⟩ := tri_nf_of_irr8 hA hK hY
  obtain ⟨rfl, rfl, b₀, e, hb₀, he, hCX, hCY, l, hl, hβl⟩ := bil_of_nf hK (om8Datum K) hXNF hXt
    hjX hYNF hYt hjY (nf_natRep hK) (fun a => mem_natWts) β hβ hβ0
  exact ⟨CX, CY, bX, bY, b₀, e, l, hXNF, hYNF, hb₀, he, hCX, hCY, hl, hβl⟩

theorem tri_pair_unique (hB : NFIsoStatement)
    {CX CY : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X}
    {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y} {b₀ : ZMod (Nat.card Kˣ)} {e : ℕ}
    (hXNF : NF (om8Datum K) σX 0 CX bX) (hYNF : NF (om8Datum K) σY 0 CY bY) (hb₀ : 2 * b₀ = 1)
    (he : e < 2) (hCX : ∀ a, a ∈ CX ↔ IsSpinWt b₀ e a)
    (hCY : ∀ a, a ∈ CY ↔ IsSpinWt b₀ (1 - e) a)
    {Z Z' : Type} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z] [AddCommGroup Z']
    [Module K Z'] [FiniteDimensional K Z'] {σZ : Representation K (Om8 K) Z}
    {σZ' : Representation K (Om8 K) Z'} (hZ : Om8Irr8 σZ) (hZ' : Om8Irr8 σZ')
    {γ : Z →ₗ[K] Z' →ₗ[K] (Fin 4 ⊕ Fin 4 → K)} (hγ : IsEquivBil σZ σZ' γ) (hγ0 : γ ≠ 0) :
    ((∃ f : Z ≃ₗ[K] X, ∀ (g : Om8 K) (z : Z), f (σZ g z) = σX g (f z)) ∧
        ∃ f : Z' ≃ₗ[K] Y, ∀ (g : Om8 K) (z : Z'), f (σZ' g z) = σY g (f z)) ∨
      ((∃ f : Z ≃ₗ[K] Y, ∀ (g : Om8 K) (z : Z), f (σZ g z) = σY g (f z)) ∧
        ∃ f : Z' ≃ₗ[K] X, ∀ (g : Om8 K) (z : Z'), f (σZ' g z) = σX g (f z)) := by
  obtain ⟨jZ, CZ, bZ, hjZ, hZt, hZNF⟩ := tri_nf_of_irr8 hA hK hZ
  obtain ⟨jZ', CZ', bZ', hjZ', hZ't, hZ'NF⟩ := tri_nf_of_irr8 hA hK hZ'
  obtain ⟨rfl, rfl, b₁, e', hb₁, he', hCZ, hCZ', -⟩ := bil_of_nf hK (om8Datum K) hZNF hZt hjZ
    hZ'NF hZ't hjZ' (nf_natRep hK) (fun a => mem_natWts) γ hγ hγ0
  obtain ⟨-, hodd, -⟩ := bil_card_facts hK
  have hbb : b₁ = b₀ := by
    have hu : IsUnit (2 : ZMod (Nat.card Kˣ)) := bil_isUnit_two hodd
    exact hu.mul_right_injective (hb₁.trans hb₀.symm)
  subst hbb
  by_cases hee : e' = e
  · subst hee
    left
    have h1 : CZ = CX := Finset.ext fun a => (hCZ a).trans (hCX a).symm
    have h2 : CZ' = CY := Finset.ext fun a => (hCZ' a).trans (hCY a).symm
    have hXNF' : NF (om8Datum K) σX 0 CZ bX := by rw [h1]; exact hXNF
    have hYNF' : NF (om8Datum K) σY 0 CZ' bY := by rw [h2]; exact hYNF
    exact ⟨hB (om8Datum K) σZ σX 0 CZ bZ bX hZNF hXNF',
      hB (om8Datum K) σZ' σY 0 CZ' bZ' bY hZ'NF hYNF'⟩
  · right
    have h1 : CZ = CY := Finset.ext fun a => (hCZ a).trans (by
      rw [show e' = 1 - e by omega]
      exact (hCY a).symm)
    have h2 : CZ' = CX := Finset.ext fun a => (hCZ' a).trans (by
      rw [show 1 - e' = e by omega]
      exact (hCX a).symm)
    have hYNF' : NF (om8Datum K) σY 0 CZ bY := by rw [h1]; exact hYNF
    have hXNF' : NF (om8Datum K) σX 0 CZ' bX := by rw [h2]; exact hXNF
    exact ⟨hB (om8Datum K) σZ σY 0 CZ bZ bY hZNF hYNF',
      hB (om8Datum K) σZ' σX 0 CZ' bZ' bX hZ'NF hXNF'⟩

end Pair

end CFSG.RankThree.GF2n.Stroth80.Tri

end
