module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL2OutAux

public section

namespace CFSG.Quasithin.H13.L829NK.L2Out

open CFSG CFSG.ComponentClassification.AutL2Facts GorensteinWalter Subgroup

section Standard

variable {F : Type} [Field F] [Finite F]

theorem torSub_comm_tor_neg_one {U : Subgroup Fˣ} {x : PGL2 F} (hx : x ∈ torSub F U) :
    x * tor F (-1) = tor F (-1) * x := by
  obtain ⟨y, -, ε, rfl⟩ := mem_torSub.mp hx
  cases ε
  · rw [swp_false, mul_one, ← map_mul, ← map_mul, mul_comm]
  · rw [swp_true, mul_assoc (tor F y) (sw F) (tor F (-1)), sw_mul_tor, inv_neg_one,
      ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm y]

theorem exists_z0_stdT (hsq : IsSquare (-1 : F)) (h2 : (2 : F) ≠ 0)
    (htv : (-1 : Fˣ) ∈ zpowers (stdGen F ^ 2)) :
    ∃ z₀ : PSL2 F, z₀ ∈ stdT F ∧ z₀ ≠ 1 ∧ (∀ s ∈ stdT F, s * z₀ = z₀ * s) ∧
      incl F z₀ = SemidirectProduct.inl (tor F (-1)) := by
  obtain ⟨z₀, hz₀⟩ := exists_psl2_tor_neg_one hsq
  have hT : Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) z₀ = tor F (-1) :=
    SemidirectProduct.inl_injective ((incl_apply F z₀).symm.trans hz₀)
  have hmemT : ∀ s : PSL2 F, s ∈ stdT F ↔
      Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) s ∈
        torSub F (zpowers (stdGen F ^ 2)) := fun s => Iff.rfl
  refine ⟨z₀, ?_, ?_, ?_, hz₀⟩
  · rw [hmemT, hT]
    exact mem_torSub.mpr ⟨-1, htv, false, by rw [swp_false, mul_one]⟩
  · intro h
    apply tor_neg_one_ne_one h2
    rw [← hT, h, map_one]
  · intro s hs
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_mul, map_mul, hT]
    exact torSub_comm_tor_neg_one ((hmemT s).mp hs)

theorem stdT_center_card (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (h8 : 8 ≤ 2 ^ twoVal F) :
    Nat.card ↥(stdT F ⊓ centralizer ((stdT F : Subgroup (PSL2 F)) : Set (PSL2 F))) = 2 := by
  have hcard := (sylow_noncomm_center hodd (stdSylow F hodd hsq hq4)
    (by rw [card_sylow_psl2 hodd hq4]; exact h8)).2
  rw [coe_stdSylow] at hcard
  exact hcard

theorem stdT_center_eq (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (h8 : 8 ≤ 2 ^ twoVal F) {z₀ : PSL2 F} (hz₀ : z₀ ∈ stdT F)
    (hz1 : z₀ ≠ 1) (hcomm : ∀ s ∈ stdT F, s * z₀ = z₀ * s) {v : PSL2 F}
    (hv : v ∈ stdT F ⊓ centralizer ((stdT F : Subgroup (PSL2 F)) : Set (PSL2 F))) :
    v = 1 ∨ v = z₀ := by
  haveI : Finite (PSL2 F) := inferInstance
  exact eq_one_or_eq_of_card_two_mem _ (stdT_center_card hodd hsq hq4 h8)
    (Subgroup.mem_inf.mpr ⟨hz₀, mem_centralizer_iff.mpr hcomm⟩) hz1 hv

theorem center_of_conj (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (h8 : 8 ≤ 2 ^ twoVal F) {z₀ : PSL2 F} (hz₀ : z₀ ∈ stdT F)
    (hz1 : z₀ ≠ 1) (hcomm : ∀ s ∈ stdT F, s * z₀ = z₀ * s) (D : Sylow 2 (PSL2 F))
    {h : PSL2 F} (hh : h • stdSylow F hodd hsq hq4 = D) :
    ∀ w ∈ (D : Subgroup (PSL2 F)) ⊓ centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)),
      w = 1 ∨ w = h * z₀ * h⁻¹ := by
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwD, hwC⟩ := hw
  have hwD' := hwD
  rw [← hh, mem_smul_sylow_iff, coe_stdSylow] at hwD'
  have hv : h⁻¹ * w * h ∈ stdT F ⊓ centralizer ((stdT F : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
    rw [Subgroup.mem_inf]
    refine ⟨hwD', mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have hhs : h * s * h⁻¹ ∈ (D : Subgroup (PSL2 F)) := by
      rw [← hh, mem_smul_sylow_iff, show h⁻¹ * (h * s * h⁻¹) * h = s by group, coe_stdSylow]
      exact hs
    have hw' := (mem_centralizer_iff.mp hwC) (h * s * h⁻¹) hhs
    calc s * (h⁻¹ * w * h) = h⁻¹ * ((h * s * h⁻¹) * w) * h := by group
      _ = h⁻¹ * (w * (h * s * h⁻¹)) * h := by rw [hw']
      _ = h⁻¹ * w * h * s := by group
  rcases stdT_center_eq hodd hsq hq4 h8 hz₀ hz1 hcomm hv with h1 | h1
  · left
    calc w = h * (h⁻¹ * w * h) * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc w = h * (h⁻¹ * w * h) * h⁻¹ := by group
      _ = h * z₀ * h⁻¹ := by rw [h1]

end Standard

theorem charP_of_card_sq {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) : CharP F p := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨q, hq, n, hqp, hcard⟩ := FiniteField.card' F
  rw [← Nat.card_eq_fintype_card, hF] at hcard
  have hqd : q ∣ p ^ 2 := by
    rw [hcard]
    exact dvd_pow_self q (PNat.ne_zero n)
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow hqd)
  rw [← hqp']
  exact hq

theorem right_one_e2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ 2) [CharP F p]
    (φ : X ≃* PSL2 F) (Q : Sylow 2 X) (hQ8 : 8 ≤ Nat.card Q) (y : MulAut X) (hy : y * y = 1)
    (hfix : ∀ b ∈ centralizer (((Q : Subgroup X) ⊓ centralizer ((Q : Subgroup X) : Set X) :
      Subgroup X) : Set X), y b = b) :
    (autEquiv φ y).right = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  have hp2 : p ≠ 2 := by omega
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 (by norm_num) hF
  have hq4 : Nat.card F % 4 = 1 := by
    rw [hF]
    exact pow_mod_four_of_even hp hp2 (by decide)
  have hsq : IsSquare (-1 : F) :=
    isSquare_neg_one_of_card_sq hp hp2 (f := 1) (hF.trans (by norm_num))
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := by
      rw [← CharP.cast_eq_zero_iff F p 2]
      exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h15 : (15 : F) ≠ 0 := by
    intro h
    have hd : p ∣ 15 := by
      rw [← CharP.cast_eq_zero_iff F p 15]
      exact_mod_cast h
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 3 * 5 from hd) with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by norm_num) h5
      omega
  set D : Sylow 2 (PSL2 F) := sylowMap φ Q with hD
  have hDcoe : (D : Subgroup (PSL2 F)) = (Q : Subgroup X).map φ.toMonoidHom := by
    rw [hD]
    exact coe_sylowMap φ Q
  have hD8 : 8 ≤ Nat.card D := by
    rw [hD, card_sylowMap]
    exact hQ8
  have h8std : 8 ≤ 2 ^ twoVal F := by
    rw [← card_sylow_psl2 hodd hq4 D]
    exact hD8
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) D
  have htv : (-1 : Fˣ) ∈ zpowers (stdGen F ^ 2) := neg_one_mem_zpowers_stdGen_sq hodd h8std
  obtain ⟨z₀, hz₀mem, hz₀ne, hz₀c, hz₀inc⟩ := exists_z0_stdT hsq h2 htv
  have hcenD := center_of_conj hodd hsq hq4 h8std hz₀mem hz₀ne hz₀c D hh
  have hZ : ∀ z ∈ (Q : Subgroup X) ⊓ centralizer ((Q : Subgroup X) : Set X),
      φ z ∈ (D : Subgroup (PSL2 F)) ⊓ centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
    intro z hz
    rw [Subgroup.mem_inf] at hz ⊢
    obtain ⟨hzQ, hzC⟩ := hz
    refine ⟨?_, ?_⟩
    · rw [hDcoe]
      exact Subgroup.mem_map_of_mem _ hzQ
    · rw [mem_centralizer_iff]
      intro d hd
      rw [SetLike.mem_coe, hDcoe, Subgroup.mem_map] at hd
      obtain ⟨s, hs, rfl⟩ := hd
      have hzs := mem_centralizer_iff.mp hzC s hs
      show φ s * φ z = φ z * φ s
      rw [← map_mul, ← map_mul, hzs]
  have hW : ∀ W : PSL2 F, (∀ w ∈ (D : Subgroup (PSL2 F)) ⊓
      centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)), w * W = W * w) →
      autEquiv φ y * incl F W = incl F W * autEquiv φ y := by
    intro W hWc
    have hmem : φ.symm W ∈ centralizer (((Q : Subgroup X) ⊓ centralizer ((Q : Subgroup X) :
        Set X) : Subgroup X) : Set X) := by
      rw [mem_centralizer_iff]
      intro z hz
      have hz' : z ∈ (Q : Subgroup X) ⊓ centralizer ((Q : Subgroup X) : Set X) := hz
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hWc (φ z) (hZ z hz')
    have h' := (apply_eq_iff_commute φ y (φ.symm W)).mp (hfix _ hmem)
    rwa [MulEquiv.apply_symm_apply] at h'
  have hcomm_u : ∀ u : Fˣ,
      (incl F h)⁻¹ * autEquiv φ y * incl F h * SemidirectProduct.inl (tor F (u * u)) =
        SemidirectProduct.inl (tor F (u * u)) * ((incl F h)⁻¹ * autEquiv φ y * incl F h) := by
    intro u
    have hsqu : IsSquare (((u * u : Fˣ)) : F) := ⟨(u : F), by rw [Units.val_mul]⟩
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (tor_mem_range hsqu)
    have hinl : SemidirectProduct.inl (tor F (u * u)) = incl F t := by
      rw [incl_apply, ht]
    rw [hinl]
    have hcT : tor F (-1) * tor F (u * u) = tor F (u * u) * tor F (-1) := by
      rw [← map_mul, ← map_mul, mul_comm]
    have hcT' : (SemidirectProduct.inl (tor F (-1)) : PGammaL2 F) *
        SemidirectProduct.inl (tor F (u * u)) =
        SemidirectProduct.inl (tor F (u * u)) * SemidirectProduct.inl (tor F (-1)) :=
      calc (SemidirectProduct.inl (tor F (-1)) : PGammaL2 F) * SemidirectProduct.inl (tor F (u * u))
          = SemidirectProduct.inl (tor F (-1) * tor F (u * u)) := (map_mul _ _ _).symm
        _ = SemidirectProduct.inl (tor F (u * u) * tor F (-1)) := by rw [hcT]
        _ = SemidirectProduct.inl (tor F (u * u)) * SemidirectProduct.inl (tor F (-1)) :=
            map_mul _ _ _
    have hz0t : z₀ * t = t * z₀ := by
      apply incl_injective F
      rw [map_mul, map_mul, hz₀inc, ← hinl]
      exact hcT'
    have hc : ∀ w ∈ (D : Subgroup (PSL2 F)) ⊓
        centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)),
        w * (h * t * h⁻¹) = (h * t * h⁻¹) * w := by
      intro w hw
      rcases hcenD w hw with rfl | rfl
      · simp
      · calc h * z₀ * h⁻¹ * (h * t * h⁻¹) = h * (z₀ * t) * h⁻¹ := by group
          _ = h * (t * z₀) * h⁻¹ := by rw [hz0t]
          _ = (h * t * h⁻¹) * (h * z₀ * h⁻¹) := by group
    have hg := hW (h * t * h⁻¹) hc
    have hconj : incl F (h * t * h⁻¹) = incl F h * incl F t * (incl F h)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj] at hg
    calc (incl F h)⁻¹ * autEquiv φ y * incl F h * incl F t
        = (incl F h)⁻¹ * (autEquiv φ y * (incl F h * incl F t * (incl F h)⁻¹)) * incl F h := by
          group
      _ = (incl F h)⁻¹ * ((incl F h * incl F t * (incl F h)⁻¹) * autEquiv φ y) * incl F h := by
          rw [hg]
      _ = incl F t * ((incl F h)⁻¹ * autEquiv φ y * incl F h) := by group
  set g' : PGammaL2 F := (incl F h)⁻¹ * autEquiv φ y * incl F h with hg'
  obtain ⟨r, hr⟩ := id hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hii : tor F (Units.mk0 r hr0 * Units.mk0 r hr0) = tor F (-1) := by
    congr 1
    ext
    simp [hr]
  have hcomm_neg : g' * SemidirectProduct.inl (tor F (-1)) =
      SemidirectProduct.inl (tor F (-1)) * g' := by
    have h' := hcomm_u (Units.mk0 r hr0)
    rwa [hii] at h'
  obtain ⟨a, ε, ha⟩ := (commute_tor_neg_one_iff h2 g').mp hcomm_neg
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = g'.right := ⟨_, rfl⟩
  have ha' : g' = nm F a ε σ := by rw [ha, ← hσ]
  have hT : ∀ u : Fˣ, twist F ε (fu F σ (u * u)) = u * u := by
    intro u
    have h' := hcomm_u u
    rw [ha', inl_tor] at h'
    exact (nm_commute_tor_iff a (u * u) ε σ).mp h'
  have hσ1 : σ = 1 := field_part_eq_one h2 hsq h15 ε σ hT
  have hright : g'.right = (autEquiv φ y).right := by
    have hfix1 : fieldProj F (incl F h) = 1 := rfl
    calc g'.right = fieldProj F g' := rfl
      _ = fieldProj F ((incl F h)⁻¹) * fieldProj F (autEquiv φ y) * fieldProj F (incl F h) := by
          rw [hg', map_mul, map_mul]
      _ = (autEquiv φ y).right := by
          rw [map_inv, hfix1, inv_one, one_mul, mul_one]
          rfl
  rw [← hright, ← hσ, hσ1]

end CFSG.Quasithin.H13.L829NK.L2Out
