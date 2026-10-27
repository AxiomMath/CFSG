module

public import CFSG.RankThree.PartOne.SEITZ8.D4Omega
public import CFSG.RankThree.PartOne.SEITZ8.D4Entry
public import CFSG.RankThree.PartOne.SEITZ7.D4BrN
public import CFSG.Timmesfeld.RankTwo.ModelD43Weyl
public import CFSG.RankThree.PartOne.SEITZ8.D4Z

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

theorem borel_stab_tw (hσ : ∀ c, σ (σ (σ c)) = c) {b : twistedGroup σ}
    (hb : b ∈ borel (twistedDatum σ) (hHat σ)) :
    ∃ χ : Kˣ, σ (χ : K) = χ ∧
      (b : adjointGroup d4 K) • (rv 22 : RootModule d4 K) = (χ : K) • rv 22 ∧
      (∀ x : RootModule d4 K, coordAt (d4Root 23) ((b : adjointGroup d4 K) • x) =
        ((χ⁻¹ : Kˣ) : K) * coordAt (d4Root 23) x) ∧
      ∀ c : K, (b : adjointGroup d4 K) * xe 22 c * (b : adjointGroup d4 K)⁻¹ =
        xe 22 ((χ : K) * c) := by
  have hbD : (b : adjointGroup d4 K) ∈ omegaH K := borel_le_omegaH (borel_twisted_le σ hb)
  obtain ⟨χ, a1, b1, c1⟩ := hbD
  refine ⟨χ, ?_, a1, b1, c1⟩
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hb' : b ∈ (borel (twistedDatum σ) (hHat σ) : Set (twistedGroup σ)) := hb
  rw [coe_borel hct, Set.mem_mul] at hb'
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
  have hu0U : ((u0 : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
    rw [posUnipotent_twisted] at hu0
    exact Subgroup.mem_subgroupOf.1 hu0
  have hmem : xH (1 : K) ∈ twistedRootSubgroupD4 σ (rt 7) :=
    (mem_XH hσ _).2 ⟨1, map_one σ, rfl⟩
  have hcomm := commute_Uhat_xH hσ hu0U (1 : K)
  have h1 := c1 1
  rw [Subgroup.coe_mul, mul_one] at h1
  have e : ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K)) * xe 22 1 *
      ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K))⁻¹ =
        (t0 : adjointGroup d4 K) * xe 22 1 * (t0 : adjointGroup d4 K)⁻¹ := by
    have hc : (u0 : adjointGroup d4 K) * xe 22 1 = xe 22 1 * (u0 : adjointGroup d4 K) := hcomm
    calc _ = (t0 : adjointGroup d4 K) * ((u0 : adjointGroup d4 K) * xe 22 1) *
          (u0 : adjointGroup d4 K)⁻¹ * (t0 : adjointGroup d4 K)⁻¹ := by group
      _ = _ := by rw [hc]; group
  have hconj : (t0 : adjointGroup d4 K) * xe 22 1 * (t0 : adjointGroup d4 K)⁻¹ ∈
      twistedRootSubgroupD4 σ (rt 7) := Tt_conj_X ht0 (isRoot_rt (by norm_num : 7 < 12)) hmem
  rw [e] at h1
  rw [h1] at hconj
  obtain ⟨c', hc'σ, hc'⟩ := (mem_XH hσ _).1 hconj
  have hc'eq : c' = (χ : K) := by
    have : xPar (rootOperatorFamily d4) (d4Root 22) c' =
        xPar (rootOperatorFamily d4) (d4Root 22) (χ : K) := by
      exact hc'.symm
    exact xPar_injective (isRoot_d4 (by norm_num : 22 < 24)) this
  rw [← hc'eq]
  exact hc'σ

omit [CharP K 2] in
theorem long_step_zero : ∀ p ∈ longPos, ∃ q ∈ longPos,
    reflect d4 (nd 2) (d4Root p) = d4Root q := by decide +kernel

omit [CharP K 2] in
theorem long_step_one : ∀ p ∈ longPos, ∃ q₃ < 24, ∃ q₁ < 24, ∃ q ∈ longPos,
    reflect d4 (nd 3) (d4Root p) = d4Root q₃ ∧ reflect d4 (nd 1) (d4Root q₃) = d4Root q₁ ∧
      reflect d4 (nd 0) (d4Root q₁) = d4Root q := by decide +kernel

theorem gen_stab (i : Fin (Tag.rank .G2)) {t : ℕ} (ht : t ∈ longPos) :
    ∃ q ∈ longPos, (nHatE K i : adjointGroup d4 K) • (rv t : RootModule d4 K) = rv q ∧
      ∀ c : K, nHatE K i * xe t c * (nHatE K i)⁻¹ = xe q c := by
  have hK : (2 : K) = 0 := CharTwo.two_eq_zero
  have ht24 : t < 24 := lt_of_mem_longPos ht
  have hroot : IsRoot d4 (d4Root t) := isRoot_d4 ht24
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨q, hq, hr⟩ := long_step_zero t ht
    refine ⟨q, hq, ?_, fun c => ?_⟩
    · rw [show (⟨0, by decide⟩ : Fin (Tag.rank .G2)) = ng 0 from rfl, nHatE_zero]
      exact weylElement_smul_rv (nd 2) ht24 hr hK
    · rw [CFSG.Timmesfeld.RankTwo.nHatE_conj_xPar (ng 0) hroot c, twReflectHom_zero, hr]
  | ⟨1, _⟩ =>
    obtain ⟨q₃, hq₃, q₁, hq₁, q, hq, h3, h1, h0⟩ := long_step_one t ht
    refine ⟨q, hq, ?_, fun c => ?_⟩
    · rw [show (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = ng 1 from rfl, nHatE_one, mul_smul,
        mul_smul, weylElement_smul_rv (nd 3) ht24 h3 hK, weylElement_smul_rv (nd 1) hq₃ h1 hK,
        weylElement_smul_rv (nd 0) hq₁ h0 hK]
    · rw [CFSG.Timmesfeld.RankTwo.nHatE_conj_xPar (ng 1) hroot c, twReflectHom_one, h3, h1, h0]

theorem listProd_stab (ω : List (Fin (Tag.rank .G2))) :
    ∃ t ∈ longPos, (ω.map (nHatE K)).prod • (rv 22 : RootModule d4 K) = rv t ∧
      ∀ c : K, (ω.map (nHatE K)).prod * xe 22 c * ((ω.map (nHatE K)).prod)⁻¹ = xe t c := by
  induction ω with
  | nil => exact ⟨22, by simp [longPos], by simp, fun c => by simp⟩
  | cons i ω ih =>
    obtain ⟨t, ht, h1, h2⟩ := ih
    obtain ⟨q, hq, hs1, hs2⟩ := gen_stab (K := K) i ht
    refine ⟨q, hq, ?_, fun c => ?_⟩
    · rw [List.map_cons, List.prod_cons, mul_smul, h1]
      exact hs1
    · rw [List.map_cons, List.prod_cons,
        show nHatE K i * (ω.map (nHatE K)).prod * xe 22 c *
          (nHatE K i * (ω.map (nHatE K)).prod)⁻¹ = nHatE K i * ((ω.map (nHatE K)).prod *
            xe 22 c * ((ω.map (nHatE K)).prod)⁻¹) * (nHatE K i)⁻¹ by group, h2 c]
      exact hs2 c

omit [CharP K 2] in
theorem coe_listProd_nHat (ω : List (Fin (Tag.rank .G2))) :
    (((ω.map (nHat σ)).prod : twistedGroup σ) : adjointGroup d4 K) = (ω.map (nHatE K)).prod := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]
    rfl

theorem listProd_stab_tw (ω : List (Fin (Tag.rank .G2))) :
    ∃ t ∈ longPos,
      (((ω.map (nHat σ)).prod : twistedGroup σ) : adjointGroup d4 K) • (rv 22 : RootModule d4 K) =
        rv t ∧ ∀ c : K, (((ω.map (nHat σ)).prod : twistedGroup σ) : adjointGroup d4 K) *
          xe 22 c * (((ω.map (nHat σ)).prod : twistedGroup σ) : adjointGroup d4 K)⁻¹ = xe t c := by
  obtain ⟨t, ht, h1, h2⟩ := listProd_stab (K := K) ω
  refine ⟨t, ht, ?_, fun c => ?_⟩
  · rw [coe_listProd_nHat]
    exact h1
  · rw [coe_listProd_nHat]
    exact h2 c

theorem nrep_stab_tw (hσ : ∀ c, σ (σ (σ c)) = c)
    (w : (coxeterMatrix (twistedDatum σ).isFiniteType).Group) :
    ∃ t ∈ longPos,
      ((nrep (twistedDatum_isCTGroupDatum σ hσ) w : twistedGroup σ) : adjointGroup d4 K) •
          (rv 22 : RootModule d4 K) = rv t ∧
      ∀ c : K, ((nrep (twistedDatum_isCTGroupDatum σ hσ) w : twistedGroup σ) :
          adjointGroup d4 K) * xe 22 c *
        ((nrep (twistedDatum_isCTGroupDatum σ hσ) w : twistedGroup σ) :
          adjointGroup d4 K)⁻¹ = xe t c := by
  obtain ⟨ω, hω, rfl⟩ :=
    ((coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem).exists_isReduced w
  rw [nrep_wordProd (twistedDatum_isCTGroupDatum σ hσ) hω]
  exact listProd_stab_tw ω

omit [CharP K 2] [Field K] in
theorem d4Root_inj : ∀ p < 24, ∀ q < 24, d4Root p = d4Root q → p = q := by decide +kernel

theorem bigCell_tw (hσ : ∀ c, σ (σ (σ c)) = c) (g : twistedGroup σ)
    (hne0 : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ≠ 0) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* twistedGroup σ,
      ∃ μ₁ μ₂ : fixedField σ, μ₁ ≠ 0 ∧ μ₂ ≠ 0 ∧
        (μ₁ : K) * (μ₂ : K) =
          coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ∧
        (∀ c : fixedField σ, ψ (sl2Upper (μ₁ * c)) = psiB σ hσ (sl2Upper c)) ∧
        (∀ c : fixedField σ,
          ψ (sl2Lower (μ₂ * c)) = g * psiB σ hσ (sl2Upper c) * g⁻¹) := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨χ₁, hχ₁, a1, bb1, c1⟩ := borel_stab_tw hσ hb₁
  obtain ⟨χ₂, hχ₂, a2, bb2, c2⟩ := borel_stab_tw hσ hb₂
  obtain ⟨t, ht, hv, hc⟩ := nrep_stab_tw hσ w
  have hlam : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) =
      ((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * coordAt (d4Root 23) (rv t : RootModule d4 K)) := by
    rw [hg, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, a2, smul_smul_comm', hv, bb1,
      coordAt_smul]
  have ht23 : t = 23 := by
    by_contra hne
    apply hne0
    have h1 : d4Root 23 ≠ d4Root t := fun h => hne (d4Root_inj t (lt_of_mem_longPos ht) 23
      (by norm_num) h.symm)
    rw [hlam, rv, coordAt_rootVec_ne h1]
    simp
  subst ht23
  have hμ₁ : σ (((χ₁⁻¹ : Kˣ)) : K) = ((χ₁⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hχ₁]
  refine ⟨(MulAut.conj b₁).toMonoidHom.comp (psiB σ hσ), ⟨((χ₁⁻¹ : Kˣ) : K), hμ₁⟩,
    ⟨(χ₂ : K), hχ₂⟩, fun h => Units.ne_zero χ₁⁻¹ (congrArg Subtype.val h),
    fun h => Units.ne_zero χ₂ (congrArg Subtype.val h),
    ?_, fun c => ?_, fun c => ?_⟩
  · rw [hlam, rv, coordAt_rootVec_self (isRoot_d4 (by norm_num))]
    simp
  · apply Subtype.ext
    have e1 : ((⟨((χ₁⁻¹ : Kˣ) : K), hμ₁⟩ * c : fixedField σ) : K) =
        ((χ₁⁻¹ : Kˣ) : K) * (c : K) := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv]
    rw [psiB_upper σ hσ, psiB_upper σ hσ, e1]
    show (b₁ : adjointGroup d4 K) * xe 22 (((χ₁⁻¹ : Kˣ) : K) * (c : K)) *
      (b₁ : adjointGroup d4 K)⁻¹ = xe 22 (c : K)
    rw [c1, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · apply Subtype.ext
    have e2 : ((⟨(χ₂ : K), hχ₂⟩ * c : fixedField σ) : K) = (χ₂ : K) * (c : K) := rfl
    have hgc : (g : adjointGroup d4 K) = (b₁ : adjointGroup d4 K) *
        ((nrep hct w : twistedGroup σ) : adjointGroup d4 K) * (b₂ : adjointGroup d4 K) := by
      rw [hg]
      rfl
    have hR : ((g * psiB σ hσ (sl2Upper c) * g⁻¹ : twistedGroup σ) : adjointGroup d4 K) =
        (g : adjointGroup d4 K) * xe 22 (c : K) * (g : adjointGroup d4 K)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, psiB_upper σ hσ]
      rfl
    have hL : (((MulAut.conj b₁).toMonoidHom.comp (psiB σ hσ)) (sl2Lower
        (⟨(χ₂ : K), hχ₂⟩ * c)) : adjointGroup d4 K) =
        (b₁ : adjointGroup d4 K) * xe 23 ((χ₂ : K) * (c : K)) * (b₁ : adjointGroup d4 K)⁻¹ := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_mul, Subgroup.coe_inv]
      rw [psiB_lower σ hσ, e2]
    rw [hL, hR, hgc]
    set n : adjointGroup d4 K := ((nrep hct w : twistedGroup σ) : adjointGroup d4 K) with hn
    have e : (b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K) * xe 22 (c : K) *
        ((b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K))⁻¹ =
        (b₁ : adjointGroup d4 K) * (n * ((b₂ : adjointGroup d4 K) * xe 22 (c : K) *
          (b₂ : adjointGroup d4 K)⁻¹) * n⁻¹) * (b₁ : adjointGroup d4 K)⁻¹ := by
      group
    rw [e, c2, hc]

end CFSG.RankThree.PartOne.SEITZ8
