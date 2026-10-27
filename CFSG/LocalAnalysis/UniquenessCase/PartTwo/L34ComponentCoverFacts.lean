module

public import CFSG.GroupTheory.ComponentImageUniqueness
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Out
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXE9
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import CFSG.Adapters.LieModelSimple
public import CFSG.Quasithin.Background.HSU3Unitary
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Aut
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinIrredThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {M K : Subgroup G}

theorem exists_quotient_center_equiv_of_map_eq {X Y : Type*} [Group X] [Group Y]
    {C : Subgroup X} {H : Subgroup Y} (ψ : X →* Y) (hC : CFSG.IsComponent C)
    (hmap : C.map ψ = H) (hsimple : IsSimpleGroup ↥H) :
    ∃ e : (C ⧸ Subgroup.center C) ≃* ↥H, ∀ c : C,
      e (QuotientGroup.mk c) =
        ⟨ψ (c : X), hmap ▸ Subgroup.mem_map_of_mem ψ c.2⟩ := by
  classical
  let ρ : C →* ↥H :=
    { toFun := fun c =>
        ⟨ψ (c : X), hmap ▸ Subgroup.mem_map_of_mem ψ c.2⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro a b
        ext
        simp }
  have hρ : Function.Surjective ρ := by
    intro h
    have hmem : (h : Y) ∈ C.map ψ := by
      rw [hmap]
      exact h.2
    obtain ⟨c, hc, hcψ⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨c, hc⟩, Subtype.ext hcψ⟩
  have hkerρ : ρ.ker = Subgroup.center C := by
    have h := CFSG.ComponentImage.ker_comp_subtype_eq_center ψ hC hmap hsimple
    ext c
    rw [← h, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun hh => Subtype.ext_iff.mp hh, fun hh => Subtype.ext hh⟩
  let e₁ : (C ⧸ ρ.ker) ≃* ↥H :=
    QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  let e₂ : (C ⧸ Subgroup.center C) ≃* (C ⧸ ρ.ker) :=
    QuotientGroup.quotientMulEquivOfEq hkerρ.symm
  refine ⟨e₂.trans e₁, ?_⟩
  intro c
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk ρ hρ c]
  rfl

theorem barImage_l34_center_card_and_exists_e9
    (hK : K ∈ calC M)
    {Y : Type} [Group Y] (ψ : Bar2 M →* Y) {H : Subgroup Y}
    (himage : (UC22.barImage M K).map ψ = H) (hL34 : IsLn ↥H 3 2) :
    (Nat.card (Subgroup.center ↥(UC22.barImage M K)) = 1 ∨
        Nat.card (Subgroup.center ↥(UC22.barImage M K)) = 3) ∧
      ∃ E : Subgroup (Bar2 M), E ≤ UC22.barImage M K ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  let C : Subgroup (Bar2 M) := UC22.barImage M K
  have hC : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hsimpleH : IsSimpleGroup ↥H :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL34
  obtain ⟨eCH, -⟩ := exists_quotient_center_equiv_of_map_eq ψ hC himage hsimpleH
  have hPSLH : IsPSL 3 2 2 ↥H :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL34 (by decide)
  have hPSL : IsPSL 3 2 2 (C ⧸ Subgroup.center C) :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eCH.symm hPSLH
  obtain ⟨eBK⟩ := UC22.uc22p22l_barImage_equiv hK
  have hoddC : Odd (Nat.card (Subgroup.center C)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eBK).toEquiv]
    exact UC22.uc22p22l_odd_center_quotient (Λ := K)
  have hperf : commutator C = ⊤ := Group.isPerfect_def.mp hC.1.1
  have hnocentraltwo : ∀ z ∈ Subgroup.center C, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
    intro z hz k hk
    have hdvd₁ : orderOf z ∣ Nat.card (Subgroup.center C) := Subgroup.orderOf_dvd_natCard (Subgroup.center C) hz
    have hdvd₂ : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center C)) :=
      (Nat.coprime_two_left.mpr hoddC).pow_left k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd₂ hdvd₁)
  have hdvd := CFSG.Quasithin.H13.S126P31.card_center_dvd_three_of_quotient hperf hnocentraltwo hPSL
  have hcard : Nat.card (Subgroup.center C) = 1 ∨ Nat.card (Subgroup.center C) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Or.inl h1
    · exact Or.inr h3
  obtain ⟨E₀, hE₀ab, hE₀card⟩ :=
    CFSG.Quasithin.H13.Ch9.L34.exists_elemAbelian_nine_of_isPSL hPSL
  obtain ⟨E, hEab, hEcard⟩ :=
    CFSG.Quasithin.H13.Ch4.J4KX.exists_e9_of_quotient (Subgroup.center C) E₀ hE₀ab hE₀card
  exact ⟨hcard, E.map C.subtype, Subgroup.map_subtype_le E,
    CFSG.SectionRank.isElemAbelian_map hEab C.subtype,
    by rw [Subgroup.card_map_of_injective C.subtype_injective, hEcard]⟩

theorem barImage_l34_center_inverted_of_field_action
    (hK : K ∈ calC M)
    {Y : Type} [Group Y] (ψ : Bar2 M →* Y) {H : Subgroup Y}
    (himage : (UC22.barImage M K).map ψ = H) (hL34 : IsLn ↥H 3 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (π : Matrix.SpecialLinearGroup (Fin 3) F →* ↥H)
    (hπ : Function.Surjective π)
    (hπker : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))
    (A : Matrix.GeneralLinearGroup (Fin 3) F) (x : Bar2 M)
    (hxN : ψ x ∈ Subgroup.normalizer (H : Set Y))
    (hfield : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
      ψ x * (π g : Y) * (ψ x)⁻¹ =
        (π (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          3 F A (Matrix.SpecialLinearGroup.map
            (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom g)) : Y)) :
    ∀ z : ↥(UC22.barImage M K), z ∈ Subgroup.center ↥(UC22.barImage M K) →
      x * (z : Bar2 M) * x⁻¹ = (z : Bar2 M)⁻¹ := by
  classical
  let C : Subgroup (Bar2 M) := UC22.barImage M K
  have hC : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hsimpleH : IsSimpleGroup ↥H :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL34
  have hna : ∃ a ∈ C.map ψ, ∃ b ∈ C.map ψ, a * b ≠ b * a :=
    CFSG.ComponentImage.exists_noncommuting_map_of_isSimpleGroup ψ hC himage hsimpleH
  have hxNormal : ψ x ∈ Subgroup.normalizer (C.map ψ : Set Y) := by
    rwa [himage]
  have hxC : x ∈ Subgroup.normalizer (C : Set (Bar2 M)) :=
    CFSG.ComponentImage.mem_normalizer_of_map_mem_normalizer ψ hC hna hxNormal
  obtain ⟨eCH, heCH⟩ := exists_quotient_center_equiv_of_map_eq ψ hC himage hsimpleH
  let ρ : C →* ↥H :=
    { toFun := fun c =>
        ⟨ψ (c : Bar2 M), himage ▸ Subgroup.mem_map_of_mem ψ c.2⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro a b
        ext
        simp }
  have heCHρ : ∀ c : C, eCH (QuotientGroup.mk c) = ρ c := fun c => heCH c
  have hPSLH : IsPSL 3 2 2 ↥H :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL34 (by decide)
  have hPSL : IsPSL 3 2 2 (C ⧸ Subgroup.center C) :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eCH.symm hPSLH
  obtain ⟨hcenterCard, -⟩ := barImage_l34_center_card_and_exists_e9 hK ψ himage hL34
  rcases hcenterCard with hZ1 | hZ3
  ·
    intro z hz
    have hz1 : z = 1 := Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp hZ1 ▸ hz)
    simp [hz1]
  ·
    have hperf : commutator C = ⊤ := Group.isPerfect_def.mp hC.1.1
    have hprojker : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F).ker =
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.ker_proj,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    let πZ : (Matrix.SpecialLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ≃* ↥H :=
      (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπ)
    have hπZ : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
        πZ (QuotientGroup.mk s) = π s := by
      intro s
      rw [show πZ = (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective π hπ) from rfl,
        MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk π hπ s
    let qPSL : (Matrix.SpecialLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
      (QuotientGroup.quotientMulEquivOfEq hprojker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F))
    have hqPSL : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
        qPSL (QuotientGroup.mk s) = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s := by
      intro s
      rw [show qPSL = (QuotientGroup.quotientMulEquivOfEq hprojker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F)) from rfl,
        MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F) s
    let eQuot : (C ⧸ Subgroup.center C) ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
      eCH.trans (πZ.symm.trans qPSL)
    have hsymm : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
        eQuot.symm (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) =
          eCH.symm (π s) := by
      intro s
      rw [MulEquiv.symm_apply_eq]
      rw [show eQuot = eCH.trans (πZ.symm.trans qPSL) from rfl,
        MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      have hπZs : πZ.symm (π s) = QuotientGroup.mk s := by
        rw [MulEquiv.symm_apply_eq]
        exact hπZ s
      rw [hπZs, hqPSL s]
    have hoddZ3 : Odd (Nat.card (Subgroup.center C)) := by
      rw [hZ3]
      norm_num
    have hz : Subgroup.center C ≠ ⊥ := by
      intro hbot
      have h := congrArg (fun H : Subgroup C => Nat.card H) hbot
      rw [hZ3] at h
      have h1 : Nat.card (⊥ : Subgroup C) = 1 := by simp
      omega
    obtain ⟨φ, hφ⟩ :=
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.exists_mulEquiv_over_sl3
        (k := F) (p := 2) (f := 2) (K := C)
        (by norm_num [hF]) (by norm_num [hF]) hperf hPSL hoddZ3 hz eQuot
    let e : C ≃* Matrix.SpecialLinearGroup (Fin 3) F := φ.symm
    have hsquare : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F, π s = ρ (φ s) := by
      intro s
      have h1 : QuotientGroup.mk (φ s) = eQuot.symm
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) := by
        rw [← hφ s, MulEquiv.symm_apply_apply]
      calc π s = eCH (eCH.symm (π s)) := (MulEquiv.apply_symm_apply eCH (π s)).symm
        _ = eCH (eQuot.symm (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s)) := by
            rw [hsymm s]
        _ = eCH (QuotientGroup.mk (φ s)) := by rw [h1]
        _ = ρ (φ s) := heCHρ (φ s)
    have hsquareC : ∀ c : C, π (e c) = ρ c := by
      intro c
      have h := hsquare (e c)
      rwa [show φ (e c) = c from φ.apply_symm_apply c] at h
    let α : MulAut C := C.normalizerMonoidHom ⟨x, hxC⟩
    have hαcoe : ∀ c : C, ((α c : C) : Bar2 M) = x * (c : Bar2 M) * x⁻¹ :=
      fun c => Subgroup.normalizerMonoidHom_apply_apply_coe C ⟨x, hxC⟩ c
    let β : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) :=
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A *
        CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F
          (CFSG.Quasithin.H.SU3.bar 1)
    have hslField : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F
          (CFSG.Quasithin.H.SU3.bar 1)) g =
        Matrix.SpecialLinearGroup.map
          (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom g := by
      intro g
      apply Subtype.ext
      ext i j
      change (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv (Fin 3)
        (CFSG.Quasithin.H.SU3.bar 1) g : Matrix (Fin 3) (Fin 3) F) i j = _
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
    have hαβpoint : ∀ c : C, (π (e (α c)) : Y) = (π (β (e c)) : Y) := by
      intro c
      calc (π (e (α c)) : Y) = (ρ (α c) : Y) := congrArg Subtype.val (hsquareC (α c))
        _ = ψ ((α c : C) : Bar2 M) := rfl
        _ = ψ (x * (c : Bar2 M) * x⁻¹) := by rw [hαcoe c]
        _ = ψ x * ψ (c : Bar2 M) * (ψ x)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = ψ x * (π (e c) : Y) * (ψ x)⁻¹ := by
            change ψ x * (ρ c : Y) * (ψ x)⁻¹ = _
            rw [show (ρ c : Y) = (π (e c) : Y) from
              (congrArg Subtype.val (hsquareC c)).symm]
        _ = (π (β (e c)) : Y) := by
            rw [show β (e c) = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
              3 F A (Matrix.SpecialLinearGroup.map
                (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom (e c)) from by
              rw [show β = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
                  3 F A * CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
                    (Fin 3) F (CFSG.Quasithin.H.SU3.bar 1) from rfl,
                MulAut.mul_apply, hslField]]
            exact hfield (e c)
    let σ : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) := MulAut.congr e α * β⁻¹
    have hσmem : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
        σ s * s⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      intro s
      rw [← hπker, MonoidHom.mem_ker]
      have hπσ : π (σ s) = π s := by
        apply Subtype.ext
        have hcongr_apply : MulAut.congr e α (β⁻¹ s) =
            e (α (e.symm (β⁻¹ s))) := by
          rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
        rw [show σ s = MulAut.congr e α (β⁻¹ s) from by
          rw [show σ = MulAut.congr e α * β⁻¹ from rfl, MulAut.mul_apply]]
        rw [hcongr_apply]
        rw [hαβpoint (e.symm (β⁻¹ s)), MulEquiv.apply_symm_apply,
          show β (β⁻¹ s) = s by
            rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]]
      rw [map_mul, map_inv, hπσ, mul_inv_cancel]
    have hSLperfect : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
    have hσ1 : σ = 1 := CFSG.GroupTheory.MulAut.eq_one_of_mul_mem_center hSLperfect σ hσmem
    have hcongr : MulAut.congr e α = β := by
      have h := hσ1
      rw [show σ = MulAut.congr e α * β⁻¹ from rfl] at h
      exact mul_inv_eq_one.mp h
    intro z hz
    have hzSL : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
      (Subgroup.centerCongr e ⟨z, hz⟩).2
    have hβz : β (e z) = (e z)⁻¹ := by
      obtain ⟨c, hc3, hwc⟩ := UC22.uc22pwI3_center_scalar hzSL
      have hw : e z = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3 := by
        apply Subtype.ext
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement]
        exact hwc
      have hc3' : (c : F) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
      have hc2 : (c ^ 2) ^ 3 = 1 := by
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_one]
        rw [show ((c : F) ^ 2) ^ 3 = ((c : F) ^ 3) ^ 2 by ring, hc3', one_pow]
      have hfrob : (CFSG.Quasithin.H.SU3.bar 1) (c : F) = (c : F) ^ 2 := by
        rw [CFSG.Quasithin.H.SU3.bar_apply]
        norm_num
      have hfieldscalar : ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
          (Fin 3) F (CFSG.Quasithin.H.SU3.bar 1))
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3) :
              Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ((c : F) ^ 2) := by
        ext i j
        change (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv (Fin 3)
          (CFSG.Quasithin.H.SU3.bar 1)
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3) :
            Matrix (Fin 3) (Fin 3) F) i j = Matrix.scalar (Fin 3) ((c : F) ^ 2) i j
        rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement,
          Matrix.scalar_apply, Matrix.scalar_apply]
        by_cases hij : i = j
        · subst hij
          simp [hfrob]
        · simp [hij]
      have hconjscalar : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          3 F A (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 := by
        apply Subtype.ext
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement]
        have hGL : A * Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2) * A⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2) := by
          rw [show A * Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2) =
              Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2) * A from
                (Matrix.GeneralLinearGroup.scalar_commute (c ^ 2) A).symm,
            mul_assoc, mul_inv_cancel, mul_one]
        have hmat := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 3) F =>
          (x : Matrix (Fin 3) (Fin 3) F)) hGL
        simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
          using hmat
      have hβscalar : β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 := by
        apply Subtype.ext
        calc ((β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3) :
              Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
            = ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
                (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) F
                  (CFSG.Quasithin.H.SU3.bar 1)
                  (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3)) :
                Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
              simp only [β, MulAut.mul_apply]
          _ = ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
                (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2) :
                Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
              rw [show CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
                  (Fin 3) F (CFSG.Quasithin.H.SU3.bar 1)
                  (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3) =
                  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 from
                    Subtype.ext hfieldscalar]
          _ = ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 :
                Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
              rw [hconjscalar]
          _ = ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 :
                Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
      have hprod : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3 *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement,
          Matrix.SpecialLinearGroup.coe_one]
        change Matrix.diagonal (fun _ : Fin 3 => (c : F)) *
          Matrix.diagonal (fun _ : Fin 3 => ((c : F) ^ 2)) = 1
        rw [Matrix.diagonal_mul_diagonal]
        have hc3' : (c : F) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
        have hfun : (fun _ : Fin 3 => (c : F) * (c : F) ^ 2) = fun _ => (1 : F) := by
          funext i
          rw [show (c : F) * (c : F) ^ 2 = (c : F) ^ 3 by ring, hc3']
        rw [hfun, Matrix.diagonal_one]
      calc β (e z) = β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3) := by
            rw [hw]
        _ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (c ^ 2) hc2 := hβscalar
        _ = (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc3)⁻¹ :=
            eq_inv_of_mul_eq_one_right hprod
        _ = (e z)⁻¹ := by rw [hw]
    have heq : e (α z) = e (z⁻¹) := by
      have h1 : MulAut.congr e α (e z) = β (e z) := by rw [hcongr]
      have h2 : MulAut.congr e α (e z) = e (α z) := by
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [← h2, h1, hβz, map_inv]
    have hαz : α z = z⁻¹ := e.injective heq
    have hcoe : ((α z : C) : Bar2 M) = x * (z : Bar2 M) * x⁻¹ := hαcoe z
    rw [← hcoe, hαz]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
