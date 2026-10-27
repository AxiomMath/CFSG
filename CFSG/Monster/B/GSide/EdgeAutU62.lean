module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import Certificates.Certificate16005

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

theorem mulAut_eq_conj_of_selfNormalizing {G P : Type*} [Group G] [Group P] (ι : P →* G)
    (hι : Function.Injective ι) (κ : G →* MulAut P) (hκ : ∀ g p, ι (κ g p) = g * ι p * g⁻¹)
    (hchar : ∀ τ : MulAut G, ∀ p, ∃ p', τ (ι p) = ι p')
    (hcent : ∀ g : G, (∀ p, g * ι p = ι p * g) → g = 1)
    (hnorm : ∀ α : MulAut P, (∀ g, ∃ g', α * κ g * α⁻¹ = κ g') → ∃ g₀, α = κ g₀)
    (τ : MulAut G) : ∃ g, τ = MulAut.conj g := by
  choose f hf using fun p => hchar τ p
  choose f' hf' using fun p => hchar τ⁻¹ p
  have hff' : ∀ p, f (f' p) = p := fun p => hι (by
    rw [← hf, ← hf']
    exact MulAut.apply_inv_self _ τ (ι p))
  have hf'f : ∀ p, f' (f p) = p := fun p => hι (by
    rw [← hf', ← hf]
    exact MulAut.inv_apply_self _ τ (ι p))
  let α : MulAut P :=
    { toFun := f
      invFun := f'
      left_inv := hf'f
      right_inv := hff'
      map_mul' := fun p q => hι (by rw [← hf, map_mul, map_mul, map_mul, ← hf, ← hf]) }
  have hα : ∀ p, ι (α p) = τ (ι p) := fun p => (hf p).symm
  have hαinv : ∀ p, ι (α⁻¹ p) = τ⁻¹ (ι p) := fun p => (hf' p).symm
  obtain ⟨g₀, hg₀⟩ := hnorm α fun g => ⟨τ g, MulEquiv.ext fun p => hι (by
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hκ, hαinv, hκ, map_mul, map_mul, map_inv,
      ← MulAut.mul_apply _ τ τ⁻¹, mul_inv_cancel, MulAut.one_apply])⟩
  have hτι : ∀ p, τ (ι p) = g₀ * ι p * g₀⁻¹ := fun p => by rw [← hα, hg₀, hκ]
  refine ⟨g₀, MulEquiv.ext fun x => ?_⟩
  have hz := hcent (x⁻¹ * g₀⁻¹ * τ x * g₀) fun p => by
    have e1 : τ (x * ι p * x⁻¹) = τ x * (g₀ * ι p * g₀⁻¹) * (τ x)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hτι]
    have e2 : τ (x * ι p * x⁻¹) = g₀ * (x * ι p * x⁻¹) * g₀⁻¹ := by
      rw [← hκ, hτι, hκ]
    have e3 := e1.symm.trans e2
    calc x⁻¹ * g₀⁻¹ * τ x * g₀ * ι p
        = x⁻¹ * g₀⁻¹ * (τ x * (g₀ * ι p * g₀⁻¹) * (τ x)⁻¹) * (τ x * g₀) := by group
      _ = x⁻¹ * g₀⁻¹ * (g₀ * (x * ι p * x⁻¹) * g₀⁻¹) * (τ x * g₀) := by rw [e3]
      _ = ι p * (x⁻¹ * g₀⁻¹ * τ x * g₀) := by group
  rw [MulAut.conj_apply]
  calc τ x = g₀ * x * (x⁻¹ * g₀⁻¹ * τ x * g₀) * g₀⁻¹ := by group
    _ = g₀ * x * g₀⁻¹ := by rw [hz, mul_one]

open CFSG.Monster.B.TwoA.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Fischer (F4)
open scoped commutatorElement

abbrev PI : Type := primeFormP hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)

theorem isPrimeFormGram_one6 : IsPrimeFormGram (1 : GL (Fin 6) F4) := by
  refine ⟨by rw [Units.val_one, Matrix.transpose_one], fun i j => ?_⟩
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

@[expose] def suEquiv :
    unitarySU 2 1 F4 6 ≃* gramSU hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
  MulEquiv.subgroupCongr (unitarySU_eq_gramSU hF4 6)

theorem coe_suEquiv (g : unitarySU 2 1 F4 6) : ((suEquiv g : gramSU hF4 _) : GL (Fin 6) F4) = g :=
  rfl

theorem map_normOneScalars_suEquiv :
    (normOneScalars hF4 (unitarySU 2 1 F4 6) 6).map suEquiv.toMonoidHom =
      normOneScalars hF4 (gramSU hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) 6 := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hg
    exact ⟨suEquiv.symm g, hg, suEquiv.apply_symm_apply g⟩

@[expose] def psuEquiv : unitaryPSU hF4 6 ≃* PI :=
  QuotientGroup.congr _ _ suEquiv map_normOneScalars_suEquiv

theorem psuEquiv_mk (g : unitarySU 2 1 F4 6) :
    psuEquiv (g : unitaryPSU hF4 6) = ((suEquiv g : gramSU hF4 _) : PI) :=
  QuotientGroup.congr_mk _ _ _ _ g

@[expose] def barEquiv : F4 ≃+* F4 :=
  { hF4.bar with
    invFun := hF4.bar
    left_inv := hF4.bar_bar
    right_inv := hF4.bar_bar }

theorem barEquiv_apply (c : F4) : barEquiv c = hF4.bar c := rfl

abbrev fBar : MulAut PI := primeFormFieldHom hF4 isPrimeFormGram_one6 barEquiv

theorem psuEquiv_frobQI (x : unitaryPSU hF4 6) : psuEquiv (frobQI x) = fBar (psuEquiv x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
  rw [frobQI_mk, psuEquiv_mk, psuEquiv_mk]
  change ((suEquiv (frobSUI g) : gramSU hF4 _) : PI) =
    primeFormFieldAut hF4 isPrimeFormGram_one6 barEquiv _
  rw [primeFormFieldAut_mk]
  congr 1

theorem conj_mk_eq_primeFormConjHom
    (s : gramSU hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :
    MulAut.conj (s : PI) = primeFormConjHom hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
      ⟨s, (mem_gramSU_iff_unitary hF4).1 s.2 |>.1⟩ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem not_isMulCommutative_unitaryPSU : ¬ IsMulCommutative (unitaryPSU hF4 6) := by
  intro h
  have := (Group.is_simple_iff_prime_card (α := unitaryPSU hF4 6)).1 isSimpleGroup_unitaryPSU
  rw [natCard_unitaryPSU] at this
  exact absurd this (by norm_num)

theorem exists_ne_commute_unitaryPSU : ∃ a b : unitaryPSU hF4 6, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact not_isMulCommutative_unitaryPSU ⟨⟨h⟩⟩

theorem center_unitaryPSU : Subgroup.center (unitaryPSU hF4 6) = ⊥ := by
  rcases isSimpleGroup_unitaryPSU.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := exists_ne_commute_unitaryPSU
    exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

theorem commutator_unitaryPSU : commutator (unitaryPSU hF4 6) = ⊤ := by
  rcases isSimpleGroup_unitaryPSU.eq_bot_or_eq_top_of_normal (commutator _) with h | h
  · obtain ⟨a, b, hab⟩ := exists_ne_commute_unitaryPSU
    have hc : ⁅a, b⁆ ∈ commutator (unitaryPSU hF4 6) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact absurd hc hab
  · exact h

@[expose] def kappaU : PSU62 →* MulAut (unitaryPSU hF4 6) :=
  SemidirectProduct.lift MulAut.conj frobHomI fun ε => MonoidHom.ext fun n => MulEquiv.ext
    fun x => by
      change frobHomI ε n * x * (frobHomI ε n)⁻¹ =
        (frobHomI ε * MulAut.conj n * (frobHomI ε)⁻¹) x
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
        MulAut.apply_inv_self]

theorem kappaU_mk (n : unitaryPSU hF4 6) (ε : Multiplicative (ZMod 2)) :
    kappaU ⟨n, ε⟩ = MulAut.conj n * frobHomI ε := by
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul, kappaU, SemidirectProduct.lift_inl,
    SemidirectProduct.lift_inr]

theorem inl_kappaU (g : PSU62) (p : unitaryPSU hF4 6) :
    (SemidirectProduct.inl (kappaU g p) : PSU62) = g * SemidirectProduct.inl p * g⁻¹ := by
  obtain ⟨n, ε⟩ := g
  rw [kappaU_mk, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    SemidirectProduct.inl_aut, SemidirectProduct.mk_eq_inl_mul_inr,
    show (SemidirectProduct.inr ε⁻¹ : PSU62) = (SemidirectProduct.inr ε)⁻¹ from map_inv _ _]
  group

theorem inl_mem_commutator (p : unitaryPSU hF4 6) :
    (SemidirectProduct.inl p : PSU62) ∈ commutator PSU62 := by
  have h := Subgroup.mem_map_of_mem (SemidirectProduct.inl : unitaryPSU hF4 6 →* PSU62)
    (show p ∈ commutator (unitaryPSU hF4 6) by rw [commutator_unitaryPSU]; exact Subgroup.mem_top p)
  rw [commutator_def, Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono le_top le_top h

theorem commutator_PSU62 : commutator PSU62 = (SemidirectProduct.inl).range := by
  refine le_antisymm ?_ ?_
  · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact Abelianization.commutator_subset_ker _
  · rintro _ ⟨p, rfl⟩
    exact inl_mem_commutator p

theorem index_commutator_PSU62 : (commutator PSU62).index = 2 := by
  rw [commutator_PSU62, SemidirectProduct.range_inl_eq_ker_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 SemidirectProduct.rightHom_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  rfl

theorem exists_inl_eq (τ : MulAut PSU62) (p : unitaryPSU hF4 6) :
    ∃ p', τ (SemidirectProduct.inl p) = SemidirectProduct.inl p' := by
  have h2 : τ (SemidirectProduct.inl p) ∈ commutator PSU62 := by
    have h := Subgroup.mem_map_of_mem τ.toMonoidHom (inl_mem_commutator p)
    rwa [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ τ.surjective] at h
  rw [commutator_PSU62] at h2
  obtain ⟨p', hp'⟩ := h2
  exact ⟨p', hp'.symm⟩

theorem barEquiv_ne_refl : barEquiv ≠ RingEquiv.refl F4 := fun h => by
  obtain ⟨c, hc⟩ := hF4.exists_bar_ne
  exact hc (congrArg (fun σ : F4 ≃+* F4 => σ c) h)

abbrev fieldFactor : MulAut PI →* (F4 ≃+* F4) :=
  primeFormFieldFactor hF4 isPrimeFormGram_one6 (by norm_num) (by norm_num)

theorem fieldFactor_conj (s : gramSU hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :
    fieldFactor (MulAut.conj (s : PI)) = RingEquiv.refl F4 := by
  have h := primeFormFieldFactor_apply hF4 isPrimeFormGram_one6 (by norm_num) (by norm_num)
    ⟨s, (mem_gramSU_iff_unitary hF4).1 s.2 |>.1⟩ (RingEquiv.refl F4)
  rwa [show primeFormFieldHom hF4 isPrimeFormGram_one6 (RingEquiv.refl F4) = 1 from map_one _,
    mul_one, ← conj_mk_eq_primeFormConjHom] at h

theorem fieldFactor_fBar : fieldFactor fBar = barEquiv := by
  have h := primeFormFieldFactor_apply hF4 isPrimeFormGram_one6 (by norm_num) (by norm_num) 1
    barEquiv
  rwa [map_one, one_mul] at h

theorem fBar_ne_conj (y : PI) : fBar ≠ MulAut.conj y := fun h => by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 := fieldFactor_fBar
  rw [h, fieldFactor_conj] at h1
  exact barEquiv_ne_refl h1.symm

theorem congr_frobQI : MulAut.congr psuEquiv frobQI = fBar :=
  MulEquiv.ext fun y => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, psuEquiv_frobQI,
      MulEquiv.apply_symm_apply]

theorem congr_conj (n : unitaryPSU hF4 6) :
    MulAut.congr psuEquiv (MulAut.conj n) = MulAut.conj (psuEquiv n) :=
  MulEquiv.ext fun y => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply,
      MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_one_of_forall_commute (g : PSU62)
    (hg : ∀ p, g * SemidirectProduct.inl p = SemidirectProduct.inl p * g) : g = 1 := by
  have hk : kappaU g = 1 := MulEquiv.ext fun p => SemidirectProduct.inl_injective (by
    rw [inl_kappaU, hg, mul_inv_cancel_right]
    rfl)
  obtain ⟨n, ε⟩ := g
  rw [kappaU_mk] at hk
  induction ε using Multiplicative.rec with
  | ofAdd ε =>
  rcases zmod2_cases' ε with rfl | rfl
  · have h0 : frobHomI (Multiplicative.ofAdd 0) = 1 := map_one _
    rw [h0, mul_one] at hk
    have hn : n ∈ Subgroup.center (unitaryPSU hF4 6) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun σ : MulAut (unitaryPSU hF4 6) => σ x) hk
      change n * x * n⁻¹ = x at h
      calc x * n = n * x * n⁻¹ * n := by rw [h]
        _ = n * x := by group
    rw [center_unitaryPSU, Subgroup.mem_bot] at hn
    rw [hn]
    rfl
  · exfalso
    have h1 : frobHomI (Multiplicative.ofAdd 1) = frobQI := by
      change frobPowI 1 = frobQI
      rw [frobPowI, ite_eq_right (by decide)]
    rw [h1] at hk
    have h2 : frobQI = MulAut.conj n⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hk
    have h3 := congr_frobQI
    rw [h2, congr_conj] at h3
    exact fBar_ne_conj _ h3.symm

theorem ringEquiv_F4_cases (σ : F4 ≃+* F4) :
    σ = RingEquiv.refl F4 ∨ σ = barEquiv := by
  have hω : σ F4.ω * σ F4.ω + σ F4.ω + 1 = 0 := by
    rw [← map_mul, ← map_add, ← map_one σ, ← map_add,
      show F4.ω * F4.ω + F4.ω + 1 = 0 from Certificates.certificate16005.1, map_zero]
  have hcases : ∀ y : F4, y * y + y + 1 = 0 → y = F4.ω ∨ y = F4.ω * F4.ω :=
    Certificates.certificate16005.2.1
  have hall : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = 1 + F4.ω :=
    Certificates.certificate16005.2.2.1
  have hbar : ∀ x : F4, barEquiv x = x * x := fun x => by
    rw [barEquiv_apply, hF4.bar_apply, pow_one, sq]
  rcases hcases _ hω with h | h
  · left
    refine RingEquiv.ext fun x => ?_
    rcases hall x with rfl | rfl | rfl | rfl
    · exact map_zero σ
    · exact map_one σ
    · exact h
    · rw [map_add, map_one, h]
      rfl
  · right
    refine RingEquiv.ext fun x => ?_
    rw [hbar]
    rcases hall x with rfl | rfl | rfl | rfl
    · rw [map_zero, mul_zero]
    · rw [map_one, mul_one]
    · exact h
    · rw [map_add, map_one, h]
      exact Certificates.certificate16005.2.2.2.1

theorem primeFormFieldHom_cases (φ : F4 ≃+* F4) :
    primeFormFieldHom hF4 isPrimeFormGram_one6 φ = 1 ∨
      primeFormFieldHom hF4 isPrimeFormGram_one6 φ = fBar := by
  rcases ringEquiv_F4_cases φ with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

theorem conj_mul_fBar_mul_inv
    (A : primeFormUnitary hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :
    primeFormConjHom hF4 _ A * fBar * (primeFormConjHom hF4 _ A)⁻¹ =
      primeFormConjHom hF4 _ (A * primeFormFieldU hF4 isPrimeFormGram_one6 barEquiv A⁻¹) *
        fBar := by
  have h := primeFormField_conj_eq hF4 isPrimeFormGram_one6 barEquiv A⁻¹
  rw [map_mul, ← h, map_inv]
  group

theorem det_eq_one_of_conj
    (A : primeFormUnitary hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
    (s : gramSU hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
    (h : primeFormConjHom hF4 _ (A * primeFormFieldU hF4 isPrimeFormGram_one6 barEquiv A⁻¹) =
      MulAut.conj (s : PI)) :
    ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
  set s' : primeFormUnitary hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
    ⟨s, (mem_gramSU_iff_unitary hF4).1 s.2 |>.1⟩ with hs'
  rw [conj_mk_eq_primeFormConjHom] at h
  have h1 : primeFormConjHom hF4 _ (s'⁻¹ * (A * primeFormFieldU hF4 isPrimeFormGram_one6
      barEquiv A⁻¹)) = 1 := by
    rw [map_mul, h, map_inv, inv_mul_cancel]
  have h2 := (primeFormPsi_eq_one_iff hF4 isPrimeFormGram_one6 (by norm_num)
    ⟨s'⁻¹ * (A * primeFormFieldU hF4 isPrimeFormGram_one6 barEquiv A⁻¹),
      RingEquiv.refl F4⟩).1 (by
    rw [primeFormPsi_apply, show primeFormFieldHom hF4 isPrimeFormGram_one6
      (RingEquiv.refl F4) = 1 from map_one _, mul_one, h1])
  obtain ⟨c, -, hc⟩ := h2.2
  set X : GL (Fin 6) F4 := ((s'⁻¹ * (A * primeFormFieldU hF4 isPrimeFormGram_one6 barEquiv A⁻¹) :
    primeFormUnitary hF4 _) : GL (Fin 6) F4) with hX
  change X = Matrix.GeneralLinearGroup.scalar (Fin 6) c at hc
  have hdet : ((Matrix.GeneralLinearGroup.det X : F4ˣ) : F4) = (c : F4) ^ 6 := by
    rw [hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
  have hs1 : ((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 :=
    ((mem_gramSU_iff_unitary hF4).1 s.2).2
  set d := ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero (A : GL (Fin 6) F4)
  set e' := (((A : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det with he'
  have hAinv : e' * d = 1 := by
    rw [he', hd, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hsinv : (((s : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
    have h := Matrix.det_mul (((s : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
      ((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
    rw [Units.inv_mul, Matrix.det_one, hs1, mul_one] at h
    exact h.symm
  have hbarA : ((glAut barEquiv ((A : GL (Fin 6) F4)⁻¹) : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4).det = barEquiv e' := by
    rw [coe_glAut, he', RingEquiv.map_det]
    rfl
  have hXe : X = (s : GL (Fin 6) F4)⁻¹ * ((A : GL (Fin 6) F4) *
      glAut barEquiv ((A : GL (Fin 6) F4)⁻¹)) := by
    rw [hX, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU,
      Subgroup.coe_inv]
  have e : ((Matrix.GeneralLinearGroup.det X : F4ˣ) : F4) = d * barEquiv e' := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hXe, Units.val_mul, Units.val_mul,
      Matrix.det_mul, Matrix.det_mul, hsinv, one_mul, hbarA]
  rw [e] at hdet
  have hbar : ∀ x : F4, barEquiv x = x * x := fun x => by
    rw [barEquiv_apply, hF4.bar_apply, pow_one, sq]
  rw [hbar] at hdet
  have key : ∀ d e c : F4, e * d = 1 → d * (e * e) = c ^ 6 → c ≠ 0 → d = 1 :=
    Certificates.certificate16005.2.2.2.2
  exact key d e' c hAinv hdet c.ne_zero

theorem fieldFactor_conjHom
    (B : primeFormUnitary hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :
    fieldFactor (primeFormConjHom hF4 _ B) = RingEquiv.refl F4 := by
  have h := primeFormFieldFactor_apply hF4 isPrimeFormGram_one6 (by norm_num) (by norm_num) B
    (RingEquiv.refl F4)
  rwa [show primeFormFieldHom hF4 isPrimeFormGram_one6 (RingEquiv.refl F4) = 1 from map_one _,
    mul_one] at h

theorem frobHomI_one : frobHomI (Multiplicative.ofAdd 1) = frobQI := by
  change frobPowI 1 = frobQI
  rw [frobPowI, ite_eq_right (by decide)]

theorem kappaU_selfNormalizing (α : MulAut (unitaryPSU hF4 6))
    (hα : ∀ g, ∃ g', α * kappaU g * α⁻¹ = kappaU g') : ∃ g₀, α = kappaU g₀ := by
  set α' := MulAut.congr psuEquiv α with hα'
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor hF4 isPrimeFormGram_one6
    (by norm_num) (by norm_num) α'
  have hkt : kappaU ⟨1, Multiplicative.ofAdd 1⟩ = frobQI := by
    rw [kappaU_mk, map_one, one_mul, frobHomI_one]
  obtain ⟨g', hg'⟩ := hα ⟨1, Multiplicative.ofAdd 1⟩
  rw [hkt] at hg'
  have hg'' := congrArg (MulAut.congr psuEquiv) hg'
  rw [map_mul, map_mul, map_inv, congr_frobQI, ← hα'] at hg''
  obtain ⟨l', ε'⟩ := g'
  rw [kappaU_mk, map_mul, congr_conj] at hg''
  have hFcomm : primeFormFieldHom hF4 isPrimeFormGram_one6 φ * fBar *
      (primeFormFieldHom hF4 isPrimeFormGram_one6 φ)⁻¹ = fBar := by
    rcases primeFormFieldHom_cases φ with h | h <;> rw [h] <;> group
  have hLHS : α' * fBar * α'⁻¹ =
      primeFormConjHom hF4 _ (A * primeFormFieldU hF4 isPrimeFormGram_one6 barEquiv A⁻¹) *
        fBar := by
    calc α' * fBar * α'⁻¹ = primeFormConjHom hF4 _ A * (primeFormFieldHom hF4
          isPrimeFormGram_one6 φ * fBar * (primeFormFieldHom hF4 isPrimeFormGram_one6 φ)⁻¹) *
          (primeFormConjHom hF4 _ A)⁻¹ := by rw [hA]; group
      _ = primeFormConjHom hF4 _ A * fBar * (primeFormConjHom hF4 _ A)⁻¹ := by rw [hFcomm]
      _ = _ := conj_mul_fBar_mul_inv A
  rw [hLHS] at hg''
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (psuEquiv l')
  induction ε' using Multiplicative.rec with
  | ofAdd ε' =>
  rcases zmod2_cases' ε' with rfl | rfl
  · exfalso
    have h0 : MulAut.congr psuEquiv (frobHomI (Multiplicative.ofAdd 0)) = 1 := by
      rw [show frobHomI (Multiplicative.ofAdd (0 : ZMod 2)) = 1 from map_one _, map_one]
    rw [h0, mul_one] at hg''
    have h1 := congrArg fieldFactor hg''
    rw [map_mul, fieldFactor_fBar, fieldFactor_conjHom, ← hs, fieldFactor_conj] at h1
    exact barEquiv_ne_refl ((by simpa using h1 : barEquiv = 1).trans rfl)
  · rw [frobHomI_one, congr_frobQI, mul_left_inj, ← hs] at hg''
    have hdet := det_eq_one_of_conj A s hg''
    set sA : gramSU hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
      ⟨A, (mem_gramSU_iff_unitary hF4).2 ⟨A.2, hdet⟩⟩ with hsA
    have hcA : primeFormConjHom hF4 _ A = MulAut.conj (sA : PI) := by
      rw [conj_mk_eq_primeFormConjHom]
    rw [hcA] at hA
    rcases primeFormFieldHom_cases φ with hφ | hφ
    · refine ⟨⟨psuEquiv.symm (sA : PI), Multiplicative.ofAdd 0⟩,
        (MulAut.congr psuEquiv).injective ?_⟩
      rw [← hα', hA, hφ, kappaU_mk, map_mul, congr_conj, MulEquiv.apply_symm_apply,
        show frobHomI (Multiplicative.ofAdd (0 : ZMod 2)) = 1 from map_one _, map_one]
    · refine ⟨⟨psuEquiv.symm (sA : PI), Multiplicative.ofAdd 1⟩,
        (MulAut.congr psuEquiv).injective ?_⟩
      rw [← hα', hA, hφ, kappaU_mk, map_mul, congr_conj, MulEquiv.apply_symm_apply,
        frobHomI_one, congr_frobQI]

theorem PSU62_mulAut_eq_conj
    (τ : MulAut PSU62) : ∃ g, τ = MulAut.conj g :=
  mulAut_eq_conj_of_selfNormalizing SemidirectProduct.inl SemidirectProduct.inl_injective kappaU
    inl_kappaU exists_inl_eq eq_one_of_forall_commute kappaU_selfNormalizing τ

theorem mulAut_eq_conj_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ τ : MulAut H, ∃ g, τ = MulAut.conj g) (τ : MulAut G) : ∃ g, τ = MulAut.conj g := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e τ)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h1 := congrArg (fun σ : MulAut H => σ (e x)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem p1Quot_mulAut_eq_conj
    (τ : MulAut (CFSG.Monster.B.TwoA.Sp8.P1 ⧸ CFSG.Monster.B.TwoA.Sp8.N1.subgroupOf
      CFSG.Monster.B.TwoA.Sp8.P1)) : ∃ g, τ = MulAut.conj g := by
  obtain ⟨e⟩ := CFSG.Monster.B.TwoA.Sp8.nonempty_p1Quot_PSU62
  exact mulAut_eq_conj_of_mulEquiv e PSU62_mulAut_eq_conj τ

theorem Usig_mulAut_eq_conj
    (τ : MulAut Usig) : ∃ g, τ = MulAut.conj g := by
  obtain ⟨e⟩ := CFSG.Monster.B.TwoA.Sp8.nonempty_p1Quot_PSU62
  exact mulAut_eq_conj_of_mulEquiv (CFSG.Monster.B.TwoA.Sp8.p1QuotEquiv.symm.trans e)
    PSU62_mulAut_eq_conj τ

end CFSG.Monster.B.GSide
