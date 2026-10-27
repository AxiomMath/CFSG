module

public import CFSG.Milestones.ASVolI.A3Aut.L2
public import CFSG.Milestones.ASVolI.A3Aut.Core2
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallSL2
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.LieType.Chevalley.E6GraphInvolutionForms

public section

namespace CFSG.Walter

open CFSG.Open CFSG.GorensteinWalter CFSG.ASVolI CFSG.SeitzReduction.LinearPilot
open CFSG.GroupTheory
open scoped MatrixGroups

theorem psl2QuotientMap_injective_of_charTwo {K : Type} [Field K] [CharP K 2] :
    Function.Injective (psl2QuotientMap K) := by
  change Function.Injective (QuotientGroup.mk' (Subgroup.center (SL(2, K))))
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
    CFSG.Walter.sl2_center_eq_bot_of_charTwo]

theorem burnsideAut_sl2DiagHom_injective (K : Type) [Field K] :
    Function.Injective (burnsideAut_sl2DiagHom K) := by
  intro l m h
  have h' := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change (l : K) = (m : K) at h'
  exact Units.ext h'

private theorem orderOf_psl2DiagHom {K : Type} [Field K] [CharP K 2] (l : Kˣ) :
    orderOf (psl2QuotientMap K (burnsideAut_sl2DiagHom K l)) = orderOf l := by
  rw [orderOf_injective (psl2QuotientMap K) psl2QuotientMap_injective_of_charTwo]
  exact orderOf_injective (burnsideAut_sl2DiagHom K) (burnsideAut_sl2DiagHom_injective K) l

theorem psl2FieldAut_diag_fixed {K : Type} [Field K] (σ : K ≃+* K) (l : Kˣ)
    (hl : σ (l : K) = (l : K)) :
    psl2FieldAut K σ (psl2QuotientMap K (burnsideAut_sl2DiagHom K l)) =
      psl2QuotientMap K (burnsideAut_sl2DiagHom K l) := by
  rw [burnsideAut_psl2FieldAut_diag]
  congr 1
  have hu : ((Units.map (σ : K →* K) l : Kˣ) : K) = (l : K) := by simpa using hl
  exact congrArg (burnsideAut_sl2DiagHom K) (Units.ext hu)

theorem psl2DiagHom_comm {K : Type} [Field K] (l m : Kˣ) :
    psl2QuotientMap K (burnsideAut_sl2DiagHom K l) *
        psl2QuotientMap K (burnsideAut_sl2DiagHom K m) =
      psl2QuotientMap K (burnsideAut_sl2DiagHom K m) *
        psl2QuotientMap K (burnsideAut_sl2DiagHom K l) := by
  change (psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K) l *
      (psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K) m =
    (psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K) m *
      (psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K) l
  rw [← map_mul, ← map_mul, mul_comm l m]

private theorem fixedField_card_eq_two_pow {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (σ : K ≃+* K) :
    let R := FixedPoints.subfield (Subgroup.zpowers σ) K
    Nat.card R = 2 ^ (a / orderOf σ) := by
  let R := FixedPoints.subfield (Subgroup.zpowers σ) K
  have hAut : Nat.card (RingAut K) = a :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have : Finite (RingAut K) := Finite.of_injective (fun e : RingAut K => (e : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have he : orderOf σ ∣ a := by rw [← hAut]; exact orderOf_dvd_natCard σ
  have hcard : Nat.card K = Nat.card R ^ orderOf σ :=
    CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf K σ
  have hmul : a / orderOf σ * orderOf σ = a := Nat.div_mul_cancel he
  have hpow : Nat.card R ^ orderOf σ = (2 ^ (a / orderOf σ)) ^ orderOf σ := by
    calc Nat.card R ^ orderOf σ = Nat.card K := hcard.symm
      _ = 2 ^ a := hK
      _ = 2 ^ (a / orderOf σ * orderOf σ) := by rw [hmul]
      _ = (2 ^ (a / orderOf σ)) ^ orderOf σ := pow_mul ..
  exact Nat.pow_left_injective (orderOf_pos σ).ne' hpow

private theorem exists_fixed_unit {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (σ : K ≃+* K) :
    ∃ μ : Kˣ, σ (μ : K) = (μ : K) ∧ orderOf μ = 2 ^ (a / orderOf σ) - 1 := by
  let R := FixedPoints.subfield (Subgroup.zpowers σ) K
  let : IsCyclic Rˣ := inferInstance
  obtain ⟨μR, hμR⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Rˣ)
  let μ : Kˣ := Units.map (R.subtype : R →+* K).toMonoidHom μR
  have hinj : Function.Injective (Units.map (R.subtype : R →+* K).toMonoidHom) := by
    intro x y h
    apply Units.ext
    apply (R.subtype : R →+* K).injective
    exact congrArg (fun u : Kˣ => (u : K)) h
  have hμord : orderOf μ = orderOf μR := orderOf_injective _ hinj μR
  refine ⟨μ, ?_, ?_⟩
  · change σ (((μR : R) : R) : K) = (((μR : R) : R) : K)
    exact (CFSG.Walter.mem_fixedSubfield_iff σ _).mp (μR : R).2
  · rw [hμord, hμR, Nat.card_units, fixedField_card_eq_two_pow hK σ]

private noncomputable def psl2DiagInner (K : Type) [Field K] :
    Subgroup (MulAut (PSL2 K)) :=
  (burnsideAut_psl2Diag K).map (MulAut.conj : PSL2 K →* MulAut (PSL2 K))

private noncomputable def psl2InnerU (K : Type) [Field K] :
    Subgroup (MulAut (PSL2 K)) :=
  (psl2UpperUnipotentSubgroup K).map (MulAut.conj : PSL2 K →* MulAut (PSL2 K))

private theorem odd_card_psl2DiagInner {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha1 : 1 ≤ a) : Odd (Nat.card (psl2DiagInner K)) := by
  rw [psl2DiagInner, Subgroup.card_map_of_injective
    (CFSG.ASVolI.burnsideAut_conj_injective (CFSG.GorensteinWalter.psl2_center_eq_bot K))]
  exact burnsideAut_card_psl2Diag_odd ha1 hK

private theorem psl2FieldAut_mem_normalizer_diagInner {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) :
    psl2FieldAut K σ ∈
      Subgroup.normalizer (psl2DiagInner K : Set (MulAut (PSL2 K))) :=
  burnsideAut_mem_normalizer_map_conj (burnsideAut_map_psl2FieldAut_diag σ)

private theorem psl2DiagInner_inf_zpowers_field {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) :
    psl2DiagInner K ⊓ Subgroup.zpowers (psl2FieldAut K σ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx.1
  have hxInn : MulAut.conj y ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range :=
    ⟨y, rfl⟩
  have hxField : MulAut.conj y ∈ (psl2FieldAut K).range :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨σ, rfl⟩) hx.2
  have hxboth : MulAut.conj y ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range ⊓
      (psl2FieldAut K).range := ⟨hxInn, hxField⟩
  rw [burnsideAut_psl2_inn_inf_field] at hxboth
  exact Subgroup.mem_bot.mp hxboth

private theorem odd_orderOf_conj_mul_field {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha1 : 1 ≤ a) {d : PSL2 K}
    (hd : d ∈ burnsideAut_psl2Diag K) (σ : K ≃+* K) (hσ : Odd (orderOf σ)) :
    Odd (orderOf (MulAut.conj d * psl2FieldAut K σ)) := by
  let T := psl2DiagInner K
  let C := Subgroup.zpowers (psl2FieldAut K σ)
  have hCT : C ≤ Subgroup.normalizer (T : Set (MulAut (PSL2 K))) :=
    Subgroup.zpowers_le.mpr (psl2FieldAut_mem_normalizer_diagInner σ)
  have hcard :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C) (K := T) hCT
  have hdisj : C ⊓ T = ⊥ := by
    rw [inf_comm]
    exact psl2DiagInner_inf_zpowers_field σ
  have hCop : Nat.card C * Nat.card T = Nat.card (T ⊔ C : Subgroup (MulAut (PSL2 K))) := by
    rw [← hcard, sup_comm, hdisj]
    simp
  have hCodd : Odd (Nat.card C) := by
    rw [show Nat.card C = orderOf (psl2FieldAut K σ) from Nat.card_zpowers _]
    rw [orderOf_injective (psl2FieldAut K) (psl2FieldAut_injective K) σ]
    exact hσ
  have hTodd : Odd (Nat.card T) := odd_card_psl2DiagInner hK ha1
  have hodd : Odd (Nat.card (T ⊔ C : Subgroup (MulAut (PSL2 K)))) := by
    rw [← hCop]
    exact hCodd.mul hTodd
  have hmem : MulAut.conj d * psl2FieldAut K σ ∈
      (T ⊔ C : Subgroup (MulAut (PSL2 K))) := by
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ hd)
      (Subgroup.mem_zpowers (psl2FieldAut K σ))
  have hdvd := orderOf_dvd_natCard
    (⟨_, hmem⟩ : (T ⊔ C : Subgroup (MulAut (PSL2 K))))
  rw [Subgroup.orderOf_mk] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

private theorem sup_zpowers_eq_sup_of_mul_mem {A : Type} [Group A] {E : Subgroup A}
    {θ₀ θ₁ u : A} (hu : u ∈ E) (hθ : θ₁ = u * θ₀) :
    E ⊔ Subgroup.zpowers θ₁ = E ⊔ Subgroup.zpowers θ₀ := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    refine Subgroup.zpowers_le.mpr ?_
    rw [hθ]
    exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers θ₀)
  · refine sup_le le_sup_left ?_
    refine Subgroup.zpowers_le.mpr ?_
    have hθ₀ : θ₀ = u⁻¹ * θ₁ := by rw [hθ]; group
    rw [hθ₀]
    exact Subgroup.mul_mem_sup (E.inv_mem hu) (Subgroup.mem_zpowers θ₁)

private theorem card_zpowers_eq_of_mul_mem {A : Type} [Group A] [Finite A]
    {E : Subgroup A} (hE2 : IsPGroup 2 E) {θ₀ θ₁ u : A} (hu : u ∈ E)
    (hθ : θ₁ = u * θ₀)
    (hC : Subgroup.zpowers θ₁ ≤ Subgroup.normalizer (E : Set A))
    (hX : Subgroup.zpowers θ₀ ≤ Subgroup.normalizer (E : Set A))
    (hCodd : Odd (Nat.card (Subgroup.zpowers θ₁)))
    (hXodd : Odd (Nat.card (Subgroup.zpowers θ₀))) :
    Nat.card (Subgroup.zpowers θ₁) = Nat.card (Subgroup.zpowers θ₀) := by
  let C := Subgroup.zpowers θ₁
  let X := Subgroup.zpowers θ₀
  have hCE : C ⊓ E = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_two_of_odd (H := E) (K := C) hE2 hCodd
  have hXE : X ⊓ E = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_two_of_odd (H := E) (K := X) hE2 hXodd
  have hsup : E ⊔ C = E ⊔ X := sup_zpowers_eq_sup_of_mul_mem hu hθ
  have hcardC :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C) (K := E) hC
  have hcardX :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := X) (K := E) hX
  have h1 : Nat.card C * Nat.card E = Nat.card (C ⊔ E : Subgroup A) := by
    rw [← hcardC, hCE]
    simp
  have h2 : Nat.card X * Nat.card E = Nat.card (X ⊔ E : Subgroup A) := by
    rw [← hcardX, hXE]
    simp
  have hEpos : 0 < Nat.card E := Nat.card_pos
  apply Nat.mul_right_cancel hEpos
  rw [h1, h2, sup_comm C E, sup_comm X E, hsup]

private theorem exists_diag_fixed_element {K : Type} [Field K] [Finite K] [CharP K 2]
    {a : ℕ} (hK : Nat.card K = 2 ^ a) (σ : K ≃+* K) {d : PSL2 K}
    (hd : d ∈ burnsideAut_psl2Diag K) :
    ∃ y : PSL2 K, orderOf y = 2 ^ (a / orderOf σ) - 1 ∧
      (MulAut.conj d * psl2FieldAut K σ) y = y := by
  obtain ⟨μ, hμfix, hμord⟩ := exists_fixed_unit hK σ
  obtain ⟨lam, rfl⟩ := MonoidHom.mem_range.mp hd
  let y := psl2QuotientMap K (burnsideAut_sl2DiagHom K μ)
  have hyord : orderOf y = 2 ^ (a / orderOf σ) - 1 := by
    rw [show orderOf y = orderOf μ from orderOf_psl2DiagHom μ, hμord]
  refine ⟨y, hyord, ?_⟩
  have hσy : psl2FieldAut K σ y = y := psl2FieldAut_diag_fixed σ μ hμfix
  rw [MulAut.mul_apply, MulAut.conj_apply, hσy]
  have hcomm : psl2QuotientMap K (burnsideAut_sl2DiagHom K lam) * y =
      y * psl2QuotientMap K (burnsideAut_sl2DiagHom K lam) := psl2DiagHom_comm lam μ
  calc psl2QuotientMap K (burnsideAut_sl2DiagHom K lam) * y *
        (psl2QuotientMap K (burnsideAut_sl2DiagHom K lam))⁻¹ =
      y * psl2QuotientMap K (burnsideAut_sl2DiagHom K lam) *
        (psl2QuotientMap K (burnsideAut_sl2DiagHom K lam))⁻¹ := by rw [hcomm]
    _ = y := by group

private theorem fixedField_card_two_of_div_eq_one {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (σ : K ≃+* K) (hs : a / orderOf σ = 1) :
    let R := FixedPoints.subfield (Subgroup.zpowers σ) K
    Nat.card R = 2 ∧ Subsingleton Rˣ := by
  let R := FixedPoints.subfield (Subgroup.zpowers σ) K
  have hRcard : Nat.card R = 2 := by
    have h := fixedField_card_eq_two_pow hK σ
    rw [hs] at h
    simpa [R] using h
  have hcardUnits : Nat.card Rˣ = 1 := by
    rw [Nat.card_units, hRcard]
  exact ⟨hRcard, (Nat.card_eq_one_iff_unique.mp hcardUnits).1⟩

private theorem fieldMuConj_injective_of_fixedField_card_two {K : Type} [Field K]
    (σ : K ≃+* K)
    (hR : Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) K) = 2) :
    Function.Injective (fun μ : Kˣ => μ * (Units.map (σ : K →* K) μ)⁻¹) := by
  let R := FixedPoints.subfield (Subgroup.zpowers σ) K
  let σu : Kˣ →* Kˣ := Units.map (σ : K →* K)
  have hR' : Nat.card R = 2 := hR
  have hcardUnits : Nat.card Rˣ = 1 := by
    rw [Nat.card_units, hR']
  haveI : Subsingleton Rˣ := (Nat.card_eq_one_iff_unique.mp hcardUnits).1
  intro μ ν h
  change μ * (σu μ)⁻¹ = ν * (σu ν)⁻¹ at h
  have hfix : σu (ν⁻¹ * μ) = ν⁻¹ * μ := by
    rw [map_mul, map_inv]
    calc (σu ν)⁻¹ * σu μ = ν⁻¹ * (ν * (σu ν)⁻¹) * σu μ := by group
      _ = ν⁻¹ * (μ * (σu μ)⁻¹) * σu μ := by rw [← h]
      _ = ν⁻¹ * μ := by group
  have hmem : ((ν⁻¹ * μ : Kˣ) : K) ∈ R := by
    rw [CFSG.Walter.mem_fixedSubfield_iff]
    simpa [σu] using congrArg Units.val hfix
  let xR : R := ⟨((ν⁻¹ * μ : Kˣ) : K), hmem⟩
  have hx0 : xR ≠ 0 := by
    intro h0
    have hzero : ((ν⁻¹ * μ : Kˣ) : K) = 0 := congrArg Subtype.val h0
    exact (ν⁻¹ * μ).ne_zero hzero
  let uR : Rˣ := Units.mk0 xR hx0
  have huR : uR = 1 := Subsingleton.elim _ _
  have hx1 : xR = 1 := by
    have := congrArg (fun u : Rˣ => (u : R)) huR
    simpa [uR] using this
  have hval : ((ν⁻¹ * μ : Kˣ) : K) = 1 := congrArg Subtype.val hx1
  have hνμ : ν⁻¹ * μ = 1 := Units.ext (by simpa using hval)
  calc μ = ν * (ν⁻¹ * μ) := by group
    _ = ν := by rw [hνμ, mul_one]

private theorem exists_mul_inv_eq_of_fixedField_card_two {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K)
    (hR : Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) K) = 2) (lam : Kˣ) :
    ∃ μ : Kˣ, μ * (Units.map (σ : K →* K) μ)⁻¹ = lam := by
  exact Finite.surjective_of_injective
    (fieldMuConj_injective_of_fixedField_card_two σ hR) lam

private theorem orderThreeSL2_image_order_and_fixed {K : Type} [Field K] [CharP K 2]
    (σ : K ≃+* K) :
    let z := psl2QuotientMap K
      (CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2 K)
    orderOf z = 3 ∧ psl2FieldAut K σ z = z := by
  let z := psl2QuotientMap K
    (CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2 K)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hzpow : z ^ 3 = 1 := by
    change (psl2QuotientMap K
      (CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2 K)) ^ 3 = 1
    rw [← map_pow,
      CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2_pow_three h2, map_one]
  have hzne : z ≠ 1 := by
    intro h
    apply CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2_ne_one h2
    apply psl2QuotientMap_injective_of_charTwo
    simpa [z] using h
  refine ⟨orderOf_eq_prime hzpow hzne, ?_⟩
  show psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center (SL(2, K)))
    (CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2 K)) =
    QuotientGroup.mk' (Subgroup.center (SL(2, K)))
      (CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2 K)
  rw [psl2RingEquiv_mk]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    CFSG.LieType.Chevalley.E6GraphInvolution.coe_orderThreeSL2 h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_orderThree_fixed_of_s_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {a : ℕ} (hK : Nat.card K = 2 ^ a) (σ : K ≃+* K) {d : PSL2 K}
    (hd : d ∈ burnsideAut_psl2Diag K) (hs : a / orderOf σ = 1) :
    ∃ y : PSL2 K, orderOf y = 3 ∧ (MulAut.conj d * psl2FieldAut K σ) y = y := by
  obtain ⟨lam, rfl⟩ := MonoidHom.mem_range.mp hd
  obtain ⟨hRcard, _⟩ := fixedField_card_two_of_div_eq_one hK σ hs
  obtain ⟨μ, hμ⟩ := exists_mul_inv_eq_of_fixedField_card_two σ hRcard lam
  let B := psl2QuotientMap K (burnsideAut_sl2DiagHom K μ)
  let z := psl2QuotientMap K (CFSG.LieType.Chevalley.E6GraphInvolution.orderThreeSL2 K)
  obtain ⟨hzord, hzfix⟩ := orderThreeSL2_image_order_and_fixed (K := K) σ
  have hzord' : orderOf z = 3 := hzord
  have hzfix' : psl2FieldAut K σ z = z := hzfix
  have hd' : psl2QuotientMap K (burnsideAut_sl2DiagHom K lam) =
      B * (psl2FieldAut K σ B)⁻¹ := by
    let F : Kˣ →* PSL2 K := (psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K)
    have h := congrArg F hμ
    have hσB : F (Units.map (σ : K →* K) μ) = psl2FieldAut K σ B :=
      (burnsideAut_psl2FieldAut_diag σ μ).symm
    rw [map_mul, map_inv, hσB] at h
    exact h.symm
  refine ⟨B * z * B⁻¹, ?_, ?_⟩
  · change orderOf (MulAut.conj B z) = 3
    rw [MulEquiv.orderOf_eq, hzord']
  · change (MulAut.conj (psl2QuotientMap K (burnsideAut_sl2DiagHom K lam)) *
      psl2FieldAut K σ) (B * z * B⁻¹) = B * z * B⁻¹
    rw [hd', MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hzfix']
    group

private theorem psl2FieldAut_inv_maps_upper {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) :
    (psl2UpperUnipotentSubgroup K).map ((psl2FieldAut K σ)⁻¹).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
  have hσU := burnsideAut_map_psl2FieldAut_upper σ
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu' : u ∈ (psl2UpperUnipotentSubgroup K).map
        (psl2FieldAut K σ).toMonoidHom := by rw [hσU]; exact hu
    obtain ⟨v, hv, hvu⟩ := hu'
    rw [← hvu]
    change ((psl2FieldAut K σ)⁻¹ * psl2FieldAut K σ) v ∈
      psl2UpperUnipotentSubgroup K
    rw [inv_mul_cancel, MulAut.one_apply]
    exact hv
  · rw [Subgroup.card_map_of_injective (psl2FieldAut K σ).symm.injective]

private theorem mem_borel_of_conj_maps_upper {K : Type} [Field K] [Finite K] [CharP K 2]
    {θ : MulAut (PSL2 K)} {σ : K ≃+* K} {g : PSL2 K}
    (hθU : (psl2UpperUnipotentSubgroup K).map θ.toMonoidHom =
      psl2UpperUnipotentSubgroup K)
    (hθeq : θ = MulAut.conj g * psl2FieldAut K σ) :
    g ∈ psl2Borel K := by
  have hσinv := psl2FieldAut_inv_maps_upper σ
  have hconjU : (psl2UpperUnipotentSubgroup K).map (MulAut.conj g).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
    have hg_eq : MulAut.conj g = θ * (psl2FieldAut K σ)⁻¹ := by
      rw [hθeq]
      group
    rw [hg_eq, show (θ * (psl2FieldAut K σ)⁻¹).toMonoidHom =
      θ.toMonoidHom.comp ((psl2FieldAut K σ)⁻¹).toMonoidHom from rfl]
    rw [← Subgroup.map_map, hσinv, hθU]
  have hgN : g ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjU
  rw [← psl2UpperUnipotent_normalizer_eq_borel]
  exact hgN

theorem exists_mul_mem_upper_diag_of_mem_borel {K : Type} [Field K] [Finite K]
    {g : PSL2 K} (hgB : g ∈ psl2Borel K) :
    ∃ u d : PSL2 K, u ∈ psl2UpperUnipotentSubgroup K ∧
      d ∈ burnsideAut_psl2Diag K ∧ u * d = g := by
  let UB : Subgroup (psl2Borel K) :=
    (psl2UpperUnipotentSubgroup K).subgroupOf (psl2Borel K)
  let DB : Subgroup (psl2Borel K) :=
    (burnsideAut_psl2Diag K).subgroupOf (psl2Borel K)
  have hUB : UB.Normal := psl2UpperUnipotent_normal_in_borel
  have hgBsup : (⟨g, hgB⟩ : psl2Borel K) ∈ UB ⊔ DB := by
    have hmem : (⟨g, hgB⟩ : psl2Borel K) ∈
        (psl2UpperUnipotentSubgroup K ⊔ burnsideAut_psl2Diag K).subgroupOf
          (psl2Borel K) := by
      rw [← burnsideAut_psl2Borel_eq_sup]
      simpa using Subgroup.mem_top (⟨g, hgB⟩ : psl2Borel K)
    rwa [Subgroup.subgroupOf_sup psl2UpperUnipotent_le_borel
      burnsideAut_psl2Diag_le_borel] at hmem
  obtain ⟨uB, huB, dB, hdB, hudB⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := UB) (t := DB)).mp hgBsup
  exact ⟨(uB : PSL2 K), (dB : PSL2 K), huB, hdB, congrArg Subtype.val hudB⟩

theorem exists_factorization_of_normalizes_upper {K : Type} [Field K] [Finite K]
    [CharP K 2] {a : ℕ} (hK : Nat.card K = 2 ^ a) {θ : MulAut (PSL2 K)}
    (hθU : (psl2UpperUnipotentSubgroup K).map θ.toMonoidHom =
      psl2UpperUnipotentSubgroup K) :
    ∃ (u d : PSL2 K) (σ : K ≃+* K),
      u ∈ psl2UpperUnipotentSubgroup K ∧ d ∈ burnsideAut_psl2Diag K ∧
      θ = MulAut.conj u * (MulAut.conj d * psl2FieldAut K σ) := by
  obtain ⟨gP, σ, hθeq⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut θ
  obtain ⟨g, hg⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective K gP
  have hθeq' : θ = MulAut.conj g * psl2FieldAut K σ := by
    rw [hθeq, ← hg,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL]
  have hgB : g ∈ psl2Borel K := mem_borel_of_conj_maps_upper hθU hθeq'
  obtain ⟨u, d, hu, hd, hud⟩ := exists_mul_mem_upper_diag_of_mem_borel hgB
  refine ⟨u, d, σ, hu, hd, ?_⟩
  rw [hθeq', ← hud, map_mul]
  group

private theorem exists_conj_map_zpowers_eq_of_mul_mem {A : Type} [Group A] [Finite A]
    {E : Subgroup A} (hE2 : IsPGroup 2 E)
    {θ θ₀ u : A} (hu : u ∈ E)
    (hθeq : θ = u * θ₀) (hθodd : Odd (orderOf θ))
    (hCnorm : Subgroup.zpowers θ ≤ Subgroup.normalizer (E : Set A))
    (hXnorm : Subgroup.zpowers θ₀ ≤ Subgroup.normalizer (E : Set A))
    (hXodd : Odd (Nat.card (Subgroup.zpowers θ₀))) :
    ∃ e ∈ E, Subgroup.zpowers θ₀ =
      (Subgroup.zpowers θ).map (MulAut.conj e).toMonoidHom := by
  let C := Subgroup.zpowers θ
  let X := Subgroup.zpowers θ₀
  have hCodd : Odd (Nat.card C) := by
    rw [show Nat.card C = orderOf θ from Nat.card_zpowers θ]
    exact hθodd
  have hEC : E ⊓ C = ⊥ :=
    inf_eq_bot_of_isPGroup_two_of_odd (H := E) (K := C) hE2 hCodd
  have hθ₀mem : θ₀ ∈ E ⊔ C := by
    have hθ₀eq : θ₀ = u⁻¹ * θ := by rw [hθeq]; group
    rw [hθ₀eq]
    exact Subgroup.mul_mem_sup (E.inv_mem hu) (Subgroup.mem_zpowers θ)
  have hXY : X ≤ E ⊔ C := Subgroup.zpowers_le.mpr hθ₀mem
  obtain ⟨e, heE, hXle⟩ := burnsideAut_le_conj_complement
    (E := E) (Y := E ⊔ C) (C := C) (X := X)
    (sup_le Subgroup.le_normalizer hCnorm) hE2 le_sup_right hEC rfl hXY hXodd
  have hcardCX : Nat.card C = Nat.card X :=
    card_zpowers_eq_of_mul_mem (E := E) hE2 hu hθeq hCnorm hXnorm hCodd hXodd
  have hXeq : X = C.map (MulAut.conj e).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hXle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj e).injective, hcardCX]
  exact ⟨e, heE, hXeq⟩

private theorem exists_fixed_of_mul_mem_two_group {A : Type} [Group A] [Finite A]
    {E : Subgroup (MulAut A)} (hE2 : IsPGroup 2 E)
    {θ θ₀ u : MulAut A} (hu : u ∈ E)
    (hθeq : θ = u * θ₀) (hθodd : Odd (orderOf θ))
    (hCnorm : Subgroup.zpowers θ ≤ Subgroup.normalizer (E : Set (MulAut A)))
    (hXnorm : Subgroup.zpowers θ₀ ≤ Subgroup.normalizer (E : Set (MulAut A)))
    (hXodd : Odd (Nat.card (Subgroup.zpowers θ₀)))
    {y : A} (hyfix : θ₀ y = y) :
    ∃ x : A, orderOf x = orderOf y ∧ θ x = x := by
  obtain ⟨e, heE, hXeq⟩ := exists_conj_map_zpowers_eq_of_mul_mem
    (A := MulAut A) hE2 hu hθeq hθodd hCnorm hXnorm hXodd
  let g₁ : MulAut A := (MulAut.conj e) θ
  have hg₁X : g₁ ∈ Subgroup.zpowers θ₀ := by
    rw [hXeq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers θ)
  have hg₁fix : g₁ y = y := by
    let Hy : Subgroup (MulAut A) := MulAction.stabilizer (MulAut A) y
    have hθ₀Hy : θ₀ ∈ Hy := by
      simpa [Hy, MulAut.smul_def] using hyfix
    exact (Subgroup.zpowers_le.mpr hθ₀Hy) hg₁X
  have hθfix : θ (e.symm y) = e.symm y := by
    have h1 : e (θ (e.symm y)) = y := by
      simpa [g₁, MulAut.conj_apply, MulAut.mul_apply] using hg₁fix
    simpa using congrArg e.symm h1
  exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq], hθfix⟩

private theorem fieldPart_s_dvd {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha1 : 1 ≤ a) {θ : MulAut (PSL2 K)} {u d : PSL2 K}
    {σ : K ≃+* K} (hθ : Odd (orderOf θ))
    (hθfac : θ = MulAut.conj u * (MulAut.conj d * psl2FieldAut K σ)) :
    let s := a / orderOf σ
    s ∣ a ∧ Odd (a / s) ∧ Odd (orderOf σ) := by
  have hσfield : psl2FieldPart K θ = σ := by
    rw [hθfac, map_mul, map_mul, psl2FieldPart_conj, psl2FieldPart_conj,
      psl2FieldPart_psl2FieldAut, one_mul, one_mul]
  have he_dvd_θ : orderOf σ ∣ orderOf θ := by
    rw [← hσfield]
    exact orderOf_map_dvd (psl2FieldPart K) θ
  have he_odd : Odd (orderOf σ) := hθ.of_dvd_nat he_dvd_θ
  have he_dvd_a : orderOf σ ∣ a := by
    have hAut : Nat.card (RingAut K) = a :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
    have : Finite (RingAut K) := Finite.of_injective (fun e : RingAut K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
    rw [← hAut]
    exact orderOf_dvd_natCard σ
  let s := a / orderOf σ
  have hs_dvd : s ∣ a := ⟨orderOf σ, (Nat.div_mul_cancel he_dvd_a).symm⟩
  have hs_odd : Odd (a / s) := by
    have ha0 : a ≠ 0 := by omega
    rw [show a / s = orderOf σ from Nat.div_div_self he_dvd_a ha0]
    exact he_odd
  exact ⟨hs_dvd, hs_odd, he_odd⟩

private theorem psl2InnerU_isPGroup {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) : IsPGroup 2 (psl2InnerU K) := by
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hK
  have hU2 : IsPGroup 2 (psl2UpperUnipotentSubgroup K) := by
    rw [← hQ]
    exact Q.isPGroup'
  exact hU2.map (MulAut.conj : PSL2 K →* MulAut (PSL2 K))

private theorem conj_diag_field_maps_upper {K : Type} [Field K] [Finite K] {d : PSL2 K}
    (hd : d ∈ burnsideAut_psl2Diag K) (σ : K ≃+* K) :
    (psl2UpperUnipotentSubgroup K).map
      (MulAut.conj d * psl2FieldAut K σ).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
  have hdU : (psl2UpperUnipotentSubgroup K).map (MulAut.conj d).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
    have hdB : d ∈ psl2Borel K := burnsideAut_psl2Diag_le_borel hd
    have hdN : d ∈ Subgroup.normalizer
        ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)) := by
      rw [psl2UpperUnipotent_normalizer_eq_borel]
      exact hdB
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN
  rw [show (MulAut.conj d * psl2FieldAut K σ).toMonoidHom =
    (MulAut.conj d).toMonoidHom.comp (psl2FieldAut K σ).toMonoidHom from rfl]
  rw [← Subgroup.map_map, burnsideAut_map_psl2FieldAut_upper, hdU]

private theorem psl2_even_fixed_points_of_normalizes_upper {K : Type} [Field K] [Finite K]
    {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha1 : 1 ≤ a)
    (θ : MulAut (PSL2 K)) (hθ : Odd (orderOf θ))
    (hθU : (psl2UpperUnipotentSubgroup K).map θ.toMonoidHom =
      psl2UpperUnipotentSubgroup K) :
    ∃ s : ℕ, s ∣ a ∧ Odd (a / s) ∧
      (∃ x : PSL2 K, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
      (s = 1 → ∃ x : PSL2 K, orderOf x = 3 ∧ θ x = x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨u, d, σ, hu, hd, hθfac⟩ :=
    exists_factorization_of_normalizes_upper hK hθU
  let θ₀ : MulAut (PSL2 K) := MulAut.conj d * psl2FieldAut K σ
  let s := a / orderOf σ
  obtain ⟨hs_dvd, hs_odd, he_odd⟩ := fieldPart_s_dvd hK ha1 hθ hθfac
  obtain ⟨y, hyord, hyfix⟩ := exists_diag_fixed_element hK σ hd
  let E := psl2InnerU K
  have hE2 : IsPGroup 2 E := psl2InnerU_isPGroup hK
  have hCnorm : Subgroup.zpowers θ ≤
      Subgroup.normalizer (E : Set (MulAut (PSL2 K))) :=
    Subgroup.zpowers_le.mpr (burnsideAut_mem_normalizer_map_conj hθU)
  have hXnorm : Subgroup.zpowers θ₀ ≤
      Subgroup.normalizer (E : Set (MulAut (PSL2 K))) :=
    Subgroup.zpowers_le.mpr (burnsideAut_mem_normalizer_map_conj
      (conj_diag_field_maps_upper hd σ))
  have hXodd : Odd (Nat.card (Subgroup.zpowers θ₀)) := by
    rw [show Nat.card (Subgroup.zpowers θ₀) = orderOf θ₀ from Nat.card_zpowers θ₀]
    exact odd_orderOf_conj_mul_field hK ha1 hd σ he_odd
  obtain ⟨x, hxord, hxfix⟩ := exists_fixed_of_mul_mem_two_group (E := E) hE2
    (u := MulAut.conj u) (Subgroup.mem_map_of_mem _ hu) hθfac hθ hCnorm hXnorm hXodd hyfix
  refine ⟨s, hs_dvd, hs_odd, ⟨x, ?_, hxfix⟩, ?_⟩
  · rw [hxord, hyord]
  · intro hs1
    obtain ⟨z, hzord, hzfix⟩ := exists_orderThree_fixed_of_s_one hK σ hd hs1
    obtain ⟨x₃, hx₃ord, hx₃fix⟩ := exists_fixed_of_mul_mem_two_group (E := E) hE2
      (u := MulAut.conj u) (Subgroup.mem_map_of_mem _ hu) hθfac hθ hCnorm hXnorm hXodd hzfix
    exact ⟨x₃, by rw [hx₃ord, hzord], hx₃fix⟩

theorem exists_conj_upper_of_sylow {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (S : Sylow 2 (PSL2 K)) :
    ∃ h : PSL2 K, (psl2UpperUnipotentSubgroup K).map (MulAut.conj h).toMonoidHom =
      (S : Subgroup (PSL2 K)) := by
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hK
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 K) Q S
  have hhsub : (Q : Subgroup (PSL2 K)).map (MulAut.conj h).toMonoidHom =
      (S : Subgroup (PSL2 K)) := by
    have h := congrArg (fun T : Sylow 2 (PSL2 K) => (T : Subgroup (PSL2 K))) hh
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    convert h using 2
    ext x
    rfl
  refine ⟨h, ?_⟩
  rw [← hQ]
  exact hhsub

theorem conj_theta_maps_upper {K : Type} [Field K] [Finite K]
    {θ : MulAut (PSL2 K)} {S : Sylow 2 (PSL2 K)} {h : PSL2 K}
    (hhU : (psl2UpperUnipotentSubgroup K).map (MulAut.conj h).toMonoidHom =
      (S : Subgroup (PSL2 K)))
    (hS : ∀ x ∈ (S : Subgroup (PSL2 K)), θ x ∈ (S : Subgroup (PSL2 K))) :
    (psl2UpperUnipotentSubgroup K).map
      (MulAut.conj (MulAut.conj h)⁻¹ θ).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
  have hSinv : ∀ y ∈ (S : Subgroup (PSL2 K)), MulAut.conj h⁻¹ y ∈
      psl2UpperUnipotentSubgroup K := by
    intro y hy
    have hy' : y ∈ (psl2UpperUnipotentSubgroup K).map
        (MulAut.conj h).toMonoidHom := by rw [hhU]; exact hy
    obtain ⟨u, hu, huy⟩ := hy'
    rw [← huy]
    have hcinv : MulAut.conj h⁻¹ = (MulAut.conj h)⁻¹ := by
      ext x
      simp [MulAut.conj_apply]
    rw [hcinv]
    change (MulAut.conj h)⁻¹ ((MulAut.conj h) u) ∈
      psl2UpperUnipotentSubgroup K
    rw [MulAut.inv_apply_self]
    exact hu
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    have h1 : MulAut.conj h u ∈ (S : Subgroup (PSL2 K)) := by
      have : MulAut.conj h u ∈ (psl2UpperUnipotentSubgroup K).map
          (MulAut.conj h).toMonoidHom := Subgroup.mem_map_of_mem _ hu
      rwa [hhU] at this
    have h2 : θ (MulAut.conj h u) ∈ (S : Subgroup (PSL2 K)) := hS _ h1
    have h3 := hSinv _ h2
    simpa [MulAut.mul_apply, MulAut.conj_apply] using h3
  · rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj h)⁻¹ θ).injective]

private theorem exists_fixed_of_conj_mul {A : Type} [Group A] (θ θ₁ : MulAut A) (h : A)
    (hθeq : θ = MulAut.conj h * θ₁ * (MulAut.conj h)⁻¹) {y : A} (hy : θ₁ y = y) :
    ∃ x : A, orderOf x = orderOf y ∧ θ x = x := by
  refine ⟨MulAut.conj h y, by rw [MulEquiv.orderOf_eq], ?_⟩
  calc θ (MulAut.conj h y) =
      (MulAut.conj h * θ₁ * (MulAut.conj h)⁻¹) (MulAut.conj h y) :=
        congrArg (fun φ : MulAut A => φ (MulAut.conj h y)) hθeq
    _ = MulAut.conj h (θ₁ ((MulAut.conj h)⁻¹ ((MulAut.conj h) y))) := by
        rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = MulAut.conj h (θ₁ y) := by rw [MulAut.inv_apply_self]
    _ = MulAut.conj h y := by rw [hy]

theorem psl2_even_odd_aut_fixed_points {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a)
    (θ : MulAut (PSL2 K)) (hθ : Odd (orderOf θ))
    (S : Sylow 2 (PSL2 K))
    (hS : ∀ x ∈ (S : Subgroup (PSL2 K)), θ x ∈ (S : Subgroup (PSL2 K))) :
    ∃ s : ℕ, s ∣ a ∧ Odd (a / s) ∧
      (∃ x : PSL2 K, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
      (s = 1 → ∃ x : PSL2 K, orderOf x = 3 ∧ θ x = x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ≤ Nat.card K := by
    have h := (Finite.one_lt_card (α := K))
    omega
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at hK
    omega
  obtain ⟨h, hhU⟩ := exists_conj_upper_of_sylow hK S
  let θ₁ : MulAut (PSL2 K) := MulAut.conj (MulAut.conj h)⁻¹ θ
  have hθ₁odd : Odd (orderOf θ₁) := by
    rw [show θ₁ = MulAut.conj (MulAut.conj h)⁻¹ θ from rfl,
      MulEquiv.orderOf_eq]
    exact hθ
  have hθ₁Umap : (psl2UpperUnipotentSubgroup K).map θ₁.toMonoidHom =
      psl2UpperUnipotentSubgroup K := conj_theta_maps_upper hhU hS
  obtain ⟨s, hsdvd, hsodd, ⟨y, hyord, hyfix⟩, hy3⟩ :=
    psl2_even_fixed_points_of_normalizes_upper hK ha1 θ₁ hθ₁odd hθ₁Umap
  have hθeq : θ = MulAut.conj h * θ₁ * (MulAut.conj h)⁻¹ := by
    rw [show θ₁ = (MulAut.conj h)⁻¹ * θ * MulAut.conj h from rfl]
    group
  refine ⟨s, hsdvd, hsodd, ?_, ?_⟩
  · obtain ⟨x, hxord, hxfix⟩ := exists_fixed_of_conj_mul θ θ₁ h hθeq hyfix
    exact ⟨x, by rw [hxord, hyord], hxfix⟩
  · intro hs1
    obtain ⟨z, hzord, hzfix⟩ := hy3 hs1
    obtain ⟨x, hxord, hxfix⟩ := exists_fixed_of_conj_mul θ θ₁ h hθeq hzfix
    exact ⟨x, by rw [hxord, hzord], hxfix⟩

end CFSG.Walter
