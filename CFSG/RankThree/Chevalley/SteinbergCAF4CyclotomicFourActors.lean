module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourNonregular
public import CFSG.RankThree.Chevalley.SteinbergBNF4OddDescendedRootCore
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups SteinbergBN EvenF4QPlus RootSpace CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.LieType.Steinberg.Adjoint
open Subgroup
open scoped Pointwise

variable (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]

theorem exists_ne_one_map_eq_one_of_card_sq {L P : Type*} [Field L] [Group P] {p : ℕ}
    (hp : p.Prime) (hP : ∀ a : P, a ^ p = 1) (hcard : Nat.card P = p ^ 2) (χ : P →* Lˣ) :
    ∃ a : P, a ≠ 1 ∧ χ a = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hχ : Function.Injective χ := by
    intro a b hab
    by_contra hne
    have h1 : a * b⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h)
    exact hcon _ h1 (by rw [map_mul, map_inv, hab, mul_inv_cancel])
  have : Finite χ.range := Finite.of_equiv P (MonoidHom.ofInjective hχ).toEquiv
  have : IsCyclic χ.range := isCyclic_subgroup_units χ.range
  have : IsCyclic P := isCyclic_of_surjective (MonoidHom.ofInjective hχ).symm.toMonoidHom
    (MonoidHom.ofInjective hχ).symm.surjective
  have hexp : Monoid.exponent P ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hP
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.two_le]

theorem eq_one_of_torusRootChar_single {z : ModGL Tag.F4 Ω} (hz : z ∈ torusGroup Tag.F4 Ω)
    (h : ∀ i, torusRootChar z (Pi.single i 1) = 1) : z = 1 := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hz
  have hc : c = 1 := funext fun i => by
    have h1 := h i
    rw [torusRootChar_rootDiagUnit c (isRoot_single Tag.F4 i), rootChar_pi_single] at h1
    exact Units.val_eq_one.1 h1
  rw [hc, rootDiagUnit_one]

theorem conj_inv_baseChange_mem {g x : ModGL Tag.F4 Ω} {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹)
    {y : adjointGroup Tag.F4 K}
    (hy : y ∈ centralizer ({x₁} : Set (adjointGroup Tag.F4 K))) :
    g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g ∈
      conjEntrywiseImage K g⁻¹ ⊓ centralizer {x} := by
  refine ⟨⟨y, y.2, ?_⟩, mem_centralizer_singleton_iff.2 ?_⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  · have h1 : baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) *
        baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) =
        baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) *
          baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) := by
      rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        mem_centralizer_singleton_iff.1 hy]
    rw [hx₁] at h1
    calc g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g * x =
          g⁻¹ * (baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * (g * x * g⁻¹)) * g := by
            group
      _ = g⁻¹ * ((g * x * g⁻¹) * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K)) * g := by
            rw [h1]
      _ = x * (g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g) := by group

theorem exists_injective_pi_of_conj_mem {N : Type*} [CommGroup N] {T₀ : Subgroup (ModGL Tag.F4 Ω)}
    (e : T₀ ≃* N × N) (g : ModGL Tag.F4 Ω) (X : Subgroup (adjointGroup Tag.F4 K))
    (hX : ∀ y ∈ X, g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g ∈ T₀) :
    ∃ φ : X →* (Fin Tag.G2.rank → N), Function.Injective φ := by
  classical
  set ψ : X →* T₀ := ((MulAut.conj g⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K Ω)).comp
    ((adjointGroup Tag.F4 K).subtype.comp X.subtype))).codRestrict T₀ fun y => by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Subgroup.coe_subtype] using hX y y.2 with hψ
  have hψinj : Function.Injective ψ := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    simp only [hψ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype, mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext (Subtype.ext (baseChangeGL_injective _ h1))
  refine ⟨{ toFun := fun z i => if i.val = 0 then (e (ψ z)).1 else (e (ψ z)).2
            map_one' := by
              funext i
              split_ifs <;> simp
            map_mul' := fun a b => by
              funext i
              simp only [Pi.mul_apply, map_mul, Prod.fst_mul, Prod.snd_mul]
              split_ifs <;> rfl }, fun a b hab => ?_⟩
  have h0 : (e (ψ a)).1 = (e (ψ b)).1 := by simpa using congrFun hab ⟨0, by decide⟩
  have h1 : (e (ψ a)).2 = (e (ψ b)).2 := by
    have h := congrFun hab ⟨1, by decide⟩
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, one_ne_zero, ↓reduceIte] at h
    exact h
  exact hψinj (e.injective (Prod.ext h0 h1))

theorem mul_comm_of_conj_mem_torusGroup (g : ModGL Tag.F4 Ω) (X : Subgroup (adjointGroup Tag.F4 K))
    (hX : ∀ y ∈ X, g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g ∈
      torusGroup Tag.F4 Ω) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro a ha b hb
  have h1 := mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (hX a ha))
    (torusGroup_le_diagonalGroup (hX b hb))
  apply Subtype.ext
  apply baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  calc baseChangeGL (algebraMap K Ω) (a : ModGL Tag.F4 K) *
        baseChangeGL (algebraMap K Ω) (b : ModGL Tag.F4 K) =
      g * ((g⁻¹ * baseChangeGL (algebraMap K Ω) (a : ModGL Tag.F4 K) * g) *
        (g⁻¹ * baseChangeGL (algebraMap K Ω) (b : ModGL Tag.F4 K) * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * baseChangeGL (algebraMap K Ω) (b : ModGL Tag.F4 K) * g) *
        (g⁻¹ * baseChangeGL (algebraMap K Ω) (a : ModGL Tag.F4 K) * g)) * g⁻¹ := by rw [h1]
    _ = _ := by group

variable [Finite K] [IsAlgClosure K Ω] (F : Ω →+* Ω)

theorem exists_lang_torus_coordinates (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1) (P : Subgroup (adjointGroup Tag.F4 K))
    (hP : IsPGroup p P) :
    ∃ g ∈ adjointGroup Tag.F4 Ω, g⁻¹ * Units.map (entrywiseHom F) g =
        canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3) ∧
      ∀ y ∈ P, ∃ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹,
        baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) = g * x * g⁻¹ := by
  classical
  have hT := F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF _ rfl
  obtain ⟨g₀, hg₀, hg₀n⟩ := hT.1
  obtain ⟨-, -, -, hpr, -⟩ := hT.2 g₀ hg₀ hg₀n _ _ _ rfl rfl rfl
  obtain ⟨-, hconjP, -, -⟩ := hpr p hp hp3 hpd
  obtain ⟨c, hc⟩ := hconjP P hP
  set bc := baseChangeGL (τ := Tag.F4) (algebraMap K Ω) with hbc
  have hcG : bc (c : ModGL Tag.F4 K) ∈ adjointGroup Tag.F4 Ω :=
    baseChangeGL_mem_adjointGroup _ c.2
  have hFc : Units.map (entrywiseHom F) (bc (c : ModGL Tag.F4 K)) = bc c :=
    units_map_entrywiseHom_baseChangeGL_algebraMap F hF _
  refine ⟨(bc (c : ModGL Tag.F4 K))⁻¹ * g₀, mul_mem (inv_mem hcG) hg₀, ?_, fun y hy => ?_⟩
  · rw [map_mul, map_inv, hFc, ← hg₀n]
    group
  · obtain ⟨x, ⟨hxH, -⟩, hxe⟩ := hc ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, map_mul, map_inv] at hxe
    have hy' : bc (y : ModGL Tag.F4 K) =
        ((bc (c : ModGL Tag.F4 K))⁻¹ * g₀) * x * ((bc (c : ModGL Tag.F4 K))⁻¹ * g₀)⁻¹ := by
      calc bc (y : ModGL Tag.F4 K) = (bc (c : ModGL Tag.F4 K))⁻¹ *
            (bc (c : ModGL Tag.F4 K) * bc (y : ModGL Tag.F4 K) * (bc (c : ModGL Tag.F4 K))⁻¹) *
              bc (c : ModGL Tag.F4 K) := by group
        _ = _ := by rw [← hxe]; group
    refine ⟨x, ⟨hxH, y, y.2, ?_⟩, hy'⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hbc, hy']
    group

theorem F4_four_torus_data (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + 1) {g : ModGL Tag.F4 Ω} (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3)) :
    Nonempty ((torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ : Subgroup (ModGL Tag.F4 Ω)) ≃*
      Multiplicative (ZMod (Nat.card K ^ 2 + 1)) × Multiplicative (ZMod (Nat.card K ^ 2 + 1))) ∧
    ∀ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹, orderOf x = p →
      {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} = ∅ →
        conjEntrywiseImage K g⁻¹ ⊓ centralizer {x} =
          torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ := by
  obtain ⟨-, he, -, hpr, -⟩ := (F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF
    _ rfl).2 g hg hgn _ _ _ rfl rfl rfl
  obtain ⟨-, -, -, hcls⟩ := hpr p hp hp3 hpd
  exact ⟨he, fun x hx hxp => (hcls x hx hxp _ rfl).2.2⟩

theorem exists_lang_coordinate (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1) {x₁ : adjointGroup Tag.F4 K}
    (hx₁p : orderOf x₁ = p) :
    ∃ g ∈ adjointGroup Tag.F4 Ω, g⁻¹ * Units.map (entrywiseHom F) g =
        canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3) ∧
      ∃ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹, orderOf x = p ∧
        baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹ := by
  have hP : IsPGroup p (zpowers x₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₁p, pow_one])
  obtain ⟨g, hg, hgn, hc⟩ := exists_lang_torus_coordinates K Ω F hF hp hp3 hpd _ hP
  obtain ⟨x, hx, hx₁⟩ := hc x₁ (mem_zpowers x₁)
  refine ⟨g, hg, hgn, x, hx, ?_, hx₁⟩
  have hinj : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup Tag.F4 K).subtype) :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective
  have h1 := orderOf_injective _ hinj x₁
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hx₁, hx₁p] at h1
  rw [← h1, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
    orderOf_injective _ (MulAut.conj g).injective]

theorem F4_four_nonregular_actor {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + 1) (B : Subgroup (MulAut (adjointGroup Tag.F4 K)))
    (hB : (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range ≤ B)
    {g : ModGL Tag.F4 Ω} (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g =
      canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3))
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    Nonempty ((⁅centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₁} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) ≃*
        matrixIsometryGroup (f4J0 K)) ∧
    inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x₁, hB ⟨x₁, rfl⟩⟩ : B)} : Set B)) ≤
      (centralizer ({x₁} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₁} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
            Set (adjointGroup Tag.F4 K))).map
        ((MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).codRestrict B
          fun c => hB ⟨c, rfl⟩) ∧
    ∀ y ∈ centralizer ({x₁} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₁} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
            Set (adjointGroup Tag.F4 K)),
      g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g ∈
          torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ ∧
        ∀ α ∈ {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1},
          torusRootChar (g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g) α = 1 := by
  classical
  set n := canonicalRep (coxeterSystem Tag.F4) Ω (f4Coxeter ^ 3) with hn
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup Tag.F4 Ω ⊓ Γ with hT₀
  obtain ⟨-, -, -, hpr, -⟩ := (F4_cyclotomic_four_torus_and_regular_prime_centralizers K Ω F hF n
    rfl).2 g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) rfl rfl rfl
  obtain ⟨-, -, -, hcls⟩ := hpr p hp hp3 hpd
  obtain ⟨hcase, -, -⟩ := hcls x hx hxp _ rfl
  obtain ⟨u, ε, hε, hu, huw⟩ := hcase.resolve_left hne.ne_empty
  set h := canonicalRep (coxeterSystem Tag.F4) Ω u with hh
  set Γ₁ := Γ.map (MulAut.conj h).toMonoidHom with hΓ₁
  set D := Γ₁ ⊓ centralizer {h * x * h⁻¹} with hD
  set R := ⁅D, D⁆ with hR
  obtain ⟨-, ⟨-, -, -, -, e, -, -⟩, hRq, -, -, -, -, ⟨-, hCDR, -, -⟩,
      ⟨x₀, hx₀, hD₀, hR₀', R₀, hR₀le, M, -, kM, -, hkeq⟩, hroot⟩ :=
    odd_F4_cyclotomic_four_nonregular_derived_centralizers hℓ hℓ2 hf K hK Ω F hF hp hp3 n g rfl hg
      hgn Γ T₀ rfl rfl x hx hxp u ε hε hu huw h (h * x * h⁻¹) rfl rfl Γ₁ D R rfl rfl rfl
  have hx₀₁ : x₀ = x₁ :=
    Subtype.ext (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω) (hx₀.trans hx₁.symm))
  subst hx₀₁
  set ι' : adjointGroup Tag.F4 K →* ModGL Tag.F4 Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype with hι'
  have hι'inj : Function.Injective ι' :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective
  have eR : (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) ≃* R :=
    (Subgroup.equivMapOfInjective _ ι' hι'inj).trans ((MulEquiv.subgroupCongr hR₀').trans
      (Subgroup.equivMapOfInjective R _ (MulAut.conj (g * h⁻¹)).injective).symm)
  have hRL := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hRq)
  have hconj1 : ((Matrix.SpecialLinearGroup.map (algebraMap K M)).range.map
      (CFSG.RankThree.Classical.conjSL (1 : GL (Fin 2) M))) =
        (Matrix.SpecialLinearGroup.map (algebraMap K M)).range := by
    have h1 : CFSG.RankThree.Classical.conjSL (1 : GL (Fin 2) M) = MonoidHom.id _ :=
      MonoidHom.ext fun A => Subtype.ext (by
        simp only [CFSG.RankThree.Classical.conjSL, Units.val_one, inv_one, Matrix.one_mul,
          Matrix.mul_one]
        rfl)
    rw [h1, Subgroup.map_id]
  have hS := odd_F4_descended_root_layer_local_core_contained_in_derived_centralizer hℓ hℓ2 hf
    K hK hp B hB x₀ hRL R₀ hR₀le M (algebraMap K M) .short (kM : ModGL Tag.F4 M) 1
    (by rw [hconj1]; exact hkeq)
  refine ⟨⟨eR.trans e⟩, hS, fun y hy => ?_⟩
  obtain ⟨hyC, hyR⟩ := hy
  have h1 : ι' y ∈ (centralizer ({x₀} : Set (adjointGroup Tag.F4 K))).map ι' := ⟨y, hyC, rfl⟩
  rw [hD₀] at h1
  obtain ⟨d, hdD, hdy⟩ := h1
  have hdR : d ∈ centralizer (R : Set (ModGL Tag.F4 Ω)) := by
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : (MulAut.conj (g * h⁻¹)).toMonoidHom r ∈
        (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)).map
            ι' := by
      rw [hR₀']
      exact ⟨r, hr, rfl⟩
    obtain ⟨r', hr'R, hr'e⟩ := hr'
    have hc := mem_centralizer_iff.1 hyR r' hr'R
    have hdy' : (MulAut.conj (g * h⁻¹)) d = ι' y := hdy
    have hr'e' : ι' r' = (MulAut.conj (g * h⁻¹)) r := hr'e
    apply (MulAut.conj (g * h⁻¹)).injective
    rw [map_mul (MulAut.conj (g * h⁻¹)) r d, map_mul (MulAut.conj (g * h⁻¹)) d r, hdy', ← hr'e',
      ← map_mul ι', ← map_mul ι', hc]
  have hdDR : d ∈ D ⊓ centralizer (R : Set (ModGL Tag.F4 Ω)) := ⟨hdD, hdR⟩
  have hkey : g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g = h⁻¹ * d * h⁻¹⁻¹ := by
    change g⁻¹ * ι' y * g = _
    rw [← hdy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨⟨t₀, ht₀, ht₀d⟩, -, -⟩ := (hCDR d).1 hdDR
  refine ⟨?_, fun α hα => ?_⟩
  · rw [hkey, ← ht₀d]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show h⁻¹ * (h * t₀ * h⁻¹) * h⁻¹⁻¹ = t₀ by group]
    exact ht₀
  · rw [hkey]
    exact hroot α hα _ ⟨d, hdDR, rfl⟩

end CFSG.RankThree.Chevalley
