module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeSixNonregular
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourActors

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups SteinbergBN EvenF4QPlus RootSpace CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.LieType.Steinberg.Adjoint
open Subgroup
open scoped Pointwise

variable (K : Type) [Field K] [Finite K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (F : Ω →+* Ω)

theorem F4_three_six_torus_data (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} {ε : ℤ}
    {w : WeylGroup Tag.F4}
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    (hp : p.Prime) (hp3 : 3 < p) :
    (∃ g ∈ adjointGroup Tag.F4 Ω,
      g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w) ∧
    ∀ g ∈ adjointGroup Tag.F4 Ω,
      g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w →
      Odd (Nat.card (torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ :
        Subgroup (ModGL Tag.F4 Ω))) ∧
      (∀ P : Subgroup (adjointGroup Tag.F4 K), IsPGroup p P → ∃ c : adjointGroup Tag.F4 K,
        (P.map (MulAut.conj c).toMonoidHom).map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype) ≤
          (torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹).map (MulAut.conj g).toMonoidHom) ∧
      ∀ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹, orderOf x = p →
        ({α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} = ∅ ∨
          ∃ (u : WeylGroup Tag.F4) (κ : F4A2Kind) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧
            (fun α => u • α) '' {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} =
              parabolicRoots Tag.F4 {κ.i, κ.j} ∧
            ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots Tag.F4 {κ.i, κ.j}),
              weylAct Tag.F4 (u * w * u⁻¹) z =
                ε • weylAct Tag.F4 ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ δ) z) ∧
        ({α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} = ∅ →
          conjEntrywiseImage K g⁻¹ ⊓ centralizer {x} =
            torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹) := by
  classical
  have hcardT : ∀ (g : ModGL Tag.F4 Ω) (T₀ : Subgroup (ModGL Tag.F4 Ω)),
      Nat.card (T₀.map (MulAut.conj g).toMonoidHom) = Nat.card T₀ := fun g _ =>
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rcases hεw with ⟨rfl, rfl, hpd⟩ | ⟨rfl, rfl, hpd⟩
  · have hT := F4_cyclotomic_three_torus_and_regular_prime_centralizers K Ω F hF _ rfl
    refine ⟨hT.1, fun g hg hgn => ?_⟩
    obtain ⟨-, -, -, hodd, hpr, -⟩ := hT.2 g hg hgn _ _ _ rfl rfl rfl
    obtain ⟨-, hconjP, -, hcls⟩ := hpr p hp hp3 hpd
    refine ⟨hcardT g _ ▸ hodd, hconjP, fun x hx hxp => ?_⟩
    obtain ⟨hcase, -, hreg⟩ := hcls x hx hxp _ rfl
    refine ⟨?_, hreg⟩
    rcases hcase with h | ⟨u, i, j, δ, hij, hδ, hu, huw⟩
    · exact Or.inl h
    · right
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, .long, δ, hδ, hu, fun z hz => by rw [huw z hz, one_smul]; rfl⟩
      · exact ⟨u, .short, δ, hδ, hu, fun z hz => by rw [huw z hz, one_smul]; rfl⟩
  · have hT := F4_cyclotomic_six_torus_and_surviving_A2_kernels K Ω F hF _ rfl
    refine ⟨hT.2.2.2.1, fun g hg hgn => ?_⟩
    obtain ⟨-, -, -, hodd, hpr, -⟩ := hT.2.2.2.2 g hg hgn _ _ _ rfl rfl rfl
    obtain ⟨-, hconjP, -, hcls⟩ := hpr p hp hp3 hpd
    refine ⟨hcardT g _ ▸ hodd, hconjP, fun x hx hxp => ?_⟩
    obtain ⟨hcase, hreg⟩ := hcls x hx hxp _ rfl
    refine ⟨?_, hreg⟩
    rcases hcase with h | ⟨u, i, j, δ, hij, hδ, hu, huw⟩
    · exact Or.inl h
    · right
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, .long, δ, hδ, hu, fun z hz => by rw [huw z hz, neg_smul, one_smul]; rfl⟩
      · exact ⟨u, .short, δ, hδ, hu, fun z hz => by rw [huw z hz, neg_smul, one_smul]; rfl⟩

theorem exists_lang_torus_coordinates_three_six (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ}
    {ε : ℤ} {w : WeylGroup Tag.F4}
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    (hp : p.Prime) (hp3 : 3 < p) (P : Subgroup (adjointGroup Tag.F4 K)) (hP : IsPGroup p P) :
    ∃ g ∈ adjointGroup Tag.F4 Ω,
      g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w ∧
      ∀ y ∈ P, ∃ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹,
        baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) = g * x * g⁻¹ := by
  classical
  have hT := F4_three_six_torus_data K Ω F hF hεw hp hp3
  obtain ⟨g₀, hg₀, hg₀n⟩ := hT.1
  obtain ⟨-, hconjP, -⟩ := hT.2 g₀ hg₀ hg₀n
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

theorem exists_lang_coordinate_three_six (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} {ε : ℤ}
    {w : WeylGroup Tag.F4}
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    (hp : p.Prime) (hp3 : 3 < p) {x₁ : adjointGroup Tag.F4 K} (hx₁p : orderOf x₁ = p) :
    ∃ g ∈ adjointGroup Tag.F4 Ω,
      g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w ∧
      ∃ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹, orderOf x = p ∧
        baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹ := by
  have hP : IsPGroup p (zpowers x₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₁p, pow_one])
  obtain ⟨g, hg, hgn, hc⟩ := exists_lang_torus_coordinates_three_six K Ω F hF hεw hp hp3 _ hP
  obtain ⟨x, hx, hx₁⟩ := hc x₁ (mem_zpowers x₁)
  refine ⟨g, hg, hgn, x, hx, ?_, hx₁⟩
  have hinj : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup Tag.F4 K).subtype) :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective
  have h1 := orderOf_injective _ hinj x₁
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hx₁, hx₁p] at h1
  rw [← h1, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
    orderOf_injective _ (MulAut.conj g).injective]

theorem F4_three_six_regular_actor (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} {ε : ℤ}
    {w : WeylGroup Tag.F4}
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    (hp : p.Prime) (hp3 : 3 < p) {g : ModGL Tag.F4 Ω} (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w)
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hreg : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1} = ∅)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    Odd (Nat.card (centralizer ({x₁} : Set (adjointGroup Tag.F4 K)))) ∧
      (⁅centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₁} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) =
          ⊥ := by
  classical
  obtain ⟨hodd, -, hcls⟩ := (F4_three_six_torus_data K Ω F hF hεw hp hp3).2 g hg hgn
  have hT₀ := (hcls x hx hxp).2 hreg
  have hX : ∀ y ∈ centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
      g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g ∈
        torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ := fun y hy => by
    rw [← hT₀]
    exact conj_inv_baseChange_mem K Ω hx₁ hy
  set ι : adjointGroup Tag.F4 K →* ModGL Tag.F4 Ω := (MulAut.conj g⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype) with hι
  have hιinj : Function.Injective ι := (MulAut.conj g⁻¹).injective.comp
    ((baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective)
  have hle : (centralizer ({x₁} : Set (adjointGroup Tag.F4 K))).map ι ≤
      torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hX y hy
    simpa only [hι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.coe_subtype] using h1
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective hιinj] at h1
  refine ⟨hodd.of_dvd_nat h1, Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha =>
    mem_centralizer_iff.2 fun b hb => ?_⟩
  exact mul_comm_of_conj_mem_torusGroup K Ω g _ (fun y hy => (hX y hy).1) b hb a ha

theorem F4_three_six_nonregular_actor {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} {ε : ℤ}
    {w : WeylGroup Tag.F4}
    (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4 ∧ p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      (ε = -1 ∧ w = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1))
    (hp : p.Prime) (hp3 : 3 < p) (B : Subgroup (MulAut (adjointGroup Tag.F4 K)))
    (hB : (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range ≤ B)
    {g : ModGL Tag.F4 Ω} (hg : g ∈ adjointGroup Tag.F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = canonicalRep (coxeterSystem Tag.F4) Ω w)
    {x : ModGL Tag.F4 Ω} (hx : x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹)
    (hxp : orderOf x = p) (hne : {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty)
    {x₁ : adjointGroup Tag.F4 K}
    (hx₁ : baseChangeGL (algebraMap K Ω) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹) :
    (⁅centralizer ({x₁} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₁} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) ≠ ⊥ ∧
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x₁, hB ⟨x₁, rfl⟩⟩ : B)} : Set B)))) := by
  classical
  have hεw' : (ε = 1 ∧ w = f4Coxeter ^ 4) ∨ (ε = -1 ∧ w = f4PhiSix) := by
    rcases hεw with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    exacts [Or.inl ⟨h1, h2⟩, Or.inr ⟨h1, h2⟩]
  obtain ⟨-, -, hcls⟩ := (F4_three_six_torus_data K Ω F hF hεw hp hp3).2 g hg hgn
  obtain ⟨u, κ, δ, hδ, hu, huw⟩ := ((hcls x hx hxp).1).resolve_left hne.ne_empty
  set Γ := conjEntrywiseImage K g⁻¹ with hΓ
  set T₀ := torusGroup Tag.F4 Ω ⊓ Γ with hT₀
  set h := canonicalRep (coxeterSystem Tag.F4) Ω u with hh
  set Γ₁ := Γ.map (MulAut.conj h).toMonoidHom with hΓ₁
  set D := Γ₁ ⊓ centralizer {h * x * h⁻¹} with hD
  set R := ⁅D, D⁆ with hR
  obtain ⟨-, -, hRq, -, -, hRne, -, -, ⟨hZD, hoddZ, -⟩,
      ⟨x₀, hx₀, hD₀, hR₀', R₀, hR₀le, M, -, kM, -, hkeq⟩⟩ :=
    odd_F4_cyclotomic_three_six_nonregular_derived_centralizers hℓ hℓ2 hf K hK Ω F hF ε w hεw' hp
      hp3 _ g rfl hg hgn Γ T₀ rfl rfl x hx hxp u κ δ hδ hu huw h (h * x * h⁻¹) rfl rfl Γ₁ D R rfl
      rfl rfl
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
  have hne' : (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
      centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) ≠ ⊥ :=
    fun hbot => hRne (by
      have h1 := hR₀'
      rw [hbot, Subgroup.map_bot] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj (g * h⁻¹)).injective).1 h1.symm)
  have hX : ((centralizer ({x₀} : Set (adjointGroup Tag.F4 K)) ⊓
      centralizer ((⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
          Set (adjointGroup Tag.F4 K))).map ι').map (MulAut.conj (g * h⁻¹)⁻¹).toMonoidHom ≤
        D ⊓ centralizer (R : Set (ModGL Tag.F4 Ω)) := by
    rintro _ ⟨_, ⟨y, ⟨hyC, hyR⟩, rfl⟩, rfl⟩
    have h1 : ι' y ∈ (centralizer ({x₀} : Set (adjointGroup Tag.F4 K))).map ι' := ⟨y, hyC, rfl⟩
    rw [hD₀] at h1
    obtain ⟨d, hdD, hdy⟩ := h1
    have hdy' : (MulAut.conj (g * h⁻¹)) d = ι' y := hdy
    have hd : (MulAut.conj (g * h⁻¹)⁻¹).toMonoidHom (ι' y) = d := by
      rw [← hdy']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hd]
    refine ⟨hdD, mem_centralizer_iff.2 fun r hr => ?_⟩
    have hr' : (MulAut.conj (g * h⁻¹)).toMonoidHom r ∈
        (⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
          centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)).map
            ι' := by
      rw [hR₀']
      exact ⟨r, hr, rfl⟩
    obtain ⟨r', hr'R, hr'e⟩ := hr'
    have hc := mem_centralizer_iff.1 hyR r' hr'R
    have hr'e' : ι' r' = (MulAut.conj (g * h⁻¹)) r := hr'e
    apply (MulAut.conj (g * h⁻¹)).injective
    rw [map_mul (MulAut.conj (g * h⁻¹)) r d, map_mul (MulAut.conj (g * h⁻¹)) d r, hdy', ← hr'e',
      ← map_mul ι', ← map_mul ι', hc]
  have hoddDR : Odd (Nat.card (D ⊓ centralizer (R : Set (ModGL Tag.F4 Ω)) :
      Subgroup (ModGL Tag.F4 Ω))) := by
    rw [hZD, Subgroup.card_map_of_injective D.subtype_injective]
    exact hoddZ
  have hoddX : Odd (Nat.card (centralizer ({x₀} : Set (adjointGroup Tag.F4 K)) ⊓
      centralizer ((⁅centralizer ({x₀} : Set (adjointGroup Tag.F4 K)),
        centralizer ({x₀} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
          Set (adjointGroup Tag.F4 K)) : Subgroup (adjointGroup Tag.F4 K))) := by
    have h1 := Subgroup.card_dvd_of_le hX
    rw [Subgroup.card_map_of_injective (MulAut.conj (g * h⁻¹)⁻¹).injective,
      Subgroup.card_map_of_injective hι'inj] at h1
    exact hoddDR.of_dvd_nat h1
  have hconj1 : ((Matrix.SpecialLinearGroup.map (algebraMap K M)).range.map
      (CFSG.RankThree.Classical.conjSL (1 : GL (Fin 2) M))) =
        (Matrix.SpecialLinearGroup.map (algebraMap K M)).range := by
    have h1 : CFSG.RankThree.Classical.conjSL (1 : GL (Fin 2) M) = MonoidHom.id _ :=
      MonoidHom.ext fun A => Subtype.ext (by
        simp only [CFSG.RankThree.Classical.conjSL, Units.val_one, inv_one, Matrix.one_mul,
          Matrix.mul_one]
        rfl)
    rw [h1, Subgroup.map_id]
  have hK' : Nat.card K = ℓ ^ f := hK
  exact ⟨hne', odd_F4_descended_root_layer_centralizer_local_core_odd hℓ hℓ2 hf K hK' hp B hB x₀
    hRL hoddX R₀ hR₀le M (algebraMap K M) κ (kM : ModGL Tag.F4 M) 1
    (by rw [hconj1]; exact hkeq)⟩

end CFSG.RankThree.Chevalley
