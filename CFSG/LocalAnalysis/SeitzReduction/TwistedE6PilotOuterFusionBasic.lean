module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotOuterFusionBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

section Def

variable {C : Type*} [Group C]

@[expose] def TwistedFusionIn (η : MulAut C) (S : Set C) : Prop :=
  ⁅η.toMonoidHom.eqLocus (MonoidHom.id C), η.toMonoidHom.eqLocus (MonoidHom.id C)⁆ =
      η.toMonoidHom.eqLocus (MonoidHom.id C) ∧
    ∃ (m₀ : C) (y₀ : η.toMonoidHom.eqLocus (MonoidHom.id C)), (y₀ : C) ≠ 1 ∧
      (η m₀)⁻¹ * m₀ = y₀ ∧
      ∀ β : MulAut (η.toMonoidHom.eqLocus (MonoidHom.id C)), (β y₀ : C) ∈ S

end Def

@[expose] def OuterFusionIn {G C : Type*} [Group G] [Group C] (L : Subgroup G) (e : L ≃* C)
    (t : G) (S : Set C) : Prop :=
  ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∉ L ⊔ zpowers t →
    ∃ h : G, ∃ z : L, h⁻¹ * t * h = t * z ∧ z ≠ 1 ∧ e z ∈ S

section Coordinates

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_mulAut_conj_eq_of_family (hset : StandardSetting G L) {C : Type*} [Group C]
    (e : L ≃* C) {ι : Type*} {η : ι → MulAut C}
    (hcan : ∀ α : MulAut C, α ^ 2 = 1 → α ∉ (MulAut.conj : C →* MulAut C).range →
      ∃ (i : ι) (ψ : MulAut C), ψ * α * ψ⁻¹ = η i)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {x : G} (hxC : x ∈ centralizer ({t} : Set G)) (hx2 : x * x = 1)
    (hxL : x ∉ L ⊔ zpowers t) :
    ∃ (i : ι) (ψ : MulAut C), ∀ l l' : L, (l' : G) = x * l * x⁻¹ →
      ψ (e l') = η i (ψ (e l)) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hN : x ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht hxC
  set α : MulAut L := L.normalizerMonoidHom ⟨x, hN⟩ with hαdef
  have hα : ∀ l : L, ((α l : L) : G) = x * l * x⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hN⟩ l
  have hα2 : α ^ 2 = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [sq, MulAut.mul_apply, MulAut.one_apply, hα, hα]
    calc x * (x * (l : G) * x⁻¹) * x⁻¹ = (x * x) * l * (x * x)⁻¹ := by group
      _ = l := by rw [hx2, one_mul, inv_one, mul_one]
  have hαo : α ∉ (MulAut.conj : L →* MulAut L).range := by
    rintro ⟨l, hl⟩
    refine hxL (F4Pilot.mem_sup_zpowers_of_conj_eq htC ht hKt hxC l.2 fun y hy => ?_)
    have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h, hα]
  obtain ⟨i, ψ, hψ⟩ := hcan ((e.symm.trans α).trans e)
    ((F4Pilot.pow_two_conj_eq_one_iff e α).2 hα2)
    fun h => hαo ((F4Pilot.conj_mem_range_conj_iff e α).1 h)
  have hψ' : ∀ c, ψ (((e.symm.trans α).trans e) c) = η i (ψ c) := fun c => by
    rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  refine ⟨i, ψ, fun l l' hl' => ?_⟩
  have hl : l' = α l := Subtype.ext (hl'.trans (hα l).symm)
  rw [hl, ← hψ' (e l), F4Pilot.conj_mulEquiv_apply, MulEquiv.symm_apply_apply]

theorem exists_injective_fixedPoints (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {g : G} (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    {C : Type*} [Group C] (ε₁ ε₂ : L ≃* C) {η₁ η₂ : MulAut C}
    (hε₁ : ∀ l l' : L, (l' : G) = (g⁻¹ * t * g) * l * (g⁻¹ * t * g)⁻¹ → ε₁ l' = η₁ (ε₁ l))
    (hε₂ : ∀ l l' : L, (l' : G) = (g * t * g⁻¹) * l * (g * t * g⁻¹)⁻¹ → ε₂ l' = η₂ (ε₂ l))
    (hF : ⁅η₁.toMonoidHom.eqLocus (MonoidHom.id C), η₁.toMonoidHom.eqLocus (MonoidHom.id C)⁆ =
      η₁.toMonoidHom.eqLocus (MonoidHom.id C)) :
    ∃ β₀ : η₁.toMonoidHom.eqLocus (MonoidHom.id C) →* η₂.toMonoidHom.eqLocus (MonoidHom.id C),
      Function.Injective β₀ ∧ ∀ w : η₁.toMonoidHom.eqLocus (MonoidHom.id C),
        ∃ hw : g * (ε₁.symm w : G) * g⁻¹ ∈ L, (β₀ w : C) = ε₂ ⟨_, hw⟩ := by
  set F₁ := η₁.toMonoidHom.eqLocus (MonoidHom.id C) with hF₁def
  set F₂ := η₂.toMonoidHom.eqLocus (MonoidHom.id C) with hF₂def
  have hmemF₁ : ∀ c : C, c ∈ F₁ ↔ η₁ c = c := fun c => Iff.rfl
  have hmemF₂ : ∀ c : C, c ∈ F₂ ↔ η₂ c = c := fun c => Iff.rfl
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set s := g⁻¹ * t * g with hsdef
  have hsN : s ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht hsC
  have hsfix : ∀ a : L, ε₁ a ∈ F₁ → (a : G) * s = s * a := by
    intro a ha
    have hmem : s * (a : G) * s⁻¹ ∈ L := (mem_normalizer_iff.1 hsN a).1 a.2
    have h1 := hε₁ a ⟨_, hmem⟩ rfl
    rw [(hmemF₁ _).1 ha] at h1
    have h2 : s * (a : G) * s⁻¹ = a := congrArg Subtype.val (ε₁.injective h1)
    calc (a : G) * s = s * a * s⁻¹ * s := by rw [h2]
      _ = s * a := by group
  set Θ : Subgroup G := (F₁.map ε₁.symm.toMonoidHom).map L.subtype with hΘdef
  have hΘperf : ⁅Θ, Θ⁆ = Θ := by rw [hΘdef, ← map_commutator, ← map_commutator, hF]
  have hΘL : Θ ≤ L := map_subtype_le _
  have hΘt : Θ ≤ centralizer ({t} : Set G) :=
    hΘL.trans (CFSG.SeitzReduction.le_centralizer_of_mem_centralizer htC)
  have hΘs : Θ ≤ centralizer ({s} : Set G) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact hsfix (ε₁.symm w) (by simpa using hw)
  have hΘLg := std_perfect_le_inf_conjugate hset hOut htC ht g hΘperf hΘt hΘs
  have hgL : ∀ w ∈ F₁, g * (ε₁.symm w : G) * g⁻¹ ∈ L := by
    intro w hw
    have hmem : (ε₁.symm w : G) ∈ Θ := ⟨ε₁.symm w, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨l, hl, hl'⟩ := (hΘLg hmem).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hl'
    rw [← hl']
    simpa [mul_assoc] using hl
  have hFix2 : ∀ w (hw : w ∈ F₁), ε₂ ⟨g * (ε₁.symm w : G) * g⁻¹, hgL w hw⟩ ∈ F₂ := by
    intro w hw
    rw [hmemF₂]
    refine (hε₂ _ _ ?_).symm
    have hc := mem_centralizer_iff.1 htC _ (ε₁.symm w).2
    calc g * (ε₁.symm w : G) * g⁻¹ = g * ((ε₁.symm w : G) * t * t) * g⁻¹ := by
          rw [mul_assoc (ε₁.symm w : G), htt, mul_one]
      _ = g * (t * (ε₁.symm w : G) * t) * g⁻¹ := by rw [hc]
      _ = g * t * g⁻¹ * (g * (ε₁.symm w : G) * g⁻¹) * (g * t⁻¹ * g⁻¹) := by
          rw [inv_eq_of_mul_eq_one_right htt]
          group
      _ = g * t * g⁻¹ * (g * (ε₁.symm w : G) * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
  let φ₁ : F₁ →* G := (MulAut.conj g).toMonoidHom.comp
    (L.subtype.comp (ε₁.symm.toMonoidHom.comp F₁.subtype))
  have hφ₁ : ∀ w : F₁, φ₁ w = g * (ε₁.symm w : G) * g⁻¹ := fun w => rfl
  let φ₂ : F₁ →* L := φ₁.codRestrict L fun w => by rw [hφ₁]; exact hgL w w.2
  let β₀ : F₁ →* F₂ := (ε₂.toMonoidHom.comp φ₂).codRestrict F₂ fun w => hFix2 w w.2
  have hβ₀ : ∀ w : F₁, (β₀ w : C) = ε₂ ⟨g * (ε₁.symm w : G) * g⁻¹, hgL w w.2⟩ := fun w => rfl
  refine ⟨β₀, fun w w' h => ?_, fun w => ⟨hgL w w.2, hβ₀ w⟩⟩
  have h1 := congrArg Subtype.val h
  rw [hβ₀, hβ₀] at h1
  have h2 := congrArg Subtype.val (ε₂.injective h1)
  simp only at h2
  have h3 : (ε₁.symm w : G) = ε₁.symm w' := by
    have := congrArg (fun x => g⁻¹ * x * g) h2
    simpa [mul_assoc] using this
  exact Subtype.ext (ε₁.symm.injective (Subtype.ext h3))

end Coordinates

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem outerFusionIn_of_twistedFusionIn_of_outer (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {ι : Type*}
    (η : ι → MulAut C)
    (hcan : ∀ α : MulAut C, α ^ 2 = 1 → α ∉ (MulAut.conj : C →* MulAut C).range →
      ∃ (i : ι) (ψ : MulAut C), ψ * α * ψ⁻¹ = η i)
    (hdist : ∀ i j, Nat.card ((η i).toMonoidHom.eqLocus (MonoidHom.id C)) =
      Nat.card ((η j).toMonoidHom.eqLocus (MonoidHom.id C)) → i = j)
    (S : Set C) (hS : ∀ β : MulAut C, ∀ x ∈ S, β x ∈ S) (hη : ∀ i, TwistedFusionIn (η i) S)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hout : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∉ L ⊔ zpowers t →
      g * t * g⁻¹ ∉ L ⊔ zpowers t) :
    OuterFusionIn L e t S := by
  intro g hsC hsL
  have : Finite C := Finite.of_equiv L e.toEquiv
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hss : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
  have ht'C := F4Pilot.conj_inv_mem_centralizer_singleton hsC
  have ht't' : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have ht'L := hout g hsC hsL
  obtain ⟨i₁, ψ₁, hψ₁⟩ := exists_mulAut_conj_eq_of_family hset e hcan ht hKt hsC hss hsL
  obtain ⟨i₂, ψ₂, hψ₂⟩ := exists_mulAut_conj_eq_of_family hset e hcan ht hKt ht'C ht't' ht'L
  have hε₁ : ∀ l l' : L, (l' : G) = (g⁻¹ * t * g) * l * (g⁻¹ * t * g)⁻¹ →
      (e.trans ψ₁) l' = η i₁ ((e.trans ψ₁) l) := fun l l' h => hψ₁ l l' h
  have hε₂ : ∀ l l' : L, (l' : G) = (g * t * g⁻¹) * l * (g * t * g⁻¹)⁻¹ →
      (e.trans ψ₂) l' = η i₂ ((e.trans ψ₂) l) := fun l l' h => hψ₂ l l' h
  obtain ⟨β₁₂, hinj₁₂, hβ₁₂⟩ := exists_injective_fixedPoints hset hOut ht htC hsC
    (e.trans ψ₁) (e.trans ψ₂) hε₁ hε₂ (hη i₁).1
  have ht'C' : g⁻¹⁻¹ * t * g⁻¹ ∈ centralizer ({t} : Set G) := by rwa [inv_inv]
  obtain ⟨β₂₁, hinj₂₁, -⟩ := exists_injective_fixedPoints hset hOut ht htC ht'C'
    (e.trans ψ₂) (e.trans ψ₁) (fun l l' h => hε₂ l l' (by rwa [inv_inv] at h))
    (fun l l' h => hε₁ l l' (by rwa [inv_inv] at h)) (hη i₂).1
  have hcard := le_antisymm (Nat.card_le_card_of_injective _ hinj₁₂)
    (Nat.card_le_card_of_injective _ hinj₂₁)
  obtain rfl := hdist i₁ i₂ hcard
  let β : MulAut ((η i₁).toMonoidHom.eqLocus (MonoidHom.id C)) :=
    MulEquiv.ofBijective β₁₂ ⟨hinj₁₂, Finite.injective_iff_surjective.1 hinj₁₂⟩
  obtain ⟨-, m₀, y₀, hy₀1, hmy₀, hβS⟩ := hη i₁
  set ε₁ := e.trans ψ₁ with hε₁def
  set ε₂ := e.trans ψ₂ with hε₂def
  set s := g⁻¹ * t * g with hsdef
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsN : s ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht hsC
  set m : L := ε₁.symm m₀ with hmdef
  set y : L := ε₁.symm y₀ with hydef
  have hmL : s * (m : G) * s⁻¹ ∈ L := (mem_normalizer_iff.1 hsN m).1 m.2
  have hsm : ε₁ ⟨_, hmL⟩ = η i₁ m₀ := by
    rw [hε₁ m ⟨_, hmL⟩ rfl, hmdef, MulEquiv.apply_symm_apply]
  have hyG : (y : G) = s * (m : G)⁻¹ * s⁻¹ * m := by
    have h1 : y = (⟨_, hmL⟩ : L)⁻¹ * m := by
      apply ε₁.injective
      rw [map_mul, map_inv, hsm, hydef, hmdef, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, hmy₀]
    rw [h1, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hkey : (m : G)⁻¹ * s * m = s * y := by
    rw [hyG]
    calc (m : G)⁻¹ * s * m = (m : G)⁻¹ * s⁻¹ * m := by rw [hsinv]
      _ = s * (s * (m : G)⁻¹ * s⁻¹ * m) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hss, one_mul]
  obtain ⟨hzL, hβy⟩ := hβ₁₂ y₀
  refine ⟨g * m * g⁻¹, ⟨_, hzL⟩, ?_, ?_, ?_⟩
  · calc (g * (m : G) * g⁻¹)⁻¹ * t * (g * m * g⁻¹) = g * ((m : G)⁻¹ * s * m) * g⁻¹ := by
          rw [hsdef]; group
      _ = g * (s * y) * g⁻¹ := by rw [hkey]
      _ = t * (g * y * g⁻¹) := by rw [hsdef]; group
  · intro h1
    apply hy₀1
    have h1' : g * (y : G) * g⁻¹ = 1 := congrArg Subtype.val h1
    have hy1 : (y : G) = 1 := by
      calc (y : G) = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h1']; group
    have hy1' : y = 1 := Subtype.ext hy1
    rw [← MulEquiv.apply_symm_apply ε₁ (y₀ : C), ← hydef, hy1', map_one]
  ·
    have h1 : ψ₂ (e ⟨_, hzL⟩) ∈ S := by
      have h2 := hβS β
      have h3 : (β y₀ : C) = ε₂ ⟨_, hzL⟩ := hβy
      rw [h3] at h2
      exact h2
    have h4 := hS ψ₂⁻¹ _ h1
    rwa [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h4

theorem outerFusionIn_of_twistedFusionIn (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hZ : center L = ⊥)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    {C : Type*} [Group C] (e : L ≃* C) {ι : Type*} (η : ι → MulAut C)
    (hcan : ∀ α : MulAut C, α ^ 2 = 1 → α ∉ (MulAut.conj : C →* MulAut C).range →
      ∃ (i : ι) (ψ : MulAut C), ψ * α * ψ⁻¹ = η i)
    (hdist : ∀ i j, Nat.card ((η i).toMonoidHom.eqLocus (MonoidHom.id C)) =
      Nat.card ((η j).toMonoidHom.eqLocus (MonoidHom.id C)) → i = j)
    (S : Set C) (hS : ∀ β : MulAut C, ∀ x ∈ S, β x ∈ S) (hη : ∀ i, TwistedFusionIn (η i) S)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∉ L ⊔ zpowers t →
      ∃ h : G, ∃ z : L, h⁻¹ * t * h = t * z ∧ z ≠ 1 ∧ e z ∈ S :=
  outerFusionIn_of_twistedFusionIn_of_outer hset hOut e η hcan hdist S hS hη ht hKt
    fun _ hsC hsL => F4Pilot.conj_inv_not_mem_sup_zpowers hset hOut hZ hperf ht hKt hsC hsL

omit [Finite G] in
theorem exists_conj_eq_mul_rep_of_outerFusionIn {C : Type*} [Group C] {e : L ≃* C} {t : G}
    {S : Set C} (hC1 : OuterFusionIn L e t S) (htC : t ∈ centralizer (L : Set G)) {κ : Type*}
    (rep : κ → C) (hrep : ∀ x ∈ S, ∃ k : κ, IsConj x (rep k)) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hsL : g⁻¹ * t * g ∉ L ⊔ zpowers t) :
    ∃ (k : κ) (h : G), h⁻¹ * t * h = t * (e.symm (rep k) : G) := by
  obtain ⟨h₀, z, hz, -, hzS⟩ := hC1 g hsC hsL
  obtain ⟨k, hk⟩ := hrep _ hzS
  obtain ⟨c, hc⟩ := isConj_iff.1 hk
  set l : L := e.symm c with hl
  have hlt : (l : G) * t = t * l := mem_centralizer_iff.1 htC l l.2
  have hlz : (l : G) * z * (l : G)⁻¹ = e.symm (rep k) := by
    have h1 : l * z * l⁻¹ = e.symm (rep k) := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, hl, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hc]
    exact congrArg Subtype.val h1
  refine ⟨k, h₀ * (l : G)⁻¹, ?_⟩
  calc (h₀ * (l : G)⁻¹)⁻¹ * t * (h₀ * (l : G)⁻¹) = l * (h₀⁻¹ * t * h₀) * (l : G)⁻¹ := by group
    _ = l * t * z * (l : G)⁻¹ := by rw [hz, mul_assoc (l : G) t z]
    _ = t * ((l : G) * z * (l : G)⁻¹) := by rw [hlt]; group
    _ = t * (e.symm (rep k) : G) := by rw [hlz]

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
