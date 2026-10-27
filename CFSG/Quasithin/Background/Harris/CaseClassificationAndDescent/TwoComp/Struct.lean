module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Defs
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Descent
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpC
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoprimeCentralizer

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank CFSG.SectionRank

section Generic

variable {G : Type*} [Group G]

theorem mathlibSubnormal_of_open_top {H : Subgroup G} (h : CFSG.Open.IsSubnormal H ⊤) :
    H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff.1 h

theorem isComponent_subgroupOf_of_le {X Y M : Subgroup G} (hM : CFSG.Open.IsComponentOf M X)
    (hYX : Y ≤ X) (hMY : M ≤ Y) : CFSG.IsComponent (M.subgroupOf Y) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMY).symm
    (isQuasisimple_of_open hM.2.2), ?_⟩
  have h := Quasithin.A3.subnormal_comap Y.subtype hM.2.1
  rw [show X.comap Y.subtype = ⊤ from (Subgroup.eq_top_iff' _).2 fun y => hYX y.2] at h
  exact mathlibSubnormal_of_open_top h

theorem isComponentOf_map_conj {X M : Subgroup G} (hM : CFSG.Open.IsComponentOf M X) {γ : G}
    (hγ : γ ∈ X) : CFSG.Open.IsComponentOf (M.map (MulAut.conj γ).toMonoidHom) X := by
  have hX : X.map (MulAut.conj γ).toMonoidHom = X := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact X.mul_mem (X.mul_mem hγ hy) (X.inv_mem hγ)
    · intro hx
      exact ⟨γ⁻¹ * x * γ, X.mul_mem (X.mul_mem (X.inv_mem hγ) hx) hγ, by group⟩
  refine ⟨hX ▸ Subgroup.map_mono hM.1, hX ▸ Quasithin.A3.subnormal_map _ hM.2.1, ?_⟩
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective M (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective).symm
    hM.2.2

theorem layer_top_of_sup_eq_top {Q : Type*} [Group Q] {K₁ K₂ : Subgroup Q}
    (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂) (hsup : K₁ ⊔ K₂ = ⊤) :
    CFSG.layer ↥(⊤ : Subgroup Q) = ⊤ := by
  let e : Q ≃* ↥(⊤ : Subgroup Q) := Subgroup.topEquiv.symm
  have c₁ := CFSG.LocalCores.isComponent_map_mulEquiv e h₁
  have c₂ := CFSG.LocalCores.isComponent_map_mulEquiv e h₂
  refine eq_top_iff.2 ?_
  have : K₁.map e.toMonoidHom ⊔ K₂.map e.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← this]
  exact sup_le (CFSG.LocalCores.component_le_layer c₁) (CFSG.LocalCores.component_le_layer c₂)

theorem pCore_two_eq_bot_of_irr {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤) : CFSG.pCore 2 ↥H = ⊥ := by
  have h := CFSG.Quasithin.SzN31.pCoreOf_two_eq_bot_of_isIrr hirr
  have h' : CFSG.Open.pCore 2 ↥H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 h
  exact h'

@[expose] def actOn (N B : Subgroup G) (hB : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N)
    (hsq : ∀ b ∈ B, b * b = 1) : ↥B →* MulAut ↥N where
  toFun b :=
    { toFun := fun n => ⟨(b : G) * n * (b : G)⁻¹, hB b b.2 n n.2⟩
      invFun := fun n => ⟨(b : G) * n * (b : G)⁻¹, hB b b.2 n n.2⟩
      left_inv := fun n => Subtype.ext (by
        have h := hsq b b.2
        have hinv : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right h
        have h1 : ∀ x : G, (b : G) * ((b : G) * x) = x := fun x => by rw [← mul_assoc, h, one_mul]
        show (b : G) * ((b : G) * n * (b : G)⁻¹) * (b : G)⁻¹ = n
        rw [hinv]
        simp only [mul_assoc, h1, h, mul_one])
      right_inv := fun n => Subtype.ext (by
        have h := hsq b b.2
        have hinv : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right h
        have h1 : ∀ x : G, (b : G) * ((b : G) * x) = x := fun x => by rw [← mul_assoc, h, one_mul]
        show (b : G) * ((b : G) * n * (b : G)⁻¹) * (b : G)⁻¹ = n
        rw [hinv]
        simp only [mul_assoc, h1, h, mul_one])
      map_mul' := fun x y => Subtype.ext (by
        show (b : G) * ((x : G) * y) * (b : G)⁻¹ = (b : G) * x * (b : G)⁻¹ * ((b : G) * y * (b : G)⁻¹)
        simp only [mul_assoc, inv_mul_cancel_left]) }
  map_one' := MulEquiv.ext fun n => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun n => Subtype.ext (by
    show ((a * b : ↥B) : G) * (n : G) * ((a * b : ↥B) : G)⁻¹ =
      (a : G) * ((b : G) * n * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc])

theorem commute_of_actOn_eq_one (N B : Subgroup G) (hB : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N)
    (hsq : ∀ b ∈ B, b * b = 1) (b : ↥B) (hb : actOn N B hB hsq b = 1) :
    ∀ n ∈ N, (b : G) * n = n * b := by
  intro n hn
  have h := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : G)) hb
  have h2 : (b : G) * n * (b : G)⁻¹ = n := h
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

theorem card_le_two_pow_of_range {S : Type*} [Group S] {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {B : Type*} [Group B] (hc : ∀ x y : B, x * y = y * x) (hs : ∀ x : B, x * x = 1)
    (ψ : B →* MulAut S) : Nat.card ψ.range ≤ 2 ^ r := by
  apply hr
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, hc]
  · rintro _ ⟨x, rfl⟩
    rw [← map_mul, hs, map_one]

theorem card_le_of_injective_hom {S : Type*} [Group S] {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {B : Type*} [Group B] (hc : ∀ x y : B, x * y = y * x) (hs : ∀ x : B, x * x = 1)
    (ψ : B →* MulAut S) (hinj : Function.Injective ψ) : Nat.card B ≤ 2 ^ r := by
  have : Nat.card B = Nat.card ψ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [this]
  exact card_le_two_pow_of_range hr hc hs ψ

theorem card_le_of_two_homs {S : Type*} [Group S] {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {B : Type*} [Group B] [Finite B] (hc : ∀ x y : B, x * y = y * x) (hs : ∀ x : B, x * x = 1)
    (ψ₁ ψ₂ : B →* MulAut S) (hinj : ∀ b, ψ₁ b = 1 → ψ₂ b = 1 → b = 1) :
    Nat.card B ≤ 2 ^ r * 2 ^ r := by
  have h1 : Nat.card B = Nat.card (B ⧸ ψ₁.ker) * Nat.card ψ₁.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (B ⧸ ψ₁.ker) = Nat.card ψ₁.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ₁).toEquiv
  have : Finite ψ₂.range :=
    Finite.of_surjective (fun b : B => (⟨ψ₂ b, b, rfl⟩ : ψ₂.range))
      (fun ⟨_, b, hb⟩ => ⟨b, Subtype.ext hb⟩)
  have h3 : Nat.card ψ₁.ker ≤ Nat.card ψ₂.range := by
    refine Nat.card_le_card_of_injective (fun k : ψ₁.ker => (⟨ψ₂ k.1, k.1, rfl⟩ : ψ₂.range)) ?_
    intro k k' hkk
    have hψ : ψ₂ k.1 = ψ₂ k'.1 := congrArg Subtype.val hkk
    have hk1 : ψ₁ (k.1 * k'.1⁻¹) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 k.2, MonoidHom.mem_ker.1 k'.2]; simp
    have hk2 : ψ₂ (k.1 * k'.1⁻¹) = 1 := by
      rw [map_mul, map_inv, hψ]; simp
    have := hinj _ hk1 hk2
    exact Subtype.ext (mul_inv_eq_one.1 this)
  calc Nat.card B = Nat.card ψ₁.range * Nat.card ψ₁.ker := by rw [h1, h2]
    _ ≤ 2 ^ r * 2 ^ r :=
      Nat.mul_le_mul (card_le_two_pow_of_range hr hc hs ψ₁)
        (h3.trans (card_le_two_pow_of_range hr hc hs ψ₂))

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Γ A L L₂ : Subgroup (GLV V)} {m : ℕ}

set_option linter.unusedSectionVars false in
theorem Setting.nontrivial_V (h : Setting Γ A L L₂ m) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, -, l, -, hne⟩ := h.hyp.L_comm
  exact hne (LinearEquiv.ext fun v => Subsingleton.elim _ _)

theorem Setting.comm (h : Setting Γ A L L₂ m) : ∀ x ∈ L, ∀ y ∈ L₂, x * y = y * x := by
  have : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite
  have hLH : L ≤ L ⊔ L₂ := le_sup_left
  have hL₂H : L₂ ≤ L ⊔ L₂ := le_sup_right
  have c1 := isComponent_subgroupOf_of_le h.hyp.L_comp h.hyp.H_le hLH
  have c2 := isComponent_subgroupOf_of_le h.comp₂ h.hyp.H_le hL₂H
  rcases CFSG.LocalCores.distinct_components_commute c1 c2 with heq | hbot
  · exfalso
    apply h.ne
    have := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 hLH, inf_eq_left.2 hL₂H] at this
    exact this.symm
  · intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have hx' : (⟨x, hLH hx⟩ : ↥(L ⊔ L₂)) ∈ L.subgroupOf (L ⊔ L₂) := hx
    have := Subgroup.mem_centralizer_iff.1 (hle hx') ⟨y, hL₂H hy⟩ hy
    exact (congrArg Subtype.val this).symm

theorem Setting.centerL_odd (h : Setting Γ A L L₂ m) : Odd (Nat.card (Subgroup.center ↥L)) := by
  have hodd := OrdinaryProofs.centralizer_card_odd h.hyp.H_irr
  have hle : (Subgroup.center ↥L).map L.subtype ≤
      Subgroup.centralizer ((L ⊔ L₂ : Subgroup (GLV V)) : Set (GLV V)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    have h1 : L ≤ Subgroup.centralizer ({(z : GLV V)} : Set (GLV V)) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩).symm
    have h2 : L₂ ≤ Subgroup.centralizer ({(z : GLV V)} : Set (GLV V)) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (h.comm _ z.2 l hl)
    intro g hg
    have := Subgroup.mem_centralizer_iff.1 (sup_le h1 h2 hg) (z : GLV V) rfl
    exact this.symm
  have hdvd : Nat.card ((Subgroup.center ↥L).map L.subtype) ∣
      Nat.card (Subgroup.centralizer ((L ⊔ L₂ : Subgroup (GLV V)) : Set (GLV V))) :=
    Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
  exact hodd.of_dvd_nat hdvd

theorem Setting.sqtkHyp
    (h : Setting Γ A L L₂ m) : CFSG.QuasithinUnique.Vol2Native.SQTKHypCat ↥(L ⊔ L₂) := by
  have : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite
  have hLH : L ≤ L ⊔ L₂ := le_sup_left
  have hL₂H : L₂ ≤ L ⊔ L₂ := le_sup_right
  have c1 := isComponent_subgroupOf_of_le h.hyp.L_comp h.hyp.H_le hLH
  have c2 := isComponent_subgroupOf_of_le h.comp₂ h.hyp.H_le hL₂H
  have hsup : L.subgroupOf (L ⊔ L₂) ⊔ L₂.subgroupOf (L ⊔ L₂) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (L ⊔ L₂))
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hLH, inf_eq_left.2 hL₂H, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h.hyp.quotient.of_le h.hyp.H_le
  have hS : IsSQTKCat S := ⟨G11.isStronglyQuasithin_of_tc hst, hkg⟩
  have hsurj : Function.Surjective (φ.comp (⊤ : Subgroup S).subtype) := by
    intro y
    obtain ⟨s, hs⟩ := hφ y
    exact ⟨⟨s, Subgroup.mem_top s⟩, hs⟩
  have hsq := CFSG.QuasithinUnique.Setup.Layer.sqtk_two_power_index oddKernelCentralization
    catalogStepHyp hS ⊤ (φ.comp (⊤ : Subgroup S).subtype) hsurj ⊤
    (layer_top_of_sup_eq_top c1 c2 hsup)
    (fun g => ⟨0, by
      have : Subsingleton (↥(L ⊔ L₂) ⧸ (⊤ : Subgroup ↥(L ⊔ L₂))) :=
        QuotientGroup.subsingleton_quotient_top
      simp [Subsingleton.elim g 1]⟩)
  exact ⟨inferInstance, hsq.1.1, hsq.1.2, pCore_two_eq_bot_of_irr h.hyp.H_irr⟩

theorem Setting.comp_eq
    (h : Setting Γ A L L₂ m) {M : Subgroup (GLV V)} (hM : IsComponentOf M Γ)
    (hMH : M ≤ L ⊔ L₂) (hiso : Nonempty (↥M ≃* ↥L)) : M = L ∨ M = L₂ := by
  have : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite
  have hLH : L ≤ L ⊔ L₂ := le_sup_left
  have hL₂H : L₂ ≤ L ⊔ L₂ := le_sup_right
  have c1 := isComponent_subgroupOf_of_le h.hyp.L_comp h.hyp.H_le hLH
  have c2 := isComponent_subgroupOf_of_le h.comp₂ h.hyp.H_le hL₂H
  have cM := isComponent_subgroupOf_of_le hM h.hyp.H_le hMH
  have hA := CFSG.QuasithinUnique.Vol2Native.a134SQTKFactCat ↥(L ⊔ L₂) h.sqtkHyp
  obtain ⟨φ, -⟩ := h.qe
  have hne : L.subgroupOf (L ⊔ L₂) ≠ L₂.subgroupOf (L ⊔ L₂) := by
    intro heq
    have := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 hLH, inf_eq_left.2 hL₂H] at this
    exact h.ne this.symm
  have iso12 : Nonempty (↥(L.subgroupOf (L ⊔ L₂)) ≃* ↥(L₂.subgroupOf (L ⊔ L₂))) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hLH).trans (φ.trans (Subgroup.subgroupOfEquivOfLe hL₂H).symm)⟩
  obtain ⟨hcl, -⟩ := hA _ _ c1 c2 hne iso12
  obtain ⟨ψ⟩ := hiso
  rcases hcl _ cM ⟨(Subgroup.subgroupOfEquivOfLe hMH).trans
      (ψ.trans (Subgroup.subgroupOfEquivOfLe hLH).symm)⟩ with h1 | h1
  · left
    have := Subgroup.subgroupOf_inj.1 h1
    rwa [inf_eq_left.2 hMH, inf_eq_left.2 hLH] at this
  · right
    have := Subgroup.subgroupOf_inj.1 h1
    rwa [inf_eq_left.2 hMH, inf_eq_left.2 hL₂H] at this

theorem Setting.perm
    (h : Setting Γ A L L₂ m) :
    ∀ γ ∈ Γ,
      ((∀ l ∈ L, γ * l * γ⁻¹ ∈ L) ∧ (∀ l ∈ L₂, γ * l * γ⁻¹ ∈ L₂)) ∨
      ((∀ l ∈ L, γ * l * γ⁻¹ ∈ L₂) ∧ (∀ l ∈ L₂, γ * l * γ⁻¹ ∈ L)) := by
  intro γ hγ
  obtain ⟨φ, -⟩ := h.qe
  set f : GLV V ≃* GLV V := MulAut.conj γ with hf
  have hfx : ∀ x, f x = γ * x * γ⁻¹ := fun x => rfl
  have hmem : ∀ (M : Subgroup (GLV V)) (x : GLV V), x ∈ M → γ * x * γ⁻¹ ∈ M.map f.toMonoidHom :=
    fun M x hx => ⟨x, hx, rfl⟩
  have hle : ∀ M : Subgroup (GLV V), M ≤ L ⊔ L₂ → M.map f.toMonoidHom ≤ L ⊔ L₂ := by
    rintro M hM _ ⟨x, hx, rfl⟩
    exact h.hyp.H_normal γ hγ x (hM hx)
  have hc1 := isComponentOf_map_conj h.hyp.L_comp hγ
  have hc2 := isComponentOf_map_conj h.comp₂ hγ
  have e1 : Nonempty (↥(L.map f.toMonoidHom) ≃* ↥L) :=
    ⟨(Subgroup.equivMapOfInjective L f.toMonoidHom f.injective).symm⟩
  have e2 : Nonempty (↥(L₂.map f.toMonoidHom) ≃* ↥L) :=
    ⟨(Subgroup.equivMapOfInjective L₂ f.toMonoidHom f.injective).symm.trans φ.symm⟩
  have r1 := h.comp_eq hc1 (hle L le_sup_left) e1
  have r2 := h.comp_eq hc2 (hle L₂ le_sup_right) e2
  have hne : L.map f.toMonoidHom ≠ L₂.map f.toMonoidHom := fun heq =>
    h.ne (Subgroup.map_injective f.injective heq).symm
  rcases r1 with r1 | r1 <;> rcases r2 with r2 | r2
  · exact absurd (r1.trans r2.symm) hne
  · left
    exact ⟨fun l hl => r1 ▸ hmem L l hl, fun l hl => r2 ▸ hmem L₂ l hl⟩
  · right
    exact ⟨fun l hl => r1 ▸ hmem L l hl, fun l hl => r2 ▸ hmem L₂ l hl⟩
  · exact absurd (r1.trans r2.symm) hne

theorem Setting.types
    (h : Setting Γ A L L₂ m) : A134Types (↥L ⧸ Subgroup.center ↥L) := by
  have : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite
  have hLH : L ≤ L ⊔ L₂ := le_sup_left
  have hL₂H : L₂ ≤ L ⊔ L₂ := le_sup_right
  have c1 := isComponent_subgroupOf_of_le h.hyp.L_comp h.hyp.H_le hLH
  have c2 := isComponent_subgroupOf_of_le h.comp₂ h.hyp.H_le hL₂H
  have hH := h.sqtkHyp
  have hA := CFSG.QuasithinUnique.Vol2Native.a134SQTKFactCat ↥(L ⊔ L₂) hH
  obtain ⟨φ, -⟩ := h.qe
  have hne : L.subgroupOf (L ⊔ L₂) ≠ L₂.subgroupOf (L ⊔ L₂) := by
    intro heq
    have := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 hLH, inf_eq_left.2 hL₂H] at this
    exact h.ne this.symm
  have iso12 : Nonempty (↥(L.subgroupOf (L ⊔ L₂)) ≃* ↥(L₂.subgroupOf (L ⊔ L₂))) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hLH).trans (φ.trans (Subgroup.subgroupOfEquivOfLe hL₂H).symm)⟩
  obtain ⟨-, hty⟩ := hA _ _ c1 c2 hne iso12
  rcases hty with h1 | ⟨-, h3⟩
  · let e : ↥L ≃* ↥(L.subgroupOf (L ⊔ L₂)) := (Subgroup.subgroupOfEquivOfLe hLH).symm
    refine CFSG.Quasithin.A38.A134Types.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.subgroupOf (L ⊔ L₂))) e
        (Subgroup.map_center_eq e)) h1
  · exfalso
    have := hH.pRank_le (L.subgroupOf (L ⊔ L₂) ⊔ L₂.subgroupOf (L ⊔ L₂)) Nat.prime_three
      (by norm_num)
    omega

theorem Setting.m_le_two_mul_of_perm (h : Setting Γ A L L₂ m)
    (hperm : ∀ γ ∈ Γ,
      ((∀ l ∈ L, γ * l * γ⁻¹ ∈ L) ∧ (∀ l ∈ L₂, γ * l * γ⁻¹ ∈ L₂)) ∨
      ((∀ l ∈ L, γ * l * γ⁻¹ ∈ L₂) ∧ (∀ l ∈ L₂, γ * l * γ⁻¹ ∈ L)))
    {S : Type} [Group S] (e : ↥L ≃* S) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r) : m ≤ 2 * r := by
  classical
  have : Finite (GLV V) := OrdinaryProofs.finite_GLV_of_finite
  obtain ⟨φ, -⟩ := h.qe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [sq] using h.hyp.A_elem.2 a ha
  have hinv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsq a ha)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.hyp.A_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA2 : IsPGroup 2 ↥A := OrdinaryProofs.isPGroup_two_of_isElemAbelian h.hyp.A_elem
  have hbot := OrdinaryProofs.inf_centralizer_eq_bot_of_two_group h.hyp.H_irr Γ hA2
  have faith : ∀ a ∈ A, (∀ l ∈ L, a * l = l * a) → (∀ l ∈ L₂, a * l = l * a) → a = 1 := by
    intro a ha h1 h2
    have hc : a ∈ A ⊓ (Γ ⊓ Subgroup.centralizer ((L ⊔ L₂ : Subgroup (GLV V)) : Set (GLV V))) := by
      refine ⟨ha, h.hyp.A_le ha, ?_⟩
      have hle : L ⊔ L₂ ≤ Subgroup.centralizer ({a} : Set (GLV V)) := by
        refine sup_le (fun l hl => ?_) (fun l hl => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact h1 l hl
        · rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact h2 l hl
      show a ∈ Subgroup.centralizer ((L ⊔ L₂ : Subgroup (GLV V)) : Set (GLV V))
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.1 (hle hg) a rfl).symm
    rw [hbot, Subgroup.mem_bot] at hc
    exact hc
  let A₀ : Subgroup (GLV V) :=
    A ⊓ Subgroup.normalizer (L : Set (GLV V)) ⊓ Subgroup.normalizer (L₂ : Set (GLV V))
  have conj_back : ∀ a ∈ A, ∀ x : GLV V, a * (a * x * a⁻¹) * a⁻¹ = x := by
    intro a ha x
    have h1 := hsq a ha
    rw [hinv a ha]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by simp only [mul_assoc]
      _ = x := by rw [h1]; simp
  have mem_A₀ : ∀ a ∈ A, (∀ l ∈ L, a * l * a⁻¹ ∈ L) → (∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂) → a ∈ A₀ := by
    intro a ha h1 h2
    refine ⟨⟨ha, Subgroup.mem_normalizer_iff.2 fun x => ⟨h1 x, fun hx => ?_⟩⟩,
      Subgroup.mem_normalizer_iff.2 fun x => ⟨h2 x, fun hx => ?_⟩⟩
    · simpa [conj_back a ha x] using h1 _ hx
    · simpa [conj_back a ha x] using h2 _ hx
  have hB₁ : ∀ b ∈ A₀, ∀ n ∈ L, b * n * b⁻¹ ∈ L := fun b hb n hn =>
    (Subgroup.mem_normalizer_iff.1 hb.1.2 n).1 hn
  have hB₂ : ∀ b ∈ A₀, ∀ n ∈ L₂, b * n * b⁻¹ ∈ L₂ := fun b hb n hn =>
    (Subgroup.mem_normalizer_iff.1 hb.2 n).1 hn
  have hsq₀ : ∀ b ∈ A₀, b * b = 1 := fun b hb => hsq b hb.1.1
  have hc₀ : ∀ x y : ↥A₀, x * y = y * x := fun x y => Subtype.ext (hAc x x.2.1.1 y y.2.1.1)
  have hs₀ : ∀ x : ↥A₀, x * x = 1 := fun x => Subtype.ext (hsq₀ x x.2)
  let e₂ : ↥L₂ ≃* S := φ.symm.trans e
  let ψ₁ : ↥A₀ →* MulAut S := (MulAut.congr e).toMonoidHom.comp (actOn L A₀ hB₁ hsq₀)
  let ψ₂ : ↥A₀ →* MulAut S := (MulAut.congr e₂).toMonoidHom.comp (actOn L₂ A₀ hB₂ hsq₀)
  have cent₁ : ∀ b : ↥A₀, ψ₁ b = 1 → ∀ l ∈ L, (b : GLV V) * l = l * b := by
    intro b hb
    exact commute_of_actOn_eq_one L A₀ hB₁ hsq₀ b ((MulAut.congr e).injective (hb.trans (map_one _).symm))
  have cent₂ : ∀ b : ↥A₀, ψ₂ b = 1 → ∀ l ∈ L₂, (b : GLV V) * l = l * b := by
    intro b hb
    exact commute_of_actOn_eq_one L₂ A₀ hB₂ hsq₀ b ((MulAut.congr e₂).injective (hb.trans (map_one _).symm))
  have key : Nat.card ↥A ≤ 2 ^ r * 2 ^ r := by
    by_cases hall : ∀ a ∈ A, a ∈ A₀
    · have hAeq : A₀ = A := le_antisymm (fun a ha => ha.1.1) hall
      have hinj : ∀ b : ↥A₀, ψ₁ b = 1 → ψ₂ b = 1 → b = 1 := fun b h1 h2 =>
        Subtype.ext (faith b b.2.1.1 (cent₁ b h1) (cent₂ b h2))
      have := card_le_of_two_homs hr hc₀ hs₀ ψ₁ ψ₂ hinj
      rwa [show Nat.card ↥A₀ = Nat.card ↥A by rw [hAeq]] at this
    · push Not at hall
      obtain ⟨t, htA, htn⟩ := hall
      have swap : ∀ a ∈ A, a ∉ A₀ →
          (∀ l ∈ L, a * l * a⁻¹ ∈ L₂) ∧ (∀ l ∈ L₂, a * l * a⁻¹ ∈ L) := by
        intro a ha han
        rcases hperm a (h.hyp.A_le ha) with ⟨h1, h2⟩ | h1
        · exact absurd (mem_A₀ a ha h1 h2) han
        · exact h1
      have hsw : ∀ a ∈ A, a ∉ A₀ → ∀ b ∈ A, b ∉ A₀ → a * b ∈ A₀ := by
        intro a ha han b hb hbn
        refine mem_A₀ _ (A.mul_mem ha hb) (fun l hl => ?_) (fun l hl => ?_)
        · have := (swap a ha han).2 _ ((swap b hb hbn).1 l hl)
          rwa [show a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ by group]
        · have := (swap a ha han).1 _ ((swap b hb hbn).2 l hl)
          rwa [show a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ by group]
      have hidx : (A₀.subgroupOf A).index = 2 := by
        rw [Subgroup.index_eq_two_iff]
        refine ⟨⟨t, htA⟩, fun b => ?_⟩
        by_cases hb : (b : GLV V) ∈ A₀
        · right
          refine ⟨hb, fun hbt => ?_⟩
          have hbt' : (b : GLV V) * t ∈ A₀ := hbt
          apply htn
          have := A₀.mul_mem (A₀.inv_mem hb) hbt'
          simpa using this
        · left
          exact ⟨hsw b b.2 hb t htA htn, hb⟩
      have hAle : A₀ ≤ A := fun a ha => ha.1.1
      have h1 : Nat.card ↥(A₀.subgroupOf A) * 2 = Nat.card ↥A := by
        have := Subgroup.card_mul_index (A₀.subgroupOf A)
        rwa [hidx] at this
      have h2 : Nat.card ↥(A₀.subgroupOf A) = Nat.card ↥A₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv
      have hinj : Function.Injective ψ₁ := by
        rw [injective_iff_map_eq_one]
        intro b hb
        refine Subtype.ext (faith b b.2.1.1 (cent₁ b hb) (fun y hy => ?_))
        have hl := (swap t htA htn).2 y hy
        have hbl := cent₁ b hb _ hl
        have ht1 := hsq t htA
        have hbt := hAc _ b.2.1.1 t htA
        have hy' : y = t * (t * y * t⁻¹) * t := by
          rw [hinv t htA]
          calc y = (t * t) * y * (t * t) := by rw [ht1]; simp
            _ = t * (t * y * t) * t := by simp only [mul_assoc]
        have key : ∀ l : GLV V, (b : GLV V) * l = l * b → (b : GLV V) * (t * l * t) = (t * l * t) * b := by
          intro l hl
          calc (b : GLV V) * (t * l * t) = ((b : GLV V) * t) * l * t := by simp only [mul_assoc]
            _ = (t * (b : GLV V)) * l * t := by rw [hbt]
            _ = t * ((b : GLV V) * l) * t := by simp only [mul_assoc]
            _ = t * (l * (b : GLV V)) * t := by rw [hl]
            _ = t * l * ((b : GLV V) * t) := by simp only [mul_assoc]
            _ = t * l * (t * (b : GLV V)) := by rw [hbt]
            _ = (t * l * t) * b := by simp only [mul_assoc]
        have := key _ hbl
        rwa [← hy'] at this
      have h3 := card_le_of_injective_hom hr hc₀ hs₀ ψ₁ hinj
      have h4 : 2 ≤ 2 ^ r := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
      calc Nat.card ↥A = Nat.card ↥(A₀.subgroupOf A) * 2 := h1.symm
        _ = Nat.card ↥A₀ * 2 := by rw [h2]
        _ ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul h3 h4
  rw [h.hyp.A_card, ← pow_add] at key
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 key
  omega

theorem Setting.m_le_two_mul
    (h : Setting Γ A L L₂ m) {S : Type} [Group S] (e : ↥L ≃* S) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r) : m ≤ 2 * r :=
  h.m_le_two_mul_of_perm h.perm e hr1 hr

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
