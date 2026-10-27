module

public import CFSG.Quasithin.Background.SzG11TwoCommon
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin CFSG.Quasithin.SzG11NC CFSG.QuasithinUnique

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ L : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V}

theorem exists_sylow_package_of_normal [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀)
    {H : Subgroup (GLV V)} (hHΓ : H ≤ Γ) (hnormH : ∀ γ ∈ Γ, ∀ k ∈ H, γ * k * γ⁻¹ ∈ H) :
    ∃ P : Subgroup (GLV V),
      IsSylowTwoOf P (H ⊓ MulAction.stabilizer (GLV V) v₁) ∧
      ∀ x ∈ X, ∀ t ∈ P, x * t * x⁻¹ * t⁻¹ ∈ X ⊓ H := by
  obtain ⟨S, hS, hXS, hSn⟩ := hyp.four
  obtain ⟨hSΓ, hcomm⟩ := hyp.toG101Hyp.g10_9 hS ⟨hXS, hSn⟩ hnormH
  have hΓn : Γ ≤ Subgroup.normalizer (H : Set (GLV V)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hnormH γ hγ k hk, fun hk => ?_⟩
    have := hnormH γ⁻¹ (Γ.inv_mem hγ) _ hk
    simpa [mul_assoc] using this
  have hP : IsSylowTwoOf (S ⊓ H) H := A4.isSylowTwoOf_inf_normal hSΓ hHΓ hΓn
  refine ⟨S ⊓ H, ?_, hcomm⟩
  have hSstab : S ≤ MulAction.stabilizer (GLV V) v₁ := hS.1.trans inf_le_right
  have hle : S ⊓ H ≤ H ⊓ MulAction.stabilizer (GLV V) v₁ :=
    le_inf inf_le_right (inf_le_left.trans hSstab)
  exact A4.isSylowTwoOf_mono hP hle inf_le_left

theorem no_E_line_in_W [Finite V] {E : Type} [Field E] [Module E V]
    (hyp : G101Hyp B Γ v₁ W X X₀)
    (hdich : ∀ x ∈ X, (∀ (e : E) (v : V), x (e • v) = e • x v) ∨
      (∀ (e : E) (v : V), x (e • v) = e ^ 2 • x v))
    {u : V} (hu : u ∈ W) (hnot : ∀ c : E, u ≠ c • v₁) {κ : E} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1) :
    κ • u ∉ W := by
  classical
  intro hκu
  have : Nontrivial V := ⟨⟨v₁, 0, hyp.point⟩⟩
  have hnot' : (⟨u, hu⟩ : W) ∉ Submodule.span (ZMod 2) {(⟨v₁, hyp.mem_W⟩ : W)} := by
    intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have hc' := congrArg Subtype.val hc
    rcases zmod_two_cases c with rfl | rfl
    · apply hnot 0
      simpa using hc'.symm
    · apply hnot 1
      simpa using hc'.symm
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot' inferInstance
  have hf0 : f ⟨v₁, hyp.mem_W⟩ = 0 := by
    have : f ⟨v₁, hyp.mem_W⟩ ∈ (Submodule.span (ZMod 2) {(⟨v₁, hyp.mem_W⟩ : W)}).map f :=
      ⟨_, Submodule.subset_span rfl, rfl⟩
    rw [hf2, Submodule.mem_bot] at this
    exact this
  have hfu : f ⟨u, hu⟩ = 1 := by
    rcases zmod_two_cases (f ⟨u, hu⟩) with h | h
    · exact absurd h hf1
    · exact h
  obtain ⟨x, hxX, hx⟩ := hyp.transvection_full f hf0
  have e1 := hx ⟨u, hu⟩
  have e2 := hx ⟨κ • u, hκu⟩
  simp only at e1 e2
  rw [hfu, one_smul] at e1
  rcases hdich x hxX with hlin | hfrob
  · have e3 : x (κ • u) = κ • x u := hlin κ u
    rw [e2, e1, smul_add] at e3
    have e4 : (f ⟨κ • u, hκu⟩) • v₁ = κ • v₁ := add_left_cancel e3
    have e5 : κ • v₁ = 0 ∨ κ • v₁ = v₁ := by
      rcases zmod_two_cases (f ⟨κ • u, hκu⟩) with h | h
      · left; rw [← e4, h, zero_smul]
      · right; rw [← e4, h, one_smul]
    rcases eq_zero_or_one_of_smul_eq hyp.point e5 with h | h
    · exact hκ0 h
    · exact hκ1 h
  · have e3 : x (κ • u) = κ ^ 2 • x u := hfrob κ u
    rw [e2, e1, smul_add] at e3
    have hκ2 : κ ^ 2 - κ ≠ 0 := by
      intro h
      have : κ * (κ - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact hκ0 h'
      · exact hκ1 (sub_eq_zero.1 h')
    have hu' : ∃ a : E, (κ ^ 2 - κ) • u = a • v₁ := by
      rcases zmod_two_cases (f ⟨κ • u, hκu⟩) with h | h
      · rw [h, zero_smul, add_zero] at e3
        refine ⟨-κ ^ 2, ?_⟩
        rw [sub_smul, e3, neg_smul]
        abel
      · rw [h, one_smul] at e3
        refine ⟨1 - κ ^ 2, ?_⟩
        rw [sub_smul, sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm v₁ (κ • u)]
        exact e3.symm
    obtain ⟨a, ha⟩ := hu'
    apply hnot ((κ ^ 2 - κ)⁻¹ * a)
    rw [mul_smul, ← ha, smul_smul, inv_mul_cancel₀ hκ2, one_smul]

@[expose] def Ysp (E : Type) [Field E] [Module E V] (B : LinearMap.BilinForm (ZMod 2) V)
    (v₁ : V) : Submodule E V where
  carrier := {v | ∀ κ : E, B v₁ (κ • v) = 0}
  add_mem' := fun {a b} ha hb κ => by rw [smul_add, map_add, ha κ, hb κ, add_zero]
  zero_mem' := fun κ => by rw [smul_zero, map_zero]
  smul_mem' := fun c v hv κ => by rw [smul_smul]; exact hv (κ * c)

theorem mem_Ysp {E : Type} [Field E] [Module E V] {v : V} :
    v ∈ Ysp E B v₁ ↔ ∀ κ : E, B v₁ (κ • v) = 0 := Iff.rfl

theorem Ysp_le_perp {E : Type} [Field E] [Module E V] {v : V} (hv : v ∈ Ysp E B v₁) :
    B v₁ v = 0 := by
  simpa using hv 1

theorem pow_four_eq {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) (κ : E) :
    κ ^ 4 = κ := by
  have : Fintype E := Fintype.ofFinite E
  have h := FiniteField.pow_card κ
  rwa [← Nat.card_eq_fintype_card, hE] at h

theorem card_eq_four_mul_Ysp [Finite V] {E : Type} [Field E] [Finite E] [Module E V]
    (hE : Nat.card E = 4) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) (hv₁ : v₁ ≠ 0) :
    Nat.card V = 4 * Nat.card (Ysp E B v₁) := by
  classical
  have h2 : (2 : E) = 0 := two_eq_zero_of_card_four hE
  obtain ⟨ω, hω0, hω1, hωsq, hall⟩ := E4_cases hE h2
  let ωLin : V →ₗ[ZMod 2] V :=
    (AddMonoidHom.mk' (fun v : V => ω • v) (fun a b => smul_add ω a b)).toZModLinearMap 2
  have ωLin_apply : ∀ v, ωLin v = ω • v := fun v => rfl
  let Φ' : V →+ ZMod 2 × ZMod 2 :=
    AddMonoidHom.prod ((B v₁).toAddMonoidHom) (((B v₁).comp ωLin).toAddMonoidHom)
  have hker : ∀ v, v ∈ Φ'.ker ↔ v ∈ Ysp E B v₁ := by
    intro v
    rw [AddMonoidHom.mem_ker, mem_Ysp]
    constructor
    · intro h κ
      have h1 : B v₁ v = 0 := congrArg Prod.fst h
      have h2' : B v₁ (ω • v) = 0 := congrArg Prod.snd h
      rcases hall κ with rfl | rfl | rfl | rfl
      · simp
      · simpa using h1
      · exact h2'
      · rw [add_smul, one_smul, map_add, h2', h1, add_zero]
    · intro h
      exact Prod.ext (show B v₁ v = 0 from by simpa using h 1) (show B v₁ (ω • v) = 0 from h ω)
  have hc1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ'.ker
  have hc2 : Nat.card Φ'.ker = Nat.card (Ysp E B v₁) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => hker v))
  have hc3 : Nat.card (V ⧸ Φ'.ker) ≤ 4 := by
    have := Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective Φ')
    rwa [Nat.card_prod, Nat.card_zmod] at this
  have hVY : Nat.card V ≤ 4 * Nat.card (Ysp E B v₁) := by
    rw [hc1, hc2]
    exact Nat.mul_le_mul_right _ hc3
  have hcard := Submodule.card_eq_card_quotient_mul_card (Ysp E B v₁)
  have : Finite (V ⧸ Ysp E B v₁) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  obtain ⟨w, hw⟩ : ∃ w, B v₁ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv₁ (hnd v₁ hcon)
  have hwY : w ∉ Ysp E B v₁ := fun h => hw (Ysp_le_perp h)
  have hnt : Nontrivial (V ⧸ Ysp E B v₁) :=
    ⟨⟨Submodule.Quotient.mk w, 0, fun h => hwY (Submodule.Quotient.mk_eq_zero _ |>.1 h)⟩⟩
  have hq1 : 1 < Nat.card (V ⧸ Ysp E B v₁) := Finite.one_lt_card
  have hq := Module.natCard_eq_pow_finrank (K := E) (V := V ⧸ Ysp E B v₁)
  rw [hE] at hq
  have hYpos : 0 < Nat.card (Ysp E B v₁) := Nat.card_pos
  have hq4 : Nat.card (V ⧸ Ysp E B v₁) ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card V > 4 * Nat.card (Ysp E B v₁) := by
      rw [hcard]
      nlinarith
    omega
  rcases hk : Module.finrank E (V ⧸ Ysp E B v₁) with _ | _ | k
  · rw [hk] at hq
    simp at hq
    omega
  · rw [hk] at hq
    simp at hq
    rw [hcard, hq, mul_comm]
  · rw [hk] at hq
    have : 4 ^ (k + 2) ≥ 16 := by
      calc 4 ^ (k + 2) ≥ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16 := by norm_num
    omega

@[expose] def Nsp (E : Type) [Field E] [Module E V] (B : LinearMap.BilinForm (ZMod 2) V)
    (v₁ : V) : Submodule E (Ysp E B v₁) :=
  (Submodule.span E {v₁}).submoduleOf (Ysp E B v₁)

theorem mem_Nsp {E : Type} [Field E] [Module E V] {y : Ysp E B v₁} :
    y ∈ Nsp E B v₁ ↔ ∃ c : E, c • v₁ = (y : V) := by
  rw [Nsp]
  show (y : V) ∈ Submodule.span E {v₁} ↔ _
  rw [Submodule.mem_span_singleton]

abbrev Mq (E : Type) [Field E] [Module E V] (B : LinearMap.BilinForm (ZMod 2) V) (v₁ : V) :
    Type :=
  ↥(Ysp E B v₁) ⧸ Nsp E B v₁

theorem card_Mq [Finite V] {E : Type} [Field E] [Finite E] [Module E V] (hE : Nat.card E = 4)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) (hv₁ : v₁ ≠ 0) (hiso : ∀ κ : E, B v₁ (κ • v₁) = 0) :
    Nat.card V = 16 * Nat.card (Mq E B v₁) := by
  have h4 := card_eq_four_mul_Ysp (B := B) (v₁ := v₁) hE hnd hv₁
  have hN : Nat.card (Nsp E B v₁) = 4 := by
    have hle : Submodule.span E {v₁} ≤ Ysp E B v₁ := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hiso
    have e1 := (Submodule.submoduleOfEquivOfLe hle).toEquiv
    have e2 := (LinearEquiv.toSpanNonzeroSingleton E V v₁ hv₁).toEquiv
    rw [Nsp, Nat.card_congr e1, ← Nat.card_congr e2, hE]
  have h5 : Nat.card (Ysp E B v₁) = 4 * Nat.card (Mq E B v₁) := by
    have := Submodule.card_eq_card_quotient_mul_card (Nsp E B v₁)
    rw [hN] at this
    exact this
  omega

theorem lin_trivial_on_Y [Finite V] {E : Type} [Field E] [Finite E] [Module E V]
    (hE : Nat.card E = 4) (hyp : G101Hyp B Γ v₁ W X X₀)
    (hdich : ∀ x ∈ X, (∀ (e : E) (v : V), x (e • v) = e • x v) ∨
      (∀ (e : E) (v : V), x (e • v) = e ^ 2 • x v))
    {z : GLV V} (hz : z ∈ X) (hzlin : ∀ (e : E) (v : V), z (e • v) = e • z v) {y : V}
    (hy : y ∈ Ysp E B v₁) : ∃ c : E, z y - y = c • v₁ := by
  by_contra hcon
  push Not at hcon
  have hs : z y - y ∈ W := hyp.commutator_le z hz y (Ysp_le_perp hy)
  have hsκ : ∀ κ : E, κ • (z y - y) ∈ W := by
    intro κ
    have : κ • (z y - y) = z (κ • y) - κ • y := by rw [smul_sub, hzlin κ y]
    rw [this]
    exact hyp.commutator_le z hz _ (Ysp_le_perp ((Ysp E B v₁).smul_mem κ hy))
  have hcard : 2 < Nat.card E := by omega
  obtain ⟨κ, hκ0, hκ1⟩ := exists_ne_zero_one hcard
  exact no_E_line_in_W hyp hdich hs (fun c => hcon c) hκ0 hκ1 (hsκ κ)

abbrev linOf {E : Type} [Field E] [Module E V] (c : GLV V)
    (hc : ∀ (e : E) (v : V), c (e • v) = e • c v) : V →ₗ[E] V where
  toFun := c
  map_add' := map_add c
  map_smul' := hc

@[expose] noncomputable def indEnd {E : Type} [Field E] [Module E V] (g : V →ₗ[E] V)
    (hY : ∀ y ∈ Ysp E B v₁, g y ∈ Ysp E B v₁) (hv : g v₁ = v₁) : Module.End E (Mq E B v₁) :=
  Submodule.mapQ (Nsp E B v₁) (Nsp E B v₁) (g.restrict hY) (by
    intro y hy
    rw [Submodule.mem_comap]
    obtain ⟨c, hc⟩ := mem_Nsp.1 hy
    refine mem_Nsp.2 ⟨c, ?_⟩
    rw [LinearMap.coe_restrict_apply, ← hc, map_smul, hv])

theorem indEnd_mk {E : Type} [Field E] [Module E V] (g : V →ₗ[E] V)
    (hY : ∀ y ∈ Ysp E B v₁, g y ∈ Ysp E B v₁) (hv : g v₁ = v₁) (y : Ysp E B v₁) :
    indEnd g hY hv (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨g y, hY y y.2⟩ := by
  unfold indEnd
  rw [Submodule.mapQ_apply]
  rfl

noncomputable def rhoOf {E : Type} [Field E] [Module E V] (C : Subgroup (GLV V))
    (hC : ∀ c ∈ C, (∀ (e : E) (v : V), c (e • v) = e • c v) ∧ c v₁ = v₁ ∧
      ∀ y ∈ Ysp E B v₁, c y ∈ Ysp E B v₁) :
    ↥C →* (Mq E B v₁ ≃ₗ[E] Mq E B v₁) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Mq E B v₁)).toMonoidHom.comp
    (MonoidHom.toHomUnits
      ({ toFun := fun c => indEnd (linOf c.1 (hC c.1 c.2).1) (hC c.1 c.2).2.2 (hC c.1 c.2).2.1
         map_one' := by
           apply Submodule.linearMap_qext
           apply LinearMap.ext
           intro y
           simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.one_apply]
           rw [indEnd_mk]
           rfl
         map_mul' := fun c c' => by
           apply Submodule.linearMap_qext
           apply LinearMap.ext
           intro y
           simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply]
           rw [indEnd_mk, indEnd_mk, indEnd_mk]
           rfl } : ↥C →* Module.End E (Mq E B v₁)))

theorem rhoOf_mk {E : Type} [Field E] [Module E V] (C : Subgroup (GLV V))
    (hC : ∀ c ∈ C, (∀ (e : E) (v : V), c (e • v) = e • c v) ∧ c v₁ = v₁ ∧
      ∀ y ∈ Ysp E B v₁, c y ∈ Ysp E B v₁) (c : ↥C) (y : Ysp E B v₁) :
    rhoOf C hC c (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨(c : GLV V) y, (hC c.1 c.2).2.2 y y.2⟩ := by
  show (indEnd (linOf c.1 (hC c.1 c.2).1) (hC c.1 c.2).2.2 (hC c.1 c.2).2.1)
    (Submodule.Quotient.mk y) = _
  rw [indEnd_mk]
  rfl

@[expose] def frobHom (E : Type) [Field E] (h2 : (2 : E) = 0) : E →+* E where
  toFun e := e ^ 2
  map_one' := one_pow 2
  map_mul' := fun a b => mul_pow a b 2
  map_zero' := by simp
  map_add' := fun a b => by linear_combination (a * b) * h2

instance ringHomSurjective_of_finite {E : Type} [Field E] [Finite E] (σ : E →+* E) :
    RingHomSurjective σ :=
  ⟨Finite.surjective_of_injective σ.injective⟩

@[expose] noncomputable def indSemi {E : Type} [Field E] [Finite E] [Module E V]
    (h2 : (2 : E) = 0) (x₀ : V →+ V) (hx : ∀ (e : E) (v : V), x₀ (e • v) = e ^ 2 • x₀ v)
    (hY : ∀ y ∈ Ysp E B v₁, x₀ y ∈ Ysp E B v₁) (hv : x₀ v₁ = v₁) :
    Mq E B v₁ →ₛₗ[frobHom E h2] Mq E B v₁ :=
  Submodule.mapQ (Nsp E B v₁) (Nsp E B v₁)
    ({ toFun := fun y => ⟨x₀ y, hY y y.2⟩
       map_add' := fun a b => Subtype.ext (map_add x₀ (a : V) (b : V))
       map_smul' := fun e y => Subtype.ext (hx e (y : V)) } :
      Ysp E B v₁ →ₛₗ[frobHom E h2] Ysp E B v₁) (by
    intro y hy
    rw [Submodule.mem_comap]
    obtain ⟨c, hc⟩ := mem_Nsp.1 hy
    refine mem_Nsp.2 ⟨c ^ 2, ?_⟩
    show c ^ 2 • v₁ = x₀ y
    rw [← hc, hx, hv])

theorem indSemi_mk {E : Type} [Field E] [Finite E] [Module E V] (h2 : (2 : E) = 0)
    (x₀ : V →+ V) (hx : ∀ (e : E) (v : V), x₀ (e • v) = e ^ 2 • x₀ v)
    (hY : ∀ y ∈ Ysp E B v₁, x₀ y ∈ Ysp E B v₁) (hv : x₀ v₁ = v₁) (y : Ysp E B v₁) :
    indSemi h2 x₀ hx hY hv (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨x₀ y, hY y y.2⟩ := by
  unfold indSemi
  rw [Submodule.mapQ_apply]
  rfl

theorem stab_prop [Finite V] (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) :
    ∀ c ∈ H ⊓ MulAction.stabilizer (GLV V) v₁,
      (∀ (e : CommF H hirr) (v : V), c (e • v) = e • c v) ∧ c v₁ = v₁ ∧
      ∀ y ∈ Ysp (CommF H hirr) B v₁, c y ∈ Ysp (CommF H hirr) B v₁ := by
  intro c hc
  obtain ⟨hcH, hcstab⟩ := hc
  have hv : c v₁ = v₁ := hcstab
  refine ⟨fun e v => smul_comm_of_mem hcH e v, hv, fun y hy κ => ?_⟩
  have hiso := hyp.isometry c (hHΓ hcH) v₁ (κ • y)
  rw [hv] at hiso
  rw [← smul_comm_of_mem hcH κ y, hiso]
  exact hy κ

noncomputable def rhoStab [Finite V] (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) :
    ↥(H ⊓ MulAction.stabilizer (GLV V) v₁) →*
      (Mq (CommF H hirr) B v₁ ≃ₗ[CommF H hirr] Mq (CommF H hirr) B v₁) :=
  rhoOf _ (stab_prop hyp hirr hHΓ)

theorem rhoStab_mk [Finite V] (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (c : ↥(H ⊓ MulAction.stabilizer (GLV V) v₁))
    (y : Ysp (CommF H hirr) B v₁) :
    rhoStab hyp hirr hHΓ c (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨(c : GLV V) y, (stab_prop hyp hirr hHΓ c c.2).2.2 y y.2⟩ :=
  rhoOf_mk _ _ c y

theorem glv_inv_mul_apply (g : GLV V) (v : V) : (g⁻¹ * g) v = v := by
  rw [inv_mul_cancel]
  rfl

theorem exists_xbar_commuting [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hE : Nat.card (CommF H hirr) = 4)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant H, ∃ v, x (f v) ≠ f (x v)) :
    ∃ P : Subgroup (GLV V), IsSylowTwoOf P (H ⊓ MulAction.stabilizer (GLV V) v₁) ∧
      ∃ x : Mq (CommF H hirr) B v₁ →+ Mq (CommF H hirr) B v₁,
        (∀ (e : CommF H hirr) (m : Mq (CommF H hirr) B v₁), x (e • m) = e ^ 2 • x m) ∧
        (∀ m, x (x m) = m) ∧
        ∀ p : ↥(H ⊓ MulAction.stabilizer (GLV V) v₁), (p : GLV V) ∈ P →
          ∀ m, rhoStab hyp.toG101Hyp hirr hHΓ p (x m) =
            x (rhoStab hyp.toG101Hyp hirr hHΓ p m) := by
  classical
  have h2 : (2 : CommF H hirr) = 0 := two_eq_zero_of_card_four hE
  obtain ⟨x₀, hx₀X, hx₀sq, hx₀fr⟩ := exists_frobenius_involution hyp hirr hnorm hE hex
  obtain ⟨P, hP, hcomm⟩ := exists_sylow_package_of_normal hyp hHΓ hnorm
  have hdich : ∀ x ∈ X, (∀ (e : CommF H hirr) (v : V), x (e • v) = e • x v) ∨
      (∀ (e : CommF H hirr) (v : V), x (e • v) = e ^ 2 • x v) :=
    fun x hx => commF_dichotomy hirr hnorm hE (hyp.X_le hx)
  have hx₀v : x₀ v₁ = v₁ := hyp.X_fixes x₀ hx₀X
  have hx₀inv : ∀ v, x₀ (x₀ v) = v := fun v => by
    simpa using congrArg (fun g : GLV V => g v) hx₀sq
  have hY₀ : ∀ y ∈ Ysp (CommF H hirr) B v₁, x₀ y ∈ Ysp (CommF H hirr) B v₁ := by
    intro y hy κ
    have h1 : κ • x₀ y = x₀ ((κ ^ 2) • y) := by
      rw [hx₀fr (κ ^ 2) y, ← pow_mul]
      have : κ ^ (2 * 2) = κ := pow_four_eq hE κ
      rw [this]
    rw [h1]
    have := hyp.isometry x₀ (hyp.X_le hx₀X) v₁ ((κ ^ 2) • y)
    rw [hx₀v] at this
    rw [this]
    exact hy (κ ^ 2)
  let x₀add : V →+ V := (x₀ : V →ₗ[ZMod 2] V).toAddMonoidHom
  have hx₀add : ∀ (e : CommF H hirr) (v : V), x₀add (e • v) = e ^ 2 • x₀add v := hx₀fr
  have hx₀v' : x₀add v₁ = v₁ := hx₀v
  obtain ⟨xs, hxs⟩ : ∃ xs : Mq (CommF H hirr) B v₁ →ₛₗ[frobHom (CommF H hirr) h2]
      Mq (CommF H hirr) B v₁, ∀ y : Ysp (CommF H hirr) B v₁,
      xs (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨x₀ y, hY₀ y y.2⟩ :=
    ⟨indSemi h2 x₀add hx₀add hY₀ hx₀v', indSemi_mk h2 x₀add hx₀add hY₀ hx₀v'⟩
  refine ⟨P, hP, xs.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro e m
    exact map_smulₛₗ xs e m
  · intro m
    refine Submodule.Quotient.induction_on _ m ?_
    intro y
    show xs (xs (Submodule.Quotient.mk y)) = Submodule.Quotient.mk y
    rw [hxs, hxs]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (hx₀inv y))
  · intro p hpP m
    refine Submodule.Quotient.induction_on _ m ?_
    intro y
    show rhoStab hyp.toG101Hyp hirr hHΓ p (xs (Submodule.Quotient.mk y)) =
      xs (rhoStab hyp.toG101Hyp hirr hHΓ p (Submodule.Quotient.mk y))
    rw [hxs, rhoStab, rhoOf_mk, rhoOf_mk, hxs, Submodule.Quotient.eq]
    have hz := hcomm x₀ hx₀X (p : GLV V) hpP
    have hzlin : ∀ (e : CommF H hirr) (v : V), (x₀ * (p : GLV V) * x₀⁻¹ * (p : GLV V)⁻¹) (e • v) =
        e • (x₀ * (p : GLV V) * x₀⁻¹ * (p : GLV V)⁻¹) v :=
      fun e v => smul_comm_of_mem hz.2 e v
    have hpY := stab_prop hyp.toG101Hyp hirr hHΓ (p : GLV V) p.2
    have hy' : (p : GLV V) (x₀ (y : V)) ∈ Ysp (CommF H hirr) B v₁ := hpY.2.2 _ (hY₀ _ y.2)
    obtain ⟨c, hc⟩ := lin_trivial_on_Y hE hyp.toG101Hyp hdich hz.1 hzlin hy'
    have hinv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hx₀sq
    have hzy : (x₀ * (p : GLV V) * x₀⁻¹ * (p : GLV V)⁻¹) ((p : GLV V) (x₀ (y : V))) =
        x₀ ((p : GLV V) y) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have h3 : (p : GLV V)⁻¹ ((p : GLV V) (x₀ (y : V))) = x₀ y := by
        have := glv_inv_mul_apply (p : GLV V) (x₀ (y : V))
        rwa [LinearEquiv.mul_apply] at this
      rw [h3, hinv, hx₀inv]
    rw [hzy] at hc
    refine mem_Nsp.2 ⟨-c, ?_⟩
    rw [neg_smul, ← hc]
    simp [neg_sub]

theorem rho_card_dvd [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hE : Nat.card (CommF H hirr) = 4)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant H, ∃ v, x (f v) ≠ f (x v)) :
    ∃ P : Subgroup (GLV V), IsSylowTwoOf P (H ⊓ MulAction.stabilizer (GLV V) v₁) ∧
      ∃ n : ℕ, Nat.card (Mq (CommF H hirr) B v₁) = n ^ 2 ∧
        Nat.card (Subgroup.map (rhoStab hyp.toG101Hyp hirr hHΓ)
          (P.subgroupOf (H ⊓ MulAction.stabilizer (GLV V) v₁))) ∣ (n - 1).factorial := by
  obtain ⟨P, hP, x, hx, hxx, hcomm⟩ := exists_xbar_commuting hyp hirr hHΓ hnorm hE hex
  have : Finite (Mq (CommF H hirr) B v₁) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨P, hP, Nat.card (fixAdd x), card_eq_sq hE x hx hxx, ?_⟩
  refine card_centralizer_dvd hE x hx hxx _ ?_
  rintro a ⟨p, hp, rfl⟩ m
  exact hcomm p (Subgroup.mem_subgroupOf.1 hp) m

theorem pow_le_card_map_sylow {G A : Type*} [Group G] [Group A] [Finite G] (ρ : G →* A)
    (Q : Sylow 2 G) {k : ℕ} (hk : 2 ^ k ∣ Nat.card ρ.range) :
    2 ^ k ≤ Nat.card (Subgroup.map ρ Q) := by
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 ρ.range,
      (T : Subgroup ρ.range) = Subgroup.map ρ.rangeRestrict Q :=
    ⟨Q.mapSurjective ρ.rangeRestrict_surjective,
      Sylow.coe_mapSurjective ρ.rangeRestrict_surjective Q⟩
  have hcard := T.card_eq_multiplicity
  have hle : k ≤ (Nat.card ρ.range).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hk
  have hQ : Nat.card (T : Subgroup ρ.range) = Nat.card (Subgroup.map ρ Q) := by
    have h1 : Subgroup.map ρ Q =
        Subgroup.map ρ.range.subtype (Subgroup.map ρ.rangeRestrict Q) := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, Subgroup.card_map_of_injective Subtype.val_injective, hT]
  rw [← hQ, hcard]
  exact Nat.pow_le_pow_right (by norm_num) hle

end CFSG.Quasithin.G11.SzG11S.Two
