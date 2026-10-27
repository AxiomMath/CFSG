module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ASetSummands
import CFSG.Quasithin.Background.StabSubBasics
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem le_stabSub_of_stableUnder {H : Subgroup (MulAut W)} {I : Subgroup W}
    (h : StableUnder H I) : H ≤ stabSub I := by
  intro g hg u
  refine ⟨fun hu => ?_, h g hg u⟩
  have := h g⁻¹ (H.inv_mem hg) _ hu
  rwa [MulAut.inv_apply, MulEquiv.symm_apply_apply] at this

theorem stableUnder_sup {H : Subgroup (MulAut W)} {A B : Subgroup W} (hA : StableUnder H A)
    (hB : StableUnder H B) : StableUnder H (A ⊔ B) := by
  intro x hx w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x hx y hy) (hB x hx z hz)

theorem eq_or_eq_top_of_le {H : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W} (htop : I₁ ⊔ I₂ = ⊤)
    (h₂inv : StableUnder H I₂) (h₂ : ∀ J, StableUnder H J → J ≤ I₂ → J = ⊥ ∨ J = I₂)
    {J : Subgroup W} (hJ : StableUnder H J) (hJ₁ : I₁ ≤ J) : J = I₁ ∨ J = ⊤ := by
  have hJ₂ : StableUnder H (J ⊓ I₂) := fun x hx w hw => ⟨hJ x hx w hw.1, h₂inv x hx w hw.2⟩
  rcases h₂ (J ⊓ I₂) hJ₂ inf_le_right with h | h
  · left
    refine le_antisymm (fun j hj => ?_) hJ₁
    have hj' : j ∈ I₁ ⊔ I₂ := htop ▸ Subgroup.mem_top j
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hj'
    have hzJ : z ∈ J := by
      have := J.mul_mem (J.inv_mem (hJ₁ hy)) hj
      simpa using this
    have hz1 : z = 1 := by
      have hz' : z ∈ J ⊓ I₂ := ⟨hzJ, hz⟩
      rw [h] at hz'
      exact Subgroup.mem_bot.mp hz'
    rw [hz1, mul_one]
    exact hy
  · right
    rw [eq_top_iff, ← htop]
    exact sup_le hJ₁ (by rw [← h]; exact inf_le_left)

theorem inf_eq_bot_and_sup_eq_top {H : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}
    (htop : I₁ ⊔ I₂ = ⊤) (h₁inv : StableUnder H I₁)
    (h₁ : ∀ J, StableUnder H J → J ≤ I₁ → J = ⊥ ∨ J = I₁) (h₂inv : StableUnder H I₂)
    (h₂ : ∀ J, StableUnder H J → J ≤ I₂ → J = ⊥ ∨ J = I₂) {U : Subgroup W}
    (hUne : U ≠ ⊥) (hUinv : StableUnder H U) (hU : ∀ J, StableUnder H J → J ≤ U → J = ⊥ ∨ J = U)
    (hU₂ : U ≠ I₂) : U ⊓ I₂ = ⊥ ∧ U ⊔ I₂ = ⊤ := by
  have hUle : ¬ U ≤ I₂ := fun hle => by
    rcases h₂ U hUinv hle with h | h
    · exact hUne h
    · exact hU₂ h
  constructor
  · have hinv : StableUnder H (U ⊓ I₂) := fun x hx w hw => ⟨hUinv x hx w hw.1, h₂inv x hx w hw.2⟩
    rcases hU (U ⊓ I₂) hinv inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hUle
  · rcases eq_or_eq_top_of_le (I₁ := I₂) (I₂ := I₁) (by rw [sup_comm]; exact htop) h₁inv h₁
        (stableUnder_sup hUinv h₂inv) le_sup_right with h | h
    · exact absurd (h ▸ le_sup_left) hUle
    · exact h

private theorem bijective_restrict_mk' {I₂ C : Subgroup W} (hC : C ⊓ I₂ = ⊥)
    (hC' : C ⊔ I₂ = ⊤) : Function.Bijective ((QuotientGroup.mk' I₂).comp C.subtype) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : W) ∈ I₂ := (QuotientGroup.eq_one_iff (x : W)).mp hx
    have h2 : (x : W) ∈ C ⊓ I₂ := ⟨x.2, h1⟩
    rw [hC] at h2
    exact Subtype.ext (by simpa using Subgroup.mem_bot.mp h2)
  · intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective I₂ y
    have hw : w ∈ C ⊔ I₂ := hC' ▸ Subgroup.mem_top w
    obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using hz

private theorem mul_inv_mul_mul_inv_mul (hW : ∀ w : W, w ^ 2 = 1) (a b w : W) :
    a * b⁻¹ * (a * b⁻¹ * w) = w := by
  have ha : a * a = 1 := by rw [← sq]; exact hW a
  have hb : b⁻¹ * b⁻¹ = 1 := by rw [← sq]; exact hW _
  calc a * b⁻¹ * (a * b⁻¹ * w) = (a * a) * (b⁻¹ * b⁻¹) * w := by
        simp only [mul_assoc, mul_left_comm]
    _ = w := by rw [ha, hb, one_mul, one_mul]

theorem exists_shear (hW : ∀ w : W, w ^ 2 = 1) {I₁ I₂ U : Subgroup W} (h₁ : I₁ ⊓ I₂ = ⊥)
    (h₁' : I₁ ⊔ I₂ = ⊤) (hU : U ⊓ I₂ = ⊥) (hU' : U ⊔ I₂ = ⊤) :
    ∃ τ : MulAut W, τ * τ = 1 ∧ (∀ v ∈ I₂, τ v = v) ∧ I₁.map τ.toMonoidHom = U ∧
      (∀ g : MulAut W, g ∈ stabSub I₁ → g ∈ stabSub I₂ → g ∈ stabSub U → g * τ = τ * g) ∧
      ∀ V : Subgroup W, V ⊓ I₂ = ⊥ → V ⊔ I₂ = ⊤ → V.map τ.toMonoidHom = V → U = I₁ := by
  classical
  let q : W →* W ⧸ I₂ := QuotientGroup.mk' I₂
  let α₁ : W ⧸ I₂ ≃* ↥I₁ := (MulEquiv.ofBijective _ (bijective_restrict_mk' h₁ h₁')).symm
  let αU : W ⧸ I₂ ≃* ↥U := (MulEquiv.ofBijective _ (bijective_restrict_mk' hU hU')).symm
  have hq₁ : ∀ y, q (α₁ y : W) = y := fun y =>
    (MulEquiv.ofBijective _ (bijective_restrict_mk' h₁ h₁')).apply_symm_apply y
  have hqU : ∀ y, q (αU y : W) = y := fun y =>
    (MulEquiv.ofBijective _ (bijective_restrict_mk' hU hU')).apply_symm_apply y
  have hα₁ : ∀ x ∈ I₁, ∀ y, q x = y → (α₁ y : W) = x := by
    intro x hx y hxy
    have : α₁ (q x) = ⟨x, hx⟩ :=
      (MulEquiv.ofBijective _ (bijective_restrict_mk' h₁ h₁')).symm_apply_apply ⟨x, hx⟩
    rw [← hxy, this]
  have hαU : ∀ x ∈ U, ∀ y, q x = y → (αU y : W) = x := by
    intro x hx y hxy
    have : αU (q x) = ⟨x, hx⟩ :=
      (MulEquiv.ofBijective _ (bijective_restrict_mk' hU hU')).symm_apply_apply ⟨x, hx⟩
    rw [← hxy, this]
  let τ₀ : W →* W :=
    { toFun := fun w => (αU (q w) : W) * (α₁ (q w) : W)⁻¹ * w
      map_one' := by simp
      map_mul' := fun w w' => by
        simp only [map_mul, Subgroup.coe_mul, mul_inv]
        simp only [mul_assoc, mul_left_comm, mul_comm] }
  have hτ₀ : ∀ w, τ₀ w = (αU (q w) : W) * (α₁ (q w) : W)⁻¹ * w := fun w => rfl
  have hqτ : ∀ w, q (τ₀ w) = q w := by
    intro w
    rw [hτ₀, map_mul, map_mul, map_inv, hqU, hq₁, mul_inv_cancel, one_mul]
  have hinv : ∀ w, τ₀ (τ₀ w) = w := by
    intro w
    rw [hτ₀ (τ₀ w), hqτ, hτ₀ w]
    exact mul_inv_mul_mul_inv_mul hW _ _ w
  let τ : MulAut W :=
    { toFun := τ₀
      invFun := τ₀
      left_inv := hinv
      right_inv := hinv
      map_mul' := τ₀.map_mul }
  have hτ : ∀ w, τ w = (αU (q w) : W) * (α₁ (q w) : W)⁻¹ * w := fun w => rfl
  have hτI₂ : ∀ v ∈ I₂, τ v = v := by
    intro v hv
    have hqv : q v = 1 := (QuotientGroup.eq_one_iff v).mpr hv
    rw [hτ, hqv, map_one, map_one]
    simp
  have hτI₁ : ∀ x ∈ I₁, τ x = (αU (q x) : W) := by
    intro x hx
    rw [hτ, hα₁ x hx (q x) rfl, inv_mul_cancel_right]
  refine ⟨τ, MulEquiv.ext fun w => hinv w, hτI₂, ?_, ?_, ?_⟩
  ·
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      change τ x ∈ U
      rw [hτI₁ x hx]
      exact (αU (q x)).2
    · intro hu
      refine ⟨(α₁ (q u) : W), (α₁ (q u)).2, ?_⟩
      change τ (α₁ (q u) : W) = u
      rw [hτI₁ _ (α₁ (q u)).2, hq₁]
      exact hαU u hu _ rfl
  ·
    intro g hg₁ hg₂ hgU
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hτ, hτ, map_mul, map_mul, map_inv]
    have hcomp : ∀ (C : Subgroup W) (αC : W ⧸ I₂ ≃* ↥C), (∀ y, q (αC y : W) = y) →
        (∀ x ∈ C, ∀ y, q x = y → (αC y : W) = x) → g ∈ stabSub C →
        (αC (q (g w)) : W) = g (αC (q w) : W) := by
      intro C αC hqC hαC hgC
      refine hαC _ ((hgC _).2 (αC (q w)).2) _ ?_
      have h1 : (αC (q w) : W)⁻¹ * w ∈ I₂ := by
        have h0 := hqC (q w)
        simp only [q, QuotientGroup.mk'_apply] at h0
        exact QuotientGroup.eq.mp h0
      have h2 := (hg₂ _).2 h1
      rw [map_mul, map_inv] at h2
      simp only [q, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq.mpr h2
    rw [hcomp I₁ α₁ hq₁ hα₁ hg₁, hcomp U αU hqU hαU hgU]
  ·
    intro V hV hV' hτV
    have hsec : ∀ v ∈ V, (αU (q v) : W) = (α₁ (q v) : W) := by
      intro v hv
      have hτv : τ v ∈ V := by
        rw [← hτV]
        exact ⟨v, hv, rfl⟩
      have h1 : τ v * v⁻¹ ∈ V := V.mul_mem hτv (V.inv_mem hv)
      have h2 : τ v * v⁻¹ ∈ I₂ := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change q (τ₀ v) * (q v)⁻¹ = 1
        rw [hqτ, mul_inv_cancel]
      have h3 : τ v * v⁻¹ ∈ V ⊓ I₂ := ⟨h1, h2⟩
      rw [hV, Subgroup.mem_bot, hτ, mul_inv_cancel_right, mul_inv_eq_one] at h3
      exact h3
    have hall : ∀ y : W ⧸ I₂, (αU y : W) = (α₁ y : W) := by
      intro y
      obtain ⟨⟨v, hv⟩, rfl⟩ := (bijective_restrict_mk' hV hV').2 y
      exact hsec v hv
    ext u
    constructor
    · intro hu
      rw [← hαU u hu (q u) rfl, hall]
      exact (α₁ (q u)).2
    · intro hu
      rw [← hα₁ u hu (q u) rfl, ← hall]
      exact (αU (q u)).2

private def irrSubs (H : Subgroup (MulAut W)) : Set (Subgroup W) :=
  {U | U ≠ ⊥ ∧ StableUnder H U ∧ ∀ J, StableUnder H J → J ≤ U → J = ⊥ ∨ J = U}

private theorem stableUnder_map {H : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W))) {J : Subgroup W} (hJ : StableUnder H J) :
    StableUnder H (J.map g.toMonoidHom) := by
  rintro x hx _ ⟨u, hu, rfl⟩
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) x).mp hx
  rw [inv_inv] at hx'
  refine ⟨(g⁻¹ * x * g) u, hJ _ hx' u hu, ?_⟩
  change g ((g⁻¹ * x * g) u) = x (g u)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]

private theorem map_mem_irrSubs {H : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W))) {U : Subgroup W} (hU : U ∈ irrSubs H) :
    U.map g.toMonoidHom ∈ irrSubs H := by
  obtain ⟨hU1, hUinv, hUirr⟩ := hU
  refine ⟨fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective _ g.injective).mp h),
    stableUnder_map hg hUinv, fun J hJ hJU => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) := (Subgroup.normalizer _).inv_mem hg
  have hback : (J.map g⁻¹.toMonoidHom).map g.toMonoidHom = J := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id J
    ext w
    simp
  have hle : J.map g⁻¹.toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hJU hx
    change g⁻¹ (g u) ∈ U
    rw [MulAut.inv_apply_self]
    exact hu
  rcases hUirr _ (stableUnder_map hg' hJ) hle with h | h
  · left
    rw [← hback, h, Subgroup.map_bot]
  · right
    rw [← hback, h]

@[instance_reducible] private def irrAction (H : Subgroup (MulAut W)) :
    MulAction ↥(Subgroup.normalizer (H : Set (MulAut W))) ↥(irrSubs H) where
  smul g U := ⟨U.1.map (g : MulAut W).toMonoidHom, map_mem_irrSubs g.2 U.2⟩
  one_smul U := Subtype.ext (StabLat.mem_stabSub_iff_map.mp (stabSub U.1).one_mem)
  mul_smul g g' U := Subtype.ext (by
    change U.1.map ((g : MulAut W) * g').toMonoidHom =
      (U.1.map (g' : MulAut W).toMonoidHom).map (g : MulAut W).toMonoidHom
    rw [Subgroup.map_map]
    rfl)

private theorem exists_fixed_of_odd [Finite W] {H : Subgroup (MulAut W)}
    {P : Subgroup (MulAut W)} (hPN : P ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hP : IsPGroup 2 P) (hodd : Nat.card ↥(irrSubs H) % 2 = 1) :
    ∃ U ∈ irrSubs H, P ≤ stabSub U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup W) :=
    Finite.of_injective (fun J : Subgroup W => (J : Set W)) SetLike.coe_injective
  let := irrAction H
  let : MulAction ↥P ↥(irrSubs H) := MulAction.compHom _ (Subgroup.inclusion hPN)
  have hcong := hP.card_modEq_card_fixedPoints (↥(irrSubs H))
  have hF : Nat.card ↥(MulAction.fixedPoints ↥P ↥(irrSubs H)) % 2 = 1 := by
    unfold Nat.ModEq at hcong
    omega
  obtain ⟨⟨U, hU⟩⟩ : Nonempty ↥(MulAction.fixedPoints ↥P ↥(irrSubs H)) :=
    (Nat.card_pos_iff.mp (by omega)).1
  refine ⟨U.1, U.2, fun a ha => ?_⟩
  have h1 := congrArg Subtype.val (hU ⟨a, ha⟩)
  exact StabLat.mem_stabSub_iff_map.mpr h1

private theorem mem_iff_of_map_eq {τ : MulAut W} {I₁ U : Subgroup W}
    (hτ : I₁.map τ.toMonoidHom = U) (v : W) : v ∈ I₁ ↔ τ v ∈ U := by
  rw [← hτ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem card_irrSubs_odd [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W} (h₁ : I₁ ⊓ I₂ = ⊥) (h₁' : I₁ ⊔ I₂ = ⊤)
    (hI₁ : I₁ ∈ irrSubs H) (hI₂ : I₂ ∈ irrSubs H) {U₀ : Subgroup W} (hU₀ : U₀ ∈ irrSubs H)
    (hU₀₁ : U₀ ≠ I₁) (hU₀₂ : U₀ ≠ I₂) : Nat.card ↥(irrSubs H) % 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup W) :=
    Finite.of_injective (fun J : Subgroup W => (J : Set W)) SetLike.coe_injective
  obtain ⟨hU₀c, hU₀c'⟩ := inf_eq_bot_and_sup_eq_top h₁' hI₁.2.1 hI₁.2.2 hI₂.2.1 hI₂.2.2
    hU₀.1 hU₀.2.1 hU₀.2.2 hU₀₂
  obtain ⟨τ, hττ, hτI₂, hτI₁, hτcomm, hτfix⟩ := exists_shear hW h₁ h₁' hU₀c hU₀c'
  have hτH : ∀ h ∈ H, h * τ = τ * h := fun h hh =>
    hτcomm h (le_stabSub_of_stableUnder hI₁.2.1 hh) (le_stabSub_of_stableUnder hI₂.2.1 hh)
      (le_stabSub_of_stableUnder hU₀.2.1 hh)
  have hτN : τ ∈ Subgroup.normalizer (H : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : τ * h * τ⁻¹ = h := by rw [← hτH h hh, mul_inv_cancel_right]
      rw [this]
      exact hh
    · intro hh
      have h2 : h = τ⁻¹ * (τ * h * τ⁻¹) * τ := by group
      have h3 : τ⁻¹ * (τ * h * τ⁻¹) * τ = τ * h * τ⁻¹ := by
        rw [mul_assoc, hτH _ hh, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h2, h3]
      exact hh
  have hZN : Subgroup.zpowers τ ≤ Subgroup.normalizer (H : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr hτN
  have hZp : IsPGroup 2 ↥(Subgroup.zpowers τ) :=
    E3.isPGroup_of_isElemAbelian2 (StabLat.isElemAbelian2_zpowers (by rw [sq]; exact hττ))
  let := irrAction H
  let : MulAction ↥(Subgroup.zpowers τ) ↥(irrSubs H) :=
    MulAction.compHom _ (Subgroup.inclusion hZN)
  have hcong := hZp.card_modEq_card_fixedPoints (↥(irrSubs H))
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥(irrSubs H) = {⟨I₂, hI₂⟩} := by
    ext U
    rw [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hU
      have hτU : U.1.map τ.toMonoidHom = U.1 :=
        congrArg Subtype.val (hU ⟨τ, Subgroup.mem_zpowers τ⟩)
      by_contra hne
      have hne' : U.1 ≠ I₂ := fun h => hne (Subtype.ext h)
      obtain ⟨hc, hc'⟩ := inf_eq_bot_and_sup_eq_top h₁' hI₁.2.1 hI₁.2.2 hI₂.2.1 hI₂.2.2
        U.2.1 U.2.2.1 U.2.2.2 hne'
      exact hU₀₁ (hτfix U.1 hc hc' hτU)
    · rintro rfl ⟨z, hz⟩
      apply Subtype.ext
      change I₂.map z.toMonoidHom = I₂
      have hτs : τ ∈ stabSub I₂ := StabLat.mem_stabSub_of_map_eq (by
        ext v
        constructor
        · rintro ⟨u, hu, rfl⟩
          change τ u ∈ I₂
          rw [hτI₂ u hu]
          exact hu
        · intro hv
          exact ⟨v, hv, hτI₂ v hv⟩)
      exact StabLat.mem_stabSub_iff_map.mp (Subgroup.zpowers_le.mpr hτs hz)
  have h1 : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers τ) ↥(irrSubs H)) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  rw [h1] at hcong
  unfold Nat.ModEq at hcong
  omega

theorem exists_conj_le_stabSub [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {I₁ I₂ : Subgroup W} (h₁ : I₁ ⊓ I₂ = ⊥) (h₁' : I₁ ⊔ I₂ = ⊤)
    (h₁ne : I₁ ≠ ⊥) (h₁inv : StableUnder H I₁)
    (h₁irr : ∀ J, StableUnder H J → J ≤ I₁ → J = ⊥ ∨ J = I₁)
    (h₂ne : I₂ ≠ ⊥) (h₂inv : StableUnder H I₂)
    (h₂irr : ∀ J, StableUnder H J → J ≤ I₂ → J = ⊥ ∨ J = I₂)
    {j : ℕ} (hj : 2 ≤ j) {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet j X)
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W))) :
    ∃ g : MulAut W, (∀ h ∈ H, g * h = h * g) ∧
      (A.map (MulAut.conj g).toMonoidHom ≤ stabSub I₁ ∨
        A.map (MulAut.conj g).toMonoidHom ≤ stabSub I₂) := by
  have hI₁ : I₁ ∈ irrSubs H := ⟨h₁ne, h₁inv, h₁irr⟩
  have hI₂ : I₂ ∈ irrSubs H := ⟨h₂ne, h₂inv, h₂irr⟩
  have hconj1 : A.map (MulAut.conj (1 : MulAut W)).toMonoidHom = A := by
    rw [map_one]
    exact Subgroup.map_id A
  have hI₁₂ : I₁ ≠ I₂ := fun h => h₁ne (by rw [← inf_idem I₁]; nth_rw 2 [h]; exact h₁)
  by_cases hperm : ∀ a ∈ A, I₁.map a.toMonoidHom = I₁ ∨ I₁.map a.toMonoidHom = I₂
  ·
    refine ⟨1, fun h _ => by rw [one_mul, mul_one], Or.inl ?_⟩
    rw [hconj1]
    have hind : sSupIndep ({I₁, I₂} : Set (Subgroup W)) :=
      (sSupIndep_pair hI₁₂).mpr (disjoint_iff.mpr h₁)
    refine le_stabSub_of_mem_aSet hW hj hA (hind.mono ?_)
    rintro _ ⟨a, ha, rfl⟩
    rcases hperm a ha with h | h
    · rw [h]; exact Set.mem_insert _ _
    · rw [h]; exact Set.mem_insert_of_mem _ rfl
  · push Not at hperm
    obtain ⟨a, ha, ha₁, ha₂⟩ := hperm
    have hodd := card_irrSubs_odd hW h₁ h₁' hI₁ hI₂ (map_mem_irrSubs (hAN ha) hI₁) ha₁ ha₂
    obtain ⟨U, hU, hAU⟩ := exists_fixed_of_odd hAN
      (E3.isPGroup_of_isElemAbelian2 hA.2.2.1) hodd
    by_cases hU₂ : U = I₂
    · subst hU₂
      exact ⟨1, fun h _ => by rw [one_mul, mul_one], Or.inr (by rw [hconj1]; exact hAU)⟩
    · obtain ⟨hUc, hUc'⟩ := inf_eq_bot_and_sup_eq_top h₁' h₁inv h₁irr h₂inv h₂irr
        hU.1 hU.2.1 hU.2.2 hU₂
      obtain ⟨τ, hττ, -, hτI₁, hτcomm, -⟩ := exists_shear hW h₁ h₁' hUc hUc'
      have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
      refine ⟨τ, fun h hh => (hτcomm h (le_stabSub_of_stableUnder h₁inv hh)
        (le_stabSub_of_stableUnder h₂inv hh) (le_stabSub_of_stableUnder hU.2.1 hh)).symm,
        Or.inl ?_⟩
      have hττu : ∀ v, τ (τ v) = v := fun v => by
        rw [← MulAut.mul_apply, hττ, MulAut.one_apply]
      rintro _ ⟨b, hb, rfl⟩ u
      change (τ * b * τ⁻¹) u ∈ I₁ ↔ u ∈ I₁
      rw [hτinv, mem_iff_of_map_eq hτI₁, mem_iff_of_map_eq hτI₁ u]
      have h1 : τ ((τ * b * τ) u) = b (τ u) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, hττu]
      rw [h1]
      exact hAU hb (τ u)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
