module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Pre
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Quad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

namespace SmD4Nine

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem fix_pointwise_of_fixed_vector {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP3 : IsPGroup 3 P)
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hinv : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ P) {v : V} (hvW : v ∈ W)
    (hv0 : v ≠ 0) (hhv : h v = v) : ∀ w ∈ W, h w = w := by
  have hZP : Subgroup.zpowers h ≤ P := (Subgroup.zpowers_le).2 hh
  have hZ3 : IsPGroup 3 (Subgroup.zpowers h) := hP3.to_le hZP
  have hmod := three_group_finrank_mod_two (Subgroup.zpowers h) hZ3 W
    (fun g hg => hinv g (hZP hg))
  have hvmem : v ∈ W ⊓ fixedSpace (Subgroup.zpowers h) :=
    ⟨hvW, mem_fixedSpace_zpowers_iff.2 hhv⟩
  have hpos : 0 < Module.finrank (ZMod 2) ↥(W ⊓ fixedSpace (Subgroup.zpowers h)) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hvmem⟩, fun h0 => hv0 (congrArg Subtype.val h0)⟩
  have hle : Module.finrank (ZMod 2) ↥(W ⊓ fixedSpace (Subgroup.zpowers h)) ≤
      Module.finrank (ZMod 2) W := Submodule.finrank_mono inf_le_left
  have heq : W ⊓ fixedSpace (Subgroup.zpowers h) = W :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  intro w hw
  have : w ∈ W ⊓ fixedSpace (Subgroup.zpowers h) := by rw [heq]; exact hw
  exact mem_fixedSpace_zpowers_iff.1 this.2

theorem exists_fix_pointwise {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : Nat.card P = 9)
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hinv : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) : ∃ k ∈ P, k ≠ 1 ∧ ∀ w ∈ W, k w = w := by
  by_contra hcon
  push Not at hcon
  have hmap : ∀ g : P, W.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W := by
    intro g
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw => hinv g g.2 w hw) ?_
    intro w hw
    refine ⟨(g : V ≃ₗ[ZMod 2] V)⁻¹ w, hinv _ (P.inv_mem g.2) w hw, ?_⟩
    exact CntLin.apply_inv_apply _ _
  let f : P → (W ≃ₗ[ZMod 2] W) := fun g =>
    LinearEquiv.ofSubmodules (g : V ≃ₗ[ZMod 2] V) W W (hmap g)
  have hf : ∀ g : P, ∀ w : W, ((f g w : W) : V) = (g : V ≃ₗ[ZMod 2] V) w := fun g w => rfl
  have hinj : Function.Injective f := by
    intro g g' hgg
    have hw : ∀ w ∈ W, (g : V ≃ₗ[ZMod 2] V) w = (g' : V ≃ₗ[ZMod 2] V) w := by
      intro w hw
      have := congrArg (fun e : W ≃ₗ[ZMod 2] W => ((e ⟨w, hw⟩ : W) : V)) hgg
      simpa [hf] using this
    by_contra hne
    have hmem : (g : V ≃ₗ[ZMod 2] V)⁻¹ * (g' : V ≃ₗ[ZMod 2] V) ∈ P :=
      P.mul_mem (P.inv_mem g.2) g'.2
    have hne1 : (g : V ≃ₗ[ZMod 2] V)⁻¹ * (g' : V ≃ₗ[ZMod 2] V) ≠ 1 := by
      intro h1
      exact hne (Subtype.ext (inv_mul_eq_one.1 h1))
    obtain ⟨w, hwW, hwne⟩ := hcon _ hmem hne1
    apply hwne
    rw [LinearEquiv.mul_apply, ← hw w hwW, CntLin.inv_apply_apply]
  have hc := Nat.card_le_card_of_injective f hinj
  rw [hP, card_linearEquiv_two hW] at hc
  omega

theorem exists_adapted_equiv {W₁ W₂ : Submodule (ZMod 2) V} (hc : IsCompl W₁ W₂)
    (h₁ : Module.finrank (ZMod 2) W₁ = 2) (h₂ : Module.finrank (ZMod 2) W₂ = 2) :
    ∃ Ψ : V ≃ₗ[ZMod 2] M0, ∀ w₁ w₂ : V, w₁ ∈ W₁ → w₂ ∈ W₂ →
      ((Ψ (w₁ + w₂)).1 = 0 ↔ w₁ = 0) ∧ ((Ψ (w₁ + w₂)).2 = 0 ↔ w₂ = 0) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let Θ := Submodule.prodEquivOfIsCompl W₁ W₂ hc
  let e₁ : W₁ ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) W₁ h₁).equivFun.trans (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
  let e₂ : W₂ ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) W₂ h₂).equivFun.trans (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))
  refine ⟨Θ.symm.trans (e₁.prodCongr e₂), fun w₁ w₂ hw₁ hw₂ => ?_⟩
  have hΘ : Θ.symm (w₁ + w₂) = (⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hΨ : (Θ.symm.trans (e₁.prodCongr e₂)) (w₁ + w₂) = (e₁ ⟨w₁, hw₁⟩, e₂ ⟨w₂, hw₂⟩) := by
    simp [hΘ]
  rw [hΨ]
  refine ⟨?_, ?_⟩
  · simp only [LinearEquiv.map_eq_zero_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · simp only [LinearEquiv.map_eq_zero_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem exists_equiv_of_nine (hV : Module.finrank (ZMod 2) V = 4) {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hP : Nat.card P = 9) (hfix : fixedSpace P = ⊥) :
    ∃ Ψ : V ≃ₗ[ZMod 2] M0, ∀ v : V, q0 (Ψ v) = 1 ↔ (v ≠ 0 ∧ ∃ h ∈ P, h ≠ 1 ∧ h v = v) := by
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hcomm : IsMulCommutative P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP]; norm_num)
  have hc : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hV16 : Nat.card V = 16 := by
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]
    norm_num
  obtain ⟨h₀, hh₀, hh₀1, v₀, hv₀0, hv₀⟩ : ∃ h ∈ P, h ≠ 1 ∧ ∃ v : V, v ≠ 0 ∧ h v = v := by
    by_contra hcon
    push Not at hcon
    have hfree : ∀ h ∈ P, h ≠ 1 → ∀ v : V, h v = v → v = 0 := fun h hh h1 v hv => by
      by_contra hv0
      exact hcon h hh h1 v hv0 hv
    have := card_dvd_of_free P hfree
    rw [hP, hV16] at this
    norm_num at this
  have hh₀9 : h₀ ^ 9 = 1 := by
    have : (⟨h₀, hh₀⟩ : P) ^ 9 = 1 := by
      have := pow_card_eq_one' (G := P) (x := ⟨h₀, hh₀⟩)
      rwa [hP] at this
    exact congrArg Subtype.val this
  obtain ⟨hdisj, hsup⟩ := decomp_fix_comm h₀ (p := 9) (by decide) hh₀9 ⊤ (fun _ _ => trivial)
  have hcompl : IsCompl (fixSp V h₀ ⊤) (commSp V h₀ ⊤) := ⟨hdisj, codisjoint_iff.2 hsup⟩
  have hinv₁ : ∀ g ∈ P, ∀ w ∈ fixSp V h₀ ⊤, g w ∈ fixSp V h₀ ⊤ := by
    intro g hg w hw
    rw [CntLin.mem_fixSp] at hw ⊢
    refine ⟨trivial, ?_⟩
    have := DFunLike.congr_fun (hc h₀ hh₀ g hg) w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    rw [this, hw.2]
  have hinv₂ : ∀ g ∈ P, ∀ w ∈ commSp V h₀ ⊤, g w ∈ commSp V h₀ ⊤ := by
    intro g hg w hw
    obtain ⟨s, -, rfl⟩ := CntLin.mem_commSp.1 hw
    refine CntLin.mem_commSp.2 ⟨g s, trivial, ?_⟩
    have := DFunLike.congr_fun (hc h₀ hh₀ g hg) s
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    rw [map_sub, ← this]
  have hpar₁ := three_group_finrank_mod_two P hP3 _ hinv₁
  have hpar₂ := three_group_finrank_mod_two P hP3 _ hinv₂
  rw [hfix, inf_bot_eq, finrank_bot] at hpar₁ hpar₂
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hV] at hsum
  have hpos₁ : 0 < Module.finrank (ZMod 2) (fixSp V h₀ ⊤) := by
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v₀, CntLin.mem_fixSp.2 ⟨trivial, hv₀⟩⟩, ?_⟩
    intro h0
    exact hv₀0 (congrArg Subtype.val h0)
  have hpos₂ : 0 < Module.finrank (ZMod 2) (commSp V h₀ ⊤) := by
    have : ∃ u : V, h₀ u ≠ u := by
      by_contra hcon
      push Not at hcon
      exact hh₀1 (LinearEquiv.ext fun u => by simpa using hcon u)
    obtain ⟨u, hu⟩ := this
    refine Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨h₀ u - u, CntLin.mem_commSp.2 ⟨u, trivial, rfl⟩⟩, ?_⟩
    intro h0
    exact hu (sub_eq_zero.1 (congrArg Subtype.val h0))
  have hW₁2 : Module.finrank (ZMod 2) (fixSp V h₀ ⊤) = 2 := by omega
  have hW₂2 : Module.finrank (ZMod 2) (commSp V h₀ ⊤) = 2 := by omega
  obtain ⟨k₁, hk₁P, hk₁1, hk₁⟩ := exists_fix_pointwise hP hW₁2 hinv₁
  obtain ⟨k₂, hk₂P, hk₂1, hk₂⟩ := exists_fix_pointwise hP hW₂2 hinv₂
  obtain ⟨Ψ, hΨ⟩ := exists_adapted_equiv hcompl hW₁2 hW₂2
  refine ⟨Ψ, fun v => ?_⟩
  have hvsup : v ∈ fixSp V h₀ ⊤ ⊔ commSp V h₀ ⊤ := by rw [hsup]; trivial
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hvsup
  obtain ⟨hΨ1, hΨ2⟩ := hΨ w₁ w₂ hw₁ hw₂
  have hne0 : Ψ (w₁ + w₂) ≠ 0 ↔ w₁ + w₂ ≠ 0 :=
    ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h (Ψ.injective (by rw [h0, map_zero]))⟩
  rw [q0_eq_one_iff, hne0, hΨ1, hΨ2]
  constructor
  · rintro ⟨hv0, h | h⟩
    · refine ⟨hv0, k₂, hk₂P, hk₂1, ?_⟩
      rw [h, zero_add]
      rw [h, zero_add] at hv0
      exact hk₂ w₂ hw₂
    · refine ⟨hv0, k₁, hk₁P, hk₁1, ?_⟩
      rw [h, add_zero]
      rw [h, add_zero] at hv0
      exact hk₁ w₁ hw₁
  · rintro ⟨hv0, h, hhP, hh1, hhv⟩
    refine ⟨hv0, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    rw [map_add] at hhv
    have hmem1 : h w₁ - w₁ ∈ fixSp V h₀ ⊤ := sub_mem (hinv₁ h hhP w₁ hw₁) hw₁
    have hmem2 : h w₁ - w₁ ∈ commSp V h₀ ⊤ := by
      have : h w₁ - w₁ = w₂ - h w₂ := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm w₂ w₁]
        exact hhv
      rw [this]
      exact sub_mem hw₂ (hinv₂ h hhP w₂ hw₂)
    have hf₁ : h w₁ = w₁ :=
      sub_eq_zero.1 (Submodule.disjoint_def.1 hcompl.disjoint _ hmem1 hmem2)
    have hf₂ : h w₂ = w₂ := by
      have := hhv
      rw [hf₁] at this
      exact add_left_cancel this
    have hall₁ := fix_pointwise_of_fixed_vector hP3 hW₁2 hinv₁ hhP hw₁ hn1 hf₁
    have hall₂ := fix_pointwise_of_fixed_vector hP3 hW₂2 hinv₂ hhP hw₂ hn2 hf₂
    apply hh1
    refine LinearEquiv.ext fun u => ?_
    have hus : u ∈ fixSp V h₀ ⊤ ⊔ commSp V h₀ ⊤ := by rw [hsup]; trivial
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hus
    rw [map_add, hall₁ u₁ hu₁, hall₂ u₂ hu₂]
    rfl

omit [Finite V] in
theorem orthogonal_of_normalizes {P Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {Ψ : V ≃ₗ[ZMod 2] M0}
    (hΨ : ∀ v : V, q0 (Ψ v) = 1 ↔ (v ≠ 0 ∧ ∃ h ∈ P, h ≠ 1 ∧ h v = v))
    (hnorm : ∀ γ ∈ Γ, ∀ p ∈ P, γ * p * γ⁻¹ ∈ P) :
    Γ ≤ orthogonalSubgroupOf (fun v => q0 (Ψ v)) := by
  have key : ∀ γ ∈ Γ, ∀ v, q0 (Ψ v) = 1 → q0 (Ψ (γ v)) = 1 := by
    intro γ hγ v hv
    obtain ⟨hv0, h, hhP, hh1, hhv⟩ := (hΨ v).1 hv
    refine (hΨ (γ v)).2 ⟨?_, γ * h * γ⁻¹, hnorm γ hγ h hhP, ?_, ?_⟩
    · intro h0
      exact hv0 (by simpa using h0)
    · intro h1
      apply hh1
      have : γ⁻¹ * (γ * h * γ⁻¹) * γ = h := by group
      rw [← this, h1]
      group
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, CntLin.inv_apply_apply, hhv]
  intro γ hγ
  show ∀ v, q0 (Ψ (γ v)) = q0 (Ψ v)
  intro v
  rcases q0_eq_zero_or_one (Ψ v) with h0 | h1
  · rcases q0_eq_zero_or_one (Ψ (γ v)) with h0' | h1'
    · rw [h0, h0']
    · have := key γ⁻¹ (Γ.inv_mem hγ) (γ v) h1'
      rw [CntLin.inv_apply_apply, h0] at this
      exact absurd this (by decide)
  · rw [h1, key γ hγ v h1]

end SmD4Nine

end CFSG.Quasithin.SzN31
