module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_dual_of_sub_mem_span {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {X : V} (hX : X ≠ 0) (T : V →ₗ[ZMod p] V)
    (hT : ∀ v, T v - v ∈ (ZMod p) ∙ X) : ∃ f : Module.Dual (ZMod p) V, ∀ v, T v = v + f v • X := by
  let S : V →ₗ[ZMod p] ((ZMod p) ∙ X) := LinearMap.codRestrict _ (T - LinearMap.id) fun v => hT v
  refine ⟨(LinearEquiv.coord (ZMod p) V X hX).toLinearMap ∘ₗ S, fun v => ?_⟩
  have h := LinearEquiv.coord_apply_smul (ZMod p) V X hX (S v)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, LinearMap.codRestrict_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  abel

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem eq_of_mem_zpowers_of_noTransvection (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {x : ↥Bs} (hx : x ≠ 1) {φ ψ : MulAut ↥Bs}
    (hφ : φ ∈ ggInduced ⊤ Bs) (hψ : ψ ∈ ggInduced ⊤ Bs) (hφx : φ x = x) (hψx : ψ x = x)
    (hmod : ∀ b : ↥Bs, (ψ b)⁻¹ * φ b ∈ Subgroup.zpowers x) : φ = ψ := by
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  have hθ : ψ⁻¹ * φ ∈ ggInduced ⊤ Bs := mul_mem_ggInduced (inv_mem_ggInduced hψ) hφ
  have hψix : ψ⁻¹ x = x := by
    calc ψ⁻¹ x = ψ⁻¹ (ψ x) := by rw [hψx]
      _ = x := MulAut.inv_apply_self _ _ _
  have hθx : (ψ⁻¹ * φ) x = x := by rw [MulAut.mul_apply, hφx, hψix]
  have hθmod : ∀ b : ↥Bs, b⁻¹ * (ψ⁻¹ * φ) b ∈ Subgroup.zpowers x := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod b)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : ψ⁻¹ ((ψ b)⁻¹ * φ b) = b⁻¹ * (ψ⁻¹ * φ) b := by
      rw [map_mul, map_inv, MulAut.inv_apply_self, MulAut.mul_apply]
    rw [← h1, ← hk, map_zpow, hψix]
  have hX0 : ι (Additive.ofMul x) ≠ 0 := by
    intro h
    apply hx
    have h2 : Additive.ofMul x = Additive.ofMul (1 : ↥Bs) := ι.injective (by rw [h, ofMul_one,
      map_zero])
    exact Additive.ofMul.injective h2
  have hT : ∀ v, ggLin (p := p) ι (ψ⁻¹ * φ) v - v ∈ (ZMod p) ∙ ι (Additive.ofMul x) := by
    intro v
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hθmod (Additive.toMul (ι.symm v)))
    have hv : v = ι (Additive.ofMul (Additive.toMul (ι.symm v))) := by
      rw [ofMul_toMul, AddEquiv.apply_symm_apply]
    rw [hv, ggLin_apply_ofMul]
    have h1 : ι (Additive.ofMul ((ψ⁻¹ * φ) (Additive.toMul (ι.symm v)))) -
        ι (Additive.ofMul (Additive.toMul (ι.symm v))) =
        ι (Additive.ofMul ((Additive.toMul (ι.symm v))⁻¹ *
          (ψ⁻¹ * φ) (Additive.toMul (ι.symm v)))) := by
      rw [ofMul_mul, ofMul_inv, map_add, map_neg]
      abel
    rw [h1, ← hk, ofMul_zpow, map_zsmul]
    exact zsmul_mem (Submodule.mem_span_singleton_self _) k
  obtain ⟨f, hf⟩ := exists_dual_of_sub_mem_span hX0 (ggLin (p := p) ι (ψ⁻¹ * φ)).toLinearMap hT
  have hfX : f (ι (Additive.ofMul x)) = 0 := by
    have h := hf (ι (Additive.ofMul x))
    rw [LinearEquiv.coe_coe, ggLin_apply_ofMul, hθx, left_eq_add, smul_eq_zero] at h
    exact h.resolve_right hX0
  by_cases hf0 : f = 0
  · have hT1 : ggLin (p := p) ι (ψ⁻¹ * φ) = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have h := hf v
      rw [hf0, LinearMap.zero_apply, zero_smul, add_zero, LinearEquiv.coe_coe] at h
      rw [h]
      rfl
    have h1 : ψ⁻¹ * φ = 1 := ggLin_injective ι (by rw [hT1, map_one])
    calc φ = ψ * (ψ⁻¹ * φ) := by group
      _ = ψ := by rw [h1, mul_one]
  · exact absurd (ggIsTransvection_of_apply ι hX0 hf0 hfX fun v => by
      rw [← hf v, LinearEquiv.coe_coe]) (hNT _ hθ)

theorem ggAutomizer_apply_eq_of_le_centralizer {H : Subgroup G} {x : ↥Bs}
    (hH : H ≤ Subgroup.centralizer ({(x : G)} : Set G)) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer H Bs) : φ x = x := by
  refine Subgroup.closure_induction (p := fun ψ _ => ψ x = x) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, hgH, -, hg⟩
    apply Subtype.ext
    rw [hg]
    have hc := Subgroup.mem_centralizer_iff.mp (hH hgH) (x : G) (Set.mem_singleton _)
    rw [← hc]
    group
  · rfl
  · intro ψ χ _ _ h1 h2
    rw [MulAut.mul_apply, h2, h1]
  · intro ψ _ h
    calc ψ⁻¹ x = ψ⁻¹ (ψ x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ _ _

end GG

@[expose] def GGTypeAStabBridgeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥Bs ≃+ V) (m : ℕ), 3 ≤ m → ¬ p ∣ m + 2 → ∀ (φJ : ℕ → MulAut ↥Bs)
      (φb : MulAut ↥Bs) (hJ : ℕ → V) (αJ : ℕ → Module.Dual (ZMod p) V) (hb : V)
      (αb : Module.Dual (ZMod p) V),
      GGChainPairing m hJ αJ hb αb →
      (∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j) →
      (∀ w, ggLin (p := p) ι φb w = w - αb w • hb) →
      ggAutomizer L Bs = Subgroup.closure ((φJ '' Set.Iio m) ∪ {φb}) →
      ∀ φ ∈ ggInduced ⊤ Bs, GGIsReflection p φ → (∀ b : ↥Bs, (b : G) = x → φ b = b) →
        ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x

theorem ggTypeA_reflection_mem_of_bridge (hB : GGTypeAStabBridgeInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hID : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs) [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) {m : ℕ}
    (hm : 3 ≤ m) (hpm : ¬ p ∣ m + 2) {φJ : ℕ → MulAut ↥Bs} {φb : MulAut ↥Bs} {hJ : ℕ → V}
    {αJ : ℕ → Module.Dual (ZMod p) V} {hb : V} {αb : Module.Dual (ZMod p) V}
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb)
    (hL : ggAutomizer L Bs = Subgroup.closure ((φJ '' Set.Iio m) ∪ {φb}))
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hφr : GGIsReflection p φ)
    (hφx : ∀ b : ↥Bs, (b : G) = x → φ b = b) : φ ∈ ggAutomizer L Bs := by
  obtain ⟨ψ, hψL, hmod⟩ := hB G p B Bs x L D J hcfg hOp hID hNT V ι m hm hpm φJ φb hJ αJ hb αb
    hPb hlinJ hlinb hL φ hφ hφr hφx
  have hS := hcfg.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hS.2.1
  have hx1 : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := fun h => hS.2.2.1 (congrArg Subtype.val h)
  have hLx : L ≤ Subgroup.centralizer ({((⟨x, hxBs⟩ : ↥Bs) : G)} : Set G) := hS.2.2.2.1.1
  have hψx : ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := ggAutomizer_apply_eq_of_le_centralizer hLx hψL
  have hmod' : ∀ b : ↥Bs, (ψ b)⁻¹ * φ b ∈ Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod b)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  rw [eq_of_mem_zpowers_of_noTransvection hcfg.2.1.2.1 hNT hx1 hφ
    (mem_ggInduced_top_of_mem_ggAutomizer hψL) (hφx _ rfl) hψx hmod']
  exact hψL

end CFSG.StandardType
