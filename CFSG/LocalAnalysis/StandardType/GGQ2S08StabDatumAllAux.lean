module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CenterThree
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumAux
public import CFSG.LocalAnalysis.StandardType.GGHLDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

noncomputable def ggQ2s08x1p_pick {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : G :=
  Classical.choose (mem_ggAutomizer_iff.mp (by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩))

theorem ggQ2s08x1p_pick_spec {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    ggQ2s08x1p_pick hS hBsN M i ∈ L ∧
      ggQ2s08x1p_pick hS hBsN M i ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((M.simple i b : ↥Bs) : G) =
        ggQ2s08x1p_pick hS hBsN M i * b * (ggQ2s08x1p_pick hS hBsN M i)⁻¹ :=
  Classical.choose_spec (mem_ggAutomizer_iff.mp (by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩))

noncomputable def ggQ2s08x1p_psi {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    MulAut ↥(ggGamma L hBsN).range :=
  let g := ggQ2s08x1p_pick hS hBsN M i
  let hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.le_normalizer (ggQ2s08x1p_pick_spec hS hBsN M i).1
  let hgB : g ∈ Subgroup.normalizer (Bs : Set G) := (ggQ2s08x1p_pick_spec hS hBsN M i).2.1
  ggConjAut (ggGamma L hBsN).range
    (normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hgB hgL)

theorem ggQ2s08x1p_psi_compat {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ)
    (b : ↥Bs) :
    ggQ2s08x1p_psi hS hBsN M i ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (M.simple i b) := by
  apply Subtype.ext
  set g := ggQ2s08x1p_pick hS hBsN M i with hg
  have hspec := ggQ2s08x1p_pick_spec hS hBsN M i
  set hgL : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hspec.1 with hgLdef
  set hgB : g ∈ Subgroup.normalizer (Bs : Set G) := hspec.2.1 with hgBdef
  have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB b).mp b.2
  have htb : (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) = M.simple i b :=
    Subtype.ext (hspec.2.2 b).symm
  change ((ggConjAut (ggGamma L hBsN).range
      (normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hgB hgL)
      ((ggGamma L hBsN).rangeRestrict b) : ↥(ggGamma L hBsN).range) : MulAut L) = _
  rw [ggConjAut_apply, MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict,
    ggGamma_conj_normalizer L hBsN ⟨g, hgL⟩ b hgb, htb]

theorem ggQ2s08x1p_psi_mem {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    ggQ2s08x1p_psi hS hBsN M i ∈
      ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range := by
  refine ggConjAut_mem_ggAutomizer ?_ ?_
  · refine ⟨⟨ggQ2s08x1p_pick hS hBsN M i,
      (ggQ2s08x1p_pick_spec hS hBsN M i).1⟩, ?_⟩
    exact MulEquiv.ext fun l => Subtype.ext rfl
  · exact normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN
      (ggQ2s08x1p_pick_spec hS hBsN M i).2.1
      (Subgroup.le_normalizer (ggQ2s08x1p_pick_spec hS hBsN M i).1)

theorem ggQ2s08x1p_simple_x {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.simple i ⟨x, M.hx⟩ = ⟨x, M.hx⟩ := by
  obtain ⟨-, -, -, hLx, -⟩ := hS.1.1.tableB_facts
  have hmem : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hmem
  apply Subtype.ext
  rw [hg]
  have hcx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
  calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcx]
    _ = x := by group

theorem ggQ2s08x1p_root_xV {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.root i M.xV = 0 := by
  have hfix := ggQ2s08x1p_simple_x hS hBsN M i
  have h1 : ggLin (p := 3) M.model (M.simple i) M.xV = M.xV := by
    change ggLin (p := 3) M.model (M.simple i)
        (M.model (Additive.ofMul ⟨x, M.hx⟩)) = M.model (Additive.ofMul ⟨x, M.hx⟩)
    rw [ggLin_apply_ofMul (p := 3) M.model (M.simple i) ⟨x, M.hx⟩, hfix]
  rw [M.simple_apply i M.xV] at h1
  have h2 : M.root i M.xV • M.coroot i = 0 := sub_eq_self.mp h1
  have hc0 : M.coroot i ≠ 0 := by
    intro hc
    have hp := M.pairing i i
    rw [hc, map_zero] at hp
    have hp2 : ((M.cartan i i : ℤ) : ZMod 3) = 0 := hp.symm
    rw [M.isCartan.1 i] at hp2
    exact (by decide : ¬ ((2 : ZMod 3) = 0)) hp2
  exact (smul_eq_zero.mp h2).resolve_right hc0

theorem ggQ2s08x1p_ggLin_trans {p : ℕ} [Fact p.Prime] {E : Type*} [Group E]
    {V W : Type*} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (ι : Additive E ≃+ V) (e : V ≃ₗ[ZMod p] W) (φ : MulAut E) (w : W) :
    ggLin (p := p) (ι.trans e.toAddEquiv) φ w = e (ggLin (p := p) ι φ (e.symm w)) := by
  have h2 : (ι.trans e.toAddEquiv).symm w = ι.symm (e.symm w) := rfl
  rw [ggLin_apply, ggLin_apply, h2]
  rfl

theorem ggQ2s08x1p_rootMap_ker {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) :
    LinearMap.ker M.rootMap = Submodule.span (ZMod 3) {M.xV} := by
  apply le_antisymm
  · intro v hv
    change v ∈ Submodule.span (ZMod 3) {M.model (Additive.ofMul ⟨x, M.hx⟩)}
    rw [← M.fixed_x]
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    have hv' : ∀ i, M.root i v = 0 := by
      intro i
      have h1 : M.rootMap v = 0 := LinearMap.mem_ker.mp hv
      exact congrFun h1 i
    induction hφ using Subgroup.closure_induction with
    | mem ψ hψ =>
        obtain ⟨i, rfl⟩ := hψ
        rw [M.simple_apply i v, hv' i, zero_smul, sub_zero]
    | one => exact map_one (ggLin (p := 3) M.model) ▸ rfl
    | mul a b ha hb iha ihb =>
        rw [map_mul, LinearEquiv.mul_apply, ihb, iha]
    | inv a ha iha =>
        rw [map_inv]
        calc (ggLin (p := 3) M.model a)⁻¹ v
            = (ggLin (p := 3) M.model a)⁻¹ ((ggLin (p := 3) M.model a) v) := by rw [iha]
          _ = v := LinearEquiv.symm_apply_apply _ v
  · rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    change M.rootMap M.xV = 0
    funext i
    exact ggQ2s08x1p_root_xV hS hBsN M i

theorem ggQ2s08x1p_descent {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) :
    ∃ (ι : Additive ↥(ggGamma L hBsN).range ≃+ (M.V ⧸ Submodule.span (ZMod 3) {M.xV}))
      (φ : M.Λ → MulAut ↥(ggGamma L hBsN).range)
      (h : M.Λ → M.V ⧸ Submodule.span (ZMod 3) {M.xV})
      (α : M.Λ → Module.Dual (ZMod 3) (M.V ⧸ Submodule.span (ZMod 3) {M.xV})),
      (∀ b : ↥Bs, ι (Additive.ofMul (⟨ggGamma L hBsN b, b, rfl⟩ :
          ↥(ggGamma L hBsN).range)) =
        Submodule.Quotient.mk (M.model (Additive.ofMul b))) ∧
      (∀ i j, α i (h j) = ((M.cartan i j : ℤ) : ZMod 3)) ∧
      (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
      (Submodule.span (ZMod 3) (Set.range h) = ⊤ ∨
        ∀ v, (∀ i, α i v = 0) → v = 0) ∧
      (∀ i, φ i = ggQ2s08x1p_psi hS hBsN M i) := by
  obtain ⟨hp, hBs, -, hLx, -⟩ := hS.1.1.tableB_facts
  haveI : Fact (Nat.Prime 3) := Fact.mk hp
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔
      b ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
    intro b
    rw [ggGamma_eq_one_iff L hBsN b]
    constructor
    · intro hc
      have h2 : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hc⟩
      rw [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs M.hx hSS.2.2.1 hLx
        hSS.2.2.2.2] at h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
      exact Subgroup.mem_zpowers_iff.mpr
        ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · intro hb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hbG : (b : G) = x ^ k := by
        have h := congrArg Subtype.val hk
        rw [Subgroup.coe_zpow] at h
        exact h.symm
      have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
      have hbcent : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [hbG]
        exact Subgroup.zpow_mem (Subgroup.centralizer (L : Set G)) hxcent k
      exact hbcent
  obtain ⟨VA, instA, instM, ιA, q, hA, αA, hprop1, hsurj, hqker, hprop4, hprop5, hlinA⟩ :=
    ggHL_descent (p := 3) hBsN M.hx hker M.model M.simple M.coroot M.root M.simple_apply
      (fun i => ggQ2s08x1p_root_xV hS hBsN M i)
      (ggQ2s08x1p_psi hS hBsN M)
      (fun i b => ggQ2s08x1p_psi_compat hS hBsN M i b)
  letI : AddCommGroup VA := instA
  letI : Module (ZMod 3) VA := instM
  have hqker' : LinearMap.ker q = Submodule.span (ZMod 3) {M.xV} := hqker
  let e : VA ≃ₗ[ZMod 3] (M.V ⧸ Submodule.span (ZMod 3) {M.xV}) :=
    (LinearMap.quotKerEquivOfSurjective q hsurj).symm.trans
      (Submodule.quotEquivOfEq (LinearMap.ker q) (Submodule.span (ZMod 3) {M.xV}) hqker')
  have he : ∀ v : M.V, e (q v) = Submodule.Quotient.mk v := by
    intro v
    change (Submodule.quotEquivOfEq (LinearMap.ker q) (Submodule.span (ZMod 3) {M.xV}) hqker')
      ((LinearMap.quotKerEquivOfSurjective q hsurj).symm (q v)) = Submodule.Quotient.mk v
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    exact Submodule.quotEquivOfEq_mk _ _ _ _
  refine ⟨ιA.trans e.toAddEquiv, ggQ2s08x1p_psi hS hBsN M,
    (fun i => e (hA i)), (fun i => (αA i).comp e.symm.toLinearMap), ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    have hr : (⟨ggGamma L hBsN b, b, rfl⟩ : ↥(ggGamma L hBsN).range) =
        (ggGamma L hBsN).rangeRestrict b := rfl
    rw [hr]
    change e (ιA (Additive.ofMul ((ggGamma L hBsN).rangeRestrict b))) =
      Submodule.Quotient.mk (M.model (Additive.ofMul b))
    rw [← hprop1 b]
    exact he (M.model (Additive.ofMul b))
  · intro i j
    have h1 : (αA i).comp e.symm.toLinearMap (e (hA j)) = αA i (hA j) := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    rw [h1, ← hprop4 j, hprop5 i (M.coroot j), M.pairing i j]
  · intro i w
    have htrans : ggLin (p := 3) (ιA.trans e.toAddEquiv) (ggQ2s08x1p_psi hS hBsN M i) w =
        e (ggLin (p := 3) ιA (ggQ2s08x1p_psi hS hBsN M i) (e.symm w)) :=
      ggQ2s08x1p_ggLin_trans (p := 3) ιA e _ w
    rw [htrans, hlinA i (e.symm w), map_sub, map_smul, e.apply_symm_apply]
    rfl
  · right
    intro v hv
    have hv' : e.symm v ∈ q.range := by
      obtain ⟨w, hw⟩ := hsurj (e.symm v)
      exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ := hv'
    have hw0 : M.rootMap w = 0 := by
      funext i
      have h1 : M.root i w = 0 := by
        rw [← hprop5 i w, hw]
        exact hv i
      exact h1
    have hwker : w ∈ LinearMap.ker M.rootMap := LinearMap.mem_ker.mpr hw0
    rw [ggQ2s08x1p_rootMap_ker hS hBsN M] at hwker
    have hq0 : q w = 0 := by
      have hwq : w ∈ LinearMap.ker q := by
        rw [hqker']
        exact hwker
      exact LinearMap.mem_ker.mp hwq
    have : e.symm v = 0 := by rw [← hw, hq0]
    exact e.symm.injective (by rw [this, map_zero])
  · intro i
    rfl

theorem ggQ2s08x1p_card_ggLin {p : ℕ} [Fact p.Prime] {E : Type*} [Group E]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    (ι : Additive E ≃+ V) (φ : Λ → MulAut E) :
    Nat.card ↥(Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i))) =
      Nat.card ↥(Subgroup.closure (Set.range φ)) := by
  have h1 : Subgroup.closure (Set.range (fun i => ggLin (p := p) ι (φ i))) =
      (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι) := by
    rw [MonoidHom.map_closure]
    congr 1
    exact Set.range_comp (ggLin (p := p) ι) φ
  rw [h1]
  exact Subgroup.card_map_of_injective (ggLin_injective (p := p) ι)

theorem ggQ2s08x1p_hcard {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x)
    (ι : Additive ↥(ggGamma L hBsN).range ≃+ (M.V ⧸ Submodule.span (ZMod 3) {M.xV})) :
    Nat.card ↥(Subgroup.closure
        (Set.range fun i => ggLin (p := 3) ι (ggQ2s08x1p_psi hS hBsN M i))) ≤
      Nat.card ↥(ggAutomizer L Bs) := by
  rw [ggQ2s08x1p_card_ggLin (p := 3) ι (ggQ2s08x1p_psi hS hBsN M)]
  let A : Subgroup (MulAut L) := (ggGamma L hBsN).range
  let N : Subgroup G := L ⊓ Subgroup.normalizer (Bs : Set G)
  let α : N →* MulAut ↥Bs :=
    Bs.normalizerMonoidHom.comp
      (MonoidHom.codRestrict N.subtype (Subgroup.normalizer (Bs : Set G)) (fun g => g.2.2))
  let γN : N →* MulAut L :=
    L.normalizerMonoidHom.comp
      (MonoidHom.codRestrict N.subtype (Subgroup.normalizer (L : Set G))
        (fun g => Subgroup.le_normalizer g.2.1))
  let β : N →* MulAut ↥A :=
    A.normalizerMonoidHom.comp
      (MonoidHom.codRestrict γN (Subgroup.normalizer (A : Set (MulAut L)))
        (fun g => normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN g.2.2
          (Subgroup.le_normalizer g.2.1)))
  have hα_apply : ∀ (g : N) (b : ↥Bs),
      ((α g b : ↥Bs) : G) = (g : G) * (b : G) * (g : G)⁻¹ := fun g b => rfl
  have hβ_apply : ∀ (g : N) (a : ↥A),
      ((β g a : ↥A) : MulAut L) = (γN g) * (a : MulAut L) * (γN g)⁻¹ := fun g a => rfl
  have hαrange : α.range = ggAutomizer L Bs := by
    rw [ggAutomizer_eq]
    apply le_antisymm
    · rintro x ⟨g, rfl⟩
      exact ⟨(g : G), g.2.1, g.2.2, fun b => rfl⟩
    · rintro x ⟨g, hgL, hgB, hx⟩
      refine ⟨⟨g, hgL, hgB⟩, ?_⟩
      exact MulEquiv.ext fun b => Subtype.ext (hx b).symm
  let pickN : M.Λ → N := fun i =>
    ⟨ggQ2s08x1p_pick hS hBsN M i,
      (ggQ2s08x1p_pick_spec hS hBsN M i).1,
      (ggQ2s08x1p_pick_spec hS hBsN M i).2.1⟩
  have hαpick : ∀ i, α (pickN i) = M.simple i := by
    intro i
    refine MulEquiv.ext fun b => Subtype.ext ?_
    exact ((ggQ2s08x1p_pick_spec hS hBsN M i).2.2 b).symm
  have hβpick : ∀ i, β (pickN i) = ggQ2s08x1p_psi hS hBsN M i := by
    intro i
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    rw [ggQ2s08x1p_psi_compat hS hBsN M i b]
    apply Subtype.ext
    rw [hβ_apply (pickN i) ((ggGamma L hBsN).rangeRestrict b)]
    change (γN (pickN i)) * (ggGamma L hBsN b) * (γN (pickN i))⁻¹ =
      ggGamma L hBsN (M.simple i b)
    rw [show γN (pickN i) = L.normalizerMonoidHom
      ⟨ggQ2s08x1p_pick hS hBsN M i,
        Subgroup.le_normalizer (ggQ2s08x1p_pick_spec hS hBsN M i).1⟩ from rfl]
    rw [ggGamma_conj_normalizer L hBsN _ b
      ((Subgroup.mem_normalizer_iff.mp
        (ggQ2s08x1p_pick_spec hS hBsN M i).2.1 b).mp b.2)]
    exact congrArg (ggGamma L hBsN)
      (Subtype.ext ((ggQ2s08x1p_pick_spec hS hBsN M i).2.2 b).symm)
  have hker : α.ker ≤ β.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    have hgb : (g : G) * (b : G) * (g : G)⁻¹ = (b : G) := by
      have h2 : ((α g) b : G) = (((1 : MulAut ↥Bs) b) : G) :=
        congrArg Subtype.val (congrArg (fun f : MulAut ↥Bs => f b) hg)
      rw [hα_apply g b] at h2
      simpa using h2
    apply Subtype.ext
    rw [hβ_apply g ((ggGamma L hBsN).rangeRestrict b)]
    change (γN g) * (ggGamma L hBsN b) * (γN g)⁻¹ = ggGamma L hBsN b
    rw [show γN g = L.normalizerMonoidHom ⟨(g : G), Subgroup.le_normalizer g.2.1⟩ from rfl]
    rw [ggGamma_conj_normalizer L hBsN ⟨(g : G), Subgroup.le_normalizer g.2.1⟩ b
      (by rw [hgb]; exact b.2)]
    exact congrArg (ggGamma L hBsN) (Subtype.ext hgb)
  let Dq : N ⧸ α.ker →* MulAut ↥A := QuotientGroup.lift α.ker β hker
  let P : Subgroup N := Subgroup.closure (Set.range pickN)
  have hP : P = Subgroup.closure (Set.range pickN) := rfl
  have hαP : Subgroup.map α P = α.range := by
    rw [hP, MonoidHom.map_closure]
    have h2 : α '' Set.range pickN = Set.range M.simple := by
      ext y
      constructor
      · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hαpick i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨pickN i, ⟨i, rfl⟩, hαpick i⟩
    rw [h2, ← M.automizer_L]
    exact hαrange.symm
  have hβP : Subgroup.map β P =
      Subgroup.closure (Set.range (ggQ2s08x1p_psi hS hBsN M)) := by
    rw [hP, MonoidHom.map_closure]
    have h2 : β '' Set.range pickN = Set.range (ggQ2s08x1p_psi hS hBsN M) := by
      ext y
      constructor
      · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hβpick i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨pickN i, ⟨i, rfl⟩, hβpick i⟩
    rw [h2]
  have hβN : Subgroup.map β ⊤ = Subgroup.map β P := by
    apply le_antisymm
    · rintro y ⟨g, -, rfl⟩
      have hg : α g ∈ Subgroup.map α P := by rw [hαP]; exact ⟨g, rfl⟩
      obtain ⟨p, hp, hgp⟩ := hg
      have hmemker : p⁻¹ * g ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hgp, inv_mul_cancel]
      have hβeq : β (p⁻¹ * g) = 1 := MonoidHom.mem_ker.mp (hker hmemker)
      have h3 : (β p)⁻¹ * β g = 1 := by rw [← map_inv, ← map_mul, hβeq]
      have h4 : β g = β p := by
        calc β g = β p * ((β p)⁻¹ * β g) := by group
          _ = β p * 1 := by rw [h3]
          _ = β p := mul_one _
      exact ⟨p, hp, h4.symm⟩
    · exact Subgroup.map_mono le_top
  have hDqrange : Dq.range =
      Subgroup.closure (Set.range (ggQ2s08x1p_psi hS hBsN M)) := by
    have h1 : Dq.range = β.range := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨g, by rw [QuotientGroup.lift_mk]⟩
      · rintro y ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk g, by rw [QuotientGroup.lift_mk]⟩
    have h2 : β.range = Subgroup.map β P := by
      rw [MonoidHom.range_eq_map, hβN]
    rw [h1, h2, hβP]
  have hcard1 : Nat.card ↥Dq.range ≤ Nat.card (N ⧸ α.ker) :=
    Nat.card_le_card_of_surjective (fun x : N ⧸ α.ker => (⟨Dq x, ⟨x, rfl⟩⟩ : ↥Dq.range))
      (fun y => by obtain ⟨x, hx⟩ := y.2; exact ⟨x, Subtype.ext hx⟩)
  have hcard2 : Nat.card (N ⧸ α.ker) = Nat.card ↥(ggAutomizer L Bs) := by
    have hker_rr : α.rangeRestrict.ker = α.ker := MonoidHom.ker_rangeRestrict α
    have he : Nat.card (N ⧸ α.rangeRestrict.ker) = Nat.card ↥α.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α.rangeRestrict
        (MonoidHom.rangeRestrict_surjective α)).toEquiv
    rw [hker_rr] at he
    rw [he, hαrange]
  rw [← hDqrange]
  exact le_trans hcard1 (le_of_eq hcard2)

end CFSG.StandardType

end
