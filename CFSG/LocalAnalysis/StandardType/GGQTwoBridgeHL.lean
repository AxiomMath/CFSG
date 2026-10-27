module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2x_lin_simple {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (k : M.ι) :
    ggLin (p := p) M.model (M.simple k) = M.toLin.simpleRefl k :=
  ggLin_eq_reflection (p := p) M.model (M.toLin.root_coroot_self k) (M.simple_apply k)

private theorem ggQ2x_mem_zpowers_of_smul {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x : G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (model : Additive ↥Bs ≃+ V) (ψ : MulAut ↥Bs) (hx : x ∈ Bs) (c : ZMod p)
    (h : ggLin (p := p) model ψ (model (Additive.ofMul ⟨x, hx⟩)) =
      c • model (Additive.ofMul ⟨x, hx⟩)) :
    ψ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
  rw [zpow_natCast]
  have h2 : Additive.ofMul (ψ ⟨x, hx⟩) = Additive.ofMul (⟨x, hx⟩ ^ c.val) := by
    apply model.injective
    rw [← ggLin_apply_ofMul (p := p) model ψ ⟨x, hx⟩, h]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, ofMul_pow, map_nsmul]
  exact (Additive.ofMul.injective h2).symm

theorem ggQ2_HL_lin {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x y : G} {L D J K : Subgroup G} (hHL : GGLineStabNormalizesInput)
    (hS : GGQTwoSetting p B Bs x L D J) (M : GGQTwoModel p Bs x y D L J K) :
    ∀ φ ∈ M.linGroup, φ M.xV ∈ Submodule.span (ZMod p) {M.xV} →
      φ ∈ Subgroup.normalizer (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod p] M.V)) := by
  intro φ hφ hfixspan
  obtain ⟨ψ, hψ, hφψ⟩ := Subgroup.mem_map.mp hφ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfixspan
  have hfixψ : ψ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
    refine ggQ2x_mem_zpowers_of_smul M.model ψ M.hx c ?_
    rw [hφψ]
    simpa only [GGQTwoModel.xV] using hc.symm
  have hψN : ψ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    hHL G p B Bs x L D J hS.1 M.hx ψ hψ hfixψ
  have hparab : M.parabL {k | k ≠ M.a} =
      (Subgroup.closure (M.simple '' {k | k ≠ M.a})).map (ggLin (p := p) M.model) := by
    unfold GGQTwoModel.parabL GGQ2Lin.parab
    rw [MonoidHom.map_closure]
    congr 1
    ext v
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨M.simple k, ⟨k, hk, rfl⟩, ggQ2x_lin_simple M k⟩
    · rintro ⟨w, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, (ggQ2x_lin_simple M k).symm⟩
  have hmap : (ggAutomizer L Bs).map (ggLin (p := p) M.model) = M.parabL {k | k ≠ M.a} := by
    rw [M.automizer_L, ← hparab]
  have hnorm : ggLin (p := p) M.model ψ ∈
      Subgroup.normalizer ((ggAutomizer L Bs).map (ggLin (p := p) M.model)) :=
    Subgroup.le_normalizer_map (ggLin (p := p) M.model) ⟨ψ, hψN, rfl⟩
  rw [hφψ, hmap] at hnorm
  exact hnorm

end CFSG.StandardType

end
