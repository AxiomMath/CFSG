module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDetCoord
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameGen
public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SeitzGeneration

namespace NbrFrameDet

theorem ggTorusDetEltElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGTorusDetEltElt p r R') : GGTorusDetEltElt p r R := by
  intro E hE hr h3
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := TableB.isElemAbelian_map hE e.toMonoidHom
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  obtain ⟨k, τ, hτ, hτE, w, s, hws, hP, hdet⟩ := h _ hE' (hcard ▸ hr) (hcard ▸ h3)
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτ, ?_, e.symm w, s, ?_, hP, hdet⟩
  · ext x
    constructor
    · rintro ⟨f, rfl⟩
      have hf : τ f ∈ E.map e.toMonoidHom := hτE ▸ ⟨f, rfl⟩
      obtain ⟨y, hy, hyf⟩ := hf
      simpa [← hyf] using hy
    · intro hx
      have hx' : e x ∈ τ.range := hτE ▸ ⟨x, hx, rfl⟩
      obtain ⟨f, hf⟩ := hx'
      exact ⟨f, by simp [hf]⟩
  · intro f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv e.symm w, ← map_mul, ← map_mul, hws f]

theorem ggTorusDetEltElt_of_sylowTorus_frame {G₀ : Type} [Group G₀] {p : ℕ} (hp : p.Prime)
    (u : (ZMod p)ˣ) (hu : u ^ 2 ≠ 1) (s n : G₀) (hs : orderOf s = p)
    (hn : n * s * n⁻¹ = s ^ (u : ZMod p).val)
    (hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center G₀)) {R : Type} [Group R]
    (hT : SylowTorus R p 3) (ρ : Fin 3 → G₀ →* R) (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B)) (r : ℕ) :
    GGTorusDetEltElt p r R := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, m, he, -, hm⟩ :=
    exists_frameTorus_of_commutingFrames hp (u : ZMod p) s n hs hn hZ ρ hρ hc
  have hF : IsElemAbelian p e.range := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨v, hv⟩ := a.2
      obtain ⟨w, hw⟩ := b.2
      show (a : R) * (b : R) = (b : R) * (a : R)
      rw [← hv, ← hw, ← map_mul, ← map_mul]
      congr 1
      exact mul_comm v w
    · obtain ⟨v, hv⟩ := hx
      rw [← hv, ← map_pow, ← ofAdd_toAdd v, ← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero,
        ofAdd_zero, map_one]
  have hFc : Nat.card e.range = p ^ 3 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective he, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  intro E hE _ h3
  have hEc : Nat.card E = p ^ 3 := le_antisymm (hT.rank_le hp hE) h3
  obtain ⟨x, hx⟩ := ExcHigh.exists_conj_of_sylowTorus_cube hp hT hF hFc hE hEc
  refine ⟨3, (MulAut.conj x).toMonoidHom.comp e, (MulAut.conj x).injective.comp he, ?_,
    x * m 0 * x⁻¹, ggScaleCoord u 0, ?_, hp, ?_⟩
  · rw [MonoidHom.range_comp, hx]
  · intro f
    have key := hm 0 (Multiplicative.toAdd f)
    rw [ofAdd_toAdd] at key
    have hs : ggScaleCoord u 0 f = Multiplicative.ofAdd (Function.update (Multiplicative.toAdd f)
        0 ((u : ZMod p) * Multiplicative.toAdd f 0)) := ggScaleCoord_apply u 0 _
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hs, ← key]
    group
  · rw [ggDetAut_ggScaleCoord hp u 0]
    exact hu

end NbrFrameDet

end CFSG.StandardType

end
