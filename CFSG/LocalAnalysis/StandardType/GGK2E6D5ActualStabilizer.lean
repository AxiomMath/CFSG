module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmall
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DNormalizer
public import CFSG.LocalAnalysis.StandardType.GGP3LineNormalizer

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem GGResHyp.D5_actual_join_stabilizer_card_le
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hx : x ∈ Bs)
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    (hb : b 0 = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))
    (hAL : ∀ a, HdRo7D.DSP 3 b a ↔
      a ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι)) :
    Nat.card (MulAction.stabilizer
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι))
      (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))) ≤ 3840 := by
  classical
  let A₀ := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A := A₀.map (ggLin (p := 3) ι)
  let xB : ↥Bs := ⟨x, hx⟩
  let xV := ι (Additive.ofMul xB)
  let S : Subgroup (MulAut ↥Bs) := A₀ ⊓ MulAction.stabilizer (MulAut ↥Bs) xB
  have hC2 : ∀ φ ∈ S, HdRo7C.C2SP 3 b (ggLin (p := 3) ι φ) := by
    intro φ hφ
    have hφA : φ ∈ A₀ := hφ.1
    have hφfix : φ xB = xB := MulAction.mem_stabilizer_iff.mp hφ.2
    have hφtop : φ ∈ ggAutomizer ⊤ Bs :=
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)) hφA
    have hnorm := ggAutomizer_fixes_mem_normalizer ggLNoncyclicInput_holds
      hH.1 hx hφtop hφfix
    apply HdRo7D.d_normalizer_holds 3 rfl 5 (by norm_num) V b (ggLin (p := 3) ι φ)
    · intro s hs
      obtain ⟨ψ, hψ, heq⟩ := (hAL s).mp hs
      apply (hAL _).mpr
      refine ⟨φ * ψ * φ⁻¹, (Subgroup.mem_normalizer_iff.mp hnorm ψ).mp hψ, ?_⟩
      rw [map_mul, map_mul, map_inv, heq]
    · rw [hb]
      exact (ggLin_fix_iff (p := 3) ι φ xB).mp hφfix
  have hScard : Nat.card S ≤ 3840 := by
    have hl := ggResX2Aux_card_le_of_c2sp (p := 3) rfl b ι S hC2
    exact hl
  let f : S → MulAction.stabilizer A xV := fun φ =>
    ⟨⟨ggLin (p := 3) ι φ.val, ⟨φ.val, φ.property.1, rfl⟩⟩,
      MulAction.mem_stabilizer_iff.mpr
        ((ggLin_fix_iff (p := 3) ι φ.val xB).mp
          (MulAction.mem_stabilizer_iff.mp φ.property.2))⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨φ, hφ, heq⟩ := g.val.property
    have hgfix : g.val.val xV = xV := MulAction.mem_stabilizer_iff.mp g.property
    have hφfix : φ xB = xB := (ggLin_fix_iff (p := 3) ι φ xB).mpr (heq.symm ▸ hgfix)
    refine ⟨⟨φ, hφ, MulAction.mem_stabilizer_iff.mpr hφfix⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  exact (Nat.card_le_card_of_surjective f hf).trans hScard

end CFSG.StandardType

end
