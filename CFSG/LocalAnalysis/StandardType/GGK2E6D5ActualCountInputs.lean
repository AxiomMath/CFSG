module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5ActualDSPIdentity
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5SixC2SP
public import CFSG.LocalAnalysis.StandardType.GGK2E6OriginalAxes
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5ActualStabilizer

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7D CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem d5_actual_count_inputs
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (u : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (φ : Fin 5 → MulAut ↥Bs)
    (f : (ggCoxeterMatrixD 5).Group ≃* ggAutomizer L Bs)
    (hf : ∀ i : Fin 5,
      (f ((ggCoxeterMatrixD 5).simple i) : MulAut ↥Bs) = φ i)
    (hx : x ∈ Bs) (hy : y ∈ Bs)
    (hφ : ∀ i, α i (u i) = 2)
    (hK : ∀ i j, α i (u j) = (CartanMatrix.D 5 i j : ZMod 3))
    (hx0 : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) ≠ 0)
    (hαx : ∀ i, α i (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) = 0)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • u i)
    (hR : ∀ i, GGIsReflection 3 (φ i))
    (hclos : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∃ b : Module.Basis (Fin 6) (ZMod 3) V,
      b 0 = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) ∧
      (∃ a ∈ ggAutomizer L Bs,
        ggLin (p := 3) ι a (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) ∉
          Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))}) ∧
      Nat.card (MulAction.stabilizer
        ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι))
        (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))) ≤ 3840 := by
  classical
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let yV : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  haveI : Fintype ↥Bs := Fintype.ofFinite _
  haveI : Fintype V := Fintype.ofEquiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcardV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcardBs
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hv6 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hv6
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hv6.symm
  obtain ⟨b, hb0, hbC2⟩ :=
    exists_d5_six_c2sp_basis_of_cartan (V := V) (u := u) (α := α) (x := xV)
      hφ hK hx0 hαx hdim
  have hφrefl : ∀ i : Fin 5,
      ggLin (p := 3) ι (φ i) = Module.reflection (hφ i) := by
    intro i
    ext w
    rw [hlin i w, Module.reflection_apply]
  have hC2 : ∀ i : Fin 5, C2SP 3 b (ggLin (p := 3) ι (φ i)) := by
    intro i
    rw [hφrefl i]
    exact hbC2 i
  have hAL : ∀ a : V ≃ₗ[ZMod 3] V,
      DSP 3 b a ↔ a ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι) :=
    d5_actual_AL_eq_DSP ι b (ggAutomizer L Bs) f φ hf hclos hC2 hR
  have hmove : ∃ a ∈ ggAutomizer L Bs,
      ggLin (p := 3) ι a yV ∉ Submodule.span (ZMod 3) {yV} :=
    hH.exists_L_moves_y_line_of_dsp ι hx hy b (by simpa [xV] using hb0)
      (fun a ha => (hAL a).mp ha)
  have hstab : Nat.card (MulAction.stabilizer
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)) xV) ≤ 3840 :=
    hH.D5_actual_join_stabilizer_card_le ι hx b (by simpa [xV] using hb0) hAL
  exact ⟨b, by simpa [xV] using hb0, by simpa [yV] using hmove,
    by simpa [xV] using hstab⟩

end CFSG.StandardType

end
