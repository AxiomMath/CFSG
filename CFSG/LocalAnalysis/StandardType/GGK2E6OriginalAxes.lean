module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderKnownAux
public import CFSG.LocalAnalysis.StandardType.GGK2E6D5LineMovesActualBasisFour

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggAdd_not_span_of_not_zpowers
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {x y : G} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (hnot : y ∉ Subgroup.zpowers x) :
    ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∉
      Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 : c.val • ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) =
      ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val, ZMod.natCast_zmod_val]
    exact hc
  have hpow : (⟨x, hx⟩ : ↥Bs) ^ c.val = (⟨y, hy⟩ : ↥Bs) := by
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow]
    exact ((ι.toAddMonoidHom).map_nsmul c.val _).trans h1
  apply hnot
  have heq : x ^ c.val = y := congrArg Subtype.val hpow
  rw [← heq]
  exact Subgroup.npow_mem_zpowers x c.val

theorem GGResHyp.y_not_span_x
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (hx : x ∈ Bs) (hy : y ∈ Bs) :
    ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∉
      Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} :=
  ggAdd_not_span_of_not_zpowers ι hx hy
    (HdRo7C.hdRo7CLOKnownAux_D_eq_closure hH).2

theorem GGResHyp.exists_L_moves_y_line_of_dsp
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hx : x ∈ Bs) (hy : y ∈ Bs)
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    (hb : b 0 = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))
    (hDSP : ∀ a, HdRo7D.DSP 3 b a →
      a ∈ (ggAutomizer L Bs).map (ggLin (p := 3) ι)) :
    ∃ a ∈ ggAutomizer L Bs,
      ggLin (p := 3) ι a (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) ∉
        Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} := by
  have hnonaxis := hH.y_not_span_x ι hx hy
  rw [← hb] at hnonaxis
  obtain ⟨a, ha, hmove⟩ := d5_basis_exists_line_move b hnonaxis
  obtain ⟨a', ha', heq⟩ := hDSP a ha
  exact ⟨a', ha', heq.symm ▸ hmove⟩

end CFSG.StandardType

end
