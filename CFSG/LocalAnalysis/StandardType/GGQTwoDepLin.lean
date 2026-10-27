module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDepSurv
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepSix
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepFive
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssembleCaseII

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_dep_lin (hHeart : GGQ2HeartInput) (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hB : ¬ D.Basis) (hII : ¬ D.CaseII) (h4 : 4 ≤ Module.finrank (ZMod 3) D.V) (x y : D.V)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hy : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {y})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  obtain ⟨e, hE, hcart, ha, -, hdim⟩ := ggQ2_dep_types D hB hII h4 x y hx0 hy0 hx hy
  rcases hdim with h6 | ⟨h5, -⟩
  ·
    have hsym : ∀ i j, D.cartan i j = D.cartan j i := by
      intro i j
      obtain ⟨p, rfl⟩ := e.surjective i
      obtain ⟨q, rfl⟩ := e.surjective j
      rw [hcart p q, hcart q p]
      exact congrFun (congrFun (CartanMatrix.E_transpose 6) q) p
    have hroots := ggQ2_dep_six_roots D e hE ha h6 x hx0 hx
    have hpm := ggQ2_dep_six_pm D hsym e hE h6 hroots A hW hTF
    exact ggQ2_P3_of_dual_pm D hsym A hW x hpm
  ·
    have hpm : ∀ a ∈ A, ∃ g ∈ D.weyl, (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) :=
      hHeart D e hE h5 A hW hTF
    have hweyl : D.weyl ≤ reflGp A := by
      rw [GGQ2Lin.weyl, GGQ2Lin.parab, Subgroup.closure_le]
      rintro t ⟨k, -, rfl⟩
      exact Subgroup.subset_closure
        ⟨hW (Subgroup.subset_closure ⟨k, Set.mem_univ k, rfl⟩),
          D.coroot k, D.root k, D.root_coroot_self k, rfl⟩
    exact ggQ2_P3_of_pm A x fun a ha => by
      obtain ⟨g, hg, hgcase⟩ := hpm a ha
      exact ⟨g, hweyl hg, hgcase⟩

theorem ggQ2_dep_orbit (hHeart : GGQ2HeartInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) (hbas : ¬ GGQTwoBasis M) (hII : ¬ M.toLin.CaseII) :
    ∃ u : ↥Bs, (u : G) ∈ D ∧ u ≠ 1 ∧ GGOrbitStableAt p Bs u := by
  subst hp
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hune : (⟨x, M.hx⟩ : ↥Bs) ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
  have hyne : y ≠ 1 := hnb.1.2.2.1
  have hy0 : M.yV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨y, M.hy⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨y, M.hy⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (by simpa using h0)
    exact hyne (Subtype.ext_iff.mp h1)
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (by simpa using h0)
    exact hune h1
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : FiniteDimensional (ZMod 3) M.V := Module.Finite.of_finite
  have : FiniteDimensional (ZMod 3) M.toLin.V := ‹FiniteDimensional (ZMod 3) M.V›
  have hcardV : Nat.card M.V = 3 ^ Module.finrank (ZMod 3) M.V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := M.V), Nat.card_zmod]
  have hcardM : Nat.card M.V = Nat.card ↥Bs := by
    calc Nat.card M.V = Nat.card (Additive ↥Bs) := (Nat.card_congr M.model.toEquiv).symm
      _ = Nat.card ↥Bs := Nat.card_congr Additive.toMul
  have hpowle : 3 ^ 4 ≤ 3 ^ Module.finrank (ZMod 3) M.V := by
    calc 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
      _ = Nat.card M.V := hcardM.symm
      _ = 3 ^ Module.finrank (ZMod 3) M.V := hcardV
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V :=
    (Nat.pow_le_pow_iff_right (hS.1.1.tableB_facts).1.one_lt).mp hpowle
  have hx := (ggQ2_fixed_lin M).1
  have hy := (ggQ2_fixed_lin M).2
  have hW := ggQ2_weyl_le_lin M
  have hTF : TransvectionFree M.linGroup := ggQ2_transvectionFree M hS.1.2.2.2.1
  have hA := ggQ2_dep_lin hHeart M.toLin hbas hII h4 M.xV M.yV hx0 hy0 hx hy M.linGroup hW hTF
  refine ⟨⟨x, M.hx⟩, hxD, hune, ?_⟩
  rw [ggQ2_orbit_iff M (by decide : (3 : ℕ) ≠ 2) ⟨x, M.hx⟩]
  exact hA

theorem ggQ2_dependentOther_of_heart (hHeart : GGQ2HeartInput) : GGQ2DependentOtherInput := by
  intro G _ _ p _ hp B Bs x L D J hS y K hnb M hbas hII hC hΓ
  exact ggQ2_reduction hS hC hΓ (ggQ2_dep_orbit hHeart hp hS hnb M hbas hII)

end CFSG.StandardType

end
