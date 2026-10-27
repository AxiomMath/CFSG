module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12R6D8
public import CFSG.Quasithin.Vol2.Ch12Sec6L12a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_mem_Vv_beta_eq (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {c : ↥(coreMod 8)} (hc : c ∈ core01) :
    ∃ w : G, ∃ hw : w ∈ V, w ∈ Vv L V v ∧ F.β ⟨w, hw⟩ = QuotientGroup.mk c := by
  obtain ⟨h0, h1⟩ := mem_core01.1 hc
  have hx : Multiplicative.toAdd (c : PermMod 8) ∈ c01 :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h0, h1, mem_coreMod.1 c.2⟩
  obtain ⟨y, hyv, hyx⟩ := exists_coordV_eq h1222 hH hv hβ hx
  have hy := Vv_le_V hH v hyv
  obtain ⟨c', hc', hcy, hβc'⟩ := coordV_spec h1222 hH hv hβ hy hyv
  have hcc : c' = c :=
    Subtype.ext (Multiplicative.toAdd.injective (hcy.trans hyx))
  exact ⟨y, hy, hyv, by rw [hβc', hcc]⟩

theorem mem_Vv_of_beta_eq (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G} (hyV : y ∈ V)
    {c : ↥(coreMod 8)} (hc : c ∈ core01) (hβy : F.β ⟨y, hyV⟩ = QuotientGroup.mk c) :
    y ∈ Vv L V v := by
  obtain ⟨w, hw, hwv, hβw⟩ := exists_mem_Vv_beta_eq h1222 hH hv hβ hc
  have h := congrArg Subtype.val (S126L19.beta_inj F hZ (hβy.trans hβw.symm))
  rw [show y = w from h]
  exact hwv

theorem exists_mk_core01_of_coord_eq {c : ↥(coreMod 8)}
    (h : Multiplicative.toAdd (c : PermMod 8) 0 = Multiplicative.toAdd (c : PermMod 8) 1) :
    ∃ c' ∈ core01, (QuotientGroup.mk c : D8) = QuotientGroup.mk c' := by
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcases (Multiplicative.toAdd (c : PermMod 8) 0) with h0 | h0
  · exact ⟨c, mem_core01.2 ⟨h0, h.symm.trans h0⟩, rfl⟩
  · refine ⟨c * S126FE.eOm, mem_core01.2 ?_, ?_⟩
    · have h1 : Multiplicative.toAdd (c : PermMod 8) 1 = 1 := h.symm.trans h0
      have e0 : Multiplicative.toAdd ((S126FE.eOm : ↥(coreMod 8)) : PermMod 8) 0 = 1 := rfl
      have e1 : Multiplicative.toAdd ((S126FE.eOm : ↥(coreMod 8)) : PermMod 8) 1 = 1 := rfl
      simp only [Subgroup.coe_mul, toAdd_mul, Pi.add_apply, e0, e1, h0, h1]
      exact ⟨by decide, by decide⟩
    · rw [QuotientGroup.mk_mul, (S126FE.mk_eq_one_iff _).2 (Or.inr rfl), mul_one]

theorem exists_twenty (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∃ U : Finset ↥V, U.card = 20 ∧ (∀ u ∈ U, HasWt 4 (F.β u)) ∧
      (∀ u ∈ U, (u : G) ∉ Vv L V v) ∧ ∀ u ∈ U, ∀ u' ∈ U, (u : G)⁻¹ * u' ∈ Vv L V v := by
  classical
  obtain ⟨W, hW20, hWwt, hWnot, hWq⟩ := exists_D8_twenty
  set g : D8 → ↥V := Function.surjInv F.β_surj with hg
  have hgβ : ∀ y, F.β (g y) = y := Function.surjInv_eq F.β_surj
  have hginj : Function.Injective g := Function.injective_surjInv F.β_surj
  refine ⟨W.image g, by rw [Finset.card_image_of_injective _ hginj, hW20], ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hu
    rw [hgβ]
    exact hWwt y hy
  · intro u hu huv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨c, hc, hβc⟩ := beta_mem_of_mem_Vv h1222 F hH hv hβ (g y).2 huv
    rw [hgβ] at hβc
    exact hWnot y hy c hc hβc
  · intro u hu u' hu'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hu'
    obtain ⟨c, hc, hcq⟩ := hWq y hy y' hy'
    obtain ⟨w, hw, hwv, hβw⟩ := exists_mem_Vv_beta_eq h1222 hH hv hβ hc
    have hmem : (((g y)⁻¹ * g y' : ↥V) : G) = w := by
      have hb : F.β ((g y)⁻¹ * g y') = F.β ⟨w, hw⟩ := by
        rw [map_mul, map_inv, hgβ, hgβ, hcq, hβw]
      exact congrArg Subtype.val (S126L19.beta_inj F hZ hb)
    have : (((g y)⁻¹ * g y' : ↥V) : G) = ((g y : ↥V) : G)⁻¹ * ((g y' : ↥V) : G) := rfl
    rw [← this, hmem]
    exact hwv

end S126T2

end CFSG.Quasithin.H13
