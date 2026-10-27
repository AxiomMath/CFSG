module

public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Background.SmithD321Count
public import CFSG.Quasithin.Vol2.Ch3T326F
public import CFSG.Quasithin.Vol2.Ch3T326K

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def D36L32 {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) : Prop :=
  IsPSL 3 2 1 ↥(autSub L (orbSup T V)) ∧
    (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
    (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
      commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom ∧
        IsSumMod (commSub (orbSup T V) L ⊓ fixV Mp) V (V.map s.toMonoidHom)
          (commSub (orbSup T V) L)) ∧
    Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)

@[expose] def Concl326Cii {G : Type} [Group G] [Finite G] (T L V₀ : Subgroup G) : Prop :=
  Nonempty (↥(autOn (autOn (Subgroup.normalizer (conjClosure L T : Set G))
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))) ≃*
      MulAut ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) ∧
    conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
    (∃ s ∈ T ⊓ Subgroup.normalizer (L : Set G),
      s ∉ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))) ∧
    (∃ x ∈ T, ∀ s ∈ T ⊓ Subgroup.normalizer (L : Set G),
      s ∉ L ⊔ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) →
      ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ =
        CFSG.conjugate V₀ x ⊔ CFSG.conjugate (CFSG.conjugate V₀ x) s ∧
      CFSG.conjugate V₀ x ⊓ CFSG.conjugate (CFSG.conjugate V₀ x) s = ⊥) ∧
    Nat.card V₀ = 2 ^ 3

section Translate

variable {G : Type} [Group G] {X Y VM : Subgroup G} [IsMulCommutative ↥VM]

omit [IsMulCommutative ↥VM] in
theorem le_centralizer_of_forall_fix (hY : Y ≤ Subgroup.normalizer (VM : Set G)) (hX : X ≤ VM)
    (h : ∀ u ∈ X.subgroupOf VM, ∀ g ∈ autOn Y VM, g u = u) :
    X ≤ Subgroup.centralizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := h ⟨x, hX hx⟩ (Subgroup.mem_subgroupOf.mpr hx) _
    (Setup.mem_autOn_iff.mpr ⟨⟨y, hY hy⟩, hy, rfl⟩)
  have h2 : y * x * y⁻¹ = x := by
    have h3 := congrArg Subtype.val h1
    rwa [Setup.coe_conjAct_apply] at h3
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [h2]

theorem commSub_top_autOn (hYV : Y ≤ Subgroup.normalizer (VM : Set G)) :
    commSub ⊤ (autOn Y VM) = (⁅VM, Y⁆).subgroupOf VM := by
  rw [← commV_eq_commSub, Vol2.Ch11.SecC.B51.commV_autOn hYV]

end Translate

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem subgroupOf_conjugate {x : G} (hx : x ∈ T) :
    (CFSG.conjugate V₀ x).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) =
      (V₀.subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))).map
        (conjAct (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
          ⟨x⁻¹, c.T_le_NVM (T.inv_mem hx)⟩).toMonoidHom := by
  rw [map_conjAct_subgroupOf ((T325.V₀_le_V T V₀).trans (T325.V_le_VM T (conjClosure L T) V₀))]
  show _ = (CFSG.conjugate V₀ x⁻¹⁻¹).subgroupOf _
  rw [inv_inv]

theorem orbSup_conjugate [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] {x : G} (hx : x ∈ T) :
    orbSup (autOn T (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        ((CFSG.conjugate V₀ x).subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) =
      (conjClosure V₀ T).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) := by
  rw [c.subgroupOf_conjugate hx, SmithD321.orbSup_map_of_mem
    (Setup.mem_autOn_iff.mpr ⟨⟨x⁻¹, c.T_le_NVM (T.inv_mem hx)⟩, T.inv_mem hx, rfl⟩), c.orbSup_eq]

theorem card_subgroupOf_conjugate {x : G} (hx : x ∈ T) :
    Nat.card ↥((CFSG.conjugate V₀ x).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) =
      Nat.card ↥(V₀.subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  rw [c.subgroupOf_conjugate hx]
  exact Subgroup.card_map_of_injective
    (f := (conjAct _ ⟨x⁻¹, c.T_le_NVM (T.inv_mem hx)⟩).toMonoidHom) (MulEquiv.injective _)

end Ctx

end CFSG.Quasithin.H13.T326
