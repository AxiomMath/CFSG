module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Items
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal
open scoped commutatorElement

theorem mem_ggCenterOf_iff {G : Type} [Group G] (Y : Subgroup G) (x : G) :
    x ∈ ggCenterOf Y ↔ x ∈ Y ∧ ∀ y ∈ Y, y * x = x * y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun y hy => congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2), rfl⟩

theorem itemOne_of_core
    {U X : Type} [Group U] [Group X] [Finite X] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card ψ.ker))
    {Rr Rm : Subgroup U} (hRr : IsPGroup 2 Rr)
    (hcore : pCoreOf 2 (Subgroup.normalizer (Rr : Set U)) ⊔ (Rr ⊔ Rm) = ⊤) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)) ⊔
      (Rr.map ψ ⊔ Rm.map ψ) = ψ.range := by
  rw [← Subgroup.map_sup]
  exact pCoreOf_range_inf_normalizer_sup_eq_range hker hodd hRr
    (GGRootNorm.isPGroup_pCoreOf _) (GGRootNorm.pCoreOf_le _)
    (GGRootNorm.le_normalizer_pCoreOf _) hcore

theorem itemFour_of_core
    {U X : Type} [Group U] [Group X] [Finite X] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card ψ.ker))
    {Rr : Subgroup U} (hRr : IsPGroup 2 Rr)
    (hcomm : ⁅pCoreOf 2 (Subgroup.normalizer (Rr : Set U)),
        pCoreOf 2 (Subgroup.normalizer (Rr : Set U))⁆ ≤ Rr)
    (hcent : pCoreOf 2 (Subgroup.normalizer (Rr : Set U)) ≤ Subgroup.centralizer (Rr : Set U)) :
    ⁅pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)),
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X))⁆ ≤
        Rr.map ψ ∧
      pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)) ≤
        Subgroup.centralizer ((Rr.map ψ : Subgroup X) : Set X) :=
  item_four_of_pCore_le hker hodd hRr le_rfl hcomm hcent

theorem itemFourIrred_of_core
    {U X : Type} [Group U] [Group X] [Finite X] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card ψ.ker))
    {Rr : Subgroup U} (hRr : IsPGroup 2 Rr)
    (hirr : ∀ V : Subgroup U,
      ggCenterOf (pCoreOf 2 (Subgroup.normalizer (Rr : Set U))) ≤ V →
      V ≤ pCoreOf 2 (Subgroup.normalizer (Rr : Set U)) →
      Subgroup.normalizer (Rr : Set U) ≤ Subgroup.normalizer (V : Set U) →
      V = ggCenterOf (pCoreOf 2 (Subgroup.normalizer (Rr : Set U))) ∨
        V = pCoreOf 2 (Subgroup.normalizer (Rr : Set U))) :
    ∀ V : Subgroup X,
      ggCenterOf (pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X))) ≤ V →
      V ≤ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)) →
      V ≠ ggCenterOf
        (pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X))) →
      V ≠ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)) →
      ¬ (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X) ≤
          Subgroup.normalizer (V : Set X)) := by
  have hkerN : ψ.ker ≤ Subgroup.normalizer (Rr : Set U) :=
    hker.trans (Subgroup.center_le_normalizer (Rr : Set U))
  have hN := map_normalizer_eq_range_inf_normalizer_map hker hodd hRr
  have hQ := map_pCoreOf_eq_of_odd_central_ker hker hodd hkerN
  rw [← hN, ← hQ]
  intro V hV1 hV2 hV3 hV4 hVN
  set N := Subgroup.normalizer (Rr : Set U) with hNdef
  set Qt := pCoreOf 2 N with hQtdef
  let Vt : Subgroup U := V.comap ψ ⊓ Qt
  have hc1 : ggCenterOf Qt ≤ Vt := by
    intro z hz
    obtain ⟨hzQ, hzc⟩ := (mem_ggCenterOf_iff Qt z).1 hz
    refine ⟨?_, hzQ⟩
    refine hV1 ((mem_ggCenterOf_iff _ _).2 ⟨⟨z, hzQ, rfl⟩, ?_⟩)
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul, hzc q hq]
  have hc3 : N ≤ Subgroup.normalizer (Vt : Set U) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hψn : ψ n ∈ Subgroup.normalizer (V : Set X) := hVN ⟨n, hn, rfl⟩
    have h1 := Subgroup.mem_normalizer_iff.1 hψn (ψ x)
    have h2 := Subgroup.mem_normalizer_iff.1 (GGRootNorm.le_normalizer_pCoreOf N hn) x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨by simpa using h1.1 hx1, h2.1 hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨by simpa using h1.2 (by simpa using hx1), h2.2 hx2⟩
  rcases hirr Vt hc1 inf_le_right hc3 with h | h
  · apply hV3
    refine le_antisymm ?_ hV1
    intro v hv
    obtain ⟨q, hq, rfl⟩ := hV2 hv
    have hqV : q ∈ Vt := ⟨hv, hq⟩
    rw [h] at hqV
    obtain ⟨hqQ, hqc⟩ := (mem_ggCenterOf_iff Qt q).1 hqV
    refine (mem_ggCenterOf_iff _ _).2 ⟨⟨q, hq, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hqc y hy]
  · apply hV4
    refine le_antisymm hV2 ?_
    rintro _ ⟨q, hq, rfl⟩
    have : q ∈ Vt := h ▸ hq
    exact this.1


theorem ggRootSub_eq_map {U G : Type} [Group U] [Group G] (Δ : UniversalRootDatum U) (ψ : U →* G)
    (γ : Fin Δ.rank → ℤ) (u : U) :
    ggRootSub Δ ψ γ u = (ggRootSub Δ (MonoidHom.id U) γ u).map ψ := by
  simp [ggRootSub, Subgroup.map_id]

end CFSG.StandardType.LieKnownR2.Short
