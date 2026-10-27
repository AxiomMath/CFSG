module

public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_mem_sup_pCore {H N X : Subgroup G} {t : G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) (ht : t ∈ Subgroup.normalizer (N : Set G))
    (hNH : N ≤ H) (hXH : X ≤ H) (hX : ∀ x ∈ X, ⁅t, x⁆ ∈ N) :
    ∀ y ∈ X ⊔ N, ⁅t, y⁆ ∈ N := by
  let Y : Subgroup G :=
    { carrier := {y | y ∈ H ∧ ⁅t, y⁆ ∈ N}
      one_mem' := ⟨H.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨H.mul_mem hxH hyH, ?_⟩
        have h1 : ⁅t, x * y⁆ = ⁅t, x⁆ * (x * ⁅t, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact N.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hH hxH) ⁅t, y⁆).mp hy)
      inv_mem' := by
        rintro x ⟨hxH, hx⟩
        refine ⟨H.inv_mem hxH, ?_⟩
        have h1 : ⁅t, x⁻¹⁆ = x⁻¹ * (⁅t, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [h1]
        have h2 := (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hxH)) (⁅t, x⁆)⁻¹).mp
          (N.inv_mem hx)
        rwa [inv_inv] at h2 }
  have hNY : N ≤ Y := by
    intro n hn
    refine ⟨hNH hn, ?_⟩
    rw [commutatorElement_def]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp ht n).mp hn) (N.inv_mem hn)
  have hXY : X ≤ Y := by
    intro x hx
    exact ⟨hXH hx, hX x hx⟩
  intro y hy
  exact (sup_le hXY hNY hy).2

private theorem tauOf_le_of_le_sup_pCore {H T X X' : Subgroup G} (hX : X ≤ H)
    (hX' : X' ≤ X ⊔ pCoreOf 2 H) : E1.tauOf H T X ≤ E1.tauOf H T X' := by
  intro t ht
  obtain ⟨htT, htN, htX⟩ := E1.mem_tauOf.mp ht
  refine E1.mem_tauOf.mpr ⟨htT, htN, fun a' ha' => ?_⟩
  exact commutator_mem_sup_pCore (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) htN
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hX htX a' (hX' ha')

private theorem tauOf_eq_of_sup_pCore {H T A A' : Subgroup G} (hA : A ≤ H) (hA' : A' ≤ H)
    (h : A ⊔ pCoreOf 2 H = A' ⊔ pCoreOf 2 H) : E1.tauOf H T A = E1.tauOf H T A' :=
  le_antisymm (tauOf_le_of_le_sup_pCore hA ((le_sup_left : A' ≤ A' ⊔ pCoreOf 2 H).trans h.ge))
    (tauOf_le_of_le_sup_pCore hA' ((le_sup_left : A ≤ A ⊔ pCoreOf 2 H).trans h.le))

private theorem map_mk'_eq_of_sup_pCore {Q : Type*} [Group Q] (N X X' : Subgroup Q) [N.Normal]
    (h : X ⊔ N = X' ⊔ N) : X.map (QuotientGroup.mk' N) = X'.map (QuotientGroup.mk' N) := by
  have hN : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)
  have key : ∀ Y : Subgroup Q,
      (Y ⊔ N).map (QuotientGroup.mk' N) = Y.map (QuotientGroup.mk' N) := by
    intro Y
    rw [Subgroup.map_sup, hN, sup_bot_eq]
  calc X.map (QuotientGroup.mk' N) = (X ⊔ N).map (QuotientGroup.mk' N) := (key X).symm
    _ = (X' ⊔ N).map (QuotientGroup.mk' N) := by rw [h]
    _ = X'.map (QuotientGroup.mk' N) := key X'

private theorem eOne_congr_bar {Q : Type} [Group Q] {X X' : Subgroup Q}
    (h : E1.barO2 Q X = E1.barO2 Q X') : E1.EOne Q X ↔ E1.EOne Q X' := by
  unfold E1.EOne
  rw [h]

private theorem eTwo_congr_bar {Q : Type} [Group Q] {S X X' : Subgroup Q}
    (h₁ : E1.tauOf (⊤ : Subgroup Q) S X = E1.tauOf (⊤ : Subgroup Q) S X')
    (h₂ : E1.barRad Q X = E1.barRad Q X') : E1.ETwo Q S X ↔ E1.ETwo Q S X' := by
  unfold E1.ETwo
  rw [h₁, h₂]

private theorem isE_of_sup_pCore {i : ℕ} {H T B B' K : Subgroup G} (hT : IsSylowIn 2 T H)
    (hB : B ≤ T) (hB' : B' ≤ T) (hBab : IsElemAbelian 2 B)
    (h : B ⊔ pCoreOf 2 H = B' ⊔ pCoreOf 2 H) (hK : E1.IsE i H T B K) : E1.IsE i H T B' K := by
  obtain ⟨hKH, hτK, hSK, hrest⟩ := hK
  have hBH : B ≤ H := hB.trans hT.le
  have hB'H : B' ≤ H := hB'.trans hT.le
  have hτeq : E1.tauOf H T B = E1.tauOf H T B' := tauOf_eq_of_sup_pCore hBH hB'H h
  have hBτ : B ⊔ pCoreOf 2 H ≤ E1.tauOf H T B := E1.le_tauOf hT hB hBab
  have hτTK : E1.tauOf H T B ≤ K := hτK.trans inf_le_right
  have hBK : B ≤ K := ((le_sup_left : B ≤ B ⊔ pCoreOf 2 H).trans hBτ).trans hτTK
  have hB'K : B' ≤ K :=
    ((le_sup_left : B' ≤ B' ⊔ pCoreOf 2 H).trans (h.ge.trans hBτ)).trans hτTK
  have hOK : pCoreOf 2 H ≤ K :=
    ((le_sup_right : pCoreOf 2 H ≤ B ⊔ pCoreOf 2 H).trans hBτ).trans hτTK
  have hOK' : pCoreOf 2 H ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOK
      (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hBK2 : B ⊔ pCoreOf 2 K = B' ⊔ pCoreOf 2 K := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · exact ((le_sup_left : B ≤ B ⊔ pCoreOf 2 H).trans h.le).trans (sup_le_sup le_rfl hOK')
    · exact ((le_sup_left : B' ≤ B' ⊔ pCoreOf 2 H).trans h.ge).trans (sup_le_sup le_rfl hOK')
  have hsubK : B.subgroupOf K ⊔ CFSG.Open.pCore 2 ↥K =
      B'.subgroupOf K ⊔ CFSG.Open.pCore 2 ↥K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBK,
      Subgroup.map_subgroupOf_eq_of_le hB'K]
    exact hBK2
  have hPR : CFSG.Open.pCore 2 ↥K ≤ CFSG.solvableRadical ↥K := by
    haveI : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥K) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥K)).isNilpotent
    exact A3.le_solvableRadical inferInstance inferInstance
  have hR : ∀ Y : Subgroup ↥K,
      Y ⊔ CFSG.solvableRadical ↥K = (Y ⊔ CFSG.Open.pCore 2 ↥K) ⊔ CFSG.solvableRadical ↥K := by
    intro Y
    rw [sup_assoc, sup_eq_right.mpr hPR]
  have hsubR : B.subgroupOf K ⊔ CFSG.solvableRadical ↥K =
      B'.subgroupOf K ⊔ CFSG.solvableRadical ↥K := by
    rw [hR (B.subgroupOf K), hsubK, ← hR (B'.subgroupOf K)]
  have hbar : E1.barO2 ↥K (B.subgroupOf K) = E1.barO2 ↥K (B'.subgroupOf K) :=
    map_mk'_eq_of_sup_pCore (CFSG.Open.pCore 2 ↥K) _ _ hsubK
  have hrad : E1.barRad ↥K (B.subgroupOf K) = E1.barRad ↥K (B'.subgroupOf K) :=
    map_mk'_eq_of_sup_pCore (CFSG.solvableRadical ↥K) _ _ hsubR
  have hτQ : E1.tauOf (⊤ : Subgroup ↥K) ((T ⊓ K).subgroupOf K) (B.subgroupOf K) =
      E1.tauOf (⊤ : Subgroup ↥K) ((T ⊓ K).subgroupOf K) (B'.subgroupOf K) := by
    apply tauOf_eq_of_sup_pCore le_top le_top
    rw [E1.pCoreOf_top_eq]
    exact hsubK
  refine ⟨hKH, ?_, hSK, ?_⟩
  · rw [← hτeq]
    exact hτK
  · rcases hrest with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(eOne_congr_bar hbar).mp h1, by rw [← hbar]; exact h2⟩
    · exact Or.inr ⟨(eTwo_congr_bar hτQ hrad).mp h1, by rw [← hrad]; exact h2⟩

theorem isE_congr_of_sup_pCore {i : ℕ} {H T B B' K : Subgroup G} (hT : IsSylowIn 2 T H)
    (hB : B ≤ T) (hB' : B' ≤ T) (hBab : IsElemAbelian 2 B) (hB'ab : IsElemAbelian 2 B')
    (h : B ⊔ pCoreOf 2 H = B' ⊔ pCoreOf 2 H) :
    E1.IsE i H T B K ↔ E1.IsE i H T B' K :=
  ⟨isE_of_sup_pCore hT hB hB' hBab h, isE_of_sup_pCore hT hB' hB hB'ab h.symm⟩

end CFSG.Quasithin.RonanE111
