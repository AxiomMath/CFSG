module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralInvolutionHullRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.TIInductionBase
public import CFSG.Quasithin.Background.GoldschmidtShultStatements

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.QuasithinUnique CFSG.ShultStronglyClosedTI

variable {G : Type} [Group G] [Finite G]

theorem omegaOne_of_stronglyEmbedded {T V : Subgroup G} (hVT : V ≤ T) (hV : V ≠ ⊥)
    (hVel : IsElemAbelian 2 V) (hclosed : fusionStronglyClosed (V : Set G) T)
    (hB : fusionStronglyEmbedded ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalClosure (V : Set G)))) :
    IsOmegaOne V (T ⊓ Subgroup.normalClosure (V : Set G)) := by
  set L := Subgroup.normalClosure (V : Set G) with hL
  have hVL : V ≤ L := Subgroup.le_normalClosure
  refine ⟨le_inf hVT hVL, ?_⟩
  rintro x ⟨hxT, hxL⟩ hx2
  by_cases hx1 : x = 1
  · rw [hx1]
    exact V.one_mem
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  have hv1' : v ≠ 1 := fun e => hv1 (Subtype.ext e)
  have hS := native_strong_embedding_of_order_conditions hB
  have hvInv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (⟨v, hVL hv⟩ : ↥L) :=
    ⟨fun e => hv1' (congrArg Subtype.val e), Subtype.ext (by simpa using hVel.2 v hv)⟩
  have hxInv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (⟨x, hxL⟩ : ↥L) :=
    ⟨fun e => hx1 (congrArg Subtype.val e), Subtype.ext (by simpa using hx2)⟩
  obtain ⟨g, hg⟩ := hS.involutions_conjugate hvInv hxInv
  have hg' : (g : G)⁻¹ * v * g = x := by
    simpa [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] using congrArg Subtype.val hg
  have := hclosed v hv g (by rw [hg']; exact hxT)
  rwa [hg'] at this

theorem normalClosure_eq_oddCore_sup_of_card_two (T : Sylow 2 G) {V : Subgroup G}
    (hVT : V ≤ (T : Subgroup G)) (hVel : IsElemAbelian 2 V) (hcard : Nat.card V = 2)
    (hclosed : fusionStronglyClosed (V : Set G) (T : Subgroup G)) :
    Subgroup.normalClosure (V : Set G) =
      oddCoreIn (Subgroup.normalClosure (V : Set G)) ⊔ V := by
  set L := Subgroup.normalClosure (V : Set G) with hL
  have hVL : V ≤ L := Subgroup.le_normalClosure
  obtain ⟨⟨z, hz⟩, hz1⟩ : ∃ a : ↥V, a ≠ 1 := by
    apply Subgroup.ne_bot_iff_exists_ne_one.mp
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hVeq : ∀ y ∈ V, y ≠ 1 → y = z := by
    intro y hy hy1
    obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : ↥V)).mp hcard
    have h1 := hc ⟨y, hy⟩ (fun e => hy1 (congrArg Subtype.val e))
    have h2 := hc ⟨z, hz⟩ hz1
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hz2 : z ^ 2 = 1 := hVel.2 z hz
  have hzT : z ∈ (T : Subgroup G) := hVT hz
  have hiso : ∀ g : G, g⁻¹ * z * g ∈ (T : Subgroup G) → g⁻¹ * z * g = z := by
    intro g hg
    refine hVeq _ (hclosed z hz g hg) fun e => hz1' ?_
    have := congrArg (fun w => g * w * g⁻¹) e
    simpa [mul_assoc] using this
  have hcent : (⟨z, hzT⟩ : ↥(T : Subgroup G)) ∈ Subgroup.center ↥(T : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    have h1 : (t : G) * z * (t : G)⁻¹ = z := by
      have := hiso (t : G)⁻¹ (by
        rw [inv_inv]
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem t.2 hzT)
          ((T : Subgroup G).inv_mem t.2))
      simpa using this
    show (t : G) * z = z * (t : G)
    calc (t : G) * z = (t : G) * z * (t : G)⁻¹ * (t : G) := by group
      _ = z * t := by rw [h1]
  have hord : orderOf (⟨z, hzT⟩ : ↥(T : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hz2 hz1'
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar T ⟨z, hzT⟩ hcent hord hiso
  have hconj : ∀ g : G, g⁻¹ * z * g ∈ V ⊔ CFSG.oddCore G := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcc : c⁻¹ * z * c = z := by
      rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
    have hkey : (c * k)⁻¹ * z * (c * k) = z * (z⁻¹ * k⁻¹ * z * k) := by
      calc (c * k)⁻¹ * z * (c * k) = k⁻¹ * (c⁻¹ * z * c) * k := by group
        _ = z * (z⁻¹ * k⁻¹ * z * k) := by rw [hcc]; group
    rw [hkey]
    refine Subgroup.mul_mem_sup hz ?_
    have h1 := (inferInstance : (CFSG.oddCore G).Normal).conj_mem k⁻¹ ((CFSG.oddCore G).inv_mem hk)
      z⁻¹
    rw [inv_inv] at h1
    exact (CFSG.oddCore G).mul_mem h1 hk
  have hLle : L ≤ V ⊔ CFSG.oddCore G := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨a, ha, hxa⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxa
    by_cases ha1 : a = 1
    · subst ha1
      simp
    · have haz := hVeq a ha ha1
      subst haz
      have := hconj c⁻¹
      simpa using this
  have hint : oddCoreIn L = L ⊓ CFSG.oddCore G :=
    CFSG.ComponentClassification.OddCore.normal_intersection G L
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hLle hx)
    have hbL : b ∈ L := by
      have := L.mul_mem (L.inv_mem (hVL ha)) hx
      simpa using this
    have hbO : b ∈ oddCoreIn L := by
      rw [hint]
      exact ⟨hbL, hb⟩
    have h := Subgroup.mul_mem_sup ha hbO
    rwa [sup_comm] at h
  · refine sup_le ?_ hVL
    rw [hint]
    exact inf_le_left

theorem shult_core_of_stronglyEmbedded (T : Sylow 2 G) {V : Subgroup G}
    (hVT : V ≤ (T : Subgroup G)) (hV : V ≠ ⊥) (hVel : IsElemAbelian 2 V)
    (hclosed : fusionStronglyClosed (V : Set G) (T : Subgroup G))
    (hB : fusionStronglyEmbedded ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalClosure (V : Set G)))) :
    ShultCoreConclusion (T : Subgroup G) V := by
  by_cases h2 : Nat.card V = 2
  · exact Or.inl ⟨h2, normalClosure_eq_oddCore_sup_of_card_two T hVT hVel h2 hclosed⟩
  · have hcard : 4 ≤ Nat.card V := ti_induction_card_ge_four T V hVT hV h2
    obtain ⟨hq, hz, -, hbender⟩ := normalizer_elementary_ambient_hull_native_recognition V hVel
      hcard hB
    exact Or.inr ⟨hcard, ⟨hq, hz, hbender⟩,
      omegaOne_of_stronglyEmbedded hVT hV hVel hclosed hB⟩

end CFSG.Quasithin.Shult
