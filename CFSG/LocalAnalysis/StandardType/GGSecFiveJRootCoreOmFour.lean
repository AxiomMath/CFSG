module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDiag
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmEigen
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmLevi
import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.LeviComm
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
import CFSG.RankThree.PartOne.KFCL.L4Block
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Card
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 Polynomial

private theorem jcoreOm_le_or_le {G : Type*} [Group G] {L₁ L₂ T : Subgroup G}
    [IsSimpleGroup ↥L₁] [IsSimpleGroup ↥L₂] (hc : ∀ u ∈ L₁, ∀ v ∈ L₂, u * v = v * u)
    (hT : T ≤ L₁ ⊔ L₂) (hTn : (T.subgroupOf (L₁ ⊔ L₂)).Normal)
    (hab : ∃ a b : ↥T, a * b ≠ b * a) : L₁ ≤ T ∨ L₂ ≤ T := by
  have hTc : ∀ t ∈ T, ∀ s ∈ L₁ ⊔ L₂, s * t * s⁻¹ ∈ T := fun t ht s hs =>
    Subgroup.mem_subgroupOf.mp (hTn.conj_mem ⟨t, hT ht⟩ (Subgroup.mem_subgroupOf.mpr ht) ⟨s, hs⟩)
  have key : ∀ L : Subgroup G, IsSimpleGroup ↥L → L ≤ L₁ ⊔ L₂ →
      L₁ ⊔ L₂ ≤ Subgroup.normalizer (L : Set G) → ¬ L ≤ T → ∀ t ∈ T, ∀ l ∈ L, l * t = t * l := by
    intro L hL hLS hNL hLT t ht l hl
    have hn : (T.subgroupOf L).Normal := ⟨fun y hy g => Subgroup.mem_subgroupOf.mpr
      (hTc _ (Subgroup.mem_subgroupOf.mp hy) _ (hLS g.2))⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hL _ hn with h | h
    · have hcL : t * l * t⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL (hT ht)) l).mp hl) (L.inv_mem hl)
      have hcT : t * l * t⁻¹ * l⁻¹ ∈ T := by
        have h1 := T.mul_mem ht (hTc _ (T.inv_mem ht) _ (hLS hl))
        rwa [← mul_assoc, ← mul_assoc] at h1
      have h1 := Subgroup.disjoint_def.mp (Subgroup.subgroupOf_eq_bot.mp h) hcT hcL
      calc l * t = t * l * t⁻¹ * l⁻¹ * (l * t) := by rw [h1, one_mul]
        _ = t * l := by group
    · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hLT
  obtain ⟨a, b, hab⟩ := hab
  by_contra hne
  rw [not_or] at hne
  have hN₁ : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set G) :=
    sup_le Subgroup.le_normalizer fun v hv => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun u hu => hc u hu v hv)
  have hN₂ : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set G) :=
    sup_le (fun u hu => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun v hv => (hc u hu v hv).symm)) Subgroup.le_normalizer
  have hS : L₁ ⊔ L₂ ≤ Subgroup.centralizer {(a : G)} :=
    sup_le (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
        (key L₁ inferInstance le_sup_left hN₁ hne.1 a a.2 l hl))
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
        (key L₂ inferInstance le_sup_right hN₂ hne.2 a a.2 l hl))
  exact hab (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hS (hT b.2))).symm)

open CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2 CFSG.SeitzReduction.OmegaPilot in
private theorem jcoreOm_isSimple_levi {K V : Type} [Field K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {P₁ P₂ : HypPair Q}
    (h : P₁.Orth P₂) : IsSimpleGroup ↥(leviV Q P₁.e P₂.e P₁.f P₂.f) := by
  have hE : ∀ u w : V, eichler Q u w ∈ (⊤ : Subgroup (V ≃ₗ[K] V)) := fun _ _ => Subgroup.mem_top _
  have hL : leviFix ⊤ P₁ P₂ = leviV Q P₁.e P₂.e P₁.f P₂.f := by
    refine le_antisymm ((leviFix_le_closure h hE).trans (Subgroup.closure_mono ?_)) ?_
    · rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      exacts [Or.inl ⟨t, rfl⟩, Or.inr ⟨t, rfl⟩]
    · rw [leviV, Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      exacts [(eichler_mem_leviFix h hE t).1, (eichler_mem_leviFix h hE t).2]
  have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := K) hK
  exact ((MulEquiv.subgroupCongr hL).symm.trans (leviFixEquiv P₁ P₂ h hE)).isSimpleGroup

open CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2 in
private theorem jcoreOm_levi_le {K V : Type} [Field K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {A B : HypPair Q} (hAB : A.Orth B)
    {T : Subgroup (V ≃ₗ[K] V)} (hTq : CFSG.IsQuasisimple ↥T)
    (hTle : T ≤ leviV Q A.e B.e A.f B.f ⊔ leviV Q A.e B.f A.f B.e)
    (hTn : (T.subgroupOf (leviV Q A.e B.e A.f B.f ⊔ leviV Q A.e B.f A.f B.e)).Normal) :
    leviV Q A.e B.e A.f B.f ≤ T ∨ leviV Q A.e B.f A.f B.e ≤ T := by
  have h₁ := jcoreOm_isSimple_levi hK hAB
  have h₂ : IsSimpleGroup ↥(leviV Q A.e B.f A.f B.e) :=
    jcoreOm_isSimple_levi (P₁ := A) (P₂ := swapPair B) hK (orth_swapPair_right hAB)
  refine jcoreOm_le_or_le (leviV_comm_swap hAB) hTle hTn ?_
  obtain ⟨-, -, a, b, hab⟩ := hTq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem jcoreOm_fixed_four {n p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hx : OddOrderIsometry (quadPlus n F) p x) {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c)
    {i j : Fin n} (hij : i ≠ j) (hai : a i = 1) (haj : a j = 1)
    (hk : ∀ k, a k = 1 → k = i ∨ k = j)
    {T : Subgroup ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))}
    (hTq : CFSG.IsQuasisimple ↥T) (hTle : T ≤ supportedFixedDerived (quadPlus n F) x)
    (hTn : (T.subgroupOf (supportedFixedDerived (quadPlus n F) x)).Normal) :
    JCoreOmRootPair n F T := by
  classical
  have hAB := plusPair_orth (K := F) hij
  have hspan : Submodule.span F {(plusPair F i).e, (plusPair F i).f, (plusPair F j).e,
      (plusPair F j).f} = fixedSpace x := by
    rw [jcoreOm_eigen_eq_span (W := fixedSpace x) hxa 1 fun v => by
      rw [one_smul]; exact mem_fixedSpace]
    congr 1
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Subtype.exists,
      plusPair_e, plusPair_f]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨.inl i, by simp [hai], rfl⟩, ⟨.inr i, by simp [hai], rfl⟩,
        ⟨.inl j, by simp [haj], rfl⟩, ⟨.inr j, by simp [haj], rfl⟩]
    · rintro ⟨c, hc, rfl⟩
      rcases c with k | k <;> rcases hk k (by simpa using hc) with rfl | rfl <;> simp
  rw [supportedFixedDerived_eq_levi_of_card_ne_three hx _ _ hAB hspan (by omega) (by omega)]
    at hTle hTn
  rcases jcoreOm_levi_le hF hAB hTq hTle hTn with h | h
  · exact ⟨i, j, hij, false, true, fun c => ⟨h (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)),
      h (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))⟩⟩
  · exact ⟨i, j, hij, false, false, fun c => ⟨h (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)),
      h (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))⟩⟩

end CFSG.StandardType

end
