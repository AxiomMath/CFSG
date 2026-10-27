module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LNA
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SH1

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.Sec4.Ronan148L (E27Move)

structure RankThreeData (X : Type) [Group X] : Prop where
  cubeInner : CubeInner X
  exists_pair : ∃ F F' : Subgroup X, F ≤ F' ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
    CFSG.Assembly.IsElemAbelian 3 F' ∧ Nat.card F' = 27 ∧
    ∃ t : X, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ f ∈ F, t * f = f * t

section Row



theorem row427_of_e27Move
    {S X : Type} [Group S] [Finite S] [Group X] (eS : S ≃* X)
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hR : RankThreeData X) (hmove : E27Move X) : Row427 S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK htype
  obtain ⟨F, F', hFF', hF, hF9, hF', hF'27, t, ht1, ht2, htF⟩ := hR.exists_pair
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hZ : Subgroup.center ↥L = ⊥ := hZS ↥L (sectionFourHyp_subgroup hG L) hL.1 hZ3 ⟨e⟩
  let eL : ↥L ≃* X := (quotCenterEquivOfEqBot hZ).trans (e.trans eS)
  have hcube : CubeInner ↥L := cubeInner_of_mulEquiv eL hR.cubeInner
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  let ι : X →* G := L.subtype.comp eL.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp eL.symm.injective
  have hιL : ∀ x : X, ι x ∈ L := fun x => (eL.symm x).2
  have hZ' : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1 := by
    intro x hxL hxC
    have hc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hFF'ι : F.map ι ≤ F'.map ι := Subgroup.map_mono hFF'
  have hF'L : F'.map ι ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact hιL x
  have htF' : ∀ f ∈ F.map ι, ι t * f = f * ι t := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, htF x hx]
  have hC : ∀ w ∈ Subgroup.centralizer (L : Set G), w ^ 3 = 1 → w = 1 := fun w hw hw3 =>
    eq_one_of_mem_centralizer_of_partTwo hEF hZ' hF'L hFF'ι (Ronan148S.isElemAbelian_map _ hF)
      (by rw [Subgroup.card_map_of_injective hι, hF9]) (Ronan148S.isElemAbelian_map _ hF')
      (by rw [Subgroup.card_map_of_injective hι, hF'27]) (hιL t)
      (by rw [Ne, map_eq_one_iff ι hι]; exact ht1) (by rw [← map_pow, ht2, map_one])
      htF' hw hw3
  have hAL : A ≤ L := le_of_inner_of_centralizer hZ hcube hAN hA.1 hC
  set A₁ : Subgroup X := (A.subgroupOf L).map eL.toMonoidHom with hA₁
  have hA₁e : CFSG.Assembly.IsElemAbelian 3 A₁ :=
    Ronan148S.isElemAbelian_map _ (isElemAbelian_comap L.subtype L.subtype_injective hA.1)
  have hA₁c : Nat.card A₁ = 27 := by
    rw [hA₁, Subgroup.card_map_of_injective eL.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA.2]
  have hdL : d ∈ L := hAL hdA
  have hd₁ : eL ⟨d, hdL⟩ ∈ A₁ := ⟨⟨d, hdL⟩, hdA, rfl⟩
  have hd₁1 : eL ⟨d, hdL⟩ ≠ 1 := by
    rw [Ne, map_eq_one_iff _ eL.injective]
    intro h
    exact hd1 (congrArg Subtype.val h)
  obtain ⟨n, hn, hnd⟩ := hmove A₁ ⟨hA₁e, hA₁c⟩ _ hd₁ hd₁1
  have hnL : eL.symm n ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    have h := Subgroup.map_equiv_normalizer_eq (A.subgroupOf L) eL
    have hn' : n ∈ ((Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
        eL.toMonoidHom) := by
      rw [h]
      exact hn
    obtain ⟨m, hm, hmn⟩ := hn'
    rw [← hmn]
    simpa using hm
  have hnG : ((eL.symm n : ↥L) : G) ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_subgroupOf hAL hnL
  have hnd' := hN hnG
  apply hnd
  have h1 : eL.symm n ∈ Subgroup.normalizer
      (((Subgroup.zpowers d).subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hdL) hnd'
  rw [zpowers_subgroupOf hdL] at h1
  have h2 := Subgroup.map_equiv_normalizer_eq (Subgroup.zpowers (⟨d, hdL⟩ : ↥L)) eL
  rw [MonoidHom.map_zpowers] at h2
  have h3 : eL (eL.symm n) ∈ (Subgroup.normalizer
      ((Subgroup.zpowers (⟨d, hdL⟩ : ↥L) : Subgroup ↥L) : Set ↥L)).map eL.toMonoidHom :=
    ⟨_, h1, rfl⟩
  rw [h2] at h3
  simpa using h3

theorem rowOf427_of_e27Move
    {X : Type} [Group X]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* X) →
      Subgroup.center L = ⊥)
    (hR : RankThreeData X) (hmove : E27Move X) : RowOf427 X := by
  intro S _ _ _ _ ⟨eSX⟩
  refine row427_of_e27Move eSX ?_ hR hmove
  intro L _ _ hS hL hZ3 ⟨e'⟩
  exact hZS L hS hL hZ3 ⟨e'.trans eSX⟩

end Row

section Move

variable {X : Type} [Group X]

theorem e27Move_of_rep {E₀ : Subgroup X}
    (hrep : ∀ A : Subgroup X, CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 →
      ∃ φ : MulAut X, A = E₀.map φ.toMonoidHom)
    (hmv : ∀ s ∈ E₀, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (E₀ : Set X),
      n ∉ Subgroup.normalizer ((Subgroup.zpowers s : Subgroup X) : Set X)) : E27Move X := by
  intro A hA s hs hs1
  obtain ⟨φ, rfl⟩ := hrep A hA.1 hA.2
  obtain ⟨s', hs', rfl⟩ := hs
  have hs'1 : s' ≠ 1 := by
    rintro rfl
    exact hs1 (map_one _)
  obtain ⟨n, hn, hns⟩ := hmv s' hs' hs'1
  refine ⟨φ n, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨n, hn, rfl⟩
  · intro hn'
    apply hns
    have hZ : (Subgroup.zpowers s').map φ.toMonoidHom =
        Subgroup.zpowers (φ.toMonoidHom s') := MonoidHom.map_zpowers _ s'
    rw [← hZ, ← Subgroup.map_equiv_normalizer_eq] at hn'
    obtain ⟨m, hm, hmn⟩ := hn'
    rwa [φ.injective hmn] at hm

end Move

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
