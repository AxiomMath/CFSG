module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinSwap
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem exists_lemma115Hyp_centralizer (hq : QTKECore G) {A : Subgroup G} (hA2 : IsPGroup 2 A)
    (hA1 : A ≠ ⊥) (hAc : A ≤ Subgroup.centralizer (A : Set G)) :
    ∃ (S M : Subgroup G) (z : G), Lemma115Hyp (Subgroup.centralizer (A : Set G)) S M z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (A : Set G) with hHdef
  have hBH : A ⊔ Subgroup.centralizer (A : Set G) ≤ H := sup_le hAc le_rfl
  have hHB : H ≤ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf H
  obtain ⟨T, hST, hT⟩ := exists_isSylowTwoOf_of_le (le_top : S ≤ ⊤) hS.isPGroup
  have hAS : A ≤ S := (le_pCoreOf_of_le_normalizer hAc hHB hA2).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)
  have hTbot : T ≠ ⊥ := fun h => hA1 (le_bot_iff.1 (h ▸ (hAS.trans hST)))
  have hZne : centerOf T ≠ ⊥ := by
    have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTbot
    have hTp : IsPGroup 2 ↥T := hT.isPGroup
    have := hTp.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥T)
    intro hbot
    apply hc1
    have hcmem : ((c : ↥T) : G) ∈ centerOf T :=
      ⟨(c : ↥T).2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩)⟩
    rw [hbot, Subgroup.mem_bot] at hcmem
    exact Subtype.ext (Subtype.ext hcmem)
  obtain ⟨z, hzZ, hz1, hz2⟩ :=
    exists_involution_of_isPGroup_ne_bot (hT.isPGroup.to_le inf_le_left) hZne
  have hz2' : z * z = 1 := by rwa [sq] at hz2
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hloc : IsTwoLocal (Subgroup.centralizer ({z} : Set G)) :=
    ⟨Subgroup.zpowers z, fun h => hz1 (Subgroup.zpowers_eq_bot.mp h),
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; norm_num),
      (normalizer_zpowers_eq_centralizer hz2').symm⟩
  obtain ⟨M, hzM, hmax⟩ := Finite.exists_le_maximal hloc
  have hM : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M :=
    ⟨hmax.prop, fun K hK hMK => (hmax.eq_of_le hK hMK).symm⟩
  exact ⟨S, M, z, lemma116 hq.2.1 hA2 hA1 hBH hHB hS hT hST hzZ.1 hzZ.2 hz1 hz2 hM hzM⟩

theorem exists_lemma115Cases_centralizer (hlist : Lemma115_3_List) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G) {A : Subgroup G} (hA2 : IsPGroup 2 A)
    (hA1 : A ≠ ⊥) (hAc : A ≤ Subgroup.centralizer (A : Set G)) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer (A : Set G))) : ∃ z : G, Lemma115Cases K z := by
  obtain ⟨S, M, z, h⟩ := exists_lemma115Hyp_centralizer hq hA2 hA1 hAc
  exact ⟨z, hlist G hs hnab hq _ S M z h K hK⟩

omit [Finite G] in
theorem centralizer_sup_zpowers (A : Subgroup G) (t : G) :
    Subgroup.centralizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (le_sup_left : A ≤ A ⊔ Subgroup.zpowers t))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2
        ((le_sup_right : Subgroup.zpowers t ≤ A ⊔ Subgroup.zpowers t) (Subgroup.mem_zpowers t))))
  · rintro x ⟨hxA, hxt⟩
    have h1 : A ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hxA a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hxt).symm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 hy)

end Ambient

end E6

end CFSG.Quasithin
