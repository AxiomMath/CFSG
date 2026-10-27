module

public import CFSG.Quasithin.Vol2.Ch1EightFourList
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.Ch1Four

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

theorem eq_of_modO2Image_eq {G : Type} [Group G] [Finite G] {S L K : Subgroup G}
    (hL : quasithinIsLocal S L) (hK : quasithinIsLocal S K) (hLK : L ≤ K)
    (heq : modO2Image (K ⊔ S) L = modO2Image (K ⊔ S) K) : L = K := by
  have hS : IsSylowTwoOf S (K ⊔ S) := ⟨le_sup_right, hK.1, hK.2.2.1⟩
  have hO : pCoreOf 2 (K ⊔ S) ≤ S := pCoreOf_two_le_of_isSylowTwoOf hS
  have hKLS : K ≤ L ⊔ S := by
    intro k hk
    have hkH : k ∈ K ⊔ S := (le_sup_left : K ≤ K ⊔ S) hk
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ S)) (⟨k, hkH⟩ : ↥(K ⊔ S)) ∈
        modO2Image (K ⊔ S) K := Subgroup.mem_map.mpr ⟨⟨k, hkH⟩, hk, rfl⟩
    rw [← heq] at hmem
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlk
    have h2 : ((l⁻¹ * ⟨k, hkH⟩ : ↥(K ⊔ S)) : G) ∈ S := by
      apply hO
      refine ⟨l⁻¹ * ⟨k, hkH⟩, ?_, rfl⟩
      exact hlk
    have hk' : k = (l : G) * ((l⁻¹ * ⟨k, hkH⟩ : ↥(K ⊔ S)) : G) := by simp
    rw [hk']
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hl))
      (Subgroup.mem_sup_right h2)
  have hH : L ⊔ S = K ⊔ S := le_antisymm (sup_le_sup_right hLK S) (sup_le hKLS le_sup_right)
  have hLc : L ∈ cComp (K ⊔ S) := by
    rw [← hH]
    exact cComp_of_isLocal hL
  exact (modO2Image_bijOn (K ⊔ S)).injOn hLc (cComp_of_isLocal hK) heq

theorem lemma128Four_of
    (h312 : A312ForSQTK) : Lemma128Four := by
  intro G _ _ hQ hs hnab S L hL hlist
  refine ⟨hL, fun K hK hLK => ?_⟩
  have hS : IsSylowTwoOf S (K ⊔ S) := ⟨le_sup_right, hK.1, hK.2.2.1⟩
  have hBH : L ≤ K ⊔ S := hLK.trans le_sup_left
  have hB : L ∈ lFamily S := mem_lFamily_of_isLocal hL
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.2.1.2.1
  have hperfX : Group.IsPerfect (ModO2 L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hX := listNum_of_a128FourList hperfX hlist
  obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hBH
  rcases lemma_1_2_4_list hQ hs hnab h312 hK.2.2.2 hS hBH hB (cComp_of_isLocal hK) hLK with
    heq | hcase | hnq
  · exact (eq_of_modO2Image_eq hL hK hLK heq).symm
  · exact (core hX (InitNum.of_mulEquiv e.symm (init_of_a312Case hcase))).elim
  · have hperfB : Group.IsPerfect ↥(modO2Image (K ⊔ S) L) :=
      Subgroup.isPerfect_iff.mpr (modO2Image_mem_lFamily hS hBH hB).2.1
    have hBL : modO2Image (K ⊔ S) L ≤ modO2Image (K ⊔ S) K :=
      Subgroup.map_mono (fun x hx => hLK hx)
    exact (core hX (InitNum.of_mulEquiv e.symm (init_of_a312Nonquasi hBL hperfB hnq))).elim

end CFSG.Quasithin.Ch1Four
