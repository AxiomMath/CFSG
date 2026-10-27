module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki

variable {G : Type*} [Group G] [Finite G]

@[expose] def R1Full (G : Type*) [Group G] : Prop :=
  (∃ (N : Subgroup G) (_ : N.Normal),
    oddCore G < N ∧ Odd N.index ∧
    fusionIsBenderGroup (N ⧸ (oddCore G).subgroupOf N)) ∧
  ∀ H₁ H₂ : Subgroup G, fusionStronglyEmbedded H₁ → fusionStronglyEmbedded H₂ →
    ∃ g : G, H₁.map (MulAut.conj g⁻¹).toMonoidHom = H₂

omit [Finite G] in
theorem r1Full_iff_explicit :
    R1Full G ↔
      (∃ (N : Subgroup G) (_ : N.Normal),
        oddCore G < N ∧ Odd N.index ∧
        ExplicitRankOneModel (N ⧸ (oddCore G).subgroupOf N)) ∧
      ∀ H₁ H₂ : Subgroup G, fusionStronglyEmbedded H₁ → fusionStronglyEmbedded H₂ →
        ∃ g : G, H₁.map (MulAut.conj g⁻¹).toMonoidHom = H₂ := by
  unfold R1Full
  simp_rw [explicitRankOneModel_iff_fusionIsBenderGroup]

omit [Finite G] in
theorem rankOneModel_of_equiv {Y : Type*} [Group Y] (e : G ≃* Y)
    (hmodel : fusionIsBenderGroup Y) : fusionIsBenderGroup G := by
  rcases hmodel with ⟨f, hf, ⟨m⟩⟩ | ⟨f, hf, ⟨m⟩⟩ | ⟨a, ha, ⟨m⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans m⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans m⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans m⟩⟩)

theorem elementary_hull_odd_quotient_simple (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hV : IsElemAbelian 2 V)
    (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    IsSimpleGroup (G ⧸ oddCore G) := by
  let : IsSimpleGroup (G ⧸ twoPrimeCore G) :=
    (native_strong_embedding_of_order_conditions hH).isSimpleGroup_quotient_twoPrimeCore
    (involutionCore_eq_top_of_elementary_hull V hV hgen)
  exact (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_twoPrimeCore (G := G))).isSimpleGroup

theorem elementary_hull_odd_quotient_nonabelian (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    ∃ a b : G ⧸ oddCore G, a * b ≠ b * a := by
  let : IsSimpleGroup (G ⧸ oddCore G) :=
    elementary_hull_odd_quotient_simple H V hH hV hgen
  obtain ⟨E, hEcard, _⟩ := twoRankAtLeastTwo_of_elementary_card_ge_four V hV hcard
  let inclusion : E →* V := E.subtype
  let injection : E →* G ⧸ oddCore G :=
    ((QuotientGroup.mk' (oddCore G)).domRestrict V).comp inclusion
  have hinj : Function.Injective injection :=
    (odd_quotient_injective_on_elementary V (oddCore G) hV
      (CFSG.ComponentClassification.OddCore.odd_card G)).comp E.subtype_injective
  have hdiv : 4 ∣ Nat.card (G ⧸ oddCore G) := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_injective injection hinj
  by_contra hnonab
  let : IsMulCommutative (G ⧸ oddCore G) := isMulCommutative_iff.mpr (by
    intro a b
    exact not_ne_iff.mp fun hne => hnonab ⟨a, b, hne⟩)
  let : CommGroup (G ⧸ oddCore G) := IsMulCommutative.instCommGroup
  have hprime : Nat.Prime (Nat.card (G ⧸ oddCore G)) := IsSimpleGroup.prime_card
  rcases (Nat.dvd_prime hprime).mp hdiv with hfour | hfour
  · norm_num at hfour
  · rw [hfour.symm] at hprime
    norm_num at hprime

theorem elementary_hull_perfect_of_odd_quotient (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤)
    (hperfect : Group.IsPerfect (G ⧸ oddCore G)) : commutator G = ⊤ := by
  let : Group.IsPerfect (G ⧸ oddCore G) := hperfect
  let q : G →* G ⧸ oddCore G := QuotientGroup.mk' (oddCore G)
  have hmap : (commutator G).map q = ⊤ :=
    CFSG.ComponentClassification.CentralExtensions.derived_map_eq_top q
      (QuotientGroup.mk'_surjective _)
  have hsup : commutator G ⊔ oddCore G = ⊤ := by
    have hcomap := Subgroup.comap_map_eq q (commutator G)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
    exact hcomap.symm
  let abelianQuotient : G →* G ⧸ commutator G := QuotientGroup.mk' (commutator G)
  have hsurj : Function.Surjective (abelianQuotient.domRestrict (oddCore G)) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) y
    have hmem : g ∈ commutator G ⊔ oddCore G := hsup ▸ Subgroup.mem_top g
    obtain ⟨d, hd, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    refine ⟨⟨r, hr⟩, ?_⟩
    change abelianQuotient r = abelianQuotient (d * r)
    have hdq : abelianQuotient d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    rw [map_mul, hdq, one_mul]
  have hodd : Odd (Nat.card (G ⧸ commutator G)) :=
    (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (Subgroup.card_dvd_of_surjective hsurj)
  exact normal_eq_top_of_odd_index_elementary_hull V (commutator G) hV hgen
    (by simpa only [Subgroup.index_eq_card] using hodd)

theorem normal_elementary_hull_quasisimple (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hVH : V ≤ H)
    (hVnormal : (V.subgroupOf H).Normal) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    IsQuasisimple G ∧ Subgroup.center G = oddCore G ∧
      Odd (Nat.card (Subgroup.center G)) := by
  let : IsSimpleGroup (G ⧸ oddCore G) :=
    elementary_hull_odd_quotient_simple H V hH hV hgen
  have hnonab := elementary_hull_odd_quotient_nonabelian H V hH hV hcard hgen
  have hquotientPerfect : Group.IsPerfect (G ⧸ oddCore G) :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top _ hnonab⟩
  have hperfect := elementary_hull_perfect_of_odd_quotient V hV hgen hquotientPerfect
  have hRcenter := oddCore_le_center_of_normal_elementary_hull H V
    hH hVH hVnormal hV hcard hgen
  have hcenterR : Subgroup.center G ≤ oddCore G := by
    intro z hz
    have himage : (QuotientGroup.mk' (oddCore G)) z ∈
        Subgroup.center (G ⧸ oddCore G) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (oddCore G) y
      simpa only [map_mul] using congrArg (QuotientGroup.mk' (oddCore G))
        ((Subgroup.mem_center_iff.mp hz) g)
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ hnonab] at himage
    exact (QuotientGroup.eq_one_iff z).mp (Subgroup.mem_bot.mp himage)
  have hcenter := le_antisymm hcenterR hRcenter
  refine ⟨⟨hperfect, ?_⟩, hcenter, ?_⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hcenter).isSimpleGroup
  · rw [hcenter]
    exact CFSG.ComponentClassification.OddCore.odd_card G

theorem normal_elementary_hull_recognition (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hVH : V ≤ H)
    (hVnormal : (V.subgroupOf H).Normal) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤)
    (hrecognition : R1Full G) :
    IsQuasisimple G ∧ Subgroup.center G = oddCore G ∧
      Odd (Nat.card (Subgroup.center G)) ∧
      fusionIsBenderGroup (G ⧸ Subgroup.center G) := by
  obtain ⟨hquasi, hcenter, hodd⟩ := normal_elementary_hull_quasisimple H V
    hH hVH hVnormal hV hcard hgen
  obtain ⟨N, hNnormal, hRN, hindex, hmodel⟩ := hrecognition.1
  let : N.Normal := hNnormal
  have hNtop := normal_eq_top_of_odd_index_elementary_hull V N hV hgen hindex
  let e : N ≃* G := (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
  have hmap : ((oddCore G).subgroupOf N).map e.toMonoidHom = oddCore G := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hg
      refine ⟨⟨g, hRN.le hg⟩, hg, ?_⟩
      rfl
  let quotientEquiv := QuotientGroup.congr ((oddCore G).subgroupOf N) (oddCore G) e hmap
  have hwholeModel : fusionIsBenderGroup (G ⧸ oddCore G) :=
    rankOneModel_of_equiv quotientEquiv.symm hmodel
  exact ⟨hquasi, hcenter, hodd,
    rankOneModel_of_equiv (QuotientGroup.quotientMulEquivOfEq hcenter) hwholeModel⟩

end CFSG.ShultStronglyClosedTI
