module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.Adapters.LieModelSimple
import CFSG.Walter.J1Props.Hyp
import CFSG.Walter.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

private lemma r95_opp_le_self (p : ℕ) (Y : Subgroup G) : Opp p Y ≤ Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (Subgroup.closure_le Y).2 fun _ hx => hx.1

private lemma r95_opp_le_L9 (Y W : Subgroup G) : Opp 3 Y ≤ L9 Y W := by
  intro x hx
  have h : (Opp 3 Y).map (MulAut.conj ((1 : ↥W) : G)).toMonoidHom ≤ L9 Y W :=
    le_iSup (fun w : ↥W => (Opp 3 Y).map (MulAut.conj (w : G)).toMonoidHom) 1
  simpa using h ⟨x, hx, rfl⟩

theorem r95_prod_of_lbar_le {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃)
    (hH : H ≠ ⊤) (h92 : R92 D) (hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) :
    H = (H ⊓ D.M) ⊔ I9 H := by
  have hHL : H = L9 Y H ⊔ (H ⊓ D.M) := (h92 Y H D₃ hyp hH).1
  have hYH : Y ≤ H := hyp.2.1.1
  have hXH : Opp 3 Y ≤ H := (r95_opp_le_self 3 Y).trans hYH
  have hLH : L9 Y H ≤ H := iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hXH hx)) (H.inv_mem h.2)
  have key : L9 Y H ≤ (H ⊓ D.M) ⊔ I9 H := by
    intro l hl
    have hlH : l ∈ H := hLH hl
    have hx : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ⟨l, hlH⟩ ∈ img9 H (L9 Y H) :=
      Subgroup.mem_map.2 ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.1 (hLM hx)
    have hm' : (m : G) ∈ H ⊓ D.M := Subgroup.mem_subgroupOf.1 hm
    obtain ⟨z, hz, hmz⟩ := (QuotientGroup.mk'_eq_mk' (CFSG.pPrimeCore 3 ↥H)).1 hmeq
    have hker : (m : G)⁻¹ * l ∈ I9 H := by
      refine Subgroup.mem_map.2 ⟨z, hz, ?_⟩
      have h := congrArg Subtype.val hmz
      simp only [Subgroup.coe_mul] at h
      rw [← h, inv_mul_cancel_left]
      rfl
    have hl' : l = (m : G) * ((m : G)⁻¹ * l) := (mul_inv_cancel_left (m : G) l).symm
    rw [hl']
    exact Subgroup.mul_mem_sup hm' hker
  have hle : H ≤ (H ⊓ D.M) ⊔ I9 H :=
    calc H = L9 Y H ⊔ (H ⊓ D.M) := hHL
      _ ≤ (H ⊓ D.M) ⊔ I9 H := sup_le key le_sup_left
  exact le_antisymm hle (sup_le inf_le_left (Subgroup.map_subtype_le _))

theorem r95_isSimple_lbar {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (h92 : R92 D) (hnot : ¬ IsPGroup 3 (Lbar9 Y H)) :
    IsSimpleGroup (Lbar9 Y H) := by
  have hshape := (h92 Y H D₃ hyp hH).2
  unfold Shape92 at hshape
  rcases hshape with ⟨-, h3⟩ | hJ | ⟨p, f, h⟩ | ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩
  · exact absurd h3 hnot
  · obtain ⟨e⟩ := hJ
    haveI : IsSimpleGroup CFSG.Open.walterJ1 := CFSG.Walter.J1Props.isSimpleGroup_walterJ1
    exact (e.trans CFSG.Walter.walterJ1EquivNative.symm).isSimpleGroup
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem r95_section_lbar {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    ∃ (E : Subgroup (Lbar9 Y H)) (π : E →* BarO3 (Opp 3 Y)), Function.Surjective π := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYH : Y ≤ H := hyp.2.1.1
  have hXH : Opp 3 Y ≤ H := (r95_opp_le_self 3 Y).trans hYH
  have hXL : Opp 3 Y ≤ L9 Y H := r95_opp_le_L9 Y H
  let φ : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let ι : ↥(Opp 3 Y) →* Lbar9 Y H :=
    (φ.comp (Subgroup.inclusion hXH)).codRestrict (img9 H (L9 Y H)) fun x =>
      Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x, Subgroup.mem_subgroupOf.2 (hXL x.2), rfl⟩
  have hker : ι.ker = (CFSG.pPrimeCore 3 ↥H).comap (Subgroup.inclusion hXH) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hx
      have hxval : φ (Subgroup.inclusion hXH x) = 1 := Subtype.ext_iff.mp hx
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hXH x)).mp hxval
    · intro hx
      have hxval : φ (Subgroup.inclusion hXH x) = 1 :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hXH x)).mpr hx
      apply Subtype.ext
      exact hxval
  have hle : ι.ker ≤ CFSG.pPrimeCore 3 ↥(Opp 3 Y) := by
    rw [hker]
    have hcop : Nat.Coprime 3
        (Nat.card ((CFSG.pPrimeCore 3 ↥H).comap (Subgroup.inclusion hXH))) :=
      (show Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥H)) from
        CFSG.pPrimeCore_coprime_card).coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hXH))
    exact le_sSup ⟨(inferInstance : (CFSG.pPrimeCore 3 ↥H).Normal).comap _, hcop⟩
  let g : ↥(Opp 3 Y) →* BarO3 (Opp 3 Y) := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y))
  have hle' : ι.rangeRestrict.ker ≤ g.ker := by
    rw [MonoidHom.ker_rangeRestrict, QuotientGroup.ker_mk']
    exact hle
  let π : ↥ι.range →* BarO3 (Opp 3 Y) :=
    ι.rangeRestrict.liftOfSurjective ι.rangeRestrict_surjective ⟨g, hle'⟩
  refine ⟨ι.range, π, ?_⟩
  have hπ : π.comp ι.rangeRestrict = g := by
    simp only [π]
    rw [MonoidHom.liftOfRightInverse_comp]
  exact Function.Surjective.of_comp (f := π) (g := ι.rangeRestrict) (by
    rw [← MonoidHom.coe_comp, hπ]
    exact QuotientGroup.mk'_surjective _)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
