module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

theorem img9_L9_normal {Y H : Subgroup G} (hYH : Y ≤ H) : (img9 H (L9 Y H)).Normal := by
  have hXH : Opp 3 Y ≤ H := (opp_le_self 3 Y).trans hYH
  have hLH : L9 Y H ≤ H := iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hXH hx)) (H.inv_mem h.2)
  have key : ∀ g : ↥H, (L9 Y H).map (MulAut.conj (g : G)).toMonoidHom ≤ L9 Y H := by
    intro g
    unfold L9
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_map]
    have e : (MulAut.conj (g : G)).toMonoidHom.comp (MulAut.conj (h : G)).toMonoidHom =
        (MulAut.conj ((g * h : ↥H) : G)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact le_iSup (fun h : ↥H => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) (g * h)
  have hHL : H ≤ normalizer (L9 Y H : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact key ⟨g, hg⟩ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    · intro hx
      have := key ⟨g⁻¹, H.inv_mem hg⟩ (Subgroup.mem_map.2 ⟨g * x * g⁻¹, hx, rfl⟩)
      simpa [MulAut.conj_apply, mul_assoc] using this
  haveI : ((L9 Y H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem pPrimeCore_Lbar9 {Y H : Subgroup G} (hYH : Y ≤ H) :
    CFSG.pPrimeCore 3 (Lbar9 Y H) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := img9_L9_normal hYH
  have h0 : CFSG.pPrimeCore 3 (Hbar9 H) = ⊥ := pPrimeCore_barO3 H
  have hle : (CFSG.pPrimeCore 3 (Lbar9 Y H)).map (img9 H (L9 Y H)).subtype ≤
      CFSG.pPrimeCore 3 (Hbar9 H) :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, by
      rw [Subgroup.card_map_of_injective (img9 H (L9 Y H)).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card⟩
  rw [h0, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (img9 H (L9 Y H)).subtype_injective).mp hle

theorem not_hasE9_Lbar9 {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    ¬ HasE9 (Lbar9 Y H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have hXH : Opp 3 Y ≤ H := (opp_le_self 3 Y).trans hyp.2.1.1
  have hLH : L9 Y H ≤ H := iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hXH hx)) (H.inv_mem h.2)
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let φ := π.subgroupMap ((L9 Y H).subgroupOf H)
  have hφ : Function.Surjective φ := π.subgroupMap_surjective _
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map ((L9 Y H).subgroupOf H).subtype ≤ CFSG.pPrimeCore 3 ↥H := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : π x = 1 := congrArg Subtype.val (φ.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp hx1
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective ((L9 Y H).subgroupOf H).subtype_injective] at hdvd
    exact fun h3 => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      CFSG.pPrimeCore_coprime_card (h3.trans hdvd)
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have h1 : HasE9 (↥((L9 Y H).subgroupOf H) ⧸ φ.ker) :=
    h.map_injective e.symm.toMonoidHom e.symm.injective
  have h2 := CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient φ.ker hker h1
  exact not_hasE9_L9 hyp (h2.map_injective (Subgroup.subgroupOfEquivOfLe hLH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hLH).injective)

theorem closure_threeElements_L9 (Y H : Subgroup G) :
    closure {x : ↥(L9 Y H) | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤ := by
  set C := closure {x : ↥(L9 Y H) | ∃ k : ℕ, orderOf x = 3 ^ k}
  have hL : L9 Y H ≤ C.map (L9 Y H).subtype := by
    refine iSup_le fun h => ?_
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    have hyL : (MulAut.conj (h : G)).toMonoidHom y ∈ L9 Y H := by
      refine (le_iSup (fun k : ↥H => (Opp 3 Y).map (MulAut.conj (k : G)).toMonoidHom) h) ?_
      refine Subgroup.mem_map_of_mem _ ?_
      unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      exact Subgroup.subset_closure ⟨hyY, k, hk⟩
    refine ⟨⟨_, hyL⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
    rw [← Subgroup.orderOf_coe]
    change orderOf ((MulAut.conj (h : G)) y) = 3 ^ k
    rw [MulEquiv.orderOf_eq, hk]
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨c, hc, hcx⟩ := hL hx
  rwa [show c = ⟨x, hx⟩ from Subtype.ext hcx] at hc

theorem closure_threeElements_Lbar9 {Y H : Subgroup G} (hYH : Y ≤ H) :
    closure {x : Lbar9 Y H | ∃ k : ℕ, orderOf x = 3 ^ k} = ⊤ := by
  have hXH : Opp 3 Y ≤ H := (opp_le_self 3 Y).trans hYH
  have hLH : L9 Y H ≤ H := iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hXH hx)) (H.inv_mem h.2)
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let φ := (π.subgroupMap ((L9 Y H).subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hLH).symm.toMonoidHom
  have hφ : Function.Surjective φ :=
    (π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hLH).symm.surjective
  exact closure_threeElements_of_surjective φ hφ (closure_threeElements_L9 Y H)

theorem shape92_of_hyp91 (hK32 : UCK.K32) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) :
    Shape92 (Lbar9 Y H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : CFSG.Open.IsKGroup (Lbar9 Y H) := CFSG.Open.IsKGroup.subgroup
    ((CFSG.Open.IsKProper.isKGroup D.standing.kProper H hH).quotient _) _
  have hE9 := not_hasE9_Lbar9 hyp
  have hO := pPrimeCore_Lbar9 hyp.2.1.1
  unfold Shape92
  by_cases hnp : IsPGroup 3 (Lbar9 Y H)
  · left
    refine ⟨?_, hnp⟩
    haveI := CFSG.GroupTheory.ThreeTranspositions.isCyclic_of_isPGroup_three hE9
      (P := ⊤) (hnp.to_subgroup ⊤)
    exact isCyclic_of_surjective (Subgroup.topEquiv : ↥(⊤ : Subgroup (Lbar9 Y H)) ≃* _)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (Lbar9 Y H)) ≃* _).surjective
  · obtain ⟨hS, hnab⟩ :=
      isSimpleGroup_of_not_hasE9 hSch hK hE9 hO (closure_threeElements_Lbar9 hyp.2.1.1) hnp
    have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (Lbar9 Y H)) = 1 := by
      refine le_antisymm (pRank_three_le_one_of_not_hasE9 hE9) ?_
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card_of_not_isPGroup hO hnp)
      have hx3 : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
      exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := zpowers x) (by norm_num) le_top
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hx3) (k := 1) (by rw [hx3, pow_one])
    rcases hK32 (Lbar9 Y H) hK hS hnab hrank with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl h)

theorem r92_of_inputs (hK32 : UCK.K32) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (D : Data G) : R92 D :=
  fun _ _ _ hyp hH => ⟨eq_L9_sup_of_hyp91 hyp, shape92_of_hyp91 hK32 hSch hyp hH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
