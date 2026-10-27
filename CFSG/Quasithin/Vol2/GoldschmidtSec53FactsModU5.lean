module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem normalizer_hypProjUnitriangular_five :
    Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) = hypProjBorel h 2 1 :=
  normalizer_hypProjUnitriangular h (by norm_num) (by norm_num)

theorem u5PtP_ne_u5LnP : u5PtP h ≠ u5LnP h := by
  intro heq
  have h1 : rSU h ∈ u5LnStab h := N₁sub_le_u5LnStab rSU_mem_N₁sub
  have heq' : projIsoStabilizer h 2 1 (hypFlag h 2 1 1) =
      projIsoStabilizer h 2 1 (hypFlag h 2 1 2) := heq
  have h2 : rSU h ∈ u5PtStab h := by
    have h3 : rSU h ∈ (projIsoStabilizer h 2 1 (hypFlag h 2 1 1)).comap (hypProj h 2 1) := by
      rw [heq', comap_projIsoStabilizer]
      exact h1
    rwa [comap_projIsoStabilizer] at h3
  rw [mem_u5PtStab_iff] at h2
  have := h2 ιe₂ (by decide)
  have hσ : σr ιe₂ = ιe₁ := by decide
  rw [mat_rSU] at this
  simp [hσ] at this

theorem u5_yamStd : Yam.YamStd (hypPSU h 2 1) (hypProjUnitriangular h 2 1) (u5PtP h) (u5LnP h) := by
  have := finite_hypPSU_five h
  have hsimple := isSimpleGroup_hypPSU_five h
  have hno : ∀ R : Subgroup (hypPSU h 2 1), R.Normal → IsPGroup 2 ↥R → R = ⊥ := by
    intro R hR hRp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at hRp
      have hp : IsPGroup 2 (hypPSU h 2 1) := hRp.of_equiv Subgroup.topEquiv
      exact ((Subgroup.nontrivial_iff_ne_bot _).mp hp.center_nontrivial) (u5_center_eq_bot h)
  have hN := normalizer_hypProjUnitriangular_five (h := h)
  have hc1 : IsCoatom (u5PtP h) :=
    isCoatom_projIsoStabilizer_hypFlag h (by norm_num) le_rfl le_rfl (by norm_num)
  have hc2 : IsCoatom (u5LnP h) :=
    isCoatom_projIsoStabilizer_hypFlag h (by norm_num) le_rfl (by norm_num) le_rfl
  refine ⟨u5_sylow h, hno, u5PtP_ne_u5LnP, hN ▸ hypProjBorel_le_projIsoStabilizer h le_rfl
      (by norm_num), hN ▸ hypProjBorel_le_projIsoStabilizer h (by norm_num) le_rfl, hc1, hc2,
    ?_, isTwoLocal_of_le_normalizer hc1 hno (map_ZPsub_ne_bot (h := h)) isPGroup_map_ZPsub
      u5PtP_le_normalizer, isTwoLocal_of_le_normalizer hc2 hno (map_Vsub_ne_bot (h := h))
      isPGroup_map_Vsub u5LnP_le_normalizer⟩
  intro A hNA hAt
  obtain ⟨A', hA', hAA'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hAt
  rw [hN] at hNA
  obtain ⟨d, hd1, hd2, rfl⟩ := eq_projIsoStabilizer_of_isCoatom h (by norm_num) le_rfl hA'
    (hNA.trans hAA')
  interval_cases d
  · exact Or.inl hAA'
  · exact Or.inr hAA'

theorem u5_lieFactsOf (hf : 2 ≤ f) :
    Yam.LieFactsOf (hypProjUnitriangular h 2 1) (u5PtP h) (u5LnP h) := by
  have hN := normalizer_hypProjUnitriangular_five (h := h)
  refine ⟨⟨?_, fun a ha a' ha' h1 h1' => trans_u5PtP hf ha ha' h1 h1', fun a ha _ _ h1 _ => ?_⟩,
    ?_, U_le_perfectCore_u5PtP hf, U_le_perfectCore_u5LnP hf⟩
  · rw [u5PtP_inf_u5LnP, ← hN]
    exact (borelBase_u5 h).isSolvable_B
  · rw [centerOf_u5LnP_eq_bot hf, Subgroup.mem_bot] at ha
    exact absurd ha h1
  · rw [u5PtP_inf_u5LnP, hN]

end CFSG.Quasithin.H13.Sec53F.Unit

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem lieModelFacts_u5 : LieModelFacts .PSU 5 :=
  Yam.lieModelFacts_of_std fun Y _ f hpar hY => by
    rcases hY with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hc
      have hm : 1 ≤ f := hadm.2.1
      have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
      obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
      let e' : hypPSU h 2 1 ≃* Y := (hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm
      exact ⟨_, inferInstance, Unit.finite_hypPSU_five h, _, _, _, Unit.u5_yamStd,
        Unit.u5_lieFactsOf hpar.1, ⟨e'.symm⟩⟩
    all_goals exact absurd hn (by norm_num)

end CFSG.Quasithin.H13.Sec53F
