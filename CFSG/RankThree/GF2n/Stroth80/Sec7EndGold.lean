module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCList
public import CFSG.ClassicalInvolution.AschTight.StronglyClosed
public import CFSG.LargeExtraspecial.S111SHCor3
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
open scoped commutatorElement

section GoldFacts



theorem endg_gold_facts {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (h : goldschmidtSimpleType L) :
    OutCyc L ∧ ((∀ w : L, orderOf w = 2 → Group.IsSolvable ↥(Subgroup.centralizer ({w} : Set L))) ∨
      ∀ T : Sylow 2 L, Nat.card (T : Subgroup L) ≤ 8) := by
  refine ⟨outCyc_of_goldschmidtSimpleType h, ?_⟩
  have hbender : fusionIsBenderGroup L →
      ∀ w : L, orderOf w = 2 → Group.IsSolvable ↥(Subgroup.centralizer ({w} : Set L)) :=
    fun hb w hw =>
    CFSG.ClassicalInvolution.Disconnected.AschTight.isSolvable_centralizer_of_isBenderGroup
      (CFSG.ClassicalInvolution.Disconnected.AschTight.isBenderGroup_of_fusionIsBenderGroup' hb) hw
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  · exact Or.inl (hbender (Or.inl ⟨f, by omega, ⟨e⟩⟩))
  · exact Or.inl (hbender (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)))
  · exact Or.inl (hbender (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)))
  · haveI := hp
    refine Or.inr fun T => ?_
    have := (CFSG.Goldschmidt.GoldType.sylow_of_psl2_odd hpo hf h8 e T).1
    omega
  · refine Or.inr fun T => ?_
    have := (CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := L) (Or.inl ⟨m, hm, hcard⟩) T).2.1
    omega
  · refine Or.inr fun T => ?_
    have := (CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := L) (Or.inr ⟨e⟩) T).2.1
    omega

end GoldFacts

section GoldDecomp

theorem endg_goldschmidtSimpleType_congr {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L') : goldschmidtSimpleType L := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨p, f, hp, hpo, hf, h5, h8, ⟨e'⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hpo, hf, h5, h8, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, by rw [Nat.card_congr e.toEquiv]; exact hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))



variable {X : Type} [Group X] [Finite X]

theorem endg_isComponent_map_subtype {U : Subgroup X} (hU : U.Normal) {K : Subgroup ↥U}
    (hK : IsComponent K) : IsComponent (K.map U.subtype) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective U.subtype U.subtype_injective) hK.1, ?_⟩
  refine Subgroup.IsSubnormal.trans (K := U) ?_ ?_ hU.isSubnormal
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have : (K.map U.subtype).subgroupOf U = K :=
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective K
    rw [this]
    exact hK.2

theorem endg_gold_decomp (T : Sylow 2 X) {z : X} (hzT : z ∈ (T : Subgroup X))
    (hzc : ∀ x ∈ (T : Subgroup X), x * z = z * x)
    (hab : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl z))
    (hO : goldschmidtOddCore ↥(Subgroup.normalClosure ({z} : Set X)) = ⊥)
    (hO2 : pCore 2 ↥(Subgroup.normalClosure ({z} : Set X)) = ⊥) :
    Subgroup.normalClosure ({z} : Set X) = ⨆ (K : Subgroup X)
        (_ : IsComponent K ∧ K ≤ Subgroup.normalClosure ({z} : Set X)), K ∧
      ∀ K : Subgroup X, IsComponent K → K ≤ Subgroup.normalClosure ({z} : Set X) →
        goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K) := by
  classical
  set U : Subgroup X := Subgroup.normalClosure ({z} : Set X) with hU
  haveI hUn : U.Normal := Subgroup.normalClosure_normal
  obtain ⟨hWT, hcl⟩ := CFSG.LargeExtraspecial.S11.wcl_stronglyClosed T hzT hzc hab
  set W := CFSG.LargeExtraspecial.S11.wcl z with hW
  have hzU : z ∈ U := Subgroup.subset_normalClosure (Set.mem_singleton z)
  have hWU : W ≤ U := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨m, rfl, -⟩
    exact hUn.conj_mem z hzU m
  have hMU : U = Subgroup.normalClosure (W : Set X) := by
    apply le_antisymm
    · exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr
        (CFSG.LargeExtraspecial.S11.self_mem_wcl z))
    · exact Subgroup.normalClosure_le_normal hWU
  have key : ∀ M : Subgroup X, M = Subgroup.normalClosure (W : Set X) →
      (pCore 2 (↥M ⧸ goldschmidtOddCore ↥M) ⊔ goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊤ ∧
        ∀ K : Subgroup (↥M ⧸ goldschmidtOddCore ↥M), IsComponentOf K ⊤ →
          goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K)) := by
    intro M hM
    subst hM
    have h := CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian X T W hWT hab hcl
    exact ⟨h.1, h.2.2⟩
  obtain ⟨hlayer, hsimple⟩ := key U hMU
  have hinj : Function.Injective (QuotientGroup.mk' (goldschmidtOddCore ↥U)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  let e : ↥U ≃* (↥U ⧸ goldschmidtOddCore ↥U) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (goldschmidtOddCore ↥U))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have hpQ : pCore 2 (↥U ⧸ goldschmidtOddCore ↥U) = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 e, hO2, Subgroup.map_bot]
  rw [hpQ, bot_sup_eq] at hlayer
  rw [goldschmidtLayer.eq_sSup] at hlayer
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  ·
    intro u hu
    have hq : e ⟨u, hu⟩ ∈ sSup {K : Subgroup (↥U ⧸ goldschmidtOddCore ↥U) | IsComponentOf K ⊤} := by
      rw [hlayer]; exact Subgroup.mem_top _
    have hle : sSup {K : Subgroup (↥U ⧸ goldschmidtOddCore ↥U) | IsComponentOf K ⊤} ≤
        (⨆ (K : Subgroup X) (_ : IsComponent K ∧ K ≤ U), K).comap
          (U.subtype.comp e.symm.toMonoidHom) := by
      refine sSup_le fun K hK => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have hK' : IsComponent K := (CFSG.isComponent_iff_open K).mpr hK
      have h1 : IsComponent (K.map e.symm.toMonoidHom) :=
        CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK'
      have h2 : IsComponent ((K.map e.symm.toMonoidHom).map U.subtype) :=
        endg_isComponent_map_subtype hUn h1
      have h3 : (K.map e.symm.toMonoidHom).map U.subtype ≤ U := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      refine le_iSup₂_of_le ((K.map e.symm.toMonoidHom).map U.subtype) ⟨h2, h3⟩ ?_
      rw [Subgroup.map_map]
    have := hle hq
    rw [Subgroup.mem_comap] at this
    simpa using this
  · exact iSup₂_le fun K hK => hK.2
  · intro K hK hKU
    have h1 : IsComponent (K.subgroupOf U) := CFSG.LocalCores.component_overgroup hK hKU
    have h2 : IsComponent ((K.subgroupOf U).map e.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv e h1
    have h3 := hsimple _ ((CFSG.isComponent_iff_open _).mp h2)
    let ε : ↥((K.subgroupOf U).map e.toMonoidHom) ≃* ↥K :=
      ((K.subgroupOf U).equivMapOfInjective e.toMonoidHom e.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hKU)
    have hcen : (Subgroup.center ↥((K.subgroupOf U).map e.toMonoidHom)).map ε.toMonoidHom =
        Subgroup.center ↥K := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ε
    exact endg_goldschmidtSimpleType_congr
      (QuotientGroup.congr (Subgroup.center ↥((K.subgroupOf U).map e.toMonoidHom))
        (Subgroup.center ↥K) ε hcen).symm h3

end GoldDecomp

end CFSG.RankThree.GF2n.Stroth80
