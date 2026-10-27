module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Sp6P
import CFSG.RankThree.PartTwo.Sec21.HeringFFLE27
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)

theorem c8_exists_noncyclic_three_sp6 :
    ∃ E : Subgroup ↥(StatedSp 3 (ZMod 2)), IsPGroup 3 E ∧ ¬ IsCyclic E := by
  obtain ⟨E, hE, hE27⟩ := CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.exists_e27_H6
  refine ⟨E, fun g => ⟨1, Subtype.ext ?_⟩, fun hc => ?_⟩
  · simpa using hE.2 g.1 g.2
  · obtain ⟨g, hg⟩ := hc.exists_ofOrder_eq_natCard
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 g.1 g.2)
    have h3 : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hg3
    rw [hg, hE27] at h3
    exact absurd h3 (by norm_num)

variable {G : Type} [Group G] [Finite G]

theorem c8_exists_noncyclic_le_of_le_barSub {p : ℕ} [Fact p.Prime] {V₀ V X : Subgroup G}
    {hV : IsElemAbelian 2 V} {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : E ≤ barSub V₀ V hV X)
    (hEp : IsPGroup p E) (hEc : ¬ IsCyclic E) :
    ∃ Y : Subgroup G, Y ≤ X ∧ IsPGroup p Y ∧ ¬ IsCyclic Y := by
  by_contra h
  push Not at h
  have hB : ∀ A : Subgroup ↥(stabTil V₀ V),
      A ≤ X.subgroupOf (stabTil V₀ V) → IsPGroup p A → IsCyclic A := by
    intro A hAX hAp
    have hmapX : A.map (stabTil V₀ V).subtype ≤ X := by
      rintro x ⟨a, ha, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hAX ha)
    have hcyc : IsCyclic (A.map (stabTil V₀ V).subtype) := h _ hmapX (hAp.map _)
    exact (Subgroup.equivMapOfInjective A (stabTil V₀ V).subtype
      (stabTil V₀ V).subtype_injective).isCyclic.mpr hcyc
  exact hEc (CFSG.AGLEmbedding.isCyclic_of_le_map (actTil V₀ V hV) hB hE hEp)

private theorem c8_isTwoLocal_normalizer_pCoreOf {H : Subgroup G} (h : pCoreOf 2 H ≠ ⊥) :
    IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) ∧ H ≤ normalizer (pCoreOf 2 H : Set G) := by
  refine ⟨⟨pCoreOf 2 H, h, (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype, rfl⟩, ?_⟩
  have hN : ((pCoreOf 2 H).subgroupOf H).Normal := by
    have : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    exact CFSG.pCore_normal (p := 2) (G := ↥H)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hN

theorem c8_le_of_noncyclic_three (D : Data G) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    {K X : Subgroup G} (hK : CFSG.QuasithinUnique.CharTwo K) (hXK : X ≤ K ⊓ D.M)
    (hXp : IsPGroup 3 X) (hXc : ¬ IsCyclic X) : K ≤ D.M := by
  by_cases hO : pCoreOf 2 K = ⊥
  · have hcent : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro x hx
      rw [Subgroup.mem_bot.mp hx]
      exact Subgroup.one_mem _
    have hKbot : K = ⊥ := by
      have hK' : K ⊓ centralizer ((⊥ : Subgroup G) : Set G) ≤ ⊥ := by
        simpa [CFSG.QuasithinUnique.CharTwo, hO] using hK
      rw [hcent, inf_top_eq] at hK'
      exact le_bot_iff.mp hK'
    rw [hKbot]
    exact bot_le
  · obtain ⟨hN, hKN⟩ := c8_isTwoLocal_normalizer_pCoreOf hO
    exact hKN.trans (le_of_noncyclic_of_isTwoLocal D h61 h3
      (hXK.trans inf_le_right) hXp hXc hN ((hXK.trans inf_le_left).trans hKN))

theorem c8_barSub_inf_eq (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (h8 : Case167_8 D V₀ V hV L)
    (hM : Mbar D.M V₀ V hV = lBar V₀ V hV L) {v₀ : IntMod V hV} {T₀ K : Subgroup G}
    (hK : Sp6InL D L v₀.val T₀ K) (ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)))
    (hψ : ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) =
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (hLift : barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)) :
    barSub V₀ V hV (K ⊓ D.M) = ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) := by
  have hM' : barSub V₀ V hV D.M = lBar V₀ V hV L := hM
  have hB_le : barSub V₀ V hV (K ⊓ D.M) ≤ lBar V₀ V hV L := by
    have h1 : barSub V₀ V hV (K ⊓ D.M) ≤ barSub V₀ V hV D.M :=
      barSub_mono V₀ V hV inf_le_right
    rwa [hM'] at h1
  have hP_le_B : ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) ≤
      barSub V₀ V hV (K ⊓ D.M) := by
    have hle : L ⊓ centralizer ({v₀.val} : Set G) ≤ K ⊓ D.M :=
      le_inf hK.2.1 (inf_le_left.trans hS.setting.hyp151.le)
    have h1 : barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) ≤
        barSub V₀ V hV (K ⊓ D.M) := barSub_mono V₀ V hV hle
    rwa [hLift] at h1
  set A : Subgroup ↥(StatedSp 3 (ZMod 2)) :=
    (barSub V₀ V hV (K ⊓ D.M)).subgroupOf (lBar V₀ V hV L) |>.map ψ.toMonoidHom
    with hA_def
  have hB_eq : barSub V₀ V hV (K ⊓ D.M) = pullSub ψ A := by
    rw [hA_def]
    exact eq_pullSub_of_le ψ hB_le
  have hP0_le_A : stabilizer 3 (ZMod 2) (lagrangianZero 3) ≤ A := by
    intro s hs
    have hb_pull : ((ψ.symm s : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) ∈
        pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) :=
      mem_pullSub.mpr ⟨(ψ.symm s).2, by simpa using hs⟩
    have hb_P : ((ψ.symm s : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) ∈
        ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) := by
      rwa [← hψ] at hb_pull
    have hb_B : ((ψ.symm s : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) ∈
        barSub V₀ V hV (K ⊓ D.M) := hP_le_B hb_P
    rw [hA_def]
    exact Subgroup.mem_map.mpr ⟨ψ.symm s, Subgroup.mem_subgroupOf.mpr hb_B,
      MulEquiv.apply_symm_apply ψ s⟩
  rcases c8_stabilizer_lagrangianZero_maximal hP0_le_A with hAeq | hAtop
  · rw [hB_eq, hAeq]
    exact hψ.symm
  · exfalso
    obtain ⟨E, hEp, hEc⟩ := c8_exists_noncyclic_three_sp6
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let f : ↥(StatedSp 3 (ZMod 2)) →* MulAut (Vtil V₀ V hV) :=
      (lBar V₀ V hV L).subtype.comp ψ.symm.toMonoidHom
    have hf : Function.Injective f :=
      (lBar V₀ V hV L).subtype_injective.comp ψ.symm.injective
    have hE'_p : IsPGroup 3 (pullSub ψ E) := by
      rw [pullSub_eq_map]
      exact hEp.map f
    have hE'_c : ¬ IsCyclic (pullSub ψ E) := by
      intro hc
      rw [pullSub_eq_map] at hc
      exact hEc ((Subgroup.equivMapOfInjective E f hf).isCyclic.mpr hc)
    have hE'_le : pullSub ψ E ≤ barSub V₀ V hV (K ⊓ D.M) := by
      rw [hB_eq, hAtop]
      exact pullSub_mono ψ le_top
    obtain ⟨Y, hYX, hYp, hYc⟩ := c8_exists_noncyclic_le_of_le_barSub hE'_le hE'_p hE'_c
    have h3 : 3 ∈ D.sig := by rw [h8.2.2.1]; exact Set.mem_singleton 3
    exact hK.2.2.1 (c8_le_of_noncyclic_three D h61 h3 hK.2.2.2 hYX hYp hYc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
