module

public import CFSG.Quasithin.EmptyFaithful.E111RFacts
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837E
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.Quasithin.EmptyFaithful.E111RMain
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Ch8310Aut

theorem nParam_sup_le_two_of_psl24 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) (hY : IsPSL 2 2 2 Y) {B : Subgroup (MulAut Y)}
    (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : Y →* MulAut Y).range)
      (MulAut.conj : Y →* MulAut Y).range) :
    E1.nParam ((MulAut.conj : Y →* MulAut Y).range ⊔ B) ≤ 2 := by
  set I := (MulAut.conj : Y →* MulAut Y).range with hI
  set Z := I ⊔ B with hZdef
  set e := Vol2.Ch11.SecB.generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFY : IsPSL 2 2 2 (ASInputs.FStar ↥Z) :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hY
  have key : E1.nParam (⊤ : Subgroup ↥Z) = 2 := by
    simpa using Vol2.Ch11.SecE3.nParam_eq_of_isPSL22 (T := B.subgroupOf Z) hFY hFs
      (Vol2.Ch11.SecB.isSylowTwo_sup hB hBI) (Vol2.Ch11.SecB.generalizedFitting_sup_sup hnab B)
  rw [E1.nParam_subgroupOf, key]

end Ch8310Aut

open Ch8310 in
theorem claim8310N_of' (h37 : Vol2Native.A37ForSQTKCat) :
    Claim8310N := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV hK1 _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  obtain ⟨K, s, hsT, hsN, hKC, hKz, F, _, _, hF, ⟨eF⟩⟩ := hK1
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hsGz : s ∈ Subgroup.centralizer ({z} : Set G) := hTz hsT
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    conjClosure_le fun h hh x hx =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    Ch837.zpowers_le_pCoreOf hz2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl) le_rfl
  have hPGz : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)) := mem_cComp_iff.mpr hKC
  set K' := CFSG.conjugate K s with hK'def
  have hK'eq : conjByElt s⁻¹ K = K' := by
    rw [hK'def, Ch837.conjByElt_eq_conjugate, inv_inv]
  have hK'c : K' ∈ cComp (Subgroup.centralizer ({z} : Set G)) :=
    conjSub_mem_cComp_of_mem hKc (Subgroup.inv_mem _ hsGz)
  have hne : K ≠ K' := fun h => hsN (by
    have h1 : conjByElt s⁻¹ K = K := hK'eq.trans h.symm
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem (A38.map_conj_eq_iff.mp h1))
  have hcommKK' := (Vol2Native.lemma_1_2_1_two hKl h37 hPGz hKc hK'c hne).1
  have hK'NK : K' ≤ Subgroup.normalizer (K : Set G) := Ch837.le_normalizer_of_commutator_le
    (hcommKK'.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)))
  have hKNK' : K ≤ Subgroup.normalizer (K' : Set G) := Ch837.le_normalizer_of_commutator_le
    (by
      rw [Subgroup.commutator_comm]
      exact hcommKK'.trans (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K')))
  have hKKz : K ≤ ch83Kz T L z := by rw [hKz]; exact le_sup_left
  have hK'Kz : K' ≤ ch83Kz T L z := by rw [hKz]; exact le_sup_right
  have hKzNK : ch83Kz T L z ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKz]; exact sup_le Subgroup.le_normalizer hK'NK
  have hKzNK' : ch83Kz T L z ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hKz]; exact sup_le hKNK' Subgroup.le_normalizer
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eA⟩ := Ch8310.a5_of_sl24 hF
  have eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5) := eF.trans eA
  obtain ⟨eKK'⟩ := Ch837.nonempty_quot_conjugate_equiv K s
  have eK' : ↥K' ⧸ CFSG.pCore 2 ↥K' ≃* alternatingGroup (Fin 5) := eKK'.symm.trans eK
  have hPSLA : IsPSL 2 2 2 (alternatingGroup (Fin 5)) := by
    obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inl hF)
    exact ⟨⟨Nat.prime_two, by norm_num, by decide⟩, F, inferInstance, inferInstance,
      by rw [hF]; norm_num, ⟨e₅.symm⟩⟩
  have hST : ch83S T L z ≤ T :=
    pCoreOf_le_of_isSylowIn ⟨le_sup_right, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hS2 : IsPGroup 2 (ch83S T L z) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  set Y := ch83Kz T L z ⊔ ch83S T L z with hYdef
  have hKzY : ch83Kz T L z ≤ Y := le_sup_left
  have hYGz : Y ≤ Subgroup.centralizer ({z} : Set G) := sup_le hKzGz (hST.trans hTz)
  have hYN : Y ≤ Subgroup.normalizer (ch83Kz T L z : Set G) := hYGz.trans hGzKz
  set O := pCoreOf 2 (ch83Kz T L z) with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOY : O ≤ Y := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKzY
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  set Nb : Subgroup ↥Y := O.subgroupOf Y with hNbdef
  have hNb : Nb.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYO
  set π : ↥Y →* ↥Y ⧸ Nb := QuotientGroup.mk' Nb with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Nb
  set P : Vol2.Ch11.SecB.GrpPred := fun (Q : Type) [Group Q] =>
    Nonempty (Q ≃* alternatingGroup (Fin 5)) with hPdef
  have hP : Vol2.Ch11.SecB.IsoInv P := by
    intro A B _ _ e h
    obtain ⟨e'⟩ := h
    exact ⟨e.trans e'⟩
  have hcomp : ∀ J : Subgroup G, J ∈ cComp (Subgroup.centralizer ({z} : Set G)) →
      J ≤ ch83Kz T L z → ch83Kz T L z ≤ Subgroup.normalizer (J : Set G) →
      (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
      IsSimpleGroup ↥((J.subgroupOf Y).map π) ∧
        (∃ a b : ↥((J.subgroupOf Y).map π), a * b ≠ b * a) ∧
        ((J.subgroupOf Y).map π).IsSubnormal ∧ P ↥((J.subgroupOf Y).map π) := by
    intro J hJc hJKz hKzJ eJ
    have hJY : J ≤ Y := hJKz.trans hKzY
    set ψ : ↥J →* ↥Y ⧸ Nb := π.comp (Subgroup.inclusion hJY) with hψ
    have hrange : ψ.range = (J.subgroupOf Y).map π := by
      rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    have hker : ψ.ker = CFSG.pCore 2 ↥J := by
      rw [← Vol2.Ch10.SecA.subgroupOf_pCoreOf,
        ← Vol2.Ch10.SecA.inf_pCoreOf_eq_of_normal hJKz hKzJ]
      ext j
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hNbdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    have e1 : ↥J ⧸ CFSG.pCore 2 ↥J ≃* ↥((J.subgroupOf Y).map π) :=
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hrange)
    have e2 : ↥((J.subgroupOf Y).map π) ≃* alternatingGroup (Fin 5) := e1.symm.trans eJ
    have hab : ∃ a b : ↥((J.subgroupOf Y).map π), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := Vol2Native.A312L.Seven.alt5_nonabelian
      refine ⟨e2.symm a, e2.symm b, fun h => hab ?_⟩
      simpa using congrArg e2 h
    refine ⟨e2.isSimpleGroup, hab, ?_, ⟨e2⟩⟩
    have h1 := A4.subnormal_comap Y.subtype hJc.2.2.1
    have h2 : (Subgroup.centralizer ({z} : Set G)).comap Y.subtype = ⊤ :=
      Subgroup.subgroupOf_eq_top.mpr hYGz
    rw [h2] at h1
    exact (Vol2.Ch11.SecB.isSubnormal_of_open h1 Subgroup.IsSubnormal.top).map hπs
  have hpowY : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ ch83Kz T L z :=
    B6.isTwoQuotient_of_sup_eq hS2 hYN (sup_comm _ _)
  have hsecQ : Vol2.Ch11.SecB.SecAll (↥Y ⧸ Nb) P := by
    refine Vol2.Ch11.SecB.secAll_of_components hP
      {(K.subgroupOf Y).map π, (K'.subgroupOf Y).map π} ?_ ?_
    · rintro J (rfl | rfl)
      · exact hcomp K hKc hKKz hKzNK eK
      · exact hcomp K' hK'c hK'Kz hKzNK' eK'
    · intro g
      obtain ⟨y, rfl⟩ := hπs g
      obtain ⟨k, hk⟩ := hpowY y y.2
      refine ⟨k, ?_⟩
      rw [sSup_pair, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup (hKKz.trans hKzY)
        (hK'Kz.trans hKzY), ← hKz, ← map_pow]
      exact ⟨y ^ 2 ^ k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hkerπ : Group.IsSolvable ↥π.ker := by
    have h2 : IsPGroup 2 ↥π.ker := by
      rw [hπdef, QuotientGroup.ker_mk', hNbdef]
      exact hO2.comap_subtype
    have : Group.IsNilpotent ↥π.ker := h2.isNilpotent
    infer_instance
  have hsecY : Vol2.Ch11.SecB.SecAll ↥Y P :=
    Vol2.Ch11.SecB.secAll_of_surjective hP π hπs hkerπ hsecQ

  have hE : ASInputs.E111Hyp ↥Y 2 := by
    intro H₁ K₁ _ _ hsn hsimple hnab B hB hBI
    have hsn' : H₁.IsSubnormal := Vol2.Ch11.SecB.isSubnormal_of_open hsn Subgroup.IsSubnormal.top
    obtain ⟨e⟩ := hsecY H₁ (K₁.subgroupOf H₁) hsn' hsimple hnab
    exact Ch8310Aut.nParam_sup_le_two_of_psl24 hnab
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hPSLA) hB hBI
  have hsecA : Vol2.Ch11.SecB.SecAll ↥Y (E2.E22N.AutRankLe 2) := by
    intro H₁ N _ hsn hs hnab
    obtain ⟨e⟩ := hsecY H₁ N hsn hs hnab
    exact E2.E22N.autRankLe_of_isPSL22 hnab
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hPSLA)
  have := E2.E22N.e111ForQn_autRankLe (n := 2) (by norm_num) ↥Y hE hsecA
  rw [E1.nParam_subgroupOf]
  simpa using this

end CFSG.Quasithin.H13
