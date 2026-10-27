module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_isElemAbelian_comm {X : Type} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : IsMulCommutative X := by
  obtain ⟨e⟩ := h
  refine IsMulCommutative.of_comm fun a b => ?_
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

private theorem s16c167_not_comm_of_case2 (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hC : Counterex16 D ⊥ V L hV) (h2 : Case168_2 D ⊥ V hV L) :
    ¬ IsMulCommutative ↥(lBar ⊥ V hV L) := by
  rintro hcomm
  haveI := hcomm
  obtain ⟨e⟩ := h2.1
  have hcenter : ∀ σ : Equiv.Perm (Fin 3), (∀ τ, σ * τ = τ * σ) → σ = 1 := by decide
  have hLM : L ≤ D.M := hC.setting.hyp151.le
  have hle : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hLM
  have htriv : ∀ a : ↥(lBar ⊥ V hV L), (a : MulAut (Vtil ⊥ V hV)) = 1 := by
    intro a
    have haM : (a : MulAut (Vtil ⊥ V hV)) ∈ Mbar D.M ⊥ V hV := hle a.2
    have haC : (a : MulAut (Vtil ⊥ V hV)) ∈
        Subgroup.centralizer ((lBar ⊥ V hV L : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg (fun x : ↥(lBar ⊥ V hV L) => (x : MulAut (Vtil ⊥ V hV)))
        (mul_comm' ⟨b, hb⟩ a)
    have hak : (a : MulAut (Vtil ⊥ V hV)) ∈ kBar D.M ⊥ V hV L :=
      Subgroup.mem_inf.2 ⟨haM, haC⟩
    have hctr : ∀ τ : Equiv.Perm (Fin 3), e ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ * τ =
        τ * e ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ := by
      intro τ
      obtain ⟨k, hk⟩ := e.surjective τ
      rw [← hk]
      have hAK : (⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ : ↥(kBar D.M ⊥ V hV L)) * k =
          k * ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ := by
        apply Subtype.ext
        have hkC : (k : MulAut (Vtil ⊥ V hV)) ∈
            Subgroup.centralizer ((lBar ⊥ V hV L : Subgroup _) : Set _) :=
          (Subgroup.mem_inf.1 k.2).2
        exact (Subgroup.mem_centralizer_iff.1 hkC) (a : MulAut (Vtil ⊥ V hV)) a.2
      calc e ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ * e k =
            e (⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ * k) := (map_mul e _ _).symm
        _ = e (k * ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩) := by rw [hAK]
        _ = e k * e ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ := map_mul e _ _
    have hea1 : e ⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ = 1 := hcenter _ hctr
    have hsub : (⟨(a : MulAut (Vtil ⊥ V hV)), hak⟩ : ↥(kBar D.M ⊥ V hV L)) = 1 :=
      e.injective (by rw [hea1, map_one])
    exact congrArg (fun x : ↥(kBar D.M ⊥ V hV L) => (x : MulAut (Vtil ⊥ V hV))) hsub
  apply hC.ne_bot
  rw [← le_bot_iff]
  intro a ha
  exact Subgroup.mem_bot.2 (htriv ⟨a, ha⟩)

theorem s16c167_twenty_two_small (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) (h13 : Concl1613_2 D ⊥ V hV L)
    (h2 : Case168_2 D ⊥ V hV L) : Case168_2Small D ⊥ V hV L := by
  have hnc := s16c167_not_comm_of_case2 D hC h2
  have hsig : D.sig = {3} := h2.2.2
  rcases h13 with h | h | h | h | h | h | h
  · exact h
  ·
    exfalso
    obtain ⟨p, -, h4⟩ := h
    exact hnc (s16c167_isElemAbelian_comm h4.1)
  ·
    exfalso
    obtain ⟨hpo, -, -⟩ := h
    obtain ⟨-, hcard, -⟩ := hpo
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : Group.IsNilpotent ↥(lBar ⊥ V hV L) :=
      (IsPGroup.of_card (p := 3) (n := 3) hcard).isNilpotent
    haveI : Group.IsSolvable ↥(lBar ⊥ V hV L) := inferInstance
    haveI : IsSimpleGroup ↥(lBar ⊥ V hV L) := s16c167_cfg2_simple D h2
    exact hnc (IsMulCommutative.of_comm
      (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))
  ·
    exfalso
    obtain ⟨hFel, -, -⟩ := h
    have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hC.setting.hyp151.le
    have hFle : fstarBar D.M ⊥ V hV ≤ Mbar D.M ⊥ V hV :=
      (s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)).1
    have hFnorm : ∀ x ∈ Mbar D.M ⊥ V hV, ∀ f ∈ fstarBar D.M ⊥ V hV,
        x * f * x⁻¹ ∈ fstarBar D.M ⊥ V hV :=
      (s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)).2.1
    have hFself : ∀ x ∈ Mbar D.M ⊥ V hV,
        (∀ f ∈ fstarBar D.M ⊥ V hV, x * f = f * x) → x ∈ fstarBar D.M ⊥ V hV :=
      (s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)).2.2
    have hFcomm : ∀ f ∈ fstarBar D.M ⊥ V hV, ∀ g ∈ fstarBar D.M ⊥ V hV,
        f * g = g * f := fun f hf g hg => congrArg Subtype.val
      ((s16c167_isElemAbelian_comm hFel).is_comm.comm ⟨f, hf⟩ ⟨g, hg⟩)
    have hLbot : lBar ⊥ V hV L ≠ ⊥ := by
      haveI := (s16c167_cfg2_simple D h2).toNontrivial
      exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
    obtain ⟨I, hirr, -, hsup⟩ := s16c167_case2_irr D h2
    have hall : commSub ⊤ (lBar ⊥ V hV L) = ⊤ := by
      refine top_le_iff.1 (hsup.symm.le.trans (sup_le ?_ ?_))
      · calc I 0 = commSub (I 0) (lBar ⊥ V hV L) := (hirr 0).1.symm
          _ ≤ commSub ⊤ (lBar ⊥ V hV L) := commSub_mono le_top le_rfl
      · calc I 1 = commSub (I 1) (lBar ⊥ V hV L) := (hirr 1).1.symm
          _ ≤ commSub ⊤ (lBar ⊥ V hV L) := commSub_mono le_top le_rfl
    obtain ⟨t, -, -, -, -, hW136⟩ := hC.conc
    have hLnormM : ∀ x ∈ Mbar D.M ⊥ V hV,
        (lBar ⊥ V hV L).map (MulAut.conj x).toMonoidHom = lBar ⊥ V hV L :=
      s16c167_cfg2_normal hLbot hall hW136
    have hLnormF : lBar ⊥ V hV L ≤ Subgroup.normalizer
        (fstarBar D.M ⊥ V hV : Set (MulAut (Vtil ⊥ V hV))) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx f hf
      exact hFnorm x (hLM hx) f hf
    haveI : ((fstarBar D.M ⊥ V hV).subgroupOf (lBar ⊥ V hV L)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hLnormF
    have hcommLb : IsMulCommutative ↥(lBar ⊥ V hV L) := by
      have hLleF : lBar ⊥ V hV L ≤ fstarBar D.M ⊥ V hV := by
        rcases (s16c167_cfg2_simple D h2).eq_bot_or_eq_top_of_normal
            ((fstarBar D.M ⊥ V hV).subgroupOf (lBar ⊥ V hV L)) with hbot | htop
        · intro x hx
          refine hFself x (hLM hx) fun f hf => ?_
          have hcLb : x * f * x⁻¹ * f⁻¹ ∈ lBar ⊥ V hV L := by
            have hconj : f * x⁻¹ * f⁻¹ ∈ lBar ⊥ V hV L := by
              have hmap := hLnormM f (hFle hf)
              have hmem : (MulAut.conj f) x⁻¹ ∈
                  (lBar ⊥ V hV L).map (MulAut.conj f).toMonoidHom :=
                Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom
                  ((lBar ⊥ V hV L).inv_mem hx)
              rw [hmap] at hmem
              simpa [MulAut.conj_apply] using hmem
            have heq : x * f * x⁻¹ * f⁻¹ = x * (f * x⁻¹ * f⁻¹) := by group
            rw [heq]
            exact (lBar ⊥ V hV L).mul_mem hx hconj
          have hcF : x * f * x⁻¹ * f⁻¹ ∈ fstarBar D.M ⊥ V hV := by
            have h1 : x * f * x⁻¹ ∈ fstarBar D.M ⊥ V hV := hFnorm x (hLM hx) f hf
            exact (fstarBar D.M ⊥ V hV).mul_mem h1 ((fstarBar D.M ⊥ V hV).inv_mem hf)
          have hmem : (⟨x * f * x⁻¹ * f⁻¹, hcLb⟩ : ↥(lBar ⊥ V hV L)) ∈
              (fstarBar D.M ⊥ V hV).subgroupOf (lBar ⊥ V hV L) :=
            Subgroup.mem_subgroupOf.mpr hcF
          rw [hbot] at hmem
          have hone : x * f * x⁻¹ * f⁻¹ = 1 :=
            congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
          have hx1 : x * f * x⁻¹ = f := mul_inv_eq_one.mp hone
          calc x * f = (x * f * x⁻¹) * x := by group
            _ = f * x := by rw [hx1]
        · exact Subgroup.subgroupOf_eq_top.mp htop
      refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
      exact hFcomm a.1 (hLleF a.2) b.1 (hLleF b.2)
    exact hnc hcommLb
  ·
    exfalso
    have h37 : (3 : ℕ) = 7 := Set.singleton_eq_singleton_iff.mp (hsig ▸ h.2.2.2.2)
    exact absurd h37 (by norm_num)
  ·
    exfalso
    obtain ⟨p, -, h10⟩ := h
    haveI : IsCyclic ↥(lBar ⊥ V hV L) := h10.1.1
    exact hnc inferInstance
  ·
    exfalso
    have h37 : (3 : ℕ) = 7 := Set.singleton_eq_singleton_iff.mp (hsig ▸ h.2.2.2)
    exact absurd h37 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
