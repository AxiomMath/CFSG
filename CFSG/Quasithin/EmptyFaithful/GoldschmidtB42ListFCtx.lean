module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJCtx
public import CFSG.Quasithin.EmptyFaithful.SBc3List

public section

namespace CFSG.Quasithin.B42ListF

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem star_data (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hlj : Input15120LJ) (h56 : AsB56) {G : Type} [Group G] [Finite G]
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hchar : CharTwo L) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* Y),
      Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        CFSG.IsQuasisimple Y ∧ B56QuasisimpleList Y := by
  set S := s1516 T Z₁ with hSdef
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hlocal := quasithinIsLocal_iff_lFamily.mp hc.hL.mem.2
  have hSyl : IsSylowTwoOf S (L ⊔ S) := hlocal.2.1
  have hpcX : pCoreOf 2 (L ⊔ S) ≠ ⊥ := hlocal.2.2
  have hLX : L ∈ cComp (L ⊔ S) := cComp_of_isLocal hc.hL.mem.2
  have hX : CharTwo (L ⊔ S) := by
    by_cases hSN : S ≤ Subgroup.normalizer (L : Set G)
    · exact charTwo_sup_of_odd_quotient1515c hSyl.2.1 hSN hchar
    · have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hpcX hLX with
          hn | ⟨-, htypes⟩
        · exact absurd (le_sup_right.trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)) hSN
        · exact Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
      have hcenter := LJ.center_eq_bot_of_simple hc.hL.quasi hsimple
      have hz : ∀ x : ↥L ⧸ CFSG.pCore 2 ↥L, (∀ y, y * x = x * y) → x = 1 := fun x hx => by
        have : x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.mem_center_iff.mpr hx
        rw [hcenter] at this
        exact Subgroup.mem_bot.mp this
      exact S151S5.charTwo_sup_of_simple_comp hSyl.2.1 (subnormal_of_mem_cComp hLX)
        (perfect_of_mem_cComp hLX) hchar hc.hL.quasi hz
  have hred := C1GN.isTwoReducedIn_VZ hX hSyl
  have hVe : IsElemAbelian 2 (VZ S (L ⊔ S)) := hred.2.2.1
  have : IsMulCommutative ↥(VZ S (L ⊔ S)) := hVe.1
  have hO2 := LJ.pCoreOf_le_centralizer hred
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hLnV : ¬ L ≤ Subgroup.centralizer (VZ S (L ⊔ S) : Set G) := by
    intro hLV
    apply hc.hL.not_le
    intro x hx
    refine ⟨hc.hL.mem.1 hx, hq.centralizer_le_mc ?_⟩
    have hTV : quasithinOmegaOneCenter T ≤ VZ S (L ⊔ S) := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      have hzS : z ∈ S := ⟨hz.1.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hz.1.2 y (hZ₁T hy)⟩
      have hzZS : z ∈ quasithinOmegaOneCenter S :=
        Subgroup.subset_closure ⟨⟨hzS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_iff.mp hz.1.2 y (s1516_le T Z₁ hy)⟩, hz.2⟩
      exact le_conjClosure _ _ hzZS
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTV) (hLV hx)
  have hSQ : SQTKGroup ↥(L ⊔ S) :=
    sqtkGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpcX
  have hJ := hlj G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar
  have hJX : thompsonJ S ≤ thompsonJ (L ⊔ S) := thompsonJ_le_thompsonJ_of_isSylowTwoOf hSyl
  have hLJ : L ≤ thompsonJ (L ⊔ S) := by
    have h1 : ⁅L, thompsonJ S⁆ ≤ thompsonJ (L ⊔ S) := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      have hl' : l ∈ Subgroup.normalizer (thompsonJ (L ⊔ S) : Set G) :=
        GammaExtra.normalizer_le_normalizer_thompsonJ (L ⊔ S)
          (Subgroup.le_normalizer ((le_sup_left : L ≤ L ⊔ S) hl))
      have h2 := (Subgroup.mem_normalizer_iff.mp hl' j).1 (hJX hj)
      rw [commutatorElement_def]
      exact (thompsonJ (L ⊔ S)).mul_mem h2 ((thompsonJ (L ⊔ S)).inv_mem (hJX hj))
    rwa [hJ] at h1
  have hLcJ : L ∈ cComp (thompsonJ (L ⊔ S)) :=
    cComp_mem_of_le hLX hLJ (thompsonJ_le_self _)
  have hLN : L ≤ Subgroup.normalizer (VZ S (L ⊔ S) : Set G) := le_sup_left.trans hred.2.1
  have hsub : IsSubnormal L (L ⊔ S) := subnormal_of_mem_cComp hLX
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (VZ S (L ⊔ S) : Set G) := fun x hx =>
    hO2 (S151S5.pCoreOf_le_of_isSubnormal' hsub hx)
  have hle : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLN).ker := by
    intro x hx
    rw [InternalSec.mem_ker_autOnHom]
    exact hO2L ⟨x, by assumption, rfl⟩
  let ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L (VZ S (L ⊔ S))) :=
    QuotientGroup.lift _ (InternalSec.autOnHom hLN) hle
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLN y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hne : ∃ k, ρ k ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hLnV
    intro l hl
    have h1 : ρ (QuotientGroup.mk ⟨l, hl⟩) = 1 := hall _
    have h2 : (InternalSec.autOnHom hLN) ⟨l, hl⟩ = 1 := h1
    exact (InternalSec.mem_ker_autOnHom hLN ⟨l, hl⟩).1 h2
  have hqX : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hc.hL.quasi
  have hY : CFSG.IsQuasisimple ↥(autOn L (VZ S (L ⊔ S))) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqX hρs hne
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqX hne
  have hlist := SBc3.autOn_mem_list_of_component h56 hVe hred hSQ hLcJ hY
  exact ⟨_, inferInstance, inferInstance, ρ, hρs, hker, hY, hlist⟩

end CFSG.Quasithin.B42ListF
