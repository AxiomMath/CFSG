module

public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111
public import CFSG.Quasithin.EmptyFaithful.S1421Elim
public import CFSG.Quasithin.Background.F1Rank
public import CFSG.Quasithin.Recognition.F112WSetup

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S1421

section L16

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem isQuasithinSub_of_qtke (hK : quasithinIsQTKECat G) (X : Subgroup G) : IsQuasithinSub X := by
  intro p hp hp2 R _ hRne hR2
  have hloc : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
    (pRank_le_two_of_isTwoLocal hK hloc hp hp2)

omit [Finite G] in
theorem psi_mem_pCore_iff {P : Subgroup G} (e : OTwoQuot P ≃* Equiv.Perm (Fin 3)) (x : ↥P) :
    psi e x = 1 ↔ x ∈ CFSG.Open.pCore 2 ↥P := by
  unfold psi
  rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    QuotientGroup.mk'_apply, e.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem isSolvable_yT (F : Facts1422 T M) : Group.IsSolvable ↥(yOfL22 T M ⊔ T) := by
  obtain ⟨e⟩ := F.sThree
  have hS3 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have h2 : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ T)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(yOfL22 T M ⊔ T)) 2).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ T)).subtype (psi e)
    (fun x hx => ⟨⟨x, (psi_mem_pCore_iff e x).mp hx⟩, rfl⟩)

theorem isSolvable_l2_sup (h : Hyp1421 G T M) (F : Facts1422 T M) {S : Subgroup G} (hST : S ≤ T) :
    Group.IsSolvable ↥(l2Of T H (yOfL22 T M) ⊔ S) := by
  have hle : l2Of T H (yOfL22 T M) ⊔ S ≤ yOfL22 T M ⊔ T :=
    sup_le (sup_le le_sup_left ((s2_le_T h).trans le_sup_right)) (hST.trans le_sup_right)
  have := isSolvable_yT F
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem vz_le_pCoreOf_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    VZ T M ≤ pCoreOf 2 (l2Of T H (yOfL22 T M)) := by
  obtain ⟨hVred, -⟩ := isTwoReducedIn_VZ_of_hyp h
  refine le_pCoreOf_of_le_normalizer 2 ((vz_le_y h F).trans le_sup_left) ?_
    (isPGroup_of_isElemAbelian hVred.2.2.1)
  exact sup_le ((yOfL22_le T M).trans hVred.2.1) ((s2_le_T h).trans ((T_le_M h).trans hVred.2.1))

theorem Z_le_pCoreOf_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (l2Of T H (yOfL22 T M)) :=
  (le_conjClosure _ _).trans (vz_le_pCoreOf_l2 h F)

theorem Z_le_centralizer_pCoreOf_l2 (h : Hyp1421 G T M) (F : Facts1422 T M) :
    quasithinOmegaOneCenter T ≤
      Subgroup.centralizer (pCoreOf 2 (l2Of T H (yOfL22 T M)) : Set G) := by
  have h1 : pCoreOf 2 (l2Of T H (yOfL22 T M)) ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_s2_l2 h F)).trans (s2_le_T h)
  exact (quasithinOmegaOneCenter_le_center T).trans
    (inf_le_right.trans (Subgroup.centralizer_le h1))

theorem not_l2_le_normalizer_Z (h : Hyp1421 G T M) (F : Facts1422 T M) :
    ¬ l2Of T H (yOfL22 T M) ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  fun hh => not_y_le_normalizer_Z h F (le_sup_left.trans hh)

theorem isSylowTwoOf_vertex_of_borelOf_le {K1 L2 S : Subgroup G} (h : Hyp111 K1 L2 S)
    (hB2 : borelOf L2 S ≤ S) : IsSylowTwoOf S (L2 ⊔ bigB K1 L2 S) := by
  have hbig : bigB K1 L2 S = borelOf K1 S ⊔ S := by
    unfold bigB
    rw [sup_assoc, sup_eq_right.mpr hB2]
  have hSB : S ≤ bigB K1 L2 S := le_sup_right
  have hSB1 : S ≤ Subgroup.normalizer ((borelOf K1 S : Subgroup G) : Set G) :=
    F1.le_normalizer_borelOf h.h1.normalizes
  have hodd1 : ¬ 2 ∣ S.relIndex (bigB K1 L2 S) := by
    rw [hbig, F112W.relIndex_sup_eq_relIndex_inf hSB1]
    intro hd
    have hsyl : IsSylowTwoOf (S ⊓ K1) (borelOf K1 S) :=
      F7.isSylowTwoOf_mono_right h.h1.sylow (F1.sylow_le_borelOf K1 S) (F1.borelOf_le K1 S)
    exact F7.isSylowTwoOf_odd_relIndex hsyl (hd.trans (Subgroup.relIndex_dvd_of_le_left
      (borelOf K1 S) (le_inf (F1.sylow_le_borelOf K1 S) inf_le_left)))
  have hBN : bigB K1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le (sup_le h.h2.borel_le ((F1.borelOf_le L2 S).trans Subgroup.le_normalizer))
      h.h2.normalizes
  have hodd2 : ¬ 2 ∣ (bigB K1 L2 S).relIndex (L2 ⊔ bigB K1 L2 S) := by
    rw [F112W.relIndex_sup_eq_relIndex_inf hBN]
    intro hd
    exact F7.isSylowTwoOf_odd_relIndex h.h2.sylow (hd.trans (Subgroup.relIndex_dvd_of_le_left L2
      (le_inf inf_le_right (inf_le_left.trans hSB))))
  refine F7.isSylowTwoOf_of_relIndex (hSB.trans le_sup_right) h.h1.pgroup ?_
  rw [← Subgroup.relIndex_mul_relIndex S (bigB K1 L2 S) (L2 ⊔ bigB K1 L2 S) hSB le_sup_right]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
  exacts [hodd1 hd, hodd2 hd]

theorem Z_le_pCoreOf_vertex (h : Hyp1421 G T M) (F : Facts1422 T M)
    (hF111 : Hyp111 K1 (l2Of T H (yOfL22 T M)) (sOf T K1)) :
    quasithinOmegaOneCenter T ≤
      pCoreOf 2 (l2Of T H (yOfL22 T M) ⊔ bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1)) := by
  have hBN : bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1) ≤
      Subgroup.normalizer ((l2Of T H (yOfL22 T M) : Subgroup G) : Set G) :=
    sup_le (sup_le hF111.h2.borel_le ((F1.borelOf_le _ _).trans Subgroup.le_normalizer))
      hF111.h2.normalizes
  refine (Z_le_pCoreOf_l2 h F).trans (le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 _).trans le_sup_left) (sup_le (le_normalizer_pCoreOf 2 _)
      (hBN.trans (normalizer_le_normalizer_pCoreOf 2 _))) (pCoreOf_isPGroup 2 _))

theorem Z_le_centralizer_pCoreOf_vertex (hF111 : Hyp111 K1 (l2Of T H (yOfL22 T M)) (sOf T K1))
    (hB2 : borelOf (l2Of T H (yOfL22 T M)) (sOf T K1) ≤ sOf T K1) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer
      (pCoreOf 2 (l2Of T H (yOfL22 T M) ⊔ bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1)) :
        Set G) := by
  have h1 : pCoreOf 2 (l2Of T H (yOfL22 T M) ⊔
      bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1)) ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_vertex_of_borelOf_le hF111 hB2)).trans
      sOf_le_T
  exact (quasithinOmegaOneCenter_le_center T).trans
    (inf_le_right.trans (Subgroup.centralizer_le h1))

theorem lemma_14_2_16_survivor_legacyBare (hF112 : F112LegacyPrintedError) (hLF : ListedGroupFacts)
    (hRO : RankOneListedFacts.{0}) (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1)
    (hf : CharTwo (l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1)))
    (h15 : pCoreOf 2 (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1) = ⊥)
    (hbridge : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 3)) → IsL2Quot 1 X) :
    IsWeakBNPair (K1 ⊔ bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1))
        (l2Of T H (yOfL22 T M) ⊔ bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1)) ∧
      F112SurvivorLegacyBare K1 (l2Of T H (yOfL22 T M)) (sOf T K1) := by
  have hyp := st.hyp
  have F := st.facts
  have N := st.notation_
  have hF111 := hyp111_of_inputs h311 st h13 hf h15 hbridge
  refine ⟨(prop_F19_of_listed hRO hF111).2.1, ?_⟩
  have hc : ⁅yOfL22 T M, s2Of T H (yOfL22 T M)⁆ = yOfL22 T M := lemma_14_2_14 h311 st
  have hS2S : s2Of T H (yOfL22 T M) ≤ sOf T K1 := s2_le_sOf N h13
  have hBorel2 := borelOf_l2_eq h311 st h13
  have hnorm : ((sOf T K1).subgroupOf (sOf T K1 ⊔ borelOf (l2Of T H (yOfL22 T M)) (sOf T K1))).Normal := by
    rw [hBorel2, sup_eq_left.mpr hS2S, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  obtain ⟨L1', L2', hor, -, hlist, -⟩ := hF112 G K1 (l2Of T H (yOfL22 T M)) (sOf T K1) hF111
    (isQuasithinSub_of_qtke hyp.qtke _) (Or.inr hnorm)
  obtain ⟨e⟩ := oTwoQuot_l2_equiv_perm3 hyp F (lemma_14_2_14 h311 st)
  exact f112_survivor_legacyBare hLF N.cComp_mem ⟨e⟩ (isSolvable_l2_sup hyp F sOf_le_T)
    (quasithinOmegaOneCenter T) hyp.card_omegaOneCenter (Z_le_pCoreOf_l2 hyp F)
    (Z_le_centralizer_pCoreOf_l2 hyp F) (not_l2_le_normalizer_Z hyp F) ⟨L1', L2', hor, hlist⟩


theorem lemma_14_2_16_survivor (hF112 : F112Statement) (hLF : ListedGroupFacts)
    (hRO : RankOneListedFacts.{0}) (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1)
    (hf : CharTwo (l2Of T H (yOfL22 T M) ⊔ sOf T K1 ⊔ borelOf K1 (sOf T K1)))
    (h15 : pCoreOf 2 (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1) = ⊥)
    (hbridge : ∀ (X : Type) [Group X], Nonempty (X ≃* Equiv.Perm (Fin 3)) → IsL2Quot 1 X) :
    IsWeakBNPair (K1 ⊔ bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1))
        (l2Of T H (yOfL22 T M) ⊔ bigB K1 (l2Of T H (yOfL22 T M)) (sOf T K1)) ∧
      F112Survivor K1 (l2Of T H (yOfL22 T M)) (sOf T K1) := by
  have hyp := st.hyp
  have F := st.facts
  have N := st.notation_
  have hF111 := hyp111_of_inputs h311 st h13 hf h15 hbridge
  refine ⟨(prop_F19_of_listed hRO hF111).2.1, ?_⟩
  have hS2S : s2Of T H (yOfL22 T M) ≤ sOf T K1 := s2_le_sOf N h13
  have hBorel2 := borelOf_l2_eq h311 st h13
  have hnorm : ((sOf T K1).subgroupOf (sOf T K1 ⊔ borelOf (l2Of T H (yOfL22 T M)) (sOf T K1))).Normal := by
    rw [hBorel2, sup_eq_left.mpr hS2S, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hqt := isQuasithinSub_of_qtke hyp.qtke (K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1)
  have hB2 : borelOf (l2Of T H (yOfL22 T M)) (sOf T K1) ≤ sOf T K1 := hBorel2 ▸ hS2S
  obtain ⟨e⟩ := oTwoQuot_l2_equiv_perm3 hyp F (lemma_14_2_14 h311 st)
  exact f112_survivor hLF hF111 hqt hnorm N.cComp_mem ⟨e⟩ (isSolvable_l2_sup hyp F sOf_le_T)
    (quasithinOmegaOneCenter T) hyp.card_omegaOneCenter (Z_le_pCoreOf_vertex hyp F hF111)
    (Z_le_centralizer_pCoreOf_vertex hF111 hB2) (not_l2_le_normalizer_Z hyp F)
    (hF112 G K1 (l2Of T H (yOfL22 T M)) (sOf T K1) ⟨hF111, hqt, Or.inr hnorm⟩)

end L16

end S1421

end CFSG.Quasithin
