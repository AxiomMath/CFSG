module

public import CFSG.Quasithin.H13.AS91Sec8V1AutCheck
public import CFSG.Quasithin.H13.AS91Sec8V1Gens
public import CFSG.Quasithin.AppendixH.H14.H141S1
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ASVolI.ChH (M24g S24)

theorem sxCert_originalSubgroup :
    sxCert.originalSubgroup = Subgroup.closure ({sxA, sxB} : Set S24) := by
  rw [sxCert, certificate_originalSubgroup, sxAT_eq, sxBT_eq]
  congr 1
  ext g
  simp

theorem sxCert_card_closure :
    Nat.card ↥(Subgroup.closure ({sxA, sxB} : Set S24)) = 138240 := by
  have h := sx_schreier
  rw [← sxCert_originalSubgroup,
    ← CFSG.Certificates.RawSchreierDatum.orderCertificate_eq_card sxCert h.1, h.2]

theorem sextStab_eq_closure :
    sextStab = Subgroup.closure ({sxA, sxB} : Set S24) := by
  have hle : Subgroup.closure ({sxA, sxB} : Set S24) ≤ sextStab := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact sxA_mem
    · exact sxB_mem
  have hcard : Nat.card ↥sextStab ≤
      Nat.card ↥(Subgroup.closure ({sxA, sxB} : Set S24)) := by
    rw [sxCert_card_closure]
    simpa [sextStab, CFSG.ASVolI.ChH.MY] using
      (CFSG.Quasithin.AppendixH.H14.card_MS_le
        (S := sextFin 0) (isSextet_sextFin (by norm_num)))
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem card_sextStab :
    Nat.card ↥sextStab = 138240 := by
  rw [sextStab_eq_closure]
  exact sxCert_card_closure

theorem center_sextStab_eq_bot :
    Subgroup.center ↥sextStab = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hzO : (z : S24) ∈ sxCert.originalSubgroup := by
    rw [sxCert_originalSubgroup]
    rw [← sextStab_eq_closure]
    exact z.2
  have hzE : (z : S24) ∈ enumeration sxCert :=
    (mem_enumeration_iff sxCert (sx_schreier.1) _).2 hzO
  obtain ⟨T, hT, hRep⟩ := exists_mem_of_forall₂_left
    (forall₂_allTables hn sxCert) _ (List.mem_reverse.2 hzE)
  have hcommA : (z : S24) * sxA = sxA * (z : S24) :=
    (congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hz ⟨sxA, sxA_mem⟩)).symm
  have hcommB : (z : S24) * sxB = sxB * (z : S24) :=
    (congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hz ⟨sxB, sxB_mem⟩)).symm
  have hcA : commT 24 T (toTable sxA) = true :=
    (commT_iff hRep (rep_toTable hn sxA)).2 hcommA
  have hcB : commT 24 T (toTable sxB) = true :=
    (commT_iff hRep (rep_toTable hn sxB)).2 hcommB
  have hall : (allTables sxCert).all (fun T =>
      !commT 24 T (toTable sxA) || !commT 24 T (toTable sxB) || tblEq 24 T (idT 24)) = true := by
    simpa only [sxCenterOK, sxAT_eq, sxBT_eq] using sx_center
  have hT' := List.all_eq_true.1 hall T hT
  rw [hcA, hcB] at hT'
  simp only [Bool.not_true, Bool.false_or] at hT'
  exact Subtype.ext (eq_one_of_tblEq_idT hn hRep hT')

theorem card_mulAut_sextStab_le :
    Nat.card (MulAut ↥sextStab) ≤ Nat.card ↥sextStab := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier sxCert := sx_schreier.1
  have hmemA : sxA ∈ sxCert.originalSubgroup := by
    rw [sxCert_originalSubgroup]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hmemB : sxB ∈ sxCert.originalSubgroup := by
    rw [sxCert_originalSubgroup]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hordA_perm : orderOf sxA = 5 :=
    (ordTest_iff perm_faithful (rep_toTable hn sxA) (by norm_num)).1 (sx_aut_orders.1)
  have hordB_perm : orderOf sxB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn sxB) (by norm_num)).1 (sx_aut_orders.2)
  have hordA : orderOf (⟨sxA, sxA_mem⟩ : ↥sextStab) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hordA_perm
  have hordB : orderOf (⟨sxB, sxB_mem⟩ : ↥sextStab) = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact hordB_perm
  have hws : ∀ p ∈ sxAutWords, 0 < p.2 := by decide
  have hwr_perm : WordsRel sxAutWords sxA sxB :=
    (wordsTest_iff perm_faithful (rep_toTable hn sxA) (rep_toTable hn sxB)
      hordA_perm hordB_perm (by norm_num) (by norm_num) hws).1 sx_aut_words
  have hwr : WordsRel sxAutWords (⟨sxA, sxA_mem⟩ : ↥sextStab) ⟨sxB, sxB_mem⟩ := by
    rw [← wordsRel_coe]
    exact hwr_perm
  have himg : sextStab.subtype '' ({⟨sxA, sxA_mem⟩, ⟨sxB, sxB_mem⟩} : Set ↥sextStab) =
      ({sxA, sxB} : Set S24) := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · intro hg
      rcases hg with rfl | rfl
      · exact ⟨⟨sxA, sxA_mem⟩, Set.mem_insert _ _, rfl⟩
      · exact ⟨⟨sxB, sxB_mem⟩, Set.mem_insert_of_mem _ (Set.mem_singleton _), rfl⟩
  have hgen : Subgroup.closure ({⟨sxA, sxA_mem⟩, ⟨sxB, sxB_mem⟩} : Set ↥sextStab) = ⊤ := by
    refine Subgroup.map_injective (f := sextStab.subtype) sextStab.subtype_injective ?_
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure, himg,
      sextStab_eq_closure]
  have hbound := card_mulAut_le_wordPairs (⟨sxA, sxA_mem⟩ : ↥sextStab)
    ⟨sxB, sxB_mem⟩ hgen sxAutWords hwr
  have hspec := pairTables_spec (H := sxCert.originalSubgroup) hn hmemA hmemB
  have hreps : ∀ r ∈ [sxA], r ∈ sxCert.originalSubgroup ∧ orderOf r = 5 := by
    intro r hr
    rw [List.mem_singleton] at hr
    exact hr ▸ ⟨hmemA, hordA_perm⟩
  have hcount := card_pairs_eq_repsTotal hn sxCert hQ (mx := 5) (my := 4)
    (by norm_num) (by norm_num) (ws := sxAutWords) hws
    (gens := pairTables sxA sxB) (gensInv := pairTables sxA⁻¹ sxB⁻¹)
    (gg := fun l => if l = 0 then sxA else sxB) hspec [sxA] hreps 40000 sx_aut_reps.1
  have hsubS : sxCert.originalSubgroup = sextStab :=
    sxCert_originalSubgroup.trans sextStab_eq_closure.symm
  simp only [List.map_cons, List.map_nil] at hcount
  rw [hsubS, sx_aut_reps.2] at hcount
  rw [hordA, hordB] at hbound
  rw [hcount] at hbound
  rwa [card_sextStab]

theorem sextStabAutInner_holds :
    SextStabAutInner := by
  intro θ
  have htop : inner ↥sextStab = ⊤ :=
    CFSG.Sporadic.Schreier.inner_eq_top_of_card_le center_sextStab_eq_bot card_mulAut_sextStab_le
  have hθ : θ ∈ inner ↥sextStab := htop ▸ Subgroup.mem_top θ
  obtain ⟨n, hn⟩ := hθ
  exact ⟨n, fun g => by rw [← hn, MulAut.conj_apply]⟩

end CFSG.Quasithin.H13.AS91.M24G
