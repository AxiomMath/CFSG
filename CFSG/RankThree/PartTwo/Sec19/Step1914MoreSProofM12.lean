module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof
public import CFSG.RankThree.PartTwo.Sec13.Item137ProofInvert
import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofCore
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1914SplitUse
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137ProofMain
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
public import CFSG.RankThree.PartTwo.Toolkit.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Step1914MoreM12Gen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
    ∀ E₀ F₀ : Subgroup X, E₀ ≠ F₀ → IsPGroup 3 (E₀ ⊔ F₀ : Subgroup X) →
      Nat.card E₀ = 9 → Nat.card F₀ = 9 →
      Nonempty (Sec4.autIn ⊤ E₀ ≃* GL (Fin 2) (ZMod 3)) →
      Nonempty (Sec4.autIn ⊤ F₀ ≃* GL (Fin 2) (ZMod 3)) →
        Subgroup.normalizer (E₀ : Set X) ⊔ Subgroup.normalizer (F₀ : Set X) = ⊤

namespace Step1914MoreSProof

variable {G : Type} [Group G] [Finite G]

theorem config137_swap {A L P E F : Subgroup G} {c t : G} (h : Config137 A c L P E F t) :
    Config137 A c L P F E t := by
  obtain ⟨h1, h2, h3, h4, hΔ, hAAt, hEF, hEA, hEAt, hFA, hFAt, hEN, hFN, hEa, hFa, hEdec,
    hFdec⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, hAAt, hEF.symm, hFA, hFAt, hEA, hEAt, hFN, hEN, hFa, hEa, hFdec,
    hEdec⟩
  rw [hΔ]
  ext X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem exists_config137_of_sylow
    (h131 : Item131) {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (S : Sylow 3 L) (hBS : (A ⊓ L).subgroupOf L ≤ S) :
    Nat.card (Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype : Subgroup G) = 81 ∧
      ∃ (E F : Subgroup G) (t : G),
        Config137 A c L (Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype) E F t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspor := sporadicModels131
  have h414 := Sec4.Sporadic.rank3II_4_14_local
  have hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X := fun X _ h => Toolkit.m12ThreeLocalData X h
  obtain ⟨hcL, h9, ⟨eA⟩⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3 (fun hcB => hcL (hBL hcB)) le_rfl h9
      (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  have hBp : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hB'map : ((A ⊓ L).subgroupOf L).map L.subtype = A ⊓ L :=
    Subgroup.map_subgroupOf_eq_of_le hBL
  have hB'9 : Nat.card ((A ⊓ L).subgroupOf L) = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hS3 : IsPGroup 3 (S : Subgroup L) := S.isPGroup'
  have hBaut : Nat.card (Sec4.autIn ⊤
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))) = 6 := by
    obtain ⟨e⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc hBL hBp
    rw [← hAB] at e
    rw [Nat.card_congr (e.symm.trans eA).toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨Eb, Fb, t₀, ht₀, hinv, hΔ, hncard, ⟨eE⟩, ⟨eF⟩, hHeis⟩ :=
    exists_bar_config h414 hM12D hM S hBS hB'9 hBaut
  obtain ⟨hS27, -, -⟩ := facts_of_isHeisThree_map hS3 hHeis
  have hΦB := liftSup_map (c := c) hS3 hBS
  rw [hB'map, ← hAB] at hΦB
  have hΦBt := liftSup_conjugate hLc hS3 (Subgroup.map_mono hBS) ht₀
  rw [hΦB] at hΦBt
  have hsetG := setOf_elemAbelian_eq_image_liftSup hc3 hcL hLc hS3 hHeis
  rw [hΔ, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    hΦB, hΦBt] at hsetG
  have hsub4 : ({Eb, Fb,
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)),
      conjugate (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) t₀)} :
      Set (Subgroup (L ⧸ aschbacherSolvableCore 3 L))) ⊆
        {Y | Y ≤ (S : Subgroup L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))} := by
    rw [← hΔ]
    exact fun Y hY => hY.1
  have hncardG : ({liftSup L c S Eb, liftSup L c S Fb, A, conjugate A (t₀ : G)} :
      Set (Subgroup G)).ncard = 4 := by
    have := ((liftSup_injOn hc3 hcL hLc S).mono hsub4).ncard_image
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hΦB,
      hΦBt, hncard] at this
    exact this
  obtain ⟨hEF, hEA, hEAt, hFA, hFAt, hAAt⟩ := ne_of_ncard_eq_four hncardG
  have hP81 := card_zpowers_sup_map hc3 hcL hLc hS27
  have hAP : A ≤ Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype :=
    hAB ▸ sup_le_sup_left (hB'map ▸ Subgroup.map_mono hBS) _
  have hAL : A ⊔ L = Subgroup.zpowers c ⊔ L :=
    le_antisymm (sup_le (hAB ▸ sup_le le_sup_left (hBL.trans le_sup_right)) le_sup_right)
      (sup_le_sup_right (Subgroup.zpowers_le.mpr h.mem_A) L)
  have hPAL : Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype ≤ A ⊔ L :=
    hAL ▸ sup_le_sup_left (Subgroup.map_subtype_le _) _
  have hPNA := le_normalizer_of_card hAP h.card_eq hP81
  have hEP : ∀ Y, liftSup L c S Y ≤ Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype :=
    fun Y => sup_le_sup_left (Subgroup.map_mono (liftIn_le _ _)) _
  obtain ⟨eE'⟩ := nonempty_autIn_liftSup hc3 hcL hLc hS3 (hsub4 (by simp) : Eb ≤ _)
  obtain ⟨eF'⟩ := nonempty_autIn_liftSup hc3 hcL hLc hS3 (hsub4 (by simp) : Fb ≤ _)
  refine ⟨hP81, liftSup L c S Eb, liftSup L c S Fb, (t₀ : G),
    hAL ▸ isSylowOf_zpowers_sup hc3 hcL hLc S hS27, hAP,
    ⟨t₀.2, mem_normalizer_zpowers_sup hLc ht₀⟩, inv_of_mem_commutator hLc hS3 hHeis ht₀ hinv,
    ?_, hAAt, hEF, hEA, hEAt, hFA, hFAt, (hEP Eb).trans (le_inf hPAL hPNA),
    (hEP Fb).trans (le_inf hPAL hPNA), ⟨eE'.trans eE⟩, ⟨eF'.trans eF⟩,
    by rw [liftSup_inf hc3 hcL hLc]; rfl, by rw [liftSup_inf hc3 hcL hLc]; rfl⟩
  rw [hsetG]
  ext X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

omit [Finite G] in
theorem card_inf_eq_nine {L F : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l) (hF27 : Nat.card F = 27)
    (hFdec : F = Subgroup.zpowers c ⊔ (F ⊓ L)) : Nat.card (F ⊓ L : Subgroup G) = 9 := by
  have hle : F ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hLc x hx.2))
  have hdisj : Subgroup.zpowers c ⊓ (F ⊓ L) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (zpowers_inf_eq_bot hc3 hcL).le)
  have h1 := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj
  rw [← hFdec, hF27, card_zpowers_of_pow_three hc3 hc1] at h1
  omega

end Step1914MoreSProof

open Step1914MoreSProof in
theorem step1914MoreSM12_of_gen
    (htri : Step1914Tri) (h131 : Item131) (h132 : Item132) (h133 : Item133) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h13S : Sec17.Item13Setup) (hPGL : Item137InvertPGL)
    (h195 : Item195) (hgen : Step1914MoreM12Gen) : Step1914MoreSM12 := by
  intro G _ _ A c L E M hctx hLM hM12
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hctx.mem_partTwoE.1
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hst hctx.partTwoS_eq hEE (hA.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  obtain ⟨φ⟩ := hM12
  obtain ⟨h3M, -, -, hsol⟩ := KFacts.ks18M12 _ ⟨φ⟩
  have hθeq := theta_eq_pCore_two_of_solvable hsol
  have hθM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hθeq).trans φ⟩
  have hE9 := rank3II_19_14E_of_tri htri KFacts.ks18M12 G A c L E M hctx hLM
  have hEB : E = Subgroup.zpowers c ⊔ (E ⊓ L) :=
    Step1914TriProof.eq_zpowers_sup_of_nine_le hE hcE hcL (by rw [hE9])
  have h3L : 3 ∣ Nat.card L := h3M.trans (Subgroup.card_quotient_dvd_card _)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    (hctx.le_centralizer.trans (Sec13.centralizer_le_normalizer_zpowers c)).trans
      (Step1914TriProof.normalizer_zpowers_le_of_three_dvd hctx h3L)
  have hQ3 : IsPGroup 3 (((E ⊔ A) ⊓ L).subgroupOf L) :=
    (hctx.isPGroup_sup.to_le inf_le_left).comap_subtype
  obtain ⟨S, hQS⟩ := hQ3.exists_le_sylow
  have hS3 : IsPGroup 3 (S : Subgroup L) := S.isPGroup'
  have hAbS : (A ⊓ L).subgroupOf L ≤ S :=
    (Subgroup.subgroupOf_mono L (inf_le_inf_right L le_sup_right)).trans hQS
  have hEbS : (E ⊓ L).subgroupOf L ≤ S :=
    (Subgroup.subgroupOf_mono L (inf_le_inf_right L le_sup_left)).trans hQS
  obtain ⟨hP81, E', F', t, hcfg⟩ := exists_config137_of_sylow h131 hD hθM S hAbS
  set P := Subgroup.zpowers c ⊔ (S : Subgroup L).map L.subtype with hP
  have hSL : (S : Subgroup L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hPL : P ⊓ L = (S : Subgroup L).map L.subtype :=
    zpowers_sup_inf_eq hc3 hcL hSL fun y hy => (hLc y (hSL hy)).symm
  have hELS : E ⊓ L ≤ (S : Subgroup L).map L.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : E ⊓ L ≤ L)]
    exact Subgroup.map_mono hEbS
  have hEP : E ≤ P := hEB ▸ sup_le_sup_left hELS _
  obtain ⟨F, hcfgF⟩ : ∃ F : Subgroup G, Config137 A c L P F E t := by
    have hcfg' := hcfg
    obtain ⟨-, -, -, -, hΔ, -⟩ := hcfg'
    have hmem : E ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
        Nat.card B = 27} := ⟨hEP, hE.1, hE.2⟩
    rw [hΔ] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · exact absurd (h1 ▸ hctx.mem_partTwoT) hctx.not_mem_partTwoT
    · exfalso
      apply hctx.not_mem_partTwoT
      have hT := hctx.mem_partTwoT
      rw [h1, conjugate] at hT
      exact (map_mem_partTwoT_iff (MulAut.conj t⁻¹)).mp hT
    · rw [← h1] at hcfg
      exact ⟨F', config137_swap hcfg⟩
    · rw [← h1] at hcfg
      exact ⟨E', hcfg⟩
  have hcfgF' := hcfgF
  obtain ⟨-, -, -, -, hΔ, -, hFE', -, -, -, -, -, -, ⟨eF⟩, ⟨eE⟩, hFdec, -⟩ := hcfgF'
  have hFmem : F ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 27} := by
    rw [hΔ]
    simp
  obtain ⟨hFP, hF3, hF27⟩ := hFmem
  have hF : IsE27 F := ⟨hF3, hF27⟩
  have hFNE : F ≤ Subgroup.normalizer (E : Set G) :=
    hFP.trans (le_normalizer_of_card hEP hE.2 hP81)
  have h9 : 9 ≤ Nat.card (F ⊓ E : Subgroup G) := by
    have hcard := Sec6.card_sup_mul_card_inf hFNE
    have hle : Nat.card (F ⊔ E : Subgroup G) ≤ 81 :=
      hP81 ▸ Subgroup.card_le_of_le (sup_le hFP hEP)
    rw [hF27, hE.2] at hcard
    by_contra hlt
    push Not at hlt
    have : Nat.card (F ⊔ E : Subgroup G) * Nat.card (F ⊓ E : Subgroup G) ≤ 81 * 8 :=
      Nat.mul_le_mul hle (by omega)
    omega
  have hF𝓔 := mem_partTwoE_of_nine_le hctx hF h9
  have hFM := le_M_of_nine_le hctx hF h9
  have hF9 : Nat.card (F ⊓ L : Subgroup G) = 9 := card_inf_eq_nine hc3 hc1 hcL hLc hF27 hFdec
  have hFLS : F ⊓ L ≤ (S : Subgroup L).map L.subtype := hPL ▸ inf_le_inf_right L hFP
  have hFbS : (F ⊓ L).subgroupOf L ≤ S := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hFLS (Subgroup.mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy
  have hEp : IsPGroup 3 (E ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hFp : IsPGroup 3 (F ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [hF9]; norm_num)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hcardb : ∀ {Y : Subgroup G}, Y ≤ L → (Y.subgroupOf L) ≤ S →
      Nat.card ((Y.subgroupOf L).map π) = Nat.card Y := by
    intro Y hYL hYS
    rw [card_map_eq_of_injOn _ ((injOn_mk_of_isPGroup Nat.prime_three hS3).mono hYS)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  have hautb : ∀ {Y : Subgroup G}, Y ≤ L → IsPGroup 3 Y → Subgroup.zpowers c ⊔ Y ≤ ⊤ →
      Nonempty (Sec4.autIn L (Subgroup.zpowers c ⊔ Y) ≃* GL (Fin 2) (ZMod 3)) →
      Nonempty (Sec4.autIn ⊤ ((Y.subgroupOf L).map π) ≃* GL (Fin 2) (ZMod 3)) := by
    intro Y hYL hYp _ ⟨e⟩
    obtain ⟨e'⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc hYL hYp
    exact ⟨e'.symm.trans e⟩
  have hFT : F ∉ partTwoT G := by
    intro hFT
    obtain ⟨-, M', hM'⟩ := mem_partTwoT_iff.mp hFT
    have hM'M := eq_of_mem_scriptM hctx hF hFM hM'
    rw [hM'M] at hM'
    apply hLM
    have h2E : 2 ≤ CFSG.Open.pRank 3 (E ⊓ L : Subgroup G) :=
      Late.two_le_pRank_of_elemAbelian (Late.isElemAbelian_of_le hE.1 inf_le_left)
        (by rw [hE9])
    have h2F : 2 ≤ CFSG.Open.pRank 3 (F ⊓ L : Subgroup G) :=
      Late.two_le_pRank_of_elemAbelian (Late.isElemAbelian_of_le hF3 inf_le_left)
        (by rw [hF9])
    refine le_of_normalizer_sup_eq_top inf_le_right inf_le_right hEp hFp ?_
      ((theta_le_gamma hE hEN).trans hctx.mem_scriptM.2)
      ((normalizer_le_gamma inf_le_left h2E).trans hctx.mem_scriptM.2)
      ((normalizer_le_gamma inf_le_left h2F).trans hM'.2)
    refine hgen _ hθM _ _ ?_ ?_ (by rw [hcardb inf_le_right hEbS, hE9])
      (by rw [hcardb inf_le_right hFbS, hF9])
      (hautb inf_le_right hEp le_top (hEB ▸ ⟨eE⟩))
      (hautb inf_le_right hFp le_top (hFdec ▸ ⟨eF⟩))
    · intro heq
      apply hFE'
      have h1 : (E ⊓ L).subgroupOf L = (F ⊓ L).subgroupOf L := by
        rw [← liftIn_map hS3 hEbS, ← liftIn_map hS3 hFbS]
        exact congrArg (liftIn (S : Subgroup L)) heq
      have h2 : E ⊓ L = F ⊓ L := by
        rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : E ⊓ L ≤ L),
          ← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : F ⊓ L ≤ L), h1]
      rw [hFdec, hEB, h2]
    · exact (hS3.map π).to_le (sup_le (Subgroup.map_mono hEbS) (Subgroup.map_mono hFbS))
  have hSF : HypS F := h195 G hctx.toSec19Std F hF𝓔 hFT
  have hNF := item137NormLe_of h131 h132 h13S sporadicModels131 G A c L hD hθM P F E t hcfgF F
    (Or.inl rfl) (Or.inl hSF)
  exact item137Move_of h131 h133 h134 h48 h13S hPGL G A c L hD hθM P F E t hcfgF (Or.inl hSF)
    hNF

end CFSG.RankThree.PartTwo.Sec19
