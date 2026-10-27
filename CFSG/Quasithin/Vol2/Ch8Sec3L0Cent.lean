module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem conjSubgroupsBy_fsuM_eq_of_fsu (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    conjSubgroupsBy (fsuM T L) L = {L, CFSG.conjugate L t} := by
  have hcard := ncard_conjSubgroupsBy_fsuM h37 h38 hfsu.simple hfsu.nonabelian
    hfsu.qtke hfsu.faithful hnn
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · rintro K (rfl | rfl)
    · simpa [conjugate_one] using conjugate_mem_conjSubgroupsBy (T := T) (L := K)
        (fsuM T K).one_mem
    · exact conjugate_mem_conjSubgroupsBy (le_fsuM T L ht)
  · rw [hcard, Set.ncard_pair (ne_conjugate htn)]

theorem conjugate_eq_or_of_fsu (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate L s = L ∨ CFSG.conjugate L s = CFSG.conjugate L t := by
  have h := conjugate_mem_conjSubgroupsBy hs
  rw [conjSubgroupsBy_fsuM_eq_of_fsu h37 h38 hfsu hnn ht htn] at h
  exact h

theorem mul_self_mem_normalizer_of_fsu (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    t * t ∈ Subgroup.normalizer (L : Set G) := by
  rcases conjugate_eq_or_of_fsu h37 h38 hfsu hnn ht htn (le_fsuM T L (T.mul_mem ht ht)) with
    h | h
  · exact conjugate_eq_self_iff.mp h
  · have := mul_inv_mem_normalizer_of_conjugate_eq h
    rw [mul_inv_cancel_right] at this
    exact absurd this htn

theorem fsuL0_eq_sup_of_fsu (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hfsu : FSU G T L I) (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L = L ⊔ CFSG.conjugate L t := by
  refine le_antisymm (conjClosure_le fun s hs l hl => ?_)
    (sup_le (le_fsuL0 T L) (conjugate_le_fsuL0 ht))
  have hmem : s * l * s⁻¹ ∈ CFSG.conjugate L s⁻¹ := by
    rw [mem_conjugate_iff]
    simpa [mul_assoc] using hl
  rcases conjugate_eq_or_of_fsu h37 h38 hfsu hnn ht htn (le_fsuM T L (T.inv_mem hs)) with h | h
  · rw [h] at hmem
    exact Subgroup.mem_sup_left hmem
  · rw [h] at hmem
    exact Subgroup.mem_sup_right hmem

theorem commutator_conjugate_le_of_fsu (h37 : Vol2Native.A37ForSQTKCat) (hfsu : FSU G T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅L, CFSG.conjugate L t⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 (CFSG.conjugate L t) := by
  have := hfsu.simple
  exact (Vol2Native.lemma_1_2_1_two (qtkeCore_of_cat hfsu.nonabelian hfsu.qtke).1 h37
    (pCoreOf_fsuM_ne_bot hfsu.faithful) (mem_cComp_fsuM hfsu.maximal.1)
    (conjugate_mem_cComp_fsuM hfsu.maximal.1 (le_fsuM T L ht)) (ne_conjugate htn)).1

theorem isSimpleGroup_conjugate_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    IsSimpleGroup (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) := by
  have := hfsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hfsu.nonabelian hfsu.qtke).1
  rcases Vol2Native.lemma_1_2_1_three hK h37 h38 (pCoreOf_fsuM_ne_bot hfsu.faithful)
      (conjugate_mem_cComp_fsuM hfsu.maximal.1 (le_fsuM T L ht)) with hnorm | ⟨-, htypes⟩
  · exfalso
    have hN := (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((conjugate_le_fsuL0 ht).trans (fsuL0_le_fsuM T L))).mp hnorm
    have h1 : CFSG.conjugate (CFSG.conjugate L t) t = CFSG.conjugate L t :=
      conjugate_eq_self_iff.mpr (hN (le_fsuM T L ht))
    rw [conjugate_conjugate,
      conjugate_eq_self_iff.mpr (mul_self_mem_normalizer_of_fsu h37 h38 hfsu hnn ht htn)] at h1
    exact ne_conjugate htn h1
  · exact Vol2Native.L122A.isSimpleGroup_of_a38Types htypes

theorem center_quot_eq_bot_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
  center_eq_bot_of_perfect (perfect_L hfsu.maximal.1)
    (isSimpleGroup_of_not_normal h37 h38 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.faithful hnn)

theorem center_quot_conjugate_eq_bot_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    Subgroup.center (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) = ⊥ :=
  center_eq_bot_of_perfect
    (perfect_of_mem_cComp (conjugate_mem_cComp_fsuM hfsu.maximal.1 (le_fsuM T L ht)))
    (isSimpleGroup_conjugate_of_fsu h37 h38 hfsu hnn ht htn)

theorem inf_sup_pCoreOf_fsuL0_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    L ⊓ (CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L)) = pCoreOf 2 L :=
  inf_sup_pCoreOf_eq (center_quot_eq_bot_of_fsu h37 h38 hfsu hnn) (le_fsuL0 T L)
    (conjugate_le_fsuL0 ht) (Subgroup.map_subtype_le _) (fsuL0_le_normalizer hfsu.maximal.1)
    (fun _ hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_fsuL0 T L hx))
    ((commutator_conjugate_le_of_fsu h37 hfsu ht htn).trans inf_le_left)
    (inf_pCoreOf_fsuL0 hfsu.maximal.1)

theorem conjugate_inf_sup_pCoreOf_fsuL0_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L t ⊓ (L ⊔ pCoreOf 2 (fsuL0 T L)) = pCoreOf 2 (CFSG.conjugate L t) :=
  inf_sup_pCoreOf_eq (center_quot_conjugate_eq_bot_of_fsu h37 h38 hfsu hnn ht htn)
    (conjugate_le_fsuL0 ht) (le_fsuL0 T L) (Subgroup.map_subtype_le _)
    (fsuL0_le_normalizer_conjugate hfsu.maximal.1 (le_fsuM T L ht))
    (fun _ hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (conjugate_le_fsuL0 ht hx))
    ((Subgroup.commutator_comm _ _).le.trans ((commutator_conjugate_le_of_fsu h37 hfsu ht htn).trans
      inf_le_right))
    (conjugate_inf_pCoreOf_fsuL0 hfsu.maximal.1 ht)

theorem sup_pCoreOf_inf_eq_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    (CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L)) ⊓ (L ⊔ pCoreOf 2 (fsuL0 T L)) =
      pCoreOf 2 (fsuL0 T L) := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right le_sup_right)
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) := fun _ hl =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_fsuL0 T L hl)
  have hx2 : x ∈ ((L ⊔ pCoreOf 2 (fsuL0 T L) : Subgroup G) : Set G) := hx.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLO] at hx2
  obtain ⟨l, hl, o, ho, rfl⟩ := hx2
  have hl' : l ∈ CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L) := by
    have := (CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L)).mul_mem hx.1
      (Subgroup.mem_sup_right ((pCoreOf 2 (fsuL0 T L)).inv_mem ho))
    simpa using this
  have hlO : l ∈ pCoreOf 2 L := by
    rw [← inf_sup_pCoreOf_fsuL0_of_fsu h37 h38 hfsu hnn ht htn]
    exact ⟨hl, hl'⟩
  exact (pCoreOf 2 (fsuL0 T L)).mul_mem
    (sup_pCoreOf_le hfsu.maximal.1 ht (Subgroup.mem_sup_left hlO)) ho

theorem exists_fsuL0_prod_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ φ : ↥(fsuL0 T L) →* (↥L ⧸ CFSG.pCore 2 ↥L) ×
        (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)),
      Function.Surjective φ ∧ φ.ker = (pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L) ∧
      (∀ (l : G) (hl : l ∈ L),
        φ ⟨l, le_fsuL0 T L hl⟩ = (((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L), 1)) ∧
      ∀ (l : G) (hl : l ∈ CFSG.conjugate L t), φ ⟨l, conjugate_le_fsuL0 ht hl⟩ =
        (1, ((⟨l, hl⟩ : ↥(CFSG.conjugate L t)) :
          ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t))) := by
  have hloc := hfsu.maximal.1
  have hOX : pCoreOf 2 (fsuL0 T L) ≤ fsuL0 T L := Subgroup.map_subtype_le _
  have hL0 := fsuL0_eq_sup_of_fsu h37 h38 hfsu hnn ht htn
  have hNO : fsuL0 T L ≤ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  obtain ⟨φ₁, hs₁, hk₁, hL₁, hLt₁⟩ := exists_proj (le_fsuL0 T L) (conjugate_le_fsuL0 ht) hOX
    (by rw [hL0]; exact sup_le le_sup_left (le_sup_left.trans le_sup_right))
    (le_normalizer_sup (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht)) hNO)
    (inf_sup_pCoreOf_fsuL0_of_fsu h37 h38 hfsu hnn ht htn)
  obtain ⟨φ₂, hs₂, hk₂, hLt₂, hL₂⟩ := exists_proj (conjugate_le_fsuL0 ht) (le_fsuL0 T L) hOX
    (by rw [hL0]; exact sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    (le_normalizer_sup (fsuL0_le_normalizer hloc) hNO)
    (conjugate_inf_sup_pCoreOf_fsuL0_of_fsu h37 h38 hfsu hnn ht htn)
  refine ⟨φ₁.prod φ₂, ?_, ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rintro ⟨a, b⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨⟨l', hl'⟩, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨l, le_fsuL0 T L hl⟩ * ⟨l', conjugate_le_fsuL0 ht hl'⟩, ?_⟩
    rw [map_mul, MonoidHom.prod_apply, MonoidHom.prod_apply, hL₁ l hl, hL₂ l hl, hLt₁ l' hl',
      hLt₂ l' hl']
    simp
  · rw [MonoidHom.ker_prod, hk₁, hk₂]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← Subgroup.mem_inf, sup_pCoreOf_inf_eq_of_fsu h37 h38 hfsu hnn ht htn]
  · rw [MonoidHom.prod_apply, hL₁ l hl, hL₂ l hl]
  · rw [MonoidHom.prod_apply, hLt₁ l hl, hLt₂ l hl]

theorem false_of_mem_centralizer_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyL : y ∈ L)
    (hyC : y ∈ Subgroup.centralizer (fsuVM T L I : Set G)) (hyO : y ∉ pCoreOf 2 L) : False := by
  have hs := isSimpleGroup_of_not_normal h37 h38 hfsu.simple hfsu.nonabelian hfsu.qtke
    hfsu.faithful hnn
  set D := L ⊓ Subgroup.centralizer (fsuVM T L I : Set G)
  have hDL : D ≤ L := inf_le_left
  have hn : L ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.normalizer (L : Set G) ⊓
        Subgroup.normalizer (Subgroup.centralizer (fsuVM T L I : Set G) : Set G) :=
      ⟨Subgroup.le_normalizer hx,
        le_normalizer_centralizer ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)) hx⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf hx'
  have : (D.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr hn
  have hnorm := (this.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _))
  have htop : (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    refine (hs.eq_bot_or_eq_top_of_normal _).resolve_left fun hbot => hyO ?_
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨y, hyL⟩) ∈
        (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      ⟨⟨y, hyL⟩, ⟨hyL, hyC⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, mk_eq_one_iff] at hmem
    exact hmem
  have hDeq : D = L := eq_of_forall_mul_mem_pCoreOf hfsu.faithful hDL hn fun x hx => by
    have hx' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩) ∈
        (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdx⟩ := hx'
    refine ⟨d, hd, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← subgroupOf_pCoreOf,
      Subgroup.mem_subgroupOf] at hdx
    simpa using hdx
  apply commutator_fsuVM_ne_bot hfsu
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  intro x hx
  rw [← hDeq] at hx
  exact hx.2

theorem fsuL0_inf_centralizer_le_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  obtain ⟨φ, -, hk, hL, hLt⟩ := exists_fsuL0_prod_of_fsu h37 h38 hfsu hnn ht htn
  have hloc := hfsu.maximal.1
  have hNC := le_normalizer_centralizer (fsuL0_le_normalizer_fsuVM T L I)
  intro x hx
  by_contra hxO
  have hφ : φ ⟨x, hx.1⟩ ≠ 1 := fun h => hxO (by
    rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf] at h
    exact h)
  have hcC : ∀ y ∈ fsuL0 T L, ⁅x, y⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro y hy
    rw [commutatorElement_def]
    have h1 : y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hNC hy) _).mp ((Subgroup.centralizer _).inv_mem hx.2)
    simpa [mul_assoc] using (Subgroup.centralizer _).mul_mem hx.2 h1
  by_cases ha : (φ ⟨x, hx.1⟩).1 = 1
  · have hb : (φ ⟨x, hx.1⟩).2 ∉ Subgroup.center _ := by
      rw [center_quot_conjugate_eq_bot_of_fsu h37 h38 hfsu hnn ht htn, Subgroup.mem_bot]
      exact fun hb => hφ (Prod.ext ha hb)
    rw [Subgroup.mem_center_iff] at hb
    push Not at hb
    obtain ⟨c, hc⟩ := hb
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hlL0 : l ∈ fsuL0 T L := conjugate_le_fsuL0 ht hl
    have hyLt : ⁅x, l⁆ ∈ CFSG.conjugate L t := by
      rw [commutatorElement_def]
      have h1 : x * l * x⁻¹ ∈ CFSG.conjugate L t := (Subgroup.mem_normalizer_iff.mp
        (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht) hx.1) l).mp hl
      exact (CFSG.conjugate L t).mul_mem h1 ((CFSG.conjugate L t).inv_mem hl)
    have hval : φ ⟨⁅x, l⁆, conjugate_le_fsuL0 ht hyLt⟩ =
        φ ⁅(⟨x, hx.1⟩ : ↥(fsuL0 T L)), ⟨l, hlL0⟩⁆ := rfl
    rw [hLt _ hyLt, map_commutatorElement, hLt l hl] at hval
    have hyO : ⁅x, l⁆ ∉ pCoreOf 2 (CFSG.conjugate L t) := by
      intro hyO
      have h2 := congrArg Prod.snd hval
      rw [(mk_eq_one_iff (⟨_, hyLt⟩ : ↥(CFSG.conjugate L t))).mpr hyO] at h2
      have h3 : ⁅(φ ⟨x, hx.1⟩).2, ((⟨l, hl⟩ : ↥(CFSG.conjugate L t)) :
          ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t))⁆ = 1 := by
        simpa [commutatorElement_def] using h2.symm
      exact hc (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    refine false_of_mem_centralizer_of_fsu h37 h38 hfsu hnn (y := t * ⁅x, l⁆ * t⁻¹)
      (mem_conjugate_iff.mp hyLt) ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_centralizer (le_normalizer_fsuVM T L I) ht) _).mp (hcC l hlL0))
      fun hO => hyO ?_
    rw [pCoreOf_conjugate, mem_conjugate_iff]
    exact hO
  · have ha' : (φ ⟨x, hx.1⟩).1 ∉ Subgroup.center _ := by
      rw [center_quot_eq_bot_of_fsu h37 h38 hfsu hnn, Subgroup.mem_bot]
      exact ha
    rw [Subgroup.mem_center_iff] at ha'
    push Not at ha'
    obtain ⟨c, hc⟩ := ha'
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hlL0 : l ∈ fsuL0 T L := le_fsuL0 T L hl
    have hyL : ⁅x, l⁆ ∈ L := by
      rw [commutatorElement_def]
      have h1 : x * l * x⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (fsuL0_le_normalizer hloc hx.1) l).mp hl
      exact L.mul_mem h1 (L.inv_mem hl)
    have hval : φ ⟨⁅x, l⁆, le_fsuL0 T L hyL⟩ = φ ⁅(⟨x, hx.1⟩ : ↥(fsuL0 T L)), ⟨l, hlL0⟩⁆ := rfl
    rw [hL _ hyL, map_commutatorElement, hL l hl] at hval
    refine false_of_mem_centralizer_of_fsu h37 h38 hfsu hnn hyL (hcC l hlL0) fun hyO => ?_
    have h2 := congrArg Prod.fst hval
    rw [(mk_eq_one_iff (⟨_, hyL⟩ : ↥L)).mpr hyO] at h2
    have h3 : ⁅(φ ⟨x, hx.1⟩).1, ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)⁆ = 1 := by
      simpa [commutatorElement_def] using h2.symm
    exact hc (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

end CFSG.Quasithin.Vol2.Ch10.SecA
