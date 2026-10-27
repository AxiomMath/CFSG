module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.Defs
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLieFast

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.EvenSmallLie.CatalogOrders

private theorem gkL_markChar_prime (lab : LargeEvenLabel) : (markChar lab).Prime := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markChar] <;> norm_num

private theorem gkL_one_le_markDeg {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    1 ≤ markDeg lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markDeg]
  all_goals first | (split_ifs <;> omega) | omega

private theorem gkL_lieMin_markTag_le_markRank {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) : lieMin (markTag lab) ≤ markRank lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp only [lieMin] <;> omega) | (simp only [lieMin]; omega)

private theorem gkL_markRank_zero_or_classical (lab : LargeEvenLabel) :
    markRank lab = 0 ∨ markTag lab = .PSL ∨ markTag lab = .PSU ∨ markTag lab = .PSp ∨
      markTag lab = .POmegaOdd ∨ markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markRank]
  all_goals first | (split_ifs <;> simp) | simp

private theorem gkL_markRank_le_lieExp_add_one {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) :
    markRank lab ≤ lieExp (markTag lab) (markRank lab) + 1 :=
  le_lieExp_add_one (gkL_lieMin_markTag_le_markRank hl) (gkL_markRank_zero_or_classical lab)

private theorem gkL_lieAdm_markTag {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    lieAdm (markTag lab) (markChar lab) (markDeg lab) = true := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;>
    simp only [lieAdm, markTag, markChar, markDeg]
  case twB2 =>
    obtain ⟨-, -, hodd, h3⟩ := hl
    rw [Nat.odd_iff] at hodd
    simp [hodd, h3]
  all_goals first | rfl | (split_ifs <;> rfl)

private def gkL_labelRealizable (t : CFSG.Open.StatedLieTag) (q : ℕ) : Bool :=
  q % 2 == 0 || (t == .PSU && q == 3) || (t == .PSL && q == 9)

private theorem gkL_labelRealizable_of_mod_two (t : CFSG.Open.StatedLieTag) (q : ℕ)
    (h : q % 2 = 0) : gkL_labelRealizable t q = true := by
  simp [gkL_labelRealizable, h]

private theorem gkL_labelRealizable_markChar_pow_markDeg {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) :
    gkL_labelRealizable (markTag lab) (markChar lab ^ markDeg lab) = true := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [LargeEvenInLambda2] at hl <;> simp only [markTag, markChar, markDeg]
  case B2der => decide
  case G2der => decide
  all_goals (try split_ifs)
  all_goals
    first
    | (apply gkL_labelRealizable_of_mod_two
       exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega)))

@[expose] def labOrd (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .twF4 => CFSG.Open.ordTwistedF4 (2 ^ lab.n)
  | .twF4der => CFSG.Open.ordTits
  | _ => EvenSmallLie.CatalogOrders.lieOrd (markTag lab) (markRank lab)
      (markChar lab ^ markDeg lab)

private theorem gkL_labOrd_eq_lieOrd_of_markTag_mem {lab : LargeEvenLabel}
    (ht : markTag lab ∈ searchTags) :
    labOrd lab = lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [labOrd, markTag, markRank, markChar, markDeg]
  all_goals first | rfl |
    (exact absurd ht (by simp only [markTag, searchTags]; decide))

private theorem gkL_card_eq_labOrd_of_markedModel
    {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) {R : Type} [Group R] (hm : MarkedModel lab R) :
    Nat.card R = labOrd lab := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;>
    simp only [MarkedModel, markTag, markRank, markChar, markDeg, labOrd] at hm ⊢
  case B2der => exact CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hm
  case G2der => exact CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hm
  all_goals first
    | (rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hm]; rfl)
    | (rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hm]; split_ifs <;> rfl)

private theorem gkL_labOrd_C_true_of_search {M : ℕ} (hM : M ≠ 0) {ps : List ℕ}
    (hps : ∀ p : ℕ, p.Prime → p ∣ M → p ∈ ps)
    {C : CFSG.Open.StatedLieTag → ℕ → ℕ → ℕ → Bool} (hS : lieSearch ps M C = true)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (ht : markTag lab ∈ searchTags) (hcard : labOrd lab = M) :
    C (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) M = true := by
  have hEq := gkL_labOrd_eq_lieOrd_of_markTag_mem (lab := lab) ht
  have hlie : lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) = M := by
    rw [← hEq]; exact hcard
  have hd : lieOrd (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) ∣ M :=
    ⟨1, by rw [hlie, mul_one]⟩
  have hs := lieSearch_sound (ps := ps) (N := M) (C := C) hM hps hS
    (t := markTag lab) (n := markRank lab) (p := markChar lab) (f := markDeg lab)
    ht (gkL_markChar_prime lab) (gkL_one_le_markDeg hl) (gkL_lieMin_markTag_le_markRank hl)
    (gkL_markRank_le_lieExp_add_one hl) (gkL_lieAdm_markTag hl) hd
  rw [hlie] at hs
  exact hs

private theorem gkL_labOrd_ne_of_search {M : ℕ} (hM : M ≠ 0) {ps : List ℕ}
    (hps : ∀ p : ℕ, p.Prime → p ∣ M → p ∈ ps)
    {C : CFSG.Open.StatedLieTag → ℕ → ℕ → ℕ → Bool} (hS : lieSearch ps M C = true)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (ht : markTag lab ∈ searchTags)
    (hCf : C (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) M = false) :
    labOrd lab ≠ M := by
  intro hcard
  have hs := gkL_labOrd_C_true_of_search hM hps hS hl ht hcard
  rw [hCf] at hs
  exact Bool.false_ne_true hs

private theorem gkL_mem_of_dvd_list_prod {p : ℕ} (hp : p.Prime) :
    ∀ {l : List ℕ}, (∀ q ∈ l, q.Prime) → p ∣ l.prod → p ∈ l
  | [], _, h => by simp at h; exact absurd h hp.ne_one
  | q :: l, hl, h => by
      rw [List.prod_cons] at h
      rw [List.mem_cons]
      rcases hp.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hl q (by simp))).mp h)
      · exact Or.inr (gkL_mem_of_dvd_list_prod hp (fun r hr => hl r (by simp [hr])) h)

private theorem gkL_mem_of_dvd_prod_list {N : ℕ} {l ps : List ℕ} (hN : N = l.prod)
    (hprime : l.all (fun q => q.Prime) = true) (hsub : l.all (fun q => q ∈ ps) = true)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ N) : p ∈ ps := by
  have hmem : p ∈ l := gkL_mem_of_dvd_list_prod hp
    (fun q hq => of_decide_eq_true (List.all_eq_true.mp hprime q hq)) (hN ▸ hd)
  exact of_decide_eq_true (List.all_eq_true.mp hsub p hmem)

private theorem gkL_mem_primes_126000 {p : ℕ} (hp : p.Prime) (hd : p ∣ 126000) :
    p ∈ [2, 3, 5, 7] :=
  gkL_mem_of_dvd_prod_list (l := [2, 2, 2, 2, 3, 3, 5, 5, 5, 7]) (ps := [2, 3, 5, 7])
    (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_fi24 {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29) :
    p ∈ [2, 3, 5, 7, 11, 13, 17, 23, 29] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 21 2 ++ List.replicate 16 3 ++ List.replicate 2 5 ++
      List.replicate 3 7 ++ [11, 13, 17, 23, 29])
    (ps := [2, 3, 5, 7, 11, 13, 17, 23, 29]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_th {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31) :
    p ∈ [2, 3, 5, 7, 13, 19, 31] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 15 2 ++ List.replicate 10 3 ++ List.replicate 3 5 ++
      List.replicate 2 7 ++ [13, 19, 31]) (ps := [2, 3, 5, 7, 13, 19, 31])
    (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_hn {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) :
    p ∈ [2, 3, 5, 7, 11, 19] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 14 2 ++ List.replicate 6 3 ++ List.replicate 6 5 ++
      [7, 11, 19]) (ps := [2, 3, 5, 7, 11, 19]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_he {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) :
    p ∈ [2, 3, 5, 7, 17] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 10 2 ++ List.replicate 3 3 ++ List.replicate 2 5 ++
      List.replicate 3 7 ++ [17]) (ps := [2, 3, 5, 7, 17]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_m12 {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ 6 * 3 ^ 3 * 5 * 11) :
    p ∈ [2, 3, 5, 11] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 6 2 ++ List.replicate 3 3 ++ [5, 11])
    (ps := [2, 3, 5, 11]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_l33 {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ 4 * 3 ^ 3 * 13) :
    p ∈ [2, 3, 13] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 4 2 ++ List.replicate 3 3 ++ [13])
    (ps := [2, 3, 13]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_fi22 {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) :
    p ∈ [2, 3, 5, 7, 11, 13] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 17 2 ++ List.replicate 9 3 ++ List.replicate 2 5 ++
      [7, 11, 13]) (ps := [2, 3, 5, 7, 11, 13]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_mem_primes_hs {p : ℕ} (hp : p.Prime)
    (hd : p ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    p ∈ [2, 3, 5, 7, 11] :=
  gkL_mem_of_dvd_prod_list (l := List.replicate 9 2 ++ List.replicate 2 3 ++ List.replicate 3 5 ++
      [7, 11]) (ps := [2, 3, 5, 7, 11]) (by decide) (by decide) (by decide) hp hd

private theorem gkL_lieSearch_126000 :
    lieSearch [2, 3, 5, 7] 126000
      (fun t n q ord => !(ord == 126000) || !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 16) (by decide +kernel)

private theorem gkL_lieSearch_fi24 :
    lieSearch [2, 3, 5, 7, 11, 13, 17, 23, 29]
      (2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29)
      (fun t n q ord => !(ord == 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29) ||
        !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 80) (by decide +kernel)

private theorem gkL_lieSearch_th :
    lieSearch [2, 3, 5, 7, 13, 19, 31] (2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31)
      (fun t n q ord => !(ord == 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31) ||
        !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 56) (by decide +kernel)

private theorem gkL_lieSearch_hn :
    lieSearch [2, 3, 5, 7, 11, 19] (2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19)
      (fun t n q ord => !(ord == 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) ||
        !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 47) (by decide +kernel)

private theorem gkL_lieSearch_he :
    lieSearch [2, 3, 5, 7, 17] (2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17)
      (fun t n q ord => !(ord == 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) ||
        !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 31) (by decide +kernel)

private theorem gkL_lieSearch_m12 :
    lieSearch [2, 3, 5, 11] (2 ^ 6 * 3 ^ 3 * 5 * 11)
      (fun t n q ord => !(ord == 2 ^ 6 * 3 ^ 3 * 5 * 11) || !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 16) (by decide +kernel)

private theorem gkL_lieSearch_l33 :
    lieSearch [2, 3, 13] (2 ^ 4 * 3 ^ 3 * 13)
      (fun t n q ord => !(ord == 2 ^ 4 * 3 ^ 3 * 13) || !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 12) (by decide +kernel)

private theorem gkL_lieSearch_fi22 :
    lieSearch [2, 3, 5, 7, 11, 13] (2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13)
      (fun t n q ord => !(ord == 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ||
        !(gkL_labelRealizable t q)) = true :=
  lieSearch_of_lieSearchB (L := 45) (by decide +kernel)

private theorem gkL_lieSearch_hs :
    lieSearch [2, 3, 5, 7, 11] (2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11)
      (fun t n q ord => !(ord == 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) || !(gkL_labelRealizable t q)) =
    true :=
  lieSearch_of_lieSearchB (L := 25) (by decide +kernel)

private theorem gkL_Cne_apply_false {M : ℕ} {t : CFSG.Open.StatedLieTag} {q : ℕ}
    (h : gkL_labelRealizable t q = true) :
    (fun _ _ _ ord => !(ord == M) || !(gkL_labelRealizable t q)) t 0 q M = false := by
  simp [h]

private theorem gkL_ordTwistedF4_ne_of_not_dvd_36 {n M : ℕ} (h3 : 3 ≤ n) (hM : ¬ 2 ^ 36 ∣ M) :
    CFSG.Open.ordTwistedF4 (2 ^ n) ≠ M := by
  intro h
  apply hM
  have hdvd : 2 ^ (12 * n) ∣ CFSG.Open.ordTwistedF4 (2 ^ n) := by
    rw [CFSG.Open.ordTwistedF4]
    have hq : (2 ^ n) ^ 12 = 2 ^ (12 * n) := by rw [← pow_mul, mul_comm]
    rw [← hq]
    simp only [mul_assoc]
    exact dvd_mul_right _ _
  rw [h] at hdvd
  exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : 36 ≤ 12 * n)) hdvd

private theorem gkL_tag_eq_twF4_or_twF4der_of_markTag_not_mem {lab : LargeEvenLabel}
    (h : markTag lab ∉ searchTags) : lab.tag = .twF4 ∨ lab.tag = .twF4der := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; exact h (by
        simp only [markTag]
        first | (split_ifs <;> simp [searchTags]) | simp [searchTags]))

private theorem gkL_labOrd_twF4_eq {lab : LargeEvenLabel} (h : lab.tag = .twF4) :
    labOrd lab = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

private theorem gkL_labOrd_twF4der_eq {lab : LargeEvenLabel} (h : lab.tag = .twF4der) :
    labOrd lab = CFSG.Open.ordTits := by
  obtain ⟨t, l, n⟩ := lab
  subst h
  rfl

private theorem gkL_labOrd_twF4_ne {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (h : lab.tag = .twF4) {M : ℕ} (hM : ¬ 2 ^ 36 ∣ M) : labOrd lab ≠ M := by
  have hn : 3 ≤ lab.n := by
    obtain ⟨t, l, n⟩ := lab
    subst h
    simp only [LargeEvenInLambda2] at hl
    exact hl.2.2.2
  rw [gkL_labOrd_twF4_eq h]
  exact gkL_ordTwistedF4_ne_of_not_dvd_36 hn hM

private theorem gkL_labOrd_ne_of_source {M : ℕ} (hM : M ≠ 0) {ps : List ℕ}
    (hps : ∀ p : ℕ, p.Prime → p ∣ M → p ∈ ps)
    {C : CFSG.Open.StatedLieTag → ℕ → ℕ → ℕ → Bool} (hS : lieSearch ps M C = true)
    (h36 : ¬ 2 ^ 36 ∣ M) (htits : CFSG.Open.ordTits ≠ M)
    (hlab : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markTag lab ∈ searchTags →
      C (markTag lab) (markRank lab) (markChar lab ^ markDeg lab) M = false)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) : labOrd lab ≠ M := by
  by_cases ht : markTag lab ∈ searchTags
  · exact gkL_labOrd_ne_of_search hM hps hS hl ht (hlab lab hl ht)
  · rcases gkL_tag_eq_twF4_or_twF4der_of_markTag_not_mem ht with h | h
    · exact gkL_labOrd_twF4_ne hl h h36
    · rw [gkL_labOrd_twF4der_eq h]; exact htits

private theorem gkL_center_eq_bot_of_simple_nonabelian_lem {H : Type*} [Group H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm)

private theorem gkL_centerQuot_nonabelian' {H : Type*} [Group H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) :
    ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a :=
  nonabelian_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (gkL_center_eq_bot_of_simple_nonabelian_lem hna)).trans
      QuotientGroup.quotientBot).symm hna

private theorem gkL_sz_nonabelian'
    {a : ℕ} (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenSzGroup a K), x * y ≠ y * x := by
  have hsimple := CFSG.LieType.Ree.suzuki_simple (a := a) (K := K) ha hK
  have hperfect := CFSG.LieType.Ree.suzuki_perfect (a := a) (K := K) ha hK
  have hna : ∃ g h : suzukiGroup a K, g * h ≠ h * g := by
    by_contra h
    push Not at h
    haveI : Nontrivial (suzukiGroup a K) := hsimple.2.1
    haveI : Group.IsPerfect (suzukiGroup a K) := hperfect.2
    haveI : IsMulCommutative (suzukiGroup a K) := ⟨Std.Commutative.mk h⟩
    exact not_subsingleton (suzukiGroup a K) Group.IsPerfect.subsingleton_of_isMulCommutative
  haveI : IsSimpleGroup (suzukiGroup a K) := hsimple.2.2
  have hq : ∃ x y : LargeEvenCenterQuot (suzukiGroup a K), x * y ≠ y * x :=
    gkL_centerQuot_nonabelian' hna
  obtain ⟨e⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  exact nonabelian_of_mulEquiv e.symm hq

private theorem gkL_g2der_nonabelian'
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x := by
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv K .G2
  have hna : ∃ a b : DerivedCentralQuotient (adjointGroup .G2 K), a * b ≠ b * a := by
    have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK
    have hC : CFSG.Open.StatedClassicalModel
        ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ .PSU 3 3 1 := by
      rcases hL with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact h
      · simp [chevalleyExceptionalTags] at ht
      · simp [reeTitsTags] at ht
      · cases ht
    have hsimple : IsSimpleGroup ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hC).2
    have hcard : Nat.card ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ = 6048 := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : 3 ≠ 0) hL]
      decide
    have hneq : ∃ a b : ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆, a * b ≠ b * a := by
      by_contra hnab
      have hcomm : ∀ a b : ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆, a * b = b * a := by
        intro a b
        by_contra h
        exact hnab ⟨a, b, h⟩
      haveI : IsMulCommutative ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
        IsMulCommutative.of_comm hcomm
      have hp : (Nat.card ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆).Prime :=
        Group.is_simple_iff_prime_card.mp hsimple
      rw [hcard] at hp
      norm_num at hp
    exact gkL_centerQuot_nonabelian' hneq
  exact nonabelian_of_mulEquiv e₁.symm hna

private theorem gkL_rawDatum_imp'
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → MarkedModel lab R →
      Q' R I F)
    (h : LargeEvenRawDatum lab Q) : LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg]
    at hn hl h hQQ' ⊢
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_linear (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      have := four_le_two_pow (hl2 (by omega))
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three n h.2
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  case B =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case C =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case D =>
    split_ifs at h hQQ' ⊢ with h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_linear 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp, by simp⟩⟩
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case twD =>
    split_ifs at h hQQ' ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case G2 =>
    obtain ⟨-, hn2⟩ := hl
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, by
      have := four_le_two_pow hn2; omega⟩, untwistedChevalleyModel_largeEven .G2 hK⟩)
  case F4 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .F4 hK⟩)
  case E6 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E6 hK⟩)
  case E7 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E7 hK⟩)
  case E8 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E8 hK⟩)
  case twE6 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .E6 hK⟩)
  case triD4 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .D4 hK⟩)
  case twB2 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeSuzuki_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    have hSz := suzukiModel_largeEvenSz (a := (n - 1) / 2) (by omega) K hK
      (gkL_sz_nonabelian' (a := (n - 1) / 2) (by omega) K hK)
    rwa [← hn'] at hSz
  case twF4 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeTwF4_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    have hRee := reeTitsRelationModel_largeEven ((n - 1) / 2) hK
    rw [← hn'] at hRee
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, rfl, ⟨k, hk⟩, hn3⟩,
      (n - 1) / 2, hn', hRee⟩))
  case B2der =>
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inl ⟨by decide, statedClassicalModel_b2der hK⟩
  case G2der =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact lieModel_g2der K hK (gkL_g2der_nonabelian' K hK)
  case twF4der =>
    obtain ⟨-, rfl⟩ := hl
    refine recipeTwF4_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      0, rfl, reeTitsRelationModel_largeEven 0 hK⟩))

theorem largeEvenMarking_card_labOrd
    {L : Type} [Group L]
    (hm : LargeEvenMarking L (fun _ _ _ _ _ _ => True)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ MarkedModel lab (L ⧸ Subgroup.center L) ∧
      Nat.card (L ⧸ Subgroup.center L) = labOrd lab := by
  obtain ⟨lab, hlab, hmodel⟩ := largeEvenMarking_markedModel_centerQuot hm
  exact ⟨lab, hlab, hmodel, gkL_card_eq_labOrd_of_markedModel hlab hmodel⟩

theorem labOrd_eq_of_rawDatum
    {lab : LargeEvenLabel} {N : ℕ} (hl : LargeEvenInLambda2 lab)
    (h : LargeEvenRawDatum lab (fun R _ _ _ => Nat.card R = N)) : labOrd lab = N := by
  have h' := gkL_rawDatum_imp' (lab := lab) hl
    (Q := fun R _ _ _ => Nat.card R = N)
    (Q' := fun R _ _ _ => Nat.card R = N ∧ Nat.card R = labOrd lab)
    (fun R _ I F hq hmk => ⟨hq, gkL_card_eq_labOrd_of_markedModel hl hmk⟩) h
  obtain ⟨R, _, I, F, hN, hL⟩ := largeEvenRawDatum_exists h'
  exact hL.symm.trans hN

theorem labOrd_ne_126000 (lab : LargeEvenLabel) (hl : LargeEvenInLambda2 lab) :
    labOrd lab ≠ 126000 :=
  gkL_labOrd_ne_of_source (M := 126000) (ps := [2, 3, 5, 7])
    (C := fun t n q ord => !(ord == 126000) || !(gkL_labelRealizable t q))
    (by norm_num) (fun p hp hd => gkL_mem_primes_126000 hp hd) gkL_lieSearch_126000
    (by norm_num) (by decide)
    (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
        := lab) hl

@[expose] def bmCompOrders : List ℕ :=
  [2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29,
   2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31,
   2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19,
   2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17,
   2 ^ 6 * 3 ^ 3 * 5 * 11,
   2 ^ 4 * 3 ^ 3 * 13,
   2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13,
   2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11]

theorem labOrd_not_mem_bmCompOrders (lab : LargeEvenLabel) (hl : LargeEvenInLambda2 lab) :
    labOrd lab ∉ bmCompOrders := by
  simp only [bmCompOrders, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29)
      (ps := [2, 3, 5, 7, 11, 13, 17, 23, 29])
      (C := fun t n q ord =>
        !(ord == 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29) ||
          !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_fi24 hp hd) gkL_lieSearch_fi24 (by norm_num)
      (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31)
      (ps := [2, 3, 5, 7, 13, 19, 31])
      (C := fun t n q ord => !(ord == 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31) ||
        !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_th hp hd) gkL_lieSearch_th (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19)
      (ps := [2, 3, 5, 7, 11, 19])
      (C := fun t n q ord => !(ord == 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) ||
        !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_hn hp hd) gkL_lieSearch_hn (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17)
      (ps := [2, 3, 5, 7, 17])
      (C := fun t n q ord => !(ord == 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) ||
        !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_he hp hd) gkL_lieSearch_he (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 6 * 3 ^ 3 * 5 * 11) (ps := [2, 3, 5, 11])
      (C := fun t n q ord => !(ord == 2 ^ 6 * 3 ^ 3 * 5 * 11) || !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_m12 hp hd) gkL_lieSearch_m12 (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 4 * 3 ^ 3 * 13) (ps := [2, 3, 13])
      (C := fun t n q ord => !(ord == 2 ^ 4 * 3 ^ 3 * 13) || !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_l33 hp hd) gkL_lieSearch_l33 (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13)
      (ps := [2, 3, 5, 7, 11, 13])
      (C := fun t n q ord => !(ord == 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ||
        !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_fi22 hp hd) gkL_lieSearch_fi22 (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl
  · exact gkL_labOrd_ne_of_source (M := 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) (ps := [2, 3, 5, 7, 11])
      (C := fun t n q ord => !(ord == 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) || !(gkL_labelRealizable t q))
      (by norm_num) (fun p hp hd => gkL_mem_primes_hs hp hd) gkL_lieSearch_hs (by norm_num)
          (by decide)
      (fun lab hl _ => gkL_Cne_apply_false (gkL_labelRealizable_markChar_pow_markDeg hl)) (lab
          := lab) hl

theorem largeEvenMarking_not_card_126000
    {L : Type} [Group L]
    (h : Nat.card (L ⧸ Subgroup.center L) = 126000) :
    ¬ LargeEvenMarking L (fun _ _ _ _ _ _ => True) := by
  intro hm
  obtain ⟨lab, hl, _, hcard⟩ := largeEvenMarking_card_labOrd hm
  exact labOrd_ne_126000 lab hl (hcard ▸ h)

theorem largeEvenMarking_not_card_of_mem_bmCompOrders
    {L : Type} [Group L] {N : ℕ}
    (hN : N ∈ bmCompOrders) (h : Nat.card (L ⧸ Subgroup.center L) = N) :
    ¬ LargeEvenMarking L (fun _ _ _ _ _ _ => True) := by
  intro hm
  obtain ⟨lab, hl, _, hcard⟩ := largeEvenMarking_card_labOrd hm
  have hEq : labOrd lab = N := hcard.symm.trans h
  exact labOrd_not_mem_bmCompOrders lab hl (hEq.symm ▸ hN)

end CFSG.StandardType.SporadicShape
