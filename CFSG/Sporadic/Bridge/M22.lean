module

public import CFSG.Sporadic.Bridge.M22Check
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Blueprint.NativeSporadic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Certificates.CosetFacts
import all CFSG.Certificates.PresentationLetters
import all CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Sporadic.Bridge.M22

open CFSG.Certificates CFSG.Certificates.CosetEnumeration TauCeti Equiv

theorem factElt_mem_of_factsOK {G : Type*} [Group G] {H : Subgroup G} {gen : ℕ → G} {L N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl inv : ℕ → ℕ} {rels subs : List (List ℕ)}
    (hinv : ∀ c ≤ L, gen (inv c) = (gen c)⁻¹) (hlet : ∀ w ∈ rels ++ subs, ∀ c ∈ w, c ≤ L)
    (hrels : ∀ w ∈ rels, evalWord gen w = 1) (hsubs : ∀ w ∈ subs, evalWord gen w ∈ H)
    (hfacts : factsOK N (L + 1) fx fc fy kind wi fs ft fo refs pl inv rels subs 0 F = true) :
    ∀ f < F, factElt gen (L + 1) pl fx fc fy f ∈ H := by
  set L' := L + 1
  have hok : ∀ f < F, factOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs f = true :=
    fun f hf => factOK_of_factsOK hfacts f (Nat.zero_le f) (by simpa using hf)
  have hwinv : ∀ w ∈ rels ++ subs, ∀ c ∈ w, gen (inv c) = (gen c)⁻¹ :=
    fun w hw c hc => hinv c (hlet w hw c hc)
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf
    have h := hok f hf
    unfold factOK at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨_, _, h⟩ := h
    have ih' : ∀ g < f, factElt gen L' pl fx fc fy g ∈ H :=
      fun g hg => ih g hg (lt_trans hg hf)
    split at h
    ·
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨hpl, hcL, hxy⟩ := h
      have hpl' : pl (fy f) = fx f * L' + fc f := by simpa using Nat.eq_of_beq_eq_true hpl
      have hL0 : 0 < L' := by omega
      have hdiv : pl (fy f) / L' = fx f := by
        rw [hpl', Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt hcL,
          Nat.zero_add]
      have hmod : pl (fy f) % L' = fc f := by
        rw [hpl', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcL]
      have hy0 : 0 < fy f := lt_of_le_of_lt (Nat.zero_le _) hxy
      rw [factElt, rep_eq gen L' pl hy0 (by rw [hdiv]; exact hxy), hdiv, hmod]
      simp
    ·
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hwm := wordAt_mem h1
      rw [← walk_mem_iff (H := H) ih' _ 0 (fs f) (hwinv _ (List.mem_append_left _ hwm)) h3
        (Nat.zero_le _) (by simpa using h2), hrels _ hwm]
      simp
    ·
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hwm := wordAt_mem h1
      rw [← walk_mem_iff (H := H) ih' _ 0 0 (hwinv _ (List.mem_append_right _ hwm)) h3
        (Nat.zero_le _) (by simpa using h2), rep_zero]
      simpa using hsubs _ hwm
    · exact absurd h (by simp)

theorem evalWord_mem_of_walkOK {G : Type*} [Group G] {H : Subgroup G} {gen : ℕ → G} {L' F o : ℕ}
    {fx fc fy refs pl inv : ℕ → ℕ} {w : List ℕ}
    (htrue : ∀ f < F, factElt gen L' pl fx fc fy f ∈ H) (hw : ∀ c ∈ w, gen (inv c) = (gen c)⁻¹)
    (h : walkOK fx fc fy inv refs F 0 o 0 1 0 w = true) : evalWord gen w ∈ H := by
  simpa [rep_zero] using walk_mem_of_lt htrue w 1 0 hw h Nat.zero_lt_one

theorem generatorCount_eq : Sporadic.m22Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

private theorem presentation_eq : SporadicName.M22.presentation = Sporadic.m22Presentation := rfl

noncomputable def aElt : Sporadic.m22Presentation.Group := presLetter _ 0

noncomputable def bElt : Sporadic.m22Presentation.Group := presLetter _ 2

theorem presLetter_inv {c : ℕ} (hc : c ≤ 4) :
    presLetter Sporadic.m22Presentation.relatorSet
        (invLetter Sporadic.m22Presentation.generatorCount c) =
      (presLetter Sporadic.m22Presentation.relatorSet c)⁻¹ :=
  presLetter_invLetter _ (by rw [generatorCount_eq]; exact hc)

theorem presLetter_one : presLetter Sporadic.m22Presentation.relatorSet 1 = aElt⁻¹ := by
  have h := presLetter_inv (c := 0) (by norm_num)
  rwa [show invLetter Sporadic.m22Presentation.generatorCount 0 = 1 by
    rw [generatorCount_eq]; rfl] at h

theorem presLetter_three : presLetter Sporadic.m22Presentation.relatorSet 3 = bElt⁻¹ := by
  have h := presLetter_inv (c := 2) (by norm_num)
  rwa [show invLetter Sporadic.m22Presentation.generatorCount 2 = 3 by
    rw [generatorCount_eq]; rfl] at h

theorem presLetter_inv_of_le {w : List ℕ} (hw : ∀ c ∈ w, c ≤ 4) :
    ∀ c ∈ w, presLetter Sporadic.m22Presentation.relatorSet
        (invLetter Sporadic.m22Presentation.generatorCount c) =
      (presLetter Sporadic.m22Presentation.relatorSet c)⁻¹ :=
  fun c hc => presLetter_inv (hw c hc)

theorem codes_relators_eq : codes Sporadic.m22Presentation.relators =
    [[0, 0, 0, 0, 2, 1, 2, 1, 2], [0, 0, 2, 1, 3, 0, 2, 2, 1, 3],
      [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]] := by
  rw [codes_relators, Sporadic.m22Presentation_relatorLetters]
  rfl

theorem relators_evalWord : ∀ r ∈ codes Sporadic.m22Presentation.relators,
    evalWord (presLetter Sporadic.m22Presentation.relatorSet) r = 1 := by
  intro w hw
  simp only [codes, List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [evalWord_presLetter]
  exact PresentedGroup.one_of_mem (relators_mem _ v hv)

theorem relator_one : aElt ^ 4 * bElt * aElt⁻¹ * bElt * aElt⁻¹ * bElt = 1 := by
  have h := relators_evalWord _ (by rw [codes_relators_eq]; exact List.mem_cons_self ..)
  simp only [evalWord_cons, evalWord_nil, presLetter_one, mul_one] at h
  rw [← h]
  simp only [aElt, bElt, pow_succ, pow_zero, one_mul, mul_assoc]

theorem b_pow_eleven : bElt ^ 11 = 1 := by
  have h := relators_evalWord [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] (by rw [codes_relators_eq]; simp)
  simp only [evalWord_cons, evalWord_nil, mul_one] at h
  rw [← h]
  simp only [bElt, pow_succ, pow_zero, one_mul, mul_assoc]

theorem bElt_mem_zpowers : ∀ w ∈ [[2]],
    evalWord (presLetter Sporadic.m22Presentation.relatorSet) w ∈ Subgroup.zpowers bElt := by
  intro w hw
  rw [List.mem_singleton] at hw
  subst hw
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact Subgroup.mem_zpowers bElt

@[expose] def gen (i : ℕ) : Perm (Fin 22) :=
  if i = 0 then
    List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
      List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]
  else if i = 1 then
    List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
      List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]
  else 1

theorem gen_mem (i : ℕ) : gen i ∈ Blueprint.NativeSporadic.M22 := by
  unfold gen
  split
  · exact Subgroup.subset_closure (by simp)
  · split
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _

theorem nativeWord_mem (w : List (ℕ × Bool)) : wordProd gen w ∈ Blueprint.NativeSporadic.M22 :=
  wordProd_mem gen_mem w

@[expose] def alpha : Perm (Fin 22) :=
  List.formPerm [0, 16, 19, 14, 9] * List.formPerm [1, 10, 7, 11, 6] *
    List.formPerm [2, 18, 13, 8, 17] * List.formPerm [3, 4, 5, 12, 15]

@[expose] def beta : Perm (Fin 22) :=
  List.formPerm [0, 6, 1, 11, 20, 16, 17, 14, 13, 8, 7] *
    List.formPerm [2, 5, 12, 15, 9, 10, 19, 4, 21, 18, 3]

theorem alpha_eq : alpha = wordProd gen
    [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)] := by
  decide +kernel

theorem beta_eq : beta = wordProd gen
    [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, false), (0, true)] := by
  decide +kernel

@[expose] noncomputable def img (i : ℕ) : ↥Blueprint.NativeSporadic.M22 :=
  if i = 0 then ⟨alpha, alpha_eq ▸ nativeWord_mem _⟩
  else if i = 1 then ⟨beta, beta_eq ▸ nativeWord_mem _⟩ else 1

theorem img_val (i : ℕ) : ((img i : ↥Blueprint.NativeSporadic.M22) : Perm (Fin 22)) =
    if i = 0 then alpha else if i = 1 then beta else 1 := by
  unfold img
  split
  · rfl
  · split <;> rfl

theorem relators_eval : ∀ v ∈ Sporadic.m22Presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd, Subgroup.coe_one]
  simp only [img_val]
  revert v
  rw [Sporadic.m22Presentation_relatorLetters]
  decide +kernel

noncomputable def toNative : Sporadic.m22Presentation.Group →* ↥Blueprint.NativeSporadic.M22 :=
  presHom _ img relators_eval

theorem toNative_aElt :
    ((toNative aElt : ↥Blueprint.NativeSporadic.M22) : Perm (Fin 22)) = alpha := by
  rw [show aElt = presGen Sporadic.m22Presentation 0 from rfl, toNative,
    presHom_presGen _ img relators_eval (by rw [generatorCount_eq]; norm_num), img_val]
  rfl

theorem toNative_bElt :
    ((toNative bElt : ↥Blueprint.NativeSporadic.M22) : Perm (Fin 22)) = beta := by
  rw [show bElt = presGen Sporadic.m22Presentation 1 from rfl, toNative,
    presHom_presGen _ img relators_eval (by rw [generatorCount_eq]; norm_num), img_val]
  rfl

@[expose] def genWord (i : ℕ) : List (ℕ × Bool) :=
  if i = 0 then
    [(0, true), (1, true), (1, true), (0, true), (0, true), (1, false), (1, false), (0, false),
      (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, false)]
  else
    [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, true)]

theorem gen_eq_wordProd : ∀ i ∈ [0, 1],
    gen i = wordProd (fun j => (img j : Perm (Fin 22))) (genWord i) := by
  simp only [img_val]
  decide +kernel

theorem toNative_surjective : Function.Surjective toNative := by
  have hgen : ∀ i ∈ [0, 1], (⟨gen i, gen_mem i⟩ : ↥Blueprint.NativeSporadic.M22) ∈
      toNative.range := by
    intro i hi
    refine ⟨wordProd (presGen _) (genWord i), ?_⟩
    rw [toNative, presHom_wordProd _ img relators_eval (genWord i) (by
      rw [generatorCount_eq]
      rcases List.mem_pair.mp hi with rfl | rfl <;> decide)]
    exact Subtype.ext (by rw [coe_wordProd]; exact (gen_eq_wordProd i hi).symm)
  intro y
  obtain ⟨y, hy⟩ := y
  suffices H : ∀ z (hz : z ∈ Blueprint.NativeSporadic.M22),
      (⟨z, hz⟩ : ↥Blueprint.NativeSporadic.M22) ∈ toNative.range from H y hy
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact hgen 0 (by simp)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hgen 1 (by simp)
  | one => exact toNative.range.one_mem
  | mul x y hx hy ihx ihy => exact toNative.range.mul_mem ihx ihy
  | inv x hx ih => exact toNative.range.inv_mem ih

theorem pow_eq_one_of_mem_zpowers {u : Sporadic.m22Presentation.Group} {k : ℕ}
    (hmem : u ^ k ∈ Subgroup.zpowers bElt)
    (hc : ∀ r < 11, beta ^ r * (toNative u : Perm (Fin 22)) =
      (toNative u : Perm (Fin 22)) * beta ^ r → r = 0) : u ^ k = 1 := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hr : bElt ^ j = bElt ^ (j % 11).toNat := by
    rw [zpow_eq_zpow_emod' j b_pow_eleven, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))]
    norm_num
  have hr11 : (j % 11).toNat < 11 := by omega
  have hcomm : bElt ^ (j % 11).toNat * u = u * bElt ^ (j % 11).toNat := by
    rw [← hr, hj]
    exact (Commute.pow_self u k).eq
  have h := congrArg (fun g => ((toNative g : ↥Blueprint.NativeSporadic.M22) : Perm (Fin 22))) hcomm
  simp only [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, toNative_bElt] at h
  rw [← hj, hr, hc _ hr11 h, pow_zero]

theorem a_pow_five_mem : aElt ^ 5 ∈ Subgroup.zpowers bElt := by
  have htrue := factElt_mem_of_factsOK (H := Subgroup.zpowers bElt)
    (gen := presLetter Sporadic.m22Presentation.relatorSet)
    (L := 2 * Sporadic.m22Presentation.generatorCount) (N := 5317) (F := 8642)
    (fx := M22Data.PowA.fx) (fc := M22Data.PowA.fc) (fy := M22Data.PowA.fy)
    (kind := M22Data.PowA.kind) (wi := M22Data.PowA.wi) (fs := M22Data.PowA.fs)
    (ft := M22Data.PowA.ft) (fo := M22Data.PowA.fo) (refs := M22Data.PowA.refs)
    (pl := M22Data.PowA.pl) (inv := invLetter Sporadic.m22Presentation.generatorCount)
    (rels := M22Data.PowA.words) (subs := [[2]])
    (fun c hc => presLetter_invLetter _ hc)
    (by rw [generatorCount_eq]; decide +kernel)
    (evalWord_of_derivedOK (presLetter_eps _)
      (fun c hc => presLetter_invLetter _ (Nat.le_of_lt hc)) relators_evalWord
      (by rw [codes_relators_eq, generatorCount_eq]; decide +kernel))
    bElt_mem_zpowers
    (by rw [generatorCount_eq]; exact M22Data.PowA.facts_all)
  have h := evalWord_mem_of_walkOK htrue (w := [0, 0, 0, 0, 0])
    (presLetter_inv_of_le (by decide)) (by rw [generatorCount_eq]; exact M22Data.PowA.close)
  simpa [evalWord, aElt, pow_succ, mul_assoc] using h

theorem a_pow_five : aElt ^ 5 = 1 :=
  pow_eq_one_of_mem_zpowers a_pow_five_mem (by rw [toNative_aElt]; decide +kernel)

theorem ab_inv_pow_three : (aElt * bElt⁻¹) ^ 3 = 1 := by
  calc (aElt * bElt⁻¹) ^ 3 =
        aElt * (aElt ^ 4 * bElt * aElt⁻¹ * bElt * aElt⁻¹ * bElt)⁻¹ * aElt ^ 4 := by
          simp only [pow_succ, pow_zero, one_mul]
          group
    _ = aElt ^ 5 := by rw [relator_one]; group
    _ = 1 := a_pow_five

theorem relatorsA_evalWord :
    ∀ r ∈ codes Sporadic.m22Presentation.relators ++ [[0, 0, 0, 0, 0], [0, 3, 0, 3, 0, 3]],
      evalWord (presLetter Sporadic.m22Presentation.relatorSet) r = 1 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact relators_evalWord r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa [evalWord, aElt, pow_succ, mul_assoc] using a_pow_five
    · simpa [evalWord, presLetter_three, aElt, pow_succ, mul_assoc] using ab_inv_pow_three

theorem abb_pow_five_mem : (aElt * bElt * bElt) ^ 5 ∈ Subgroup.zpowers bElt := by
  have htrue := factElt_mem_of_factsOK (H := Subgroup.zpowers bElt)
    (gen := presLetter Sporadic.m22Presentation.relatorSet)
    (L := 2 * Sporadic.m22Presentation.generatorCount) (N := 2533) (F := 3798)
    (fx := M22Data.PowAbb.fx) (fc := M22Data.PowAbb.fc) (fy := M22Data.PowAbb.fy)
    (kind := M22Data.PowAbb.kind) (wi := M22Data.PowAbb.wi) (fs := M22Data.PowAbb.fs)
    (ft := M22Data.PowAbb.ft) (fo := M22Data.PowAbb.fo) (refs := M22Data.PowAbb.refs)
    (pl := M22Data.PowAbb.pl) (inv := invLetter Sporadic.m22Presentation.generatorCount)
    (rels := M22Data.PowAbb.words) (subs := [[2]])
    (fun c hc => presLetter_invLetter _ hc)
    (by rw [generatorCount_eq]; decide +kernel)
    (evalWord_of_derivedOK (presLetter_eps _)
      (fun c hc => presLetter_invLetter _ (Nat.le_of_lt hc)) relatorsA_evalWord
      (by rw [codes_relators_eq, generatorCount_eq]; decide +kernel))
    bElt_mem_zpowers
    (by rw [generatorCount_eq]; exact M22Data.PowAbb.facts_all)
  have h := evalWord_mem_of_walkOK htrue (w := [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2])
    (presLetter_inv_of_le (by decide)) (by rw [generatorCount_eq]; exact M22Data.PowAbb.close)
  simpa [evalWord, aElt, bElt, pow_succ, mul_assoc] using h

theorem abb_pow_five : (aElt * bElt * bElt) ^ 5 = 1 :=
  pow_eq_one_of_mem_zpowers abb_pow_five_mem (by
    simp only [map_mul, Subgroup.coe_mul, toNative_aElt, toNative_bElt]
    decide +kernel)

theorem relatorsAbb_evalWord : ∀ r ∈ codes Sporadic.m22Presentation.relators ++
    [[0, 0, 0, 0, 0], [0, 3, 0, 3, 0, 3], [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2]],
    evalWord (presLetter Sporadic.m22Presentation.relatorSet) r = 1 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact relators_evalWord r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa [evalWord, aElt, pow_succ, mul_assoc] using a_pow_five
    · simpa [evalWord, presLetter_three, aElt, pow_succ, mul_assoc] using ab_inv_pow_three
    · simpa [evalWord, aElt, bElt, pow_succ, mul_assoc] using abb_pow_five

theorem index_le :
    (Subgroup.zpowers bElt).FiniteIndex ∧ (Subgroup.zpowers bElt).index ≤ 40320 := by
  have h := index_le_of_facts (H := Subgroup.zpowers bElt)
    (gen := presLetter Sporadic.m22Presentation.relatorSet)
    (L := 2 * Sporadic.m22Presentation.generatorCount) (N := 40460) (F := 81016)
    (fx := M22Data.fx) (fc := M22Data.fc) (fy := M22Data.fy)
    (kind := M22Data.kind) (wi := M22Data.wi) (fs := M22Data.fs) (ft := M22Data.ft)
    (fo := M22Data.fo) (refs := M22Data.refs) (pl := M22Data.pl) (ffi := M22Data.ffi)
    (inv := invLetter Sporadic.m22Presentation.generatorCount) (live := M22Data.live)
    (rels := M22Data.words) (subs := [[2]])
    (closure_presLetter _) (fun c hc => presLetter_invLetter _ hc)
    (fun c hc => invLetter_lt hc)
    (by rw [generatorCount_eq]; decide +kernel)
    (evalWord_of_derivedOK (presLetter_eps _)
      (fun c hc => presLetter_invLetter _ (Nat.le_of_lt hc)) relatorsAbb_evalWord
      (by rw [codes_relators_eq, generatorCount_eq]; decide +kernel))
    bElt_mem_zpowers M22Data.live_zero (by norm_num)
    (by rw [generatorCount_eq]; exact M22Data.facts_all)
    (by rw [generatorCount_eq]; exact M22Data.cover_all)
  rw [M22Data.liveCount_eq] at h
  exact h

theorem finite_card_le :
    Finite Sporadic.m22Presentation.Group ∧ Nat.card Sporadic.m22Presentation.Group ≤ 443520 :=
  finite_card_le_of_zpowers bElt (k := 11) (n := 40320) (by norm_num) b_pow_eleven
    index_le.1 index_le.2

theorem tauCeti_finite_card_le :
    Finite SporadicName.M22.Group ∧ Nat.card SporadicName.M22.Group ≤ 443520 := by
  show Finite SporadicName.M22.presentation.Group ∧
    Nat.card SporadicName.M22.presentation.Group ≤ 443520
  rw [presentation_eq]
  exact finite_card_le

@[expose] def witnesses0 : List (Fin 22 × List (ℕ × Bool)) :=
  [(0, []),
    (12, [(0, true)]),
    (20, [(1, false)]),
    (21, [(1, true)]),
    (1, [(1, true), (0, true)]),
    (2, [(1, true), (1, true)]),
    (3, [(1, false), (0, true)]),
    (5, [(0, true), (1, true)]),
    (7, [(0, true), (1, true), (0, true)]),
    (10, [(1, true), (0, true), (1, true)]),
    (11, [(0, true), (1, false), (0, true)]),
    (14, [(1, false), (0, true), (1, true)]),
    (15, [(0, true), (1, true), (1, true)]),
    (17, [(1, true), (1, true), (0, true)]),
    (4, [(1, true), (0, true), (1, false), (0, true)]),
    (6, [(1, true), (1, true), (0, true), (1, true)]),
    (9, [(1, false), (0, true), (1, true), (0, true)]),
    (13, [(0, true), (1, true), (0, true), (1, true)]),
    (8, [(0, true), (1, false), (0, true), (1, true), (0, true)]),
    (16, [(0, true), (1, true), (1, true), (0, true), (1, true)]),
    (19, [(1, true), (0, true), (1, true), (0, true), (1, true)]),
    (18, [(1, true), (0, true), (1, true), (1, true), (0, true), (1, true)])]

@[expose] def witnesses1 : List (Fin 22 × List (ℕ × Bool)) :=
  [(1, []),
    (21, [(1, true), (0, true), (1, false)]),
    (4, [(1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]),
    (5, [(1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true)]),
    (3, [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (12, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]),
    (15, [(1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, false)]),
    (16, [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true)]),
    (17, [(1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, false)]),
    (6, [(1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, false)]),
    (8, [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
      (0, true)]),
    (13, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, false)]),
    (20, [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, false)]),
    (2, [(1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, false)]),
    (19, [(1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false),
      (0, true), (1, false)]),
    (7, [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, true)]),
    (14, [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (1, true), (0, true), (1, false)]),
    (11, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (0, true)]),
    (18, [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (0, true), (1, false), (0, true)]),
    (9, [(1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (0, true)]),
    (10, [(1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (1, true), (0, true), (1, false)])]

@[expose] def witnesses2 : List (Fin 22 × List (ℕ × Bool)) :=
  [(2, []),
    (12, [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true)]),
    (7, [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true)]),
    (3, [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true)]),
    (13, [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (1, true), (0, true)]),
    (19, [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true)]),
    (5, [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, true)]),
    (18, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, true)]),
    (9, [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true)]),
    (4, [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, false)]),
    (10, [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true)]),
    (11, [(1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (1, true)]),
    (6, [(1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true)]),
    (14, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true)]),
    (15, [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false)]),
    (16, [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false)]),
    (17, [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false)]),
    (20, [(1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true)]),
    (21, [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, true)]),
    (8, [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true)])]

@[expose] def witnesses3 : List (Fin 22 × List (ℕ × Bool)) :=
  [(3, []),
    (14, [(1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (1, true), (0, true), (1, true)]),
    (5, [(1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false)]),
    (8, [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false)]),
    (10, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (1, true)]),
    (18, [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (1, true), (0, true)]),
    (7, [(1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, true)]),
    (13, [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (1, true), (0, true)]),
    (4, [(1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false)]),
    (11, [(1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true)]),
    (15, [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (16, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true)]),
    (21, [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]),
    (12, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]),
    (6, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true)]),
    (20, [(1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true)])]

@[expose] def witnesses4 : List (Fin 22 × List (ℕ × Bool)) :=
  [(4, []),
    (15, [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, false), (0, true), (1, true)]),
    (16, [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true)])]

@[expose] noncomputable def stab1 : Subgroup (Perm (Fin 22)) :=
  Blueprint.NativeSporadic.M22 ⊓ MulAction.stabilizer (Perm (Fin 22)) (0 : Fin 22)
@[expose] noncomputable def stab2 : Subgroup (Perm (Fin 22)) :=
  stab1 ⊓ MulAction.stabilizer (Perm (Fin 22)) (1 : Fin 22)
@[expose] noncomputable def stab3 : Subgroup (Perm (Fin 22)) :=
  stab2 ⊓ MulAction.stabilizer (Perm (Fin 22)) (2 : Fin 22)
@[expose] noncomputable def stab4 : Subgroup (Perm (Fin 22)) :=
  stab3 ⊓ MulAction.stabilizer (Perm (Fin 22)) (3 : Fin 22)
@[expose] noncomputable def stab5 : Subgroup (Perm (Fin 22)) :=
  stab4 ⊓ MulAction.stabilizer (Perm (Fin 22)) (4 : Fin 22)

theorem witnesses_ok0 : ∀ x ∈ witnesses0, wordProd gen x.2 (0 : Fin 22) = x.1 := by
  decide +kernel
theorem witnesses_ok1 : ∀ x ∈ witnesses1,
    wordProd gen x.2 (0 : Fin 22) = 0 ∧ wordProd gen x.2 (1 : Fin 22) = x.1 := by
  decide +kernel
theorem witnesses_ok2 : ∀ x ∈ witnesses2, wordProd gen x.2 (0 : Fin 22) = 0 ∧
    wordProd gen x.2 (1 : Fin 22) = 1 ∧ wordProd gen x.2 (2 : Fin 22) = x.1 := by
  decide +kernel
theorem witnesses_ok3 : ∀ x ∈ witnesses3, wordProd gen x.2 (0 : Fin 22) = 0 ∧
    wordProd gen x.2 (1 : Fin 22) = 1 ∧ wordProd gen x.2 (2 : Fin 22) = 2 ∧
    wordProd gen x.2 (3 : Fin 22) = x.1 := by
  decide +kernel
theorem witnesses_ok4 : ∀ x ∈ witnesses4, wordProd gen x.2 (0 : Fin 22) = 0 ∧
    wordProd gen x.2 (1 : Fin 22) = 1 ∧ wordProd gen x.2 (2 : Fin 22) = 2 ∧
    wordProd gen x.2 (3 : Fin 22) = 3 ∧ wordProd gen x.2 (4 : Fin 22) = x.1 := by
  decide +kernel

theorem witnesses_nodup : (witnesses0.map Prod.fst).Nodup ∧ (witnesses1.map Prod.fst).Nodup ∧
    (witnesses2.map Prod.fst).Nodup ∧ (witnesses3.map Prod.fst).Nodup ∧
    (witnesses4.map Prod.fst).Nodup := by
  decide +kernel

theorem witnesses_length : witnesses0.length = 22 ∧ witnesses1.length = 21 ∧
    witnesses2.length = 20 ∧ witnesses3.length = 16 ∧ witnesses4.length = 3 := by
  decide +kernel

theorem le_card_native : 443520 ≤ Nat.card Blueprint.NativeSporadic.M22 := by
  have h0 := le_card_of_witnesses (K := Blueprint.NativeSporadic.M22) gen 0 witnesses0
    (fun x _ => nativeWord_mem x.2) (fun x hx => witnesses_ok0 x hx) witnesses_nodup.1
  have h1 := le_card_of_witnesses (K := stab1) gen 1 witnesses1
    (fun x hx => ⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok1 x hx).1⟩)
    (fun x hx => (witnesses_ok1 x hx).2) witnesses_nodup.2.1
  have h2 := le_card_of_witnesses (K := stab2) gen 2 witnesses2
    (fun x hx => ⟨⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok2 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok2 x hx).2.1⟩)
    (fun x hx => (witnesses_ok2 x hx).2.2) witnesses_nodup.2.2.1
  have h3 := le_card_of_witnesses (K := stab3) gen 3 witnesses3
    (fun x hx => ⟨⟨⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok3 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok3 x hx).2.1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok3 x hx).2.2.1⟩)
    (fun x hx => (witnesses_ok3 x hx).2.2.2) witnesses_nodup.2.2.2.1
  have h4 := le_card_of_witnesses (K := stab4) gen 4 witnesses4
    (fun x hx => ⟨⟨⟨⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).2.1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).2.2.1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).2.2.2.1⟩)
    (fun x hx => (witnesses_ok4 x hx).2.2.2.2) witnesses_nodup.2.2.2.2
  obtain ⟨l0, l1, l2, l3, l4⟩ := witnesses_length
  rw [l0] at h0; rw [l1] at h1; rw [l2] at h2; rw [l3] at h3; rw [l4] at h4
  have h5 : 1 ≤ Nat.card ↥stab5 := Nat.card_pos
  change 22 * Nat.card ↥stab1 ≤ Nat.card ↥Blueprint.NativeSporadic.M22 at h0
  change 21 * Nat.card ↥stab2 ≤ Nat.card ↥stab1 at h1
  change 20 * Nat.card ↥stab3 ≤ Nat.card ↥stab2 at h2
  change 16 * Nat.card ↥stab4 ≤ Nat.card ↥stab3 at h3
  change 3 * Nat.card ↥stab5 ≤ Nat.card ↥stab4 at h4
  omega

theorem nonempty_mulEquiv :
    Nonempty (↥Blueprint.NativeSporadic.M22 ≃* SporadicName.M22.Group) := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  show Nonempty (↥Blueprint.NativeSporadic.M22 ≃* SporadicName.M22.presentation.Group)
  rw [presentation_eq]
  exact nonempty_mulEquiv_of_surjective toNative toNative_surjective hcard le_card_native

end CFSG.Sporadic.Bridge.M22
