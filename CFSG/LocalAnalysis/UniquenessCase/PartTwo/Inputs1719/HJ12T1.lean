module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Spec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Objects
public import CFSG.Quasithin.Background.B6Basic

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.StepA (mulR idR Realizable linOfRows_mulR linOfRows_idR)
open CFSG.GF2Type.Smith1979.GammaU.Viol
open CFSG.GF2Type.Smith1979.GammaU.SigmaP (gensOK_spec)
open HJBridge (grpOf)
open CFSG.Sporadic.J2.Module12 (A12 B12)
open HJ12 (wordR hjTauc hjAc hjBc isInvol)

def e16Test (invs : List (Array ℕ)) (t : Array ℕ) : Bool :=
  (invs.filter fun s => s != t && HJ12.commR s t).any fun s =>
    (invs.filter fun s => s != t && HJ12.commR s t).any fun r =>
      !([idR, t, s, mulR t s].contains r) && HJ12.commR r s &&
        (invs.filter fun s => s != t && HJ12.commR s t).any fun q =>
          !(([idR, t, s, mulR t s] ++
            [idR, t, s, mulR t s].map (fun y => mulR y r)).contains q) &&
            HJ12.commR q s && HJ12.commR q r

theorem e16Test_eq_true {invs : List (Array ℕ)} {t s r q : Array ℕ}
    (hs : s ∈ invs) (hst : (s != t && HJ12.commR s t) = true)
    (hr : r ∈ invs) (hrt : (r != t && HJ12.commR r t) = true)
    (hr2 : (!([idR, t, s, mulR t s]).contains r && HJ12.commR r s) = true)
    (hq : q ∈ invs) (hqt : (q != t && HJ12.commR q t) = true)
    (hq3 : (!(([idR, t, s, mulR t s] ++
        [idR, t, s, mulR t s].map (fun y => mulR y r)).contains q) &&
        HJ12.commR q s && HJ12.commR q r) = true) :
    e16Test invs t = true := by
  simp only [e16Test, List.any_eq_true]
  refine ⟨s, List.mem_filter.2 ⟨hs, hst⟩, r, List.mem_filter.2 ⟨hr, hrt⟩, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨hr2, ?_⟩
  rw [List.any_eq_true]
  exact ⟨q, List.mem_filter.2 ⟨hq, hqt⟩, hq3⟩

theorem grpOf_append_singleton {gs : List (Array ℕ)} {x : MulAut W12} {r : Array ℕ}
    (hx : HJBridge.RowsOf x r) (hok : Realizable r) :
    grpOf (gs ++ [r]) = grpOf gs ⊔ Subgroup.closure {x} := by
  have hsingle : grpOf [r] = Subgroup.closure {x} :=
    HJBridge.grpOf_eq_closure
      (h1 := fun g hg => by rw [List.mem_singleton] at hg; subst hg; exact ⟨x, rfl, hx⟩)
      (h2 := fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨r, List.mem_singleton_self r, hx⟩)
      (hok := fun g hg => by rw [List.mem_singleton] at hg; subst hg; exact hok)
  rw [HJBridge.grpOf_append_eq_sup, hsingle]

theorem gensOK_append_left {gs hs : List (Array ℕ)} (h : SigmaP.gensOK (gs ++ hs) = true) :
    SigmaP.gensOK gs = true := by
  simp only [SigmaP.gensOK, List.all_eq_true] at h ⊢
  exact fun g hg => h g (List.mem_append_left hs hg)

theorem gensOK_append_right {gs hs : List (Array ℕ)} (h : SigmaP.gensOK (gs ++ hs) = true) :
    SigmaP.gensOK hs = true := by
  simp only [SigmaP.gensOK, List.all_eq_true] at h ⊢
  exact fun g hg => h g (List.mem_append_right gs hg)

private theorem hjE16_aux :
    ∀ A : Subgroup (MulAut W12), A ≤ hjT1 → IsElemAbelian2 A →
      Nat.card A ≤ 16 ∧ (Nat.card A = 16 → A = hjA1 ∨ A = hjA2) := by
  classical
  have : Finite (MulAut W12) :=
    Finite.of_injective (fun e : MulAut W12 => (e : W12 → W12))
      (fun a b h => MulEquiv.ext (congrFun h))
  have h1 : HJ12.hjT1Check = true := HJ12.hjT1Check_eq
  simp only [HJ12.hjT1Check, HJ12.gensL, Bool.and_eq_true, gensOKN_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_orbitOf] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg1, hga⟩, _⟩, hc1⟩, _⟩, _⟩, hca1⟩, hca2⟩, h16a⟩, h16b⟩,
    hall1⟩, hall2⟩, hcomm1⟩, hcomm2⟩, _⟩, he16⟩, _⟩ := h1
  have hga1 : SigmaP.gensOK (HJ12.hj_a1Words.map wordR) = true := gensOK_append_left hga
  have hga2 : SigmaP.gensOK (HJ12.hj_a2Words.map wordR) = true := gensOK_append_right hga
  have hA1card : Nat.card hjA1 = 16 := by
    rw [hjA1, HJBridge.card_grpOf_eq hga1 hca1, beq_iff_eq.mp h16a]
  have hA2card : Nat.card hjA2 = 16 := by
    rw [hjA2, HJBridge.card_grpOf_eq hga2 hca2, beq_iff_eq.mp h16b]
  intro A hAT hAel
  by_cases h16 : 16 ≤ Nat.card A
  · have hrowsX : ∀ a : MulAut W12, a ∈ A → ∃ r ∈ Enum.enumGrp
        (HJ12.hj_t0Words.map wordR ++ [hjTauc]), HJBridge.RowsOf a r :=
      fun a ha => (HJBridge.mem_grpOf_iff hg1 hc1 a).1 (hAT ha)
    set invs : List (Array ℕ) :=
      (Enum.enumGrp (HJ12.hj_t0Words.map wordR ++ [hjTauc])).filter HJ12.isInvol
      with hinvs
    let rowOf : ↥A → Array ℕ := fun a => (hrowsX a.1 a.2).choose
    have hmem : ∀ a : ↥A, rowOf a ∈ Enum.enumGrp
        (HJ12.hj_t0Words.map wordR ++ [hjTauc]) := fun a => (hrowsX a.1 a.2).choose_spec.1
    have hrow : ∀ a : ↥A, HJBridge.RowsOf (a : MulAut W12) (rowOf a) :=
      fun a => (hrowsX a.1 a.2).choose_spec.2
    have hcan : ∀ a : ↥A, (rowOf a).size = 12 ∧ ∀ y ∈ rowOf a, y < 4096 :=
      fun a => canon_of_mem_enumGrp hg1 (hmem a)
    have hinj : Function.Injective rowOf := by
      intro a b hab
      exact Subtype.ext (HJBridge.rowsOf_unique (hrow a) (hab ▸ hrow b))
    have hone : rowOf 1 = idR :=
      rows_eq_of_rowsOf (hrow 1) HJBridge.rowsOf_one (hcan 1) ⟨rfl, by decide⟩
    have hmulR : ∀ a b : ↥A, mulR (rowOf a) (rowOf b) = rowOf (a * b) := by
      intro a b
      refine rows_eq_of_rowsOf (HJBridge.rowsOf_mul (hrow a) (hrow b)) (hrow (a * b))
        ⟨?_, lt_of_mem_mulR (hcan a).2⟩ (hcan (a * b))
      rw [size_mulR, (hcan b).1]
    have hsq : ∀ a : ↥A, mulR (rowOf a) (rowOf a) = idR := by
      intro a
      have h : (a * a : ↥A) = 1 := Subtype.ext (by rw [← pow_two]; exact hAel.2 a.1 a.2)
      rw [hmulR a a, h, hone]
    have hcommR : ∀ a b : ↥A, HJ12.commR (rowOf a) (rowOf b) = true := by
      intro a b
      simp only [HJ12.commR, CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR, beq_iff_eq]
      have h : (a * b : ↥A) = b * a := Subtype.ext (hAel.1 a.1 a.2 b.1 b.2)
      rw [hmulR a b, hmulR b a, h]
    have hne : ∀ a : ↥A, a ≠ 1 → rowOf a ≠ idR := by
      intro a ha h
      exact ha (hinj (by rw [h, hone]))
    have huniv : (Finset.univ : Finset ↥A).card = Nat.card A := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    have hmem_invs : ∀ a : ↥A, a ≠ 1 → rowOf a ∈ invs := by
      intro a ha
      rw [hinvs]
      simp only [List.mem_filter, HJ12.isInvol, Bool.and_eq_true, bne_iff_ne, ne_eq,
        beq_iff_eq, CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
        CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR]
      exact ⟨hmem a, hne a ha, hsq a⟩
    have key : ∀ t : ↥A, t ≠ 1 → e16Test invs (rowOf t) = true := by
      intro t ht1
      have hcard2 : ({1, t} : Finset ↥A).card < (Finset.univ : Finset ↥A).card := by
        rw [huniv]
        have := Finset.card_le_two (a := (1 : ↥A)) (b := t)
        omega
      obtain ⟨s, -, hsnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hsnot
      obtain ⟨hs1, hst⟩ := hsnot
      have hcard4 : ({1, t, s, t * s} : Finset ↥A).card <
          (Finset.univ : Finset ↥A).card := by
        rw [huniv]
        have := Finset.card_le_four (a := (1 : ↥A)) (b := t) (c := s) (d := t * s)
        omega
      obtain ⟨r, -, hrnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard4
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrnot
      obtain ⟨hr1, hrt, hrs, hrts⟩ := hrnot
      set B4 : Finset ↥A := {1, t, s, t * s} with hB4
      have hcard8 : (B4 ∪ B4.image (fun y => y * r)).card <
          (Finset.univ : Finset ↥A).card := by
        rw [huniv]
        have h1 : (B4 ∪ B4.image (fun y => y * r)).card ≤
            B4.card + (B4.image (fun y => y * r)).card := Finset.card_union_le _ _
        have h2 : (B4.image (fun y => y * r)).card ≤ B4.card := Finset.card_image_le
        have h3 : B4.card ≤ 4 := by rw [hB4]; exact Finset.card_le_four
        omega
      obtain ⟨q, -, hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard8
      rw [Finset.mem_union, not_or] at hqnot
      obtain ⟨hqB4, hqimg⟩ := hqnot
      rw [hB4] at hqB4
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqB4
      obtain ⟨hq1, hqt, hqs, hqts⟩ := hqB4
      simp only [Finset.mem_image, not_exists, not_and] at hqimg
      have hrq : r ≠ q := by
        have h := hqimg 1 (by rw [hB4]; simp)
        rwa [one_mul] at h
      have htrq : t * r ≠ q := hqimg t (by rw [hB4]; simp)
      have hsrq : s * r ≠ q := hqimg s (by rw [hB4]; simp)
      have htsrq : (t * s) * r ≠ q := hqimg (t * s) (by rw [hB4]; simp)
      have hstC : (rowOf s != rowOf t && HJ12.commR (rowOf s) (rowOf t)) = true := by
        rw [hcommR s t, Bool.and_true]
        exact bne_iff_ne.mpr (fun h => hst (hinj h))
      have hrtC : (rowOf r != rowOf t && HJ12.commR (rowOf r) (rowOf t)) = true := by
        rw [hcommR r t, Bool.and_true]
        exact bne_iff_ne.mpr (fun h => hrt (hinj h))
      have hqC : (rowOf q != rowOf t && HJ12.commR (rowOf q) (rowOf t)) = true := by
        rw [hcommR q t, Bool.and_true]
        exact bne_iff_ne.mpr (fun h => hqt (hinj h))
      have hnot2 : rowOf r ∉ [idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h | h)
        · exact hr1 (hinj (by rw [h, hone]))
        · exact hrt (hinj h)
        · exact hrs (hinj h)
        · exact hrts (hinj (h.trans (hmulR t s)))
      have hr2C : (!([idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)]).contains
          (rowOf r) && HJ12.commR (rowOf r) (rowOf s)) = true := by
        have hc : ([idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)]).contains
            (rowOf r) = false := by
          cases h : ([idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)]).contains (rowOf r)
          · rfl
          · exact absurd (List.contains_iff_mem.1 h) hnot2
        simp only [hc, Bool.not_false, Bool.true_and, hcommR r s]
      have hnot3 : rowOf q ∉ [idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)] ++
          [idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)].map
            (fun y => mulR y (rowOf r)) := by
        rw [List.mem_append, not_or]
        constructor
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | h | h | h)
          · exact hq1 (hinj (by rw [h, hone]))
          · exact hqt (hinj h)
          · exact hqs (hinj h)
          · exact hqts (hinj (h.trans (hmulR t s)))
        · simp only [List.mem_map, not_exists, not_and]
          rintro y hy h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · rw [← hone, hmulR 1 r, one_mul] at h; exact hrq (hinj h)
          · rw [hmulR t r] at h; exact htrq (hinj h)
          · rw [hmulR s r] at h; exact hsrq (hinj h)
          · rw [hmulR t s, hmulR (t * s) r] at h; exact htsrq (hinj h)
      have hq3C : (!(([idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)] ++
          [idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)].map
            (fun y => mulR y (rowOf r))).contains (rowOf q)) &&
          HJ12.commR (rowOf q) (rowOf s) && HJ12.commR (rowOf q) (rowOf r)) = true := by
        have hc : ([idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)] ++
            [idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)].map
              (fun y => mulR y (rowOf r))).contains (rowOf q) = false := by
          cases h : ([idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)] ++
              [idR, rowOf t, rowOf s, mulR (rowOf t) (rowOf s)].map
                (fun y => mulR y (rowOf r))).contains (rowOf q)
          · rfl
          · exact absurd (List.contains_iff_mem.1 h) hnot3
        simp only [hc, Bool.not_false, Bool.true_and, hcommR q s, hcommR q r]
      exact e16Test_eq_true (invs := invs) (hmem_invs s hs1) hstC (hmem_invs r hr1)
        hrtC hr2C (hmem_invs q hq1) hqC hq3C
    have hsubset : (A : Set (MulAut W12)) ⊆ (hjA1 : Set (MulAut W12)) ∪
        (hjA2 : Set (MulAut W12)) := by
      intro x hxA
      by_cases hx1 : x = 1
      · exact Or.inl (by rw [hx1]; exact one_mem hjA1)
      · let x0 : ↥A := ⟨x, hxA⟩
        have hx0ne : x0 ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
        have hx1inv : rowOf x0 ∈ invs := hmem_invs x0 hx0ne
        by_cases hA1x : rowOf x0 ∈ Enum.enumGrp (HJ12.hj_a1Words.map wordR)
        · exact Or.inl ((HJBridge.mem_grpOf_iff hga1 hca1 x).2 ⟨rowOf x0, hA1x, hrow x0⟩)
        by_cases hA2x : rowOf x0 ∈ Enum.enumGrp (HJ12.hj_a2Words.map wordR)
        · exact Or.inr ((HJBridge.mem_grpOf_iff hga2 hca2 x).2 ⟨rowOf x0, hA2x, hrow x0⟩)
        · exfalso
          have hfilter : rowOf x0 ∈ invs.filter (fun y =>
              !(Enum.enumGrp (HJ12.hj_a1Words.map wordR)).contains y &&
                !(Enum.enumGrp (HJ12.hj_a2Words.map wordR)).contains y) := by
            have h1 : (Enum.enumGrp (HJ12.hj_a1Words.map wordR)).contains
                (rowOf x0) = false := by
              cases h : (Enum.enumGrp (HJ12.hj_a1Words.map wordR)).contains (rowOf x0)
              · rfl
              · exact absurd (List.contains_iff_mem.1 h) hA1x
            have h2 : (Enum.enumGrp (HJ12.hj_a2Words.map wordR)).contains
                (rowOf x0) = false := by
              cases h : (Enum.enumGrp (HJ12.hj_a2Words.map wordR)).contains (rowOf x0)
              · rfl
              · exact absurd (List.contains_iff_mem.1 h) hA2x
            refine List.mem_filter.2 ⟨hx1inv, ?_⟩
            simp only [h1, h2, Bool.not_false, Bool.true_and]
          have hfalse : e16Test invs (rowOf x0) = false := by
            have h := List.all_eq_true.1 he16 (rowOf x0) hfilter
            simpa only [e16Test, Bool.not_eq_true_eq_eq_false,
              CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
              CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] using h
          rw [key x0 hx0ne] at hfalse
          exact absurd hfalse (by decide)
    rcases SubgroupClass.subset_union.1 hsubset with hle | hle
    · refine ⟨?_, ?_⟩
      · rw [← hA1card]
        exact Subgroup.card_le_of_le hle
      · intro hcard
        exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA1card]))
    · refine ⟨?_, ?_⟩
      · rw [← hA2card]
        exact Subgroup.card_le_of_le hle
      · intro hcard
        exact Or.inr (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA2card]))
  · refine ⟨by omega, fun hcard => ?_⟩
    exact absurd hcard (by omega)

theorem hjT1_facts :
    hjTau ∈ Subgroup.normalizer (hjL0 : Set (MulAut W12)) ∧ hjT0 ≤ hjL0 ∧ hjT0 ≤ hjT1 ∧
      hjT1 ≤ Subgroup.normalizer (hjL0 : Set (MulAut W12)) ∧ Nat.card hjT0 = 2 ^ 7 ∧
      Nat.card hjT1 = 2 ^ 8 ∧ hjA1 ≤ hjT0 ∧ hjA2 ≤ hjT0 ∧
      (∀ A : Subgroup (MulAut W12), A ≤ hjT1 → IsElemAbelian2 A →
        Nat.card A ≤ 16 ∧ (Nat.card A = 16 → A = hjA1 ∨ A = hjA2)) ∧
      thompsonJ hjT1 = hjA1 ⊔ hjA2 := by
  classical
  have : Finite (MulAut W12) :=
    Finite.of_injective (fun e : MulAut W12 => (e : W12 → W12))
      (fun a b h => MulEquiv.ext (congrFun h))
  have h1 : HJ12.hjT1Check = true := HJ12.hjT1Check_eq
  simp only [HJ12.hjT1Check, HJ12.gensL, Bool.and_eq_true, gensOKN_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_orbitOf] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg1, hga⟩, hc0⟩, hc1⟩, h128⟩, h256⟩, hca1⟩, hca2⟩, h16a⟩, h16b⟩,
    hall1⟩, hall2⟩, hcomm1⟩, hcomm2⟩, _⟩, he16⟩, _⟩ := h1
  have h2 : HJ12.hjTauCheck = true := HJ12.hjTauCheck_eq
  simp only [HJ12.hjTauCheck, Bool.and_eq_true, beq_iff_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR,
    CFSG.GF2Type.Smith1979.GammaU.native_invR] at h2
  have hτA := h2.1.2
  have hτB := h2.2
  have hgs1 : GensOK (HJ12.hj_t0Words.map wordR ++ [hjTauc]) := gensOK_spec hg1
  have hgs0 : SigmaP.gensOK (HJ12.hj_t0Words.map wordR) = true := gensOK_append_left hg1
  have hga1 : SigmaP.gensOK (HJ12.hj_a1Words.map wordR) = true := gensOK_append_left hga
  have hga2 : SigmaP.gensOK (HJ12.hj_a2Words.map wordR) = true := gensOK_append_right hga
  have hgsτ : GensOK [hjTauc] := by
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact hgs1 hjTauc (List.mem_append_right _ (List.mem_singleton_self _))
  have hτcan : HJBridge.RowsOf hjTau hjTauc := by
    intro v
    rw [hjTau, hjAct_apply, ← HJBridge.linOfRows_hjTauc]
  have hτi : HJBridge.RowsOf hjTau⁻¹ (invR hjTauc) :=
    HJBridge.rowsOf_inv hτcan (hgsτ hjTauc (List.mem_singleton_self hjTauc)).2.2.1
  have hτreal : Realizable hjTauc := by
    have h := hgsτ hjTauc (List.mem_singleton_self _)
    exact ⟨okRows_spec h.1, eqvOf _ _ h.2.2.1 h.2.2.2, fun y => eqvOf_apply _ _ _ _ y⟩
  have hrowA : HJBridge.RowsOf (hjAct A12) hjAc := by simpa using HJBridge.rowsOf_gen 0
  have hrowB : HJBridge.RowsOf (hjAct B12) hjBc := by simpa using HJBridge.rowsOf_gen 1
  have hconjA : hjTau * hjAct A12 * hjTau⁻¹ =
      hjWord (HJ12.hj_tauConjWords.headD []) := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_mul hτcan hrowA) hτi
    rw [hτA] at h; exact HJBridge.rowsOf_unique h (HJBridge.rowsOf_hjWord _)
  have hconjB : hjTau * hjAct B12 * hjTau⁻¹ =
      hjWord (HJ12.hj_tauConjWords.getD 1 []) := by
    have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_mul hτcan hrowB) hτi
    rw [hτB] at h; exact HJBridge.rowsOf_unique h (HJBridge.rowsOf_hjWord _)
  have map_conj_eq : ∀ (H : Subgroup (MulAut W12)) (g : MulAut W12),
      H.map (MulAut.conj g) ≤ H → H.map (MulAut.conj g) = H := by
    intro H g hle
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hτN : hjTau ∈ Subgroup.normalizer (hjL0 : Set (MulAut W12)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine map_conj_eq hjL0 hjTau ?_
    rw [hjL0, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · show MulAut.conj hjTau (hjAct A12) ∈ hjL0
      rw [MulAut.conj_apply, hconjA]; exact hjWord_mem _
    · show MulAut.conj hjTau (hjAct B12) ∈ hjL0
      rw [MulAut.conj_apply, hconjB]; exact hjWord_mem _
  have hT0L : hjT0 ≤ hjL0 := by
    rw [hjT0, HJBridge.grpOf_words]
    exact (Subgroup.closure_le hjL0).2 (by rintro _ ⟨w, -, rfl⟩; exact hjWord_mem w)
  have hT1eq : hjT1 = hjT0 ⊔ Subgroup.closure {hjTau} :=
    grpOf_append_singleton hτcan hτreal
  have hT0T1 : hjT0 ≤ hjT1 := by
    rw [hT1eq]
    exact le_sup_left
  have hT1N : hjT1 ≤ Subgroup.normalizer (hjL0 : Set (MulAut W12)) := by
    rw [hT1eq]
    refine sup_le (hT0L.trans Subgroup.le_normalizer) ?_
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hτN
  have hcardT0 : Nat.card hjT0 = 2 ^ 7 := by
    rw [hjT0, HJBridge.card_grpOf_eq hgs0 hc0, beq_iff_eq.mp h128]; norm_num
  have hcardT1 : Nat.card hjT1 = 2 ^ 8 := by
    rw [hjT1, HJBridge.card_grpOf_eq hg1 hc1, beq_iff_eq.mp h256]; norm_num
  have hA1T0 : hjA1 ≤ hjT0 := by
    intro t ht
    obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hga1 hca1 t).1 ht
    have h := List.all_eq_true.1 hall1 r hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact (HJBridge.mem_grpOf_iff hgs0 hc0 t).2 ⟨r, List.contains_iff_mem.1 h.1, htr⟩
  have hA2T0 : hjA2 ≤ hjT0 := by
    intro t ht
    obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hga2 hca2 t).1 ht
    have h := List.all_eq_true.1 hall2 r hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact (HJBridge.mem_grpOf_iff hgs0 hc0 t).2 ⟨r, List.contains_iff_mem.1 h.1, htr⟩
  have hA1el : IsElemAbelian 2 hjA1 := by
    have hsq : ∀ a ∈ hjA1, a ^ 2 = 1 := by
      intro a ha
      obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hga1 hca1 a).1 ha
      have h := List.all_eq_true.1 hall1 r hr
      simp only [Bool.and_eq_true, beq_iff_eq,
        CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
        CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] at h
      rw [pow_two]
      have hp := HJBridge.rowsOf_mul htr htr
      rw [h.2] at hp
      exact HJBridge.rowsOf_unique hp HJBridge.rowsOf_one
    refine B6.isElemAbelian_iff.mpr ⟨fun a ha b hb => ?_, hsq⟩
    obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hga1 hca1 a).1 ha
    obtain ⟨s, hs, hts⟩ := (HJBridge.mem_grpOf_iff hga1 hca1 b).1 hb
    have h := List.all_eq_true.1 hcomm1 r hr
    have h2 := List.all_eq_true.1 h s hs
    simp only [HJ12.commR, CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
      beq_iff_eq] at h2
    have hp := HJBridge.rowsOf_mul htr hts
    have hp' := HJBridge.rowsOf_mul hts htr
    rw [h2] at hp
    exact HJBridge.rowsOf_unique hp hp'
  have hA2el : IsElemAbelian 2 hjA2 := by
    have hsq : ∀ a ∈ hjA2, a ^ 2 = 1 := by
      intro a ha
      obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hga2 hca2 a).1 ha
      have h := List.all_eq_true.1 hall2 r hr
      simp only [Bool.and_eq_true, beq_iff_eq,
        CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
        CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] at h
      rw [pow_two]
      have hp := HJBridge.rowsOf_mul htr htr
      rw [h.2] at hp
      exact HJBridge.rowsOf_unique hp HJBridge.rowsOf_one
    refine B6.isElemAbelian_iff.mpr ⟨fun a ha b hb => ?_, hsq⟩
    obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hga2 hca2 a).1 ha
    obtain ⟨s, hs, hts⟩ := (HJBridge.mem_grpOf_iff hga2 hca2 b).1 hb
    have h := List.all_eq_true.1 hcomm2 r hr
    have h2 := List.all_eq_true.1 h s hs
    simp only [HJ12.commR, CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
      beq_iff_eq] at h2
    have hp := HJBridge.rowsOf_mul htr hts
    have hp' := HJBridge.rowsOf_mul hts htr
    rw [h2] at hp
    exact HJBridge.rowsOf_unique hp hp'
  have hA1card : Nat.card hjA1 = 16 := by
    rw [hjA1, HJBridge.card_grpOf_eq hga1 hca1, beq_iff_eq.mp h16a]
  have hA2card : Nat.card hjA2 = 16 := by
    rw [hjA2, HJBridge.card_grpOf_eq hga2 hca2, beq_iff_eq.mp h16b]
  have hE16 : ∀ A : Subgroup (MulAut W12), A ≤ hjT1 → IsElemAbelian2 A →
      Nat.card A ≤ 16 ∧ (Nat.card A = 16 → A = hjA1 ∨ A = hjA2) := hjE16_aux
  have hA1max : IsMaxElemAbelian hjT1 hjA1 := by
    refine ⟨hA1T0.trans hT0T1, hA1el, fun B hBT hBel => ?_⟩
    have hBel2 : IsElemAbelian2 B := B6.isElemAbelian_iff.mp hBel
    rw [hA1card]
    exact (hE16 B hBT hBel2).1
  have hA2max : IsMaxElemAbelian hjT1 hjA2 := by
    refine ⟨hA2T0.trans hT0T1, hA2el, fun B hBT hBel => ?_⟩
    have hBel2 : IsElemAbelian2 B := B6.isElemAbelian_iff.mp hBel
    rw [hA2card]
    exact (hE16 B hBT hBel2).1
  have hJ : thompsonJ hjT1 = hjA1 ⊔ hjA2 := by
    apply le_antisymm
    · refine iSup₂_le fun B hB => ?_
      have hBel2 : IsElemAbelian2 B := B6.isElemAbelian_iff.mp hB.2.1
      have h16B := (hE16 B hB.1 hBel2).1
      have hge : 16 ≤ Nat.card B := by
        rw [← hA1card]
        exact hB.2.2 hjA1 (hA1T0.trans hT0T1) hA1el
      rcases (hE16 B hB.1 hBel2).2 (le_antisymm h16B hge) with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · refine sup_le ?_ ?_
      · exact le_iSup₂_of_le hjA1 hA1max le_rfl
      · exact le_iSup₂_of_le hjA2 hA2max le_rfl
  exact ⟨hτN, hT0L, hT0T1, hT1N, hcardT0, hcardT1, hA1T0, hA2T0, hE16, hJ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
