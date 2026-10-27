module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_v0_good (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V)
    (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M) :
    ∀ w ∈ V₀, w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨p, hp, h3⟩ := hσ
  intro w hw hw1
  exact s16c34_uniqueMax_cent_of_mem_v0 D h61 h hp h3 hw hw1

@[expose] def s16h_CondU (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ x ∈ D.M, ∀ w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))),
    w ∉ V₀ → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))

@[expose] def s16h_CondU2 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∀ x ∈ D.M, ∀ y ∈ D.M,
    barSub V₀ V hV (conjSubgroup L x) ≠ barSub V₀ V hV (conjSubgroup L y) →
    ∀ w ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) ⊓
        preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L y))),
      w ∉ V₀ → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))

private theorem s16h_exists_conj_of_mem_s15 {D : Data G} {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) {B : Subgroup (MulAut (Vtil V₀ V hV))}
    (hB : B ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV,
        X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}) :
    ∃ g ∈ D.M, B = barSub V₀ V hV (conjSubgroup L g) := by
  obtain ⟨φ, hφ, rfl⟩ := hB
  obtain ⟨g, hgM, hg⟩ :=
    (mem_barSub V₀ V hV D.M φ⁻¹).1 ((Mbar D.M V₀ V hV).inv_mem hφ)
  refine ⟨(g : G), hgM, ?_⟩
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV g.2 L, hg, inv_inv]

theorem s16h_exists_conj_pair (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : 2 < s15 D.M V₀ V h.isElemAbelian L) :
    ∃ x ∈ D.M, ∃ y ∈ D.M, x ∉ nBar D.M V₀ V h.isElemAbelian L ∧
      y ∉ nBar D.M V₀ V h.isElemAbelian L ∧
      barSub V₀ V h.isElemAbelian (conjSubgroup L x) ≠
        barSub V₀ V h.isElemAbelian (conjSubgroup L y) := by
  have hV := h.isElemAbelian
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}
  have hsS : 2 < S.ncard := by
    change 2 < s15 D.M V₀ V hV L
    exact hs
  have hfin : S.Finite := by
    apply Set.finite_of_ncard_pos
    omega
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ := (Set.two_lt_ncard_iff hfin).1 hsS
  have hchoice : ∃ P Q : Subgroup (MulAut (Vtil V₀ V hV)), P ∈ S ∧ Q ∈ S ∧
      P ≠ barSub V₀ V hV L ∧ Q ≠ barSub V₀ V hV L ∧ P ≠ Q := by
    by_cases hA0 : A = barSub V₀ V hV L
    · exact ⟨B, C, hB, hC, (hA0 ▸ hAB).symm, (hA0 ▸ hAC).symm, hBC⟩
    · by_cases hB0 : B = barSub V₀ V hV L
      · exact ⟨A, C, hA, hC, hA0, (hB0 ▸ hBC).symm, hAC⟩
      · exact ⟨A, B, hA, hB, hA0, hB0, hAB⟩
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hPQ⟩ := hchoice
  obtain ⟨x, hx, hxP⟩ :=
    s16h_exists_conj_of_mem_s15 (D := D) (V₀ := V₀) (V := V) (L := L) hV hP
  obtain ⟨y, hy, hyQ⟩ :=
    s16h_exists_conj_of_mem_s15 (D := D) (V₀ := V₀) (V := V) (L := L) hV hQ
  have hxn : x ∉ nBar D.M V₀ V hV L := fun hmem =>
    hP0 (hxP.trans ((s15_Infra_mem_nBar_iff h.hyp125 hV hx).1 hmem))
  have hyn : y ∉ nBar D.M V₀ V hV L := fun hmem =>
    hQ0 (hyQ.trans ((s15_Infra_mem_nBar_iff h.hyp125 hV hy).1 hmem))
  have hxy : barSub V₀ V hV (conjSubgroup L x) ≠
      barSub V₀ V hV (conjSubgroup L y) := by
    intro heq
    exact hPQ (hxP.trans (heq.trans hyQ.symm))
  exact ⟨x, hx, y, hy, hxn, hyn, hxy⟩

theorem s16h_exists_two_not_mem (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : 3 < s15 D.M V₀ V h.isElemAbelian L) {X Y : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V h.isElemAbelian L) (hY : Y ∈ wConj D.M V₀ V h.isElemAbelian L)
    (hXY : X ≠ Y) :
    ∃ x ∈ D.M, ∃ y ∈ D.M,
      conjSubgroup (wSub V₀ V h.isElemAbelian L) x ≠
        conjSubgroup (wSub V₀ V h.isElemAbelian L) y ∧
      conjSubgroup (wSub V₀ V h.isElemAbelian L) x ∉ ({X, Y} : Set (Subgroup G)) ∧
      conjSubgroup (wSub V₀ V h.isElemAbelian L) y ∉ ({X, Y} : Set (Subgroup G)) := by
  have hV := h.isElemAbelian
  have hsub : ({X, Y} : Set (Subgroup G)) ⊆ wConj D.M V₀ V hV L := by
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with rfl | rfl <;> assumption
  have hfin : (wConj D.M V₀ V hV L).Finite := by
    apply Set.finite_of_ncard_pos
    rw [ncard_wConj D h hV]
    omega
  have hd : (wConj D.M V₀ V hV L \ ({X, Y} : Set (Subgroup G))).ncard =
      s15 D.M V₀ V hV L - 2 := by
    rw [Set.ncard_sdiff hsub, Set.ncard_pair hXY, ncard_wConj D h hV]
  have h2 : 1 < (wConj D.M V₀ V hV L \ ({X, Y} : Set (Subgroup G))).ncard := by
    rw [hd]
    omega
  have hdifff : (wConj D.M V₀ V hV L \ ({X, Y} : Set (Subgroup G))).Finite :=
    hfin.subset Set.sdiff_subset
  obtain ⟨A, B, hA, hB, hAB⟩ := (Set.one_lt_ncard_iff hdifff).1 h2
  obtain ⟨x, hx, rfl⟩ := hA.1
  obtain ⟨y, hy, rfl⟩ := hB.1
  exact ⟨x, hx, y, hy, hAB, hA.2, hB.2⟩

theorem s16h_barSub_ne_of_wSub_ne (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {x y : G} (hx : x ∈ D.M) (hy : y ∈ D.M)
    (hne : conjSubgroup (wSub V₀ V h.isElemAbelian L) x ≠
      conjSubgroup (wSub V₀ V h.isElemAbelian L) y) :
    barSub V₀ V h.isElemAbelian (conjSubgroup L x) ≠
      barSub V₀ V h.isElemAbelian (conjSubgroup L y) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  intro heq
  apply hne
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx),
    ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hy)]
  unfold wSub wTil
  rw [heq]

theorem s16h_le_preTil_fixV_of_ne (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {x : G} (hx : x ∈ D.M) {S : Set (Subgroup G)}
    (hS : ∀ X ∈ S, X ∈ wConj D.M V₀ V h.isElemAbelian L ∧
      X ≠ conjSubgroup (wSub V₀ V h.isElemAbelian L) x) :
    v1Sub D.M V₀ V h.isElemAbelian L ⊔ (⨆ X ∈ S, X) ≤
      preTil V₀ V h.isElemAbelian (fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L x))) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  refine sup_le (s16c34_v1Sub_le_preTil_fixV D h hx) (iSup₂_le fun X hX => ?_)
  obtain ⟨⟨m, hm, rfl⟩, hXx⟩ := hS X hX
  have hne : barSub V₀ V hV (conjSubgroup L x) ≠ barSub V₀ V hV (conjSubgroup L m) := by
    intro heq
    apply hXx
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm),
      ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx)]
    unfold wSub wTil
    rw [heq]
  have hW := s16c34_wSub_conj_le_preTil_fixV D h hm hx hne
  rwa [s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm)] at hW

theorem s16h_unique₁_of_condU (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU D V₀ V L h.hyp151.isElemAbelian)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨x, hx, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 hs
  have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
      preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) :=
    sup_le (s16c34_wSub_le_preTil_fixV hV (h.hyp151.commute x hx hxn).2)
      (s16c34_v1Sub_le_preTil_fixV D h.hyp151 hx)
  intro w hw hw1
  by_cases hw0 : w ∈ V₀
  · exact s16h_v0_good D h61 h.hyp16 hσ w hw0 hw1
  · exact hU x hx w (hle hw) hw0

theorem s16h_unique₂_of_condU (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU D V₀ V L h.hyp151.isElemAbelian) :
    ∀ x ∈ D.M, ∀ y ∈ D.M,
      ∀ w ∈ v1Sub D.M V₀ V h.hyp151.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  intro x hx y _ w hw hw1
  have hle := s16h_le_preTil_fixV_of_ne D h.hyp151 hx
    (S := {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
      X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
      X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y})
    (fun X hX => ⟨hX.1, hX.2.1⟩)
  by_cases hw0 : w ∈ V₀
  · exact s16h_v0_good D h61 h.hyp16 hσ w hw0 hw1
  · exact hU x hx w (hle hw) hw0

theorem s16h_hyp154_of_condU (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU D V₀ V L h.hyp151.isElemAbelian)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1) :
    Hyp154 D V₀ V L :=
  s16c34_hyp154_of_fields D h.hyp151 (s16h_unique₁_of_condU D h61 h hσ hU hs)
    (s16h_unique₂_of_condU D h61 h hσ hU) hs hδ

theorem s16h_unique₁_of_condU2 (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian)
    (hs : 2 < s15 D.M V₀ V h.hyp151.isElemAbelian L) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨x, hx, y, hy, hxn, hyn, hxy⟩ := s16h_exists_conj_pair D h.hyp151 hs
  have hle : ∀ z ∈ D.M, z ∉ nBar D.M V₀ V hV L →
      wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
        preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L z))) := fun z hz hzn =>
    sup_le (s16c34_wSub_le_preTil_fixV hV (h.hyp151.commute z hz hzn).2)
      (s16c34_v1Sub_le_preTil_fixV D h.hyp151 hz)
  intro w hw hw1
  by_cases hw0 : w ∈ V₀
  · exact s16h_v0_good D h61 h.hyp16 hσ w hw0 hw1
  · exact hU x hx y hy hxy w ⟨hle x hx hxn hw, hle y hy hyn hw⟩ hw0

theorem s16h_unique₂_of_condU2 (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian) :
    ∀ x ∈ D.M, ∀ y ∈ D.M,
      conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ≠
        conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y →
      ∀ w ∈ v1Sub D.M V₀ V h.hyp151.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  intro x hx y hy hne w hw hw1
  have hlex := s16h_le_preTil_fixV_of_ne D h.hyp151 hx
    (S := {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
      X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
      X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y})
    (fun X hX => ⟨hX.1, hX.2.1⟩)
  have hley := s16h_le_preTil_fixV_of_ne D h.hyp151 hy
    (S := {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
      X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
      X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y})
    (fun X hX => ⟨hX.1, hX.2.2⟩)
  by_cases hw0 : w ∈ V₀
  · exact s16h_v0_good D h61 h.hyp16 hσ w hw0 hw1
  · exact hU x hx y hy (s16h_barSub_ne_of_wSub_ne D h.hyp151 hx hy hne) w
      ⟨hlex hw, hley hw⟩ hw0

private theorem s16h_isPGroup_two_sub_v {V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hUV : U ≤ V) : IsPGroup 2 U := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hV.2 g.1 (hUV g.2)

private theorem s16h_wConj_le_v (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {Z : Subgroup G} (hZ : Z ∈ wConj D.M V₀ V h.isElemAbelian L) : Z ≤ V := by
  obtain ⟨m, hm, rfl⟩ := hZ
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L h.isElemAbelian (hMs hm)]
  exact preTil_le V₀ V h.isElemAbelian _

theorem s16h_hyp154_of_condU2 (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian)
    (hs : 3 < s15 D.M V₀ V h.hyp151.isElemAbelian L) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  have hu₁ := s16h_unique₁_of_condU2 D h61 h hσ hU (by omega)
  have hu₂ := s16h_unique₂_of_condU2 D h61 h hσ hU
  refine ⟨h.hyp151, hu₁, hu₂, ?_⟩
  intro g hg X hX Y hY hXY hne
  exfalso
  obtain ⟨x, hx, y, hy, hxy, hxXY, hyXY⟩ :=
    s16h_exists_two_not_mem D h.hyp151 hs hX hY hXY
  have hSx : ∀ Z ∈ ({X, Y} : Set (Subgroup G)),
      Z ∈ wConj D.M V₀ V hV L ∧ Z ≠ conjSubgroup (wSub V₀ V hV L) x := by
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with hZX | hZY
    · rw [hZX]
      exact ⟨hX, fun hEq => hxXY (hEq ▸ (by simp : X ∈ ({X, Y} : Set (Subgroup G))))⟩
    · rw [hZY]
      exact ⟨hY, fun hEq => hxXY (hEq ▸ (by simp : Y ∈ ({X, Y} : Set (Subgroup G))))⟩
  have hSy : ∀ Z ∈ ({X, Y} : Set (Subgroup G)),
      Z ∈ wConj D.M V₀ V hV L ∧ Z ≠ conjSubgroup (wSub V₀ V hV L) y := by
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with hZX | hZY
    · rw [hZX]
      exact ⟨hX, fun hEq => hyXY (hEq ▸ (by simp : X ∈ ({X, Y} : Set (Subgroup G))))⟩
    · rw [hZY]
      exact ⟨hY, fun hEq => hyXY (hEq ▸ (by simp : Y ∈ ({X, Y} : Set (Subgroup G))))⟩
  have hleX0 := s16h_le_preTil_fixV_of_ne D h.hyp151 hx
    (S := ({X, Y} : Set (Subgroup G))) hSx
  have hleY0 := s16h_le_preTil_fixV_of_ne D h.hyp151 hy
    (S := ({X, Y} : Set (Subgroup G))) hSy
  have hleXY : X ⊔ Y ≤ ⨆ Z ∈ ({X, Y} : Set (Subgroup G)), Z :=
    sup_le (le_iSup₂_of_le X (by simp) le_rfl) (le_iSup₂_of_le Y (by simp) le_rfl)
  have hleX : X ⊔ Y ⊔ v1Sub D.M V₀ V hV L ≤
      preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) :=
    (sup_le (hleXY.trans le_sup_right) le_sup_left).trans hleX0
  have hleY : X ⊔ Y ⊔ v1Sub D.M V₀ V hV L ≤
      preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L y))) :=
    (sup_le (hleXY.trans le_sup_right) le_sup_left).trans hleY0
  have hU₁ : ∀ w ∈ X ⊔ Y ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hw hw1
    by_cases hw0 : w ∈ V₀
    · exact s16h_v0_good D h61 h.hyp16 hσ w hw0 hw1
    · exact hU x hx y hy (s16h_barSub_ne_of_wSub_ne D h.hyp151 hx hy hxy) w
        ⟨hleX hw, hleY hw⟩ hw0
  have hV1 : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hP₁ := s16h_isPGroup_two_sub_v hV
    (sup_le (sup_le (s16h_wConj_le_v D h.hyp151 hX) (s16h_wConj_le_v D h.hyp151 hY)) hV1)
  have hP₂ := s16h_isPGroup_two_sub_v hV (sup_le hWV hV1)
  exact hne (inf_conjSubgroup_eq_bot_of_uniqueMax D.maxLocal hP₁ hP₂ hU₁ hu₁ hg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
