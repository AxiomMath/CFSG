module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Hyperplanes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVDeg
import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
import CFSG.GroupTheory.DisjointSupCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private lemma sq_eq_one_of_orderOf_eq_two {t : MulAut W} (ht : orderOf t = 2) : t ^ 2 = 1 := by
  rw [← ht]
  exact pow_orderOf_eq_one t

private lemma odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) : Odd (Nat.card E) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem rk_commSub_le_two_mul_rkIdx (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) {t : MulAut W}
    (ht : orderOf t = 2) (hinv : ∀ x ∈ E, t * x * t⁻¹ = x⁻¹) :
    rk ↥(commSub ⊤ E) ≤ 2 * rkIdx (fixV (zpowers t)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hE1 : E = ⊥
  · have h0 : commSub (⊤ : Subgroup W) (⊥ : Subgroup (MulAut W)) = ⊥ :=
      commSub_eq_bot_iff.mpr (by rw [B1.fixV_bot])
    rw [hE1, h0, rk_bot]
    exact Nat.zero_le _
  · obtain ⟨n, hcard⟩ := hE.isPGroup.exists_card_eq
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exfalso
        exact hE1 (Subgroup.card_eq_one.mp (by rw [hcard, hn, pow_zero]))
      · exact hn
    obtain ⟨m, ⟨e⟩⟩ :=
      CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence.abelian_equiv (E := ↥E) hp
        (fun x => Subtype.ext (hE.2 x.1 x.2)) (fun x y => hE.1.is_comm.comm x y)
    have hcardm : Nat.card ↥E = p ^ m := by
      rw [Nat.card_congr e.toEquiv]
      simp
    have hmn : m = n := Nat.pow_right_injective hp.two_le (hcardm.symm.trans hcard)
    rw [hmn] at e
    have hRank : IsElemAbelianOfRank p n ↥E := ⟨e⟩
    have h2 := CFSG.LocalAnalysis.WeakClosure81.rk_commSub_eq_two_mul_of_inverted
      hW ht hp hp2 hn hRank hinv
    rw [h2]
    refine Nat.mul_le_mul_left _ ?_
    calc rk ↥(commSub (commSub ⊤ E) (zpowers t)) ≤ rk ↥(commSub ⊤ (zpowers t)) :=
          rk_mono (commSub_mono le_top le_rfl)
      _ = rkIdx (fixV (zpowers t)) := by
          rw [← commV_eq_commSub,
            CFSG.LocalAnalysis.UniquenessCase.UC22.rk_commV_zpowers_eq_rkIdx_fixV t
              (sq_eq_one_of_orderOf_eq_two ht)]

omit [Finite W] in
private lemma map_hypPart_conjAut {E D : Subgroup (MulAut W)} {t : MulAut W}
    (htE : t ∈ normalizer (E : Set (MulAut W))) :
    hypPart E (D.map (MulAut.conj t).toMonoidHom) = (hypPart E D).map t.toMonoidHom := by
  have hEmap : E.map (MulAut.conj t).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htE
  have hstab := FixVLat.mem_stabSub_commV_of_mem_normalizer htE
  rw [commV_eq_commSub] at hstab
  have hUmap : (commSub ⊤ E).map t.toMonoidHom = commSub ⊤ E := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (mem_stabSub.1 hstab v).2 hv
    · intro hu
      refine ⟨t⁻¹ u, (mem_stabSub.1 hstab (t⁻¹ u)).1 ?_, by simp⟩
      simpa using hu
  calc hypPart E (D.map (MulAut.conj t).toMonoidHom)
      = commSub ⊤ E ⊓ fixV (D.map (MulAut.conj t).toMonoidHom) := rfl
    _ = commSub ⊤ E ⊓ (fixV D).map t.toMonoidHom := by rw [fixV_map_conj_eq]
    _ = (commSub ⊤ E).map t.toMonoidHom ⊓ (fixV D).map t.toMonoidHom := by rw [hUmap]
    _ = (commSub ⊤ E ⊓ fixV D).map t.toMonoidHom :=
        (Subgroup.map_inf_eq _ _ _ t.injective).symm
    _ = (hypPart E D).map t.toMonoidHom := rfl

omit [Finite W] in
private lemma conjAutMap_involutive {t : MulAut W} (htt : t * t = 1) :
    Function.Involutive (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) := by
  intro D
  show (D.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = D
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    have h : MulAut.conj t * MulAut.conj t = 1 := by
      rw [← map_mul, htt, map_one]
    refine MonoidHom.ext fun x => ?_
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut (MulAut W) => f x) h
  rw [hcomp, Subgroup.map_id]

omit [Finite W] in
private lemma conjAutMap_mem_hyperplanes {p : ℕ} {E D : Subgroup (MulAut W)} {t : MulAut W}
    (htE : t ∈ normalizer (E : Set (MulAut W))) (hD : D ∈ hyperplanes p E) :
    D.map (MulAut.conj t).toMonoidHom ∈ hyperplanes p E := by
  have hEmap : E.map (MulAut.conj t).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htE
  refine ⟨?_, ?_⟩
  · rw [← hEmap]
    exact Subgroup.map_mono hD.1
  · rw [← hEmap, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hD.2

omit [Finite W] in
private lemma map_commHom_le_commSub (A : Subgroup W) (t : MulAut W) :
    A.map (commHom t) ≤ commSub ⊤ (Subgroup.zpowers t) := by
  rintro u ⟨a, -, rfl⟩
  rw [commHom_apply]
  exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, a, Subgroup.mem_top a, rfl⟩

omit [Finite W] in
private lemma inf_fixV_eq_bot_of_disjoint_map {A : Subgroup W} {t : MulAut W}
    (h : Disjoint A (A.map t.toMonoidHom)) : A ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
  have hbot : A ⊓ A.map t.toMonoidHom = ⊥ := disjoint_iff.mp h
  rw [eq_bot_iff]
  intro a ha
  have hta : t a = a := (mem_fixV.1 ha.2) t (Subgroup.mem_zpowers t)
  have hamap : a ∈ A.map t.toMonoidHom := ⟨a, ha.1, hta⟩
  have hmem : a ∈ A ⊓ A.map t.toMonoidHom := ⟨ha.1, hamap⟩
  rwa [hbot] at hmem

private lemma rk_iSup_hypPart_eq_sum {p : ℕ} {E : Subgroup (MulAut W)}
    (hdec : iSupIndep (fun D : hyperplanes p E => hypPart E D))
    (T : Finset (Subgroup (MulAut W))) (hT : ∀ D ∈ T, D ∈ hyperplanes p E) :
    rk ↥(⨆ D ∈ T, hypPart E D) = ∑ D ∈ T, rk ↥(hypPart E D) := by
  classical
  have hmap : (T.subtype (fun D => D ∈ hyperplanes p E)).map
      (Function.Embedding.subtype (fun D => D ∈ hyperplanes p E)) = T := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem hT]
  have hsup : (⨆ D ∈ T, hypPart E D) =
      ⨆ D ∈ T.subtype (fun D => D ∈ hyperplanes p E), hypPart E D := by
    conv_lhs => rw [← hmap]
    rw [← Finset.sup_eq_iSup, Finset.sup_map, Finset.sup_eq_iSup]
    rfl
  have hsum : (∑ D ∈ T, rk ↥(hypPart E D)) =
      ∑ D ∈ T.subtype (fun D => D ∈ hyperplanes p E), rk ↥(hypPart E D) := by
    conv_lhs => rw [← hmap]
    rw [Finset.sum_map]
    rfl
  rw [hsup, hsum,
    rk_iSup_biSup_eq_sum (fun D : hyperplanes p E => hypPart E D) hdec
      (T.subtype (fun D => D ∈ hyperplanes p E))]

omit [Finite W] in
private lemma disjoint_iSup_hypPart {p : ℕ} {E : Subgroup (MulAut W)}
    (hdec : iSupIndep (fun D : hyperplanes p E => hypPart E D))
    {S T : Finset (Subgroup (MulAut W))} (hS : ∀ D ∈ S, D ∈ hyperplanes p E)
    (hT : ∀ D ∈ T, D ∈ hyperplanes p E) (hd : Disjoint S T) :
    Disjoint (⨆ D ∈ S, hypPart E D) (⨆ D ∈ T, hypPart E D) := by
  classical
  let pE : Subgroup (MulAut W) → Prop := fun D => D ∈ hyperplanes p E
  have hS' : Disjoint (S.subtype pE) (T.subtype pE) := by
    rw [Finset.disjoint_left]
    intro D hDS hDT
    rw [Finset.mem_subtype] at hDS hDT
    exact Finset.disjoint_left.mp hd hDS hDT
  have hmapS : (S.subtype pE).map (Function.Embedding.subtype pE) = S := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem hS]
  have hmapT : (T.subtype pE).map (Function.Embedding.subtype pE) = T := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem hT]
  have hsupS : (⨆ D ∈ S, hypPart E D) = (S.subtype pE).sup (fun D => hypPart E D) := by
    conv_lhs => rw [← hmapS]
    rw [← Finset.sup_eq_iSup, Finset.sup_map]
    rfl
  have hsupT : (⨆ D ∈ T, hypPart E D) = (T.subtype pE).sup (fun D => hypPart E D) := by
    conv_lhs => rw [← hmapT]
    rw [← Finset.sup_eq_iSup, Finset.sup_map]
    rfl
  rw [hsupS, hsupT]
  exact (hdec.supIndep' (S.subtype pE ∪ T.subtype pE)).disjoint_sup_sup
    Finset.subset_union_left Finset.subset_union_right hS'

omit [Finite W] in
private lemma map_iSup_hypPart_conjAut {p : ℕ} {E : Subgroup (MulAut W)} {t : MulAut W}
    [DecidableEq (Subgroup (MulAut W))]
    (htE : t ∈ normalizer (E : Set (MulAut W)))
    (T : Finset (Subgroup (MulAut W))) (hT : ∀ D ∈ T, D ∈ hyperplanes p E) :
    (⨆ D ∈ T, hypPart E D).map t.toMonoidHom =
      ⨆ D ∈ T.image (fun D : Subgroup (MulAut W) =>
          D.map (MulAut.conj t).toMonoidHom), hypPart E D := by
  classical
  revert hT
  induction T using Finset.induction_on with
  | empty => intro hT; simp
  | insert a T ha ih =>
    intro hT
    have hA : (⨆ D ∈ T, hypPart E D).map t.toMonoidHom =
        ⨆ D ∈ T.image (fun D : Subgroup (MulAut W) =>
          D.map (MulAut.conj t).toMonoidHom), hypPart E D :=
      ih (fun D hD => hT D (Finset.mem_insert_of_mem hD))
    have hFa : hypPart E (a.map (MulAut.conj t).toMonoidHom) = (hypPart E a).map t.toMonoidHom :=
      map_hypPart_conjAut htE
    calc (⨆ D ∈ insert a T, hypPart E D).map t.toMonoidHom
        = (hypPart E a ⊔ ⨆ D ∈ T, hypPart E D).map t.toMonoidHom := by
            rw [Finset.iSup_insert]
      _ = (hypPart E a).map t.toMonoidHom ⊔
            (⨆ D ∈ T, hypPart E D).map t.toMonoidHom := by
            rw [Subgroup.map_sup]
      _ = hypPart E (a.map (MulAut.conj t).toMonoidHom) ⊔
            ⨆ D ∈ T.image (fun D : Subgroup (MulAut W) =>
              D.map (MulAut.conj t).toMonoidHom), hypPart E D := by
            rw [hA, ← hFa]
      _ = ⨆ D ∈ (insert a T).image (fun D : Subgroup (MulAut W) =>
            D.map (MulAut.conj t).toMonoidHom), hypPart E D := by
            rw [Finset.image_insert, Finset.iSup_insert]

private lemma exists_reps_of_involutive {α : Type*} [LinearOrder α] {τ : α → α}
    (hτ : Function.Involutive τ) {S : Finset α} (hS : ∀ a ∈ S, τ a ∈ S)
    (hfree : ∀ a ∈ S, τ a ≠ a) :
    ∃ T₁ : Finset α, T₁ ⊆ S ∧ Disjoint T₁ (T₁.image τ) ∧ S = T₁ ∪ T₁.image τ := by
  classical
  refine ⟨S.filter (fun a => a < τ a), Finset.filter_subset _ _, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha haim
    rw [Finset.mem_filter] at ha
    rcases Finset.mem_image.mp haim with ⟨b, hb, hba⟩
    rw [Finset.mem_filter] at hb
    have h1 : b < a := by rw [← hba]; exact hb.2
    have h2 : a < b := by
      have hτa : τ a = b := by rw [← hba, hτ b]
      rw [hτa] at ha
      exact ha.2
    exact absurd h1 (not_lt.mpr (le_of_lt h2))
  · apply Finset.Subset.antisymm
    · intro a ha
      rw [Finset.mem_union]
      rcases lt_or_gt_of_ne (hfree a ha).symm with hlt | hgt
      · exact Or.inl (Finset.mem_filter.mpr ⟨ha, hlt⟩)
      · refine Or.inr (Finset.mem_image.mpr ⟨τ a, Finset.mem_filter.mpr ⟨hS a ha, ?_⟩, hτ a⟩)
        rwa [hτ a]
    · intro a ha
      rw [Finset.mem_union] at ha
      rcases ha with ha | ha
      · exact Finset.mem_of_mem_filter a ha
      · rcases Finset.mem_image.mp ha with ⟨b, hb, hba⟩
        rw [← hba]
        exact hS b (Finset.mem_of_mem_filter b hb)

theorem sum_moved_add_le (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) {t : MulAut W} (ht : orderOf t = 2)
    (htE : t ∈ normalizer (E : Set (MulAut W))) (T : Finset (Subgroup (MulAut W)))
    (hT : ∀ D ∈ T, D ∈ hyperplanes p E ∧ D.map (MulAut.conj t).toMonoidHom ≠ D)
    (D₀ : Subgroup (MulAut W)) (hD₀ : D₀ ∈ hyperplanes p E)
    (hD₀t : D₀.map (MulAut.conj t).toMonoidHom = D₀) (hD₀T : D₀ ∉ T) :
    ∑ D ∈ T, rk ↥(hypPart E D) + 2 * rk ↥(commSub (hypPart E D₀) (zpowers t)) ≤
      2 * rkIdx (fixV (zpowers t)) := by
  classical
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let : LinearOrder (Subgroup (MulAut W)) :=
    LinearOrder.lift' (Fintype.equivFin (Subgroup (MulAut W)))
      (Fintype.equivFin (Subgroup (MulAut W))).injective
  have hstab : StableUnder E (commSub ⊤ E) := by
    intro x hx u hu
    have h := FixVLat.mem_stabSub_commV_of_mem_normalizer (Subgroup.le_normalizer hx)
    rw [commV_eq_commSub] at h
    exact (mem_stabSub.1 h u).2 hu
  have hbot : commSub ⊤ E ⊓ fixV E = ⊥ := by
    have h := (B1.coprime_decomp hW (odd_card_of_isElemAbelian hp hp2 hE) (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    rw [top_inf_eq, inf_comm] at h
    exact h
  have hUU : commSub (commSub ⊤ E) E = commSub ⊤ E := by
    have h0 := (B1.coprime_decomp hW (odd_card_of_isElemAbelian hp hp2 hE) (M := commSub ⊤ E)
      hstab).1
    rwa [hbot, bot_sup_eq] at h0
  obtain ⟨hdec, -⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.inf_fixV_hyperplane_decomposition
      hW hp hp2 E hE hstab hUU
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_orderOf_eq_two ht
  have hτ : Function.Involutive (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) := conjAutMap_involutive htt
  let S : Finset (Subgroup (MulAut W)) :=
    T ∪ T.image (fun D : Subgroup (MulAut W) => D.map (MulAut.conj t).toMonoidHom)
  have hSmem : ∀ D ∈ S, D ∈ hyperplanes p E := by
    intro D hD
    rw [show S = T ∪ T.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) from rfl, Finset.mem_union] at hD
    rcases hD with hD | hD
    · exact (hT D hD).1
    · rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
      exact conjAutMap_mem_hyperplanes htE (hT C hC).1
  have hSfree : ∀ D ∈ S, (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) D ≠ D := by
    intro D hD hfix
    rw [show S = T ∪ T.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) from rfl, Finset.mem_union] at hD
    rcases hD with hD | hD
    · exact (hT D hD).2 hfix
    · rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
      exact (hT C hC).2 (hτ.injective hfix)
  have hSinv : ∀ D ∈ S, (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) D ∈ S := by
    intro D hD
    rw [show S = T ∪ T.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) from rfl, Finset.mem_union] at hD ⊢
    rcases hD with hD | hD
    · exact Or.inr (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
    · rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
      exact Or.inl (by rwa [hτ C])
  obtain ⟨T₁, hT₁sub, hT₁disj, hSdec⟩ := exists_reps_of_involutive hτ hSinv hSfree
  have hT₁mem : ∀ D ∈ T₁, D ∈ hyperplanes p E := fun D hD => hSmem D (hT₁sub hD)
  have hT₁immem : ∀ D ∈ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom), D ∈ hyperplanes p E := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
    exact conjAutMap_mem_hyperplanes htE (hT₁mem C hC)
  have hsum_mono : ∑ D ∈ T, rk ↥(hypPart E D) ≤ ∑ D ∈ S, rk ↥(hypPart E D) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => Nat.zero_le _)
  have hsumS : ∑ D ∈ S, rk ↥(hypPart E D) = 2 * ∑ D ∈ T₁, rk ↥(hypPart E D) := by
    rw [show S = T₁ ∪ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) from hSdec, Finset.sum_union hT₁disj,
      Finset.sum_image]
    · rw [two_mul, Nat.add_comm]
      congr 1
      exact Finset.sum_congr rfl fun D _ => rk_hypPart_map_conj (E := E) (n := t) htE
    · intro x _ y _ hxy
      exact hτ.injective hxy
  set A : Subgroup W := ⨆ D ∈ T₁, hypPart E D with hA
  set B : Subgroup W := hypPart E D₀ with hB
  have hsumA : ∑ D ∈ T, rk ↥(hypPart E D) ≤ 2 * rk A := by
    have hT₁rk : ∑ D ∈ T₁, rk ↥(hypPart E D) = rk A := by
      rw [hA]
      exact (rk_iSup_hypPart_eq_sum hdec T₁ hT₁mem).symm
    calc ∑ D ∈ T, rk ↥(hypPart E D) ≤ ∑ D ∈ S, rk ↥(hypPart E D) := hsum_mono
      _ = 2 * ∑ D ∈ T₁, rk ↥(hypPart E D) := hsumS
      _ = 2 * rk A := by rw [hT₁rk]
  have hdisjT₁ : Disjoint (⨆ D ∈ T₁, hypPart E D)
      (⨆ D ∈ T₁.image (fun D : Subgroup (MulAut W) =>
        D.map (MulAut.conj t).toMonoidHom), hypPart E D) :=
    disjoint_iSup_hypPart hdec hT₁mem hT₁immem hT₁disj
  have hAmap : (⨆ D ∈ T₁, hypPart E D).map t.toMonoidHom =
      ⨆ D ∈ T₁.image (fun D : Subgroup (MulAut W) =>
        D.map (MulAut.conj t).toMonoidHom), hypPart E D :=
    map_iSup_hypPart_conjAut htE T₁ hT₁mem
  have hdisjAt : Disjoint A (A.map t.toMonoidHom) := by
    rw [hA, hAmap]
    exact hdisjT₁
  have hkerA : A ⊓ (commHom t).ker = ⊥ := by
    rw [ker_commHom]
    exact inf_fixV_eq_bot_of_disjoint_map hdisjAt
  have hrkA : rk ↥(A.map (commHom t)) = rk A := by
    have h := rk_map_add_rk_inf_ker (commHom t) A
    rw [hkerA, rk_bot, add_zero] at h
    exact h
  have hBmap : B.map t.toMonoidHom = B := by
    have h := map_hypPart_conjAut (E := E) (D := D₀) (t := t) htE
    rw [hD₀t] at h
    rw [hB]
    exact h.symm
  have hBzp : Subgroup.zpowers t ≤ stabSub B := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [mem_stabSub]
    intro w
    constructor
    · intro hw
      rw [← hBmap]
      refine ⟨t w, hw, ?_⟩
      show t (t w) = w
      rw [← MulAut.mul_apply, htt]
      simp
    · intro hw
      rw [← hBmap]
      exact ⟨w, hw, rfl⟩
  have hBinv : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ B, x w ∈ B :=
    fun x hx w hw => (mem_stabSub.1 (hBzp hx) w).2 hw
  have hBcomm : commSub B (Subgroup.zpowers t) = B.map (commHom t) :=
    commSub_zpowers_eq_map hBinv
  have hD₀S : D₀ ∉ S := by
    intro h
    rw [show S = T ∪ T.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) from rfl, Finset.mem_union] at h
    rcases h with h | h
    · exact hD₀T h
    · rcases Finset.mem_image.mp h with ⟨C, hCmem, hCD⟩
      have hCEq : C = D₀ := by
        have h1 := congrArg (fun D : Subgroup (MulAut W) =>
          D.map (MulAut.conj t).toMonoidHom) hCD
        have h2 : C.map (MulAut.conj t).toMonoidHom = D₀ := by
          apply hτ.injective
          exact h1
        exact hτ.injective (by rw [h2, hD₀t])
      exact hD₀T (hCEq ▸ hCmem)
  have hUnionmem : ∀ D ∈ T₁ ∪ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom), D ∈ hyperplanes p E := by
    intro D hD
    rw [Finset.mem_union] at hD
    rcases hD with hD | hD
    · exact hT₁mem D hD
    · exact hT₁immem D hD
  have hD₀not : D₀ ∉ T₁ ∪ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) := by
    rwa [← hSdec]
  have hT₁D : Disjoint (T₁ ∪ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom)) ({D₀} : Finset (Subgroup (MulAut W))) := by
    rw [Finset.disjoint_left]
    intro D hD hD0
    rw [Finset.mem_singleton] at hD0
    subst hD0
    exact hD₀not hD
  have hdisjUnion : Disjoint (⨆ D ∈ T₁ ∪ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom), hypPart E D)
      (⨆ D ∈ ({D₀} : Finset (Subgroup (MulAut W))), hypPart E D) :=
    disjoint_iSup_hypPart hdec hUnionmem (by
      intro D hD
      rw [Finset.mem_singleton] at hD
      subst hD
      exact hD₀) hT₁D
  have hdisjUnion' : Disjoint (A ⊔ A.map t.toMonoidHom) B := by
    rw [Finset.iSup_singleton] at hdisjUnion
    rw [Finset.iSup_union, ← hAmap, ← hA, ← hB] at hdisjUnion
    exact hdisjUnion
  have hAimage_le : A.map (commHom t) ≤ A ⊔ A.map t.toMonoidHom := by
    rintro u ⟨a, ha, rfl⟩
    rw [commHom_apply]
    have h1 : t a ∈ A.map t.toMonoidHom := ⟨a, ha, rfl⟩
    have h2 : a⁻¹ ∈ A := A.inv_mem ha
    have h := Subgroup.mul_mem_sup h1 h2
    rwa [sup_comm] at h
  have hBimage_le : B.map (commHom t) ≤ B := by
    rintro u ⟨b, hb, rfl⟩
    rw [commHom_apply]
    have htb : t b ∈ B := by
      rw [← hBmap]
      exact ⟨b, hb, rfl⟩
    exact B.mul_mem htb (B.inv_mem hb)
  have hdisjImg : Disjoint (A.map (commHom t)) (B.map (commHom t)) := by
    rw [disjoint_iff]
    refine le_bot_iff.mp ?_
    have h1 : A.map (commHom t) ⊓ B.map (commHom t) ≤
        (A ⊔ A.map t.toMonoidHom) ⊓ B := inf_le_inf hAimage_le hBimage_le
    rw [disjoint_iff] at hdisjUnion'
    exact h1.trans (le_of_eq hdisjUnion')
  have hsup_eq : rk ↥(A.map (commHom t) ⊔ B.map (commHom t)) =
      rk ↥(A.map (commHom t)) + rk ↥(B.map (commHom t)) := by
    have h := rk_sup_add_rk_inf (A.map (commHom t)) (B.map (commHom t))
    rw [disjoint_iff.mp hdisjImg, rk_bot, add_zero] at h
    exact h
  have hadd : rk A + rk (commSub B (zpowers t)) ≤ rkIdx (fixV (zpowers t)) := by
    have hsubA : A.map (commHom t) ≤ commSub ⊤ (zpowers t) := map_commHom_le_commSub A t
    have hsubB : B.map (commHom t) ≤ commSub ⊤ (zpowers t) := map_commHom_le_commSub B t
    have hrank : rk ↥(A.map (commHom t)) + rk ↥(B.map (commHom t)) ≤
        rkIdx (fixV (zpowers t)) := by
      calc rk ↥(A.map (commHom t)) + rk ↥(B.map (commHom t))
          = rk ↥(A.map (commHom t) ⊔ B.map (commHom t)) := hsup_eq.symm
        _ ≤ rk ↥(commSub ⊤ (zpowers t)) := rk_mono (sup_le hsubA hsubB)
        _ = rkIdx (fixV (zpowers t)) := by
            rw [← commV_eq_commSub,
              CFSG.LocalAnalysis.UniquenessCase.UC22.rk_commV_zpowers_eq_rkIdx_fixV t htt]
    rwa [hrkA, ← hBcomm] at hrank
  calc ∑ D ∈ T, rk ↥(hypPart E D) + 2 * rk ↥(commSub B (zpowers t))
      ≤ 2 * rk A + 2 * rk ↥(commSub B (zpowers t)) := Nat.add_le_add_right hsumA _
    _ = 2 * (rk A + rk ↥(commSub B (zpowers t))) := by ring
    _ ≤ 2 * rkIdx (fixV (zpowers t)) := Nat.mul_le_mul_left _ hadd

theorem sum_moved_le (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) {t : MulAut W} (ht : orderOf t = 2)
    (htE : t ∈ normalizer (E : Set (MulAut W))) (T : Finset (Subgroup (MulAut W)))
    (hT : ∀ D ∈ T, D ∈ hyperplanes p E ∧ D.map (MulAut.conj t).toMonoidHom ≠ D) :
    ∑ D ∈ T, rk ↥(hypPart E D) ≤ 2 * rkIdx (fixV (zpowers t)) := by
  classical
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let : LinearOrder (Subgroup (MulAut W)) :=
    LinearOrder.lift' (Fintype.equivFin (Subgroup (MulAut W)))
      (Fintype.equivFin (Subgroup (MulAut W))).injective
  have hstab : StableUnder E (commSub ⊤ E) := by
    intro x hx u hu
    have h := FixVLat.mem_stabSub_commV_of_mem_normalizer (Subgroup.le_normalizer hx)
    rw [commV_eq_commSub] at h
    exact (mem_stabSub.1 h u).2 hu
  have hbot : commSub ⊤ E ⊓ fixV E = ⊥ := by
    have h := (B1.coprime_decomp hW (odd_card_of_isElemAbelian hp hp2 hE) (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    rw [top_inf_eq, inf_comm] at h
    exact h
  have hUU : commSub (commSub ⊤ E) E = commSub ⊤ E := by
    have h0 := (B1.coprime_decomp hW (odd_card_of_isElemAbelian hp hp2 hE) (M := commSub ⊤ E)
      hstab).1
    rwa [hbot, bot_sup_eq] at h0
  obtain ⟨hdec, -⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.inf_fixV_hyperplane_decomposition
      hW hp hp2 E hE hstab hUU
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_orderOf_eq_two ht
  have hτ : Function.Involutive (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) := conjAutMap_involutive htt
  let S : Finset (Subgroup (MulAut W)) := T ∪
    T.image (fun D : Subgroup (MulAut W) => D.map (MulAut.conj t).toMonoidHom)
  have hSdef : S = T ∪ T.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom) := rfl
  have hTS : T ⊆ S := Finset.subset_union_left
  have hSmem : ∀ D ∈ S, D ∈ hyperplanes p E := by
    intro D hD
    rw [hSdef, Finset.mem_union] at hD
    rcases hD with hD | hD
    · exact (hT D hD).1
    · rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
      exact conjAutMap_mem_hyperplanes htE (hT C hC).1
  have hSfree : ∀ D ∈ S,
      (fun D : Subgroup (MulAut W) => D.map (MulAut.conj t).toMonoidHom) D ≠ D := by
    intro D hD hfix
    rw [hSdef, Finset.mem_union] at hD
    rcases hD with hD | hD
    · exact (hT D hD).2 hfix
    · rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
      have hCfix : (fun D : Subgroup (MulAut W) =>
          D.map (MulAut.conj t).toMonoidHom) C = C :=
        hτ.injective hfix
      exact (hT C hC).2 hCfix
  have hSinv : ∀ D ∈ S,
      (fun D : Subgroup (MulAut W) => D.map (MulAut.conj t).toMonoidHom) D ∈ S := by
    intro D hD
    rw [hSdef, Finset.mem_union] at hD ⊢
    rcases hD with hD | hD
    · exact Or.inr (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
    · rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
      exact Or.inl (by rwa [hτ C])
  obtain ⟨T₁, hT₁sub, hT₁disj, hSdec⟩ := exists_reps_of_involutive hτ hSinv hSfree
  have hT₁mem : ∀ D ∈ T₁, D ∈ hyperplanes p E := fun D hD => hSmem D (hT₁sub hD)
  have hT₁immem : ∀ D ∈ T₁.image (fun D : Subgroup (MulAut W) =>
      D.map (MulAut.conj t).toMonoidHom), D ∈ hyperplanes p E := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
    exact conjAutMap_mem_hyperplanes htE (hT₁mem C hC)
  have hsum_mono : ∑ D ∈ T, rk ↥(hypPart E D) ≤ ∑ D ∈ S, rk ↥(hypPart E D) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTS (fun _ _ _ => Nat.zero_le _)
  have hsumS : ∑ D ∈ S, rk ↥(hypPart E D) = 2 * ∑ D ∈ T₁, rk ↥(hypPart E D) := by
    rw [hSdec, Finset.sum_union hT₁disj, Finset.sum_image]
    · rw [two_mul, Nat.add_comm]
      congr 1
      exact Finset.sum_congr rfl fun D _ => rk_hypPart_map_conj (E := E) (n := t) htE
    · intro x _ y _ hxy
      exact hτ.injective hxy
  have hdisjT₁ : Disjoint (⨆ D ∈ T₁, hypPart E D)
      (⨆ D ∈ T₁.image (fun D : Subgroup (MulAut W) =>
        D.map (MulAut.conj t).toMonoidHom), hypPart E D) :=
    disjoint_iSup_hypPart hdec hT₁mem hT₁immem hT₁disj
  have hAmap : (⨆ D ∈ T₁, hypPart E D).map t.toMonoidHom =
      ⨆ D ∈ T₁.image (fun D : Subgroup (MulAut W) =>
        D.map (MulAut.conj t).toMonoidHom), hypPart E D :=
    map_iSup_hypPart_conjAut htE T₁ hT₁mem
  have hdisjAt : Disjoint (⨆ D ∈ T₁, hypPart E D)
      ((⨆ D ∈ T₁, hypPart E D).map t.toMonoidHom) := by
    rw [hAmap]
    exact hdisjT₁
  have hker : (⨆ D ∈ T₁, hypPart E D) ⊓ (commHom t).ker = ⊥ := by
    rw [ker_commHom]
    exact inf_fixV_eq_bot_of_disjoint_map hdisjAt
  have hrk : rk ↥((⨆ D ∈ T₁, hypPart E D).map (commHom t)) =
      rk ↥(⨆ D ∈ T₁, hypPart E D) := by
    have h := rk_map_add_rk_inf_ker (commHom t) (⨆ D ∈ T₁, hypPart E D)
    rw [hker, rk_bot, add_zero] at h
    exact h
  have hA_le : (⨆ D ∈ T₁, hypPart E D).map (commHom t) ≤ commSub ⊤ (zpowers t) :=
    map_commHom_le_commSub _ t
  have hb : ∑ D ∈ T₁, rk ↥(hypPart E D) ≤ rkIdx (fixV (zpowers t)) := by
    rw [← rk_iSup_hypPart_eq_sum hdec T₁ hT₁mem]
    calc rk ↥(⨆ D ∈ T₁, hypPart E D)
        = rk ↥((⨆ D ∈ T₁, hypPart E D).map (commHom t)) := hrk.symm
      _ ≤ rk ↥(commSub ⊤ (zpowers t)) := rk_mono hA_le
      _ = rkIdx (fixV (zpowers t)) := by
          rw [← commV_eq_commSub,
            CFSG.LocalAnalysis.UniquenessCase.UC22.rk_commV_zpowers_eq_rkIdx_fixV t htt]
  calc ∑ D ∈ T, rk ↥(hypPart E D) ≤ ∑ D ∈ S, rk ↥(hypPart E D) := hsum_mono
    _ = 2 * ∑ D ∈ T₁, rk ↥(hypPart E D) := hsumS
    _ ≤ 2 * rkIdx (fixV (zpowers t)) := Nat.mul_le_mul_left _ hb

theorem dihedralDeg_le_two_mul_rk_commSub_hypPart (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E D₀ X : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    (hD₀ : D₀ ∈ hypSupp p E) (hXE : X ≤ E) (hXp : Nat.card X = p) (hXD : X ⊓ D₀ = ⊥)
    {t : MulAut W} (ht : orderOf t = 2) (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹)
    (hD₀t : D₀.map (MulAut.conj t).toMonoidHom = D₀) :
    WeakClosure81.dihedralDeg p ≤ 2 * rk ↥(commSub (hypPart E D₀) (zpowers t)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_orderOf_eq_two ht
  have hD₀hyp : D₀ ∈ hyperplanes p E := hD₀.1
  have hUne : hypPart E D₀ ≠ ⊥ := hD₀.2
  have hbotE : commSub ⊤ E ⊓ fixV E = ⊥ := by
    have h := (B1.coprime_decomp hW (odd_card_of_isElemAbelian hp hp2 hE) (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).2
    rw [top_inf_eq, inf_comm] at h
    exact h
  have hD₀Xbot : D₀ ⊓ X = ⊥ := by rw [inf_comm]; exact hXD
  have hcardD₀X : Nat.card ↥D₀ * Nat.card ↥X ≤ Nat.card ↥(D₀ ⊔ X) :=
    CFSG.GroupTheory.card_mul_card_le_card_sup_of_disjoint (G := MulAut W) (H := D₀)
      (K := X) (disjoint_iff.mpr hD₀Xbot)
  have hcardE : Nat.card E = Nat.card D₀ * p := by
    have h := Subgroup.relIndex_mul_card (H := D₀) (K := E)
    rw [inf_eq_left.mpr hD₀hyp.1, hD₀hyp.2] at h
    rw [← h, Nat.mul_comm]
  have hsup_le : D₀ ⊔ X ≤ E := sup_le hD₀hyp.1 hXE
  have hEeq : D₀ ⊔ X = E := by
    refine Subgroup.eq_of_le_of_card_ge hsup_le ?_
    rw [hcardE, ← hXp]
    exact hcardD₀X
  have hXmap_le : X.map (MulAut.conj t).toMonoidHom ≤ X := by
    rintro y ⟨x, hx, rfl⟩
    change t * x * t⁻¹ ∈ X
    rw [hinv x hx]
    exact X.inv_mem hx
  have hXmap_eq : X.map (MulAut.conj t).toMonoidHom = X := by
    refine Subgroup.eq_of_le_of_card_ge hXmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hEmap : E.map (MulAut.conj t).toMonoidHom = E := by
    rw [← hEeq, Subgroup.map_sup, hD₀t, hXmap_eq]
  have htE : t ∈ normalizer (E : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEmap
  have hXrank : IsElemAbelianOfRank p 1 ↥X := by
    have hcard : Nat.card (Multiplicative (Fin 1 → ZMod p)) = p := by
      simp [Nat.card_eq_fintype_card]
    exact ⟨mulEquivOfPrimeCardEq hXp hcard⟩
  have hXcommSub : X ≤ stabSub (commSub ⊤ E) := by
    intro x hx
    have h := FixVLat.mem_stabSub_commV_of_mem_normalizer (Subgroup.le_normalizer (hXE hx))
    rwa [commV_eq_commSub] at h
  have hXN : X ≤ Subgroup.normalizer (D₀ : Set (MulAut W)) := by
    have hcent : D₀ ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
      intro d hd x hx
      exact (congrArg Subtype.val
        (hE.1.is_comm.comm (⟨d, hD₀hyp.1 hd⟩ : ↥E) (⟨x, hXE hx⟩ : ↥E))).symm
    exact (Subgroup.le_centralizer_iff.mpr hcent).trans
      (Subgroup.centralizer_le_normalizer (D₀ : Set (MulAut W)))
  have hXfix : X ≤ stabSub (fixV D₀) := FixVLat.le_stabSub_fixV_of_le_normalizer hXN
  have hUX : StableUnder X (hypPart E D₀) := by
    intro x hx u hu
    exact ⟨(mem_stabSub.1 (hXcommSub hx) u).2 hu.1,
      (mem_stabSub.1 (hXfix hx) u).2 hu.2⟩
  have htcommSub : t ∈ stabSub (commSub ⊤ E) := by
    have h := FixVLat.mem_stabSub_commV_of_mem_normalizer htE
    rwa [commV_eq_commSub] at h
  have htN : t ∈ Subgroup.normalizer (D₀ : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hD₀t
  have htzp : Subgroup.zpowers t ≤ Subgroup.normalizer (D₀ : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr htN
  have htfix : t ∈ stabSub (fixV D₀) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer htzp (Subgroup.mem_zpowers t)
  have hUt : ∀ u ∈ hypPart E D₀, t u ∈ hypPart E D₀ := by
    intro u hu
    exact ⟨(mem_stabSub.1 htcommSub u).2 hu.1, (mem_stabSub.1 htfix u).2 hu.2⟩
  have hfaith : ∀ x ∈ X, (∀ u ∈ hypPart E D₀, x u = u) → x = 1 := by
    intro x hxX hfixx
    by_contra hxne
    have hxpow : x ^ p = 1 := hE.2 x (hXE hxX)
    have hord : orderOf x = p := orderOf_eq_prime hxpow hxne
    have hcardzp : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, hord]
    have hzpX : Subgroup.zpowers x = X :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) (by rw [hcardzp, hXp])
    have hD₀cent : D₀ ≤ centSub (hypPart E D₀) := by
      intro d hd
      exact mem_centSub.mpr fun u hu => hu.2 d hd
    have hXcent : X ≤ centSub (hypPart E D₀) := by
      rw [← hzpX]
      exact Subgroup.zpowers_le.mpr (mem_centSub.mpr hfixx)
    have hEcent : E ≤ centSub (hypPart E D₀) := by
      have hsup : D₀ ⊔ X ≤ centSub (hypPart E D₀) := sup_le hD₀cent hXcent
      rwa [hEeq] at hsup
    have hUfixE : hypPart E D₀ ≤ fixV E := by
      intro u hu e he
      exact mem_centSub.mp (hEcent he) u hu
    have hUbot : hypPart E D₀ = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hmem : u ∈ commSub ⊤ E ⊓ fixV E := ⟨hu.1, hUfixE hu⟩
      rwa [hbotE] at hmem
    exact hUne hUbot
  have h := CFSG.LocalAnalysis.WeakClosure81.n_mul_dihedralDeg_le_two_mul_rk_on
    hW ht hp hp2 Nat.one_pos hXrank hinv hUX hUt hfaith
  simpa using h

theorem commSub_inf_fixV_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E) : commSub ⊤ E ⊓ fixV E = ⊥ := by
  have h := (B1.coprime_decomp hW (odd_card_of_isElemAbelian hp hp2 hE) (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)).2
  rw [top_inf_eq, inf_comm] at h
  exact h

omit [Finite W] in
theorem mem_commSub_of_mem_normalizer {E : Subgroup (MulAut W)} {n : MulAut W}
    (hn : n ∈ normalizer (E : Set (MulAut W))) {w : W} (hw : w ∈ commSub ⊤ E) :
    n w ∈ commSub ⊤ E := by
  have h := FixVLat.mem_stabSub_commV_of_mem_normalizer hn
  rw [commV_eq_commSub] at h
  exact (mem_stabSub.1 h w).2 hw

theorem rk_commSub_le_rk (E : Subgroup (MulAut W)) : rk ↥(commSub ⊤ E) ≤ rk W := by
  have h := rk_mono (H := commSub ⊤ E) (K := ⊤) le_top
  rwa [rk_top] at h

omit [Finite W] in
theorem le_mParam_of_forall {X : Subgroup (MulAut W)} {c : ℕ}
    (hX : ∃ t ∈ X, orderOf t = 2)
    (h : ∀ t ∈ X, orderOf t = 2 → c ≤ rkIdx (fixV (zpowers t))) : c ≤ E3.mParam X := by
  classical
  obtain ⟨t₀, ht₀X, ht₀⟩ := hX
  have hev : Even (Nat.card X) := by
    rw [even_iff_two_dvd]
    have hdvd : orderOf t₀ ∣ Nat.card ↥X := Subgroup.orderOf_dvd_natCard X ht₀X
    exact ht₀ ▸ hdvd
  have hne : {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty :=
    ⟨_, t₀, ht₀X, ht₀, rfl⟩
  obtain ⟨t, htX, ht2, htEq⟩ := Nat.sInf_mem hne
  unfold E3.mParam
  rw [if_pos hev, htEq]
  exact h t htX ht2

theorem rk_commSub_le_rkIdx_fixV (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E H : Subgroup (MulAut W)} (hE : IsElemAbelian p E) (hEH : E ≤ H) :
    rk ↥(commSub ⊤ E) ≤ rkIdx (fixV H) := by
  have hbot : commSub ⊤ E ⊓ fixV H = ⊥ := by
    have hle : commSub ⊤ E ⊓ fixV H ≤ commSub ⊤ E ⊓ fixV E :=
      inf_le_inf_left _ (B1.fixV_le_fixV hEH)
    rw [eq_bot_iff]
    exact hle.trans (le_of_eq (commSub_inf_fixV_eq_bot hW hp hp2 hE))
  have h1 : rk ↥(commSub ⊤ E) + rk ↥(fixV H) ≤ rk W := by
    rw [← rk_sup_add_rk_inf (commSub ⊤ E) (fixV H), hbot, rk_bot, add_zero]
    calc rk ↥(commSub ⊤ E ⊔ fixV H) ≤ rk (⊤ : Subgroup W) := rk_mono le_top
      _ = rk W := rk_top
  have h2 := rk_add_rkIdx (fixV H)
  omega

theorem rkIdx_fixV_closure_le_three_mul (hW : ∀ w : W, w ^ 2 = 1) {t x y z : MulAut W}
    (_ht : orderOf t = 2) :
    rkIdx (fixV (closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)))) ≤
      3 * rkIdx (fixV (zpowers t)) := by
  classical
  have hset : ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)) =
      (({x * t * x⁻¹} : Set (MulAut W)) ∪ {y * t * y⁻¹}) ∪ {z * t * z⁻¹} := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  have hcl : Subgroup.closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)) =
      Subgroup.zpowers (x * t * x⁻¹) ⊔ Subgroup.zpowers (y * t * y⁻¹) ⊔
        Subgroup.zpowers (z * t * z⁻¹) := by
    rw [hset, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hidx : (fixV (Subgroup.closure
      ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)))).index ≤
      (fixV (Subgroup.zpowers t)).index ^ 3 := by
    rw [hcl, FixVLat.fixV_sup_eq, FixVLat.fixV_sup_eq]
    calc (((fixV (Subgroup.zpowers (x * t * x⁻¹)) ⊓
          fixV (Subgroup.zpowers (y * t * y⁻¹))) ⊓
          fixV (Subgroup.zpowers (z * t * z⁻¹)))).index
        ≤ (fixV (Subgroup.zpowers (x * t * x⁻¹)) ⊓
            fixV (Subgroup.zpowers (y * t * y⁻¹))).index *
            (fixV (Subgroup.zpowers (z * t * z⁻¹))).index := Subgroup.index_inf_le
      _ ≤ ((fixV (Subgroup.zpowers (x * t * x⁻¹))).index *
            (fixV (Subgroup.zpowers (y * t * y⁻¹))).index) *
            (fixV (Subgroup.zpowers (z * t * z⁻¹))).index :=
          Nat.mul_le_mul_right _ Subgroup.index_inf_le
      _ = (fixV (Subgroup.zpowers t)).index ^ 3 := by
          rw [FixVLat.index_fixV_zpowers_conj x t,
            FixVLat.index_fixV_zpowers_conj y t,
            FixVLat.index_fixV_zpowers_conj z t]
          ring
  have hle : rkIdx (fixV (Subgroup.closure
      ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)))) ≤
      3 * rkIdx (fixV (Subgroup.zpowers t)) := by
    have h1 : (fixV (Subgroup.closure
        ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)))).index =
        2 ^ rkIdx (fixV (Subgroup.closure
          ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)))) :=
      B1.index_eq_two_pow hW _
    have h2 : (fixV (Subgroup.zpowers t)).index = 2 ^ rkIdx (fixV (Subgroup.zpowers t)) :=
      B1.index_eq_two_pow hW _
    have h := hidx
    rw [h1, h2, ← pow_mul] at h
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    omega
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
