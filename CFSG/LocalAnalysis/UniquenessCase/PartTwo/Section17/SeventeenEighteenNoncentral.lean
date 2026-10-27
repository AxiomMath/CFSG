module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TwoQuotientTransfers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenPDichotomy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def NoncentralThreeFact (L : Subgroup G) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), Inputs1719.KYForm Y K S →
    Nonempty (↥K ≃* Bar2 L) →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S

theorem exists_noncentral_three_K1Nine {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hK : NoncentralThreeFact L) :
    ∃ E : Subgroup (Mbar9 D), E ≤ K1Nine D L ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype ∧
      Permutes E (S1Nine D L) :=
  exists_noncentral_three_K1Nine_of_pow hL (n := 0) (fun _ _ => by simp)
    (fun Y _ _ K S hKY hKe _ => hK Y K S hKY hKe)

theorem exists_noncyclic_permutes_of_moved {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {E : Subgroup (Mbar9 D)} (hEK : E ≤ K1Nine D L) (hEne : E ≠ ⊥) (hEp : IsPGroup 3 ↥E)
    (hEexp : ∀ x ∈ E, x ^ 3 = 1)
    (hEnc : ¬ E ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype)
    (hEperm : Permutes E (S1Nine D L))
    (hKne : ∃ t ∈ Tbar9 D, (K1Nine D L).map (MulAut.conj t).toMonoidHom ≠ K1Nine D L) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  obtain ⟨Xbar, hE_le_Xbar, hXbarT, hXbarExp, hXbarP, hXbarNcyc⟩ :=
    exists_noncyclic_permutes_sup_conj (H := Mbar9 D) (K := K1Nine D L) (T := Tbar9 D) (A := E)
      hEK (commute_of_ne_conj_K1Nine hL) hEperm hKne hEnc hEexp
  have hXbarNe : Xbar ≠ ⊥ := fun hbot => hEne (le_bot_iff.mp (hbot ▸ hE_le_Xbar))
  exact exists_permutes_of_Mbar9 D hXbarNe (hXbarP 3 hEp) (hXbarExp 3 hEexp) hXbarNcyc hXbarT

theorem exists_noncyclic_permutes_of_two {D : Data G} {L L' : Subgroup G} (hL : L ∈ calC D.M)
    (hL' : L' ∈ calC D.M) (hne : L' ≠ L) {E E' : Subgroup (Mbar9 D)}
    (hEK : E ≤ K1Nine D L) (hE'K : E' ≤ K1Nine D L')
    (hEexp : ∀ x ∈ E, x ^ 3 = 1) (hE'exp : ∀ x ∈ E', x ^ 3 = 1) (hE'ne : E' ≠ ⊥)
    (hEnc : ¬ E ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype)
    (hEperm : Permutes E (Tbar9 D)) (hE'perm : Permutes E' (Tbar9 D)) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  have hKne : K1Nine D L' ≠ K1Nine D L := fun h =>
    hne (eq_of_mem_calC_of_imageOTwoQuot_eq hL' hL h)
  have hcomm : ∀ a ∈ K1Nine D L', ∀ b ∈ K1Nine D L, a * b = b * a := fun a ha b hb =>
    CFSG.StandardType.ggCommute_of_isComponent_ne (isComponent_K1 hL) (isComponent_K1 hL')
      hKne ha hb
  have hBA : E' ≤ Subgroup.normalizer (E : Set (Mbar9 D)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (E : Set (Mbar9 D)))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcomm b (hE'K hb) a (hEK ha)).symm
  have hEset : ((E ⊔ E' : Subgroup (Mbar9 D)) : Set (Mbar9 D)) = (E : Set _) * (E' : Set _) :=
    Subgroup.coe_mul_of_right_le_normalizer_left E E' hBA
  have hPerm : Permutes (E ⊔ E') (Tbar9 D) := by
    unfold Permutes
    rw [hEset, mul_assoc, hE'perm, ← mul_assoc, hEperm, mul_assoc]
  have hExp : ∀ e ∈ E ⊔ E', e ^ 3 = 1 := by
    intro e he
    have he' : e ∈ (E : Set (Mbar9 D)) * (E' : Set (Mbar9 D)) := by
      rw [← hEset]
      exact he
    obtain ⟨a, ha, b, hb, rfl⟩ := he'
    have hab : Commute a b := (hcomm b (hE'K hb) a (hEK ha)).symm
    rw [hab.mul_pow, hEexp a ha, hE'exp b hb, one_mul]
  have hP3 : IsPGroup 3 ↥(E ⊔ E') := fun g =>
    ⟨1, Subtype.ext (by simpa using hExp g g.2)⟩
  have hE'le : E' ≤ E ⊔ E' := le_sup_right
  have hNe : E ⊔ E' ≠ ⊥ := fun h => hE'ne (le_bot_iff.mp (h ▸ hE'le))
  have hNc : ¬ IsCyclic ↥(E ⊔ E') := by
    intro hcyc
    have hdvd : Nat.card ↥(E ⊔ E') ∣ 3 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one
        (fun g => Subtype.ext (by simpa using hExp g g.2))
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact hNe (Subgroup.card_eq_one.mp h1)
    · have : Fact (Nat.card ↥(E ⊔ E')).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E'.subgroupOf (E ⊔ E')) with hb | ht
      · apply hE'ne
        rw [Subgroup.subgroupOf_eq_bot] at hb
        exact le_bot_iff.mp (hb le_rfl hE'le)
      · rw [Subgroup.subgroupOf_eq_top] at ht
        apply hEnc
        intro a ha
        have haK : a ∈ K1Nine D L := hEK ha
        have haK' : a ∈ K1Nine D L' := hE'K (ht (Subgroup.mem_sup_left ha))
        refine ⟨⟨a, haK⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact (hcomm a haK' k k.2).symm
  exact exists_permutes_of_Mbar9 D hNe hP3 hExp hNc hPerm

theorem exists_inP11_of_not_normal_of_noncentral (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hN : ¬ (L.subgroupOf D.M).Normal) (hK : NoncentralThreeFact L) :
    ∃ X : Subgroup G, F11.InP11 D X := by
  have hLM : L ≤ D.M := hL.1.le
  have hnotN : ¬ D.M ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h)
  obtain ⟨g, hgM, hgN⟩ := SetLike.not_le_iff_exists.mp hnotN
  have hMmap : D.M.map (MulAut.conj g).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)
  have hL' : uc22p20bCj g L ∈ calC D.M := by
    have h := UC6S846.calC_map D.M (MulAut.conj g) hMmap hL
    simpa [uc22p20bCj] using h
  have hne : uc22p20bCj g L ≠ L := by
    intro h
    apply hgN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [uc22p20bCj] using h
  have hK' : NoncentralThreeFact (uc22p20bCj g L) := by
    intro Y _ _ K S hKY hKe
    obtain ⟨e⟩ := hKe
    obtain ⟨f⟩ := uc22p20d_bar2_conj g L
    exact hK Y K S hKY ⟨e.trans f.symm⟩
  suffices h : ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T by
    obtain ⟨X, hXM, -, hXp, hXexp, hXnc, hXperm⟩ := h
    exact ⟨X, inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM hXp hXexp hXnc hXperm⟩
  by_cases h1 : ∃ t ∈ Tbar9 D, (K1Nine D L).map (MulAut.conj t).toMonoidHom ≠ K1Nine D L
  · obtain ⟨E, hEK, hEne, hEp, hEexp, hEnc, hEperm⟩ := exists_noncentral_three_K1Nine hL hK
    exact exists_noncyclic_permutes_of_moved hL hEK hEne hEp hEexp hEnc hEperm h1
  by_cases h2 : ∃ t ∈ Tbar9 D, (K1Nine D (uc22p20bCj g L)).map (MulAut.conj t).toMonoidHom ≠
      K1Nine D (uc22p20bCj g L)
  · obtain ⟨E, hEK, hEne, hEp, hEexp, hEnc, hEperm⟩ := exists_noncentral_three_K1Nine hL' hK'
    exact exists_noncyclic_permutes_of_moved hL' hEK hEne hEp hEexp hEnc hEperm h2
  have hT1 : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
    intro t ht
    by_contra hn
    exact h1 ⟨t, ht, (Subgroup.mem_normalizer_iff_map_conj_eq).not.mp hn⟩
  have hT2 : Tbar9 D ≤ Subgroup.normalizer (K1Nine D (uc22p20bCj g L) : Set (Mbar9 D)) := by
    intro t ht
    by_contra hn
    exact h2 ⟨t, ht, (Subgroup.mem_normalizer_iff_map_conj_eq).not.mp hn⟩
  have hS1 : S1Nine D L = Tbar9 D := inf_eq_left.mpr hT1
  have hS2 : S1Nine D (uc22p20bCj g L) = Tbar9 D := inf_eq_left.mpr hT2
  obtain ⟨E, hEK, -, -, hEexp, hEnc, hEperm⟩ := exists_noncentral_three_K1Nine hL hK
  obtain ⟨E', hE'K, hE'ne, -, hE'exp, -, hE'perm⟩ := exists_noncentral_three_K1Nine hL' hK'
  rw [hS1] at hEperm
  rw [hS2] at hE'perm
  exact exists_noncyclic_permutes_of_two hL hL' hne hEK hE'K hEexp hE'exp hE'ne hEnc hEperm
    hE'perm

theorem isSpor_quot_center_of_bar2 {M L : Subgroup G} (hL : L ∈ calC M)
    {s : TauCeti.SporadicName} (hs : IsSpor (BarInf L) s) {Y : Type} [Group Y]
    {K : Subgroup Y} (e : ↥K ≃* Bar2 L) : IsSpor (↥K ⧸ Subgroup.center ↥K) s := by
  obtain ⟨eBI⟩ := UC22.uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨eS⟩ := hs
  let eZ : (↥K ⧸ Subgroup.center ↥K) ≃* (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨(eZ.trans eBI.symm).trans eS⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
