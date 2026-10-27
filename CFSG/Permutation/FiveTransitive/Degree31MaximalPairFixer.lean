module

public import CFSG.Permutation.FiveTransitive.Degree31PairFixerBound
public import CFSG.Permutation.FiveTransitive.OddMaximalOrderDescent
public import CFSG.Permutation.FiveTransitive.ThroughEighteenClassification
public import CFSG.Permutation.FiveTransitive.ClassifiedFixedFiveImage

public section

namespace CFSG

namespace FiveTransitive.Degree31MaximalPairFixer

open MulAction FixedNormalizerAction

private theorem card_mul_image_dvd
    {G X : Type*} [Group G] [Finite G] [MulAction G X] (Q : Subgroup G) :
    Nat.card Q * Nat.card (Image (X := X) Q) ∣ Nat.card G := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hle : Inside Q ≤ f.ker := by
    intro q hq
    change toPermHom (Normalizer Q) (Fixed (X := X) Q) q = 1
    apply Equiv.ext
    intro x
    exact Subtype.ext (x.property ⟨q,hq⟩)
  have hd : Nat.card Q ∣ Nat.card f.ker := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have hm : Nat.card f.ker * Nat.card f.range = Nat.card (Normalizer Q) := by
    rw [← Subgroup.index_ker]
    exact f.ker.card_mul_index
  have hprod := Nat.mul_dvd_mul_right hd (Nat.card f.range)
  rw [hm] at hprod
  exact hprod.trans (Subgroup.card_subgroup_dvd_card (Normalizer Q))

private theorem ambient_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096) :
    Nat.card P = 83514654720 := by
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  exact hm.symm

private theorem fixed_seven_image_top_of_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hP : Nat.card P = 83514654720)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q = 2048)
    (hfixed : 6 ≤ Nat.card (fixedPoints Q X)) :
    Nat.card (fixedPoints Q X) = 7 ∧ Image (X := X) Q = ⊤ := by
  classical
  have hne : Q ≠ ⊥ := by
    intro he
    rw [he] at hQcard
    simp at hQcard
  have hmax : ∀ T : Subgroup P, IsPGroup 2 T → 6 ≤ Nat.card (fixedPoints T X) →
      Nat.card T ≤ Nat.card Q := by
    intro T hT hTf
    rw [hQcard]
    exact Degree31PairFixerBound.card_le_two_thousand_forty_eight P hcard h5 hnotAlt T hT hTf
  obtain ⟨hseven,hodd,hlt,hhalf,htrans,hlocal⟩ := OddMaximalOrderDescent.local_structure
    X P (by omega) h5 hnotAlt (by rw [hcard]; decide) Q hQ hne hfixed hmax
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  let _ : Fintype (Image (X := X) Q) := Fintype.ofFinite _
  have hclass := ThroughEighteenClassification.faithful_action_card_classification
    (Image (X := X) Q) (Fixed (X := X) Q)
    (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Nat.card (Fixed (X := X) Q) by omega))
    (by rw [hcard] at hhalf; simpa only [Nat.card_eq_fintype_card] using (show Nat.card (Fixed (X := X) Q) ≤ 18 by omega))
    (by
      intro a b ha hb
      obtain ⟨g,hg⟩ := htrans.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ Fixed (X := X) Q) ⟨b,hb⟩
      exact ⟨g,fun i => DFunLike.congr_fun hg i⟩)
  have hpairs := ClassifiedFixedFiveImage.degree_order_pairs Q hseven hodd htrans hlocal
    (by simpa only [Nat.card_eq_fintype_card] using hclass)
  rcases hpairs with ⟨hf,hi⟩ | ⟨_,hi⟩
  · refine ⟨by simpa only [fixed_eq] using hf,?_⟩
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_perm,hf,hi]
    norm_num [Nat.factorial]
  · have hd := card_mul_image_dvd (X := X) Q
    rw [hQcard,hi,hP] at hd
    norm_num at hd

theorem fixed_seven_image_top
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q = 2048)
    (hfixed : 6 ≤ Nat.card (fixedPoints Q X)) :
    Nat.card (fixedPoints Q X) = 7 ∧ Image (X := X) Q = ⊤ :=
  fixed_seven_image_top_of_card P hcard h5 hnotAlt (ambient_card P hcard h5 s hs hH)
    Q hQ hQcard hfixed

theorem full_fixer_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hall : ∀ s : Set X, s.ncard = 5 → Nat.card (fixingSubgroup P s) = 4096)
    (Q : Subgroup P) (hQcard : Nat.card Q = 2048)
    (t : Set X) (ht : 6 ≤ t.ncard) (htfix : t ⊆ fixedPoints Q X) :
    fixingSubgroup P t = Q := by
  classical
  have ht5 : 5 ≤ Nat.card t := by rw [Nat.card_coe_set_eq]; omega
  let b : Fin 5 ↪ t :=
    (Fin.castLEEmb ht5).trans (Finite.equivFin t).symm.toEmbedding
  let bX : Fin 5 ↪ X := b.trans (Function.Embedding.subtype _)
  let s : Set X := Set.range bX
  have hs : s.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective bX.injective
  have hst : s ⊆ t := by rintro x ⟨i,rfl⟩; exact (b i).property
  have hle : fixingSubgroup P t ≤ fixingSubgroup P s := by
    intro g hg
    exact (mem_fixingSubgroup_iff P).mpr (fun x hx =>
      (mem_fixingSubgroup_iff P).mp hg x (hst hx))
  have htwo : IsPGroup 2 (fixingSubgroup P t) := by
    apply IsPGroup.of_card_dvd_pow (n := 12)
    have hd := Subgroup.card_dvd_of_le hle
    rw [hall s hs] at hd
    exact hd
  have htf : t ⊆ fixedPoints (fixingSubgroup P t) X := by
    intro x hx q
    exact (mem_fixingSubgroup_iff P).mp q.property x hx
  have htf6 : 6 ≤ Nat.card (fixedPoints (fixingSubgroup P t) X) := by
    rw [Nat.card_coe_set_eq]
    exact ht.trans (Set.ncard_le_ncard htf)
  have hb := Degree31PairFixerBound.card_le_two_thousand_forty_eight
    P hcard h5 hnotAlt (fixingSubgroup P t) htwo htf6
  have hQle : Q ≤ fixingSubgroup P t := by
    intro q hq
    exact (mem_fixingSubgroup_iff P).mpr (fun x hx => htfix hx ⟨q,hq⟩)
  exact (Subgroup.eq_of_le_of_card_ge hQle (by omega)).symm

end FiveTransitive.Degree31MaximalPairFixer

end CFSG
