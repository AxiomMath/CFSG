module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.Fischer.HermitianEquiv
public import CFSG.Fischer.Classification.Unitary.Star

public section

namespace CFSG.Timmesfeld.Transvection.QTwo

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Open

@[expose] def StarFree (Y : Type) [Group Y] (F : Set Y) : Prop :=
  ∀ x ∈ F, ∀ y ∈ LocalClass F x, ∃ z ∈ LocalClass F x, z * y ≠ y * z

theorem StarFree.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] {F : Set Y} {F' : Set Y'}
    (φ : Y ≃* Y') (hF : φ '' F = F') (h : StarFree Y' F') : StarFree Y F := by
  intro x hx y hy
  have hx' : φ x ∈ F' := hF ▸ ⟨x, hx, rfl⟩
  have hy' : φ y ∈ LocalClass F' (φ x) := by
    rw [localClass_congr φ hF rfl]
    exact ⟨y, hy, rfl⟩
  obtain ⟨z', hz', hne⟩ := h _ hx' _ hy'
  rw [localClass_congr φ hF rfl] at hz'
  obtain ⟨z, hz, rfl⟩ := hz'
  exact ⟨z, hz, fun h' => hne (by rw [← map_mul, ← map_mul, h'])⟩

theorem starFree_of_one_notMem {Y : Type} [Group Y] {F : Set Y}
    (h : ∀ x ∈ F, (1 : LocalQuotient F x) ∉ LocalImages F x) : StarFree Y F := by
  intro x hx y hy
  by_contra! hall
  apply h x hx
  rw [← range_starImage]
  exact ⟨⟨y, hy⟩, (starImage_eq_one_iff _).2 hall⟩

theorem hermitian_one (x y : V) : hermitian 1 x y = fischerHermitianF4 6 x y := by
  rw [hermitian, fischerHermitianF4]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [Matrix.one_apply_ne hji.symm, mul_zero,
    zero_mul]) (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, mul_one]

theorem SU_one_eq_SUm : SU (1 : Matrix (Fin 6) (Fin 6) K) = SUm 6 := by
  rw [SU, SUm, fischerMatrixGroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, hermitian_one]
  refine and_congr_left fun _ => ?_
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

noncomputable def psuOneEquivU2 : PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* U2 6 :=
  quotientCenterCongr (MulEquiv.subgroupCongr SU_one_eq_SUm)

theorem psuOneEquivU2_mk (u : SU (1 : Matrix (Fin 6) (Fin 6) K)) :
    psuOneEquivU2 (QuotientGroup.mk u) =
      QuotientGroup.mk ⟨(u : GL (Fin 6) K), SU_one_eq_SUm ▸ u.2⟩ := by
  rw [psuOneEquivU2, quotientCenterCongr_mk]
  rfl

theorem psuOneEquivU2_image : psuOneEquivU2 '' Transvections 1 = DU 6 := by
  ext q
  constructor
  · rintro ⟨_, ⟨u, rfl, v, hv0, hv, hx⟩, rfl⟩
    refine ⟨⟨(u : GL (Fin 6) K), SU_one_eq_SUm ▸ u.2⟩, ⟨v, ⟨hv0, ?_⟩, fun x => ?_⟩, ?_⟩
    · rwa [← hermitian_one]
    · rw [← hermitian_one]
      exact hx x
    · rw [psuOneEquivU2_mk]
  · rintro ⟨h, ⟨v, ⟨hv0, hv⟩, hx⟩, rfl⟩
    refine ⟨QuotientGroup.mk ⟨(h : GL (Fin 6) K), SU_one_eq_SUm.symm ▸ h.2⟩,
      ⟨_, rfl, v, hv0, by rwa [hermitian_one], fun x => by rw [hermitian_one]; exact hx x⟩, ?_⟩
    rw [psuOneEquivU2_mk]

theorem starFree_DG : StarFree (PG 6) (DG 6) := by
  rintro _ ⟨v, hv0, hv, rfl⟩ y hy
  exact exists_not_commute_localClass_DG (by norm_num) hv0 hv y hy

theorem starFree_PSU {Hm : Matrix (Fin 6) (Fin 6) K} (hH : IsNondegenerateHermitian Hm) :
    StarFree (PSU Hm) (Transvections Hm) := by
  obtain ⟨iso, himg⟩ := exists_psu_equiv hH
  have himg' : iso.symm '' Transvections Hm = Transvections 1 := by
    rw [← himg]
    exact image_symm_image iso _
  refine StarFree.of_mulEquiv iso.symm himg' ?_
  refine StarFree.of_mulEquiv psuOneEquivU2 psuOneEquivU2_image ?_
  exact StarFree.of_mulEquiv (u2Equiv 6) (image_DU 6) starFree_DG

theorem one_notMem_transvections {Hm : Matrix (Fin 6) (Fin 6) K}
    (hH : IsNondegenerateHermitian Hm) : (1 : PSU Hm) ∉ Transvections Hm := by
  obtain ⟨iso, himg⟩ := exists_psu_equiv hH
  intro h1
  rw [← himg] at h1
  obtain ⟨t, ht, hte⟩ := h1
  have ht1 : t = 1 := iso.injective (by rw [hte, map_one])
  subst ht1
  have hmem : psuOneEquivU2 1 ∈ DU 6 := psuOneEquivU2_image ▸ ⟨1, ht, rfl⟩
  rw [map_one] at hmem
  exact Pair.ne_one (pair_DU (by norm_num)) hmem rfl

variable {H : Type} [Group H] {D : Set H}

theorem starFree_localQuotient_of_hasType {k : Fin 3} (h : HasType k H D) {e : H} (he : e ∈ D) :
    StarFree (LocalQuotient D e) (LocalImages D e) := by
  match k, h with
  | ⟨0, _⟩, h =>
    obtain ⟨Hm, hHm, iso, himg⟩ := F22_local h he
    exact StarFree.of_mulEquiv iso himg (starFree_PSU hHm)
  | ⟨1, _⟩, h =>
    have h22 := F23_local h he
    refine starFree_of_one_notMem fun x hx h1 => ?_
    obtain ⟨Hm, hHm, iso, himg⟩ := F22_local h22 hx
    apply one_notMem_transvections hHm
    rw [← himg, ← map_one iso]
    exact ⟨1, h1, rfl⟩
  | ⟨2, _⟩, h =>
    have h23 := F24_local h he
    refine starFree_of_one_notMem fun x hx h1 => ?_
    exact Pair.ne_one (F23_local h23 hx).1 h1 rfl

theorem commute_of_starFree (hP : Pair H D) {e f g : H} (he : e ∈ D) (hf : f ∈ D) (hg : g ∈ D)
    (hef : e ≠ f) (hc : e * f = f * e) (hge : g ≠ e) (hgf : g ≠ f)
    (hall : ∀ d ∈ D, d * e = e * d → d * f = f * d → d * g = g * d)
    (hloc : StarFree (LocalQuotient D e) (LocalImages D e)) :
    ∀ d ∈ D, d * e = e * d → d * f = f * d := by
  have hfe : f ∈ LocalClass D e := ⟨hf, fun h => hef h.symm, hc.symm⟩
  have hge' : g ∈ LocalClass D e := ⟨hg, hge, (hall e he rfl hc).symm⟩
  have hfg : f * g = g * f := hall f hf hc.symm rfl
  have heq : starImage D e ⟨f, hfe⟩ = starImage D e ⟨g, hge'⟩ := by
    by_contra hne
    have hsf : starImage D e ⟨f, hfe⟩ ∈ LocalImages D e := by
      rw [← range_starImage]
      exact ⟨_, rfl⟩
    have hsg : starImage D e ⟨g, hge'⟩ ∈ LocalClass (LocalImages D e)
        (starImage D e ⟨f, hfe⟩) := by
      refine ⟨by rw [← range_starImage]; exact ⟨_, rfl⟩, fun h => hne h.symm, ?_⟩
      exact ((Pair.starImage_commute_iff hP ⟨g, hge'⟩ ⟨f, hfe⟩).2 hfg.symm)
    obtain ⟨z, hz, hzne⟩ := hloc _ hsf _ hsg
    obtain ⟨d, rfl⟩ : ∃ d, starImage D e d = z := by
      rw [← Set.mem_range, range_starImage]
      exact hz.1
    have hdf : (d : H) * f = f * d :=
      (Pair.starImage_commute_iff hP d ⟨f, hfe⟩).1 hz.2.2
    exact hzne ((Pair.starImage_commute_iff hP d ⟨g, hge'⟩).2
      (hall d d.2.1 d.2.2.2 hdf))
  have hcen := (starImage_eq_starImage_iff _ _).1 heq
  have hfi : f⁻¹ = f := Pair.inv_eq hP hf
  simp only [hfi] at hcen
  intro d hd hde
  by_cases hd_e : d = e
  · rw [hd_e]
    exact hc
  have hdL : d ∈ LocalClass D e := ⟨hd, hd_e, hde⟩
  by_contra hdf
  have hzd : d * (f * g) = (f * g) * d := hcen d (mem_localGroup hdL)
  have hzf : f * (f * g) = (f * g) * f := hcen f (mem_localGroup hfe)
  have h3 : orderOf (d * f) = 3 := Pair.orderOf_mul_eq_three hP hd hf hdf
  have h2 : orderOf (f * g) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, mul_assoc, ← mul_assoc g, ← hfg, mul_assoc, Pair.mul_self hP hg, mul_one,
        Pair.mul_self hP hf]
    · intro h1
      apply hgf
      calc g = f * (f * g) := by rw [← mul_assoc, Pair.mul_self hP hf, one_mul]
        _ = f := by rw [h1, mul_one]
  have hcomm : Commute (d * f) (f * g) := by
    change d * f * (f * g) = f * g * (d * f)
    rw [mul_assoc, hzf, ← mul_assoc, hzd, mul_assoc]
  have h6 := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h3, h2]; norm_num)
  rw [h3, h2, show d * f * (f * g) = d * g by
    rw [mul_assoc, ← mul_assoc f, Pair.mul_self hP hf, one_mul]] at h6
  have hmem := Pair.orderOf_mul_mem hP hd hg
  rw [h6] at hmem
  simp at hmem

theorem false_of_starFree (hQ : QHyp H D)
    (hloc : ∀ e ∈ D, StarFree (LocalQuotient D e) (LocalImages D e)) : False := by
  have hP := hQ.hyp.pair
  obtain ⟨e, he, f, hf, hef, hc⟩ := hQ.rank
  obtain ⟨g, hg, hge, hgf, hall⟩ := hQ.thick e he f hf hef hc
  have h1 := commute_of_starFree hP he hf hg hef hc hge hgf hall (hloc e he)
  have h2 := commute_of_starFree hP hf he hg (fun h => hef h.symm) hc.symm hgf hge
    (fun d hd hdf hde => hall d hd hde hdf) (hloc f hf)
  exact hef (hQ.points e he f hf fun d hd => ⟨h1 d hd, h2 d hd⟩)

theorem not_hasType (hQ : QHyp H D) (k : Fin 3) : ¬ HasType k H D := fun h =>
  false_of_starFree hQ fun _ he => starFree_localQuotient_of_hasType h he

end CFSG.Timmesfeld.Transvection.QTwo
