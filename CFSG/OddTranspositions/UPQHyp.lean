module

public import CFSG.OddTranspositions.QHypTransvection
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.Fischer.Classification.Basic.Reduced

public section
namespace CFSG.OddTranspositions
open CFSG.Open Matrix CFSG.Blueprint.Fischer CFSG.Timmesfeld.Transvection.QTwo
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem qHyp_psu {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a) {m : ℕ} (hm : 4 ≤ m)
    (hM : fischerCentralQuotientModel D
      (fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
        A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    QHyp G D := by
  have hna' : ¬ ∀ a b : commutator G, a * b = b * a := by
    intro h
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h a b)
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff_U2 (m := m)).1 hM
  have hD : ∀ g : G, g ∈ D ↔ φ g ∈ DU m := by
    intro g
    rw [← hφ]
    exact ⟨fun h => ⟨g, h, rfl⟩, fun h => by
      obtain ⟨g', hg', hgg'⟩ := h
      exact (φ.injective hgg') ▸ hg'⟩
  refine ⟨⟨hP, hZ, hS⟩, Pair.exists_ne_commute hP hS hna', ?_, ?_⟩
  · intro e he f hf h
    exact Pair.eq_of_forall_commute_iff hP hZ hS he hf h
  · intro e he f hf hef hc
    obtain ⟨v, hv0, hv, hve⟩ := mem_DU_iff.1 ((hD e).1 he)
    obtain ⟨w, hw0, hw, hwf⟩ := mem_DU_iff.1 ((hD f).1 hf)
    have hm3 : 3 ≤ m := by omega
    have hvw_ne : tqU v ≠ tqU w := by
      intro h
      exact hef (φ.injective (by rw [← hve, ← hwf, h]))
    have hcφ : tqU v * tqU w = tqU w * tqU v := by
      rw [hve, hwf, ← map_mul, ← map_mul, hc]
    have hvw : herm frob v w = 0 :=
      (tqU_commute_iff hm3 hv0 hv hw0 hw).1 hcφ
    have hwv : herm frob w v = 0 := herm_eq_zero_comm frob frob_frob hvw
    have hvsum0 : v + w ≠ 0 := by
      intro h0
      have hwv' : w = (-1 : K) • v := by
        rw [neg_one_smul]
        exact eq_neg_of_add_eq_zero_right h0
      exact hvw_ne ((tqU_eq_tqU_iff hm3 hv0 hv hw0 hw).2 ⟨-1, hwv'⟩)
    have hvsum : herm frob (v + w) (v + w) = 0 := by
      rw [herm_add_left, herm_add_right, herm_add_right, hv, hw, hvw, hwv]
      simp
    let g : G := φ.symm (tqU (v + w))
    have hφg : φ g = tqU (v + w) := φ.apply_symm_apply _
    have hgD : g ∈ D := (hD g).2 (by rw [hφg]; exact tqU_mem_DU hvsum0 hvsum)
    have hge : g ≠ e := by
      intro hge
      have hsum : tqU (v + w) = tqU v := by rw [← hφg, hge, ← hve]
      obtain ⟨c, hc'⟩ := (tqU_eq_tqU_iff hm3 hv0 hv hvsum0 hvsum).1 hsum.symm
      have hw' : w = (c - 1) • v := by
        calc w = (v + w) - v := by rw [add_sub_cancel_left]
          _ = c • v - v := by rw [hc']
          _ = (c - 1) • v := by rw [sub_smul, one_smul]
      exact hvw_ne ((tqU_eq_tqU_iff hm3 hv0 hv hw0 hw).2 ⟨c - 1, hw'⟩)
    have hgf : g ≠ f := by
      intro hgf
      have hsum : tqU (v + w) = tqU w := by rw [← hφg, hgf, ← hwf]
      obtain ⟨c, hc'⟩ := (tqU_eq_tqU_iff hm3 hw0 hw hvsum0 hvsum).1 hsum.symm
      have hv' : v = (c - 1) • w := by
        calc v = (v + w) - w := by rw [add_sub_cancel_right]
          _ = c • w - w := by rw [hc']
          _ = (c - 1) • w := by rw [sub_smul, one_smul]
      exact hvw_ne.symm ((tqU_eq_tqU_iff hm3 hw0 hw hv0 hv).2 ⟨c - 1, hv'⟩)
    refine ⟨g, hgD, hge, hgf, ?_⟩
    intro d hd hde hdf
    obtain ⟨u, hu0, hu, hdu⟩ := mem_DU_iff.1 ((hD d).1 hd)
    have hduv : herm frob u v = 0 :=
      (tqU_commute_iff hm3 hu0 hu hv0 hv).1 (by
        rw [hdu, hve, ← map_mul, ← map_mul, hde])
    have hduw : herm frob u w = 0 :=
      (tqU_commute_iff hm3 hu0 hu hw0 hw).1 (by
        rw [hdu, hwf, ← map_mul, ← map_mul, hdf])
    have hduvw : herm frob u (v + w) = 0 := by
      rw [herm_add_right, hduv, hduw, add_zero]
    have hcomm_dg : tqU u * tqU (v + w) = tqU (v + w) * tqU u :=
      (tqU_commute_iff hm3 hu0 hu hvsum0 hvsum).2 hduvw
    exact φ.injective (by rw [map_mul, map_mul, ← hdu, hφg, hcomm_dg])

theorem transvectionHyp_of_psu {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a) {m : ℕ} (hm : 4 ≤ m)
    (hM : fischerCentralQuotientModel D
      (fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
        A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    CFSG.Timmesfeld.Transvection.TransvectionHyp G
      {A | ∃ d ∈ D, A = Subgroup.zpowers d} :=
  transvectionHyp_of_qHyp (qHyp_psu hP hZ hS hna hm hM)

end CFSG.OddTranspositions
