module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.FamilyPosition

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.PositiveNo117

open scoped Pointwise

variable {K : Type} [Field K]

theorem f4_exists_weyl_of_conj_family
    [IsAlgClosed K] {ι : Type}
    (a b : ι → Fin Tag.F4.rank → Kˣ) {g : ModGL Tag.F4 K} (hg : g ∈ adjointGroup Tag.F4 K)
    (hconj : ∀ i, g * rootDiagUnit Tag.F4 (b i) * g⁻¹ = rootDiagUnit Tag.F4 (a i)) :
    ∃ w : WeylGroup Tag.F4, ∀ i, rootDiagUnit Tag.F4 (a i) =
      canonicalRep (coxeterSystem Tag.F4) K w * rootDiagUnit Tag.F4 (b i) *
        (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ := by
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  obtain ⟨w, t, ht, u, hu, v, hv, rfl⟩ := f4_hfactor g hg
  refine ⟨w, fun i => ?_⟩
  set d := rootDiagUnit Tag.F4 (b i) with hd
  set e := rootDiagUnit Tag.F4 (a i) with he
  have hdT : d ∈ torusGroup Tag.F4 K := rootDiagUnit_mem_torusGroup _
  have heT : e ∈ torusGroup Tag.F4 K := rootDiagUnit_mem_torusGroup _
  have hnw := canonicalRep_mem_normalizer (R := K) w
  set nw := canonicalRep (coxeterSystem Tag.F4) K w with hnwdef
  have hnormT : ∀ x ∈ torusGroup Tag.F4 K, nw * x * nw⁻¹ ∈ torusGroup Tag.F4 K := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hnw x).1 hx
  set t₁ := nw * d * nw⁻¹ with ht₁
  have ht₁T : t₁ ∈ torusGroup Tag.F4 K := hnormT d hdT
  have hv₁ : d⁻¹ * v * d ∈ rootSpan Tag.F4 K (inversionSet w) := by
    have : (rootSpan Tag.F4 K (inversionSet w)).map (MulAut.conj d⁻¹).toMonoidHom =
        rootSpan Tag.F4 K (inversionSet w) := by
      refine map_rootSpan_of_forall fun α hα => ?_
      have := map_conj_rootDiagUnit_rootSubgroup (fun j => (b i j)⁻¹) hα.1
      rwa [show rootDiagUnit Tag.F4 (fun j => (b i j)⁻¹) = d⁻¹ from
        (rootDiagUnit_inv (b i)).symm] at this
    rw [← this]
    exact ⟨v, hv, by simp⟩
  have hu' : t₁⁻¹ * u * t₁ ∈ posUnipotent Tag.F4 K := by
    have hN := hTB.2.2.1 (inv_mem ht₁T)
    have := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
    simpa using this
  have h1 := hconj i
  rw [← hd, ← he, mul_inv_eq_iff_eq_mul] at h1
  have heq : (e * t) * u * nw * v = (t * t₁) * (t₁⁻¹ * u * t₁) * nw * (d⁻¹ * v * d) := by
    have h2 : e * (t * u * nw * v) = t * u * nw * v * d := h1.symm
    calc (e * t) * u * nw * v = e * (t * u * nw * v) := by group
      _ = t * u * nw * v * d := h2
      _ = (t * t₁) * (t₁⁻¹ * u * t₁) * nw * (d⁻¹ * v * d) := by
        simp only [ht₁]
        group
  have hcomm : e * t = t * e := by
    have := rootDiagUnit_mul_comm_of_mem_torusGroup (a i) ht
    exact this
  obtain ⟨h3, -, -⟩ := f4_sameW_bruhat_unique (w := w)
    (h := e * t) (h' := t * t₁) (u := u) (u' := t₁⁻¹ * u * t₁)
    (v := v) (v' := d⁻¹ * v * d)
    (mul_mem heT ht) (mul_mem ht ht₁T) hu hu' hv hv₁ heq
  have h4 : t₁ = e := by
    have : t * e = t * t₁ := by rw [← hcomm]; exact h3
    exact (mul_left_cancel this).symm
  rw [← h4]

theorem f4_familyCentralizer_factors
    {ι : Type} (a : ι → Fin Tag.F4.rank → Kˣ) :
    ∀ g ∈ familyCentralizer Tag.F4 K a, ∃ w ∈ familyStabilizer a, ∃ h ∈ torusGroup Tag.F4 K,
      ∃ u ∈ rootSpan Tag.F4 K (familyKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α}),
      ∃ v ∈ rootSpan Tag.F4 K (familyKernel a ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := by
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  have hposfin : {β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot Tag.F4).subset fun β hβ => hβ.1
  intro g hg
  obtain ⟨hgC, hgfix⟩ := mem_familyCentralizer.1 hg
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := f4_hfactor g hgC
  have key : ∀ i, w ∈ rootCharStabilizer (a i) ∧
      rootDiagUnit Tag.F4 (a i) * u * (rootDiagUnit Tag.F4 (a i))⁻¹ = u ∧
      rootDiagUnit Tag.F4 (a i) * v * (rootDiagUnit Tag.F4 (a i))⁻¹ = v := by
    intro i
    set d := rootDiagUnit Tag.F4 (a i) with hd
    obtain ⟨t, ht, hnt⟩ := exists_conj_canonicalRep (a i) w
    have hdu : d * u * d⁻¹ ∈ posUnipotent Tag.F4 K := by
      have : (posUnipotent Tag.F4 K).map (MulAut.conj d).toMonoidHom = posUnipotent Tag.F4 K := by
        rw [posUnipotent]
        exact map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup (a i) hα.1
      rw [← this]
      exact ⟨u, hu, rfl⟩
    have hdv : d * v * d⁻¹ ∈ rootSpan Tag.F4 K (inversionSet w) := by
      have : (rootSpan Tag.F4 K (inversionSet w)).map (MulAut.conj d).toMonoidHom =
          rootSpan Tag.F4 K (inversionSet w) :=
        map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup (a i) hα.1
      rw [← this]
      exact ⟨v, hv, rfl⟩
    have hu' : t⁻¹ * (d * u * d⁻¹) * t ∈ posUnipotent Tag.F4 K := by
      have hN := hTB.2.2.1 (inv_mem ht)
      have := (Subgroup.mem_normalizer_iff.1 hN (d * u * d⁻¹)).1 hdu
      simpa using this
    have heq : h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem Tag.F4) K w *
        (d * v * d⁻¹) = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := by
      calc h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem Tag.F4) K w *
            (d * v * d⁻¹) =
          (d * h * d⁻¹) * (d * u * d⁻¹) * (t * canonicalRep (coxeterSystem Tag.F4) K w) *
            (d * v * d⁻¹) := by
            rw [conj_rootDiagUnit_of_mem_torusGroup (a i) hh]
            group
        _ = (d * h * d⁻¹) * (d * u * d⁻¹) * (d * canonicalRep (coxeterSystem Tag.F4) K w * d⁻¹) *
            (d * v * d⁻¹) := by rw [hnt]
        _ = d * (h * u * canonicalRep (coxeterSystem Tag.F4) K w * v) * d⁻¹ := by group
        _ = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := hgfix i
    obtain ⟨h1, h2, h3⟩ := f4_sameW_bruhat_unique (w := w)
      (h := h * t) (h' := h) (u := t⁻¹ * (d * u * d⁻¹) * t) (u' := u)
      (v := d * v * d⁻¹) (v' := v)
      (mul_mem hh ht) hh hu' hu hdv hv heq
    have ht1 : t = 1 := by
      have := h1
      rwa [mul_eq_left] at this
    subst ht1
    have hufix : d * u * d⁻¹ = u := by simpa using h2
    have hw : w ∈ rootCharStabilizer (a i) := by
      rw [← conj_canonicalRep_eq_iff, ← hd, hnt, one_mul]
    exact ⟨hw, hufix, h3⟩
  refine ⟨w, fun i => (key i).1, h, hh, u, ?_, v, ?_, rfl⟩
  · exact mem_rootSpan_inter_of_conj_eq_family a hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (f4_positive_root_collection K).2 α hα hr) hu fun i => (key i).2.1
  · exact mem_rootSpan_inter_of_conj_eq_family a (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => f4_bijOn_prod_pinnedX K (S := inversionSet w)
        (fun β hβ => inversionSet_pos hβ)
        (fun α hα β hβ a b ha hb hr => inversionSet_closed w α hα β hβ a b ha hb hr)
        α hα hr) hv fun i => (key i).2.2

theorem f4_familyCentralizer_le_mul
    {ι : Type} (a : ι → Fin Tag.F4.rank → Kˣ)
    {g : ModGL Tag.F4 K} (hg : g ∈ familyCentralizer Tag.F4 K a) :
    ∃ w ∈ familyStabilizer a, ∃ m ∈ familyGroup (K := K) a,
      g = m * canonicalRep (coxeterSystem Tag.F4) K w := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := f4_familyCentralizer_factors a g hg
  have hnorm := canonicalRep_mem_normalizer_familyGroup (K := K) hw
  have huM : u ∈ familyGroup (K := K) a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)
  have hvM : v ∈ familyGroup (K := K) a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  have hn' : canonicalRep (coxeterSystem Tag.F4) K w * v *
      (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ ∈ familyGroup (K := K) a :=
    (Subgroup.mem_normalizer_iff.1 hnorm v).1 hvM
  refine ⟨w, hw, h * u * (canonicalRep (coxeterSystem Tag.F4) K w * v *
    (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹),
    mul_mem (mul_mem (Subgroup.mem_sup_left hh) huM) hn', ?_⟩
  group

end CFSG.StandardType.F4ExplicitPos.FamilyPosition

end

end
