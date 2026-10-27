module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FamilyPosition
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatUnique

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.FiniteCounts

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.BruhatUnique
  CFSG.StandardType.F4ExplicitPos.FamilyPosition CFSG.StandardType.F4ExplicitPos.PositiveNo117

open scoped Pointwise

variable {K : Type} [Field K] {ι : Type}

theorem f4_card_adjointGroup
    [Finite K] :
    Nat.card (adjointGroup Tag.F4 K) = Nat.card (torusGroup Tag.F4 K) *
      Nat.card K ^ {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard *
        ∑ᶠ w : WeylGroup Tag.F4, Nat.card K ^ (coxeterSystem Tag.F4).length w :=
  CFSG.StandardType.F4ExplicitPos.BruhatUnique.f4_card_adjointGroup

theorem f4_card_familyCentralizer_inf_monomial
    [Finite K]
    (a : ι → Fin Tag.F4.rank → Kˣ) :
    Nat.card (familyCentralizer Tag.F4 K a ⊓ monomialSubgroup Tag.F4 K :
        Subgroup (ModGL Tag.F4 K)) =
      Nat.card (torusGroup Tag.F4 K) * Nat.card (familyStabilizerSubgroup a) := by
  classical
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  have hBC : borelGroup Tag.F4 K ≤ adjointGroup Tag.F4 K := (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  have hTC : torusGroup Tag.F4 K ≤ adjointGroup Tag.F4 K := le_sup_left.trans hBC
  have hTN : torusGroup Tag.F4 K ≤ monomialSubgroup Tag.F4 K := le_sup_left
  have hmem : ∀ t ∈ torusGroup Tag.F4 K, ∀ w ∈ familyStabilizer a,
      t * canonicalRep (coxeterSystem Tag.F4) K w ∈
        (familyCentralizer Tag.F4 K a ⊓ monomialSubgroup Tag.F4 K :
          Subgroup (ModGL Tag.F4 K)) := by
    intro t ht w hw
    refine Subgroup.mem_inf.2 ⟨mem_familyCentralizer.2 ⟨mul_mem (hTC ht)
      (canonicalRep_mem_adjointGroup _ K w), fun i => ?_⟩,
      mul_mem (hTN ht) (canonicalRep_mem_monomialSubgroup' w)⟩
    have hdt := conj_rootDiagUnit_of_mem_torusGroup (a i) ht
    have hdn := (conj_canonicalRep_eq_iff (a i) w).2 (hw i)
    calc rootDiagUnit Tag.F4 (a i) * (t * canonicalRep (coxeterSystem Tag.F4) K w) *
          (rootDiagUnit Tag.F4 (a i))⁻¹ =
        (rootDiagUnit Tag.F4 (a i) * t * (rootDiagUnit Tag.F4 (a i))⁻¹) *
          (rootDiagUnit Tag.F4 (a i) * canonicalRep (coxeterSystem Tag.F4) K w *
            (rootDiagUnit Tag.F4 (a i))⁻¹) := by group
      _ = t * canonicalRep (coxeterSystem Tag.F4) K w := by rw [hdt, hdn]
  have e : (torusGroup Tag.F4 K × familyStabilizerSubgroup a) ≃
      (familyCentralizer Tag.F4 K a ⊓ monomialSubgroup Tag.F4 K :
        Subgroup (ModGL Tag.F4 K)) :=
    Equiv.ofBijective
      (fun p => ⟨(p.1 : ModGL Tag.F4 K) *
          canonicalRep (coxeterSystem Tag.F4) K (p.2 : WeylGroup Tag.F4),
        hmem _ p.1.2 _ (mem_familyStabilizerSubgroup.1 p.2.2)⟩)
      ⟨fun p p' h => by
        have h' : (p.1 : ModGL Tag.F4 K) *
              canonicalRep (coxeterSystem Tag.F4) K (p.2 : WeylGroup Tag.F4) =
            (p'.1 : ModGL Tag.F4 K) *
              canonicalRep (coxeterSystem Tag.F4) K (p'.2 : WeylGroup Tag.F4) :=
          congrArg Subtype.val h
        obtain ⟨hww, hh, -, -⟩ := f4_bruhat_factor_unique
          (u := 1) (u' := 1) (v := 1) (v' := 1)
          (hh := p.1.2) (hh' := p'.1.2) (hu := one_mem _) (hu' := one_mem _)
          (hv := one_mem (rootSpan Tag.F4 K (inversionSet (p.2 : WeylGroup Tag.F4))))
          (hv' := one_mem (rootSpan Tag.F4 K (inversionSet (p'.2 : WeylGroup Tag.F4))))
          (by simpa using h')
        exact Prod.ext (Subtype.ext hh) (Subtype.ext hww),
       fun g => by
        obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 g.2
        obtain ⟨hgC', hgfix'⟩ := mem_familyCentralizer.1 hgC
        obtain ⟨w, t, ht, hgt⟩ := exists_torus_mul_canonicalRep_of_mem_monomial hgN
        have hw : w ∈ familyStabilizer a := by
          intro i
          have h1 := hgfix' i
          rw [hgt] at h1
          have hdt := conj_rootDiagUnit_of_mem_torusGroup (a i) ht
          have h2 : rootDiagUnit Tag.F4 (a i) * canonicalRep (coxeterSystem Tag.F4) K w *
              (rootDiagUnit Tag.F4 (a i))⁻¹ =
                canonicalRep (coxeterSystem Tag.F4) K w := by
            have h3 : t * (rootDiagUnit Tag.F4 (a i) *
                canonicalRep (coxeterSystem Tag.F4) K w *
                (rootDiagUnit Tag.F4 (a i))⁻¹) =
                  t * canonicalRep (coxeterSystem Tag.F4) K w := by
              calc t * (rootDiagUnit Tag.F4 (a i) * canonicalRep (coxeterSystem Tag.F4) K w *
                    (rootDiagUnit Tag.F4 (a i))⁻¹) =
                  (rootDiagUnit Tag.F4 (a i) * t * (rootDiagUnit Tag.F4 (a i))⁻¹) *
                    (rootDiagUnit Tag.F4 (a i) * canonicalRep (coxeterSystem Tag.F4) K w *
                      (rootDiagUnit Tag.F4 (a i))⁻¹) := by rw [hdt]
                _ = rootDiagUnit Tag.F4 (a i) *
                    (t * canonicalRep (coxeterSystem Tag.F4) K w) *
                    (rootDiagUnit Tag.F4 (a i))⁻¹ := by group
                _ = t * canonicalRep (coxeterSystem Tag.F4) K w := h1
            exact mul_left_cancel h3
          exact (conj_canonicalRep_eq_iff (a i) w).1 h2
        exact ⟨(⟨t, ht⟩, ⟨w, mem_familyStabilizerSubgroup.2 hw⟩), Subtype.ext hgt.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod]

theorem f4_card_familyCentralizer
    [Finite K] (a : ι → Fin Tag.F4.rank → Kˣ) :
    Nat.card (familyCentralizer Tag.F4 K a) = Nat.card (torusGroup Tag.F4 K) *
      (Nat.card K ^
        (familyKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α}).ncard) *
      ∑ᶠ w : familyStabilizerSubgroup a,
        Nat.card K ^ (familyKernel a ∩ inversionSet (w : WeylGroup Tag.F4)).ncard := by
  classical
  have : Fintype (familyStabilizerSubgroup a) := Fintype.ofFinite _
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  have hBC : borelGroup Tag.F4 K ≤ adjointGroup Tag.F4 K := (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  have hTC : torusGroup Tag.F4 K ≤ adjointGroup Tag.F4 K := le_sup_left.trans hBC
  have hposfin : {β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot Tag.F4).subset fun β hβ => hβ.1
  have hcoll1 := fun {m : ℕ} (α : Fin m → Fin Tag.F4.rank → ℤ)
    (hα : Function.Injective α)
    (hr : Set.range α = {β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β}) =>
    (f4_positive_root_collection K).2 α hα hr
  have hcard1 := card_rootSpan_familyKernel_inter (τ := Tag.F4) a hposfin
    (fun β hβ => hβ.1) hcoll1
  have hcard2 : ∀ w : WeylGroup Tag.F4,
      Nat.card (rootSpan Tag.F4 K (familyKernel a ∩ inversionSet w)) =
        Nat.card K ^ (familyKernel a ∩ inversionSet w).ncard := fun w =>
    card_rootSpan_familyKernel_inter (τ := Tag.F4) a (inversionSet_finite w)
      (fun β hβ => hβ.1)
      (fun {m} α hα hr => f4_bijOn_prod_pinnedX K
        (fun β hβ => inversionSet_pos hβ)
        (fun α hα β hβ a b ha hb hr =>
          inversionSet_closed w α hα β hβ a b ha hb hr)
        α hα hr)
  have hfix : ∀ i, ∀ x ∈ torusGroup Tag.F4 K,
      rootDiagUnit Tag.F4 (a i) * x * (rootDiagUnit Tag.F4 (a i))⁻¹ = x :=
    fun i x hx => conj_rootDiagUnit_of_mem_torusGroup (a i) hx
  have hmem : ∀ w ∈ familyStabilizer a, ∀ h ∈ torusGroup Tag.F4 K,
      ∀ u ∈ rootSpan Tag.F4 K (familyKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α}),
      ∀ v ∈ rootSpan Tag.F4 K (familyKernel a ∩ inversionSet w),
        h * u * canonicalRep (coxeterSystem Tag.F4) K w * v ∈
          familyCentralizer Tag.F4 K a := by
    intro w hw h hh u hu v hv
    refine mem_familyCentralizer.2 ⟨mul_mem (mul_mem (mul_mem (hTC hh)
      (rootSpan_le_adjointGroup K _ hu)) (canonicalRep_mem_adjointGroup _ K w))
      (rootSpan_le_adjointGroup K _ hv), fun i => ?_⟩
    have hdu : rootDiagUnit Tag.F4 (a i) * u * (rootDiagUnit Tag.F4 (a i))⁻¹ = u :=
      conj_eq_iff_mem_centralizer.2 ((rootSpan_le_centralizer (a i)
        (S := familyKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α})
        (fun β hβ => ⟨hβ.1.1, hβ.1.2 i⟩)) hu)
    have hdv : rootDiagUnit Tag.F4 (a i) * v * (rootDiagUnit Tag.F4 (a i))⁻¹ = v :=
      conj_eq_iff_mem_centralizer.2 ((rootSpan_le_centralizer (a i)
        (S := familyKernel a ∩ inversionSet w)
        (fun β hβ => ⟨hβ.1.1, hβ.1.2 i⟩)) hv)
    have hdn := (conj_canonicalRep_eq_iff (a i) w).2 (hw i)
    calc rootDiagUnit Tag.F4 (a i) *
          (h * u * canonicalRep (coxeterSystem Tag.F4) K w * v) *
          (rootDiagUnit Tag.F4 (a i))⁻¹ =
        (rootDiagUnit Tag.F4 (a i) * h * (rootDiagUnit Tag.F4 (a i))⁻¹) *
          (rootDiagUnit Tag.F4 (a i) * u * (rootDiagUnit Tag.F4 (a i))⁻¹) *
          (rootDiagUnit Tag.F4 (a i) * canonicalRep (coxeterSystem Tag.F4) K w *
            (rootDiagUnit Tag.F4 (a i))⁻¹) *
          (rootDiagUnit Tag.F4 (a i) * v * (rootDiagUnit Tag.F4 (a i))⁻¹) := by group
      _ = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := by
        rw [hfix i h hh, hdu, hdn, hdv]
  have e : (Σ w : familyStabilizerSubgroup a, torusGroup Tag.F4 K ×
      (rootSpan Tag.F4 K
        (familyKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α})) ×
      (rootSpan Tag.F4 K (familyKernel a ∩ inversionSet (w : WeylGroup Tag.F4)))) ≃
      familyCentralizer Tag.F4 K a :=
    Equiv.ofBijective
      (fun p => ⟨(p.2.1 : ModGL Tag.F4 K) * (p.2.2.1 : ModGL Tag.F4 K) *
          canonicalRep (coxeterSystem Tag.F4) K (p.1 : WeylGroup Tag.F4) *
            (p.2.2.2 : ModGL Tag.F4 K),
        hmem _ (mem_familyStabilizerSubgroup.1 p.1.2) _ p.2.1.2 _ p.2.2.1.2 _
          p.2.2.2.2⟩)
      ⟨by
        rintro ⟨⟨w, hw⟩, h, u, v⟩ ⟨⟨w', hw'⟩, h', u', v'⟩ heq
        have hEq : (h : ModGL Tag.F4 K) * u *
              canonicalRep (coxeterSystem Tag.F4) K w * v =
            (h' : ModGL Tag.F4 K) * u' *
              canonicalRep (coxeterSystem Tag.F4) K w' * v' :=
          congrArg Subtype.val heq
        obtain ⟨hww, hh, hu, hv⟩ := f4_bruhat_factor_unique h.2 h'.2
          (rootSpan_mono Set.inter_subset_right u.2)
          (rootSpan_mono Set.inter_subset_right u'.2)
          (rootSpan_mono Set.inter_subset_right v.2)
          (rootSpan_mono Set.inter_subset_right v'.2) hEq
        subst hww
        have e1 : h = h' := Subtype.ext hh
        have e2 : u = u' := Subtype.ext hu
        have e3 : v = v' := Subtype.ext hv
        subst e1 e2 e3
        rfl,
       fun g => by
        obtain ⟨w, hw, h, hh, u, hu, v, hv, hg⟩ := f4_familyCentralizer_factors a g g.2
        exact ⟨⟨⟨w, mem_familyStabilizerSubgroup.2 hw⟩, ⟨h, hh⟩, ⟨u, hu⟩, ⟨v, hv⟩⟩,
          Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp only [Nat.card_prod, hcard1, hcard2]
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => by ring

theorem f4_not_dvd_relIndex_monomial
    [Finite K] {r : ℕ} [hr : Fact r.Prime]
    (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup Tag.F4)) :
    ¬ r ∣ (monomialSubgroup Tag.F4 K).relIndex (adjointGroup Tag.F4 K) := by
  classical
  have := finite_modGL (τ := Tag.F4) (K := K)
  have : Fintype (WeylGroup Tag.F4) := Fintype.ofFinite _
  set q := Nat.card K with hqdef
  set W := Nat.card (WeylGroup Tag.F4) with hWdef
  set P := ∑ᶠ w : WeylGroup Tag.F4, q ^ (coxeterSystem Tag.F4).length w with hP
  set I := (monomialSubgroup Tag.F4 K).relIndex (adjointGroup Tag.F4 K) with hI
  have hNC : monomialSubgroup Tag.F4 K ≤ adjointGroup Tag.F4 K :=
    monomialSubgroup_le_adjointGroup'
  have hH : 0 < Nat.card (torusGroup Tag.F4 K) := Nat.card_pos
  have hIdef : I = ((monomialSubgroup Tag.F4 K).subgroupOf
      (adjointGroup Tag.F4 K)).index := rfl
  have hrel : W * I = q ^
      {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard * P := by
    have h1 := Subgroup.card_mul_index
      ((monomialSubgroup Tag.F4 K).subgroupOf (adjointGroup Tag.F4 K))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv,
      card_monomialSubgroup, f4_card_adjointGroup, ← hIdef] at h1
    apply Nat.eq_of_mul_eq_mul_left hH
    rw [← mul_assoc, h1, mul_assoc]
  have hPW : P ≡ W [MOD r ^ M] := by
    rw [← ZMod.natCast_eq_natCast_iff, hP, finsum_eq_sum_of_fintype, Nat.cast_sum]
    have hq1 : (q : ZMod (r ^ M)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hqM
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hWdef, Nat.card_eq_fintype_card]
  have hW0 : W ≠ 0 := Nat.card_pos.ne'
  set e := W.factorization r with he
  have he1 : ¬ r ^ (e + 1) ∣ W := Nat.pow_succ_factorization_not_dvd hW0 hr.out
  have heM : e + 1 ≤ M := by
    by_contra h
    exact hW ((Nat.pow_dvd_pow r (by omega)).trans (Nat.ordProj_dvd W r))
  intro hrI
  obtain ⟨m, hm⟩ := hrI
  have hdvd : r ^ (e + 1) ∣ q ^
      {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard * P := by
    rw [← hrel, hm, pow_succ]
    exact mul_dvd_mul (Nat.ordProj_dvd W r) (Dvd.intro m rfl)
  have hcop : Nat.Coprime (r ^ (e + 1))
      (q ^ {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hqr)
  have hPr : r ^ (e + 1) ∣ P := hcop.dvd_of_dvd_mul_left hdvd
  exact he1 ((hPW.dvd_iff (Nat.pow_dvd_pow r heM)).1 hPr)

theorem f4_not_dvd_relIndex_familyCentralizer
    [Finite K]
    (a : ι → Fin Tag.F4.rank → Kˣ) {r : ℕ} [hr : Fact r.Prime]
    (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup Tag.F4)) :
    ¬ r ∣ (familyCentralizer Tag.F4 K a ⊓ monomialSubgroup Tag.F4 K).relIndex
      (familyCentralizer Tag.F4 K a) := by
  classical
  have : Fintype (familyStabilizerSubgroup a) := Fintype.ofFinite _
  set q := Nat.card K with hqdef
  set C := familyCentralizer Tag.F4 K a with hC
  set NC := C ⊓ monomialSubgroup Tag.F4 K with hNC
  set Ws := Nat.card (familyStabilizerSubgroup a) with hWs
  set P := ∑ᶠ w : familyStabilizerSubgroup a,
    q ^ (familyKernel a ∩ inversionSet (w : WeylGroup Tag.F4)).ncard with hP
  set n₁ := (familyKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α}).ncard with hn₁
  set I := NC.relIndex C with hI
  have hle : NC ≤ C := inf_le_left
  have hH : 0 < Nat.card (torusGroup Tag.F4 K) := Nat.card_pos
  have hrel : Ws * I = q ^ n₁ * P := by
    have h1 := Subgroup.card_mul_index (NC.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      f4_card_familyCentralizer_inf_monomial, f4_card_familyCentralizer] at h1
    apply Nat.eq_of_mul_eq_mul_left hH
    have : Nat.card (torusGroup Tag.F4 K) * Ws * I =
        Nat.card (torusGroup Tag.F4 K) * q ^ n₁ * P := by
      rw [← h1]
      rfl
    calc Nat.card (torusGroup Tag.F4 K) * (Ws * I) =
          Nat.card (torusGroup Tag.F4 K) * Ws * I := by ring
      _ = Nat.card (torusGroup Tag.F4 K) * q ^ n₁ * P := this
      _ = Nat.card (torusGroup Tag.F4 K) * (q ^ n₁ * P) := by ring
  have hPW : P ≡ Ws [MOD r ^ M] := by
    rw [← ZMod.natCast_eq_natCast_iff, hP, finsum_eq_sum_of_fintype, Nat.cast_sum]
    have hq1 : (q : ZMod (r ^ M)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hqM
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hWs, Nat.card_eq_fintype_card]
  have hW0 : Ws ≠ 0 := Nat.card_pos.ne'
  set e := Ws.factorization r with he
  have he1 : ¬ r ^ (e + 1) ∣ Ws := Nat.pow_succ_factorization_not_dvd hW0 hr.out
  have hWsW : ¬ r ^ M ∣ Ws := fun h =>
    hW (h.trans (Subgroup.card_subgroup_dvd_card (familyStabilizerSubgroup a)))
  have heM : e + 1 ≤ M := by
    by_contra h
    exact hWsW ((Nat.pow_dvd_pow r (by omega)).trans (Nat.ordProj_dvd Ws r))
  intro hrI
  obtain ⟨m, hm⟩ := hrI
  have hdvd : r ^ (e + 1) ∣ q ^ n₁ * P := by
    rw [← hrel, hm, pow_succ]
    exact mul_dvd_mul (Nat.ordProj_dvd Ws r) (Dvd.intro m rfl)
  have hcop : Nat.Coprime (r ^ (e + 1)) (q ^ n₁) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hqr)
  have hPr : r ^ (e + 1) ∣ P := hcop.dvd_of_dvd_mul_left hdvd
  exact he1 ((hPW.dvd_iff (Nat.pow_dvd_pow r heM)).1 hPr)

end CFSG.StandardType.F4ExplicitPos.FiniteCounts
end

end
