module

public import CFSG.Monster.Griess.TrialityMatrix
public import CFSG.Monster.Griess.TrilinearData
public import CFSG.Monster.Octad.ThreeOctad

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.OctadInv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem zmod2_aux_add : ∀ a b : ZMod 2, b = a + (a + b) := by decide

noncomputable abbrev octVec (o : OctIdx) : SpaceB := tbasis (.inr (.inr (.inr o)))

@[expose] noncomputable def octSpan : Submodule ℚ SpaceB := Submodule.span ℚ (Set.range octVec)

noncomputable abbrev pairVec (p : LtPair) (k : Fin 3) : SpaceB := tbasis (.inr (.inl (p, k)))

@[expose] noncomputable def pairSpan : Submodule ℚ SpaceB :=
  Submodule.span ℚ (Set.range fun q : LtPair × Fin 3 => pairVec q.1 q.2)

noncomputable abbrev sectVec (a : C₀) (i : Fin 24) (k : Fin 3) : SpaceB :=
  tbasis (.inr (.inr (.inl (a, i, k))))

@[expose] noncomputable def sectSpan (k : Fin 3) : Submodule ℚ SpaceB :=
  Submodule.span ℚ (Set.range fun q : C₀ × Fin 24 => sectVec q.1 q.2 k)

theorem octVec_mem_octSpan (o : OctIdx) : octVec o ∈ octSpan := Submodule.subset_span ⟨o, rfl⟩

theorem pairVec_mem_pairSpan (p : LtPair) (k : Fin 3) : pairVec p k ∈ pairSpan :=
  Submodule.subset_span ⟨(p, k), rfl⟩

theorem sectVec_mem_sectSpan (a : C₀) (i : Fin 24) (k : Fin 3) : sectVec a i k ∈ sectSpan k :=
  Submodule.subset_span ⟨(a, i), rfl⟩

theorem trilin_eq_of_span (F G : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ)
    {s₁ s₂ s₃ : Set SpaceB} (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ∀ z ∈ s₃, F x y z = G x y z)
    {u v w : SpaceB} (hu : u ∈ Submodule.span ℚ s₁) (hv : v ∈ Submodule.span ℚ s₂)
    (hw : w ∈ Submodule.span ℚ s₃) : F u v w = G u v w := by
  have key : (F - G) u v w = 0 := by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      induction hv using Submodule.span_induction with
      | mem y hy =>
        induction hw using Submodule.span_induction with
        | mem z hz =>
          rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, h x hx y hy z hz,
            sub_self]
        | zero => exact map_zero _
        | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
        | smul c a _ ha => rw [map_smul, ha, smul_zero]
      | zero => rw [map_zero, LinearMap.zero_apply]
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
    | zero => rw [map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, ha, smul_zero]
  rwa [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at key

@[expose] noncomputable def Tcomp (g : SpaceB →ₗ[ℚ] SpaceB) :
    SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ :=
  (T.compl₁₂ g g).compr₂ (LinearMap.lcomp ℚ ℚ g)

theorem Tcomp_apply (g : SpaceB →ₗ[ℚ] SpaceB) (u v w : SpaceB) :
    Tcomp g u v w = T (g u) (g v) (g w) := rfl

theorem T_comp_eq_of_span (g : SpaceB →ₗ[ℚ] SpaceB) {s₁ s₂ s₃ : Set SpaceB}
    (h : ∀ x ∈ s₁, ∀ y ∈ s₂, ∀ z ∈ s₃, T (g x) (g y) (g z) = T x y z) {u v w : SpaceB}
    (hu : u ∈ Submodule.span ℚ s₁) (hv : v ∈ Submodule.span ℚ s₂)
    (hw : w ∈ Submodule.span ℚ s₃) : T (g u) (g v) (g w) = T u v w := by
  have key := trilin_eq_of_span (Tcomp g) T
    (fun x hx y hy z hz => (Tcomp_apply g x y z).trans (h x hx y hy z hz)) hu hv hw
  rwa [Tcomp_apply] at key

theorem map_mem_span (g : SpaceB →ₗ[ℚ] SpaceB) {s s' : Set SpaceB}
    (h : ∀ x ∈ s, g x ∈ Submodule.span ℚ s') {u : SpaceB} (hu : u ∈ Submodule.span ℚ s) :
    g u ∈ Submodule.span ℚ s' :=
  (Submodule.span_le.2 h : Submodule.span ℚ s ≤ (Submodule.span ℚ s').comap g) hu

theorem T_tauB_symm_of_tauB {S₁ S₂ S₃ : Submodule ℚ SpaceB} (h₁ : ∀ u ∈ S₁, tauB.symm u ∈ S₁)
    (h₂ : ∀ u ∈ S₂, tauB.symm u ∈ S₂) (h₃ : ∀ u ∈ S₃, tauB.symm u ∈ S₃)
    (hT : ∀ u ∈ S₁, ∀ v ∈ S₂, ∀ w ∈ S₃, T (tauB u) (tauB v) (tauB w) = T u v w)
    {u v w : SpaceB} (hu : u ∈ S₁) (hv : v ∈ S₂) (hw : w ∈ S₃) :
    T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  have h := hT _ (h₁ u hu) _ (h₂ v hv) _ (h₃ w hw)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem T_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℚ) (x : ι → SpaceB)
    (g : κ → ℚ) (y : κ → SpaceB) (z : SpaceB) :
    T (∑ i, f i • x i) (∑ j, g j • y j) z = ∑ i, ∑ j, f i * g j * T (x i) (y j) z := by
  rw [map_sum T, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul T, LinearMap.smul_apply, LinearMap.smul_apply, map_sum (T (x i)),
    LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul (T (x i)), LinearMap.smul_apply, smul_eq_mul]
  ring

theorem T_sum_sum_sum {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] (f : ι → ℚ)
    (x : ι → SpaceB) (g : κ → ℚ) (y : κ → SpaceB) (h : μ → ℚ) (z : μ → SpaceB) :
    T (∑ i, f i • x i) (∑ j, g j • y j) (∑ k, h k • z k) =
      ∑ i, ∑ j, ∑ k, f i * g j * h k * T (x i) (y j) (z k) := by
  rw [map_sum T, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul T, LinearMap.smul_apply, LinearMap.smul_apply, map_sum (T (x i)),
    LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul (T (x i)), LinearMap.smul_apply, map_sum (T (x i) (y j)), smul_eq_mul,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul (T (x i) (y j)), smul_eq_mul]
  ring

theorem tauB_tauB_tauB (x : SpaceB) : tauB (tauB (tauB x)) = x := by
  have h := congrArg (fun e : SpaceB ≃ₗ[ℚ] SpaceB => e x) tauB_pow_three
  simp only [LinearEquiv.coe_pow] at h
  exact h

theorem tauB_tauB (x : SpaceB) : tauB (tauB x) = tauB.symm x := by
  rw [← tauB_tauB_tauB (tauB.symm x), LinearEquiv.apply_symm_apply]

theorem tauB_symm_tbasis (x : TIdx) : tauB.symm (tbasis x) = ∑ y, tauMat y x • tbasis y := by
  rw [tauB_symm_apply, Matrix.toLin_self]

theorem tauMat_apply_oct_of_notMem (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) (y : TIdx)
    (hy : y ∉ Set.range fun w : Octad.EvenQuot (octSupp d) => (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) :
    tauMat y (.inr (.inr (.inr ⟨d, v⟩))) = 0 := by
  rcases y with j | q | q | ⟨d', w⟩
  · rfl
  · rfl
  · rfl
  · have hd : d' ≠ d := by
      rintro rfl
      exact hy ⟨w, rfl⟩
    simp only [tauMat, diag2_apply_inr_inr, octBlock]
    exact blockDiagonal'_apply_ne _ _ _ hd

theorem tauB_octVec (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tauB (octVec ⟨d, v⟩) = ∑ w, octHD d v w • octVec ⟨d, w⟩ := tauB_oct d v

theorem tauB_symm_octVec (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tauB.symm (octVec ⟨d, v⟩) = ∑ w, octHD d w v • octVec ⟨d, w⟩ := by
  rw [tauB_symm_tbasis]
  refine (Fintype.sum_of_injective (fun w : Octad.EvenQuot (octSupp d) =>
    (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) ?_ _ _ ?_ ?_).symm
  · intro w w' h
    simpa using h
  · intro y hy
    rw [tauMat_apply_oct_of_notMem d v y hy, zero_smul]
  · intro w
    rw [tauMat_oct_apply_oct]

theorem tauB_pairVec (p : LtPair) (k : Fin 3) : tauB (pairVec p k) = pairVec p (k + 1) :=
  tauB_pair p k

theorem tauB_symm_pairVec (p : LtPair) (k : Fin 3) :
    tauB.symm (pairVec p (k + 1)) = pairVec p k := by
  rw [← tauB_pairVec, LinearEquiv.symm_apply_apply]

theorem tauB_sectVec (a : C₀) (i : Fin 24) (k : Fin 3) :
    tauB (sectVec a i k) = sectVec a i (k + 1) :=
  tauB_odd a i k

theorem tauB_symm_sectVec (a : C₀) (i : Fin 24) (k : Fin 3) :
    tauB.symm (sectVec a i (k + 1)) = sectVec a i k := by
  rw [← tauB_sectVec, LinearEquiv.symm_apply_apply]

theorem tauB_mem_octSpan {u : SpaceB} (hu : u ∈ octSpan) : tauB u ∈ octSpan := by
  refine map_mem_span (tauB : SpaceB →ₗ[ℚ] SpaceB) ?_ hu
  rintro _ ⟨⟨d, v⟩, rfl⟩
  change tauB (octVec ⟨d, v⟩) ∈ octSpan
  rw [tauB_octVec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (octVec_mem_octSpan _)

theorem tauB_symm_mem_octSpan {u : SpaceB} (hu : u ∈ octSpan) : tauB.symm u ∈ octSpan := by
  refine map_mem_span (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) ?_ hu
  rintro _ ⟨⟨d, v⟩, rfl⟩
  change tauB.symm (octVec ⟨d, v⟩) ∈ octSpan
  rw [tauB_symm_octVec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (octVec_mem_octSpan _)

theorem tauB_mem_pairSpan {u : SpaceB} (hu : u ∈ pairSpan) : tauB u ∈ pairSpan := by
  refine map_mem_span (tauB : SpaceB →ₗ[ℚ] SpaceB) ?_ hu
  rintro _ ⟨⟨p, k⟩, rfl⟩
  change tauB (pairVec p k) ∈ pairSpan
  rw [tauB_pairVec]
  exact pairVec_mem_pairSpan _ _

theorem tauB_symm_mem_pairSpan {u : SpaceB} (hu : u ∈ pairSpan) : tauB.symm u ∈ pairSpan := by
  refine map_mem_span (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) ?_ hu
  rintro _ ⟨⟨p, k⟩, rfl⟩
  change tauB.symm (pairVec p k) ∈ pairSpan
  have : pairVec p k = pairVec p (k - 1 + 1) := by rw [sub_add_cancel]
  rw [this, tauB_symm_pairVec]
  exact pairVec_mem_pairSpan _ _

theorem tauB_mem_sectSpan {k : Fin 3} {u : SpaceB} (hu : u ∈ sectSpan k) :
    tauB u ∈ sectSpan (k + 1) := by
  refine map_mem_span (tauB : SpaceB →ₗ[ℚ] SpaceB) ?_ hu
  rintro _ ⟨⟨a, i⟩, rfl⟩
  change tauB (sectVec a i k) ∈ sectSpan (k + 1)
  rw [tauB_sectVec]
  exact sectVec_mem_sectSpan _ _ _

theorem tauB_symm_mem_sectSpan {k : Fin 3} {u : SpaceB} (hu : u ∈ sectSpan (k + 1)) :
    tauB.symm u ∈ sectSpan k := by
  refine map_mem_span (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) ?_ hu
  rintro _ ⟨⟨a, i⟩, rfl⟩
  change tauB.symm (sectVec a i (k + 1)) ∈ sectSpan k
  rw [tauB_symm_sectVec]
  exact sectVec_mem_sectSpan _ _ _

noncomputable abbrev octLab (o : OctIdx) : ShortIdx := labelIdx (.inr (.inr (.inr o)))

noncomputable abbrev minusLab (p : LtPair) : ShortIdx := labelIdx (.inl p)

noncomputable abbrev plusLab (p : LtPair) : ShortIdx := labelIdx (.inr (.inl p))

noncomputable abbrev oddLab (a : C₀) (i : Fin 24) : ShortIdx := labelIdx (.inr (.inr (.inl (a, i))))

theorem octVec_eq (o : OctIdx) : octVec o = inX (Pi.single (octLab o) 1) :=
  (tbasis_oct o).trans (congrArg inX (Xlift_labelElt (.inr (.inr (.inr o)))))

theorem pairVec_zero (p : LtPair) : pairVec p 0 = inA (basisA s(p.1.1, p.1.2)) :=
  tbasis_pair_zero p

theorem pairVec_one (p : LtPair) :
    pairVec p 1 = inX (Pi.single (minusLab p) 1 - Pi.single (plusLab p) 1) :=
  (tbasis_pair_one p).trans (congrArg inX (congrArg₂ (· - ·) (Xlift_labelElt (.inl p))
    (Xlift_labelElt (.inr (.inl p)))))

theorem pairVec_two (p : LtPair) :
    pairVec p 2 = inX (Pi.single (minusLab p) 1 + Pi.single (plusLab p) 1) :=
  (tbasis_pair_two p).trans (congrArg inX (congrArg₂ (· + ·) (Xlift_labelElt (.inl p))
    (Xlift_labelElt (.inr (.inl p)))))

theorem sectVec_zero (a : C₀) (i : Fin 24) : sectVec a i 0 = inX (Pi.single (oddLab a i) 1) :=
  (tbasis_odd_zero a i).trans (congrArg inX (Xlift_labelElt (.inr (.inr (.inl (a, i))))))

theorem thetaD_add_smul_ΩC (a : C) (n : ZMod 2) : thetaD (a + n • ΩC) = thetaD a := by
  rcases zmod2_cases n with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul, thetaD_add, thetaD_ΩC, add_zero, Acocode,
      (Submodule.Quotient.mk_eq_zero C).2 (by
        have h : (a : Fin 24 → ZMod 2) * (ΩC : Fin 24 → ZMod 2) = a := by
          funext i
          simp [Ω]
        rw [h]
        exact a.2), add_zero]

theorem octLab_fst (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    (octLab ⟨d, v⟩).1 = ((d : C) + nOct (octRep d v) • ΩC,
      thetaD d + Submodule.Quotient.mk (Octad.ind (octRep d v))) := by
  show coordOf (rOct d (octRep d v)) = _
  rw [coordOf_rOct, aOct, thetaD_add_smul_ΩC]

theorem minusLab_fst (p : LtPair) : (minusLab p).1 = (0, deltaPair p.1.1 p.1.2) :=
  coordOf_rMinus _ _

theorem plusLab_fst (p : LtPair) : (plusLab p).1 = (ΩC, deltaPair p.1.1 p.1.2) := by
  show coordOf (rPlus p.1.1 p.1.2) = _
  rw [coordOf_rPlus, thetaD_ΩC, zero_add]

theorem oddLab_fst (a : C₀) (i : Fin 24) :
    (oddLab a i).1 = ((a : C) + mOdd a i • ΩC,
      thetaD (a : C) + Submodule.Quotient.mk (Pi.single i 1)) := by
  show coordOf (rOdd a i) = _
  rw [coordOf_rOdd, aOdd, thetaD_add_smul_ΩC]

theorem sum_sgl_sgl_mul (x y : ShortIdx) (f : ShortIdx → ℚ) :
    ∑ c, (Pi.single x 1 : SpaceX) c * (Pi.single y 1 : SpaceX) c * f c =
      if y = x then f x else 0 := by
  rw [Finset.sum_eq_single x]
  · by_cases h : y = x
    · subst h
      simp
    · rw [ite_eq_right h, Pi.single_eq_of_ne (Ne.symm h), mul_zero, zero_mul]
  · intro c _ hc
    simp [hc]
  · simp

theorem T_sgl_sgl_A (x y : ShortIdx) (A : symMat) :
    T (inX (Pi.single x 1)) (inX (Pi.single y 1)) (inA A) =
      if y = x then qf x A / 8 else 0 := by
  rw [T_XXA, sum_sgl_sgl_mul]
  split_ifs <;> ring

theorem T_sgl3 (x y z : ShortIdx) :
    T (inX (Pi.single x 1)) (inX (Pi.single y 1)) (inX (Pi.single z 1)) = tau x y z := by
  have h3 := sum3_single x y z 1 1 1
  simp only [one_smul, one_mul] at h3
  rw [T_XXX, h3]

theorem tau_eq (x y z : ShortIdx) :
    tau x y z = if z.1 = x.1 + y.1 then sgn (pair y.1.1 x.1.2) else 0 := by
  unfold tau
  split_ifs <;> rfl

noncomputable abbrev qd (d : OctadWord) : QuadraticForm (ZMod 2) (Octad.EvenQuot (octSupp d)) :=
  Octad.quadForm (octSupp d)

noncomputable abbrev bd (d : OctadWord) :
    LinearMap.BilinForm (ZMod 2) (Octad.EvenQuot (octSupp d)) :=
  QuadraticMap.polarBilin (qd d)

theorem four_dvd_card_octSupp (d : OctadWord) : 4 ∣ (octSupp d).card := by
  rw [card_octSupp]
  norm_num

theorem octRep_subset (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) : octRep d v ⊆ octSupp d :=
  (octRep_spec d v).1

theorem octRep_even (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) : Even (octRep d v).card :=
  (octRep_spec d v).2.1

theorem cls_octRep (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    Octad.cls (octSupp d) (octRep d v) = v :=
  (octRep_spec d v).2.2

theorem nOct_octRep (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    nOct (octRep d v) = qd d v := by
  conv_rhs => rw [← cls_octRep d v]
  rw [Octad.quadForm_cls (four_dvd_card_octSupp d) (octRep_subset d v) (octRep_even d v)]
  rfl

theorem bd_cls {d : OctadWord} {δ ε : Finset (Fin 24)} (hδ : δ ⊆ octSupp d) (hδe : Even δ.card)
    (hε : ε ⊆ octSupp d) (hεe : Even ε.card) :
    bd d (Octad.cls (octSupp d) δ) (Octad.cls (octSupp d) ε) = ((δ ∩ ε).card : ZMod 2) :=
  Octad.polarBilin_quadForm_cls (four_dvd_card_octSupp d) hδ hδe hε hεe

theorem bd_octRep (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    bd d v w = ((octRep d v ∩ octRep d w).card : ZMod 2) := by
  conv_lhs => rw [← cls_octRep d v, ← cls_octRep d w]
  exact bd_cls (octRep_subset d v) (octRep_even d v) (octRep_subset d w) (octRep_even d w)

theorem bd_nondegenerate (d : OctadWord) : (bd d).Nondegenerate :=
  Octad.polarBilin_quadForm_nondegenerate (four_dvd_card_octSupp d)
    (Finset.card_pos.1 (by rw [card_octSupp]; norm_num))

theorem sum_sgn_bd (d : OctadWord) (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) = if x = 0 then 64 else 0 := by
  rw [sum_sgn_bilin (bd_nondegenerate d), card_evenQuot_octSupp]
  norm_num

theorem bd_comm (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) : bd d v w = bd d w v :=
  polarBilin_symm _ v w

theorem bd_self (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) : bd d v v = 0 :=
  polarBilin_self _ v

theorem qd_add (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    qd d (v + w) = qd d v + qd d w + bd d v w :=
  quad_add _ v w

theorem octHD_apply (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    octHD d v w = (8 : ℚ)⁻¹ * sgn (bd d v w) * sgn (qd d w) := by
  rw [octHD, octH, octD, signMatrix, mul_diagonal, fourierMatrix]
  norm_num

theorem hammingNorm_Ω : hammingNorm (Ω : Fin 24 → ZMod 2) = 24 := by decide

theorem mem_octSupp {d : OctadWord} {i : Fin 24} : i ∈ octSupp d ↔ (d : Fin 24 → ZMod 2) i ≠ 0 :=
  mem_supp_iff

theorem coe_apply_eq_one {d : OctadWord} {i : Fin 24} (h : i ∈ octSupp d) :
    (d : Fin 24 → ZMod 2) i = 1 := by
  rcases zmod2_cases ((d : Fin 24 → ZMod 2) i) with h' | h'
  · exact absurd h' (mem_octSupp.1 h)
  · exact h'

theorem coe_apply_eq_zero {d : OctadWord} {i : Fin 24} (h : i ∉ octSupp d) :
    (d : Fin 24 → ZMod 2) i = 0 := by
  by_contra h'
  exact h (mem_octSupp.2 h')

theorem eq_zero_or_eq_of_supported {d : OctadWord} {x : Fin 24 → ZMod 2} (hx : x ∈ C)
    (hs : ∀ i, i ∉ octSupp d → x i = 0) : x = 0 ∨ x = d := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  · right
    have h8 := eight_le_wt hx h0
    have hsub : supp x ⊆ octSupp d := fun i hi => by
      by_contra h
      exact (mem_supp_iff.1 hi) (hs i h)
    have hcard : (supp x).card = 8 := by
      have h1 := Finset.card_le_card hsub
      rw [card_octSupp] at h1
      have h2 : (supp x).card = hammingNorm x := card_supp x
      omega
    have heq : supp x = octSupp d :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, card_octSupp])
    funext i
    by_cases hi : i ∈ octSupp d
    · rw [coe_apply_eq_one hi]
      have hxi : x i ≠ 0 := mem_supp_iff.1 (heq ▸ hi)
      rcases zmod2_cases (x i) with h | h
      · exact absurd h hxi
      · exact h
    · rw [coe_apply_eq_zero hi, hs i hi]

theorem ind_octSupp (d : OctadWord) : Octad.ind (octSupp d) = (d : Fin 24 → ZMod 2) :=
  Octad.ind_wordSupport _

theorem mk_eq_zero_iff_octMk_eq_zero {d : OctadWord} (x : Octad.evenSubsets (octSupp d)) :
    (Submodule.Quotient.mk (x : Fin 24 → ZMod 2) : Cocode) = 0 ↔ Octad.mk (octSupp d) x = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Octad.mk_eq_zero_iff, Octad.mem_complSpan_iff, ind_octSupp]
  constructor
  · intro h
    exact eq_zero_or_eq_of_supported h x.2.1
  · rintro (h | h)
    · rw [h]
      exact C.zero_mem
    · rw [h]
      exact (d : C).2

theorem octMk_eq_cls {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    Octad.mk (octSupp d) ⟨Octad.ind δ, Octad.ind_mem_evenSubsets hδ he⟩ =
      Octad.cls (octSupp d) δ :=
  (Octad.cls_eq hδ he).symm

theorem ind_mem_octRep (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    Octad.ind (octRep d v) ∈ Octad.evenSubsets (octSupp d) :=
  Octad.ind_mem_evenSubsets (octRep_subset d v) (octRep_even d v)

theorem octMk_octRep (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    Octad.mk (octSupp d) ⟨Octad.ind (octRep d v), ind_mem_octRep d v⟩ = v :=
  (octMk_eq_cls (octRep_subset d v) (octRep_even d v)).trans (cls_octRep d v)

theorem pair_mk_eq (a : C) (x : Fin 24 → ZMod 2) :
    pair a (Submodule.Quotient.mk x) = (a : Fin 24 → ZMod 2) ⬝ᵥ x := pair_mk a x

theorem pair_ΩC_ind {δ : Finset (Fin 24)} (he : Even δ.card) :
    pair ΩC (Submodule.Quotient.mk (Octad.ind δ)) = 0 := by
  rw [pair_mk, coe_ΩC, dotProduct]
  simp only [Ω, one_mul]
  rw [Octad.sum_ind (Finset.subset_univ δ)]
  exact (ZMod.natCast_eq_zero_iff_even).2 he

theorem pair_oct_ind {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) : pair (d : C) (Submodule.Quotient.mk (Octad.ind δ)) = 0 := by
  rw [pair_mk, dotProduct]
  have h : ∀ i, (d : Fin 24 → ZMod 2) i * Octad.ind δ i = Octad.ind δ i := by
    intro i
    by_cases hi : i ∈ δ
    · rw [coe_apply_eq_one (hδ hi), one_mul]
    · simp [Octad.ind, hi]
  simp only [h]
  rw [Octad.sum_ind (Finset.subset_univ δ)]
  exact (ZMod.natCast_eq_zero_iff_even).2 he

theorem P_oct (d : OctadWord) : P ((d : C) : Fin 24 → ZMod 2) = 0 := P_octad d.2

theorem add_self_F2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eq_iff_add_eq_zero_F2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x = y ↔ x + y = 0 :=
  ⟨fun h => by rw [h, add_self_F2], fun h => (add_eq_zero_iff'.1 h).symm⟩

theorem add_add_eq_zero_iff_F2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {v w h : M} :
    v + w + h = 0 ↔ w = v + h := by
  rw [eq_iff_add_eq_zero_F2 w (v + h)]
  constructor <;> intro H <;> rw [← H] <;> abel

theorem smul_ΩC_inj {m t : ZMod 2} : m • ΩC = t • ΩC ↔ m = t := by
  constructor
  · intro h
    have := congrArg μ₀ h
    rwa [map_smul, map_smul, μ₀_ΩC, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
  · rintro rfl
    rfl

theorem hammingNorm_add_Ω (x : Fin 24 → ZMod 2) : hammingNorm (x + Ω) + hammingNorm x = 24 := by
  have h := Code.hammingNorm_add_add x Ω
  have hx : x * Ω = x := by
    funext i
    simp [Ω]
  rw [hx, hammingNorm_Ω] at h
  omega

theorem octad_eq_of_add_eq_smul {d d' : OctadWord} {t : ZMod 2}
    (h : (d : C) + (d' : C) = t • ΩC) : d = d' ∧ t = 0 := by
  rcases zmod2_cases t with rfl | rfl
  · rw [zero_smul] at h
    exact ⟨Subtype.ext (add_eq_zero_iff'.1 h).symm, rfl⟩
  · exfalso
    rw [one_smul] at h
    have h' : ((d' : C) : Fin 24 → ZMod 2) = (d : Fin 24 → ZMod 2) + Ω := by
      have := congrArg (fun x : C => (x : Fin 24 → ZMod 2)) h
      simp only [Submodule.coe_add, coe_ΩC] at this
      rw [← this]
      funext i
      simp only [Pi.add_apply]
      exact zmod2_aux_add _ _
    have h1 := hammingNorm_add_Ω ((d : C) : Fin 24 → ZMod 2)
    rw [← h', d.2, d'.2] at h1
    omega

theorem pair_add_smul_ΩC_thetaD (a b : C) (n : ZMod 2) (ε : Cocode) :
    pair (a + n • ΩC) (thetaD b + ε) = θ b a + pair a ε + n * pair ΩC ε := by
  rw [pair_add_left, pair_smul_left, pair_add_right, pair_add_right, pair_thetaD,
    pair_ΩC_thetaD]
  ring

theorem ind_pair {k l : Fin 24} (hkl : k ≠ l) :
    Octad.ind ({k, l} : Finset (Fin 24)) = Pi.single k 1 + Pi.single l 1 := by
  funext i
  simp only [Octad.ind, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, Pi.single_apply]
  by_cases h1 : i = k <;> by_cases h2 : i = l <;> simp_all

theorem even_card_pair {k l : Fin 24} (hkl : k ≠ l) : Even ({k, l} : Finset (Fin 24)).card := by
  rw [Finset.card_pair hkl]
  exact even_two

theorem pair_subset_octSupp {d : OctadWord} {k l : Fin 24} (hk : k ∈ octSupp d)
    (hl : l ∈ octSupp d) : ({k, l} : Finset (Fin 24)) ⊆ octSupp d :=
  Finset.insert_subset hk (Finset.singleton_subset_iff.2 hl)

theorem card_inter_pair (δ : Finset (Fin 24)) {k l : Fin 24} (hkl : k ≠ l) :
    ((δ ∩ {k, l}).card : ZMod 2) = Octad.ind δ k + Octad.ind δ l := by
  rw [← Octad.sum_ind (Finset.inter_subset_right : δ ∩ {k, l} ⊆ {k, l}), Finset.sum_pair hkl]
  simp [Octad.ind, Finset.mem_inter]

theorem bd_pair (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) {k l : Fin 24}
    (hkl : k ≠ l) (hk : k ∈ octSupp d) (hl : l ∈ octSupp d) :
    bd d v (Octad.cls (octSupp d) {k, l}) =
      Octad.ind (octRep d v) k + Octad.ind (octRep d v) l := by
  conv_lhs => rw [← cls_octRep d v]
  rw [bd_cls (octRep_subset d v) (octRep_even d v) (pair_subset_octSupp hk hl)
    (even_card_pair hkl), card_inter_pair _ hkl]

theorem uQ_mul_uQ_label (l : ShortLabel) (i j : Fin 24) :
    uQ (labelIdx l) i * uQ (labelIdx l) j = (labelVec l i : ℚ) * (labelVec l j : ℚ) := by
  have h := (classOf_eq_iff (uvec_mem (labelIdx l)) (labelVec_mem l)).1
    ((classOf_uvec (labelIdx l)).trans (phi0_labelElt l))
  show ((uvec (labelIdx l) i : ℤ) : ℚ) * ((uvec (labelIdx l) j : ℤ) : ℚ) = _
  rcases h with h | h
  · rw [h]
  · rw [h, Pi.neg_apply, Pi.neg_apply, Int.cast_neg, Int.cast_neg, neg_mul_neg]

theorem cast_vOct (d : OctadWord) {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d) (i : Fin 24) :
    ((vOct ((d : C) : Fin 24 → ZMod 2) δ i : ℤ) : ℚ) =
      if i ∈ octSupp d then 2 * sgn (Octad.ind δ i) else 0 := by
  simp only [vOct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, liftℤ, Int.cast_sub, Int.cast_mul]
  by_cases hi : i ∈ octSupp d
  · rw [ite_eq_left hi, coe_apply_eq_one hi, bitLift_one]
    by_cases hiδ : i ∈ δ
    · simp only [Octad.ind, hiδ, ite_true, bitLift_one]
      norm_num [sgn]
    · simp only [Octad.ind, hiδ, ite_false]
      norm_num [sgn, bitLift]
  · have hiδ : i ∉ δ := fun h => hi (hδ h)
    rw [ite_eq_right hi, coe_apply_eq_zero hi]
    simp only [Octad.ind, hiδ, ite_false]
    norm_num [bitLift]

theorem uQ_mul_uQ_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) (i j : Fin 24) :
    uQ (octLab ⟨d, v⟩) i * uQ (octLab ⟨d, v⟩) j =
      (if i ∈ octSupp d then 2 * sgn (Octad.ind (octRep d v) i) else 0) *
        (if j ∈ octSupp d then 2 * sgn (Octad.ind (octRep d v) j) else 0) := by
  rw [uQ_mul_uQ_label]
  exact congrArg₂ (· * ·) (cast_vOct d (octRep_subset d v) i) (cast_vOct d (octRep_subset d v) j)

theorem not_mem_C_of_outside {d : OctadWord} {x : Fin 24 → ZMod 2} {k l : Fin 24} (hkl : k ≠ l)
    (hx : ∀ i, i ∉ octSupp d → x i = (Pi.single k 1 + Pi.single l 1 : Fin 24 → ZMod 2) i)
    (hout : ¬(k ∈ octSupp d ∧ l ∈ octSupp d)) : x ∉ C := by
  intro hxC
  obtain ⟨m, hm, hxm⟩ : ∃ m, m ∉ octSupp d ∧ x m = 1 := by
    by_cases hk : k ∈ octSupp d
    · have hl : l ∉ octSupp d := fun hl => hout ⟨hk, hl⟩
      refine ⟨l, hl, ?_⟩
      rw [hx l hl, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hkl), Pi.single_eq_same, zero_add]
    · refine ⟨k, hk, ?_⟩
      rw [hx k hk, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl, add_zero]
  have hx0 : x ≠ 0 := fun h => by
    rw [h] at hxm
    exact zero_ne_one hxm
  have hxd : x + ((d : C) : Fin 24 → ZMod 2) ≠ 0 := fun h => by
    have := congrFun h m
    rw [Pi.add_apply, coe_apply_eq_zero hm, add_zero, hxm] at this
    exact one_ne_zero this
  have h1 := eight_le_wt hxC hx0
  have h2 := eight_le_wt (C.add_mem hxC (d : C).2) hxd
  have h3 := Code.hammingNorm_add_add x ((d : C) : Fin 24 → ZMod 2)
  rw [d.2] at h3
  have h4 : hammingNorm x ≤ hammingNorm (x * ((d : C) : Fin 24 → ZMod 2)) + 2 := by
    rw [← card_supp, ← card_supp, ← supp_inter]
    calc (supp x).card ≤ (supp x ∩ octSupp d ∪ {k, l}).card := by
          refine Finset.card_le_card fun i hi => ?_
          by_cases hid : i ∈ octSupp d
          · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hi, hid⟩)
          · apply Finset.mem_union_right
            have hxi := mem_supp_iff.1 hi
            rw [hx i hid, Pi.add_apply, Pi.single_apply, Pi.single_apply] at hxi
            rw [Finset.mem_insert, Finset.mem_singleton]
            by_contra hc
            simp only [not_or] at hc
            rw [ite_eq_right hc.1, ite_eq_right hc.2, add_zero] at hxi
            exact hxi rfl
      _ ≤ (supp x ∩ octSupp d).card + ({k, l} : Finset (Fin 24)).card := Finset.card_union_le _ _
      _ ≤ (supp x ∩ octSupp d).card + 2 := by
          have := Finset.card_le_two (a := k) (b := l)
          omega
  omega

end CFSG.Monster.Griess.OctadInv
