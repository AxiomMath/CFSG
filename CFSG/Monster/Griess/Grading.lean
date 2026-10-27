module

public import CFSG.Monster.Griess.Product
public import CFSG.Monster.Griess.TrialityMatrix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module

abbrev CmodΩ : Type := C ⧸ (ZMod 2 ∙ ΩC)

abbrev Gam : Type := (ZMod 2 × ZMod 2) × CmodΩ

noncomputable instance : DecidableEq Gam := Classical.decEq _

@[expose] def gx : ZMod 2 × ZMod 2 := (1, 0)

@[expose] def gy : ZMod 2 × ZMod 2 := (0, 1)

@[expose] def gz : ZMod 2 × ZMod 2 := (1, 1)

theorem gx_add_gy : gx + gy = gz := rfl

abbrev clsΩ (a : C) : CmodΩ := Submodule.Quotient.mk a

theorem clsΩ_ΩC : (Submodule.Quotient.mk ΩC : CmodΩ) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self ΩC)

@[expose] def xgrade (p : C × Cocode) : Gam := ((pair ΩC p.2, 0), clsΩ p.1)

@[expose] def wgrade (k : SpinIdx) : Gam := ((1 + k.1, 1), clsΩ (k.2 : C))

@[expose] def bgrade : BIdx → Gam
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl c) => xgrade c.1
  | Sum.inr (Sum.inr k) => wgrade k.1

@[expose] noncomputable def Bstd (g : Gam) : Submodule ℚ SpaceB :=
  Submodule.span ℚ (basisB '' {k | bgrade k = g})

theorem add_self_gam (x : Gam) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem xgrade_add (p q : C × Cocode) : xgrade (p + q) = xgrade p + xgrade q := by
  simp only [xgrade, Prod.snd_add, Prod.fst_add, pair_add_right, Submodule.Quotient.mk_add,
    Prod.mk_add_mk, add_zero]

theorem wgrade_qPerm (a : C) (δ : Cocode) (k : SpinIdx) :
    wgrade (qPerm a δ k) = wgrade k + xgrade (a, δ) := by
  have h : clsΩ (shift a k.2 : C) = clsΩ (k.2 : C) + clsΩ a := by
    rw [coe_shift]
    simp only [clsΩ, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, clsΩ_ΩC, smul_zero,
      add_zero]
  simp only [wgrade, xgrade, qPerm, h, Prod.mk_add_mk, add_zero]
  congr 2
  ring

theorem T_single_single_A {c d : ShortIdx} (h : xgrade c.1 + xgrade d.1 + 0 ≠ 0) (A : symMat) :
    T (inX (Pi.single c 1)) (inX (Pi.single d 1)) (inA A) = 0 := by
  have hcd : c ≠ d := fun hcd => h (by rw [hcd, add_zero, add_self_gam])
  rw [T_XXA]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun e _ => ?_)
  by_cases hc : e = c
  · subst hc
    simp [hcd]
  · simp [Pi.single_apply, hc]

theorem T_single3 {c d e : ShortIdx} (h : xgrade c.1 + xgrade d.1 + xgrade e.1 ≠ 0) :
    T (inX (Pi.single c 1)) (inX (Pi.single d 1)) (inX (Pi.single e 1)) = 0 := by
  have h3 := sum3_single c d e 1 1 1
  simp only [one_smul, one_mul] at h3
  rw [T_XXX, h3]
  unfold tau
  rw [ite_eq_right]
  intro he
  apply h
  rw [he, xgrade_add]
  exact add_self_gam _

theorem T_tensor_single_A {k l : SpinIdx} (h : wgrade k + wgrade l + 0 ≠ 0) (i j : Fin 24)
    (A : symMat) :
    T (inW (tensor (Pi.single k 1) (Pi.single i 1))) (inW (tensor (Pi.single l 1) (Pi.single j 1)))
      (inA A) = 0 := by
  have hkl : k ≠ l := fun hkl => h (by rw [hkl, add_zero, add_self_gam])
  rw [T_tensor_tensor_A, single_dotProduct_single, ite_eq_right hkl, zero_mul]

theorem T_tensor_single_X {k l : SpinIdx} {c : ShortIdx} (h : wgrade k + wgrade l + xgrade c.1 ≠ 0)
    (i j : Fin 24) :
    T (inW (tensor (Pi.single k 1) (Pi.single i 1))) (inW (tensor (Pi.single l 1) (Pi.single j 1)))
      (inX (Pi.single c 1)) = 0 := by
  have hl : qPerm c.1.1 c.1.2 k ≠ l := fun hl => h (by
    rw [← hl, wgrade_qPerm, ← add_assoc, add_self_gam, zero_add, add_self_gam])
  have hs : ∀ f : ShortIdx → ℚ, ∑ x, (Pi.single c 1 : SpaceX) x * f x = f c := fun f => by
    simpa using sum_single_mul c 1 f
  rw [T_WWX, hs, gWWX_tensor, Rmat, single_vecMul_qmatR, smul_dotProduct,
    single_dotProduct_single, ite_eq_right hl, smul_zero, zero_mul, zero_div]

theorem T_basisB_eq_zero (i j k : BIdx) (h : bgrade i + bgrade j + bgrade k ≠ 0) :
    T (basisB i) (basisB j) (basisB k) = 0 := by
  rcases i with z₁ | c₁ | k₁ <;> rcases j with z₂ | c₂ | k₂ <;> rcases k with z₃ | c₃ | k₃ <;>
    simp only [bgrade] at h <;>
    simp only [basisB_inl, basisB_inr_inl, basisB_inr_inr]
  · exact absurd (by simp) h
  · exact T_AAX _ _ _
  · exact T_AAW _ _ _
  · rw [T_swap23]; exact T_AAX _ _ _
  · rw [T_swap12, T_swap23]
    exact T_single_single_A (by convert h using 1; abel) _
  · exact T_AXW _ _ _
  · rw [T_swap23]; exact T_AAW _ _ _
  · rw [T_swap23]; exact T_AXW _ _ _
  · rw [T_swap12, T_swap23]
    exact T_tensor_single_A (by convert h using 1; abel) _ _ _
  · rw [T_swap12, T_swap23]; exact T_AAX _ _ _
  · rw [T_swap23]
    exact T_single_single_A (by convert h using 1; abel) _
  · rw [T_swap12]; exact T_AXW _ _ _
  · exact T_single_single_A h _
  · exact T_single3 h
  · exact T_XXW _ _ _
  · rw [T_swap23, T_swap12]; exact T_AXW _ _ _
  · rw [T_swap23]; exact T_XXW _ _ _
  · rw [T_swap12, T_swap23]
    exact T_tensor_single_X (by convert h using 1; abel) _ _
  · rw [T_swap12, T_swap23]; exact T_AAW _ _ _
  · rw [T_swap12, T_swap23]; exact T_AXW _ _ _
  · rw [T_swap23]
    exact T_tensor_single_A (by convert h using 1; abel) _ _ _
  · rw [T_swap23, T_swap12, T_swap23]; exact T_AXW _ _ _
  · rw [T_swap12, T_swap23]; exact T_XXW _ _ _
  · rw [T_swap23]
    exact T_tensor_single_X (by convert h using 1; abel) _ _
  · exact T_tensor_single_A h _ _ _
  · exact T_tensor_single_X h _ _
  · exact T_WWW _ _ _

theorem T_Bstd {g h k : Gam} (hghk : g + h + k ≠ 0) {u v w : SpaceB} (hu : u ∈ Bstd g)
    (hv : v ∈ Bstd h) (hw : w ∈ Bstd k) : T u v w = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      induction hw using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨l, hl, rfl⟩ := hz
        refine T_basisB_eq_zero i j l ?_
        have hi' : bgrade i = g := hi
        have hj' : bgrade j = h := hj
        have hl' : bgrade l = k := hl
        rw [hi', hj', hl']
        exact hghk
      | zero => exact map_zero _
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul c a _ ha => rw [map_smul, ha, smul_zero]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, ha, smul_zero]

@[expose] def oddSlot : Fin 3 → ZMod 2 × ZMod 2
  | 0 => gx
  | 1 => gy
  | 2 => gz

@[expose] def tgrade : TIdx → Gam
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl x)) => (oddSlot x.2.2, clsΩ (x.1 : C))
  | Sum.inr (Sum.inr (Sum.inr o)) => (0, clsΩ (o.1 : C))

@[expose] noncomputable def Bg (g : Gam) : Submodule ℚ SpaceB :=
  Submodule.span ℚ (tbasis '' {x | tgrade x = g})

theorem tbasis_mem_Bg (x : TIdx) : tbasis x ∈ Bg (tgrade x) :=
  Submodule.subset_span ⟨x, rfl, rfl⟩

theorem basisB_mem_Bstd (k : BIdx) : basisB k ∈ Bstd (bgrade k) :=
  Submodule.subset_span ⟨k, rfl, rfl⟩

theorem pair_ΩC_mk (v : Fin 24 → ZMod 2) :
    pair ΩC (Submodule.Quotient.mk v) = ∑ k, v k := by
  rw [pair_mk, coe_ΩC, dotProduct]
  simp [Ω]

theorem inX_smul (t : ℚ) (x : SpaceX) : inX (t • x) = t • inX x := by
  rw [inX, inX, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem inW_smul (t : ℚ) (N : SpaceW) : inW (t • N) = t • inW N := by
  rw [inW, inW, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem inX_sub (x y : SpaceX) : inX (x - y) = inX x - inX y := by
  rw [inX, inX, inX, Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]

theorem inX_add (x y : SpaceX) : inX (x + y) = inX x + inX y := by
  rw [inX, inX, inX, Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]

theorem inX_Xlift_mem_Bstd {r : Q} (hr : IsShortCoord (coordOf r)) :
    inX (Xlift r) ∈ Bstd (xgrade (coordOf r)) := by
  have h : inX (Xlift r) = sgn (centralCoord r) • basisB (Sum.inr (Sum.inl ⟨coordOf r, hr⟩)) :=
    (congrArg inX (Xlift_eq hr)).trans ((inX_smul _ _).trans
      (congrArg (sgn (centralCoord r) • ·) (basisB_inr_inl _).symm))
  rw [h]
  exact Submodule.smul_mem _ _ (basisB_mem_Bstd (Sum.inr (Sum.inl ⟨coordOf r, hr⟩)))

theorem inW_tensor_mem_Bstd (η : ZMod 2) (c : C₀) (i : Fin 24) (t : ℚ) :
    inW (t • tensor (Spin.E η c) (Pi.single i 1)) ∈ Bstd (wgrade (η, c)) := by
  have h : inW (t • tensor (Spin.E η c) (Pi.single i 1)) =
      t • basisB (Sum.inr (Sum.inr ((η, c), i))) :=
    (inW_smul _ _).trans (congrArg (t • ·) (basisB_inr_inr ((η, c), i)).symm)
  rw [h]
  exact Submodule.smul_mem _ _ (basisB_mem_Bstd (Sum.inr (Sum.inr ((η, c), i))))

theorem two_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

theorem xgrade_rMinus (i j : Fin 24) : xgrade (coordOf (rMinus i j)) = 0 := by
  rw [coordOf_rMinus, xgrade, deltaPair, pair_ΩC_mk]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true, two_zmod2, Submodule.Quotient.mk_zero]
  rfl

theorem xgrade_rPlus (i j : Fin 24) : xgrade (coordOf (rPlus i j)) = 0 := by
  rw [coordOf_rPlus, xgrade, pair_add_right, pair_ΩC_thetaD, zero_add, deltaPair, pair_ΩC_mk]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true, two_zmod2]
  rw [show clsΩ ΩC = 0 from clsΩ_ΩC]
  rfl

theorem xgrade_rOdd (c : C₀) (i : Fin 24) : xgrade (coordOf (rOdd c i)) = (gx, clsΩ (c : C)) := by
  rw [coordOf_rOdd, xgrade, pair_add_right, pair_ΩC_thetaD, zero_add, pair_ΩC_mk]
  simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true]
  have h : clsΩ (aOdd c i) = clsΩ (c : C) := by
    rw [aOdd]
    simp only [clsΩ, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, clsΩ_ΩC, smul_zero,
      add_zero]
  rw [h]
  rfl

theorem xgrade_rOct (d : C) {δ : Finset (Fin 24)} (he : Even δ.card) :
    xgrade (coordOf (rOct d δ)) = (0, clsΩ d) := by
  rw [coordOf_rOct, xgrade, pair_add_right, pair_ΩC_thetaD, zero_add, pair_ΩC_mk,
    Octad.sum_ind (Finset.subset_univ δ), (ZMod.natCast_eq_zero_iff_even).2 he]
  have h : clsΩ (aOct d δ) = clsΩ d := by
    rw [aOct]
    simp only [clsΩ, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, clsΩ_ΩC, smul_zero,
      add_zero]
  rw [h]
  rfl

theorem isShortCoord_of_tbasis {r : Q} (h : IsShort (QuotientGroup.mk r)) :
    IsShortCoord (coordOf r) := (isShort_mk_iff r).1 h

theorem tbasis_mem_Bstd (x : TIdx) : tbasis x ∈ Bstd (tgrade x) := by
  obtain ⟨_, _, _, _, hPair, hOdd, hOct, -⟩ := short_vector_triality_basis
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · rw [tbasis_diag]
    exact basisB_inl _ ▸ basisB_mem_Bstd (Sum.inl s(i, i))
  · have hm := (isShort_mk_iff _).1 (hPair p).1
    have hp := (isShort_mk_iff _).1 (hPair p).2.1
    have h1 := inX_Xlift_mem_Bstd hm
    have h2 := inX_Xlift_mem_Bstd hp
    rw [xgrade_rMinus] at h1
    rw [xgrade_rPlus] at h2
    fin_cases k
    · show tbasis (.inr (.inl (p, 0))) ∈ Bstd 0
      rw [tbasis_pair_zero]
      exact basisB_inl _ ▸ basisB_mem_Bstd (Sum.inl s(p.1.1, p.1.2))
    · show tbasis (.inr (.inl (p, 1))) ∈ Bstd 0
      rw [tbasis_pair_one]
      show inX (Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2)) ∈ Bstd 0
      rw [inX_sub]
      exact sub_mem h1 h2
    · show tbasis (.inr (.inl (p, 2))) ∈ Bstd 0
      rw [tbasis_pair_two]
      show inX (Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2)) ∈ Bstd 0
      rw [inX_add]
      exact add_mem h1 h2
  · fin_cases k
    · show tbasis (.inr (.inr (.inl (c, i, 0)))) ∈ Bstd (gx, clsΩ (c : C))
      rw [tbasis_odd_zero]
      have h := inX_Xlift_mem_Bstd ((isShort_mk_iff _).1 (hOdd c i).1)
      rw [xgrade_rOdd] at h
      exact h
    · show tbasis (.inr (.inr (.inl (c, i, 1)))) ∈ Bstd (wgrade (1, c))
      rw [tbasis_odd_one]
      exact inW_tensor_mem_Bstd 1 c i _
    · show tbasis (.inr (.inr (.inl (c, i, 2)))) ∈ Bstd (wgrade (0, c))
      rw [tbasis_odd_two]
      exact inW_tensor_mem_Bstd 0 c i _
  · rw [tbasis_oct]
    obtain ⟨hδ, he, hcls⟩ := octRep_spec d v
    have h := inX_Xlift_mem_Bstd ((isShort_mk_iff _).1 (hOct d (octRep d v) hδ he).1)
    rw [xgrade_rOct (d : C) he] at h
    exact h

theorem Bg_le_Bstd (g : Gam) : Bg g ≤ Bstd g := by
  rw [Bg, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : tgrade x = g := hx
  exact hx' ▸ tbasis_mem_Bstd x

theorem T_Bg {g h k : Gam} (hghk : g + h + k ≠ 0) {u v w : SpaceB} (hu : u ∈ Bg g)
    (hv : v ∈ Bg h) (hw : w ∈ Bg k) : T u v w = 0 :=
  T_Bstd hghk (Bg_le_Bstd g hu) (Bg_le_Bstd h hv) (Bg_le_Bstd k hw)

theorem bform_Bg_eq_zero {g h : Gam} (hgh : g ≠ h) {u v : SpaceB} (hu : u ∈ Bg g)
    (hv : v ∈ Bg h) : bform u v = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hi' : tgrade i = g := hi
      have hj' : tgrade j = h := hj
      have hij : i ≠ j := fun e => hgh (by rw [← hi', ← hj', e])
      rw [bform_tbasis, ite_eq_right hij]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

theorem iSup_Bg : ⨆ g, Bg g = ⊤ := by
  rw [eq_top_iff, ← tbasis.span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact Submodule.mem_iSup_of_mem (tgrade x) (tbasis_mem_Bg x)

theorem iSupIndep_Bg : iSupIndep Bg := by
  intro g
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx1, hx2⟩
  have hker : ⨆ (h : Gam) (_ : h ≠ g), Bg h ≤ LinearMap.ker (bform x) :=
    iSup₂_le fun h hne v hv => LinearMap.mem_ker.2 (bform_Bg_eq_zero (Ne.symm hne) hx1 hv)
  have h0 : bform x x = 0 := LinearMap.mem_ker.1 (hker hx2)
  rw [Submodule.mem_bot]
  by_contra hne
  exact lt_irrefl _ (h0 ▸ bform_self_pos hne)

theorem isInternal_Bg : DirectSum.IsInternal Bg :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_Bg iSup_Bg

theorem bform_tbasis_right (x : SpaceB) (y : TIdx) :
    bform x (tbasis y) = tbasis.repr x y * tnorm y := by
  have h : LinearMap.flip bform (tbasis y) = tnorm y • tbasis.coord y := by
    refine tbasis.ext fun z => ?_
    rw [LinearMap.flip_apply, bform_tbasis, LinearMap.smul_apply, Basis.coord_apply,
      Basis.repr_self, smul_eq_mul]
    by_cases hz : z = y
    · subst hz
      rw [ite_eq_left rfl, Finsupp.single_eq_same, mul_one]
    · rw [ite_eq_right hz, Finsupp.single_eq_of_ne (Ne.symm hz), mul_zero]
  have h' := congrArg (fun f : SpaceB →ₗ[ℚ] ℚ => f x) h
  simp only [LinearMap.flip_apply, LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul] at h'
  rw [h', mul_comm]

theorem mem_Bg_of_orthogonal {m : Gam} {x : SpaceB}
    (h : ∀ y, tgrade y ≠ m → bform x (tbasis y) = 0) : x ∈ Bg m := by
  rw [← tbasis.sum_repr x]
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : tgrade y = m
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  · have h1 := h y hy
    rw [bform_tbasis_right] at h1
    rw [(mul_eq_zero.1 h1).resolve_right (tnorm_ne_zero y), zero_smul]
    exact zero_mem _

theorem gmul_mem_Bg {g h : Gam} {u v : SpaceB} (hu : u ∈ Bg g) (hv : v ∈ Bg h) :
    gmul u v ∈ Bg (g + h) :=
  mem_Bg_of_orthogonal fun y hy => by
    rw [bform_gmul]
    exact T_Bg (fun h0 => hy (eq_of_add_eq_zero' h0)) hu hv (tbasis_mem_Bg y)

@[expose] def alpha2 (a : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (a.2, a.1 + a.2)

theorem alpha2_alpha2_alpha2 (a : ZMod 2 × ZMod 2) : alpha2 (alpha2 (alpha2 a)) = a := by
  revert a
  decide

theorem alpha2_add (a b : ZMod 2 × ZMod 2) : alpha2 (a + b) = alpha2 a + alpha2 b := by
  revert a b
  decide

@[expose] def alphaG : Gam ≃+ Gam where
  toFun g := (alpha2 g.1, g.2)
  invFun g := (alpha2 (alpha2 g.1), g.2)
  left_inv g := Prod.ext (alpha2_alpha2_alpha2 g.1) rfl
  right_inv g := Prod.ext (alpha2_alpha2_alpha2 g.1) rfl
  map_add' g h := Prod.ext (alpha2_add g.1 h.1) rfl

theorem alphaG_apply (g : Gam) : alphaG g = (alpha2 g.1, g.2) := rfl

theorem alphaG_gx (c : CmodΩ) : alphaG (gx, c) = (gy, c) :=
  Prod.ext (show alpha2 gx = gy by decide) rfl

theorem alphaG_gy (c : CmodΩ) : alphaG (gy, c) = (gz, c) :=
  Prod.ext (show alpha2 gy = gz by decide) rfl

theorem alphaG_gz (c : CmodΩ) : alphaG (gz, c) = (gx, c) :=
  Prod.ext (show alpha2 gz = gx by decide) rfl

theorem alphaG_zero_left (c : CmodΩ) : alphaG (0, c) = (0, c) :=
  Prod.ext (show alpha2 0 = 0 by decide) rfl

theorem alphaG_alphaG_alphaG (g : Gam) : alphaG (alphaG (alphaG g)) = g :=
  Prod.ext (alpha2_alpha2_alpha2 g.1) rfl

theorem alpha2_oddSlot (k : Fin 3) : alpha2 (oddSlot k) = oddSlot (k + 1) := by
  revert k
  decide

theorem tauB_tbasis_mem_Bg (x : TIdx) : tauB (tbasis x) ∈ Bg (alphaG (tgrade x)) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · rw [tauB_diag]
    have h : alphaG (tgrade (.inl i)) = tgrade (.inl i) := alphaG_zero_left 0
    rw [h]
    exact tbasis_mem_Bg _
  · rw [tauB_pair]
    have h : alphaG (tgrade (.inr (.inl (p, k)))) = tgrade (.inr (.inl (p, k + 1))) :=
      alphaG_zero_left 0
    rw [h]
    exact tbasis_mem_Bg _
  · rw [tauB_odd]
    have h : alphaG (tgrade (.inr (.inr (.inl (c, i, k))))) =
        tgrade (.inr (.inr (.inl (c, i, k + 1)))) :=
      Prod.ext (alpha2_oddSlot k) rfl
    rw [h]
    exact tbasis_mem_Bg _
  · rw [tauB_oct]
    have h : alphaG (tgrade (.inr (.inr (.inr ⟨d, v⟩)))) = (0, clsΩ (d : C)) :=
      alphaG_zero_left _
    rw [h]
    exact Submodule.sum_mem _ fun w _ =>
      Submodule.smul_mem _ _ (tbasis_mem_Bg (.inr (.inr (.inr ⟨d, w⟩))))

theorem tauB_mem_Bg {g : Gam} {u : SpaceB} (hu : u ∈ Bg g) : tauB u ∈ Bg (alphaG g) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : tgrade i = g := hi
    exact hi' ▸ tauB_tbasis_mem_Bg i
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem tauB_inv_eq : tauB⁻¹ = tauB * tauB :=
  inv_eq_of_mul_eq_one_right ((pow_three tauB).symm.trans tauB_pow_three)

theorem tauB_symm_apply' (u : SpaceB) : tauB.symm u = tauB (tauB u) :=
  congrArg (fun f : SpaceB ≃ₗ[ℚ] SpaceB => f u) tauB_inv_eq

theorem map_tauB_Bg (g : Gam) : (Bg g).map (tauB : SpaceB →ₗ[ℚ] SpaceB) = Bg (alphaG g) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact tauB_mem_Bg hu
  · intro v hv
    refine ⟨tauB.symm v, ?_, tauB.apply_symm_apply v⟩
    rw [tauB_symm_apply']
    have h := tauB_mem_Bg (tauB_mem_Bg hv)
    rwa [alphaG_alphaG_alphaG] at h

theorem tauB_symm_mem_Bg {g : Gam} {u : SpaceB} (hu : u ∈ Bg (alphaG g)) : tauB.symm u ∈ Bg g := by
  rw [tauB_symm_apply']
  have h := tauB_mem_Bg (tauB_mem_Bg hu)
  rwa [alphaG_alphaG_alphaG] at h

theorem rational_Griess_binary_grading :
    (∀ i : Fin 24, tgrade (.inl i) = 0) ∧ (∀ q : LtPair × Fin 3, tgrade (.inr (.inl q)) = 0) ∧
    (∀ (c : C₀) (i : Fin 24), tgrade (.inr (.inr (.inl (c, i, 0)))) = (gx, clsΩ (c : C)) ∧
      tgrade (.inr (.inr (.inl (c, i, 1)))) = (gy, clsΩ (c : C)) ∧
      tgrade (.inr (.inr (.inl (c, i, 2)))) = (gz, clsΩ (c : C))) ∧
    (∀ o : OctIdx, tgrade (.inr (.inr (.inr o))) = (0, clsΩ (o.1 : C))) ∧
    gx + gy = gz ∧
    (∀ g, Bg g = Submodule.span ℚ (tbasis '' {x | tgrade x = g})) ∧
    DirectSum.IsInternal Bg ∧
    (∀ g h : Gam, g ≠ h → ∀ u ∈ Bg g, ∀ v ∈ Bg h, bform u v = 0) ∧
    (∀ g h k : Gam, g + h + k ≠ 0 → ∀ u ∈ Bg g, ∀ v ∈ Bg h, ∀ w ∈ Bg k, T u v w = 0) ∧
    (∀ g h : Gam, ∀ u ∈ Bg g, ∀ v ∈ Bg h, gmul u v ∈ Bg (g + h)) ∧
    (∀ c : CmodΩ, alphaG (gx, c) = (gy, c) ∧ alphaG (gy, c) = (gz, c) ∧ alphaG (gz, c) = (gx, c) ∧
      alphaG (0, c) = (0, c)) ∧
    (∀ g, (Bg g).map (tauB : SpaceB →ₗ[ℚ] SpaceB) = Bg (alphaG g)) ∧
    (∀ g h k : Gam, g + h + k = 0 ↔ alphaG g + alphaG h + alphaG k = 0) ∧
    (∀ g h k : Gam, g + h + k = 0 ↔ alphaG.symm g + alphaG.symm h + alphaG.symm k = 0) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, gx_add_gy, fun _ => rfl,
    isInternal_Bg, fun _ _ hgh _ hu _ hv => bform_Bg_eq_zero hgh hu hv,
    fun _ _ _ h _ hu _ hv _ hw => T_Bg h hu hv hw, fun _ _ _ hu _ hv => gmul_mem_Bg hu hv,
    fun c => ⟨alphaG_gx c, alphaG_gy c, alphaG_gz c, alphaG_zero_left c⟩, map_tauB_Bg,
    fun g h k => by rw [← map_add, ← map_add, AddEquivClass.map_eq_zero_iff],
    fun g h k => by rw [← map_add, ← map_add, AddEquivClass.map_eq_zero_iff]⟩

end CFSG.Monster.Griess
