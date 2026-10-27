module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflectionCharpoly
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix Certificates.A8Nbr476

namespace CFSG.StandardType.A11

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem a11rf_shuffle {G : Type} [Group G] (a0 a1 a2 a3 b0 b1 b2 b3 : G)
    (h01 : Commute b0 a1) (h02 : Commute b0 a2) (h03 : Commute b0 a3)
    (h12 : Commute b1 a2) (h13 : Commute b1 a3) (h23 : Commute b2 a3) :
    (a0*a1*a2*a3)*(b0*b1*b2*b3) = (a0*b0)*(a1*b1)*(a2*b2)*(a3*b3) := by
  group
  rw [Commute.right_comm h03.symm]
  rw [Commute.right_comm h02.symm]
  rw [Commute.right_comm h01.symm]
  rw [Commute.right_comm h13.symm]
  rw [Commute.right_comm h12.symm]
  rw [Commute.right_comm h23.symm]

private theorem a11rf_fPow_add {G : Type} [Group G] {f : Fin 4 → G}
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (u v : Fin 4 → ZMod 7) :
    fPow f (u + v) = fPow f u * fPow f v := by
  have hcoord : ∀ i, f i ^ ((u + v) i).val = f i ^ (u i).val * f i ^ (v i).val := by
    intro i
    rw [Pi.add_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod ((u i).val + (v i).val)
      (by rw [← hord i]; exact pow_orderOf_eq_one (f i))]
    rw [pow_add]
  simp only [fPow]
  rw [hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  exact (a11rf_shuffle (f 0 ^ (u 0).val) (f 1 ^ (u 1).val) (f 2 ^ (u 2).val) (f 3 ^ (u 3).val)
    (f 0 ^ (v 0).val) (f 1 ^ (v 1).val) (f 2 ^ (v 2).val) (f 3 ^ (v 3).val)
    (Commute.pow_pow (hcomm 0 1) _ _) (Commute.pow_pow (hcomm 0 2) _ _)
    (Commute.pow_pow (hcomm 0 3) _ _) (Commute.pow_pow (hcomm 1 2) _ _)
    (Commute.pow_pow (hcomm 1 3) _ _) (Commute.pow_pow (hcomm 2 3) _ _)).symm

private theorem a11rf_fPow_zero {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f 0 = 1 := by
  simp [fPow]

private theorem a11rf_fPow_single {G : Type} [Group G] (f : Fin 4 → G) (i : Fin 4) :
    fPow f (Pi.single i 1) = f i := by
  have h1 : (1 : ZMod 7).val = 1 := ZMod.val_one'' (by norm_num)
  fin_cases i <;> simp [fPow, Pi.single, h1]

private def a11rf_fPowSubgroup {G : Type} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7) :
    Subgroup G where
  carrier := Set.range (fPow f)
  one_mem' := ⟨0, a11rf_fPow_zero f⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, a11rf_fPow_add hcomm hord u v⟩
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    refine ⟨-u, ?_⟩
    have h : fPow f (-u) * fPow f u = 1 := by
      rw [← a11rf_fPow_add hcomm hord, neg_add_cancel, a11rf_fPow_zero]
    exact eq_inv_of_mul_eq_one_left h

private theorem a11rf_fPow_surj {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hBs : Subgroup.closure (Set.range f) = Bs) :
    ∀ b : ↥Bs, ∃ v : Fin 4 → ZMod 7, fPow f v = (b : G) := by
  have hle : Subgroup.closure (Set.range f) ≤ a11rf_fPowSubgroup f hcomm hord := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, a11rf_fPow_single f i⟩
  intro b
  have hb : (b : G) ∈ Subgroup.closure (Set.range f) := by
    rw [hBs]; exact b.2
  exact hle hb

private theorem a11rf_fPow_mem {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs) (v : Fin 4 → ZMod 7) : fPow f v ∈ Bs := by
  rw [← hBs]
  have h0 : f 0 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : f 1 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨1, rfl⟩
  have h2 : f 2 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨2, rfl⟩
  have h3 : f 3 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨3, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ h0 _) (Subgroup.pow_mem _ h1 _)) (Subgroup.pow_mem _ h2 _))
    (Subgroup.pow_mem _ h3 _)

private theorem a11rf_fPow_inj {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4) :
    Function.Injective (fPow f) := by
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  have hdom : Fintype.card (Fin 4 → ZMod 7) = 7 ^ 4 := by
    simp [Fintype.card_fun, ZMod.card]
  have hcod : Fintype.card ↥Bs = 7 ^ 4 := by
    rw [← Nat.card_eq_fintype_card, ← hBs]
    exact hcard
  let e : (Fin 4 → ZMod 7) ≃ ↥Bs := Fintype.equivOfCardEq (by rw [hdom, hcod])
  have hsurj : Function.Surjective (fun v => (⟨fPow f v, a11rf_fPow_mem hBs v⟩ : ↥Bs)) := by
    intro b
    obtain ⟨v, hv⟩ := a11rf_fPow_surj hcomm hord hBs b
    exact ⟨v, Subtype.ext hv⟩
  have hinj : Function.Injective (fun v => (⟨fPow f v, a11rf_fPow_mem hBs v⟩ : ↥Bs)) :=
    (Finite.injective_iff_surjective_of_equiv e).mpr hsurj
  intro u v huv
  exact hinj (Subtype.ext huv)

private theorem a11rf_conjMat_mul_self {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {f : Fin 4 → G} {h : G} {M : M4} {φ : MulAut ↥Bs}
    (hM : ConjMat f h M)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = h * b * h⁻¹)
    (hφ2 : φ ^ 2 = 1) :
    M * M = 1 := by
  have hinj := a11rf_fPow_inj hcomm hord hBs hcard
  have hcent : ∀ b : ↥Bs, h ^ 2 * (b : G) * (h ^ 2)⁻¹ = (b : G) := by
    intro b
    have hb2 : h * (h * (b : G) * h⁻¹) * h⁻¹ = (b : G) := by
      have h1 : (φ (φ b) : G) = (b : G) := by
        have := congrArg (fun ψ : MulAut ↥Bs => ((ψ b : ↥Bs) : G)) hφ2
        simpa [pow_two, MulAut.mul_apply] using this
      rwa [hφ (φ b), hφ b] at h1
    have h3 : h ^ 2 * (b : G) * (h ^ 2)⁻¹ = h * (h * (b : G) * h⁻¹) * h⁻¹ := by
      rw [pow_two]
      group
    rw [h3, hb2]
  have hvec : ∀ v, Matrix.vecMul (Matrix.vecMul v M) M = v := by
    intro v
    apply hinj
    have hb := hcent ⟨fPow f v, a11rf_fPow_mem hBs v⟩
    have h1 : fPow f (Matrix.vecMul (Matrix.vecMul v M) M) =
        h ^ 2 * fPow f v * (h ^ 2)⁻¹ := by
      rw [← hM (Matrix.vecMul v M), ← hM v]
      rw [pow_two]
      group
    rw [h1, hb]
  apply Matrix.ext
  intro i j
  have h := congrFun (hvec (Pi.single i 1)) j
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_apply] at h
  have hsum : (∑ k : Fin 4, (Pi.single i 1 : Fin 4 → ZMod 7) k * (M * M) k j) =
      (M * M) i j := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; rw [Pi.single_eq_of_ne hk]; simp
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp only [dotProduct, Matrix.col_apply] at h
  rw [hsum] at h
  by_cases hij : i = j
  · subst hij; simpa [Pi.single_eq_same, Matrix.one_apply] using h
  · have hji : j ≠ i := fun hh => hij hh.symm
    simpa [Pi.single_eq_of_ne hji, Matrix.one_apply, hij] using h

private theorem a11rf_fPow_ell {G : Type} [Group G] (f : Fin 4 → G) (c : ZMod 7) :
    fPow f ![1, 1, 1, c] = ell f c := by
  have h1 : (1 : ZMod 7).val = 1 := ZMod.val_one'' (by norm_num)
  simp [fPow, ell, h1]

private noncomputable def a11rf_fPowEquiv {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {f : Fin 4 → G}
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4) :
    (Fin 4 → ZMod 7) ≃ ↥Bs :=
  Equiv.ofBijective (fun v => (⟨fPow f v, a11rf_fPow_mem hBs v⟩ : ↥Bs))
    ⟨fun u v huv => a11rf_fPow_inj hcomm hord hBs hcard (Subtype.ext_iff.mp huv), by
      intro b
      obtain ⟨v, hv⟩ := a11rf_fPow_surj hcomm hord hBs b
      exact ⟨v, Subtype.ext hv⟩⟩

private theorem a11rf_conjMat_fix {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {f : Fin 4 → G} {h : G} {M : M4}
    (hM : ConjMat f h M)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    {y' : G} {c : ZMod 7} (hline : Subgroup.zpowers y' = Subgroup.zpowers (ell f c))
    (hhy' : h * y' * h⁻¹ = y') :
    Matrix.vecMul ![1, 1, 1, c] M = ![1, 1, 1, c] := by
  have hinj := a11rf_fPow_inj hcomm hord hBs hcard
  have hcomm_y' : Commute h y' := by
    show h * y' = y' * h
    calc h * y' = h * y' * h⁻¹ * h := by group
      _ = y' * h := by rw [hhy']
  have hell_zp : ell f c ∈ Subgroup.zpowers y' := by
    rw [hline]; exact Subgroup.mem_zpowers (ell f c)
  have hcomm_ell : h * ell f c = ell f c * h := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hell_zp
    rw [← hn]
    exact (hcomm_y'.zpow_right n).eq
  have hfix_ell : h * ell f c * h⁻¹ = ell f c := by
    rw [hcomm_ell]; group
  apply hinj
  rw [← hM ![1, 1, 1, c], a11rf_fPow_ell f c, hfix_ell]

private theorem a11rf_conjMat_fixed_card {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {f : Fin 4 → G} {h : G} {M : M4} {φ : MulAut ↥Bs}
    (hM : ConjMat f h M)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hord : ∀ i, orderOf (f i) = 7)
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = h * b * h⁻¹)
    (hfixcard : Nat.card {b : ↥Bs // φ b = b} = 7 ^ 3) :
    Nat.card {v : Fin 4 → ZMod 7 // Matrix.vecMul v M = v} = 7 ^ 3 := by
  have hinj := a11rf_fPow_inj hcomm hord hBs hcard
  have heq : {v : Fin 4 → ZMod 7 // Matrix.vecMul v M = v} ≃ {b : ↥Bs // φ b = b} :=
    Equiv.subtypeEquiv (a11rf_fPowEquiv hcomm hord hBs hcard) (fun v => by
      constructor
      · intro hv
        apply Subtype.ext
        rw [hφ (a11rf_fPowEquiv hcomm hord hBs hcard v)]
        change h * fPow f v * h⁻¹ = fPow f v
        rw [hM v, hv]
      · intro hv
        apply hinj
        have h1 : ((φ (a11rf_fPowEquiv hcomm hord hBs hcard v) : ↥Bs) : G) =
            (a11rf_fPowEquiv hcomm hord hBs hcard v : G) := congrArg (fun b : ↥Bs => (b : G)) hv
        rw [hφ (a11rf_fPowEquiv hcomm hord hBs hcard v)] at h1
        change h * fPow f v * h⁻¹ = fPow f v at h1
        rw [hM v] at h1
        exact h1)
  rwa [Nat.card_congr heq]

private theorem a11rf_fPow_one {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f ![1, 1, 1, 1] = f 0 * f 1 * f 2 * f 3 := by
  have h1 : (1 : ZMod 7).val = 1 := ZMod.val_one'' (by norm_num)
  simp [fPow, h1]

private theorem a11rf_rank_of_fix {M : M4} (hM : M * M = 1)
    (hfix : Nat.card {v : Fin 4 → ZMod 7 // Matrix.vecMul v M = v} = 7 ^ 3) :
    (M - 1).rank = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp2 : (2 : ZMod 7) ≠ 0 := by
    intro h
    have hdvd : 7 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 7).mp h
    norm_num at hdvd
  have hcard : Fintype.card (Fin 4) = 3 + 1 := by simp
  have hMT : Mᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have hfixT : Nat.card {v : Fin 4 → ZMod 7 // Mᵀ *ᵥ v = v} = 7 ^ 3 := by
    rw [← hfix]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun v => by rw [Matrix.mulVec_transpose])
  obtain ⟨h1, h2⟩ := CFSG.StandardType.finrank_ker_sub_one_add_one_eq_of_natCard_fixed
    hp2 Mᵀ hMT hcard hfixT
  have hV : Module.finrank (ZMod 7) (Fin 4 → ZMod 7) = Fintype.card (Fin 4) :=
    Module.finrank_fintype_fun_eq_card (R := ZMod 7) (η := Fin 4)
  have h1' : Module.finrank (ZMod 7) (LinearMap.ker (Mᵀ.mulVecLin - LinearMap.id)) = 3 := by
    simpa only [Module.End.one_eq_id] using h1
  have hrange : Module.finrank (ZMod 7) (LinearMap.range (Mᵀ.mulVecLin - LinearMap.id)) = 1 := by
    have hrn1 := LinearMap.finrank_range_add_finrank_ker (Mᵀ.mulVecLin - LinearMap.id)
    simp only [h1', hV, hcard] at hrn1
    omega
  have hmap : (Mᵀ - 1).mulVecLin = Mᵀ.mulVecLin - LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hrankT : (Mᵀ - 1).rank = 1 := by
    change Module.finrank (ZMod 7) (LinearMap.range ((Mᵀ - 1).mulVecLin)) = 1
    rw [hmap]
    exact hrange
  calc (M - 1).rank = ((M - 1)ᵀ).rank := (Matrix.rank_transpose (M - 1)).symm
    _ = (Mᵀ - 1).rank := by rw [Matrix.transpose_sub, Matrix.transpose_one]
    _ = 1 := hrankT

theorem a11ReflFixInput_holds : A11ReflFixInput := by
  intro hAM hLR hBF G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hrefl c hc hline g hgK hgN
  obtain ⟨A, hAnb, hAex, hAgen, hAunit, hAnt, hA89⟩ :=
    hAM G B Bs x L D J y K φ₃ f n Φ ρ hctx
  obtain ⟨hRest, hConfig, hFrameSpec, hFrameExtra, hCohSpec, hRhoSpec⟩ := hctx
  obtain ⟨hGlue, hφ₃K, hnbK, hBs, hx, hy, hD, hnL, hJK, hJ9, hLgen⟩ := hFrameSpec
  obtain ⟨hinjφ₃, hfT9, hfcomm, hford, hfcard, hn3, hnact, hcomp⟩ := hGlue
  have hxmem : x ∈ Bs := by
    rw [← hBs, hx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩))
      (Subgroup.subset_closure ⟨2, rfl⟩)) (Subgroup.subset_closure ⟨3, rfl⟩)
  let xb : ↥Bs := ⟨x, hxmem⟩
  let H : Subgroup (MulAut ↥Bs) := ggAutomizer K' Bs
  let stab : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | φ xb = xb}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        change (a * b) xb = xb
        rw [MulAut.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change a⁻¹ xb = xb
        have h := congrArg (fun z => (a⁻¹) z) ha
        simpa using h.symm }
  have hReflFixes : ∀ φ ∈ H, GGIsReflection 7 φ → φ xb = xb := by
    intro φ hφH hφrefl
    obtain ⟨h, hhK, hhN, hφ⟩ := mem_ggAutomizer_iff.mp hφH
    obtain ⟨M, hMA, hMconj⟩ := hAnb h hhN
    have hM2 : M * M = 1 :=
      a11rf_conjMat_mul_self hMconj hfcomm hford hBs hfcard hφ hφrefl.1
    have hhy' : h * y' * h⁻¹ = y' := by
      have hc := le_centralizer_of_nbr hnb hhK
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [hc]; group
    have hMfix : Matrix.vecMul ![1, 1, 1, c] M = ![1, 1, 1, c] :=
      a11rf_conjMat_fix hMconj hfcomm hford hBs hfcard hline hhy'
    have hfixcard : Nat.card {b : ↥Bs // φ b = b} = 7 ^ 3 := by
      have h1 := hφrefl.2
      have hBsCard : Nat.card ↥Bs = 7 ^ 4 := by rw [← hBs]; exact hfcard
      rw [hBsCard] at h1
      omega
    have hMrank : (M - 1).rank = 1 :=
      a11rf_rank_of_fix hM2
        (a11rf_conjMat_fixed_card hMconj hfcomm hford hBs hfcard hφ hfixcard)
    have hMcl : M ∈ Submonoid.closure G314gens :=
      hLR A hAgen hAunit hAnt hA89 M hMA hMrank
    have hbf := hBF c hc M hMcl hMrank hMfix
    have hMe : Matrix.vecMul ![1, 1, 1, 1] M = ![1, 1, 1, 1] := by
      rcases hbf with h | h | h | ⟨hc0, h | h⟩
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
      · exfalso; rw [h] at hM2; exact absurd hM2 (by decide)
      · exfalso; rw [h] at hM2; exact absurd hM2 (by decide)
    apply Subtype.ext
    have hxe : fPow f ![1, 1, 1, 1] = x := by rw [a11rf_fPow_one, ← hx]
    calc (φ xb : G) = h * (xb : G) * h⁻¹ := hφ xb
      _ = h * fPow f ![1, 1, 1, 1] * h⁻¹ := by rw [hxe]
      _ = fPow f (Matrix.vecMul ![1, 1, 1, 1] M) := hMconj ![1, 1, 1, 1]
      _ = fPow f ![1, 1, 1, 1] := by rw [hMe]
      _ = x := hxe
  have hHstab : H ≤ stab := by
    have hH : H = Subgroup.closure {φ | φ ∈ H ∧ GGIsReflection 7 φ} := hrefl
    rw [hH, Subgroup.closure_le]
    rintro φ ⟨hφH, hφrefl⟩
    exact hReflFixes φ hφH hφrefl
  have hgH : ggConjAut Bs hgN ∈ H := ggConjAut_mem_ggAutomizer hgK hgN
  have hfix : ggConjAut Bs hgN xb = xb := hHstab hgH
  have h := congrArg (fun b : ↥Bs => (b : G)) hfix
  rw [ggConjAut_apply] at h
  simpa using h

end CFSG.StandardType.A11

end
