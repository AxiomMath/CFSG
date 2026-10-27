module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGA11L89B
public import CFSG.LocalAnalysis.StandardType.GGA8NbrPlumb
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev four : Finset (Fin 4) := insert 0 (insert 1 (insert 2 ({3} : Finset (Fin 4))))

private theorem noncommProd_four {M : Type*} [Monoid M] (g : Fin 4 → M)
    (comm : Set.Pairwise (↑four : Set (Fin 4)) (Function.onFun Commute g)) :
    four.noncommProd g comm = g 0 * g 1 * g 2 * g 3 := by
  rw [Finset.noncommProd_insert_of_notMem (ha := by decide),
    Finset.noncommProd_insert_of_notMem (ha := by decide),
    Finset.noncommProd_insert_of_notMem (ha := by decide),
    Finset.noncommProd_singleton]
  simp only [mul_assoc]

private theorem pow_mod_seven {M : Type*} [Monoid M] {x : M} (hx : x ^ 7 = 1) (m : ℕ) :
    x ^ (m % 7) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 7, pow_add, pow_mul, hx, one_pow, mul_one]

private noncomputable def fcomm {G : Type} [Monoid G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (v : Fin 4 → ZMod 7) :
    Set.Pairwise (↑four : Set (Fin 4)) (Function.onFun Commute (fun i => f i ^ (v i).val)) :=
  fun i _ j _ _ => ((hfcomm i j).pow_left (v i).val).pow_right (v j).val

private theorem fPow_eq_noncomm {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (v : Fin 4 → ZMod 7) :
    fPow f v = four.noncommProd (fun i => f i ^ (v i).val) (fcomm f hfcomm v) := by
  rw [fPow]
  exact (noncommProd_four _ (fcomm f hfcomm v)).symm

private theorem fPow_mul {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (v w : Fin 4 → ZMod 7) :
    fPow f (v + w) = fPow f v * fPow f w := by
  rw [fPow_eq_noncomm f hfcomm (v + w), fPow_eq_noncomm f hfcomm v,
    fPow_eq_noncomm f hfcomm w]
  set g2 : Fin 4 → G := fun i => f i ^ (v i).val with hg2
  set g3 : Fin 4 → G := fun i => f i ^ (w i).val with hg3
  have cgf : (↑four : Set (Fin 4)).Pairwise fun x y => Commute (g3 x) (g2 y) :=
    fun i _ j _ _ => ((hfcomm i j).pow_left (w i).val).pow_right (v j).val
  have hcong : four.noncommProd (fun i => f i ^ ((v + w) i).val) (fcomm f hfcomm (v + w)) =
      four.noncommProd (g2 * g3) _ :=
    Finset.noncommProd_congr (s₁ := four) (s₂ := four)
      (f := fun i => f i ^ ((v + w) i).val) (g := g2 * g3)
      rfl (fun i _ => by
        rw [Pi.mul_apply, hg2, hg3]
        have hval : ((v + w) i).val = ((v i).val + (w i).val) % 7 := by
          rw [Pi.add_apply, ZMod.val_add]
        rw [hval, pow_mod_seven (hf7 i), pow_add])
      (fcomm f hfcomm (v + w))
  rw [hcong]
  rw [Finset.noncommProd_mul_distrib g2 g3 (fcomm f hfcomm v) (fcomm f hfcomm w) cgf]

private theorem fPow_zero {G : Type} [Group G] (f : Fin 4 → G) : fPow f 0 = 1 := by
  simp [fPow]

private theorem fPow_nsmul {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (n : ℕ) (w : Fin 4 → ZMod 7) :
    fPow f (n • w) = fPow f w ^ n := by
  induction n with
  | zero => simp [fPow_zero]
  | succ n ih =>
      rw [succ_nsmul, fPow_mul f hfcomm hf7, ih, pow_succ]

private theorem fPow_linear {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (w : Fin 4 → (Fin 4 → ZMod 7)) (n : Fin 4 → ℕ) :
    fPow f (∑ i, n i • w i) = (fPow f (w 0)) ^ (n 0) * (fPow f (w 1)) ^ (n 1) *
      (fPow f (w 2)) ^ (n 2) * (fPow f (w 3)) ^ (n 3) := by
  rw [Fin.sum_univ_four]
  rw [fPow_mul f hfcomm hf7, fPow_mul f hfcomm hf7, fPow_mul f hfcomm hf7,
    fPow_nsmul f hfcomm hf7, fPow_nsmul f hfcomm hf7, fPow_nsmul f hfcomm hf7,
    fPow_nsmul f hfcomm hf7]

private theorem ConjMat_of_basis {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (h : G) (M : Certificates.A8Nbr476.M4)
    (hM : ∀ i, h * f i * h⁻¹ = fPow f (fun j => M i j)) (v : Fin 4 → ZMod 7) :
    h * fPow f v * h⁻¹ = fPow f (v ᵥ* M) := by
  have hvec : v ᵥ* M = ∑ i, (v i).val • (fun j => M i j) := by
    rw [Matrix.vecMul_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [hvec, fPow_linear f hfcomm hf7]
  rw [show h * fPow f v * h⁻¹ = MulAut.conj h (fPow f v) from rfl]
  rw [fPow]
  simp only [map_mul, map_pow, MulAut.conj_apply]
  rw [hM 0, hM 1, hM 2, hM 3]

private theorem fPow_neg {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (v : Fin 4 → ZMod 7) :
    fPow f (-v) = (fPow f v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← fPow_mul f hfcomm hf7, neg_add_cancel, fPow_zero]

private theorem fPow_single {G : Type} [Group G] (f : Fin 4 → G) (i : Fin 4) :
    fPow f (Pi.single i 1) = f i := by
  fin_cases i <;> simp [fPow, show (1 : ZMod 7).val = 1 from by decide]

private theorem fPow_mem {G : Type} [Group G] (f : Fin 4 → G) (v : Fin 4 → ZMod 7) :
    fPow f v ∈ Subgroup.closure (Set.range f) := by
  rw [fPow]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))) _
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4))) _
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))) _
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))) _

private noncomputable def fPowSub {G : Type} [Group G] (f : Fin 4 → G)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) : Subgroup G where
  carrier := Set.range (fPow f)
  one_mem' := ⟨0, fPow_zero f⟩
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, fPow_mul f hfcomm hf7 v w⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨-v, fPow_neg f hfcomm hf7 v⟩

private theorem fPow_surj {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) :
    ∀ b ∈ Bs, ∃ v, fPow f v = b := by
  intro b hb
  have hle : Subgroup.closure (Set.range f) ≤ fPowSub f hfcomm hf7 :=
    (Subgroup.closure_le (fPowSub f hfcomm hf7)).2 (by
      rintro _ ⟨i, rfl⟩
      exact ⟨Pi.single i 1, fPow_single f i⟩)
  have hmem : b ∈ fPowSub f hfcomm hf7 := hle (hBs ▸ hb)
  exact hmem

private theorem fPow_inj {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) :
    Function.Injective (fPow f) := by
  let g : (Fin 4 → ZMod 7) → ↥Bs := fun v => ⟨fPow f v, hBs ▸ fPow_mem f v⟩
  have hsurjg : Function.Surjective g := by
    intro b
    obtain ⟨v, hv⟩ := fPow_surj hBs hfcomm hf7 b.1 b.2
    exact ⟨v, Subtype.ext hv⟩
  have hcardg : Nat.card (Fin 4 → ZMod 7) = Nat.card ↥Bs := by
    have h1 : Nat.card (Fin 4 → ZMod 7) = 7 ^ 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have h2 : Nat.card ↥Bs = 7 ^ 4 := by
      rw [← hBs]; exact hcard
    rw [h1, h2]
  have hbij : Function.Bijective g :=
    (Nat.bijective_iff_surjective_and_card g).mpr ⟨hsurjg, hcardg⟩
  intro v w hvw
  exact hbij.1 (Subtype.ext hvw)

private theorem row_eq_vecMul_ev (M : Certificates.A8Nbr476.M4) (j k : Fin 4) :
    M j k = (Matrix.vecMul (ev j) M) k := by
  rw [Matrix.vecMul_apply, ev, single_dotProduct, one_mul]
  rfl

private noncomputable def fPowAddHom {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) :
    (Fin 4 → ZMod 7) →+ Additive ↥Bs where
  toFun v := Additive.ofMul ⟨fPow f v, hBs ▸ fPow_mem f v⟩
  map_zero' := by
    change Additive.ofMul ⟨fPow f 0, _⟩ = Additive.ofMul (1 : ↥Bs)
    congr 1
    apply Subtype.ext
    exact fPow_zero f
  map_add' v w := by
    rw [← ofMul_mul]
    congr 1
    apply Subtype.ext
    exact fPow_mul f hfcomm hf7 v w

private theorem fPowAddHom_inj {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) :
    Function.Injective (fPowAddHom hBs hfcomm hf7) := by
  intro v w h
  apply fPow_inj hBs hcard hfcomm hf7
  have hh := congrArg (fun x : Additive ↥Bs => ((Additive.toMul x : ↥Bs) : G)) h
  simpa [fPowAddHom] using hh

private theorem fPowAddHom_surj {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) :
    Function.Surjective (fPowAddHom hBs hfcomm hf7) := by
  intro x
  obtain ⟨v, hv⟩ := fPow_surj hBs hfcomm hf7 (Additive.toMul x).1 (Additive.toMul x).2
  refine ⟨v, ?_⟩
  apply Additive.ofMul.injective
  exact Subtype.ext hv

private noncomputable def fPowEquiv {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1) :
    Additive ↥Bs ≃+ (Fin 4 → ZMod 7) :=
  (AddEquiv.ofBijective (fPowAddHom hBs hfcomm hf7)
    ⟨fPowAddHom_inj hBs hcard hfcomm hf7, fPowAddHom_surj hBs hfcomm hf7⟩).symm

private theorem fPowEquiv_apply {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (v : Fin 4 → ZMod 7) :
    fPowEquiv hBs hcard hfcomm hf7 (Additive.ofMul ⟨fPow f v, hBs ▸ fPow_mem f v⟩) = v := by
  rw [fPowEquiv]
  exact AddEquiv.symm_apply_apply _ v

private theorem no_transv {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    (hNT : GGNoTransvection 7 Bs)
    {t : Certificates.A8Nbr476.M4} {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) (hcg : ConjMat f g t)
    (ht : Certificates.A8Nbr476.IsTransv t) : False := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let ι := fPowEquiv hBs hcard hfcomm hf7
  let φ : MulAut ↥Bs := ggConjAut Bs hgN
  have hφ : φ ∈ ggInduced ⊤ Bs := ggConjAut_mem_ggInduced (Subgroup.mem_top g) hgN
  have hlin : ∀ v : Fin 4 → ZMod 7, ggLin (p := 7) ι φ v = Matrix.vecMul v t := by
    intro v
    have e1 : ι (Additive.ofMul (⟨fPow f v, hBs ▸ fPow_mem f v⟩ : ↥Bs)) = v :=
      fPowEquiv_apply hBs hcard hfcomm hf7 v
    conv_lhs => rw [← e1]
    rw [ggLin_apply_ofMul]
    have e2 : φ ⟨fPow f v, hBs ▸ fPow_mem f v⟩ =
        ⟨fPow f (Matrix.vecMul v t), hBs ▸ fPow_mem f (Matrix.vecMul v t)⟩ := by
      apply Subtype.ext
      change ((ggConjAut Bs hgN ⟨fPow f v, _⟩ : ↥Bs) : G) = fPow f (Matrix.vecMul v t)
      rw [ggConjAut_apply]
      exact hcg v
    rw [e2, fPowEquiv_apply]
  obtain ⟨u, w, hu, hw, hwu, hvec⟩ := ggIsTransv_exists_lin ht
  let f' : Module.Dual (ZMod 7) (Fin 4 → ZMod 7) :=
    { toFun := fun v => v ⬝ᵥ u
      map_add' := fun a b => add_dotProduct a b u
      map_smul' := fun c v => by rw [smul_dotProduct]; rfl }
  have hf0 : f' ≠ 0 := by
    intro hf
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    have h1 := LinearMap.congr_fun hf (Pi.single i 1)
    apply hi
    simpa [f', dotProduct, Pi.single_apply] using h1
  have hfw : f' w = 0 := hwu
  have hform : ∀ v, ggLin (p := 7) ι φ v = v + f' v • w := by
    intro v
    rw [hlin v, hvec v]
    rfl
  exact hNT φ hφ (ggIsTransvection_of_apply (p := 7) ι hw hf0 hfw hform)

noncomputable section

private instance : Fintype F2 := Fintype.ofFinite F2

private lemma a11am_cardF2 : Fintype.card F2 = 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by omega)]
  norm_num

private def a11am_e2 : ZMod 2 ≃+* F2 :=
  FiniteField.ringEquivOfCardEq (K := ZMod 2) (K' := F2) (by rw [a11am_cardF2]; decide)

private def a11am_OmZ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0,0,1;1,0,1;0,1,0]

private lemma a11am_e2_Om (i j : Fin 3) : a11am_e2 (a11am_OmZ i j) = Om i j := by
  fin_cases i <;> fin_cases j <;> simp [a11am_OmZ, Om, a11am_e2, map_zero, map_one]

private def a11am_blk9 : Fin 9 → Fin 4 := ![1,1,1,0,2,2,2,0,0]
private def a11am_idxIn9 : Fin 9 → Fin 3 := ![0,1,2,0,0,1,2,1,2]

private lemma a11am_blk_castLE (h : 9 ≤ 12) (a : Fin 9) : blk (Fin.castLE h a) = a11am_blk9 a := by
  fin_cases a <;> rfl

private lemma a11am_idxIn_castLE (h : 9 ≤ 12) (a : Fin 9) : idxIn (Fin.castLE h a) = a11am_idxIn9 a := by
  fin_cases a <;> rfl

private lemma a11am_T9mat_eq (i : Fin 3) :
    T9mat i = Matrix.of (fun a b =>
      if a11am_blk9 a = (i.castSucc : Fin 4) ∧ a11am_blk9 b = i.castSucc then Om (a11am_idxIn9 a) (a11am_idxIn9 b)
      else if a = b then 1 else 0) := by
  ext a b
  simp [T9mat, a11am_blk_castLE, a11am_idxIn_castLE]

private def a11am_T9matZ (i : Fin 3) : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  Matrix.of fun a b =>
    if a11am_blk9 a = (i.castSucc : Fin 4) ∧ a11am_blk9 b = i.castSucc
    then a11am_OmZ (a11am_idxIn9 a) (a11am_idxIn9 b)
    else if a = b then 1 else 0

private lemma a11am_T9mat_bridge (i : Fin 3) : a11am_e2.mapMatrix (a11am_T9matZ i) = T9mat i := by
  rw [a11am_T9mat_eq]
  ext a b
  by_cases h1 : a11am_blk9 a = (i.castSucc : Fin 4) <;>
  by_cases h2 : a11am_blk9 b = i.castSucc <;>
  by_cases hab : a = b <;>
  simp [a11am_T9matZ, h1, h2, hab, a11am_e2_Om, map_zero, map_one]

private def a11am_FrZ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1,0,0;0,0,1;0,1,1]

private def a11am_F0matZ : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  Matrix.of fun a b =>
    if a11am_blk9 a = (0 : Fin 4) ∧ a11am_blk9 b = 0
    then a11am_FrZ (a11am_idxIn9 a) (a11am_idxIn9 b)
    else if a = b then 1 else 0

private lemma a11am_F0matZ_mul_T9Z0 :
    a11am_F0matZ * a11am_T9matZ 0 = a11am_T9matZ 0 ^ 2 * a11am_F0matZ := by decide

private lemma a11am_F0matZ_comm_T9Z1 :
    a11am_F0matZ * a11am_T9matZ 1 = a11am_T9matZ 1 * a11am_F0matZ := by decide

private lemma a11am_F0matZ_comm_T9Z2 :
    a11am_F0matZ * a11am_T9matZ 2 = a11am_T9matZ 2 * a11am_F0matZ := by decide

private lemma a11am_F0matZ_pow_three : a11am_F0matZ ^ 3 = 1 := by decide

private lemma a11am_F0matZ_det : a11am_F0matZ.det = 1 := by
  have h : (a11am_F0matZ.det) ^ 3 = 1 := by
    rw [← Matrix.det_pow, a11am_F0matZ_pow_three, Matrix.det_one]
  have hx : ∀ x : ZMod 2, x ^ 3 = x := by decide
  rw [hx] at h
  exact h

private def a11am_F0mat : Matrix (Fin 9) (Fin 9) F2 := a11am_e2.mapMatrix a11am_F0matZ

private lemma a11am_F0mat_mul_T9mat0 :
    a11am_F0mat * T9mat 0 = T9mat 0 ^ 2 * a11am_F0mat := by
  have h := congrArg a11am_e2.mapMatrix a11am_F0matZ_mul_T9Z0
  rw [map_mul, map_mul, map_pow, a11am_T9mat_bridge] at h
  exact h

private lemma a11am_F0mat_comm_T9mat1 :
    a11am_F0mat * T9mat 1 = T9mat 1 * a11am_F0mat := by
  have h := congrArg a11am_e2.mapMatrix a11am_F0matZ_comm_T9Z1
  rw [map_mul, map_mul, a11am_T9mat_bridge] at h
  exact h

private lemma a11am_F0mat_comm_T9mat2 :
    a11am_F0mat * T9mat 2 = T9mat 2 * a11am_F0mat := by
  have h := congrArg a11am_e2.mapMatrix a11am_F0matZ_comm_T9Z2
  rw [map_mul, map_mul, a11am_T9mat_bridge] at h
  exact h

private lemma a11am_F0mat_det : a11am_F0mat.det = 1 := by
  have h := RingHom.map_det a11am_e2.toRingHom a11am_F0matZ
  rw [a11am_F0matZ_det, map_one] at h
  simpa [a11am_F0mat] using h.symm

private def a11am_F0 : SL 9 := ⟨a11am_F0mat, a11am_F0mat_det⟩

private lemma a11am_F0_mul_T9_0 : a11am_F0 * T9 0 = T9 0 ^ 2 * a11am_F0 := by
  apply Subtype.ext
  change a11am_F0mat * T9mat 0 = T9mat 0 ^ 2 * a11am_F0mat
  exact a11am_F0mat_mul_T9mat0

private lemma a11am_F0_comm_T9_1 : a11am_F0 * T9 1 = T9 1 * a11am_F0 := by
  apply Subtype.ext
  change a11am_F0mat * T9mat 1 = T9mat 1 * a11am_F0mat
  exact a11am_F0mat_comm_T9mat1

private lemma a11am_F0_comm_T9_2 : a11am_F0 * T9 2 = T9 2 * a11am_F0 := by
  apply Subtype.ext
  change a11am_F0mat * T9mat 2 = T9mat 2 * a11am_F0mat
  exact a11am_F0mat_comm_T9mat2

private lemma a11am_F0mat_pow_three : a11am_F0mat ^ 3 = 1 := by
  have h := congrArg a11am_e2.mapMatrix a11am_F0matZ_pow_three
  rw [map_pow, map_one] at h
  exact h

private lemma a11am_F0_pow_three : a11am_F0 ^ 3 = 1 := by
  apply Subtype.ext
  change a11am_F0mat ^ 3 = 1
  exact a11am_F0mat_pow_three

private lemma a11am_F0_inv_eq : a11am_F0⁻¹ = a11am_F0 ^ 2 := by
  have h : a11am_F0 ^ 2 * a11am_F0 = 1 := by
    rw [← pow_succ, a11am_F0_pow_three]
  have h2 : a11am_F0 ^ 2 = a11am_F0⁻¹ := eq_inv_of_mul_eq_one_left h
  exact h2.symm

private lemma a11am_F0_conj_T9_0 : a11am_F0 * T9 0 * a11am_F0⁻¹ = T9 0 ^ 2 := by
  have h := a11am_F0_mul_T9_0
  rw [h]; group

private lemma a11am_F0_inv_conj_T9_0 : a11am_F0⁻¹ * T9 0 * a11am_F0 = T9 0 ^ 4 := by
  rw [a11am_F0_inv_eq]
  calc a11am_F0 ^ 2 * T9 0 * a11am_F0
      = a11am_F0 * (a11am_F0 * T9 0 * a11am_F0⁻¹) * a11am_F0 ^ 2 := by simp only [pow_two]; group
    _ = a11am_F0 * T9 0 ^ 2 * a11am_F0 ^ 2 := by rw [a11am_F0_conj_T9_0]
    _ = a11am_F0 * T9 0 ^ 2 * a11am_F0⁻¹ := by rw [← a11am_F0_inv_eq]
    _ = (a11am_F0 * T9 0 * a11am_F0⁻¹) ^ 2 := by simp only [pow_two]; group
    _ = (T9 0 ^ 2) ^ 2 := by rw [a11am_F0_conj_T9_0]
    _ = T9 0 ^ 4 := by group

private lemma a11am_F0_conj_T9_1 : a11am_F0 * T9 1 * a11am_F0⁻¹ = T9 1 := by
  rw [a11am_F0_comm_T9_1]; group

private lemma a11am_F0_conj_T9_2 : a11am_F0 * T9 2 * a11am_F0⁻¹ = T9 2 := by
  rw [a11am_F0_comm_T9_2]; group

private lemma a11am_F0_inv_conj_T9_1 : a11am_F0⁻¹ * T9 1 * a11am_F0 = T9 1 := by
  rw [a11am_F0_inv_eq]
  calc a11am_F0 ^ 2 * T9 1 * a11am_F0
      = a11am_F0 * (a11am_F0 * T9 1 * a11am_F0⁻¹) * a11am_F0 ^ 2 := by simp only [pow_two]; group
    _ = a11am_F0 * T9 1 * a11am_F0 ^ 2 := by rw [a11am_F0_conj_T9_1]
    _ = a11am_F0 * T9 1 * a11am_F0⁻¹ := by rw [← a11am_F0_inv_eq]
    _ = T9 1 := a11am_F0_conj_T9_1

private lemma a11am_F0_inv_conj_T9_2 : a11am_F0⁻¹ * T9 2 * a11am_F0 = T9 2 := by
  rw [a11am_F0_inv_eq]
  calc a11am_F0 ^ 2 * T9 2 * a11am_F0
      = a11am_F0 * (a11am_F0 * T9 2 * a11am_F0⁻¹) * a11am_F0 ^ 2 := by simp only [pow_two]; group
    _ = a11am_F0 * T9 2 * a11am_F0 ^ 2 := by rw [a11am_F0_conj_T9_2]
    _ = a11am_F0 * T9 2 * a11am_F0⁻¹ := by rw [← a11am_F0_inv_eq]
    _ = T9 2 := a11am_F0_conj_T9_2

end

private def permMat (σ : Equiv.Perm (Fin 4)) : Certificates.A8Nbr476.M4 :=
  fun i j => if σ i = j then 1 else 0

private theorem conjMat_perm {G : Type} [Group G] {f : Fin 4 → G}
    (hfcomm : ∀ i j, Commute (f i) (f j)) (hf7 : ∀ i, f i ^ 7 = 1)
    {g : G} {σ : Equiv.Perm (Fin 4)} (hσ : ∀ i, g * f i * g⁻¹ = f (σ i)) :
    ConjMat f g (permMat σ) := by
  apply ConjMat_of_basis f hfcomm hf7 g
  intro i
  have hrow : (fun j => permMat σ i j) = Pi.single (σ i) 1 := by
    ext j
    simp [permMat, Pi.single_apply, eq_comm]
  rw [hrow, fPow_single, hσ i]

private lemma permMat_01 :
    permMat (Equiv.swap (0 : Fin 4) 1) = !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1] := by decide

private lemma permMat_12 :
    permMat (Equiv.swap (1 : Fin 4) 2) = !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] := by decide

private lemma permMat_23 :
    permMat (Equiv.swap (2 : Fin 4) 3) = !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0] := by decide

private theorem mem_normalizer_of_generators {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs) {h : G}
    (hh : ∀ i, h * f i * h⁻¹ ∈ Bs) (hh' : ∀ i, h⁻¹ * f i * h ∈ Bs) :
    h ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have hle : Subgroup.closure (Set.range f) ≤
        Subgroup.comap (MulAut.conj h).toMonoidHom Bs := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_comap.mpr (by simpa [MulAut.conj_apply] using hh i)
    have hx := hle (hBs ▸ hb)
    have hx2 := Subgroup.mem_comap.mp hx
    simpa [MulAut.conj_apply] using hx2
  · intro hb
    have hle : Subgroup.closure (Set.range f) ≤
        Subgroup.comap (MulAut.conj h⁻¹).toMonoidHom Bs := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_comap.mpr (by simpa [MulAut.conj_apply] using hh' i)
    have hx := hle (hBs ▸ hb)
    have hx2 := Subgroup.mem_comap.mp hx
    have hb' : h⁻¹ * (h * b * h⁻¹) * h ∈ Bs := by simpa [MulAut.conj_apply] using hx2
    simpa [show h⁻¹ * (h * b * h⁻¹) * h = b by group] using hb'

private def a11am_D0 : Certificates.A8Nbr476.M4 := !![2,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]

private lemma a11am_D0_row0 : (fun j => a11am_D0 0 j) = (2 : ℕ) • ev 0 := by
  ext j; fin_cases j <;> simp [a11am_D0, ev, Pi.single_apply]

private lemma a11am_D0_row1 : (fun j => a11am_D0 1 j) = ev 1 := by
  ext j; fin_cases j <;> simp [a11am_D0, ev, Pi.single_apply]

private lemma a11am_D0_row2 : (fun j => a11am_D0 2 j) = ev 2 := by
  ext j; fin_cases j <;> simp [a11am_D0, ev, Pi.single_apply]

private lemma a11am_D0_row3 : (fun j => a11am_D0 3 j) = ev 3 := by
  ext j; fin_cases j <;> simp [a11am_D0, ev, Pi.single_apply]

theorem a11AMatInput_holds : A11AMatInput := by
  intro G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx
  classical
  obtain ⟨hGlue, hKrange, hnb, hBs, hx, hy, hD, hnL, hJK, hJ9, hLcl⟩ := hctx.2.2.1
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => hGlue.2.2.1 i j
  have hf7 : ∀ i, f i ^ 7 = 1 := fun i => by
    rw [← hGlue.2.2.2.1 i]; exact pow_orderOf_eq_one (f i)
  have hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4 := hGlue.2.2.2.2.1
  have hExtra : A11FrameExtra Bs J f := hctx.2.2.2.1
  have hNT : GGNoTransvection 7 Bs := hctx.1.2.2.2.1
  have hfi : ∀ i, f i ∈ Bs := fun i => hBs ▸ Subgroup.subset_closure (Set.mem_range_self i)
  let N : Subgroup G := Subgroup.normalizer (Bs : Set G)
  let A : Submonoid Certificates.A8Nbr476.M4 :=
    { carrier := {M | ∃ h ∈ N, ConjMat f h M}
      mul_mem' := by
        rintro M₁ M₂ ⟨h₁, hh₁, hc₁⟩ ⟨h₂, hh₂, hc₂⟩
        refine ⟨h₂ * h₁, N.mul_mem hh₂ hh₁, fun v => ?_⟩
        show (h₂ * h₁) * fPow f v * (h₂ * h₁)⁻¹ = fPow f (Matrix.vecMul v (M₁ * M₂))
        have e1 : (h₂ * h₁) * fPow f v * (h₂ * h₁)⁻¹ =
            h₂ * (h₁ * fPow f v * h₁⁻¹) * h₂⁻¹ := by group
        rw [e1, hc₁ v, hc₂ (Matrix.vecMul v M₁), Matrix.vecMul_vecMul]
      one_mem' := ⟨1, N.one_mem, by
        intro v
        show (1 : G) * fPow f v * (1 : G)⁻¹ = fPow f (Matrix.vecMul v 1)
        simp [Matrix.vecMul_one]⟩ }
  have hex : ∀ h ∈ N, ∃ M ∈ A, ConjMat f h M := by
    intro h hh
    have hcm : ∀ i, h * f i * h⁻¹ ∈ Bs := fun i =>
      (Subgroup.mem_normalizer_iff.mp hh (f i)).mp (hfi i)
    let vv : Fin 4 → (Fin 4 → ZMod 7) := fun i =>
      Classical.choose (fPow_surj hBs hfcomm hf7 (h * f i * h⁻¹) (hcm i))
    have hvv : ∀ i, fPow f (vv i) = h * f i * h⁻¹ := fun i =>
      Classical.choose_spec (fPow_surj hBs hfcomm hf7 (h * f i * h⁻¹) (hcm i))
    let M : Certificates.A8Nbr476.M4 := fun i j => vv i j
    have hM : ∀ i, h * f i * h⁻¹ = fPow f (fun j => M i j) := fun i => (hvv i).symm
    exact ⟨M, ⟨h, hh, ConjMat_of_basis f hfcomm hf7 h M hM⟩,
      ConjMat_of_basis f hfcomm hf7 h M hM⟩
  have hinj := fPow_inj hBs hcard hfcomm hf7
  have hinv : ∀ a ∈ A, IsUnit a.det ∧ a⁻¹ ∈ A := by
    intro a ha
    obtain ⟨h, hh, hc⟩ := ha
    obtain ⟨a', ha', hca'⟩ := hex h⁻¹ (N.inv_mem hh)
    have h1 : ∀ v, fPow f (Matrix.vecMul v (a * a')) = fPow f v := by
      intro v
      rw [← Matrix.vecMul_vecMul]
      have e1 := hca' (Matrix.vecMul v a)
      have e2 := hc v
      rw [← e1, ← e2]
      group
    have hmul : a * a' = 1 := by
      ext j k
      have hv : Matrix.vecMul (ev j) (a * a') = ev j := hinj (h1 (ev j))
      rw [row_eq_vecMul_ev (a * a') j k, hv]
      simp [ev, Pi.single_apply, Matrix.one_apply, eq_comm]
    have h1' : ∀ v, fPow f (Matrix.vecMul v (a' * a)) = fPow f v := by
      intro v
      rw [← Matrix.vecMul_vecMul]
      have e1 := hc (Matrix.vecMul v a')
      have e2 := hca' v
      rw [← e1, ← e2]
      group
    have hmul' : a' * a = 1 := by
      ext j k
      have hv : Matrix.vecMul (ev j) (a' * a) = ev j := hinj (h1' (ev j))
      rw [row_eq_vecMul_ev (a' * a) j k, hv]
      simp [ev, Pi.single_apply, Matrix.one_apply, eq_comm]
    have hainv : a⁻¹ = a' := Matrix.inv_eq_right_inv hmul
    refine ⟨?_, ?_⟩
    · exact Matrix.isUnit_det_of_right_inverse hmul
    · rw [hainv]; exact ha'
  have hgood : ∀ a ∈ A, ∀ j : Fin 4, Matrix.vecMul (ev j) a = ev j → Good9B j a := by
    intro a ha j hfix
    obtain ⟨g, hgN, hcg⟩ := ha
    have hgf : g * f j * g⁻¹ = f j := by
      have h := hcg (ev j)
      rw [hfix] at h
      simp only [ev, fPow_single] at h
      exact h
    exact a11Lemma89BInput_holds G B Bs x L D J y K φ₃ f n Φ ρ hctx g j hgN hgf a hcg
  refine ⟨A, ?_, ?_, ?_, hinv, ?_, hgood⟩
  · exact hex
  · intro M hM; exact hM
  · intro M hM
    simp only [G314gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with hM | hM | hM | hM
    · rw [hM]
      obtain ⟨g, hgJ, hgN, hgperm⟩ := hExtra.2 (Equiv.swap (0 : Fin 4) 1) (by decide)
      refine ⟨g, hgN, ?_⟩
      rw [← permMat_01]
      exact conjMat_perm hfcomm hf7 hgperm
    · rw [hM]
      obtain ⟨g, hgJ, hgN, hgperm⟩ := hExtra.2 (Equiv.swap (1 : Fin 4) 2) (by decide)
      refine ⟨g, hgN, ?_⟩
      rw [← permMat_12]
      exact conjMat_perm hfcomm hf7 hgperm
    · rw [hM]
      have hn2N : n 2 ∈ N := by
        apply mem_normalizer_of_generators hBs
        · intro i
          rw [hGlue.2.2.2.2.2.2.1 2 i]
          exact hfi _
        · intro i
          have h := hGlue.2.2.2.2.2.2.1 2 (Equiv.swap (2 : Fin 4) 3 i)
          have h' : n 2 * f (Equiv.swap (2 : Fin 4) 3 i) * (n 2)⁻¹ = f i := by
            simpa using h
          have h2 : (n 2)⁻¹ * f i * n 2 = f (Equiv.swap (2 : Fin 4) 3 i) := by
            rw [← h']; group
          rw [h2]
          exact hfi _
      refine ⟨n 2, hn2N, ?_⟩
      rw [← permMat_23]
      apply conjMat_perm hfcomm hf7
      intro i
      exact hGlue.2.2.2.2.2.2.1 2 i
    · rw [hM]
      change a11am_D0 ∈ A
      have hKcent : φ₃.range ≤ Subgroup.centralizer ({f 3} : Set G) := hGlue.2.2.2.2.2.2.2.1
      have hfφ0 : f 0 = φ₃ (T9 0) := by simpa using hGlue.2.1 (0 : Fin 3)
      have hfφ1 : f 1 = φ₃ (T9 1) := by simpa using hGlue.2.1 (1 : Fin 3)
      have hfφ2 : f 2 = φ₃ (T9 2) := by simpa using hGlue.2.1 (2 : Fin 3)
      have hc0 : φ₃ a11am_F0 * f 0 * (φ₃ a11am_F0)⁻¹ = f 0 ^ 2 := by
        rw [hfφ0]
        have e : φ₃ (a11am_F0 * T9 0 * a11am_F0⁻¹) = φ₃ a11am_F0 * φ₃ (T9 0) * (φ₃ a11am_F0)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [← e, a11am_F0_conj_T9_0, map_pow]
      have hc1 : φ₃ a11am_F0 * f 1 * (φ₃ a11am_F0)⁻¹ = f 1 := by
        rw [hfφ1]
        have e : φ₃ (a11am_F0 * T9 1 * a11am_F0⁻¹) = φ₃ a11am_F0 * φ₃ (T9 1) * (φ₃ a11am_F0)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [← e, a11am_F0_conj_T9_1]
      have hc2 : φ₃ a11am_F0 * f 2 * (φ₃ a11am_F0)⁻¹ = f 2 := by
        rw [hfφ2]
        have e : φ₃ (a11am_F0 * T9 2 * a11am_F0⁻¹) = φ₃ a11am_F0 * φ₃ (T9 2) * (φ₃ a11am_F0)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [← e, a11am_F0_conj_T9_2]
      have hc3 : φ₃ a11am_F0 * f 3 * (φ₃ a11am_F0)⁻¹ = f 3 := by
        have hmem : φ₃ a11am_F0 ∈ Subgroup.centralizer ({f 3} : Set G) := hKcent ⟨a11am_F0, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hmem
        rw [hmem]; group
      have hc0' : (φ₃ a11am_F0)⁻¹ * f 0 * (φ₃ a11am_F0) = f 0 ^ 4 := by
        rw [hfφ0]
        have e : φ₃ (a11am_F0⁻¹ * T9 0 * a11am_F0) = (φ₃ a11am_F0)⁻¹ * φ₃ (T9 0) * φ₃ a11am_F0 := by
          rw [map_mul, map_mul, map_inv]
        rw [← e, a11am_F0_inv_conj_T9_0, map_pow]
      have hc1' : (φ₃ a11am_F0)⁻¹ * f 1 * (φ₃ a11am_F0) = f 1 := by
        rw [hfφ1]
        have e : φ₃ (a11am_F0⁻¹ * T9 1 * a11am_F0) = (φ₃ a11am_F0)⁻¹ * φ₃ (T9 1) * φ₃ a11am_F0 := by
          rw [map_mul, map_mul, map_inv]
        rw [← e, a11am_F0_inv_conj_T9_1]
      have hc2' : (φ₃ a11am_F0)⁻¹ * f 2 * (φ₃ a11am_F0) = f 2 := by
        rw [hfφ2]
        have e : φ₃ (a11am_F0⁻¹ * T9 2 * a11am_F0) = (φ₃ a11am_F0)⁻¹ * φ₃ (T9 2) * φ₃ a11am_F0 := by
          rw [map_mul, map_mul, map_inv]
        rw [← e, a11am_F0_inv_conj_T9_2]
      have hc3' : (φ₃ a11am_F0)⁻¹ * f 3 * (φ₃ a11am_F0) = f 3 := by
        have hmem : φ₃ a11am_F0 ∈ Subgroup.centralizer ({f 3} : Set G) := hKcent ⟨a11am_F0, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hmem
        rw [show (φ₃ a11am_F0)⁻¹ * f 3 * (φ₃ a11am_F0) =
          (φ₃ a11am_F0)⁻¹ * (f 3 * φ₃ a11am_F0) by group, ← hmem]
        group
      have hF0N : φ₃ a11am_F0 ∈ N := by
        apply mem_normalizer_of_generators hBs
        · intro i
          fin_cases i
          · change φ₃ a11am_F0 * f 0 * (φ₃ a11am_F0)⁻¹ ∈ Bs
            rw [hc0]; exact Subgroup.pow_mem _ (hfi 0) 2
          · change φ₃ a11am_F0 * f 1 * (φ₃ a11am_F0)⁻¹ ∈ Bs
            rw [hc1]; exact hfi 1
          · change φ₃ a11am_F0 * f 2 * (φ₃ a11am_F0)⁻¹ ∈ Bs
            rw [hc2]; exact hfi 2
          · change φ₃ a11am_F0 * f 3 * (φ₃ a11am_F0)⁻¹ ∈ Bs
            rw [hc3]; exact hfi 3
        · intro i
          fin_cases i
          · change (φ₃ a11am_F0)⁻¹ * f 0 * φ₃ a11am_F0 ∈ Bs
            rw [hc0']; exact Subgroup.pow_mem _ (hfi 0) 4
          · change (φ₃ a11am_F0)⁻¹ * f 1 * φ₃ a11am_F0 ∈ Bs
            rw [hc1']; exact hfi 1
          · change (φ₃ a11am_F0)⁻¹ * f 2 * φ₃ a11am_F0 ∈ Bs
            rw [hc2']; exact hfi 2
          · change (φ₃ a11am_F0)⁻¹ * f 3 * φ₃ a11am_F0 ∈ Bs
            rw [hc3']; exact hfi 3
      refine ⟨φ₃ a11am_F0, hF0N, ?_⟩
      apply ConjMat_of_basis f hfcomm hf7 (φ₃ a11am_F0)
      intro i
      fin_cases i
      · change φ₃ a11am_F0 * f 0 * (φ₃ a11am_F0)⁻¹ = fPow f (fun j => a11am_D0 0 j)
        rw [a11am_D0_row0, fPow_nsmul f hfcomm hf7, ev, fPow_single]
        exact hc0
      · change φ₃ a11am_F0 * f 1 * (φ₃ a11am_F0)⁻¹ = fPow f (fun j => a11am_D0 1 j)
        rw [a11am_D0_row1, ev, fPow_single]
        exact hc1
      · change φ₃ a11am_F0 * f 2 * (φ₃ a11am_F0)⁻¹ = fPow f (fun j => a11am_D0 2 j)
        rw [a11am_D0_row2, ev, fPow_single]
        exact hc2
      · change φ₃ a11am_F0 * f 3 * (φ₃ a11am_F0)⁻¹ = fPow f (fun j => a11am_D0 3 j)
        rw [a11am_D0_row3, ev, fPow_single]
        exact hc3
  · intro t ht htrans
    obtain ⟨g, hgN, hcg⟩ := ht
    exact no_transv hBs hcard hfcomm hf7 hNT hgN hcg htrans

end CFSG.StandardType.A11

end
