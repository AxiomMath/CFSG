module

public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.LatticeWeylGroup

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.Adjoint


private def l6m5_delta (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ) :
    Fin 8 → (Fin Tag.E8.rank → ℤ) :=
  ![c 0, b, c 1, c 2, c 3, c 4, c 5, c 6]

private def l6m5_Gram (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ) : Prop :=
  ∀ k l : Fin 8, iform (τ := .E8) (l6m5_delta c b k) (l6m5_delta c b l) = Tag.cartan .E8 k l

private lemma l6m5_iform_eq_sum (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x y = ∑ i, ∑ j, x i * Tag.cartan .E8 i j * y j := by
  simp only [iform, Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]

private lemma l6m5_iform_eq_dot (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) x y = dotProduct x (Matrix.mulVec (Tag.cartan .E8) y) := by
  rw [l6m5_iform_eq_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma l6m5_iform_self
    (v : Fin Tag.E8.rank → ℤ) (hv : IsRoot .E8 v) :
    iform (τ := .E8) v v = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hv
  rw [hj]
  simp [Tag.symmetrizer]

private lemma l6m5_hbc
    (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ)
    (hb' : ∀ j, iform (τ := .E8) b (c j) = if j = 2 then -1 else 0) (j : Fin 8) :
    iform (τ := .E8) (c j) b = if j = 2 then -1 else 0 := by
  rw [iform_comm (τ := .E8), hb']

private lemma l6m5_gram
    (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ)
    (hc : ∀ i, IsRoot .E8 (c i)) (hb : IsRoot .E8 b)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j)
    (hb' : ∀ j, iform (τ := .E8) b (c j) = if j = 2 then -1 else 0) :
    l6m5_Gram c b := by
  have hbc := l6m5_hbc c b hb'
  have hbb := l6m5_iform_self b hb
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [l6m5_delta, hg, hb', hbc, hbb, Tag.cartan, Tag.cartanE, CartanMatrix.A]

private lemma l6m5_gram_sum (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ)
    (hgram : l6m5_Gram c b) (k l : Fin 8) :
    (∑ i : Fin Tag.E8.rank, ∑ j : Fin Tag.E8.rank,
        l6m5_delta c b k i * Tag.cartan .E8 i j * l6m5_delta c b l j) =
      Tag.cartan .E8 k l := by
  rw [← l6m5_iform_eq_sum, hgram k l]

private noncomputable def l6m5_M (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ) :
    Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := fun i k => l6m5_delta c b k i

private lemma l6m5_M_gram (c b) (hgram : l6m5_Gram c b) :
    Matrix.transpose (l6m5_M c b) * Tag.cartan .E8 * l6m5_M c b = Tag.cartan .E8 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, l6m5_M]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact l6m5_gram_sum c b hgram k l

private lemma l6m5_cartan_det : (Tag.cartan .E8).det = 1 := by
  change (Tag.cartanE 8).det = 1
  rw [cartanE_eq, CartanMatrix.E_det (by norm_num)]
  norm_num

private lemma l6m5_M_det_unit (c b) (hgram : l6m5_Gram c b) : IsUnit (l6m5_M c b).det := by
  have hM := l6m5_M_gram c b hgram
  have hdet : (l6m5_M c b).det * (l6m5_M c b).det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, l6m5_cartan_det] at h
    simpa using h
  exact isUnit_iff_dvd_one.mpr ⟨_, by rw [mul_comm, hdet]⟩

private lemma l6m5_dot_mulVec (c b) (z x : Fin Tag.E8.rank → ℤ) :
    dotProduct (Matrix.mulVec (l6m5_M c b) x) z =
      dotProduct x (Matrix.mulVec (Matrix.transpose (l6m5_M c b)) z) := by
  have h := Matrix.dotProduct_mulVec x (Matrix.transpose (l6m5_M c b)) z
  have h2 : Matrix.vecMul x (Matrix.transpose (l6m5_M c b)) =
      Matrix.mulVec (l6m5_M c b) x := by
    rw [← Matrix.mulVec_transpose (Matrix.transpose (l6m5_M c b)) x,
      Matrix.transpose_transpose]
  rw [h, h2]

private lemma l6m5_iso (c b) (hgram : l6m5_Gram c b) (x y : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) ((l6m5_M c b).mulVecLin x) ((l6m5_M c b).mulVecLin y) =
      iform (τ := .E8) x y := by
  rw [l6m5_iform_eq_dot, l6m5_iform_eq_dot]
  simp only [Matrix.mulVecLin_apply]
  rw [l6m5_dot_mulVec c b (Matrix.mulVec (Tag.cartan .E8) (Matrix.mulVec (l6m5_M c b) y)) x]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, l6m5_M_gram c b hgram]

private lemma l6m5_iform_smul
    (w : WeylGroup .E8) (u v : Fin Tag.E8.rank → ℤ) :
    iform (τ := .E8) (w • u) (w • v) = iform (τ := .E8) u v := by
  induction w using (coxeterSystem .E8).simple_induction_left generalizing u v with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul, simple_smul, simple_smul, iform_reflect, ih]

private lemma l6m5_smul_int (w : WeylGroup .E8) (m : ℤ) (v : Fin Tag.E8.rank → ℤ) :
    w • (m • v) = m • (w • v) := by
  rw [smul_def, smul_def]
  exact LinearMap.map_smul (weylAction (isFiniteType_cartan .E8) w) m v

private noncomputable def l6m5_U (c b) (hgram : l6m5_Gram c b) :
    (Module.End ℤ (Fin Tag.E8.rank → ℤ))ˣ where
  val := (l6m5_M c b).mulVecLin
  inv := (l6m5_M c b)⁻¹.mulVecLin
  val_inv := LinearMap.ext fun x => by
    show (l6m5_M c b).mulVecLin ((l6m5_M c b)⁻¹.mulVecLin x) =
      (1 : Module.End ℤ (Fin Tag.E8.rank → ℤ)) x
    rw [Module.End.one_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (l6m5_M_det_unit c b hgram),
      Matrix.one_mulVec]
  inv_val := LinearMap.ext fun x => by
    show (l6m5_M c b)⁻¹.mulVecLin ((l6m5_M c b).mulVecLin x) =
      (1 : Module.End ℤ (Fin Tag.E8.rank → ℤ)) x
    rw [Module.End.one_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (l6m5_M_det_unit c b hgram),
      Matrix.one_mulVec]

private lemma l6m5_reflRoot_apply
    (v : Fin Tag.E8.rank → ℤ) (w : WeylGroup .E8)
    (j : Fin Tag.E8.rank) (hv : v = w • Pi.single j 1) (x : Fin Tag.E8.rank → ℤ) :
    (↑(weylToAut .E8 w * reflectUnit .E8 j * (weylToAut .E8 w)⁻¹) :
        Module.End ℤ (Fin Tag.E8.rank → ℤ)) x = x - iform (τ := .E8) x v • v := by
  rw [hv]
  have hcoe : weylToAut .E8 w * reflectUnit .E8 j * (weylToAut .E8 w)⁻¹ =
      weylToAut .E8 (w * simple .E8 j * w⁻¹) := by
    rw [map_mul, map_mul, map_inv, weylToAut_simple]
  rw [hcoe, weylToAut_apply, mul_smul, mul_smul, simple_smul]
  have hc : (∑ l, Tag.cartan .E8 j l * ((w⁻¹) • x) l) =
      iform (τ := .E8) x (w • Pi.single j 1) := by
    have h1 : iform (τ := .E8) ((w⁻¹) • x) (Pi.single j 1) =
        ∑ l, Tag.cartan .E8 j l * ((w⁻¹) • x) l := by
      rw [iform_single_right]
      simp [Tag.symmetrizer]
    rw [← h1, ← l6m5_iform_smul w ((w⁻¹) • x) (Pi.single j 1), smul_inv_smul]
  rw [reflect, smul_sub, l6m5_smul_int, smul_inv_smul, hc]

private lemma l6m5_U_conj_apply
    (c b) (hgram : l6m5_Gram c b) (k : Fin Tag.E8.rank)
    (x : Fin Tag.E8.rank → ℤ) :
    (((l6m5_U c b hgram * reflectUnit .E8 k * (l6m5_U c b hgram)⁻¹ :
        (Module.End ℤ (Fin Tag.E8.rank → ℤ))ˣ)) :
        Module.End ℤ (Fin Tag.E8.rank → ℤ)) x =
      x - iform (τ := .E8) x (l6m5_delta c b k) • l6m5_delta c b k := by
  have hMdet := l6m5_M_det_unit c b hgram
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [show (↑(l6m5_U c b hgram) : Module.End ℤ (Fin Tag.E8.rank → ℤ)) =
      (l6m5_M c b).mulVecLin from rfl,
    show (↑((l6m5_U c b hgram)⁻¹) : Module.End ℤ (Fin Tag.E8.rank → ℤ)) =
      (l6m5_M c b)⁻¹.mulVecLin from rfl]
  rw [reflectUnit_apply]
  rw [reflect, map_sub, map_smul]
  have hu : (l6m5_M c b).mulVecLin ((l6m5_M c b)⁻¹.mulVecLin x) = x := by
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hMdet, Matrix.one_mulVec]
  have he : (l6m5_M c b).mulVecLin (Pi.single k 1 : Fin Tag.E8.rank → ℤ) =
      l6m5_delta c b k := by
    rw [Matrix.mulVecLin_apply]
    ext i
    simp [Matrix.mulVec, l6m5_M, Pi.single_apply]
  have hcoef : iform (τ := .E8) x (l6m5_delta c b k) =
      ∑ l, Tag.cartan .E8 k l * ((l6m5_M c b)⁻¹.mulVecLin x) l := by
    have h1 : iform (τ := .E8) ((l6m5_M c b)⁻¹.mulVecLin x) (Pi.single k 1) =
        ∑ l, Tag.cartan .E8 k l * ((l6m5_M c b)⁻¹.mulVecLin x) l := by
      rw [iform_single_right]
      simp [Tag.symmetrizer]
    conv_lhs => rw [← hu, ← he]
    rw [l6m5_iso c b hgram, h1]
  rw [hu, he, ← hcoef]

theorem e8_weyl_generated_by_chain
    (c : Fin 8 → (Fin Tag.E8.rank → ℤ)) (b : Fin Tag.E8.rank → ℤ)
    (hc : ∀ i, IsRoot .E8 (c i)) (hb : IsRoot .E8 b)
    (hg : ∀ i j, iform (τ := .E8) (c i) (c j) = CartanMatrix.A 8 i j)
    (hb' : ∀ j, iform (τ := .E8) b (c j) = if j = 2 then -1 else 0)
    (s : Fin 8 → WeylGroup .E8) (sb : WeylGroup .E8)
    (hs : ∀ i (v : Fin Tag.E8.rank → ℤ), s i • v = v - iform (τ := .E8) v (c i) • c i)
    (hsb : ∀ v : Fin Tag.E8.rank → ℤ, sb • v = v - iform (τ := .E8) v b • b) :
    Subgroup.closure (Set.range s ∪ {sb}) = ⊤ := by
  classical
  have hgram : l6m5_Gram c b := l6m5_gram c b hc hb hg hb'
  let U : (Module.End ℤ (Fin Tag.E8.rank → ℤ))ˣ := l6m5_U c b hgram
  have hdroot : ∀ k : Fin 8, IsRoot .E8 (l6m5_delta c b k) := by
    intro k
    fin_cases k
    · exact hc 0
    · exact hb
    · exact hc 1
    · exact hc 2
    · exact hc 3
    · exact hc 4
    · exact hc 5
    · exact hc 6
  have hex : ∀ k : Fin 8, ∃ w : WeylGroup .E8, ∃ j : Fin Tag.E8.rank,
      l6m5_delta c b k = w • Pi.single j 1 := by
    intro k
    obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.mp (hdroot k)
    exact ⟨w, j, hwj.symm⟩
  let wk : Fin 8 → WeylGroup .E8 := fun k => Classical.choose (hex k)
  let jk : Fin 8 → Fin Tag.E8.rank := fun k => Classical.choose (Classical.choose_spec (hex k))
  have hwk : ∀ k, l6m5_delta c b k = wk k • Pi.single (jk k) 1 :=
    fun k => Classical.choose_spec (Classical.choose_spec (hex k))
  let rUnit : Fin 8 → (Module.End ℤ (Fin Tag.E8.rank → ℤ))ˣ := fun k =>
    weylToAut .E8 (wk k) * reflectUnit .E8 (jk k) * (weylToAut .E8 (wk k))⁻¹
  have hrUnit_apply : ∀ k (x : Fin Tag.E8.rank → ℤ),
      (rUnit k : Module.End ℤ (Fin Tag.E8.rank → ℤ)) x =
        x - iform (τ := .E8) x (l6m5_delta c b k) • l6m5_delta c b k :=
    fun k x => l6m5_reflRoot_apply (l6m5_delta c b k) (wk k) (jk k) (hwk k) x
  have hrUnit_mem : ∀ k, rUnit k ∈ latticeWeylGroup .E8 := by
    intro k
    have hw : weylToAut .E8 (wk k) ∈ latticeWeylGroup .E8 := by
      rw [← range_weylToAut]
      exact MonoidHom.mem_range.mpr ⟨wk k, rfl⟩
    have hr : reflectUnit .E8 (jk k) ∈ latticeWeylGroup .E8 := by
      rw [latticeWeylGroup]
      exact Subgroup.subset_closure ⟨jk k, rfl⟩
    exact mul_mem (mul_mem hw hr) (inv_mem hw)
  have hHK : Subgroup.closure (Set.range rUnit) ≤ latticeWeylGroup .E8 :=
    (Subgroup.closure_le (latticeWeylGroup .E8)).mpr (by rintro _ ⟨k, rfl⟩; exact hrUnit_mem k)
  have hUru : ∀ k, U * reflectUnit .E8 k * U⁻¹ = rUnit k := by
    intro k
    refine Units.ext (LinearMap.ext fun x => ?_)
    rw [l6m5_U_conj_apply c b hgram k x, hrUnit_apply k x]
  let cU : (Module.End ℤ (Fin Tag.E8.rank → ℤ))ˣ →*
      (Module.End ℤ (Fin Tag.E8.rank → ℤ))ˣ := (MulAut.conj U).toMonoidHom
  have hcU : ∀ k, cU (reflectUnit .E8 k) = rUnit k := by
    intro k
    change (MulAut.conj U) (reflectUnit .E8 k) = rUnit k
    rw [MulAut.conj_apply]
    exact hUru k
  have hmap : Subgroup.map cU (latticeWeylGroup .E8) =
      Subgroup.closure (Set.range rUnit) := by
    rw [latticeWeylGroup, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, rfl⟩; exact ⟨k, (hcU k).symm⟩
    · rintro ⟨k, rfl⟩; exact ⟨reflectUnit .E8 k, ⟨k, rfl⟩, hcU k⟩
  have hcard : Nat.card (Subgroup.closure (Set.range rUnit)) =
      Nat.card (latticeWeylGroup .E8) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (f := cU)
      (by intro a b hab; exact (MulAut.conj U).injective hab)
  haveI : Finite (latticeWeylGroup .E8) := (finite_weyl_pair_orders .E8).1
  have hHKeq : Subgroup.closure (Set.range rUnit) = latticeWeylGroup .E8 :=
    Subgroup.eq_of_le_of_card_ge hHK (le_of_eq hcard.symm)
  let u : Fin 8 → WeylGroup .E8 := ![s 0, sb, s 1, s 2, s 3, s 4, s 5, s 6]
  have hu_set : ∀ k, u k ∈ Set.range s ∪ {sb} := by
    intro k
    fin_cases k
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨5, rfl⟩
    · exact Or.inl ⟨6, rfl⟩
  have hweyl : ∀ k, weylToAut .E8 (u k) = rUnit k := by
    intro k
    refine Units.ext (LinearMap.ext fun x => ?_)
    rw [weylToAut_apply, hrUnit_apply k x]
    fin_cases k
    · change s 0 • x = x - iform (τ := .E8) x (c 0) • c 0
      rw [hs 0 x]
    · change sb • x = x - iform (τ := .E8) x b • b
      rw [hsb x]
    · change s 1 • x = x - iform (τ := .E8) x (c 1) • c 1
      rw [hs 1 x]
    · change s 2 • x = x - iform (τ := .E8) x (c 2) • c 2
      rw [hs 2 x]
    · change s 3 • x = x - iform (τ := .E8) x (c 3) • c 3
      rw [hs 3 x]
    · change s 4 • x = x - iform (τ := .E8) x (c 4) • c 4
      rw [hs 4 x]
    · change s 5 • x = x - iform (τ := .E8) x (c 5) • c 5
      rw [hs 5 x]
    · change s 6 • x = x - iform (τ := .E8) x (c 6) • c 6
      rw [hs 6 x]
  have hclosure : Subgroup.closure (Set.range u) = ⊤ := by
    have hinj : Function.Injective (weylToAut .E8) := weylToAut_injective
    have hmap2 : Subgroup.map (weylToAut .E8) (Subgroup.closure (Set.range u)) =
        latticeWeylGroup .E8 := by
      rw [MonoidHom.map_closure]
      have hrange : (weylToAut .E8) '' Set.range u = Set.range rUnit := by
        ext y
        constructor
        · rintro ⟨x, ⟨k, rfl⟩, rfl⟩; exact ⟨k, (hweyl k).symm⟩
        · rintro ⟨k, rfl⟩; exact ⟨u k, ⟨k, rfl⟩, hweyl k⟩
      rw [hrange, ← hHKeq]
    have hmapTop : Subgroup.map (weylToAut .E8) (⊤ : Subgroup (WeylGroup .E8)) =
        latticeWeylGroup .E8 := by
      rw [Subgroup.map_top, range_weylToAut]
    exact Subgroup.map_injective (f := weylToAut .E8) hinj (hmap2.trans hmapTop.symm)
  have hle : Subgroup.closure (Set.range u) ≤ Subgroup.closure (Set.range s ∪ {sb}) :=
    Subgroup.closure_mono (Set.range_subset_iff.mpr hu_set)
  rw [hclosure] at hle
  exact top_le_iff.mp hle

end CFSG.StandardType

end
