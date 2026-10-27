module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeObstruction
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zd1_zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

omit [Module.Finite (ZMod 3) U] in
private theorem zd1_pairing_eq_zero_of_commute {B : LinearMap.BilinForm (ZMod 3) U}
    {t t' : U ≃ₗ[ZMod 3] U} {u u' : U} (hcomm : Commute t t') (hne : t ≠ t')
    (hu : B u u = 1) (hu' : B u' u' = 1)
    (htu : ∀ x, t x = x + B x u • u) (htu' : ∀ x, t' x = x + B x u' • u') :
    B u u' = 0 ∧ B u' u = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : Module.Dual (ZMod 3) U := -B.flipHom u
  let φ' : Module.Dual (ZMod 3) U := -B.flipHom u'
  have hφ : φ u = 2 := by
    dsimp only [φ]
    rw [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, hu]
    rfl
  have hφ' : φ' u' = 2 := by
    dsimp only [φ']
    rw [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, hu']
    rfl
  have htR : t = Module.reflection hφ := by
    apply LinearEquiv.ext
    intro x
    rw [Module.reflection_apply x hφ, htu x]
    dsimp only [φ]
    rw [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, neg_smul, sub_neg_eq_add]
  have ht'R : t' = Module.reflection hφ' := by
    apply LinearEquiv.ext
    intro x
    rw [Module.reflection_apply x hφ', htu' x]
    dsimp only [φ']
    rw [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, neg_smul, sub_neg_eq_add]
  have hcommR : Commute (Module.reflection hφ) (Module.reflection hφ') := by
    rwa [← htR, ← ht'R]
  have hneR : Module.reflection hφ ≠ Module.reflection hφ' := by
    rwa [← htR, ← ht'R]
  have h1 : φ u' = 0 :=
    apply_eq_zero_of_commute (p := 3) (by decide) hφ hφ' hcommR hneR
  have h2 : φ' u = 0 :=
    apply_eq_zero_of_commute (p := 3) (by decide) hφ' hφ hcommR.symm (Ne.symm hneR)
  constructor
  · have h : -B u u' = 0 := by
      simpa only [φ', LinearMap.neg_apply, LinearMap.BilinForm.flip_apply] using h2
    exact neg_eq_zero.mp h
  · have h : -B u' u = 0 := by
      simpa only [φ, LinearMap.neg_apply, LinearMap.BilinForm.flip_apply] using h1
    exact neg_eq_zero.mp h

omit [Module.Finite (ZMod 3) U] in
private theorem zd1_pairing_sum {m : ℕ} {B : LinearMap.BilinForm (ZMod 3) U}
    {u : Fin m → U} (hgram : ∀ i j, B (u i) (u j) = if i = j then 1 else 0)
    (x y : Fin m → ZMod 3) :
    B (∑ i, x i • u i) (∑ j, y j • u j) = ∑ i, x i * y i := by
  calc
    B (∑ i, x i • u i) (∑ j, y j • u j)
        = ∑ i, ∑ j, x i * (y j * (if i = j then 1 else 0)) := by
          rw [LinearMap.BilinForm.sum_left]
          apply Finset.sum_congr rfl
          intro i _
          rw [LinearMap.BilinForm.sum_right]
          apply Finset.sum_congr rfl
          intro j _
          rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hgram i j]
    _ = ∑ i, x i * y i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl]
            ring
          · intro j _ hji
            rw [if_neg (Ne.symm hji), mul_zero, mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi

private theorem zd1_exists_isometry_of_orthonormal {m : ℕ}
    {B : LinearMap.BilinForm (ZMod 3) U} {u : Fin m → U}
    (hfin : Module.finrank (ZMod 3) U = m)
    (hgram : ∀ i j, B (u i) (u j) = if i = j then 1 else 0) :
    ∃ L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U, ∀ x y, B (L x) (L y) = diagF3 m 1 x y := by
  have horth : B.iIsOrtho u := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    rw [hgram i j, if_neg hij]
  have hli : LinearIndependent (ZMod 3) u :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho horth (fun i => by
      rw [hgram i i, if_pos rfl]
      decide)
  have hcard : Fintype.card (Fin m) = Module.finrank (ZMod 3) U := by
    rw [Fintype.card_fin, hfin]
  let b : Module.Basis (Fin m) (ZMod 3) U :=
    basisOfLinearIndependentOfCardEqFinrank' u hli hcard
  have hb : ∀ i, b i = u i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' u hli hcard) i
  let L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U :=
    (Pi.basisFun (ZMod 3) (Fin m)).equiv b (Equiv.refl (Fin m))
  have hLsingle : ∀ i, L (Pi.single i 1) = u i := by
    intro i
    rw [← Pi.basisFun_apply (ZMod 3) (Fin m) i]
    dsimp only [L]
    rw [Module.Basis.equiv_apply]
    simpa using hb i
  have hL : ∀ x : Fin m → ZMod 3, L x = ∑ i, x i • u i := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Pi.single i (x i) = x i • Pi.single i 1 by
      rw [← Pi.single_smul' i (x i) 1, smul_eq_mul, mul_one]]
    rw [map_smul, hLsingle i]
  refine ⟨L, fun x y => ?_⟩
  rw [hL x, hL y]
  have hdiag : diagF3 m 1 x y = ∑ i, x i * y i := by
    rw [diagF3_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [diagF3Entry]
    split_ifs <;> ring
  rw [hdiag]
  exact zd1_pairing_sum hgram x y

theorem exists_isometry_of_mulEquiv_R3_diagF3_one (hn : 3 ≤ Module.finrank (ZMod 3) U)
    (hirr : AbsIrred 3 A) {m : ℕ} (hm : 4 ≤ m)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m 1))
    (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 (diagF3 m 1)) {B : LinearMap.BilinForm (ZMod 3) U}
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u) :
    ∃ L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U, ∀ x y, B (L x) (L y) = diagF3 m 1 x y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hmem, hinj, hcomm, hprod⟩ := frame_reflBar_diagF3_one hm
  let bar : Fin m → R3 (diagF3 m 1) :=
    fun i => reflBar (diagF3 m 1) (Pi.single i 1)
  let d : Fin m → ↥A ⧸ Subgroup.center ↥A := φ.symm ∘ bar
  have hd : ∀ i, d i ∈ reflImage 3 A :=
    fun i => (hφ (d i)).mpr (by simpa [d, bar] using hmem i)
  have hd_inj : Function.Injective d := φ.symm.injective.comp hinj
  have hd_comm : Pairwise fun i j => Commute (d i) (d j) :=
    fun i j hij => (hcomm hij).map φ.symm
  have hprod_bar : (List.ofFn bar).prod = 1 := hprod
  have hd_prod : (List.ofFn d).prod = 1 := by
    have h : (List.ofFn (φ.symm ∘ bar)).prod = φ.symm (List.ofFn bar).prod := by
      rw [← List.map_ofFn, List.prod_hom]
    have hd_def : d = φ.symm ∘ bar := rfl
    rw [hd_def, h, hprod_bar, map_one]
  have hfin : Module.finrank (ZMod 3) U = m :=
    (finrank_eq_and_neg_mem_of_prod_eq_one (p := 3) (by decide) hirr hn (by omega)
      hd hd_inj hd_comm hd_prod).1
  choose t ht _ using fun i => exists_unique_refl_of_mem_reflImage hirr hn (hd i)
  have ht_refl : ∀ i, IsRefl 3 (t i : U ≃ₗ[ZMod 3] U) := fun i => (ht i).1
  have ht_mk : ∀ i, QuotientGroup.mk (t i) = d i := fun i => (ht i).2
  choose u hu using fun i => hB (t i : U ≃ₗ[ZMod 3] U) (t i).2 (ht_refl i)
  have hu_norm : ∀ i, B (u i) (u i) = 1 := fun i => (hu i).1
  have hu_act : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i :=
    fun i x => (hu i).2 x
  have hgram : ∀ i j, B (u i) (u j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact hu_norm i
    · rw [if_neg hij]
      have hmk : Commute (QuotientGroup.mk (s := Subgroup.center ↥A) (t i))
        (QuotientGroup.mk (s := Subgroup.center ↥A) (t j)) := by
        rw [ht_mk i, ht_mk j]
        exact hd_comm hij
      have hne : QuotientGroup.mk (s := Subgroup.center ↥A) (t i) ≠
        QuotientGroup.mk (s := Subgroup.center ↥A) (t j) := by
        rw [ht_mk i, ht_mk j]
        exact fun h => hij (hd_inj h)
      have hcommA : Commute (t i) (t j) :=
        (hirr.commute_mk_iff hn (ht_refl j)).mp hmk
      have hcommL : Commute ((t i : U ≃ₗ[ZMod 3] U)) ((t j : U ≃ₗ[ZMod 3] U)) :=
        hcommA.map (Subgroup.subtype A)
      have hneL : (t i : U ≃ₗ[ZMod 3] U) ≠ (t j : U ≃ₗ[ZMod 3] U) := by
        intro h
        exact hne (by rw [Subtype.ext h])
      exact (zd1_pairing_eq_zero_of_commute hcommL hneL (hu_norm i) (hu_norm j)
        (hu_act i) (hu_act j)).1
  exact zd1_exists_isometry_of_orthonormal hfin hgram

end CFSG.StandardType.ZS
