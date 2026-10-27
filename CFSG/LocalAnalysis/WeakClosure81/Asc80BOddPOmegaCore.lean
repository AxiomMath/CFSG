module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataQuotient
public import CFSG.LieType.SeitzGeneration.Basic

import CFSG.GroupTheory.ElementaryAbelianBasis
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaField
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaLin
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaLoc
import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap CFSG.Open CFSG.LieType.SeitzGeneration
  CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (projectivePointAction)

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private lemma card_range_le_two_of_sq_eq_one {G H : Type*} [Group G] [Group H]
    [Fintype H] [IsCyclic H] (φ : G →* H) (hG : ∀ x : G, φ x * φ x = 1) :
    Nat.card φ.range ≤ 2 := by
  classical
  have h := IsCyclic.card_pow_eq_one_le (α := ↥φ.range) (n := 2) (by norm_num)
  have htop : (Finset.univ : Finset ↥φ.range).filter (fun x => x ^ 2 = 1) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x _
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp x.2
    have hx : x = ⟨φ e, ⟨e, rfl⟩⟩ := Subtype.ext he.symm
    rw [hx]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [pow_two] using hG e
  have h' : Fintype.card ↥φ.range ≤ 2 := by simpa [htop] using h
  rw [Nat.card_eq_fintype_card]
  exact h'

private lemma two_le_natCard_of_ne_bot {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (h : H ≠ ⊥) : 2 ≤ Nat.card H := by
  have := (Subgroup.one_lt_card_iff_ne_bot (H := H)).mpr h
  omega

omit [Finite K] in
theorem coordinateSemilinearMap_right_one_eq_linear
    (g : coordinateSemilinearGroup d K) (hr : g.right = 1) :
    coordinateSemilinearMap g = (matrixLinearEquiv g.left).toAddEquiv := by
  apply AddEquiv.ext
  intro v
  change g.left.val *ᵥ (fun i => g.right (v i)) = matrixLinearEquiv g.left v
  rw [matrixLinearEquiv_apply, hr]
  simp

omit [Finite K] in
theorem coordinateSemilinearMap_eq_smul_of_scalar
    (g : coordinateSemilinearGroup d K) (hr : g.right = 1) {a : Kˣ}
    (hl : g.left = GeneralLinearGroup.scalar (Fin d) a) (v : Fin d → K) :
    coordinateSemilinearMap g v = (a : K) • v := by
  rw [coordinateSemilinearMap_apply, hl, hr]
  change (GeneralLinearGroup.scalar (Fin d) a).val *ᵥ v = (a : K) • v
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]

theorem stable_of_generators
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a)
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))}
    {W : Submodule K (Fin d → K)}
    {ga gb : similarityPairs Q} {a b : MulAut (matrixProjectiveDerived Q)}
    (hκa : matrixProjectiveConjugationHom Q ga = a)
    (hκb : matrixProjectiveConjugationHom Q gb = b)
    (hgen : Subgroup.closure ({a, b} : Set (MulAut (matrixProjectiveDerived Q))) = E)
    (hsta : ∀ w ∈ W, coordinateSemilinearMap ga.val w ∈ W)
    (hstb : ∀ w ∈ W, coordinateSemilinearMap gb.val w ∈ W) :
    ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
      ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W := by
  classical
  let good : similarityPairs Q → Prop :=
    fun g => ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W
  have hgood_one : good 1 := by
    intro w hw
    rw [Subgroup.coe_one, coordinateSemilinearMap_one]
    exact hw
  have hgood_mul : ∀ x y, good x → good y → good (x * y) := by
    intro x y hx hy w hw
    rw [Subgroup.coe_mul, coordinateSemilinearMap_mul]
    exact hx _ (hy w hw)
  have hgood_inv : ∀ x, good x → good (x⁻¹) := by
    intro x hx w hw
    rw [Subgroup.coe_inv, coordinateSemilinearMap_inv]
    have hsub : coordinateSemilinearMap x.val '' (W : Set (Fin d → K)) ⊆ (W : Set (Fin d → K)) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hx v hv
    have hcard : (coordinateSemilinearMap x.val '' (W : Set (Fin d → K))).ncard =
        (W : Set (Fin d → K)).ncard :=
      Set.ncard_image_of_injective (W : Set (Fin d → K))
        (coordinateSemilinearMap x.val).injective
    have heq : coordinateSemilinearMap x.val '' (W : Set (Fin d → K)) = (W : Set (Fin d → K)) :=
      Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard.symm)
    have hw' : w ∈ coordinateSemilinearMap x.val '' (W : Set (Fin d → K)) := by
      rw [heq]
      exact hw
    obtain ⟨v, hv, hvw⟩ := hw'
    rw [← hvw, AddEquiv.symm_apply_apply]
    exact hv
  have hclos_good : ∀ x ∈ Subgroup.closure ({ga, gb} : Set (similarityPairs Q)), good x := by
    intro x hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hsta
      · exact hstb
    · exact hgood_one
    · intro y z hy hz ihy ihz
      exact hgood_mul y z ihy ihz
    · intro y hy ihy
      exact hgood_inv y ihy
  have hmap : (Subgroup.closure ({ga, gb} : Set (similarityPairs Q))).map
      (matrixProjectiveConjugationHom Q) =
      Subgroup.closure ({a, b} : Set (MulAut (matrixProjectiveDerived Q))) := by
    rw [MonoidHom.map_closure]
    simp [hκa, hκb]
  intro g hgE w hw
  have hmemmap : matrixProjectiveConjugationHom Q g ∈
      (Subgroup.closure ({ga, gb} : Set (similarityPairs Q))).map
        (matrixProjectiveConjugationHom Q) := by
    rw [hmap]
    exact hgen ▸ hgE
  obtain ⟨h, hh, hκh⟩ := Subgroup.mem_map.mp hmemmap
  have hqκ : matrixProjectiveConjugationHom Q (h⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hκh, inv_mul_cancel]
  obtain ⟨hqr, c, hqc⟩ := hker (h⁻¹ * g) hqκ
  have hσq : coordinateSemilinearMap (h⁻¹ * g).val w = (c : K) • w :=
    coordinateSemilinearMap_eq_smul_of_scalar (h⁻¹ * g).val hqr hqc w
  have hmul := coordinateSemilinearMap_mul h.val (h⁻¹ * g).val w
  have hqval : h.val * (h⁻¹ * g).val = g.val := by
    have hq2 : h * (h⁻¹ * g) = g := by group
    exact congrArg Subtype.val hq2
  rw [hqval, hσq] at hmul
  rw [hmul]
  exact hclos_good h hh _ (Submodule.smul_mem _ _ hw)

theorem exists_generator_lifts
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a)
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (hEim : E ≤ matrixProjectiveImage Q)
    (hlin : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E → g.val.right = 1) :
    ∃ ga gb : similarityPairs Q,
      matrixProjectiveConjugationHom Q ga ∈ E ∧ matrixProjectiveConjugationHom Q gb ∈ E ∧
      matrixProjectiveConjugationHom Q ga ≠ 1 ∧ matrixProjectiveConjugationHom Q gb ≠ 1 ∧
      matrixProjectiveConjugationHom Q ga ≠ matrixProjectiveConjugationHom Q gb ∧
      Subgroup.closure {matrixProjectiveConjugationHom Q ga,
        matrixProjectiveConjugationHom Q gb} = E ∧
      ga.val.right = 1 ∧ gb.val.right = 1 ∧ ∃ cA cB cAB : Kˣ,
        (∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) = (cA : K) • v) ∧
        (∀ v, coordinateSemilinearMap gb.val (coordinateSemilinearMap gb.val v) = (cB : K) • v) ∧
        ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val v) =
          (cAB : K) • coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val v) := by
  classical
  have hsqE : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have hx' := hE.2 x hx
    simpa [pow_two] using hx'
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨l, hl, hndl, hmeml, hcardl⟩ :=
    CFSG.GroupTheory.exists_list_closure_card (G := MulAut (matrixProjectiveDerived Q)) E hsqE
      hcommE 2 (by rw [h4]; norm_num)
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
  have haE : a ∈ E := (hmeml a (by simp)).1
  have hbE : b ∈ E := (hmeml b (by simp)).1
  have ha1 : a ≠ 1 := (hmeml a (by simp)).2
  have hb1 : b ≠ 1 := (hmeml b (by simp)).2
  have hne : a ≠ b := by
    intro hab
    subst hab
    exact (List.not_nodup_pair a) hndl
  have hset : {x : MulAut (matrixProjectiveDerived Q) | x ∈ [a, b]} = ({a, b} : Set _) := by
    ext x
    simp
  rw [hset] at hcardl
  have hgen : Subgroup.closure ({a, b} : Set (MulAut (matrixProjectiveDerived Q))) = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haE
      · exact hbE
    · rw [hcardl, h4]
      norm_num
  obtain ⟨ga, hκga⟩ := MonoidHom.mem_range.mp (hEim haE)
  obtain ⟨gb, hκgb⟩ := MonoidHom.mem_range.mp (hEim hbE)
  have hgra : ga.val.right = 1 := hlin ga (hκga ▸ haE)
  have hgrb : gb.val.right = 1 := hlin gb (hκgb ▸ hbE)
  have hκgg : matrixProjectiveConjugationHom Q (ga * ga) = 1 := by
    rw [map_mul, hκga]
    exact hsqE a haE
  obtain ⟨hggr, cA, hcA⟩ := hker (ga * ga) hκgg
  have hA2 : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) =
      (cA : K) • v := by
    intro v
    have h1 : coordinateSemilinearMap (ga * ga).val v = (cA : K) • v :=
      coordinateSemilinearMap_eq_smul_of_scalar (ga * ga).val hggr hcA v
    have hcoe : (ga * ga).val = ga.val * ga.val := rfl
    rw [hcoe] at h1
    have h2 := coordinateSemilinearMap_mul ga.val ga.val v
    rw [h2] at h1
    exact h1
  have hκgg2 : matrixProjectiveConjugationHom Q (gb * gb) = 1 := by
    rw [map_mul, hκgb]
    exact hsqE b hbE
  obtain ⟨hbgr, cB, hcB⟩ := hker (gb * gb) hκgg2
  have hB2 : ∀ v, coordinateSemilinearMap gb.val (coordinateSemilinearMap gb.val v) =
      (cB : K) • v := by
    intro v
    have h1 : coordinateSemilinearMap (gb * gb).val v = (cB : K) • v :=
      coordinateSemilinearMap_eq_smul_of_scalar (gb * gb).val hbgr hcB v
    have hcoe : (gb * gb).val = gb.val * gb.val := rfl
    rw [hcoe] at h1
    have h2 := coordinateSemilinearMap_mul gb.val gb.val v
    rw [h2] at h1
    exact h1
  have hκcomm : matrixProjectiveConjugationHom Q (ga * gb * ga⁻¹ * gb⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hκga, hκgb]
    change a * b * a⁻¹ * b⁻¹ = 1
    rw [hcommE a haE b hbE]
    group
  obtain ⟨hcommr, cAB, hcAB⟩ := hker (ga * gb * ga⁻¹ * gb⁻¹) hκcomm
  have hcomp : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val
      (coordinateSemilinearMap ga.val⁻¹ (coordinateSemilinearMap gb.val⁻¹ v))) =
      (cAB : K) • v := by
    intro v
    have h1 : coordinateSemilinearMap (ga * gb * ga⁻¹ * gb⁻¹).val v = (cAB : K) • v :=
      coordinateSemilinearMap_eq_smul_of_scalar _ hcommr hcAB v
    have h2 : coordinateSemilinearMap (ga * gb * ga⁻¹ * gb⁻¹).val v =
        coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val
          (coordinateSemilinearMap ga.val⁻¹ (coordinateSemilinearMap gb.val⁻¹ v))) := by
      rw [show (ga * gb * ga⁻¹ * gb⁻¹).val =
        ga.val * gb.val * ga.val⁻¹ * gb.val⁻¹ from rfl]
      rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul,
        coordinateSemilinearMap_mul]
    rwa [h2] at h1
  have hAB : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val v) =
      (cAB : K) • coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val v) := by
    intro v
    have h := hcomp (coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val v))
    rw [coordinateSemilinearMap_inv, coordinateSemilinearMap_inv] at h
    rwa [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at h
  have hgen' : Subgroup.closure {matrixProjectiveConjugationHom Q ga,
      matrixProjectiveConjugationHom Q gb} = E := by
    rw [hκga, hκgb]
    exact hgen
  exact ⟨ga, gb, hκga ▸ haE, hκgb ▸ hbE, by rw [hκga]; exact ha1,
    by rw [hκgb]; exact hb1, by rw [hκga, hκgb]; exact hne, hgen', hgra, hgrb,
    cA, cB, cAB, hA2, hB2, hAB⟩

private lemma right_eq_one_of_no_stable
    (h2 : (2 : K) ≠ 0) (hnd : Q.polarBilin.Nondegenerate)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a)
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (hEim : E ≤ matrixProjectiveImage Q)
    (hno : ∀ W : Submodule K (Fin d → K), (∀ x ∈ W, Q x = 0) →
      (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
        ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W) → W = ⊥)
    (hd : 5 ≤ d) :
    ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E → g.val.right = 1 := by
  classical
  intro g hgE
  by_contra hgφ
  let κ := matrixProjectiveConjugationHom Q
  have hκker_le : κ.ker ≤ (fieldProjection Q).ker := fun x hx =>
    ((hker x) (MonoidHom.mem_ker.mp hx)).1
  let ψ : matrixProjectiveImage Q →* (K ≃+* K) :=
    (QuotientGroup.lift κ.ker (fieldProjection Q) hκker_le).comp
      (QuotientGroup.quotientKerEquivRange κ).symm.toMonoidHom
  have hψ : ∀ x : similarityPairs Q, ψ ⟨κ x, ⟨x, rfl⟩⟩ = x.val.right := by
    intro x
    have e1 : (QuotientGroup.quotientKerEquivRange κ).symm ⟨κ x, ⟨x, rfl⟩⟩ =
        (x : similarityPairs Q ⧸ κ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift κ.ker (fieldProjection Q) hκker_le
      ((QuotientGroup.quotientKerEquivRange κ).symm ⟨κ x, ⟨x, rfl⟩⟩) = x.val.right
    rw [e1, QuotientGroup.lift_mk]
    rfl
  let ψE : E →* (K ≃+* K) := ψ.comp (Subgroup.inclusion hEim)
  have hψE : ∀ (x : similarityPairs Q) (hx : κ x ∈ E), ψE ⟨κ x, hx⟩ = x.val.right := by
    intro x hx
    change ψ (Subgroup.inclusion hEim ⟨κ x, hx⟩) = x.val.right
    rw [show Subgroup.inclusion hEim ⟨κ x, hx⟩ = ⟨κ x, ⟨x, rfl⟩⟩ from rfl, hψ]
  have hsqE : ∀ x : E, x * x = 1 := by
    intro x
    apply Subtype.ext
    have hx := hE.2 (x : MulAut (matrixProjectiveDerived Q)) x.2
    simpa [pow_two] using hx
  have hψE2 : ∀ x : E, ψE x * ψE x = 1 := by
    intro x
    rw [← map_mul, hsqE x, map_one]
  have hfiniteFun : Finite (K → K) := by infer_instance
  have hfintypeFun : Fintype (K → K) := @Fintype.ofFinite _ hfiniteFun
  have hfintypeAut : Fintype (K ≃+* K) :=
    @Fintype.ofInjective _ _ hfintypeFun (fun e : K ≃+* K => (e : K → K)) (by
      intro a b h
      ext x
      exact congrFun h x)
  have hcycAut : IsCyclic (K ≃+* K) :=
    CFSG.RankThree.GF2n.Stroth80.isCyclic_ringEquiv K
  have hrangeCard : Nat.card ψE.range ≤ 2 :=
    @card_range_le_two_of_sq_eq_one _ (K ≃+* K) _ _ hfintypeAut hcycAut ψE hψE2
  have hrangeNeBot : ψE.range ≠ ⊥ := by
    intro hbot
    have hmem : ψE ⟨κ g, hgE⟩ ∈ ψE.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, hψE g hgE] at hmem
    exact hgφ hmem
  have hfintypeRange : Fintype ↥ψE.range :=
    @Fintype.ofInjective _ _ hfintypeAut Subtype.val Subtype.val_injective
  have hfinRange : Finite ↥ψE.range := @Finite.of_fintype _ hfintypeRange
  have h2le : 2 ≤ Nat.card ψE.range :=
    @two_le_natCard_of_ne_bot _ _ ψE.range hfinRange hrangeNeBot
  have hrangeEq : Nat.card ψE.range = 2 := le_antisymm hrangeCard h2le
  have hkerCard : Nat.card ψE.ker = 2 := by
    have h := Subgroup.card_ker_mul_card_range ψE
    rw [h4, hrangeEq] at h
    omega
  have hkerNeBot : ψE.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hkerCard
    omega
  obtain ⟨bker, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hkerNeBot
  let b : E := bker.1
  have hb1 : b ≠ 1 := by
    intro hb
    apply hbne
    apply Subtype.ext
    simpa [b] using congrArg Subtype.val hb
  have hψb : ψE b = 1 := bker.2
  obtain ⟨gb, hκgb⟩ := MonoidHom.mem_range.mp (hEim b.2)
  have hκgbE : κ gb ∈ E := hκgb ▸ b.2
  have hgbright : gb.val.right = 1 := by
    have h1 : ψE ⟨κ gb, hκgbE⟩ = gb.val.right := hψE gb hκgbE
    have h2 : (⟨κ gb, hκgbE⟩ : E) = b := Subtype.ext hκgb
    rw [h2, hψb] at h1
    exact h1.symm
  let a : E := ⟨κ g, hgE⟩
  have haKer : a ∉ ψE.ker := by
    intro hmem
    have h1 : ψE a = 1 := hmem
    rw [show ψE a = g.val.right from hψE g hgE] at h1
    exact hgφ h1
  have ha1 : a ≠ 1 := by
    intro ha
    apply haKer
    rw [ha]
    exact ψE.ker.one_mem
  have hne : a ≠ b := by
    intro hab
    apply haKer
    rw [hab]
    exact bker.2
  have hcommE : ∀ x y : E, x * y = y * x := fun x y =>
    hE.1.is_comm.comm x y
  have hcardClos : Nat.card (Subgroup.closure ({a, b} : Set E)) = 4 :=
    CFSG.GroupTheory.card_closure_pair_of_involutions (hsqE a) (hsqE b)
      (hcommE a b) ha1 hb1 hne.symm
  have htop : Subgroup.closure ({a, b} : Set E) = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (H := Subgroup.closure ({a, b} : Set E))).mp (by
      rw [hcardClos, h4])
  have hgen : Subgroup.closure ({(a : MulAut (matrixProjectiveDerived Q)),
      (b : MulAut (matrixProjectiveDerived Q))} : Set _) = E := by
    have hmap := MonoidHom.map_closure E.subtype ({a, b} : Set E)
    rw [htop, Subgroup.map_top, Subgroup.range_subtype] at hmap
    have himg : E.subtype '' ({a, b} : Set E) =
        ({(a : MulAut (matrixProjectiveDerived Q)),
          (b : MulAut (matrixProjectiveDerived Q))} : Set _) := by
      ext x
      simp
    rw [himg] at hmap
    exact hmap.symm
  have ha2 : (g * g).val.right = 1 ∧ ∃ c : Kˣ,
      (g * g).val.left = GeneralLinearGroup.scalar (Fin d) c := by
    apply hker
    rw [map_mul]
    simpa [a] using hsqE a
  have hb2 : ∃ c : Kˣ, (gb * gb).val.left = GeneralLinearGroup.scalar (Fin d) c := by
    apply (hker (gb * gb) ?_).2
    rw [map_mul, hκgb]
    simpa using congrArg Subtype.val (hsqE b)
  have hcommκ : κ (g * gb * g⁻¹ * gb⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hκgb]
    change (a : MulAut (matrixProjectiveDerived Q)) * (b : MulAut (matrixProjectiveDerived Q)) *
      (a : MulAut (matrixProjectiveDerived Q))⁻¹ *
      (b : MulAut (matrixProjectiveDerived Q))⁻¹ = 1
    rw [show (a : MulAut (matrixProjectiveDerived Q)) * (b : MulAut (matrixProjectiveDerived Q)) =
      (b : MulAut (matrixProjectiveDerived Q)) * (a : MulAut (matrixProjectiveDerived Q)) from
        congrArg Subtype.val (hcommE a b)]
    group
  have hab : ∃ c : Kˣ,
      (g * gb * g⁻¹ * gb⁻¹).val.left = GeneralLinearGroup.scalar (Fin d) c :=
    (hker _ hcommκ).2
  obtain ⟨W, hW0, hWsing, hWsta, hWstb⟩ :=
    exists_stable_singular_field h2 hnd hd g gb hgφ hgbright ha2 hb2 hab
  have hstab := stable_of_generators hker (ga := g) (gb := gb)
    (a := (a : MulAut (matrixProjectiveDerived Q)))
    (b := (b : MulAut (matrixProjectiveDerived Q))) rfl hκgb hgen hWsta hWstb
  exact hW0 (hno W hWsing hstab)

private lemma d_le_eight_of_no_stable
    (h2 : (2 : K) ≠ 0) (hnd : Q.polarBilin.Nondegenerate)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a)
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (hEim : E ≤ matrixProjectiveImage Q)
    (hlin : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E → g.val.right = 1)
    (hno : ∀ W : Submodule K (Fin d → K), (∀ x ∈ W, Q x = 0) →
      (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
        ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W) → W = ⊥) :
    d ≤ 8 := by
  classical
  by_contra hd8
  have h9 : 9 ≤ d := by omega
  obtain ⟨ga, gb, -, -, -, -, -, hgen, hgra, hgrb, cA, cB, cAB, hA2σ, hB2σ, hABσ⟩ :=
    exists_generator_lifts hker hE h4 hEim hlin
  let eA : (Fin d → K) ≃ₗ[K] (Fin d → K) := matrixLinearEquiv ga.val.left
  let eB : (Fin d → K) ≃ₗ[K] (Fin d → K) := matrixLinearEquiv gb.val.left
  have hμA : ∀ v, Q (eA.toLinearMap v) = (multiplier Q ga : K) * Q v := by
    intro v
    have h := multiplier_spec Q ga v
    rw [coordinateSemilinearMap_right_one_eq_linear ga.val hgra] at h
    rw [hgra] at h
    simpa using h
  have hμB : ∀ v, Q (eB.toLinearMap v) = (multiplier Q gb : K) * Q v := by
    intro v
    have h := multiplier_spec Q gb v
    rw [coordinateSemilinearMap_right_one_eq_linear gb.val hgrb] at h
    rw [hgrb] at h
    simpa using h
  have hA2 : ∀ v, eA (eA v) = (cA : K) • v := by
    intro v
    have h1 := hA2σ v
    rw [coordinateSemilinearMap_right_one_eq_linear ga.val hgra] at h1
    exact h1
  have hB2 : ∀ v, eB (eB v) = (cB : K) • v := by
    intro v
    have h1 := hB2σ v
    rw [coordinateSemilinearMap_right_one_eq_linear gb.val hgrb] at h1
    exact h1
  have hAB : ∀ w, eA (eB w) = (cAB : K) • eB (eA w) := by
    intro w
    have h := hABσ w
    rw [coordinateSemilinearMap_right_one_eq_linear ga.val hgra,
      coordinateSemilinearMap_right_one_eq_linear gb.val hgrb] at h
    exact h
  have hdim : 9 ≤ Module.finrank K (Fin d → K) := by
    rw [Module.finrank_fin_fun]
    exact h9
  obtain ⟨W, hW0, hWsing, hWA, hWB⟩ :=
    exists_stable_singular_of_similitudes (K := K) (V := Fin d → K) h2 hnd
      (A := eA.toLinearMap) (B := eB.toLinearMap)
      (μA := (multiplier Q ga : K)) (μB := (multiplier Q gb : K))
      (α := (cA : K)) (β := (cB : K)) (ε := (cAB : K))
      hμA hμB hA2 hB2 (Units.ne_zero cA) (Units.ne_zero cB) hAB (Or.inl hdim)
  have hsta : ∀ w ∈ W, coordinateSemilinearMap ga.val w ∈ W := by
    intro w hw
    rw [coordinateSemilinearMap_right_one_eq_linear ga.val hgra]
    exact hWA w hw
  have hstb : ∀ w ∈ W, coordinateSemilinearMap gb.val w ∈ W := by
    intro w hw
    rw [coordinateSemilinearMap_right_one_eq_linear gb.val hgrb]
    exact hWB w hw
  have hstab := stable_of_generators hker (ga := ga) (gb := gb)
    (a := matrixProjectiveConjugationHom Q ga) (b := matrixProjectiveConjugationHom Q gb)
    rfl rfl hgen hsta hstb
  exact hW0 (hno W hWsing hstab)

@[expose] def SeitzFourOOuterAniso : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (d : ℕ) (Q : QuadraticForm K (Fin d → K)), (2 : K) ≠ 0 →
    7 ≤ d → d ≤ 8 → Q.polarBilin.Nondegenerate →
    (∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) →
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q →
    CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q) →
    ∀ E : Subgroup (MulAut (matrixProjectiveDerived Q)), IsElemAbelian 2 E → Nat.card E = 4 →
      E ≤ matrixProjectiveImage Q →
      ¬ E ≤ (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range →
      (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E → g.val.right = 1) →
      (∀ W : Submodule K (Fin d → K), (∀ x ∈ W, Q x = 0) →
        (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
          ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W) → W = ⊥) →
      PlaneGen E

theorem planeGen_outer_of_mem_image (hR : SeitzFourOOuterAniso) {K : Type} [Field K] [Finite K]
    {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (h2 : (2 : K) ≠ 0) (hd : 7 ≤ d)
    (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hEQ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q))
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (hEim : E ≤ matrixProjectiveImage Q)
    (hout : ¬ E ≤
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range) :
    PlaneGen E := by
  classical
  have hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a :=
    fun g => (CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff
      Q hnd hS3 hAP g).1
  have hder : elementaryGroup Q = orthDerived Q := hEQ.symm
  by_cases hW : ∃ W : Submodule K (Fin d → K), W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
        ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W)
  · obtain ⟨W, hW0, hWsing, hWst⟩ := hW
    exact planeGen_of_stable_singular h2 (by omega) hnd hder hker hE h4 hEim hW0 hWsing hWst
  · have hno : ∀ W : Submodule K (Fin d → K), (∀ x ∈ W, Q x = 0) →
        (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
          ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W) → W = ⊥ := by
      intro W hsing hst
      by_contra hne
      exact hW ⟨W, hne, hsing, hst⟩
    have hlin : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
        g.val.right = 1 :=
      right_eq_one_of_no_stable h2 hnd hker hE h4 hEim hno (by omega)
    have hd8 : d ≤ 8 := d_le_eight_of_no_stable h2 hnd hker hE h4 hEim hlin hno
    exact hR K d Q h2 hd hd8 hnd hS3 hEQ hAP E hE h4 hEim hout hlin hno

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
