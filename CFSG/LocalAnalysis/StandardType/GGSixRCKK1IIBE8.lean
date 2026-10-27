module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Steinberg.Adjoint.Comm
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.ExtraPairs
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Form
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcC2
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.E8

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.HighestRoot CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

private abbrev rckp8_j : Fin (Tag.rank .E8) := ⟨7, by decide⟩

private abbrev rckp8_θ : Fin (Tag.rank .E8) → ℤ := highRoot .E8

private abbrev rckp8_γ : Fin (Tag.rank .E8) → ℤ := reflect .E8 rckp8_j rckp8_θ

private theorem rckp8_elem_zero_or_one (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := GaloisField.card 2 1 (by decide)
  have hunits : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, hcard]
  haveI : Subsingleton (GaloisField 2 1)ˣ :=
    Finite.card_le_one_iff_subsingleton.mp (by rw [hunits])
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have h : (Units.mk0 c hc : (GaloisField 2 1)ˣ) = 1 := Subsingleton.elim _ _
    simpa using congrArg (fun u : (GaloisField 2 1)ˣ => (u : GaloisField 2 1)) h

private theorem rckp8_rootGroup_eq_zpowers :
    (e8Datum (GaloisField 2 1)).rootGroup rckp8_θ =
      Subgroup.zpowers (xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_θ 1) := by
  have hθ : IsRoot .E8 rckp8_θ := isRoot_highRoot .E8
  apply le_antisymm
  · intro g hg
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily .E8) hθ g).1 hg
    rcases rckp8_elem_zero_or_one c with rfl | rfl
    · rw [xPar_zero]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (xPar_mem hθ 1)

private def rckp8_T {G : Type*} [Group G] (x y : G) (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy : x * y = y * x) : Subgroup G where
  carrier := {1, x, y, x * y}
  mul_mem' := by
    have h_yx : y * x = x * y := hxy.symm
    have h_xxy : x * (x * y) = y := by rw [← mul_assoc, hx2, one_mul]
    have h_yxy : y * (x * y) = x := by rw [← mul_assoc, hxy.symm, mul_assoc, hy2, mul_one]
    have h_xyx : (x * y) * x = y := by rw [mul_assoc, hxy.symm, ← mul_assoc, hx2, one_mul]
    have h_xyy : (x * y) * y = x := by rw [mul_assoc, hy2, mul_one]
    have h_xyxy : (x * y) * (x * y) = 1 := by
      have hcomm : Commute x y := hxy
      have h2 : (x * y) ^ 2 = 1 := by
        rw [hcomm.mul_pow]
        rw [show x ^ 2 = 1 by rw [pow_two]; exact hx2,
          show y ^ 2 = 1 by rw [pow_two]; exact hy2, mul_one]
      rwa [pow_two] at h2
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [one_mul])
    · exact Or.inr (Or.inl (by rw [one_mul]))
    · exact Or.inr (Or.inr (Or.inl (by rw [one_mul])))
    · exact Or.inr (Or.inr (Or.inr (by rw [one_mul])))
    · exact Or.inr (Or.inl (by rw [mul_one]))
    · exact Or.inl hx2
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl h_xxy))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_one])))
    · exact Or.inr (Or.inr (Or.inr h_yx))
    · exact Or.inl hy2
    · exact Or.inr (Or.inl h_yxy)
    · exact Or.inr (Or.inr (Or.inr (by rw [mul_one])))
    · exact Or.inr (Or.inr (Or.inl h_xyx))
    · exact Or.inr (Or.inl h_xyy)
    · exact Or.inl h_xyxy
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · left; exact inv_one
    · right; left; exact inv_eq_of_mul_eq_one_right hx2
    · right; right; left; exact inv_eq_of_mul_eq_one_right hy2
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2]
      exact hxy.symm

private theorem rckp8_T_mem {G : Type*} [Group G] {x y : G} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy : x * y = y * x) {v : G} :
    v ∈ rckp8_T x y hx2 hy2 hxy ↔ v = 1 ∨ v = x ∨ v = y ∨ v = x * y := by
  change v ∈ ({1, x, y, x * y} : Set G) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem rckp8_T_card {G : Type*} [Group G] {x y : G}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxney : x ≠ y) (hxy_ne1 : x * y ≠ 1) (hxy_nex : x * y ≠ x)
    (hxy_ney : x * y ≠ y) :
    Nat.card (rckp8_T x y hx2 hy2 hxy) = 4 := by
  classical
  let s : Finset G := {1, x, y, x * y}
  have H : ∀ z, z ∈ s ↔ z ∈ (rckp8_T x y hx2 hy2 hxy : Set G) := by
    intro z
    change z ∈ s ↔ z ∈ ({1, x, y, x * y} : Set G)
    simp only [s, Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  letI : Fintype ↑(rckp8_T x y hx2 hy2 hxy : Set G) := Fintype.ofFinset s H
  rw [show Nat.card ↥(rckp8_T x y hx2 hy2 hxy) =
      Nat.card ↑(rckp8_T x y hx2 hy2 hxy : Set G) from rfl, Nat.card_eq_fintype_card,
    Fintype.card_ofFinset s H]
  rw [show s.card = 4 from by
    rw [Finset.card_eq_four]
    exact ⟨1, x, y, x * y, hx1.symm, hy1.symm, hxy_ne1.symm, hxney, hxy_nex.symm,
      hxy_ney.symm, rfl⟩]

theorem rckIIPair_E8
    (n : ℕ) (hadm : StatedLieAdmissible .E8 n 2 1) : RCKIIPair .E8 n := by
  have hθ : IsRoot .E8 rckp8_θ := isRoot_highRoot .E8
  have hθmem : rckp8_θ ∈ (e8Datum (GaloisField 2 1)).roots := mem_adjDatum_roots.2 hθ
  have hγ : IsRoot .E8 rckp8_γ := IsRoot.reflect _ hθ
  have hγmem : rckp8_γ ∈ (e8Datum (GaloisField 2 1)).roots := mem_adjDatum_roots.2 hγ
  have hsym : ∀ i j, (e8Datum (GaloisField 2 1)).cartan i j =
      (e8Datum (GaloisField 2 1)).cartan j i := cartanE_symm 8
  have hlong : GGLongRoot (e8Datum (GaloisField 2 1)) rckp8_θ :=
    ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E8 hsym rfl hθmem
  let x : ↥(adjointGroup .E8 (GaloisField 2 1)) :=
    xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_θ 1
  let y : ↥(adjointGroup .E8 (GaloisField 2 1)) :=
    xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_γ 1
  have hx2 : x * x = 1 := by
    change xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_θ 1 *
      xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_θ 1 = 1
    have h2 : (2 : GaloisField 2 1) = 0 := CharP.cast_eq_zero (GaloisField 2 1) 2
    have h11 : (1 : GaloisField 2 1) + 1 = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [← xPar_add, h11, xPar_zero]
  have hx1 : x ≠ 1 := by
    intro h
    have h10 : (1 : GaloisField 2 1) = 0 :=
      xPar_injective (F := rootOperatorFamily .E8) hθ (by
        rw [show xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_θ 1 = x from rfl,
          h, xPar_zero])
    exact one_ne_zero h10
  have hy2 : y * y = 1 := by
    change xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_γ 1 *
      xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_γ 1 = 1
    have h2 : (2 : GaloisField 2 1) = 0 := CharP.cast_eq_zero (GaloisField 2 1) 2
    have h11 : (1 : GaloisField 2 1) + 1 = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [← xPar_add, h11, xPar_zero]
  have hy1 : y ≠ 1 := by
    intro h
    have h10 : (1 : GaloisField 2 1) = 0 :=
      xPar_injective (F := rootOperatorFamily .E8) hγ (by
        rw [show xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) rckp8_γ 1 = y from rfl,
          h, xPar_zero])
    exact one_ne_zero h10
  have hθh : height rckp8_θ = 29 := by decide +kernel
  have hγh : height rckp8_γ = 28 := by decide +kernel
  have hθγh : height (rckp8_θ + rckp8_γ) = 57 := by decide +kernel
  have hθγ_ne : rckp8_θ + rckp8_γ ≠ 0 := by
    intro h
    have := congrFun h rckp8_j
    rw [show (rckp8_θ + rckp8_γ) rckp8_j = 3 by decide +kernel, Pi.zero_apply] at this
    omega
  have hθγ_notroot : ¬ IsRoot .E8 (rckp8_θ + rckp8_γ) := by
    intro h
    have := height_le_height_highRoot (τ := .E8) h
    rw [hθγh, hθh] at this
    omega
  have hcomm : Commute x y :=
    commute_xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) e8Data_valid noG2_E8
      hθ hγ hθγ_ne hθγ_notroot (1 : GaloisField 2 1) 1
  have hxy : x * y = y * x := hcomm.eq
  have hγθ : rckp8_γ - rckp8_θ = -Pi.single rckp8_j (1 : ℤ) := by
    ext j
    fin_cases j <;> decide +kernel
  have hγθmem : rckp8_γ - rckp8_θ ∈ (e8Datum (GaloisField 2 1)).roots := by
    rw [hγθ]
    exact mem_adjDatum_roots.2 (IsRoot.neg (isRoot_single .E8 rckp8_j))
  have hne : (rckp8_γ - rckp8_θ) + rckp8_θ ≠ 0 := by
    rw [sub_add_cancel]
    intro h
    have := congrFun h rckp8_j
    rw [show rckp8_γ rckp8_j = 1 by decide +kernel, Pi.zero_apply] at this
    omega
  have hst := (CFSG.GroupTheory.GomiLeviExc.E8.isCharTwoSteinberg
      (K := GaloisField 2 1)).2 (rckp8_γ - rckp8_θ) hγθmem rckp8_θ hθmem hne
    (1 : GaloisField 2 1) 1
  have hcomm_z : ⁅xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) (rckp8_γ - rckp8_θ) 1,
      x⁆ = y := by
    rw [show (rckp8_γ - rckp8_θ) + rckp8_θ = rckp8_γ from sub_add_cancel _ _, if_pos hγmem,
      mul_one] at hst
    exact hst
  have hγθ_ne : rckp8_γ ≠ rckp8_θ := by
    intro h
    have := congrFun h rckp8_j
    rw [show rckp8_γ rckp8_j = 1 by decide +kernel,
      show rckp8_θ rckp8_j = 2 by decide +kernel] at this
    omega
  have hxney : x ≠ y := by
    intro hxy_eq
    have hpi := prodInjective (F := rootOperatorFamily .E8) (K := GaloisField 2 1)
      (Pi.evalAddMonoidHom (fun _ => ℤ) rckp8_j) [rckp8_γ, rckp8_θ]
      (by
        rw [List.nodup_cons, List.nodup_cons]
        exact ⟨fun hm => hγθ_ne (List.mem_singleton.mp hm),
          List.not_mem_nil, List.nodup_nil⟩)
      (by
        intro δ hδ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
        rcases hδ with rfl | rfl
        · exact ⟨hγ, by decide +kernel⟩
        · exact ⟨hθ, by decide +kernel⟩)
      (by
        rw [List.pairwise_cons]
        exact ⟨fun b hb => by
          rw [List.mem_singleton] at hb
          subst hb
          show (Pi.evalAddMonoidHom (fun _ => ℤ) rckp8_j) rckp8_γ ≤
            (Pi.evalAddMonoidHom (fun _ => ℤ) rckp8_j) rckp8_θ
          decide +kernel, by simp⟩)
    let f : (Fin (Tag.rank .E8) → ℤ) → ↥(adjointGroup .E8 (GaloisField 2 1)) :=
      fun δ => if δ = rckp8_γ then y else if δ = rckp8_θ then x else 1
    let g : (Fin (Tag.rank .E8) → ℤ) → ↥(adjointGroup .E8 (GaloisField 2 1)) := fun _ => 1
    have hf : ∀ δ ∈ [rckp8_γ, rckp8_θ], f δ ∈ (e8Datum (GaloisField 2 1)).rootGroup δ := by
      intro δ hδ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
      rcases hδ with rfl | rfl
      · exact xPar_mem hγ 1
      · exact xPar_mem hθ 1
    have hg : ∀ δ ∈ [rckp8_γ, rckp8_θ], g δ ∈ (e8Datum (GaloisField 2 1)).rootGroup δ := by
      intro δ hδ
      exact Subgroup.one_mem _
    have hprod : ([rckp8_γ, rckp8_θ].map f).prod = ([rckp8_γ, rckp8_θ].map g).prod := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      show f rckp8_γ * f rckp8_θ = 1
      simp only [f, if_pos rfl, if_neg (Ne.symm hγθ_ne), g]
      rw [← hxy_eq]
      exact hx2
    have h1 := hpi f g hf hg hprod rckp8_γ (by simp)
    simp only [f, if_pos rfl, g] at h1
    exact hy1 h1
  have hxy_ne1 : x * y ≠ 1 := by
    intro h
    apply hxney
    calc x = x * 1 := (mul_one x).symm
      _ = x * (x * y) := by rw [h, mul_one]
      _ = (x * x) * y := (mul_assoc x x y).symm
      _ = y := by rw [hx2, one_mul]
  have hxy_nex : x * y ≠ x := by
    intro h
    apply hy1
    calc y = 1 * y := (one_mul y).symm
      _ = (x * x) * y := by rw [hx2]
      _ = x * (x * y) := mul_assoc x x y
      _ = x * x := by rw [h]
      _ = 1 := hx2
  have hxy_ney : x * y ≠ y := by
    intro h
    apply hx1
    calc x = x * 1 := (mul_one x).symm
      _ = x * (y * y) := by rw [hy2, mul_one]
      _ = (x * y) * y := (mul_assoc x y y).symm
      _ = y * y := by rw [h]
      _ = 1 := hy2
  have hVT : Subgroup.closure ({x, y} : Set ↥(adjointGroup .E8 (GaloisField 2 1))) =
      rckp8_T x y hx2 hy2 hxy := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (rckp8_T_mem hx2 hy2 hxy).mpr (Or.inr (Or.inl rfl))
      · exact (rckp8_T_mem hx2 hy2 hxy).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · intro z hz
      rw [rckp8_T_mem hx2 hy2 hxy] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
      · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl)))
          (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl)))
  have hwconj : ∃ w : ↥(adjointGroup .E8 (GaloisField 2 1)), w * x * w⁻¹ = y := by
    obtain ⟨ε, hε, hconj⟩ := weylElement_xPar_conj (F := rootOperatorFamily .E8)
      (K := GaloisField 2 1) rckp8_j hθ
    refine ⟨CFSG.LieType.Steinberg.weylElement
      (xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1)) rckp8_j
      (1 : (GaloisField 2 1)ˣ), ?_⟩
    have h := hconj (1 : (GaloisField 2 1)ˣ) 1
    have hrefl : CFSG.LieType.RootSystem.reflection (Tag.cartan .E8) rckp8_j rckp8_θ =
        rckp8_γ := by
      rw [CFSG.LieType.RootSystem.reflection_apply]
      rfl
    have hεK : ((ε : ℤ) : GaloisField 2 1) = 1 := by
      rcases hε with rfl | rfl
      · norm_num
      · simpa using CharTwo.neg_eq (1 : GaloisField 2 1)
    simpa only [Units.val_one, one_zpow, mul_one, one_mul, hrefl, hεK] using h
  have hθθpos : 0 < rootForm (e8Datum (GaloisField 2 1)) rckp8_θ rckp8_θ := by
    obtain ⟨c, hc, hform⟩ := CFSG.ClassicalInvolution.ModelFacts.Levi.form_eq_iform_tag .E8
      (e8Datum (GaloisField 2 1)).isFiniteType
    rw [rootForm, hform rckp8_θ rckp8_θ, show iform rckp8_θ rckp8_θ = 2 by decide +kernel]
    exact mul_pos hc (by norm_num)
  have hγθpos : 0 < rootForm (e8Datum (GaloisField 2 1)) rckp8_γ rckp8_θ := by
    obtain ⟨c, hc, hform⟩ := CFSG.ClassicalInvolution.ModelFacts.Levi.form_eq_iform_tag .E8
      (e8Datum (GaloisField 2 1)).isFiniteType
    rw [rootForm, hform rckp8_γ rckp8_θ, show iform rckp8_γ rckp8_θ = 1 by decide +kernel]
    exact mul_pos hc (by norm_num)
  unfold RCKIIPair
  change ∃ (β : Fin (e8Datum (GaloisField 2 1)).rank → ℤ)
      (x : ↥(adjointGroup .E8 (GaloisField 2 1)))
      (V : Subgroup ↥(adjointGroup .E8 (GaloisField 2 1))),
    β ∈ (e8Datum (GaloisField 2 1)).roots ∧
    GGLongRoot (e8Datum (GaloisField 2 1)) β ∧
    (e8Datum (GaloisField 2 1)).rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
    x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
    V ≤ pCoreOf 2 (Subgroup.normalizer ((e8Datum (GaloisField 2 1)).rootGroup β :
      Set ↥(adjointGroup .E8 (GaloisField 2 1)))) ∧
    ∀ v ∈ V, v ≠ 1 → ∃ j : ↥(adjointGroup .E8 (GaloisField 2 1)), v = j * x * j⁻¹
  refine ⟨rckp8_θ, x, Subgroup.closure {x, y}, hθmem, hlong, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (e8Datum (GaloisField 2 1)).rootGroup rckp8_θ = Subgroup.zpowers x
    exact rckp8_rootGroup_eq_zpowers
  · exact hx2
  · exact hx1
  · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
  ·
    change IsMulCommutative (Subgroup.closure ({x, y} : Set _)) ∧
      ∀ a ∈ Subgroup.closure ({x, y} : Set _), a ^ 2 = 1
    constructor
    · refine Subgroup.isMulCommutative_closure (by
        intro a ha b hb hab
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact hcomm
        · exact hcomm.symm
        · exact absurd rfl hab)
    · intro a ha
      have ha1 : a ∈ rckp8_T x y hx2 hy2 hxy := hVT ▸ ha
      have ha' := (rckp8_T_mem hx2 hy2 hxy).mp ha1
      rcases ha' with rfl | rfl | rfl | rfl
      · rw [pow_two, one_mul]
      · rw [pow_two]; exact hx2
      · rw [pow_two]; exact hy2
      · rw [pow_two]
        have hcomm : Commute x y := hxy
        have h2 : (x * y) ^ 2 = 1 := by
          rw [hcomm.mul_pow]
          rw [show x ^ 2 = 1 by rw [pow_two]; exact hx2,
            show y ^ 2 = 1 by rw [pow_two]; exact hy2, mul_one]
        rwa [pow_two] at h2
  ·
    rw [hVT]
    exact rckp8_T_card hx2 hy2 hxy hx1 hy1 hxney hxy_ne1 hxy_nex hxy_ney
  ·
    change Subgroup.closure ({x, y} : Set ↥(adjointGroup .E8 (GaloisField 2 1))) ≤
      pCoreOf 2 (Subgroup.normalizer (((e8Datum (GaloisField 2 1)).rootGroup rckp8_θ :
        Subgroup ↥(adjointGroup .E8 (GaloisField 2 1))) : Set _))
    rw [show pCoreOf 2 (Subgroup.normalizer (((e8Datum (GaloisField 2 1)).rootGroup rckp8_θ :
        Subgroup ↥(adjointGroup .E8 (GaloisField 2 1))) : Set _)) =
        highestRootRadical (e8Datum (GaloisField 2 1)) rckp8_θ from
      CFSG.StandardType.LieKnownR2.Exc.pCoreOf_normalizer_rootGroup_highRoot_adj .E8
        (Or.inr (Or.inr rfl)) (GaloisField 2 1)]
    rw [hVT]
    intro v hv
    rw [rckp8_T_mem hx2 hy2 hxy] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_iSup_of_mem rckp8_θ
        (Subgroup.mem_iSup_of_mem ⟨hθmem, hθθpos⟩ (xPar_mem hθ 1))
    · exact Subgroup.mem_iSup_of_mem rckp8_γ
        (Subgroup.mem_iSup_of_mem ⟨hγmem, hγθpos⟩ (xPar_mem hγ 1))
    · exact Subgroup.mul_mem _
        (Subgroup.mem_iSup_of_mem rckp8_θ
          (Subgroup.mem_iSup_of_mem ⟨hθmem, hθθpos⟩ (xPar_mem hθ 1)))
        (Subgroup.mem_iSup_of_mem rckp8_γ
          (Subgroup.mem_iSup_of_mem ⟨hγmem, hγθpos⟩ (xPar_mem hγ 1)))
  ·
    intro v hv hv1
    rw [hVT, rckp8_T_mem hx2 hy2 hxy] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · exact ⟨1, by group⟩
    · obtain ⟨w, hw⟩ := hwconj
      exact ⟨w, hw.symm⟩
    · refine ⟨xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) (rckp8_γ - rckp8_θ) 1,
        ?_⟩
      have hz : xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1) (rckp8_γ - rckp8_θ) 1 *
          x * (xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1)
            (rckp8_γ - rckp8_θ) 1)⁻¹ = x * y := by
        have h1 : xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1)
            (rckp8_γ - rckp8_θ) 1 * x *
            (xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1)
              (rckp8_γ - rckp8_θ) 1)⁻¹ =
            ⁅xPar (F := rootOperatorFamily .E8) (K := GaloisField 2 1)
              (rckp8_γ - rckp8_θ) 1, x⁆ * x := by
          rw [commutatorElement_def]
          group
        rw [h1, hcomm_z, ← hxy]
      exact hz.symm

end CFSG.StandardType.RCKK1II
