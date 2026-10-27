module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBE7Aux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcC2
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Steinberg.Adjoint.Comm
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.CertE7
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Form

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.HighestRoot CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

private abbrev rckp7_j : Fin (Tag.rank .E7) := ⟨0, by decide⟩

private abbrev rckp7_θ : Fin (Tag.rank .E7) → ℤ := highRoot .E7

private abbrev rckp7_γ : Fin (Tag.rank .E7) → ℤ := reflect .E7 rckp7_j rckp7_θ

abbrev rckp7_G : Type := ↥(adjointGroup .E7 (GaloisField 2 1))

noncomputable abbrev rckp7_D :
    UniversalRootDatum rckp7_G :=
  adjDatum (rootOperatorFamily .E7) (GaloisField 2 1)

private theorem rckp7_rootGroup_eq_zpowers :
    rckp7_D.rootGroup rckp7_θ =
      Subgroup.zpowers (xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
        rckp7_θ 1) := by
  have hθ : IsRoot .E7 rckp7_θ := isRoot_highRoot .E7
  apply le_antisymm
  · intro g hg
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := rootOperatorFamily .E7) hθ g).1 hg
    rcases rckp7_elem_zero_or_one c with rfl | rfl
    · rw [xPar_zero]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (xPar_mem hθ 1)

theorem rckIIPairAdj_E7 :
    ∃ (β : Fin (Tag.rank .E7) → ℤ) (x : rckp7_G) (V : Subgroup rckp7_G),
      β ∈ rckp7_D.roots ∧ GGLongRoot rckp7_D β ∧
      rckp7_D.rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
      x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      V ≤ pCoreOf 2 (Subgroup.normalizer ((rckp7_D.rootGroup β : Subgroup rckp7_G) : Set rckp7_G)) ∧
      ∀ v ∈ V, v ≠ 1 → ∃ j : rckp7_G, v = j * x * j⁻¹ := by
  have hθ : IsRoot .E7 rckp7_θ := isRoot_highRoot .E7
  have hθmem : rckp7_θ ∈ rckp7_D.roots := mem_adjDatum_roots.2 hθ
  have hγ : IsRoot .E7 rckp7_γ := IsRoot.reflect _ hθ
  have hγmem : rckp7_γ ∈ rckp7_D.roots := mem_adjDatum_roots.2 hγ
  have hsym : ∀ i j, rckp7_D.cartan i j = rckp7_D.cartan j i := cartanE_symm 7
  have hlong : GGLongRoot rckp7_D rckp7_θ :=
    ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7 hsym rfl hθmem
  let x : rckp7_G := xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_θ 1
  let y : rckp7_G := xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_γ 1
  have hx2 : x * x = 1 := by
    change xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_θ 1 *
      xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_θ 1 = 1
    have h2 : (2 : GaloisField 2 1) = 0 := CharP.cast_eq_zero (GaloisField 2 1) 2
    have h11 : (1 : GaloisField 2 1) + 1 = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [← xPar_add, h11, xPar_zero]
  have hx1 : x ≠ 1 := by
    intro h
    have h10 : (1 : GaloisField 2 1) = 0 :=
      xPar_injective (F := rootOperatorFamily .E7) hθ (by
        rw [show xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_θ 1 = x
          from rfl, h, xPar_zero])
    exact one_ne_zero h10
  have hy2 : y * y = 1 := by
    change xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_γ 1 *
      xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_γ 1 = 1
    have h2 : (2 : GaloisField 2 1) = 0 := CharP.cast_eq_zero (GaloisField 2 1) 2
    have h11 : (1 : GaloisField 2 1) + 1 = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [← xPar_add, h11, xPar_zero]
  have hy1 : y ≠ 1 := by
    intro h
    have h10 : (1 : GaloisField 2 1) = 0 :=
      xPar_injective (F := rootOperatorFamily .E7) hγ (by
        rw [show xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) rckp7_γ 1 = y
          from rfl, h, xPar_zero])
    exact one_ne_zero h10
  have hθh : height rckp7_θ = 17 := by decide +kernel
  have hγh : height rckp7_γ = 16 := by decide +kernel
  have hθγh : height (rckp7_θ + rckp7_γ) = 33 := by decide +kernel
  have hθγ_ne : rckp7_θ + rckp7_γ ≠ 0 := by
    intro h
    have := congrFun h rckp7_j
    rw [show (rckp7_θ + rckp7_γ) rckp7_j = 3 by decide +kernel, Pi.zero_apply] at this
    omega
  have hθγ_notroot : ¬ IsRoot .E7 (rckp7_θ + rckp7_γ) := by
    intro h
    have := height_le_height_highRoot (τ := .E7) h
    rw [hθγh, hθh] at this
    omega
  have hcomm : Commute x y :=
    commute_xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1) e7AdjData_valid noG2_E7
      hθ hγ hθγ_ne hθγ_notroot (1 : GaloisField 2 1) 1
  have hxy : x * y = y * x := hcomm.eq
  have hγθ : rckp7_γ - rckp7_θ = -Pi.single rckp7_j (1 : ℤ) := by
    ext j
    fin_cases j <;> decide +kernel
  have hγθmem : rckp7_γ - rckp7_θ ∈ rckp7_D.roots := by
    rw [hγθ]
    exact mem_adjDatum_roots.2 (IsRoot.neg (isRoot_single .E7 rckp7_j))
  have hα : IsRoot .E7 (rckp7_γ - rckp7_θ) := mem_adjDatum_roots.1 hγθmem
  have hαβ_ne : rckp7_γ - rckp7_θ ≠ rckp7_θ := by
    intro h
    have := congrFun h rckp7_j
    rw [show (rckp7_γ - rckp7_θ) rckp7_j = -1 by decide +kernel,
      show rckp7_θ rckp7_j = 2 by decide +kernel] at this
    omega
  have hαβ'_ne : rckp7_γ - rckp7_θ ≠ -rckp7_θ := by
    intro h
    have := congrFun h rckp7_j
    rw [show (rckp7_γ - rckp7_θ) rckp7_j = -1 by decide +kernel,
      show (-rckp7_θ) rckp7_j = -2 by decide +kernel] at this
    omega
  have h12 : ¬ IsRoot .E7 ((rckp7_γ - rckp7_θ) + 2 • rckp7_θ) :=
    rckp7_not_isRoot_add_two_smul hα hθ hαβ_ne hαβ'_ne
  have h21 : ¬ IsRoot .E7 (2 • (rckp7_γ - rckp7_θ) + rckp7_θ) :=
    rckp7_not_isRoot_two_smul_add hα hθ hαβ_ne hαβ'_ne
  have hcomm_z : ⁅xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
      (rckp7_γ - rckp7_θ) 1, x⁆ = y := by
    have hc := commutator_xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
      e7AdjData_valid noG2_E7 hα hθ hαβ_ne hαβ'_ne (1 : GaloisField 2 1) 1
    rw [xPar_of_not_isRoot (K := GaloisField 2 1) h12,
      xPar_of_not_isRoot (K := GaloisField 2 1) h21] at hc
    rw [show (rckp7_γ - rckp7_θ) + rckp7_θ = rckp7_γ from sub_add_cancel _ _,
      rckp7_coeff11_eq_one hα hθ hαβ'_ne (by rw [sub_add_cancel]; exact hγ)] at hc
    simpa only [one_mul, mul_one] using hc
  have hγθ_ne : rckp7_γ ≠ rckp7_θ := by
    intro h
    have := congrFun h rckp7_j
    rw [show rckp7_γ rckp7_j = 1 by decide +kernel,
      show rckp7_θ rckp7_j = 2 by decide +kernel] at this
    omega
  have hxney : x ≠ y := by
    intro hxy_eq
    have hpi := prodInjective (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
      (Pi.evalAddMonoidHom (fun _ => ℤ) rckp7_j) [rckp7_γ, rckp7_θ]
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
          show (Pi.evalAddMonoidHom (fun _ => ℤ) rckp7_j) rckp7_γ ≤
            (Pi.evalAddMonoidHom (fun _ => ℤ) rckp7_j) rckp7_θ
          decide +kernel, by simp⟩)
    let f : (Fin (Tag.rank .E7) → ℤ) → rckp7_G :=
      fun δ => if δ = rckp7_γ then y else if δ = rckp7_θ then x else 1
    let g : (Fin (Tag.rank .E7) → ℤ) → rckp7_G := fun _ => 1
    have hf : ∀ δ ∈ [rckp7_γ, rckp7_θ], f δ ∈ rckp7_D.rootGroup δ := by
      intro δ hδ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hδ
      rcases hδ with rfl | rfl
      · exact xPar_mem hγ 1
      · exact xPar_mem hθ 1
    have hg : ∀ δ ∈ [rckp7_γ, rckp7_θ], g δ ∈ rckp7_D.rootGroup δ := by
      intro δ hδ
      exact Subgroup.one_mem _
    have hprod : ([rckp7_γ, rckp7_θ].map f).prod = ([rckp7_γ, rckp7_θ].map g).prod := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      show f rckp7_γ * f rckp7_θ = 1
      simp only [f, if_pos rfl, if_neg (Ne.symm hγθ_ne), g]
      rw [← hxy_eq]
      exact hx2
    have h1 := hpi f g hf hg hprod rckp7_γ (by simp)
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
  have hVT : Subgroup.closure ({x, y} : Set rckp7_G) = rckp7_T x y hx2 hy2 hxy := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (rckp7_T_mem hx2 hy2 hxy).mpr (Or.inr (Or.inl rfl))
      · exact (rckp7_T_mem hx2 hy2 hxy).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · intro z hz
      rw [rckp7_T_mem hx2 hy2 hxy] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
      · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl)))
          (Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl)))
  have hwconj : ∃ w : rckp7_G, w * x * w⁻¹ = y := by
    obtain ⟨ε, hε, hconj⟩ := weylElement_xPar_conj (F := rootOperatorFamily .E7)
      (K := GaloisField 2 1) rckp7_j hθ
    refine ⟨CFSG.LieType.Steinberg.weylElement
      (xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)) rckp7_j
      (1 : (GaloisField 2 1)ˣ), ?_⟩
    have h := hconj (1 : (GaloisField 2 1)ˣ) 1
    have hrefl : CFSG.LieType.RootSystem.reflection (Tag.cartan .E7) rckp7_j rckp7_θ =
        rckp7_γ := by
      rw [CFSG.LieType.RootSystem.reflection_apply]
      rfl
    have hεK : ((ε : ℤ) : GaloisField 2 1) = 1 := by
      rcases hε with rfl | rfl
      · norm_num
      · simpa using CharTwo.neg_eq (1 : GaloisField 2 1)
    simpa only [Units.val_one, one_zpow, mul_one, one_mul, hrefl, hεK] using h
  have hθθpos : 0 < rootForm rckp7_D rckp7_θ rckp7_θ := by
    obtain ⟨c, hc, hform⟩ := CFSG.ClassicalInvolution.ModelFacts.Levi.form_eq_iform_tag .E7
      rckp7_D.isFiniteType
    rw [rootForm, hform rckp7_θ rckp7_θ, show iform rckp7_θ rckp7_θ = 2 by decide +kernel]
    exact mul_pos hc (by norm_num)
  have hγθpos : 0 < rootForm rckp7_D rckp7_γ rckp7_θ := by
    obtain ⟨c, hc, hform⟩ := CFSG.ClassicalInvolution.ModelFacts.Levi.form_eq_iform_tag .E7
      rckp7_D.isFiniteType
    rw [rootForm, hform rckp7_γ rckp7_θ, show iform rckp7_γ rckp7_θ = 1 by decide +kernel]
    exact mul_pos hc (by norm_num)
  refine ⟨rckp7_θ, x, Subgroup.closure {x, y}, hθmem, hlong, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change rckp7_D.rootGroup rckp7_θ = Subgroup.zpowers x
    exact rckp7_rootGroup_eq_zpowers
  · exact hx2
  · exact hx1
  · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
  · change IsMulCommutative (Subgroup.closure ({x, y} : Set rckp7_G)) ∧
      ∀ a ∈ Subgroup.closure ({x, y} : Set rckp7_G), a ^ 2 = 1
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
      have ha1 : a ∈ rckp7_T x y hx2 hy2 hxy := hVT ▸ ha
      have ha' := (rckp7_T_mem hx2 hy2 hxy).mp ha1
      rcases ha' with rfl | rfl | rfl | rfl
      · rw [pow_two, one_mul]
      · rw [pow_two]; exact hx2
      · rw [pow_two]; exact hy2
      · rw [pow_two]
        have hcomm' : Commute x y := hxy
        have h2 : (x * y) ^ 2 = 1 := by
          rw [hcomm'.mul_pow]
          rw [show x ^ 2 = 1 by rw [pow_two]; exact hx2,
            show y ^ 2 = 1 by rw [pow_two]; exact hy2, mul_one]
        rwa [pow_two] at h2
  · rw [hVT]
    exact rckp7_T_card hx2 hy2 hxy hx1 hy1 hxney hxy_ne1 hxy_nex hxy_ney
  · change Subgroup.closure ({x, y} : Set rckp7_G) ≤
      pCoreOf 2 (Subgroup.normalizer ((rckp7_D.rootGroup rckp7_θ : Subgroup rckp7_G) : Set rckp7_G))
    rw [show pCoreOf 2 (Subgroup.normalizer ((rckp7_D.rootGroup rckp7_θ :
        Subgroup rckp7_G) : Set rckp7_G)) =
        highestRootRadical rckp7_D rckp7_θ from
      CFSG.StandardType.LieKnownR2.Exc.pCoreOf_normalizer_rootGroup_highRoot_adj .E7
        (Or.inr (Or.inl rfl)) (GaloisField 2 1)]
    rw [hVT]
    intro v hv
    rw [rckp7_T_mem hx2 hy2 hxy] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_iSup_of_mem rckp7_θ
        (Subgroup.mem_iSup_of_mem ⟨hθmem, hθθpos⟩ (xPar_mem hθ 1))
    · exact Subgroup.mem_iSup_of_mem rckp7_γ
        (Subgroup.mem_iSup_of_mem ⟨hγmem, hγθpos⟩ (xPar_mem hγ 1))
    · exact Subgroup.mul_mem _
        (Subgroup.mem_iSup_of_mem rckp7_θ
          (Subgroup.mem_iSup_of_mem ⟨hθmem, hθθpos⟩ (xPar_mem hθ 1)))
        (Subgroup.mem_iSup_of_mem rckp7_γ
          (Subgroup.mem_iSup_of_mem ⟨hγmem, hγθpos⟩ (xPar_mem hγ 1)))
  · intro v hv hv1
    rw [hVT, rckp7_T_mem hx2 hy2 hxy] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · exact ⟨1, by group⟩
    · obtain ⟨w, hw⟩ := hwconj
      exact ⟨w, hw.symm⟩
    · refine ⟨xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
        (rckp7_γ - rckp7_θ) 1, ?_⟩
      have hz : xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
          (rckp7_γ - rckp7_θ) 1 * x *
          (xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
            (rckp7_γ - rckp7_θ) 1)⁻¹ = x * y := by
        have h1 : xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
            (rckp7_γ - rckp7_θ) 1 * x *
            (xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
              (rckp7_γ - rckp7_θ) 1)⁻¹ =
            ⁅xPar (F := rootOperatorFamily .E7) (K := GaloisField 2 1)
              (rckp7_γ - rckp7_θ) 1, x⁆ * x := by
          rw [commutatorElement_def]
          group
        rw [h1, hcomm_z, ← hxy]
      exact hz.symm

end CFSG.StandardType.RCKK1II
