module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameCore
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5PlainFix

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section FrameF4

private def g5_betaF4 : Fin 4 → (Fin (langTag .F4).rank → ℤ) :=
  ![![1, 0, 0, 0], ![1, 2, 2, 0], ![0, 0, 1, 0], ![1, 2, 3, 2]]

private theorem g5_betaF4_mem : ∀ i, g5_betaF4 i ∈ rootFinset (langTag .F4) := by decide +kernel

private theorem g5_betaF4_isRoot
    (i : Fin 4) : IsRoot (langTag .F4) (g5_betaF4 i) :=
  mem_rootFinset.1 (g5_betaF4_mem i)

private theorem g5_betaF4_norm0 :
    iform (τ := Tag.F4) (g5_betaF4 0) (g5_betaF4 0) = 4 := by decide +kernel

private theorem g5_betaF4_norm2 :
    iform (τ := Tag.F4) (g5_betaF4 2) (g5_betaF4 2) = 2 := by decide +kernel

private theorem g5_f4_length_split :
    ∀ v ∈ rootFinset (langTag .F4), iform v v = 4 ∨ iform v v = 2 := by decide +kernel

private theorem g5_f4_not_root_mem
    {v : Fin (langTag .F4).rank → ℤ}
    (h : v ∉ rootFinset (langTag .F4)) : ¬ IsRoot (langTag .F4) v :=
  fun hv => h (mem_rootFinset.2 hv)

private theorem g5_f4_orth01
    :
    iform (g5_betaF4 0) (g5_betaF4 1) = 0 ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 0 + g5_betaF4 1) ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 0 - g5_betaF4 1) :=
  ⟨by decide +kernel, g5_f4_not_root_mem (by decide +kernel),
    g5_f4_not_root_mem (by decide +kernel)⟩

private theorem g5_f4_orth02
    :
    iform (g5_betaF4 0) (g5_betaF4 2) = 0 ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 0 + g5_betaF4 2) ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 0 - g5_betaF4 2) :=
  ⟨by decide +kernel, g5_f4_not_root_mem (by decide +kernel),
    g5_f4_not_root_mem (by decide +kernel)⟩

private theorem g5_f4_orth03
    :
    iform (g5_betaF4 0) (g5_betaF4 3) = 0 ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 0 + g5_betaF4 3) ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 0 - g5_betaF4 3) :=
  ⟨by decide +kernel, g5_f4_not_root_mem (by decide +kernel),
    g5_f4_not_root_mem (by decide +kernel)⟩

private theorem g5_f4_orth12
    :
    iform (g5_betaF4 1) (g5_betaF4 2) = 0 ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 1 + g5_betaF4 2) ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 1 - g5_betaF4 2) :=
  ⟨by decide +kernel, g5_f4_not_root_mem (by decide +kernel),
    g5_f4_not_root_mem (by decide +kernel)⟩

private theorem g5_f4_orth13
    :
    iform (g5_betaF4 1) (g5_betaF4 3) = 0 ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 1 + g5_betaF4 3) ∧
      ¬ IsRoot (langTag .F4) (g5_betaF4 1 - g5_betaF4 3) :=
  ⟨by decide +kernel, g5_f4_not_root_mem (by decide +kernel),
    g5_f4_not_root_mem (by decide +kernel)⟩

private theorem g5_f4_short_row_coeff :
    ∀ row ∈ pairTable (langTag .F4),
      iform (orbitCertRoot (langTag .F4) row.1) (orbitCertRoot (langTag .F4) row.1) = 2 →
      iform (orbitCertRoot (langTag .F4) row.2.1) (orbitCertRoot (langTag .F4) row.2.1) = 2 →
      iform (orbitCertRoot (langTag .F4) row.1) (orbitCertRoot (langTag .F4) row.2.1) = 0 →
      ∀ f ∈ row.2.2.2, f.2.2.2 = -2 := by
  decide +kernel

private theorem g5_exists_pairTable_row_gen
    {r s : Fin (langTag .F4).rank → ℤ}
    (hr : IsRoot (langTag .F4) r) (hs : IsRoot (langTag .F4) s) (hne : r ≠ s) (hne' : r ≠ -s) :
    ∃ row ∈ pairTable (langTag .F4), ∃ w : WeylGroup (langTag .F4),
      w • orbitCertRoot (langTag .F4) row.1 = r ∧
        w • orbitCertRoot (langTag .F4) row.2.1 = s := by
  obtain ⟨row, ⟨hrow, horb⟩, -⟩ :=
    (rank_two_pair_certificate (langTag .F4)).1 r s hr hs hne hne'
  obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.1 horb
  rw [Prod.smul_mk, Prod.mk.injEq] at hw
  exact ⟨row, hrow, w, hw.1, hw.2⟩

private theorem g5_f4_short_pinnedX_commute
    {α γ : Fin (langTag .F4).rank → ℤ} (hα : IsRoot (langTag .F4) α)
    (hγ : IsRoot (langTag .F4) γ) (hlenα : iform α α = 2) (hlenγ : iform γ γ = 2)
    (hip : iform α γ = 0) :
    ∀ x y : GGL, Commute (pinnedX (langTag .F4) GGL α x) (pinnedX (langTag .F4) GGL γ y) := by
  intro x y
  have hne : α ≠ γ := by
    rintro rfl
    rw [hlenα] at hip
    norm_num at hip
  have hne' : α ≠ -γ := by
    rintro rfl
    rw [CFSG.LieType.Chevalley.iform_neg_left, hlenγ] at hip
    norm_num at hip
  obtain ⟨row, hrow, w, hw1, hw2⟩ := g5_exists_pairTable_row_gen hα hγ hne hne'
  have c1 : iform (orbitCertRoot (langTag .F4) row.1) (orbitCertRoot (langTag .F4) row.1) = 2 := by
    have h := iform_smul w (orbitCertRoot (langTag .F4) row.1) (orbitCertRoot (langTag .F4) row.1)
    rw [hw1, hlenα] at h
    exact h.symm
  have c2 : iform (orbitCertRoot (langTag .F4) row.2.1) (orbitCertRoot (langTag .F4) row.2.1) = 2 := by
    have h := iform_smul w (orbitCertRoot (langTag .F4) row.2.1) (orbitCertRoot (langTag .F4) row.2.1)
    rw [hw2, hlenγ] at h
    exact h.symm
  have c3 : iform (orbitCertRoot (langTag .F4) row.1) (orbitCertRoot (langTag .F4) row.2.1) = 0 := by
    have h := iform_smul w (orbitCertRoot (langTag .F4) row.1) (orbitCertRoot (langTag .F4) row.2.1)
    rw [hw1, hw2, hip] at h
    exact h.symm
  have hcoeff : ∀ f ∈ row.2.2.2, f.2.2.2 = -2 := g5_f4_short_row_coeff row hrow c1 c2 c3
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  refine commutatorElement_eq_one_iff_commute.1 ?_
  rw [commutatorElement_pinnedX_of_two_eq_zero h2 hrow w hw1 hw2 x y]
  have hfac : ∀ f ∈ row.2.2.2,
      pinnedX (langTag .F4) GGL (w • orbitCertRoot (langTag .F4) f.2.2.1)
        ((f.2.2.2 : GGL) * x ^ f.1 * y ^ f.2.1) = 1 := by
    intro f hf
    have hc := hcoeff f hf
    have hc0 : (f.2.2.2 : GGL) = 0 := by
      rw [hc]
      simp only [Int.cast_neg, Int.cast_ofNat]
      rw [h2, neg_zero]
    rw [hc0, zero_mul, zero_mul, pinnedX_zero]
  have hprod : ∀ L : List (ℕ × ℕ × ℕ × ℤ),
      (∀ f ∈ L, pinnedX (langTag .F4) GGL (w • orbitCertRoot (langTag .F4) f.2.2.1)
        ((f.2.2.2 : GGL) * x ^ f.1 * y ^ f.2.1) = 1) →
      (L.map fun f => pinnedX (langTag .F4) GGL (w • orbitCertRoot (langTag .F4) f.2.2.1)
        ((f.2.2.2 : GGL) * x ^ f.1 * y ^ f.2.1)).prod = 1 := by
    intro L hL
    induction L with
    | nil => simp
    | cons f L ih =>
      rw [List.map_cons, List.prod_cons, hL f List.mem_cons_self,
        ih (fun g hg => hL g (List.mem_cons_of_mem _ hg)), one_mul]
  exact hprod row.2.2.2 hfac

private theorem g5_f4_short_rankOne_commute
    :
    ∀ g ∈ rootRankOneGroup (langTag .F4) GGL (g5_betaF4 2),
      ∀ h ∈ rootRankOneGroup (langTag .F4) GGL (g5_betaF4 3), g * h = h * g := by
  have hL : ∀ {δ : Fin (langTag .F4).rank → ℤ}, IsRoot (langTag .F4) δ →
      rootRankOneGroup (langTag .F4) GGL δ =
        Subgroup.closure (Set.range (pinnedX (langTag .F4) GGL δ) ∪
          Set.range (pinnedX (langTag .F4) GGL (-δ))) :=
    fun hδ => by
      rw [(exceptional_Lang_root_rank_one_torus_transport (langTag .F4) GGL hδ).1, rootSubgroup,
        rootSubgroup, Subgroup.closure_union]
  rw [hL (g5_betaF4_isRoot 2), hL (g5_betaF4_isRoot 3)]
  refine closure_commute ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · exact g5_f4_short_pinnedX_commute (g5_betaF4_isRoot 2) (g5_betaF4_isRoot 3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) c d
  · exact g5_f4_short_pinnedX_commute (g5_betaF4_isRoot 2) (IsRoot.neg (g5_betaF4_isRoot 3))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) c d
  · exact g5_f4_short_pinnedX_commute (IsRoot.neg (g5_betaF4_isRoot 2)) (g5_betaF4_isRoot 3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) c d
  · exact g5_f4_short_pinnedX_commute (IsRoot.neg (g5_betaF4_isRoot 2))
      (IsRoot.neg (g5_betaF4_isRoot 3))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) c d

private theorem g5_rootSL2_commute_of_rankOne
    (α γ : Fin (langTag .F4).rank → ℤ)
    (h : ∀ x ∈ rootRankOneGroup (langTag .F4) GGL α,
      ∀ y ∈ rootRankOneGroup (langTag .F4) GGL γ, x * y = y * x)
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL α A) (rootSL2 (langTag .F4) GGL γ B) :=
  h _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

private theorem g5_f4_commute_01
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 0) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 1) B) :=
  g5_rootSL2_commute_of_rankOne _ _
    (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .F4) GGL
      (g5_betaF4_isRoot 0) (g5_betaF4_isRoot 1)
      g5_f4_orth01.1 g5_f4_orth01.2.1 g5_f4_orth01.2.2) A B

private theorem g5_f4_commute_02
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 0) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 2) B) :=
  g5_rootSL2_commute_of_rankOne _ _
    (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .F4) GGL
      (g5_betaF4_isRoot 0) (g5_betaF4_isRoot 2)
      g5_f4_orth02.1 g5_f4_orth02.2.1 g5_f4_orth02.2.2) A B

private theorem g5_f4_commute_03
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 0) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 3) B) :=
  g5_rootSL2_commute_of_rankOne _ _
    (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .F4) GGL
      (g5_betaF4_isRoot 0) (g5_betaF4_isRoot 3)
      g5_f4_orth03.1 g5_f4_orth03.2.1 g5_f4_orth03.2.2) A B

private theorem g5_f4_commute_12
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 1) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 2) B) :=
  g5_rootSL2_commute_of_rankOne _ _
    (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .F4) GGL
      (g5_betaF4_isRoot 1) (g5_betaF4_isRoot 2)
      g5_f4_orth12.1 g5_f4_orth12.2.1 g5_f4_orth12.2.2) A B

private theorem g5_f4_commute_13
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 1) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 3) B) :=
  g5_rootSL2_commute_of_rankOne _ _
    (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .F4) GGL
      (g5_betaF4_isRoot 1) (g5_betaF4_isRoot 3)
      g5_f4_orth13.1 g5_f4_orth13.2.1 g5_f4_orth13.2.2) A B

private theorem g5_f4_commute_23
    (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 2) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 3) B) :=
  g5_rootSL2_commute_of_rankOne _ _ g5_f4_short_rankOne_commute A B

private theorem g5_f4_commute_of_lt
    (i j : Fin 4) (h : i < j) (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 i) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 j) B) := by
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
    revert h
    revert i j
    decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact g5_f4_commute_01 A B
  · exact g5_f4_commute_02 A B
  · exact g5_f4_commute_03 A B
  · exact g5_f4_commute_12 A B
  · exact g5_f4_commute_13 A B
  · exact g5_f4_commute_23 A B

private theorem g5_f4_commute_all
    (i j : Fin 4) (hij : i ≠ j) (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .F4) GGL (g5_betaF4 i) A)
      (rootSL2 (langTag .F4) GGL (g5_betaF4 j) B) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact g5_f4_commute_of_lt i j h A B
  · exact (g5_f4_commute_of_lt j i h B A).symm

private theorem g5_list_map_rootReflection_prod_smul
    {τ : Tag} (l : List (Fin τ.rank → ℤ))
    (hl : ∀ β ∈ l, IsRoot τ β) (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β u => u - corootPair β u • β) v := by
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]

private theorem g5_f4_foldr_single : ∀ j : Fin (langTag .F4).rank,
    (List.ofFn g5_betaF4).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin (langTag .F4).rank → ℤ) = -Pi.single j 1 := by
  decide +kernel

private theorem g5_f4_frame_single
    (j : Fin (langTag .F4).rank) :
    (List.ofFn fun i : Fin 4 => rootReflection (g5_betaF4 i)).prod •
      (Pi.single j 1 : Fin (langTag .F4).rank → ℤ) = -Pi.single j 1 := by
  have hmap : (List.ofFn fun i : Fin 4 => rootReflection (g5_betaF4 i)) =
      (List.ofFn g5_betaF4).map rootReflection := by
    rw [List.map_ofFn]; rfl
  rw [hmap, g5_list_map_rootReflection_prod_smul _ _ _]
  · exact g5_f4_foldr_single j
  · intro β hβ
    obtain ⟨i, hi⟩ := (List.mem_ofFn' g5_betaF4 β).1 hβ
    rw [← hi]
    exact g5_betaF4_isRoot i

private theorem g5_smul_eq_neg_of_single {τ : Tag} {w : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1) (v : Fin τ.rank → ℤ) :
    w • v = -v := by
  have hlin : weylAction (isFiniteType_cartan τ) w = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, ← smul_def, h i]
    simp
  rw [smul_def, hlin]
  simp

private theorem g5_ggLangReidx_roundtrip {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx h (ggLangReidx h.symm v) = v := by
  subst h
  funext j
  simp [ggLangReidx]

private theorem g5_permLattice_permCongr_one {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (v : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) v = v := by
  change permLattice (Equiv.permCongr (finCongr h) (Equiv.refl _)) v = v
  rw [Equiv.permCongr_refl]
  rfl

private theorem g5_GGCommPi_F4
    {p f : ℕ} (ht : GGExcFive .F4)
    (u : WeylGroup (langTag .F4)) : GGCommPi .F4 p f ht u := by
  intro v
  rw [piB_F4, g5_permLattice_permCongr_one (rank_eq_langTag f ht) v,
    g5_permLattice_permCongr_one (rank_eq_langTag f ht) (u • v)]

theorem ggG5_frame_neg_F4
    {p f : ℕ} (ht : GGExcFive .F4) (hf : 1 ≤ f) (hε : eps p f = -1) :
    Nonempty (GGLangFrame .F4 p f ht) := by
  have hR := rank_eq_langTag f ht
  let β : Fin 4 → (Fin (ggU (absTag .F4) 6 f).D.rank → ℤ) :=
    fun i => ggLangReidx hR.symm (g5_betaF4 i)
  have hβreidx : ∀ i, ggLangReidx hR (β i) = g5_betaF4 i := fun i =>
    g5_ggLangReidx_roundtrip hR (g5_betaF4 i)
  have hroot : ∀ i, β i ∈ (ggU (absTag .F4) 6 f).D.roots := by
    intro i
    rw [mem_roots_iff_isRoot f ht, hβreidx i]
    exact g5_betaF4_isRoot i
  have hfix : ∀ i, latPerm (piB .F4 p f) (β i) = β i := by
    intro i
    rw [piB_F4]
    rfl
  have hgraph : ∀ i, ggGraphLat .F4 (ggLangReidx hR (β i)) = ggLangReidx hR (β i) := by
    intro i
    rw [hβreidx i]
    rfl
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 GGL,
      Commute (rootSL2 (langTag .F4) GGL (ggLangReidx hR (β i)) A)
        (rootSL2 (langTag .F4) GGL (ggLangReidx hR (β j)) B) := by
    intro i j hij A B
    rw [hβreidx i, hβreidx j]
    exact g5_f4_commute_all i j hij A B
  have hlaw : GGWeylLaw .F4 p f ht
      (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))).prod := by
    intro u
    have hprod : (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))) =
        (List.ofFn fun i : Fin 4 => rootReflection (g5_betaF4 i)) := by
      apply congrArg List.ofFn
      funext i
      exact congrArg rootReflection (hβreidx i)
    rw [hprod, show ggGraphLat .F4 u = u from rfl]
    rw [g5_smul_eq_neg_of_single (fun j => g5_f4_frame_single j) u, hε]
    rw [piB_F4, g5_permLattice_permCongr_one hR u]
    simp
  have hrf : ∀ α ∈ (ggU (absTag .F4) 6 f).D.roots, latPerm (piB .F4 p f) α = α →
      ∃ i, ∃ u : WeylGroup (langTag .F4), GGCommPi .F4 p f ht u ∧
        u • ggLangReidx hR (β i) = ggLangReidx hR α := by
    intro α hα _
    have hαL : IsRoot (langTag .F4) (ggLangReidx hR α) := (mem_roots_iff_isRoot f ht α).1 hα
    rcases g5_f4_length_split (ggLangReidx hR α) (mem_rootFinset.2 hαL) with hlong | hshort
    · obtain ⟨u, hu⟩ :=
        ggG5_orbit_F4 (g5_betaF4_isRoot 0) hαL (g5_betaF4_norm0.trans hlong.symm)
      exact ⟨0, u, g5_GGCommPi_F4 ht u, by rw [hβreidx 0]; exact hu⟩
    · obtain ⟨u, hu⟩ :=
        ggG5_orbit_F4 (g5_betaF4_isRoot 2) hαL (g5_betaF4_norm2.trans hshort.symm)
      exact ⟨2, u, g5_GGCommPi_F4 ht u, by rw [hβreidx 2]; exact hu⟩
  have hf5 : ∀ γ : Fin (langTag .F4).rank → ℤ, IsRoot (langTag .F4) γ →
      ggGraphLat .F4 γ = γ →
      ∃ i, ∃ u : WeylGroup (langTag .F4),
        ggPhi .F4 f (canonicalRep (coxeterSystem (langTag .F4)) GGL u) =
          canonicalRep (coxeterSystem (langTag .F4)) GGL u ∧
        u • ggLangReidx hR (β i) = γ := by
    intro γ hγ _
    rcases g5_f4_length_split γ (mem_rootFinset.2 hγ) with hlong | hshort
    · obtain ⟨u, hu⟩ :=
        ggG5_orbit_F4 (g5_betaF4_isRoot 0) hγ (g5_betaF4_norm0.trans hlong.symm)
      exact ⟨0, u, ggG5_phi_canonicalRep_untw (Or.inl rfl) f u, by rw [hβreidx 0]; exact hu⟩
    · obtain ⟨u, hu⟩ :=
        ggG5_orbit_F4 (g5_betaF4_isRoot 2) hγ (g5_betaF4_norm2.trans hshort.symm)
      exact ⟨2, u, ggG5_phi_canonicalRep_untw (Or.inl rfl) f u, by rw [hβreidx 2]; exact hu⟩
  exact ggG5_frame_of_prod ht hf β hroot hfix hgraph hcomm hlaw hrf hf5

end FrameF4

end CFSG.StandardType.GGFinModel.G5
