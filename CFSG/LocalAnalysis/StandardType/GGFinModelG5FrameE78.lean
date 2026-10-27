module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameCore
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5PlainFix

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg.Adjoint

section FrameE78

private def g5_betaE7 : Fin 7 → (Fin (langTag .E7).rank → ℤ) :=
  ![![2, 2, 3, 4, 3, 2, 1], ![0, 1, 1, 2, 2, 2, 1], ![0, 1, 1, 2, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0]]

private def g5_betaE8 : Fin 8 → (Fin (langTag .E8).rank → ℤ) :=
  ![![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 0],
    ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]]

private theorem g5_betaE7_mem : ∀ i, g5_betaE7 i ∈ rootFinset (langTag .E7) := by decide +kernel

private theorem g5_betaE8_mem : ∀ i, g5_betaE8 i ∈ rootFinset (langTag .E8) := by decide +kernel

private theorem g5_betaE7_isRoot
    (i : Fin 7) : IsRoot (langTag .E7) (g5_betaE7 i) :=
  mem_rootFinset.1 (g5_betaE7_mem i)

private theorem g5_betaE8_isRoot
    (i : Fin 8) : IsRoot (langTag .E8) (g5_betaE8 i) :=
  mem_rootFinset.1 (g5_betaE8_mem i)

private theorem g5_e7_not_root_mem
    {v : Fin (langTag .E7).rank → ℤ}
    (h : v ∉ rootFinset (langTag .E7)) : ¬ IsRoot (langTag .E7) v :=
  fun hv => h (mem_rootFinset.2 hv)

private theorem g5_e8_not_root_mem
    {v : Fin (langTag .E8).rank → ℤ}
    (h : v ∉ rootFinset (langTag .E8)) : ¬ IsRoot (langTag .E8) v :=
  fun hv => h (mem_rootFinset.2 hv)

private theorem g5_e7_pair :
    ∀ i j : Fin 7, i ≠ j →
      iform (τ := Tag.E7) (g5_betaE7 i) (g5_betaE7 j) = 0 ∧
      (g5_betaE7 i + g5_betaE7 j) ∉ rootFinset (langTag .E7) ∧
      (g5_betaE7 i - g5_betaE7 j) ∉ rootFinset (langTag .E7) := by
  decide +kernel

private theorem g5_e8_pair :
    ∀ i j : Fin 8, i ≠ j →
      iform (τ := Tag.E8) (g5_betaE8 i) (g5_betaE8 j) = 0 ∧
      (g5_betaE8 i + g5_betaE8 j) ∉ rootFinset (langTag .E8) ∧
      (g5_betaE8 i - g5_betaE8 j) ∉ rootFinset (langTag .E8) := by
  decide +kernel

private theorem g5_e7_commute
    (i j : Fin 7) (hij : i ≠ j) (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .E7) GGL (g5_betaE7 i) A)
      (rootSL2 (langTag .E7) GGL (g5_betaE7 j) B) := by
  have hf := g5_e7_pair i j hij
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .E7) GGL
    (g5_betaE7_isRoot i) (g5_betaE7_isRoot j)
    hf.1 (g5_e7_not_root_mem hf.2.1) (g5_e7_not_root_mem hf.2.2) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

private theorem g5_e8_commute
    (i j : Fin 8) (hij : i ≠ j) (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .E8) GGL (g5_betaE8 i) A)
      (rootSL2 (langTag .E8) GGL (g5_betaE8 j) B) := by
  have hf := g5_e8_pair i j hij
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .E8) GGL
    (g5_betaE8_isRoot i) (g5_betaE8_isRoot j)
    hf.1 (g5_e8_not_root_mem hf.2.1) (g5_e8_not_root_mem hf.2.2) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

private theorem g5_e7_foldr_single : ∀ j : Fin (langTag .E7).rank,
    (List.ofFn g5_betaE7).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin (langTag .E7).rank → ℤ) = -Pi.single j 1 := by
  decide +kernel

private theorem g5_e8_foldr_single : ∀ j : Fin (langTag .E8).rank,
    (List.ofFn g5_betaE8).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin (langTag .E8).rank → ℤ) = -Pi.single j 1 := by
  decide +kernel

private theorem g5_list_map_rootReflection_prod_smul
    {τ : Tag} (l : List (Fin τ.rank → ℤ))
    (hl : ∀ β ∈ l, IsRoot τ β) (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β u => u - corootPair β u • β) v := by
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]

private theorem g5_smul_eq_neg_of_single {τ : Tag} {w : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1) (v : Fin τ.rank → ℤ) :
    w • v = -v := by
  have hlin : weylAction (isFiniteType_cartan τ) w = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, ← smul_def, h i]
    simp
  rw [smul_def, hlin]
  simp

private theorem g5_e7_frame_single
    (j : Fin (langTag .E7).rank) :
    (List.ofFn fun i : Fin 7 => rootReflection (g5_betaE7 i)).prod •
      (Pi.single j 1 : Fin (langTag .E7).rank → ℤ) = -Pi.single j 1 := by
  have e : (List.ofFn fun i : Fin 7 => rootReflection (g5_betaE7 i)) =
      (List.ofFn g5_betaE7).map rootReflection := by
    rw [List.map_ofFn]
    rfl
  rw [e, g5_list_map_rootReflection_prod_smul _ _ _]
  · exact g5_e7_foldr_single j
  · intro β hβ
    obtain ⟨i, hi⟩ := (List.mem_ofFn' g5_betaE7 β).1 hβ
    rw [← hi]
    exact g5_betaE7_isRoot i

private theorem g5_e8_frame_single
    (j : Fin (langTag .E8).rank) :
    (List.ofFn fun i : Fin 8 => rootReflection (g5_betaE8 i)).prod •
      (Pi.single j 1 : Fin (langTag .E8).rank → ℤ) = -Pi.single j 1 := by
  have e : (List.ofFn fun i : Fin 8 => rootReflection (g5_betaE8 i)) =
      (List.ofFn g5_betaE8).map rootReflection := by
    rw [List.map_ofFn]
    rfl
  rw [e, g5_list_map_rootReflection_prod_smul _ _ _]
  · exact g5_e8_foldr_single j
  · intro β hβ
    obtain ⟨i, hi⟩ := (List.mem_ofFn' g5_betaE8 β).1 hβ
    rw [← hi]
    exact g5_betaE8_isRoot i

private theorem g5_e7_reflections
    (v : Fin (langTag .E7).rank → ℤ) :
    (List.ofFn fun i : Fin 7 => rootReflection (g5_betaE7 i)).prod • v = -v :=
  g5_smul_eq_neg_of_single (fun j => g5_e7_frame_single j) v

private theorem g5_e8_reflections
    (v : Fin (langTag .E8).rank → ℤ) :
    (List.ofFn fun i : Fin 8 => rootReflection (g5_betaE8 i)).prod • v = -v :=
  g5_smul_eq_neg_of_single (fun j => g5_e8_frame_single j) v

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

private theorem g5_GGCommPi_E7
    {p f : ℕ} (ht : GGExcFive .E7)
    (u : WeylGroup (langTag .E7)) : GGCommPi .E7 p f ht u := by
  intro v
  rw [piB_E7, g5_permLattice_permCongr_one (rank_eq_langTag f ht) v,
    g5_permLattice_permCongr_one (rank_eq_langTag f ht) (u • v)]

private theorem g5_GGCommPi_E8
    {p f : ℕ} (ht : GGExcFive .E8)
    (u : WeylGroup (langTag .E8)) : GGCommPi .E8 p f ht u := by
  intro v
  rw [piB_E8, g5_permLattice_permCongr_one (rank_eq_langTag f ht) v,
    g5_permLattice_permCongr_one (rank_eq_langTag f ht) (u • v)]

theorem ggG5_frame_neg_E7
    {p f : ℕ} (ht : GGExcFive .E7) (hf : 1 ≤ f) (hε : eps p f = -1) :
    Nonempty (GGLangFrame .E7 p f ht) := by
  have hR := rank_eq_langTag f ht
  let β : Fin 7 → (Fin (ggU (absTag .E7) 6 f).D.rank → ℤ) :=
    fun i => ggLangReidx hR.symm (g5_betaE7 i)
  have hβreidx : ∀ i, ggLangReidx hR (β i) = g5_betaE7 i := fun i =>
    g5_ggLangReidx_roundtrip hR (g5_betaE7 i)
  have hroot : ∀ i, β i ∈ (ggU (absTag .E7) 6 f).D.roots := by
    intro i
    rw [mem_roots_iff_isRoot f ht, hβreidx i]
    exact g5_betaE7_isRoot i
  have hfix : ∀ i, latPerm (piB .E7 p f) (β i) = β i := by
    intro i
    rw [piB_E7]
    rfl
  have hgraph : ∀ i, ggGraphLat .E7 (ggLangReidx hR (β i)) = ggLangReidx hR (β i) := by
    intro i
    rw [hβreidx i]
    rfl
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 GGL,
      Commute (rootSL2 (langTag .E7) GGL (ggLangReidx hR (β i)) A)
        (rootSL2 (langTag .E7) GGL (ggLangReidx hR (β j)) B) := by
    intro i j hij A B
    rw [hβreidx i, hβreidx j]
    exact g5_e7_commute i j hij A B
  have hlaw : GGWeylLaw .E7 p f ht
      (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))).prod := by
    intro u
    have hprod : (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))) =
        (List.ofFn fun i : Fin 7 => rootReflection (g5_betaE7 i)) := by
      apply congrArg List.ofFn
      funext i
      rw [hβreidx i]
    rw [hprod, show ggGraphLat .E7 u = u from rfl]
    rw [g5_e7_reflections u, hε]
    rw [piB_E7, g5_permLattice_permCongr_one hR u]
    simp
  have hrf : ∀ α ∈ (ggU (absTag .E7) 6 f).D.roots, latPerm (piB .E7 p f) α = α →
      ∃ i, ∃ u : WeylGroup (langTag .E7), GGCommPi .E7 p f ht u ∧
        u • ggLangReidx hR (β i) = ggLangReidx hR α := by
    intro α hα _
    have hαL : IsRoot (langTag .E7) (ggLangReidx hR α) := (mem_roots_iff_isRoot f ht α).1 hα
    obtain ⟨u, hu⟩ := ggG5_orbit_simplyLaced (Or.inr (Or.inl rfl)) (g5_betaE7_isRoot 0) hαL
    exact ⟨0, u, g5_GGCommPi_E7 ht u, by rw [hβreidx 0]; exact hu⟩
  have hf5 : ∀ γ : Fin (langTag .E7).rank → ℤ, IsRoot (langTag .E7) γ →
      ggGraphLat .E7 γ = γ →
      ∃ i, ∃ u : WeylGroup (langTag .E7),
        ggPhi .E7 f (canonicalRep (coxeterSystem (langTag .E7)) GGL u) =
          canonicalRep (coxeterSystem (langTag .E7)) GGL u ∧
        u • ggLangReidx hR (β i) = γ := by
    intro γ hγ _
    obtain ⟨u, hu⟩ := ggG5_orbit_simplyLaced (Or.inr (Or.inl rfl)) (g5_betaE7_isRoot 0) hγ
    exact ⟨0, u, ggG5_phi_canonicalRep_untw (Or.inr (Or.inr (Or.inl rfl))) f u,
      by rw [hβreidx 0]; exact hu⟩
  exact ggG5_frame_of_prod ht hf β hroot hfix hgraph hcomm hlaw hrf hf5

theorem ggG5_frame_neg_E8
    {p f : ℕ} (ht : GGExcFive .E8) (hf : 1 ≤ f) (hε : eps p f = -1) :
    Nonempty (GGLangFrame .E8 p f ht) := by
  have hR := rank_eq_langTag f ht
  let β : Fin 8 → (Fin (ggU (absTag .E8) 6 f).D.rank → ℤ) :=
    fun i => ggLangReidx hR.symm (g5_betaE8 i)
  have hβreidx : ∀ i, ggLangReidx hR (β i) = g5_betaE8 i := fun i =>
    g5_ggLangReidx_roundtrip hR (g5_betaE8 i)
  have hroot : ∀ i, β i ∈ (ggU (absTag .E8) 6 f).D.roots := by
    intro i
    rw [mem_roots_iff_isRoot f ht, hβreidx i]
    exact g5_betaE8_isRoot i
  have hfix : ∀ i, latPerm (piB .E8 p f) (β i) = β i := by
    intro i
    rw [piB_E8]
    rfl
  have hgraph : ∀ i, ggGraphLat .E8 (ggLangReidx hR (β i)) = ggLangReidx hR (β i) := by
    intro i
    rw [hβreidx i]
    rfl
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 GGL,
      Commute (rootSL2 (langTag .E8) GGL (ggLangReidx hR (β i)) A)
        (rootSL2 (langTag .E8) GGL (ggLangReidx hR (β j)) B) := by
    intro i j hij A B
    rw [hβreidx i, hβreidx j]
    exact g5_e8_commute i j hij A B
  have hlaw : GGWeylLaw .E8 p f ht
      (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))).prod := by
    intro u
    have hprod : (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))) =
        (List.ofFn fun i : Fin 8 => rootReflection (g5_betaE8 i)) := by
      apply congrArg List.ofFn
      funext i
      rw [hβreidx i]
    rw [hprod, show ggGraphLat .E8 u = u from rfl]
    rw [g5_e8_reflections u, hε]
    rw [piB_E8, g5_permLattice_permCongr_one hR u]
    simp
  have hrf : ∀ α ∈ (ggU (absTag .E8) 6 f).D.roots, latPerm (piB .E8 p f) α = α →
      ∃ i, ∃ u : WeylGroup (langTag .E8), GGCommPi .E8 p f ht u ∧
        u • ggLangReidx hR (β i) = ggLangReidx hR α := by
    intro α hα _
    have hαL : IsRoot (langTag .E8) (ggLangReidx hR α) := (mem_roots_iff_isRoot f ht α).1 hα
    obtain ⟨u, hu⟩ := ggG5_orbit_simplyLaced (Or.inr (Or.inr rfl)) (g5_betaE8_isRoot 0) hαL
    exact ⟨0, u, g5_GGCommPi_E8 ht u, by rw [hβreidx 0]; exact hu⟩
  have hf5 : ∀ γ : Fin (langTag .E8).rank → ℤ, IsRoot (langTag .E8) γ →
      ggGraphLat .E8 γ = γ →
      ∃ i, ∃ u : WeylGroup (langTag .E8),
        ggPhi .E8 f (canonicalRep (coxeterSystem (langTag .E8)) GGL u) =
          canonicalRep (coxeterSystem (langTag .E8)) GGL u ∧
        u • ggLangReidx hR (β i) = γ := by
    intro γ hγ _
    obtain ⟨u, hu⟩ := ggG5_orbit_simplyLaced (Or.inr (Or.inr rfl)) (g5_betaE8_isRoot 0) hγ
    exact ⟨0, u, ggG5_phi_canonicalRep_untw (Or.inr (Or.inr (Or.inr rfl))) f u,
      by rw [hβreidx 0]; exact hu⟩
  exact ggG5_frame_of_prod ht hf β hroot hfix hgraph hcomm hlaw hrf hf5

end FrameE78

end CFSG.StandardType.GGFinModel.G5
