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

section FrameE6

private def g5_betaE6 : Fin 4 → (Fin (langTag .E6).rank → ℤ) :=
  ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]]

private theorem g5_betaE6_mem : ∀ i, g5_betaE6 i ∈ rootFinset (langTag .E6) := by decide +kernel

private theorem g5_betaE6_isRoot
    (i : Fin 4) : IsRoot (langTag .E6) (g5_betaE6 i) :=
  mem_rootFinset.1 (g5_betaE6_mem i)

private theorem g5_betaE6_fixed : ∀ i,
    permLattice (τ := langTag .E6) (TwistTag.perm .E6) (g5_betaE6 i) = g5_betaE6 i := by
  decide +kernel

private theorem g5_betaE6_pair : ∀ i j : Fin 4, i ≠ j →
    iform (τ := langTag .E6) (g5_betaE6 i) (g5_betaE6 j) = 0 ∧
    (g5_betaE6 i + g5_betaE6 j) ∉ rootFinset (langTag .E6) ∧
    (g5_betaE6 i - g5_betaE6 j) ∉ rootFinset (langTag .E6) := by decide +kernel

private theorem g5_e6_not_root_mem
    {v : Fin (langTag .E6).rank → ℤ}
    (h : v ∉ rootFinset (langTag .E6)) : ¬ IsRoot (langTag .E6) v :=
  fun hv => h (mem_rootFinset.2 hv)

private theorem g5_e6_commute
    (i j : Fin 4) (hij : i ≠ j) (A B : SL2 GGL) :
    Commute (rootSL2 (langTag .E6) GGL (g5_betaE6 i) A)
      (rootSL2 (langTag .E6) GGL (g5_betaE6 j) B) := by
  have hf := g5_betaE6_pair i j hij
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation (langTag .E6) GGL
    (g5_betaE6_isRoot i) (g5_betaE6_isRoot j)
    hf.1 (g5_e6_not_root_mem hf.2.1) (g5_e6_not_root_mem hf.2.2) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩

private def g5_permLin {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) :
    Module.End ℤ (Fin τ.rank → ℤ) :=
  LinearMap.funLeft ℤ ℤ π.symm

private theorem g5_permLin_apply {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) : g5_permLin π v = permLattice π v := rfl

private theorem g5_smul_eq_neg_perm_of_single {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    {w : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -permLattice π (Pi.single i 1))
    (v : Fin τ.rank → ℤ) : w • v = -permLattice π v := by
  have hlin : weylAction (isFiniteType_cartan τ) w = -g5_permLin π := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin τ.rank → ℤ) = x • Pi.single i 1 := by
      conv_lhs => rw [← mul_one x, ← smul_eq_mul]
      rw [Pi.single_smul]
    rw [hx, map_smul, ← smul_def, h i, LinearMap.neg_apply, map_smul, g5_permLin_apply,
      smul_neg]
  rw [smul_def, hlin, LinearMap.neg_apply, g5_permLin_apply]

private theorem g5_list_map_rootReflection_prod_smul
    {τ : Tag} (l : List (Fin τ.rank → ℤ))
    (hl : ∀ β ∈ l, IsRoot τ β) (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β u => u - corootPair β u • β) v := by
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]

private theorem g5_e6_foldr_single : ∀ j : Fin (langTag .E6).rank,
    (List.ofFn g5_betaE6).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin (langTag .E6).rank → ℤ) =
      -permLattice (τ := langTag .E6) (TwistTag.perm .E6) (Pi.single j 1) := by
  decide +kernel

private theorem g5_e6_reflections
    (v : Fin (langTag .E6).rank → ℤ) :
    (List.ofFn fun i : Fin 4 => rootReflection (g5_betaE6 i)).prod •
      v = -permLattice (τ := langTag .E6) (TwistTag.perm .E6) v := by
  refine g5_smul_eq_neg_perm_of_single
    (π := (TwistTag.perm .E6 : Equiv.Perm (Fin (langTag .E6).rank))) (fun j => ?_) v
  have e : (List.ofFn fun i : Fin 4 => rootReflection (g5_betaE6 i)) =
      (List.ofFn g5_betaE6).map rootReflection := by
    rw [List.map_ofFn]
    rfl
  have hstep := g5_list_map_rootReflection_prod_smul (τ := langTag .E6)
    (l := List.ofFn g5_betaE6)
    (fun β hβ => by
      obtain ⟨i, hi⟩ := (List.mem_ofFn' g5_betaE6 β).1 hβ
      rw [← hi]
      exact g5_betaE6_isRoot i)
    (Pi.single j 1)
  rw [e]
  exact hstep.trans (g5_e6_foldr_single j)

private theorem g5_e6_reflections_tw
    (v : Fin (langTag .twistedE6).rank → ℤ) :
    (List.ofFn fun i : Fin 4 =>
      rootReflection (τ := langTag .twistedE6) (g5_betaE6 i)).prod •
      v = -permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) v :=
  g5_e6_reflections v

private theorem g5_permLattice_self
    (v : Fin (langTag .E6).rank → ℤ) :
    permLattice (τ := langTag .E6) (TwistTag.perm .E6)
      (permLattice (τ := langTag .E6) (TwistTag.perm .E6) v) = v := by
  have hs : (TwistTag.perm .E6 : Equiv.Perm (Fin (langTag .E6).rank)).symm =
      (TwistTag.perm .E6 : Equiv.Perm (Fin (langTag .E6).rank)) := by decide +kernel
  have h := permLattice_permLattice_symm (TwistTag.perm .E6) v
  rwa [hs] at h

private theorem g5_permLattice_self_tw
    (v : Fin (langTag .twistedE6).rank → ℤ) :
    permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6)
      (permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) v) = v :=
  g5_permLattice_self v

private theorem g5_permCongr_e6
    {f : ℕ}
    (h : (ggU .E6 6 f).D.rank = (langTag .E6).rank) :
    (finCongr h).permCongr (TwistTag.perm .E6) = TwistTag.perm .E6 := by
  have he : (finCongr h : Fin (ggU .E6 6 f).D.rank ≃ Fin (langTag .E6).rank) =
      Equiv.refl (Fin (ggU .E6 6 f).D.rank) :=
    Equiv.ext fun j => Fin.ext rfl
  rw [he]
  rfl

private theorem g5_ggLangReidx_roundtrip {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx h (ggLangReidx h.symm v) = v := by
  subst h
  funext j
  simp [ggLangReidx]

private theorem g5_ggLangReidx_symm_roundtrip {R N : ℕ} (h : R = N) (v : Fin R → ℤ) :
    ggLangReidx h.symm (ggLangReidx h v) = v := by
  subst h
  funext j
  simp [ggLangReidx]

private theorem g5_permLattice_permCongr_one {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (v : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) v = v := by
  change permLattice (Equiv.permCongr (finCongr h) (Equiv.refl _)) v = v
  rw [Equiv.permCongr_refl]
  rfl

private theorem g5_GGCommPi_E6_of_twist
    {p f : ℕ} (ht : GGExcFive .E6)
    (h : ¬ p ∣ 2 ^ f - 1) {u : WeylGroup (langTag .E6)} (hu : weylTwist TwistTag.E6 u = u) :
    GGCommPi .E6 p f ht u := by
  have hπ : (finCongr (rank_eq_langTag f ht)).permCongr (piB .E6 p f) = TwistTag.perm .E6 := by
    rw [piB_E6_of_not_dvd f h]
    exact g5_permCongr_e6 (rank_eq_langTag f ht)
  intro v
  rw [hπ]
  exact (mem_relWeylTwist_iff_smul TwistTag.E6).1
    ((mem_relWeylTwist TwistTag.E6).2 hu) v

private theorem g5_GGCommPi_twistedE6
    {p f : ℕ} (ht : GGExcFive .twistedE6)
    (hdvd : p ∣ 2 ^ f + 1) (u : WeylGroup (langTag .twistedE6)) :
    GGCommPi .twistedE6 p f ht u := by
  intro v
  rw [piB_twistedE6_of_dvd f hdvd,
    g5_permLattice_permCongr_one (rank_eq_langTag f ht) v,
    g5_permLattice_permCongr_one (rank_eq_langTag f ht) (u • v)]

theorem ggG5_frame_neg_E6
    {p f : ℕ} (ht : GGExcFive .E6) (hf : 1 ≤ f) (hε : eps p f = -1) :
    Nonempty (GGLangFrame .E6 p f ht) := by
  have hnodvd : ¬ p ∣ 2 ^ f - 1 := by
    intro h
    rw [(eps_eq_one_iff p f).2 h] at hε
    norm_num at hε
  have hR := rank_eq_langTag f ht
  have hπ : (finCongr hR).permCongr (piB .E6 p f) = TwistTag.perm .E6 := by
    rw [piB_E6_of_not_dvd f hnodvd]
    exact g5_permCongr_e6 hR
  let β : Fin 4 → (Fin (ggU (absTag .E6) 6 f).D.rank → ℤ) :=
    fun i => ggLangReidx hR.symm (g5_betaE6 i)
  have hβreidx : ∀ i, ggLangReidx hR (β i) = g5_betaE6 i := fun i =>
    g5_ggLangReidx_roundtrip hR (g5_betaE6 i)
  have hroot : ∀ i, β i ∈ (ggU (absTag .E6) 6 f).D.roots := by
    intro i
    rw [mem_roots_iff_isRoot f ht, hβreidx i]
    exact g5_betaE6_isRoot i
  have hfix : ∀ i, latPerm (piB .E6 p f) (β i) = β i := by
    intro i
    have h1 : ggLangReidx hR (latPerm (piB .E6 p f) (β i)) = ggLangReidx hR (β i) := by
      rw [ggReidx_latPerm_permLattice hR (piB .E6 p f) (β i), hβreidx i, hπ]
      exact g5_betaE6_fixed i
    calc latPerm (piB .E6 p f) (β i)
        = ggLangReidx hR.symm (ggLangReidx hR (latPerm (piB .E6 p f) (β i))) :=
          (g5_ggLangReidx_symm_roundtrip hR _).symm
      _ = ggLangReidx hR.symm (ggLangReidx hR (β i)) := by rw [h1]
      _ = β i := g5_ggLangReidx_symm_roundtrip hR _
  have hgraph : ∀ i, ggGraphLat .E6 (ggLangReidx hR (β i)) = ggLangReidx hR (β i) := by
    intro i
    rw [hβreidx i]
    rfl
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 GGL,
      Commute (rootSL2 (langTag .E6) GGL (ggLangReidx hR (β i)) A)
        (rootSL2 (langTag .E6) GGL (ggLangReidx hR (β j)) B) := by
    intro i j hij A B
    rw [hβreidx i, hβreidx j]
    exact g5_e6_commute i j hij A B
  have hlaw : GGWeylLaw .E6 p f ht
      (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))).prod := by
    intro u
    have hprod : (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))) =
        (List.ofFn fun i : Fin 4 => rootReflection (g5_betaE6 i)) := by
      apply congrArg List.ofFn
      funext i
      rw [hβreidx i]
    rw [hprod, show ggGraphLat .E6 u = u from rfl]
    rw [g5_e6_reflections u, hε]
    rw [hπ]
    simp
  have hrf : ∀ α ∈ (ggU (absTag .E6) 6 f).D.roots, latPerm (piB .E6 p f) α = α →
      ∃ i, ∃ u : WeylGroup (langTag .E6), GGCommPi .E6 p f ht u ∧
        u • ggLangReidx hR (β i) = ggLangReidx hR α := by
    intro α hα hfixα
    have hαL : IsRoot (langTag .E6) (ggLangReidx hR α) := (mem_roots_iff_isRoot f ht α).1 hα
    have hfix' : permLattice (τ := langTag .E6) (TwistTag.perm .E6) (ggLangReidx hR α) =
        ggLangReidx hR α := by
      have h2 : ggLangReidx hR (latPerm (piB .E6 p f) α) = ggLangReidx hR α := by rw [hfixα]
      rw [ggReidx_latPerm_permLattice hR (piB .E6 p f) α, hπ] at h2
      exact h2
    obtain ⟨u, hu, hu'⟩ := ggG5_orbit_E6_graph (g5_betaE6_isRoot 0) hαL
      (g5_betaE6_fixed 0) hfix'
    exact ⟨0, u, g5_GGCommPi_E6_of_twist ht hnodvd hu, by rw [hβreidx 0]; exact hu'⟩
  have hf5 : ∀ γ : Fin (langTag .E6).rank → ℤ, IsRoot (langTag .E6) γ →
      ggGraphLat .E6 γ = γ →
      ∃ i, ∃ u : WeylGroup (langTag .E6),
        ggPhi .E6 f (canonicalRep (coxeterSystem (langTag .E6)) GGL u) =
          canonicalRep (coxeterSystem (langTag .E6)) GGL u ∧
        u • ggLangReidx hR (β i) = γ := by
    intro γ hγ _
    obtain ⟨u, hu⟩ := ggG5_orbit_simplyLaced (Or.inl rfl) (g5_betaE6_isRoot 0) hγ
    exact ⟨0, u, ggG5_phi_canonicalRep_untw (Or.inr (Or.inl rfl)) f u,
      by rw [hβreidx 0]; exact hu⟩
  exact ggG5_frame_of_prod ht hf β hroot hfix hgraph hcomm hlaw hrf hf5

theorem ggG5_frame_neg_twistedE6
    {p f : ℕ} (ht : GGExcFive .twistedE6) (hf : 1 ≤ f)
    (hreg : GGExcRegime p f) (hε : eps p f = -1) : Nonempty (GGLangFrame .twistedE6 p f ht) := by
  have hnodvd : ¬ p ∣ 2 ^ f - 1 := by
    intro h
    rw [(eps_eq_one_iff p f).2 h] at hε
    norm_num at hε
  have hdvd : p ∣ 2 ^ f + 1 := by
    rcases hreg with h | h
    · exact absurd h hnodvd
    · exact h
  have hR := rank_eq_langTag f ht
  let β : Fin 4 → (Fin (ggU (absTag .twistedE6) 6 f).D.rank → ℤ) :=
    fun i => ggLangReidx hR.symm (g5_betaE6 i)
  have hβreidx : ∀ i, ggLangReidx hR (β i) = g5_betaE6 i := fun i =>
    g5_ggLangReidx_roundtrip hR (g5_betaE6 i)
  have hroot : ∀ i, β i ∈ (ggU (absTag .twistedE6) 6 f).D.roots := by
    intro i
    rw [mem_roots_iff_isRoot f ht, hβreidx i]
    exact g5_betaE6_isRoot i
  have hfix : ∀ i, latPerm (piB .twistedE6 p f) (β i) = β i := by
    intro i
    rw [piB_twistedE6_of_dvd f hdvd]
    rfl
  have hgraph : ∀ i, ggGraphLat .twistedE6 (ggLangReidx hR (β i)) = ggLangReidx hR (β i) := by
    intro i
    rw [hβreidx i]
    exact g5_betaE6_fixed i
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 GGL,
      Commute (rootSL2 (langTag .twistedE6) GGL (ggLangReidx hR (β i)) A)
        (rootSL2 (langTag .twistedE6) GGL (ggLangReidx hR (β j)) B) := by
    intro i j hij A B
    rw [hβreidx i, hβreidx j]
    exact g5_e6_commute i j hij A B
  have hlaw : GGWeylLaw .twistedE6 p f ht
      (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))).prod := by
    intro u
    have hprod : (List.ofFn fun i => rootReflection (ggLangReidx hR (β i))) =
        (List.ofFn fun i : Fin 4 =>
          rootReflection (τ := langTag .twistedE6) (g5_betaE6 i)) := by
      apply congrArg List.ofFn
      funext i
      exact congrArg rootReflection (hβreidx i)
    rw [hprod]
    rw [show ggGraphLat .twistedE6 u =
        permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) u from rfl]
    rw [g5_e6_reflections_tw (permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) u), hε]
    rw [piB_twistedE6_of_dvd f hdvd, g5_permLattice_permCongr_one hR u]
    rw [g5_permLattice_self_tw]
    simp
  have hrf : ∀ α ∈ (ggU (absTag .twistedE6) 6 f).D.roots, latPerm (piB .twistedE6 p f) α = α →
      ∃ i, ∃ u : WeylGroup (langTag .twistedE6), GGCommPi .twistedE6 p f ht u ∧
        u • ggLangReidx hR (β i) = ggLangReidx hR α := by
    intro α hα _
    have hαL : IsRoot (langTag .twistedE6) (ggLangReidx hR α) :=
      (mem_roots_iff_isRoot f ht α).1 hα
    obtain ⟨u, hu⟩ := ggG5_orbit_simplyLaced (Or.inl rfl) (g5_betaE6_isRoot 0) hαL
    exact ⟨0, u, g5_GGCommPi_twistedE6 ht hdvd u, by rw [hβreidx 0]; exact hu⟩
  have hf5 : ∀ γ : Fin (langTag .twistedE6).rank → ℤ, IsRoot (langTag .twistedE6) γ →
      ggGraphLat .twistedE6 γ = γ →
      ∃ i, ∃ u : WeylGroup (langTag .twistedE6),
        ggPhi .twistedE6 f (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL u) =
          canonicalRep (coxeterSystem (langTag .twistedE6)) GGL u ∧
        u • ggLangReidx hR (β i) = γ := by
    intro γ hγ hgγ
    obtain ⟨u, hu, hu'⟩ := ggG5_orbit_E6_graph (g5_betaE6_isRoot 0) hγ
      (g5_betaE6_fixed 0) hgγ
    exact ⟨0, u, ggG5_phi_canonicalRep_twistedE6 f u hu, by rw [hβreidx 0]; exact hu'⟩
  exact ggG5_frame_of_prod ht hf β hroot hfix hgraph hcomm hlaw hrf hf5

end FrameE6

end CFSG.StandardType.GGFinModel.G5
