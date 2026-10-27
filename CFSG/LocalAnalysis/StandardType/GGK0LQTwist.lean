module

public import CFSG.LocalAnalysis.StandardType.GGK0LQRoots
public import CFSG.LocalAnalysis.StandardType.GGK0LQPair
public import CFSG.LocalAnalysis.StandardType.GGK0NormalFrob
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.LocalAnalysis.StandardType.GGK0NormalTypes
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private theorem lk0xlqtwist_iform_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (n : ℕ) (x y : Fin τ.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform
        (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) x) (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) y) =
      CFSG.LieType.Steinberg.Adjoint.iform x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]

private theorem lk0xlqtwist_neg_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (n : ℕ) (x : Fin τ.rank → ℤ) :
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) (-x) = -((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]

private theorem lk0xlqtwist_orbit_image {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (Ψ : Set (Fin τ.rank → ℤ)) :
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ]) '' Ψ = Ψ := by
  by_cases h : ({s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}).Nonempty
  · exact (Nat.sInf_mem h).2
  · have h0 : componentOrbitLength S.ρ Ψ = 0 := by
      unfold componentOrbitLength
      rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty]
    rw [h0]
    simp

private theorem lk0xlqtwist_k0pMul_getD (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
    (k0pMul a b).getD i 0 = a.getD (b.getD i 0) 0 := by
  induction b generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          show (xs.map (fun i => a.getD i 0)).getD i 0 = a.getD (xs.getD i 0) 0
          exact ih hi'

private theorem lk0xlqtwist_k0pPow_go (a : List ℕ) (f : ℕ) (acc : List ℕ) :
    k0pPow.go a f acc = acc.map ((fun j => a.getD j 0)^[f]) := by
  induction f generalizing acc with
  | zero => simp only [k0pPow.go, Function.iterate_zero, List.map_id]
  | succ f ih =>
      rw [show k0pPow.go a (f+1) acc = k0pPow.go a f (k0pMul a acc) from rfl, ih]
      unfold k0pMul
      rw [List.map_map]
      congr 1

private theorem lk0xlqtwist_k0pPow_getD (a : List ℕ) (n : ℕ) {i : ℕ} (hi : i < a.length) :
    (k0pPow a n).getD i 0 = (fun j => a.getD j 0)^[n] i := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lk0xlqtwist_k0pPow_go,
    k0pId, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

private theorem lk0xlqtwist_rho_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (fun j => A.row.rho.getD j 0)^[n] i.val = (A.row.nodePerm^[n] i).val := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, A.row.rho_apply, Function.iterate_succ_apply']

private theorem lk0xlqtwist_k0pPow_getD_nodePerm (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (k0pPow A.row.rho n).getD i.val 0 = (A.row.nodePerm^[n] i).val := by
  rw [lk0xlqtwist_k0pPow_getD A.row.rho n (by rw [A.row.rho_length]; exact i.isLt)]
  exact lk0xlqtwist_rho_iterate A n i

private theorem lk0xlqtwist_frob_nodes_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[n])
        (A.nodeMap (Pi.single i 1)) =
      (A.epsilon ^ n) • A.nodeMap (Pi.single ((A.row.nodePerm^[n]) i) 1) := by
  have hroot : ∀ m, IsRoot A.tau
      (((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[m])
        (A.nodeMap (Pi.single i 1))) := by
    intro m
    induction m with
    | zero => simpa using A.node_isRoot i
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact (A.setup.frob.isRoot_iff _).mpr ih
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [← A.frob_roots _ (hroot n), ih, map_smul, A.frob_nodes, smul_smul]
      rw [pow_succ, Function.iterate_succ_apply']

private theorem lk0xlqtwist_marks_pos (T : GGKacType) (i : Fin (k0DiagOf T).marks.length) :
    0 < (k0DiagOf T).marks.getD i.val 0 := by
  cases T <;> fin_cases i <;> decide

private theorem lk0xlqtwist_exists_ne_ne (T : GGKacType) (i y : Fin (k0DiagOf T).marks.length) :
    ∃ z : Fin (k0DiagOf T).marks.length, z ≠ i ∧ z ≠ y := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin (k0DiagOf T).marks.length)) ⊆ {i, y} := by
    intro z _
    by_cases hzi : z = i
    · simp [hzi]
    · have hzy : z = y := h z hzi
      simp [hzy]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, y} : Finset (Fin (k0DiagOf T).marks.length)).card ≤ 2 := by
    have := Finset.card_insert_le i ({y} : Finset (Fin (k0DiagOf T).marks.length))
    simpa using this
  have h3 : 3 ≤ (Finset.univ : Finset (Fin (k0DiagOf T).marks.length)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    cases T <;> decide
  omega

private theorem lk0xlqtwist_single_comb_notMem_ker (A : K0LangMark Omega lab p R I phi)
    (i y : Fin A.row.diagram.marks.length) (h : i ≠ y) (c : ℤ) :
    (Pi.single i 1 + c • Pi.single y 1 : Fin A.row.diagram.marks.length → ℤ) ∉
      A.nodeMap.ker := by
  intro hmem
  rw [A.nodeMap_ker, Submodule.mem_span_singleton] at hmem
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨z, hzi, hzy⟩ := lk0xlqtwist_exists_ne_ne A.row.T i y
  have hz0 : (Pi.single i 1 + c • Pi.single y 1 :
      Fin A.row.diagram.marks.length → ℤ) z = 0 := by
    simp [Pi.single_apply, hzi, hzy]
  have hzi1 : (Pi.single i 1 + c • Pi.single y 1 :
      Fin A.row.diagram.marks.length → ℤ) i = 1 := by
    simp [Pi.single_apply, h]
  have hkz := congrFun hk z
  rw [Pi.smul_apply, smul_eq_mul, hz0] at hkz
  have hmz : (0 : ℤ) < ((A.row.diagram.marks.getD z.val 0 : ℕ) : ℤ) := by
    exact_mod_cast lk0xlqtwist_marks_pos A.row.T z
  have hk0 : k = 0 := (mul_eq_zero.mp hkz).resolve_right (ne_of_gt hmz)
  have hki := congrFun hk i
  rw [Pi.smul_apply, smul_eq_mul, hk0, zero_mul, hzi1] at hki
  exact one_ne_zero hki.symm

theorem lq_tw_single (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h : (lqNodes A P j).length = 1) : lqTw A P j = 1 := by
  classical
  obtain ⟨N⟩ := k0Normal_nonempty A
  have hc : ((P.orbitNodes j).headD []).length = 1 := h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hc
  have hmemx : x ∈ lqNodes A P j := by
    show x ∈ (P.orbitNodes j).headD []
    rw [hx]; simp
  obtain ⟨-, -, hbound⟩ := lq_nodes_basic A P j
  have hxlt : x < A.row.diagram.marks.length := by
    have := (hbound x hmemx).1
    rw [N.length_eq]; exact this
  let i : Fin A.row.diagram.marks.length := ⟨x, hxlt⟩
  have hival : i.val = x := rfl
  set Ψ := componentRoots (rootCharHom A.a) (P.repr j) with hΨ
  have hΨroot : IsRootComponent Ψ := hΨ ▸ isRootComponent_componentRoots (P.repr j)
  have hrank : ∀ α ∈ Ψ, ∀ δ ∈ Ψ, δ = α ∨ δ = -α := (lq_rankOne_iff A P j).mpr h
  let γ : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single i 1)
  have hγΨ : γ ∈ Ψ := by
    rw [hΨ, P.repr_roots j]
    refine ⟨A.node_isRoot i, ?_⟩
    apply Submodule.subset_span
    refine ⟨i, ?_, rfl⟩
    rw [hx]; simp [hival]
  have hlen : componentOrbitLength A.setup.ρ Ψ = (P.orbitNodes j).length := by
    rw [hΨ]; exact P.orbit_length j
  have hclosed : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[
      (P.orbitNodes j).length]) '' Ψ = Ψ := by
    rw [← hlen]; exact lk0xlqtwist_orbit_image A.setup Ψ
  have hσγΨ : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[
      (P.orbitNodes j).length]) γ ∈ Ψ := by
    rw [← hclosed]; exact ⟨γ, hγΨ, rfl⟩
  have hσγ := lk0xlqtwist_frob_nodes_iterate A (P.orbitNodes j).length i
  have hγπΨ : A.nodeMap (Pi.single ((A.row.nodePerm^[(P.orbitNodes j).length]) i) 1) ∈ Ψ := by
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by
      rw [A.epsilon_eq]; split <;> simp
    have hεs : A.epsilon ^ (P.orbitNodes j).length = 1 ∨
        A.epsilon ^ (P.orbitNodes j).length = -1 := by
      rcases hε with hε | hε <;> rw [hε]
      · exact Or.inl (one_pow _)
      · rcases Nat.even_or_odd (P.orbitNodes j).length with he | ho
        · exact Or.inl he.neg_one_pow
        · exact Or.inr ho.neg_one_pow
    have hh := hσγΨ
    rw [hσγ] at hh
    rcases hεs with hεs | hεs
    · rw [hεs, one_smul] at hh; exact hh
    · rw [hεs] at hh
      have hneg := hΨroot.neg_mem _ hh
      simpa using hneg
  have hπ : (A.row.nodePerm^[(P.orbitNodes j).length]) i = i := by
    by_contra hne
    rcases hrank γ hγΨ _ hγπΨ with heq | heq
    · refine (lk0xlqtwist_single_comb_notMem_ker A _ i hne (-1)) ?_
      rw [LinearMap.mem_ker, map_add, map_smul, heq]
      simp [γ]
    · refine (lk0xlqtwist_single_comb_notMem_ker A _ i hne 1) ?_
      rw [LinearMap.mem_ker, map_add, map_smul, heq]
      simp [γ]
  have hfix : (k0pPow A.row.rho (P.orbitNodes j).length).getD x 0 = x := by
    rw [← hival, lk0xlqtwist_k0pPow_getD_nodePerm A (P.orbitNodes j).length i, hπ]
  have haut : k0AutOrder [x] (k0pPow A.row.rho (P.orbitNodes j).length) = 1 := by
    rw [show k0AutOrder [x] (k0pPow A.row.rho (P.orbitNodes j).length) =
        k0AutOrder.go [x] (k0pPow A.row.rho (P.orbitNodes j).length) 1
          (k0pPow A.row.rho (P.orbitNodes j).length) 2 from rfl]
    simp only [k0AutOrder.go]
    rw [if_pos]
    simpa [List.getD_eq_getElem?_getD] using hfix
  have hct : k0CompType (k0DiagOf A.row.T) ((P.orbitNodes j).headD []) =
      (LargeEvenLieTag.A, 1) := lq_compType_single A P j h
  have hcond : ¬ (A.row.d = 2 ∧ (P.orbitNodes j).length % 2 = 1 ∧
      k0Tau0Of (k0CompType (k0DiagOf A.row.T) ((P.orbitNodes j).headD [])).1
        (k0CompType (k0DiagOf A.row.T) ((P.orbitNodes j).headD [])).2) := by
    rintro ⟨-, -, htau⟩
    rw [hct] at htau
    simp [k0Tau0Of] at htau
  simp only [lqTw]
  rw [if_neg hcond, hx]
  exact haut

theorem lq_kind_of_rankOne
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h : (lqNodes A P j).length = 1) :
    twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner := by
  classical
  set Ψ := componentRoots (rootCharHom A.a) (P.repr j) with hΨ
  have hΨc : Ψ = componentRoots (rootCharHom A.a) (P.repr j) := hΨ
  have hrank : ∀ α ∈ Ψ, ∀ δ ∈ Ψ, δ = α ∨ δ = -α := (lq_rankOne_iff A P j).mpr h
  obtain ⟨a, ha⟩ := Quotient.exists_rep (P.repr j)
  have hα : (a : Fin A.tau.rank → ℤ) ∈ Ψ := by
    rw [hΨc]; exact ⟨a.2, ha⟩
  have hΨroot : IsRootComponent Ψ := hΨc ▸ isRootComponent_componentRoots (P.repr j)
  have hnegα : -(a : Fin A.tau.rank → ℤ) ∈ Ψ := hΨroot.neg_mem _ hα
  have hset : Ψ = {(a : Fin A.tau.rank → ℤ), -(a : Fin A.tau.rank → ℤ)} := by
    ext δ
    constructor
    · intro hδ
      rcases hrank _ hα _ hδ with hh | hh
      · exact by rw [hh]; exact Set.mem_insert _ _
      · exact by rw [hh]; exact Set.mem_insert_of_mem _ rfl
    · intro hδ
      rcases (show δ = (a : Fin A.tau.rank → ℤ) ∨ δ = -(a : Fin A.tau.rank → ℤ) by
        simpa using hδ) with rfl | rfl
      · exact hα
      · exact hnegα
  have hne : (a : Fin A.tau.rank → ℤ) ≠ -(a : Fin A.tau.rank → ℤ) := by
    intro hh
    have hroot : IsRoot A.tau (a : Fin A.tau.rank → ℤ) := hΨroot.isRoot _ hα
    have h2 : (2 : ℤ) • (a : Fin A.tau.rank → ℤ) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hh]
      rw [add_neg_cancel]
    rcases (smul_eq_zero.mp h2) with hz | hz
    · exact two_ne_zero hz
    · exact hroot.ne_zero hz
  have hncard : Ψ.ncard = 2 := by
    rw [hset, Set.ncard_pair hne]
  have hcompRank : compRank Ψ = 1 := by
    rw [hΨc, lq_compRank A P j, h]
  set s := componentOrbitLength A.setup.ρ Ψ with hs
  have hsc : s = componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j)) := by
    rw [hs, hΨc]
  have hφ : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) '' Ψ = Ψ := by
    rw [hs]; exact lk0xlqtwist_orbit_image A.setup Ψ
  have hinj : Function.Injective ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) :=
    A.setup.ρ.injective.iterate s
  have hform : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform
      (((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ)
      (((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ :=
    fun γ δ => lk0xlqtwist_iform_iterate A.setup s γ δ
  have hneg : ∀ γ, ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (-γ) =
      -((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ :=
    fun γ => lk0xlqtwist_neg_iterate A.setup s γ
  have hinner : twistInner Ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) :=
    CFSG.StandardType.LieCore.twistInner_of_small_inner (χ := rootCharHom A.a) (P.repr j)
      hφ hinj hform hneg (Or.inl ⟨hcompRank, hncard⟩)
  unfold twistKind
  rw [hsc.symm, ← hΨc]
  rw [if_pos hinner]

open CFSG.LieType.Steinberg.Adjoint

private theorem lk0xlqtwa2_lqNodes_eq (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    lqNodes A P j = (P.orbitNodes j).headD [] := rfl

private theorem lk0xlqtwa2_exists_notMem_three (T : GGKacType)
    (i j k : Fin (k0DiagOf T).marks.length) :
    ∃ z : Fin (k0DiagOf T).marks.length, z ≠ i ∧ z ≠ j ∧ z ≠ k := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin (k0DiagOf T).marks.length)) ⊆ {i, j, k} := by
    intro z _
    by_cases hzi : z = i
    · simp [hzi]
    · by_cases hzj : z = j
      · simp [hzj]
      · have hzk : z = k := h z hzi hzj
        simp [hzk]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, j, k} : Finset (Fin (k0DiagOf T).marks.length)).card ≤ 3 := by
    have hjk := Finset.card_insert_le j ({k} : Finset _)
    have hk : ({k} : Finset _).card = 1 := Finset.card_singleton k
    have hi := Finset.card_insert_le i ({j, k} : Finset _)
    omega
  have h3 : 5 ≤ (Finset.univ : Finset (Fin (k0DiagOf T).marks.length)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    cases T <;> decide
  omega

private theorem lk0xlqtwa2_node_notMem_pair
    (A : K0LangMark Omega lab p R I phi) {x y : ℕ}
    (hxlt : x < A.row.diagram.marks.length) (hylt : y < A.row.diagram.marks.length)
    {w : ℕ} (hwlt : w < A.row.diagram.marks.length)
    (hwx : w ≠ x) (hwy : w ≠ y)
    (hspan : A.nodeMap (Pi.single ⟨w, hwlt⟩ 1) ∈
      Submodule.span ℤ {A.nodeMap (Pi.single ⟨x, hxlt⟩ 1),
                         A.nodeMap (Pi.single ⟨y, hylt⟩ 1)}) :
    False := by
  let ix : Fin (k0DiagOf A.row.T).marks.length := ⟨x, hxlt⟩
  let iy : Fin (k0DiagOf A.row.T).marks.length := ⟨y, hylt⟩
  let iw : Fin (k0DiagOf A.row.T).marks.length := ⟨w, hwlt⟩
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hspan
  have hab' : a • A.nodeMap (Pi.single ix 1) + b • A.nodeMap (Pi.single iy 1) =
      A.nodeMap (Pi.single iw 1) := by simpa [ix, iy, iw] using hab
  have hmem : (Pi.single iw 1 - a • Pi.single ix 1 - b • Pi.single iy 1) ∈ A.nodeMap.ker := by
    rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, ← hab']
    abel
  rw [A.nodeMap_ker, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨z, hzi, hzj, hzk⟩ := lk0xlqtwa2_exists_notMem_three (T := A.row.T) ix iy iw
  have hz0 : (Pi.single iw 1 - a • Pi.single ix 1 - b • Pi.single iy 1 :
      Fin (k0DiagOf A.row.T).marks.length → ℤ) z = 0 := by
    simp [Pi.single_apply, hzi, hzj, hzk]
  have hzmark : ((A.row.diagram.marks.getD z.val 0 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lk0xlqtwist_marks_pos A.row.T z)
  have hcz := congrFun hc z
  rw [Pi.smul_apply, smul_eq_mul, hz0] at hcz
  have hc0 : c = 0 := (mul_eq_zero.mp hcz).resolve_right hzmark
  have hwx' : iw ≠ ix := by
    intro h; exact hwx (by simpa [ix, iw] using congrArg Fin.val h)
  have hwy' : iw ≠ iy := by
    intro h; exact hwy (by simpa [iy, iw] using congrArg Fin.val h)
  have hw1 : (Pi.single iw 1 - a • Pi.single ix 1 - b • Pi.single iy 1 :
      Fin (k0DiagOf A.row.T).marks.length → ℤ) iw = 1 := by
    simp [Pi.single_apply, hwx', hwy']
  have hcw := congrFun hc iw
  rw [Pi.smul_apply, smul_eq_mul, hc0, zero_mul, hw1] at hcw
  exact one_ne_zero hcw.symm

private theorem lk0xlqtwa2_pair_forms (T : GGKacType) (x y : ℕ) (hxy : x < y)
    (hy : y < (k0DiagOf T).marks.length)
    (hadj : 0 < (k0DiagOf T).adj x y)
    (hA : (k0CompType (k0DiagOf T) [x, y]).1 = .A) :
    (iform (lqExtRoot (absTag T) T x) (lqExtRoot (absTag T) T x) = 2 ∧
      iform (lqExtRoot (absTag T) T y) (lqExtRoot (absTag T) T y) = 2 ∧
      iform (lqExtRoot (absTag T) T x) (lqExtRoot (absTag T) T y) = -1) ∨
    (iform (lqExtRoot (absTag T) T x) (lqExtRoot (absTag T) T x) = 4 ∧
      iform (lqExtRoot (absTag T) T y) (lqExtRoot (absTag T) T y) = 4 ∧
      iform (lqExtRoot (absTag T) T x) (lqExtRoot (absTag T) T y) = -2) := by
  have hx : x < (k0DiagOf T).marks.length := by omega
  cases T
  · have hx7 : x < 7 := by
      rw [show (k0DiagOf GGKacType.E6).marks.length = 7 from rfl] at hx
      exact hx
    have hy7 : y < 7 := by
      rw [show (k0DiagOf GGKacType.E6).marks.length = 7 from rfl] at hy
      exact hy
    interval_cases x <;> interval_cases y <;> revert hA hadj <;> decide
  · have hx8 : x < 8 := by
      rw [show (k0DiagOf GGKacType.E7).marks.length = 8 from rfl] at hx
      exact hx
    have hy8 : y < 8 := by
      rw [show (k0DiagOf GGKacType.E7).marks.length = 8 from rfl] at hy
      exact hy
    interval_cases x <;> interval_cases y <;> revert hA hadj <;> decide
  · have hx9 : x < 9 := by
      rw [show (k0DiagOf GGKacType.E8).marks.length = 9 from rfl] at hx
      exact hx
    have hy9 : y < 9 := by
      rw [show (k0DiagOf GGKacType.E8).marks.length = 9 from rfl] at hy
      exact hy
    interval_cases x <;> interval_cases y <;> revert hA hadj <;> decide
  · have hx5 : x < 5 := by
      rw [show (k0DiagOf GGKacType.F4).marks.length = 5 from rfl] at hx
      exact hx
    have hy5 : y < 5 := by
      rw [show (k0DiagOf GGKacType.F4).marks.length = 5 from rfl] at hy
      exact hy
    interval_cases x <;> interval_cases y <;> revert hA hadj <;> decide

private theorem lk0xlqtwa2_k0pPow_length (a : List ℕ) (n : ℕ) :
    (k0pPow a n).length = a.length := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lk0xlqtwist_k0pPow_go]
  simp [k0pId]

private theorem lk0xlqtwa2_autOrder_eq_one (a b : ℕ) (rk : List ℕ) (hab : a ≠ b)
    (ha : rk.getD a 0 = a) (hb : rk.getD b 0 = b) :
    k0AutOrder [a, b] rk = 1 := by
  have ha' : rk[a]?.getD 0 = a := by simpa [List.getD_eq_getElem?_getD] using ha
  have hb' : rk[b]?.getD 0 = b := by simpa [List.getD_eq_getElem?_getD] using hb
  rw [show k0AutOrder [a, b] rk = k0AutOrder.go [a, b] rk 1 rk 3 from rfl]
  simp [k0AutOrder.go, List.all, List.getD_eq_getElem?_getD, ha', hb']

private theorem lk0xlqtwa2_autOrder_eq_two (a b : ℕ) (rk : List ℕ) (hab : a ≠ b)
    (hla : a < rk.length) (hlb : b < rk.length)
    (ha : rk.getD a 0 = b) (hb : rk.getD b 0 = a) :
    k0AutOrder [a, b] rk = 2 := by
  have ha' : rk[a]?.getD 0 = b := by simpa [List.getD_eq_getElem?_getD] using ha
  have hb' : rk[b]?.getD 0 = a := by simpa [List.getD_eq_getElem?_getD] using hb
  rw [show k0AutOrder [a, b] rk = k0AutOrder.go [a, b] rk 1 rk 3 from rfl]
  simp only [k0AutOrder.go]
  rw [if_neg]
  · have h1 : (k0pMul rk rk).getD a 0 = a := by
      rw [lk0xlqtwist_k0pMul_getD rk rk hla, ha, hb]
    have h2 : (k0pMul rk rk).getD b 0 = b := by
      rw [lk0xlqtwist_k0pMul_getD rk rk hlb, hb, ha]
    rw [List.getD_eq_getElem?_getD] at h1 h2
    rw [if_pos (by simp [List.all, List.getD_eq_getElem?_getD, h1, h2])]
  · simp [List.all, List.getD_eq_getElem?_getD, ha', hb', hab]

private theorem lk0xlqtwa2_rho_iterate_frobLinear (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    {γ : Fin A.tau.rank → ℤ} (hγ : IsRoot A.tau γ) :
    ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[n]) γ =
      ((A.frobLinear : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[n]) γ := by
  have hroot : ∀ m, IsRoot A.tau
      (((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[m]) γ) := by
    intro m
    induction m with
    | zero => simpa using hγ
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact (A.setup.frob.isRoot_iff _).mpr ih
  induction n generalizing γ with
  | zero => rfl
  | succ n ih =>
      have hrootn : IsRoot A.tau
          (((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[n]) γ) := hroot n
      have hroot' : ∀ m, IsRoot A.tau
          (((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[m])
            (((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[n]) γ)) := by
        intro m
        have hmn : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[m])
            (((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[n]) γ) =
            ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[m + n]) γ := by
          rw [Function.iterate_add_apply]
        rw [hmn]
        exact hroot (m + n)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ← A.frob_roots _ hrootn, ih hγ hroot]

private theorem lk0xlqtwa2_weyl_disc_step
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (m : ℤ) (hm : 0 < m)
    (hroot : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hsl : ∀ γ ∈ Ψ, iform γ γ = 2 * m)
    (hpair : ∀ γ ∈ Ψ, ∀ γ' ∈ Ψ, m ∣ iform γ γ')
    {d e : ℤ} (hd : d = m * e) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ)
    {y : WeylGroup τ}
    (hy : ∀ x : Fin τ.rank → ℤ, (∀ γ' ∈ Ψ, d ∣ iform x γ') →
      (∀ γ' ∈ Ψ, d ∣ iform (y • x) γ') ∧
        ∃ v ∈ Submodule.span ℤ Ψ, y • x - x = e • v)
    (x : Fin τ.rank → ℤ) (hx : ∀ γ' ∈ Ψ, d ∣ iform x γ') :
    (∀ γ' ∈ Ψ, d ∣ iform ((rootReflection γ * y) • x) γ') ∧
      ∃ v ∈ Submodule.span ℤ Ψ, (rootReflection γ * y) • x - x = e • v := by
  obtain ⟨h1, v₂, hv₂, h2⟩ := hy x hx
  obtain ⟨k, hk0⟩ := h1 γ hγ
  have hk : iform γ (y • x) = d * k := by
    rw [iform_comm]
    exact hk0
  have hcor : corootPair γ (y • x) = e * k := by
    unfold corootPair
    rw [hsl γ hγ, hk, hd]
    rw [show 2 * (m * e * k) = (2 * m) * (e * k) by ring]
    exact Int.mul_ediv_cancel_left (e * k) (by positivity)
  have hrs : (rootReflection γ * y) • x = y • x - (e * k) • γ := by
    rw [mul_smul, rootReflection_smul (hroot γ hγ), hcor]
  refine ⟨fun γ' hγ' => ?_, v₂ - k • γ,
    sub_mem hv₂ (Submodule.smul_mem _ _ (Submodule.subset_span hγ)), ?_⟩
  · rw [hrs, iform_sub_left,
      iform_smul_left]
    refine dvd_sub (h1 γ' hγ') ?_
    obtain ⟨t, ht⟩ := dvd_mul_of_dvd_right (hpair γ hγ γ' hγ') k
    refine ⟨t, ?_⟩
    rw [hd]
    calc e * k * iform γ γ' =
        e * (k * iform γ γ') := by ring
      _ = e * (m * t) := by rw [ht]
      _ = (m * e) * t := by ring
  · have hsub' : (y • x - (e * k) • γ) - x = (y • x - x) - (e * k) • γ := by abel
    rw [hrs, hsub', h2, smul_sub, smul_smul]

private theorem lk0xlqtwa2_weyl_disc_invariant
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (m : ℤ) (hm : 0 < m)
    (hroot : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hsl : ∀ γ ∈ Ψ, iform γ γ = 2 * m)
    (hpair : ∀ γ ∈ Ψ, ∀ γ' ∈ Ψ, m ∣ iform γ γ')
    {d e : ℤ} (hd : d = m * e) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (x : Fin τ.rank → ℤ) (hx : ∀ γ ∈ Ψ, d ∣ iform x γ) :
    (∀ γ ∈ Ψ, d ∣ iform (w • x) γ) ∧
      ∃ v ∈ Submodule.span ℤ Ψ, w • x - x = e • v := by
  induction hw using Subgroup.closure_induction_left generalizing x with
  | one => exact ⟨by simpa using hx, 0, zero_mem _, by simp⟩
  | mul_left s hs y hy ih =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    exact lk0xlqtwa2_weyl_disc_step m hm hroot hsl hpair hd hγ ih x hx
  | inv_mul_cancel s hs y hy ih =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    rw [rootReflection_inv (hroot γ hγ)]
    exact lk0xlqtwa2_weyl_disc_step m hm hroot hsl hpair hd hγ ih x hx

private theorem lk0xlqtwa2_not_twistInner_of_disc
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (m : ℤ) (hm : 0 < m)
    (hroot : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hsl : ∀ γ ∈ Ψ, iform γ γ = 2 * m)
    (hpair : ∀ γ ∈ Ψ, ∀ γ' ∈ Ψ, m ∣ iform γ γ')
    (σ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) {d e : ℤ} (hd : d = m * e)
    {μ ν : Fin τ.rank → ℤ} (hμ : μ ∈ Submodule.span ℤ Ψ)
    (hμd : ∀ γ ∈ Ψ, d ∣ iform μ γ)
    (hνd : ∀ γ ∈ Ψ, d ∣ iform ν γ)
    (hnd : ¬ d * e ∣ iform ν (σ μ - μ)) :
    ¬ twistInner Ψ (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) := by
  rintro ⟨w, hw, hσ⟩
  obtain ⟨-, v, hv, hwv⟩ :=
    lk0xlqtwa2_weyl_disc_invariant m hm hroot hsl hpair hd hw μ hμd
  have hσμ : σ μ = w • μ := by
    refine Submodule.span_induction (p := fun z _ => σ z = w • z) ?_ ?_ ?_ ?_ hμ
    · intro z hz; exact hσ z hz
    · simp
    · intro a b _ _ ha hb; rw [map_add, smul_add, ha, hb]
    · intro a z _ hz; rw [map_zsmul, smul_comm, hz]
  have hdv : d ∣ iform ν v := by
    refine Submodule.span_induction (p := fun z _ =>
      d ∣ iform ν z) ?_ ?_ ?_ ?_ hv
    · intro z hz; exact hνd z hz
    · have h0 : iform ν 0 = 0 := by
        simpa using iform_smul_right (0 : ℤ) ν 0
      show d ∣ iform ν 0
      rw [h0]; exact dvd_zero d
    · intro a b _ _ ha hb
      rw [iform_add_right]; exact dvd_add ha hb
    · intro a z _ hz
      rw [iform_smul_right]
      exact Dvd.dvd.mul_left hz a
  apply hnd
  rw [hσμ, hwv, iform_smul_right]
  simpa [mul_comm] using mul_dvd_mul_left e hdv

private theorem lk0xlqtwa2_A2_sq {τ : Tag} {α β : Fin τ.rank → ℤ} {m : ℤ}
    (hαα : iform α α = 2 * m)
    (hββ : iform β β = 2 * m)
    (hαβ : iform α β = -m)
    (hβα : iform β α = -m)
    {p : ℤ × ℤ}
    (hp : p ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)} : Finset (ℤ × ℤ))) :
    iform (p.1 • α + p.2 • β) (p.1 • α + p.2 • β) = 2 * m := by
  have hneg : ∀ x y : Fin τ.rank → ℤ,
      iform (-x) y =
        -iform x y := by
    intro x y
    rw [← neg_one_smul ℤ x, iform_smul_left]
    ring
  have hneg' : ∀ x y : Fin τ.rank → ℤ,
      iform x (-y) =
        -iform x y := by
    intro x y
    rw [← neg_one_smul ℤ y, iform_smul_right]
    ring
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hαα, hββ, hαβ, hβα, iform_add_left,
      iform_add_right,
      iform_smul_left,
      iform_smul_right, hneg, hneg'] <;> ring

private theorem lk0xlqtwa2_A2_pair {τ : Tag} {α β : Fin τ.rank → ℤ} {m : ℤ}
    (hαα : iform α α = 2 * m)
    (hββ : iform β β = 2 * m)
    (hαβ : iform α β = -m)
    (hβα : iform β α = -m)
    {p q : ℤ × ℤ}
    (hp : p ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)} : Finset (ℤ × ℤ)))
    (hq : q ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)} : Finset (ℤ × ℤ))) :
    m ∣ iform (p.1 • α + p.2 • β) (q.1 • α + q.2 • β) := by
  have hneg : ∀ x y : Fin τ.rank → ℤ,
      iform (-x) y =
        -iform x y := by
    intro x y
    rw [← neg_one_smul ℤ x, iform_smul_left]
    ring
  have hneg' : ∀ x y : Fin τ.rank → ℤ,
      iform x (-y) =
        -iform x y := by
    intro x y
    rw [← neg_one_smul ℤ y, iform_smul_right]
    ring
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [hαα, hββ, hαβ, hβα, iform_add_left,
      iform_add_right,
      iform_smul_left,
      iform_smul_right, hneg, hneg'] <;>
    ring_nf <;>
    first
      | exact dvd_zero m
      | exact dvd_refl m
      | exact dvd_mul_right m _
      | exact dvd_mul_left m _
      | exact dvd_neg.mpr (dvd_refl m)
      | exact dvd_neg.mpr (dvd_mul_right m _)
      | exact dvd_neg.mpr (dvd_mul_left m _)

private theorem lk0xlqtwa2_twistInner_congr {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (h : ∀ γ ∈ Ψ, σ γ = σ' γ) :
    twistInner Ψ σ ↔ twistInner Ψ σ' := by
  unfold twistInner
  constructor
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).symm.trans (hσ γ hγ)⟩
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).trans (hσ γ hγ)⟩

theorem lq_kind_of_A2 (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h : (lqNodes A P j).length = 2)
    (hA : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A) :
    (lqTw A P j = 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner) ∧
      (lqTw A P j ≠ 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .suN) := by
  classical
  set Ψ := componentRoots (rootCharHom A.a) (P.repr j) with hΨ
  have hΨroot : IsRootComponent Ψ := hΨ ▸ isRootComponent_componentRoots (P.repr j)
  have hroot : ∀ γ ∈ Ψ, IsRoot A.tau γ := by
    intro γ hγ; rw [hΨ, P.repr_roots j] at hγ; exact hγ.1
  have hcompRank : compRank Ψ = 2 := by rw [hΨ, lq_compRank A P j, h]
  have hncard : Ψ.ncard = 6 := by
    rw [hΨ, lq_pair_ncard A P j h]
    rw [if_pos hA]
  obtain ⟨x, y, hxy, hxylt, hybound, hadj⟩ := lq_pair_adj A P j h
  have hA' : (k0CompType (k0DiagOf A.row.T) [x, y]).1 = .A := by simpa [hxy] using hA
  let ix : Fin A.row.diagram.marks.length := ⟨x, by omega⟩
  let iy : Fin A.row.diagram.marks.length := ⟨y, hybound⟩
  let α : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single ix 1)
  let β : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single iy 1)
  have hαeq : α = lqExtRoot A.tau A.row.T x := by
    simpa [α, ix] using lq_nodeMap_eq A ix
  have hβeq : β = lqExtRoot A.tau A.row.T y := by
    simpa [β, iy] using lq_nodeMap_eq A iy
  have hforms := lk0xlqtwa2_pair_forms A.row.T x y hxylt hybound hadj hA'
  rw [A.tau_eq] at hforms
  obtain ⟨m, hm, hαα, hββ, hαβ⟩ : ∃ m : ℤ, (m = 1 ∨ m = 2) ∧
      iform α α = 2 * m ∧
      iform β β = 2 * m ∧
      iform α β = -m := by
    rcases hforms with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine ⟨1, by norm_num, ?_, ?_, ?_⟩
      · rw [hαeq]; norm_num; exact h1
      · rw [hβeq]; norm_num; exact h2
      · rw [hαeq, hβeq]; norm_num; exact h3
    · refine ⟨2, by norm_num, ?_, ?_, ?_⟩
      · rw [hαeq]; norm_num; exact h1
      · rw [hβeq]; norm_num; exact h2
      · rw [hαeq, hβeq]; norm_num; exact h3
  have hmpos : 0 < m := by rcases hm with rfl | rfl <;> norm_num
  have hβα : iform β α = -m := by
    rw [iform_comm, hαβ]
  have hαroot : IsRoot A.tau α := A.node_isRoot ix
  have hβroot : IsRoot A.tau β := A.node_isRoot iy
  have hαΨ : α ∈ Ψ := by
    rw [hΨ, P.repr_roots j]
    refine ⟨hαroot, ?_⟩
    apply Submodule.subset_span
    refine ⟨ix, ?_, rfl⟩
    change ix.val ∈ lqNodes A P j
    rw [hxy]
    change x ∈ [x, y]
    simp
  have hβΨ : β ∈ Ψ := by
    rw [hΨ, P.repr_roots j]
    refine ⟨hβroot, ?_⟩
    apply Submodule.subset_span
    refine ⟨iy, ?_, rfl⟩
    change iy.val ∈ lqNodes A P j
    rw [hxy]
    change y ∈ [x, y]
    simp
  have hxy_ne : ix ≠ iy := by
    intro heq
    have : x = y := by simpa [ix, iy] using congrArg Fin.val heq
    omega
  have hxy_ne' : ¬ iy = ix := fun h => hxy_ne h.symm
  have hset_pair : {w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
        i.val ∈ (P.orbitNodes j).headD [] ∧ w = A.nodeMap (Pi.single i 1)} = {α, β} := by
    rw [← lk0xlqtwa2_lqNodes_eq A P j, hxy]
    ext w; constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i.val = x ∨ i.val = y := by simpa using hi
      rcases hi' with hi | hi
      · left
        have hii : i = ix := Fin.ext hi
        subst hii; rfl
      · right
        have hii : i = iy := Fin.ext hi
        subst hii; rfl
    · rintro (rfl | rfl)
      · exact ⟨ix, by change x ∈ [x, y]; simp, rfl⟩
      · exact ⟨iy, by change y ∈ [x, y]; simp, rfl⟩
  have hαβ_ne : α ≠ β := by
    intro heq
    exact (lk0xlqtwist_single_comb_notMem_ker A ix iy hxy_ne (-1)) (by
      rw [LinearMap.mem_ker, map_add, map_smul]
      change α + (-1) • β = 0
      rw [heq]; simp)
  have hαβ_ne_neg : α ≠ -β := by
    intro heq
    exact (lk0xlqtwist_single_comb_notMem_ker A ix iy hxy_ne 1) (by
      rw [LinearMap.mem_ker, map_add, map_smul]
      change α + (1 : ℤ) • β = 0
      rw [heq]; simp)
  have hlin : CFSG.LieType.Steinberg.LinIndepPair α β :=
    CFSG.LieType.Steinberg.Adjoint.linIndepPair_of_ne hαroot hβroot hαβ_ne hαβ_ne_neg
  have hαβ_neg : iform α β < 0 := by
    rw [hαβ]; rcases hm with rfl | rfl <;> norm_num
  have hαβΨ : α + β ∈ Ψ := hΨroot.add_mem α hαΨ β hβΨ
    (isRoot_add_of_iform_neg hαroot hβroot hαβ_ne_neg hαβ_neg)
  let f : ℤ × ℤ → (Fin A.tau.rank → ℤ) := fun p => p.1 • α + p.2 • β
  let T : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}
  have hfin : Ψ.Finite := (rootFinset A.tau).finite_toSet.subset (fun γ hγ => by
    simpa using (mem_rootFinset.mpr (hroot γ hγ)))
  have hinj : Function.Injective f := by
    intro p q hpq
    have h0 : (p.1 - q.1) • α + (p.2 - q.2) • β = 0 := by
      have hpq' : f p = f q := hpq
      change p.1 • α + p.2 • β = q.1 • α + q.2 • β at hpq'
      rw [← sub_eq_zero] at hpq'
      convert hpq' using 1
      simp only [sub_smul]; abel
    have hz := hlin (p.1 - q.1) (p.2 - q.2) h0
    exact Prod.ext (by omega) (by omega)
  have hTcard : T.card = 6 := by decide
  have himgcard : (f '' (↑T : Set (ℤ × ℤ))).ncard = 6 := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, hTcard]
  have hTmem : ∀ {p : ℤ × ℤ}, p ∈ T →
      p = (1, 0) ∨ p = (-1, 0) ∨ p = (0, 1) ∨ p = (0, -1) ∨ p = (1, 1) ∨
        p = (-1, -1) := by
    intro p hp
    simpa [T] using hp
  have hsub : f '' (↑T : Set (ℤ × ℤ)) ⊆ Ψ := by
    rintro v ⟨p, hp, rfl⟩
    rcases hTmem hp with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [f] using hαΨ
    · simpa [f] using hΨroot.neg_mem α hαΨ
    · simpa [f] using hβΨ
    · simpa [f] using hΨroot.neg_mem β hβΨ
    · simpa [f] using hαβΨ
    · have h := hΨroot.neg_mem (α + β) hαβΨ
      have hf : f (-1, -1) = -(α + β) := by simp [f, neg_add_rev]; abel
      rwa [hf]
  have hΨeq : Ψ = f '' (↑T : Set (ℤ × ℤ)) := by
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
    rw [himgcard, hncard]
  have hsl : ∀ γ ∈ Ψ, iform γ γ = 2 * m := by
    intro γ hγ
    rw [hΨeq] at hγ
    obtain ⟨p, hp, rfl⟩ := hγ
    exact lk0xlqtwa2_A2_sq hαα hββ hαβ hβα (by simpa [T] using hp)
  have hpair : ∀ γ ∈ Ψ, ∀ γ' ∈ Ψ,
      m ∣ iform γ γ' := by
    intro γ hγ γ' hγ'
    rw [hΨeq] at hγ hγ'
    obtain ⟨p, hp, rfl⟩ := hγ
    obtain ⟨q, hq, rfl⟩ := hγ'
    exact lk0xlqtwa2_A2_pair hαα hββ hαβ hβα (by simpa [T] using hp) (by simpa [T] using hq)
  set s := (P.orbitNodes j).length with hs
  have hs_len : s = componentOrbitLength A.setup.ρ Ψ := by
    rw [hs, hΨ]; exact (P.orbit_length j).symm
  have hclosed : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) '' Ψ = Ψ := by
    rw [hs_len]; exact lk0xlqtwist_orbit_image A.setup Ψ
  have hpz_mem : ∀ z : Fin A.row.diagram.marks.length,
      A.nodeMap (Pi.single z 1) ∈ Ψ →
        (A.row.nodePerm^[s]) z = ix ∨ (A.row.nodePerm^[s]) z = iy := by
    intro z hzΨ
    have hσzΨ : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s])
        (A.nodeMap (Pi.single z 1)) ∈ Ψ := by
      rw [← hclosed]; exact ⟨_, hzΨ, rfl⟩
    have hσz := lk0xlqtwist_frob_nodes_iterate A s z
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
    have hεs : A.epsilon^s = 1 ∨ A.epsilon^s = -1 := by
      rcases hε with hε | hε <;> rw [hε]
      · exact Or.inl (one_pow _)
      · rcases Nat.even_or_odd s with he | ho
        · exact Or.inl he.neg_one_pow
        · exact Or.inr ho.neg_one_pow
    have hspan : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s])
        (A.nodeMap (Pi.single z 1)) ∈ Submodule.span ℤ {α, β} := by
      have h := hσzΨ
      rw [hΨ, P.repr_roots j] at h
      rw [hset_pair] at h
      exact h.2
    have hnode : A.nodeMap (Pi.single ((A.row.nodePerm^[s]) z) 1) ∈
        Submodule.span ℤ {A.nodeMap (Pi.single ix 1), A.nodeMap (Pi.single iy 1)} := by
      rcases hεs with hεs | hεs
      · rw [hεs, one_smul] at hσz
        rw [← hσz]
        simpa [α, β] using hspan
      · rw [hεs] at hσz
        have hx : A.nodeMap (Pi.single ((A.row.nodePerm^[s]) z) 1) =
            -(((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s])
              (A.nodeMap (Pi.single z 1))) := by rw [hσz]; simp
        rw [hx]
        exact Submodule.neg_mem _ hspan
    by_contra hcon
    push Not at hcon
    exact lk0xlqtwa2_node_notMem_pair A (x := x) (y := y)
      (w := ((A.row.nodePerm^[s]) z).val) (by omega) hybound ((A.row.nodePerm^[s]) z).isLt
      (by intro h; exact hcon.1 (Fin.ext h)) (by intro h; exact hcon.2 (Fin.ext h))
      (by simpa [ix, iy] using hnode)
  have hp_id_or_swap : ((A.row.nodePerm^[s]) ix = ix ∧ (A.row.nodePerm^[s]) iy = iy) ∨
      ((A.row.nodePerm^[s]) ix = iy ∧ (A.row.nodePerm^[s]) iy = ix) := by
    have hx' := hpz_mem ix hαΨ
    have hy' := hpz_mem iy hβΨ
    rcases hx' with hx' | hx'
    · left
      refine ⟨hx', ?_⟩
      rcases hy' with hy' | hy'
      · exfalso
        exact hxy_ne' ((A.row.nodePerm.injective).iterate s (hy'.trans hx'.symm))
      · exact hy'
    · right
      refine ⟨hx', ?_⟩
      rcases hy' with hy' | hy'
      · exact hy'
      · exfalso
        exact hxy_ne' ((A.row.nodePerm.injective).iterate s (hy'.trans hx'.symm))
  have hrk_len : (k0pPow A.row.rho s).length = A.row.diagram.marks.length := by
    rw [lk0xlqtwa2_k0pPow_length, A.row.rho_length]
  have h_o : k0AutOrder [x, y] (k0pPow A.row.rho s) =
      if (A.row.nodePerm^[s]) ix = ix then 1 else 2 := by
    rcases hp_id_or_swap with ⟨hpx, hpy⟩ | ⟨hpx, hpy⟩
    · rw [if_pos hpx]
      apply lk0xlqtwa2_autOrder_eq_one x y _ hxylt.ne
      · rw [lk0xlqtwist_k0pPow_getD_nodePerm A s ix]; exact congrArg Fin.val hpx
      · rw [lk0xlqtwist_k0pPow_getD_nodePerm A s iy]; exact congrArg Fin.val hpy
    · have hne : ¬ (A.row.nodePerm^[s]) ix = ix := by
        intro h; rw [hpx] at h; exact hxy_ne h.symm
      rw [if_neg hne]
      apply lk0xlqtwa2_autOrder_eq_two x y _ hxylt.ne
      · rw [hrk_len]; omega
      · rw [hrk_len]; omega
      · rw [lk0xlqtwist_k0pPow_getD_nodePerm A s ix]; exact congrArg Fin.val hpx
      · rw [lk0xlqtwist_k0pPow_getD_nodePerm A s iy]; exact congrArg Fin.val hpy
  have hct' : k0CompType (k0DiagOf A.row.T) [x, y] = (.A, 2) := by
    refine Prod.ext hA' ?_
    have h2 := lq_compType_A_rank (k0DiagOf A.row.T) [x, y] hA'
    rw [h2]; rfl
  have htw_eq : lqTw A P j =
      (let o := k0AutOrder [x, y] (k0pPow A.row.rho s)
       if A.row.d = 2 ∧ s % 2 = 1 then
         (if o = 1 then 2 else if o = 2 then 1 else o) else o) := by
    simp only [lqTw]
    rw [← lk0xlqtwa2_lqNodes_eq A P j, hxy, hct']
    simp only [k0Tau0Of]
    norm_num
    rw [show (P.orbitNodes j).length = s from rfl]
  have hd12 : A.row.d = 1 ∨ A.row.d = 2 := by
    rw [A.row.d_eq]; split <;> simp
  have hεs_odd : s % 2 = 1 → A.epsilon ^ s = (if A.row.d = 1 then 1 else -1) := by
    intro hodd
    rw [A.epsilon_eq]
    by_cases h1 : A.row.d = 1
    · rw [if_pos h1]; simp
    · rw [if_neg h1]; exact (Nat.odd_iff.mpr hodd).neg_one_pow
  have hεs_even : s % 2 = 0 → A.epsilon ^ s = 1 := by
    intro heven
    rw [A.epsilon_eq]
    by_cases h1 : A.row.d = 1
    · rw [if_pos h1]; simp
    · rw [if_neg h1]; exact (Nat.even_iff.mpr heven).neg_one_pow
  have hεvals : A.epsilon^s = 1 ∨ A.epsilon^s = -1 := by
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
    rcases hε with hε | hε <;> rw [hε]
    · exact Or.inl (one_pow _)
    · rcases Nat.even_or_odd s with he | ho
      · exact Or.inl he.neg_one_pow
      · exact Or.inr ho.neg_one_pow
  have hbridge : lqTw A P j = 1 ↔
      (((A.row.nodePerm^[s]) ix = ix ∧ A.epsilon^s = 1) ∨
        ((A.row.nodePerm^[s]) ix = iy ∧ A.epsilon^s = -1)) := by
    rw [htw_eq, h_o]
    have hmodlt : s % 2 < 2 := Nat.mod_lt s (by norm_num)
    by_cases hpx : (A.row.nodePerm^[s]) ix = ix
    · rw [if_pos hpx]
      have hpiy : ¬ (A.row.nodePerm^[s]) ix = iy := by
        intro hh; rw [hpx] at hh; exact hxy_ne hh
      by_cases hodd : s % 2 = 1
      · rw [hεs_odd hodd]
        rcases hd12 with hd | hd <;> simp [hd, hodd, hpx, hpiy, hxy_ne, hxy_ne']
      · have heven : s % 2 = 0 := by omega
        rw [hεs_even heven]
        rcases hd12 with hd | hd <;> simp [hd, hodd, heven, hpx, hpiy, hxy_ne, hxy_ne']
    · have hpiy : (A.row.nodePerm^[s]) ix = iy := by
        rcases hp_id_or_swap with ⟨hpx', -⟩ | ⟨hpx', -⟩
        · exact absurd hpx' hpx
        · exact hpx'
      rw [if_neg hpx]
      by_cases hodd : s % 2 = 1
      · rw [hεs_odd hodd]
        rcases hd12 with hd | hd <;> simp [hd, hodd, hpx, hpiy, hxy_ne, hxy_ne']
      · have heven : s % 2 = 0 := by omega
        rw [hεs_even heven]
        rcases hd12 with hd | hd <;> simp [hd, hodd, heven, hpx, hpiy, hxy_ne, hxy_ne']
  constructor
  · intro htw
    have hcases := hbridge.mp htw
    let φ : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℤ) := (A.frobLinear ^ s).toLinearMap
    have hφρ : ∀ γ ∈ Ψ,
        ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) γ = φ γ := by
      intro γ hγ
      rw [lk0xlqtwa2_rho_iterate_frobLinear A s (hroot γ hγ)]
      exact (LinearEquiv.pow_apply A.frobLinear s γ).symm
    have hspan_mem : ∀ γ ∈ Ψ, γ ∈ Submodule.span ℤ {α, β} := by
      intro γ hγ
      have h := hγ
      rw [hΨ, P.repr_roots j] at h
      rw [hset_pair] at h
      exact h.2
    have hinner : twistInner Ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
      rcases hcases with ⟨hpx, heps⟩ | ⟨hpx, heps⟩
      ·
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        intro γ hγ
        have hγα : φ α = (1 : WeylGroup A.tau) • α := by
          rw [← hφρ α hαΨ]
          have h := lk0xlqtwist_frob_nodes_iterate A s ix
          rw [hpx, heps, one_smul] at h
          rw [h, one_smul]
        have hγβ : φ β = (1 : WeylGroup A.tau) • β := by
          rw [← hφρ β hβΨ]
          have h := lk0xlqtwist_frob_nodes_iterate A s iy
          have hpy : (A.row.nodePerm^[s]) iy = iy := by
            rcases hp_id_or_swap with ⟨-, hpy⟩ | ⟨hx', hy'⟩
            · exact hpy
            · exfalso; exact hxy_ne (hpx.symm.trans hx')
          rw [hpy, heps, one_smul] at h
          rw [h, one_smul]
        have hφγ : φ γ = (1 : WeylGroup A.tau) • γ := by
          refine Submodule.span_induction (p := fun z _ => φ z = (1 : WeylGroup A.tau) • z)
            ?_ ?_ ?_ ?_ (hspan_mem γ hγ)
          · intro z hz
            rcases (by simpa using hz : z = α ∨ z = β) with rfl | rfl
            · exact hγα
            · exact hγβ
          · simp
          · intro a b _ _ ha hb; rw [map_add, smul_add, ha, hb]
          · intro c z _ hz; rw [map_zsmul, smul_comm, hz]
        rw [hφρ γ hγ, hφγ]
      ·
        let w : WeylGroup A.tau := rootReflection α * rootReflection β * rootReflection α
        have hcorαα : corootPair α α = 2 := by
          unfold corootPair; rw [hαα]
          rw [show 2 * (2 * m) = (2 * m) * 2 by ring]
          exact Int.mul_ediv_cancel_left 2 (by positivity)
        have hcorββ : corootPair β β = 2 := by
          unfold corootPair; rw [hββ]
          rw [show 2 * (2 * m) = (2 * m) * 2 by ring]
          exact Int.mul_ediv_cancel_left 2 (by positivity)
        have hcorαβ : corootPair α β = -1 := by
          unfold corootPair; rw [hαα, hαβ]
          rw [show 2 * (-m) = (2 * m) * (-1) by ring]
          exact Int.mul_ediv_cancel_left (-1) (by positivity)
        have hcorβα : corootPair β α = -1 := by
          unfold corootPair; rw [hββ, hβα]
          rw [show 2 * (-m) = (2 * m) * (-1) by ring]
          exact Int.mul_ediv_cancel_left (-1) (by positivity)
        have hrαα : rootReflection α • α = -α := rootReflection_smul_self hαroot
        have hrββ : rootReflection β • β = -β := rootReflection_smul_self hβroot
        have hrαβ : rootReflection α • β = α + β := by
          rw [rootReflection_smul hαroot, hcorαβ]; abel
        have hrβα : rootReflection β • α = α + β := by
          rw [rootReflection_smul hβroot, hcorβα]; abel
        have hrβneg : rootReflection β • (-α) = -(α + β) := by rw [smul_neg, hrβα]
        have hrβ : rootReflection β • (α + β) = α := by rw [smul_add, hrβα, hrββ]; abel
        have hrα : rootReflection α • (α + β) = β := by rw [smul_add, hrαα, hrαβ]; abel
        have hwα : w • α = -β := by
          dsimp [w]; rw [mul_smul, mul_smul, hrαα, hrβneg, smul_neg, hrα]
        have hwβ : w • β = -α := by
          dsimp [w]; rw [mul_smul, mul_smul, hrαβ, hrβ, hrαα]
        refine ⟨w, ?_, ?_⟩
        · change (rootReflection α * rootReflection β * rootReflection α) ∈
            Subgroup.closure {s : WeylGroup A.tau | ∃ γ ∈ Ψ, s = rootReflection γ}
          exact Subgroup.mul_mem _
            (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨α, hαΨ, rfl⟩)
              (Subgroup.subset_closure ⟨β, hβΨ, rfl⟩))
            (Subgroup.subset_closure ⟨α, hαΨ, rfl⟩)
        · intro γ hγ
          have hγα : φ α = w • α := by
            rw [← hφρ α hαΨ]
            have h := lk0xlqtwist_frob_nodes_iterate A s ix
            rw [hpx, heps] at h
            rw [h]
            simpa [β] using hwα.symm
          have hγβ : φ β = w • β := by
            rw [← hφρ β hβΨ]
            have h := lk0xlqtwist_frob_nodes_iterate A s iy
            have hpy : (A.row.nodePerm^[s]) iy = ix := by
              rcases hp_id_or_swap with ⟨-, hpy⟩ | ⟨-, hpy⟩
              · exfalso
                exact hxy_ne' ((A.row.nodePerm.injective).iterate s (by rw [hpy, hpx]))
              · exact hpy
            rw [hpy, heps] at h
            rw [h]
            simpa [α] using hwβ.symm
          have hφγ : φ γ = w • γ := by
            refine Submodule.span_induction (p := fun z _ => φ z = w • z) ?_ ?_ ?_ ?_
              (hspan_mem γ hγ)
            · intro z hz
              rcases (by simpa using hz : z = α ∨ z = β) with rfl | rfl
              · exact hγα
              · exact hγβ
            · simp
            · intro a b _ _ ha hb; rw [map_add, smul_add, ha, hb]
            · intro c z _ hz; rw [map_zsmul, smul_comm, hz]
          rw [hφρ γ hγ, hφγ]
    unfold twistKind
    rw [show componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j)) = s from
      hs_len.symm]
    rw [← hΨ]
    rw [if_pos hinner]
  · intro htw
    have hcond : ¬ (((A.row.nodePerm^[s]) ix = ix ∧ A.epsilon^s = 1) ∨
        ((A.row.nodePerm^[s]) ix = iy ∧ A.epsilon^s = -1)) := fun h => htw (hbridge.mpr h)
    let φ : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℤ) := (A.frobLinear ^ s).toLinearMap
    have hφρ : ∀ γ ∈ Ψ,
        ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) γ = φ γ := by
      intro γ hγ
      rw [lk0xlqtwa2_rho_iterate_frobLinear A s (hroot γ hγ)]
      exact (LinearEquiv.pow_apply A.frobLinear s γ).symm
    have hφα0 : φ α = A.epsilon ^ s •
        A.nodeMap (Pi.single ((A.row.nodePerm^[s]) ix) 1) := by
      rw [← hφρ α hαΨ]
      exact lk0xlqtwist_frob_nodes_iterate A s ix
    have hφβ0 : φ β = A.epsilon ^ s •
        A.nodeMap (Pi.single ((A.row.nodePerm^[s]) iy) 1) := by
      rw [← hφρ β hβΨ]
      exact lk0xlqtwist_frob_nodes_iterate A s iy
    have hout : ((A.row.nodePerm^[s]) ix = ix ∧ (A.row.nodePerm^[s]) iy = iy ∧
        A.epsilon^s = -1) ∨
        ((A.row.nodePerm^[s]) ix = iy ∧ (A.row.nodePerm^[s]) iy = ix ∧ A.epsilon^s = 1) := by
      rcases hp_id_or_swap with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rcases hεvals with he | he
        · exact absurd (Or.inl ⟨hx, he⟩) hcond
        · exact Or.inl ⟨hx, hy, he⟩
      · rcases hεvals with he | he
        · exact Or.inr ⟨hx, hy, he⟩
        · exact absurd (Or.inr ⟨hx, he⟩) hcond
    have hμmem : (2 : ℤ) • α + β ∈ Submodule.span ℤ Ψ := by
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hαΨ))
        (Submodule.subset_span hβΨ)
    have hmul : ∀ p : ℤ × ℤ,
        iform ((2 : ℤ) • α + β) (p.1 • α + p.2 • β) =
          m * 3 * p.1 := by
      intro p
      simp only [iform_add_left,
        iform_add_right,
        iform_smul_left,
        iform_smul_right, hαα, hββ, hαβ, hβα]
      ring
    have hdiv : ∀ γ ∈ Ψ, m * 3 ∣ iform ((2 : ℤ) • α + β) γ := by
      intro γ hγ
      rw [hΨeq] at hγ
      obtain ⟨p, hp, rfl⟩ := hγ
      exact ⟨p.1, hmul p⟩
    have hμμ : iform ((2 : ℤ) • α + β) ((2 : ℤ) • α + β) =
        6 * m := by
      have h := hmul (2, 1)
      dsimp only at h
      simp only [one_smul] at h
      linarith
    have hnot : ¬ twistInner Ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
      rw [lk0xlqtwa2_twistInner_congr hφρ]
      rcases hout with ⟨hx, hy, he⟩ | ⟨hx, hy, he⟩
      ·
        have hφα : φ α = -α := by
          rw [hφα0, hx, he, neg_one_smul]
        have hφβ : φ β = -β := by
          rw [hφβ0, hy, he, neg_one_smul]
        refine lk0xlqtwa2_not_twistInner_of_disc (Ψ := Ψ) m hmpos hroot hsl hpair
          φ.toAddMonoidHom (d := m * 3) (e := 3) rfl hμmem hdiv hdiv ?_
        have hval : iform ((2 : ℤ) • α + β)
            (φ.toAddMonoidHom ((2 : ℤ) • α + β) - ((2 : ℤ) • α + β)) = -12 * m := by
          have hσμ : φ.toAddMonoidHom ((2 : ℤ) • α + β) - ((2 : ℤ) • α + β) =
              (-4 : ℤ) • α + (-2 : ℤ) • β := by
            change φ ((2 : ℤ) • α + β) - ((2 : ℤ) • α + β) = _
            rw [map_add, map_zsmul, hφα, hφβ]
            module
          rw [hσμ]
          have h := hmul (-4, -2)
          dsimp only at h
          rw [h]
          ring
        rintro ⟨k, hk⟩
        rw [hval] at hk
        have h1 : (-12 : ℤ) * m = (9 * k) * m := by rw [hk]; ring
        have h2 := Int.eq_of_mul_eq_mul_right (by omega) h1
        omega
      ·
        have hφα : φ α = β := by
          rw [hφα0, hx, he, one_smul]
        have hφβ : φ β = α := by
          rw [hφβ0, hy, he, one_smul]
        refine lk0xlqtwa2_not_twistInner_of_disc (Ψ := Ψ) m hmpos hroot hsl hpair
          φ.toAddMonoidHom (d := m * 3) (e := 3) rfl hμmem hdiv hdiv ?_
        have hval : iform ((2 : ℤ) • α + β)
            (φ.toAddMonoidHom ((2 : ℤ) • α + β) - ((2 : ℤ) • α + β)) = -3 * m := by
          have hσμ : φ.toAddMonoidHom ((2 : ℤ) • α + β) = α + (2 : ℤ) • β := by
            change φ ((2 : ℤ) • α + β) = _
            rw [map_add, map_zsmul, hφα, hφβ]
            abel
          rw [hσμ]
          have h3 := hmul (-1, 1)
          have h4 := hmul (1, 0)
          have hsplit : α + (2 : ℤ) • β - ((2 : ℤ) • α + β) = (-1 : ℤ) • α + (1 : ℤ) • β := by
            simp only [neg_smul, one_smul, two_smul]; abel
          rw [hsplit, h3]
          ring
        rintro ⟨k, hk⟩
        rw [hval] at hk
        have h1 : (-3 : ℤ) * m = (9 * k) * m := by rw [hk]; ring
        have h2 := Int.eq_of_mul_eq_mul_right (by omega) h1
        omega
    unfold twistKind
    rw [show componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j)) = s from
      hs_len.symm]
    rw [← hΨ]
    rw [if_neg hnot]
    have hc1 : ¬ ((compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨ (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
        ¬ twistInner Ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]))) := by
      rw [hcompRank, hncard]
      omega
    have hc2 : ¬ (4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) := by
      rw [hcompRank]
      omega
    rw [if_neg hc1, if_neg hc2, if_pos]
    rw [hcompRank, hncard]
    exact ⟨le_refl 2, rfl⟩

end CFSG.StandardType.GGK0LQ

end
