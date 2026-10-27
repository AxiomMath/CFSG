module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowCoker

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrv4c1_zero_le_nodeSub {lab : LargeEvenLabel} {p : ℕ}
    (row : KacRow lab p) (ε q : ℤ) :
    zeroNodeLattice row ≤ nodeSub row ε q := by
  rw [nodeSub, zeroNodeLattice]
  exact le_sup_of_le_left le_sup_right

private lemma ltrv4c1_zero_mem {lab : LargeEvenLabel} {p : ℕ}
    (row : KacRow lab p) (i : Fin row.diagram.marks.length)
    (hi : row.s.getD i.val 0 = 0) :
    Pi.single i (1 : ℤ) ∈ zeroNodeLattice row := by
  rw [zeroNodeLattice]
  exact Submodule.subset_span ⟨i, hi, rfl⟩

private lemma ltrv4c1_defect_le_nodeSub {lab : LargeEvenLabel} {p : ℕ}
    (row : KacRow lab p) (ε q : ℤ) :
    nodeDefect row ε q ≤ nodeSub row ε q := by
  rw [nodeSub]
  exact le_sup_right

private lemma ltrv4c1_nodePermMap_single {lab : LargeEvenLabel} {p : ℕ}
    (row : KacRow lab p) (i : Fin row.diagram.marks.length) :
    nodePermMap row (Pi.single i (1 : ℤ)) = Pi.single (row.nodePerm i) (1 : ℤ) := by
  funext j
  simp [nodePermMap, LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

private lemma ltrv4c1_marks_mem_nodeSub {lab : LargeEvenLabel} {p : ℕ}
    (row : KacRow lab p) (ε q : ℤ) :
    nodeMarks row ∈ nodeSub row ε q := by
  rw [nodeSub]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _)))

private theorem ltrv4c1_finite_cyclic_of_gen (N : ℕ) (S : Submodule ℤ (Fin N → ℤ))
    (g : Fin N → ℤ) (n : ℕ) (hn : n ≠ 0)
    (hgen : ∀ i : Fin N, ∃ k : ℤ, (Pi.single i (1 : ℤ) : Fin N → ℤ) - k • g ∈ S)
    (hkill : ((n : ℤ) • g : Fin N → ℤ) ∈ S) :
    Finite ((Fin N → ℤ) ⧸ S) ∧ IsAddCyclic ((Fin N → ℤ) ⧸ S) := by
  classical
  let F : ℤ →+ ((Fin N → ℤ) ⧸ S) :=
    { toFun := fun k => S.mkQ (k • g)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }
  have hFn : F (n : ℤ) = 0 := by
    change S.mkQ ((n : ℤ) • g) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr hkill
  let F' : { f : ℤ →+ ((Fin N → ℤ) ⧸ S) // f (n : ℤ) = 0 } := ⟨F, hFn⟩
  let φ : ZMod n →+ ((Fin N → ℤ) ⧸ S) := (ZMod.lift n) F'
  have hφsurj : Function.Surjective φ := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ m =>
      choose k hk using hgen
      let K : ℤ := ∑ i : Fin N, m i * k i
      refine ⟨(K : ZMod n), ?_⟩
      have hm : (∑ i : Fin N, Pi.single i (m i) : Fin N → ℤ) = m := by
        funext j
        simpa using Fintype.sum_pi_single j m
      have hsingle : ∀ i : Fin N, (Pi.single i (m i) : Fin N → ℤ) =
          (m i) • (Pi.single i (1 : ℤ) : Fin N → ℤ) := by
        intro i
        funext j
        simp [Pi.single_apply, Pi.smul_apply]
      have hq : ∀ i : Fin N, S.mkQ (Pi.single i (1 : ℤ)) = S.mkQ (k i • g) := by
        intro i
        change Submodule.Quotient.mk (Pi.single i (1 : ℤ)) = Submodule.Quotient.mk (k i • g)
        rw [Submodule.Quotient.eq]
        exact hk i
      have hterm : ∀ i : Fin N, S.mkQ (Pi.single i (m i)) = (m i * k i) • S.mkQ g := by
        intro i
        rw [hsingle i, map_smul, hq i, map_smul, smul_smul]
      have hmk : S.mkQ m = ∑ i : Fin N, S.mkQ (Pi.single i (m i)) := by
        conv_lhs => rw [← hm]
        exact map_sum S.mkQ (fun i => Pi.single i (m i)) Finset.univ
      have hgoal : S.mkQ m = S.mkQ (K • g) := by
        calc
          S.mkQ m = ∑ i : Fin N, S.mkQ (Pi.single i (m i)) := hmk
          _ = ∑ i : Fin N, (m i * k i) • S.mkQ g := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
          _ = K • S.mkQ g := by
            rw [← Finset.sum_smul]
          _ = S.mkQ (K • g) := by
            rw [map_smul]
      have hφK : φ (K : ZMod n) = S.mkQ (K • g) := by
        simp [φ, ZMod.lift_coe, F, F']
      rw [hφK, ← hgoal]
      rfl
  haveI : NeZero n := ⟨hn⟩
  have hfin : Finite ((Fin N → ℤ) ⧸ S) := Finite.of_surjective φ hφsurj
  have hcyc : IsAddCyclic ((Fin N → ℤ) ⧸ S) := isAddCyclic_of_surjective φ hφsurj
  exact ⟨hfin, hcyc⟩

theorem nodeCokerCyclicR1_holds : NodeCokerCyclicR1 := by
  intro lab p row hT hdata ε q hε hq
  rcases row with ⟨T, tw, type_eq, d, d_eq, s, s_length, s_mem, s_min,
    base, base_eq, rho, rho_length, rho_mem, nodePerm, rho_apply, D, D_eq, valid⟩
  subst hT
  rcases hdata with ⟨hs, hrho⟩
  subst hrho
  let row' : KacRow lab p :=
    { T := .E6, tw := tw, type_eq := type_eq, d := d, d_eq := d_eq,
      s := s, s_length := s_length, s_mem := s_mem, s_min := s_min,
      base := base, base_eq := base_eq, rho := [0, 1, 2, 3, 4, 5, 6],
      rho_length := rho_length, rho_mem := rho_mem, nodePerm := nodePerm,
      rho_apply := rho_apply, D := D, D_eq := D_eq, valid := valid }
  let S : Submodule ℤ (NodeLat row') := nodeSub row' ε q
  have hperm : nodePerm = 1 := by
    ext i
    have h := rho_apply i
    fin_cases i <;> simpa using h.symm
  have hmarks_eq : nodeMarks row' =
      (Pi.single (0 : Fin 7) (1 : ℤ) + Pi.single (1 : Fin 7) (1 : ℤ)
        + 2 • Pi.single (2 : Fin 7) (1 : ℤ) + 2 • Pi.single (3 : Fin 7) (1 : ℤ)
        + 3 • Pi.single (4 : Fin 7) (1 : ℤ) + 2 • Pi.single (5 : Fin 7) (1 : ℤ)
        + Pi.single (6 : Fin 7) (1 : ℤ) : NodeLat row') := by
    funext i
    fin_cases i <;> rfl
  have hz_getD (i : ℕ) (h0 : [0, 1, 0, 0, 0, 0, 2].getD i 0 = 0)
      (h1 : [0, 2, 0, 0, 0, 0, 1].getD i 0 = 0) : s.getD i 0 = 0 := by
    rcases hs with h | h
    · change s = [0, 1, 0, 0, 0, 0, 2] at h
      rw [h]; exact h0
    · change s = [0, 2, 0, 0, 0, 0, 1] at h
      rw [h]; exact h1
  have hz0s : s.getD 0 0 = 0 := hz_getD 0 rfl rfl
  have hz2s : s.getD 2 0 = 0 := hz_getD 2 rfl rfl
  have hz3s : s.getD 3 0 = 0 := hz_getD 3 rfl rfl
  have hz4s : s.getD 4 0 = 0 := hz_getD 4 rfl rfl
  have hz5s : s.getD 5 0 = 0 := hz_getD 5 rfl rfl
  have hz0 : (Pi.single (0 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (0 : Fin 7) hz0s
  have hz2 : (Pi.single (2 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (2 : Fin 7) hz2s
  have hz3 : (Pi.single (3 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (3 : Fin 7) hz3s
  have hz4 : (Pi.single (4 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (4 : Fin 7) hz4s
  have hz5 : (Pi.single (5 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (5 : Fin 7) hz5s
  have hmarks_mem : nodeMarks row' ∈ S := ltrv4c1_marks_mem_nodeSub row' ε q
  let hzsum : NodeLat row' := Pi.single (0 : Fin 7) (1 : ℤ) + 2 • Pi.single (2 : Fin 7) (1 : ℤ)
      + 2 • Pi.single (3 : Fin 7) (1 : ℤ) + 3 • Pi.single (4 : Fin 7) (1 : ℤ)
      + 2 • Pi.single (5 : Fin 7) (1 : ℤ)
  have hzsum_mem : hzsum ∈ S := by
    dsimp [hzsum]
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem hz0 (S.smul_mem 2 hz2))
      (S.smul_mem 2 hz3)) (S.smul_mem 3 hz4)) (S.smul_mem 2 hz5)
  have heq : (Pi.single (1 : Fin 7) (1 : ℤ) + Pi.single (6 : Fin 7) (1 : ℤ) : NodeLat row') =
      nodeMarks row' - hzsum := by
    rw [hmarks_eq]
    dsimp [hzsum]
    funext i
    fin_cases i <;> rfl
  have hrel : (Pi.single (1 : Fin 7) (1 : ℤ) + Pi.single (6 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    rw [heq]
    exact S.sub_mem hmarks_mem hzsum_mem
  let g : NodeLat row' := Pi.single (6 : Fin 7) (1 : ℤ)
  have hPg : nodePermMap row' g = g := by
    have h := ltrv4c1_nodePermMap_single row' (6 : Fin 7)
    have hperm' : row'.nodePerm = 1 := hperm
    rw [hperm'] at h
    simpa [g, id] using h
  have hdefect : ((ε - q) • g : NodeLat row') ∈ nodeDefect row' ε q := by
    refine ⟨g, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hPg]
    rw [sub_smul]
  have hdefect_mem : ((ε - q) • g : NodeLat row') ∈ S :=
    ltrv4c1_defect_le_nodeSub row' ε q hdefect
  have hnpos : 0 < q - ε := by
    rcases hε with rfl | rfl <;> linarith
  let n : ℕ := (q - ε).natAbs
  have hn : n ≠ 0 := by
    intro h
    have hcast : (n : ℤ) = 0 := by exact_mod_cast h
    have hncast : (n : ℤ) = q - ε := by
      dsimp [n]
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos)]
    rw [hncast] at hcast
    linarith
  have hkill : ((n : ℤ) • g : NodeLat row') ∈ S := by
    have hcast : (n : ℤ) = q - ε := by
      dsimp [n]
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos)]
    rw [hcast]
    have hqε : q - ε = -(ε - q) := by ring
    rw [hqε, neg_smul]
    exact S.neg_mem hdefect_mem
  have hgen : ∀ i : Fin 7, ∃ k : ℤ, (Pi.single i (1 : ℤ) : NodeLat row') - k • g ∈ S := by
    intro i
    fin_cases i
    · exact ⟨0, by simpa using hz0⟩
    · refine ⟨-1, ?_⟩
      convert hrel using 1
      simp [g, neg_smul, sub_eq_add_neg]
      rfl
    · exact ⟨0, by simpa using hz2⟩
    · exact ⟨0, by simpa using hz3⟩
    · exact ⟨0, by simpa using hz4⟩
    · exact ⟨0, by simpa using hz5⟩
    · exact ⟨1, by simpa [g] using (Submodule.zero_mem S : (0 : NodeLat row') ∈ S)⟩
  have hmain := ltrv4c1_finite_cyclic_of_gen (N := 7) S g n hn hgen hkill
  exact hmain

theorem nodeCokerCyclicR3_holds : NodeCokerCyclicR3 := by
  intro lab p row hT hdata ε q hε hq
  rcases row with ⟨T, tw, type_eq, d, d_eq, s, s_length, s_mem, s_min,
    base, base_eq, rho, rho_length, rho_mem, nodePerm, rho_apply, D, D_eq, valid⟩
  subst hT
  rcases hdata with ⟨hs, hrho⟩
  change rho = [1, 6, 3, 5, 4, 2, 0] ∨ rho = [6, 0, 5, 2, 4, 3, 1] at hrho
  subst hs
  let row' : KacRow lab p :=
    { T := .E6, tw := tw, type_eq := type_eq, d := d, d_eq := d_eq,
      s := [0, 0, 0, 0, 1, 0, 0], s_length := s_length, s_mem := s_mem, s_min := s_min,
      base := base, base_eq := base_eq, rho := rho,
      rho_length := rho_length, rho_mem := rho_mem, nodePerm := nodePerm,
      rho_apply := rho_apply, D := D, D_eq := D_eq, valid := valid }
  let S : Submodule ℤ (NodeLat row') := nodeSub row' ε q
  have hperm4 : nodePerm (4 : Fin 7) = (4 : Fin 7) := by
    apply Fin.ext
    have h := rho_apply (4 : Fin 7)
    rcases hrho with hrho | hrho <;> rw [hrho] at h <;> simpa using h.symm
  have hz0 : (Pi.single (0 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (0 : Fin 7) rfl
  have hz1 : (Pi.single (1 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (1 : Fin 7) rfl
  have hz2 : (Pi.single (2 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (2 : Fin 7) rfl
  have hz3 : (Pi.single (3 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (3 : Fin 7) rfl
  have hz5 : (Pi.single (5 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (5 : Fin 7) rfl
  have hz6 : (Pi.single (6 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (6 : Fin 7) rfl
  let g : NodeLat row' := Pi.single (4 : Fin 7) (1 : ℤ)
  have hPg : nodePermMap row' g = g := by
    have h := ltrv4c1_nodePermMap_single row' (4 : Fin 7)
    have hperm4' : row'.nodePerm (4 : Fin 7) = (4 : Fin 7) := hperm4
    rw [hperm4'] at h
    simpa [g, id] using h
  have hdefect : ((ε - q) • g : NodeLat row') ∈ nodeDefect row' ε q := by
    refine ⟨g, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hPg]
    rw [sub_smul]
  have hdefect_mem : ((ε - q) • g : NodeLat row') ∈ S :=
    ltrv4c1_defect_le_nodeSub row' ε q hdefect
  have hnpos : 0 < q - ε := by
    rcases hε with rfl | rfl <;> linarith
  let n : ℕ := (q - ε).natAbs
  have hn : n ≠ 0 := by
    intro h
    have hcast : (n : ℤ) = 0 := by exact_mod_cast h
    have hncast : (n : ℤ) = q - ε := by
      dsimp [n]
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos)]
    rw [hncast] at hcast
    linarith
  have hkill : ((n : ℤ) • g : NodeLat row') ∈ S := by
    have hcast : (n : ℤ) = q - ε := by
      dsimp [n]
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos)]
    rw [hcast]
    have hqε : q - ε = -(ε - q) := by ring
    rw [hqε, neg_smul]
    exact S.neg_mem hdefect_mem
  have hgen : ∀ i : Fin 7, ∃ k : ℤ, (Pi.single i (1 : ℤ) : NodeLat row') - k • g ∈ S := by
    intro i
    fin_cases i
    · exact ⟨0, by simpa using hz0⟩
    · exact ⟨0, by simpa using hz1⟩
    · exact ⟨0, by simpa using hz2⟩
    · exact ⟨0, by simpa using hz3⟩
    · exact ⟨1, by simpa [g] using (Submodule.zero_mem S : (0 : NodeLat row') ∈ S)⟩
    · exact ⟨0, by simpa using hz5⟩
    · exact ⟨0, by simpa using hz6⟩
  have hmain := ltrv4c1_finite_cyclic_of_gen (N := 7) S g n hn hgen hkill
  exact hmain

theorem nodeCokerCyclicR4_holds : NodeCokerCyclicR4 := by
  intro lab p row hT hdata ε q hε hq
  rcases row with ⟨T, tw, type_eq, d, d_eq, s, s_length, s_mem, s_min,
    base, base_eq, rho, rho_length, rho_mem, nodePerm, rho_apply, D, D_eq, valid⟩
  subst hT
  rcases hdata with ⟨hs, hrho⟩
  subst hrho
  subst hs
  let row' : KacRow lab p :=
    { T := .E6, tw := tw, type_eq := type_eq, d := d, d_eq := d_eq,
      s := [0, 0, 0, 0, 0, 1, 1], s_length := s_length, s_mem := s_mem, s_min := s_min,
      base := base, base_eq := base_eq, rho := [0, 1, 2, 3, 4, 5, 6],
      rho_length := rho_length, rho_mem := rho_mem, nodePerm := nodePerm,
      rho_apply := rho_apply, D := D, D_eq := D_eq, valid := valid }
  let S : Submodule ℤ (NodeLat row') := nodeSub row' ε q
  have hperm : nodePerm = 1 := by
    ext i
    have h := rho_apply i
    fin_cases i <;> simpa using h.symm
  have hmarks_eq : nodeMarks row' =
      (Pi.single (0 : Fin 7) (1 : ℤ) + Pi.single (1 : Fin 7) (1 : ℤ)
        + 2 • Pi.single (2 : Fin 7) (1 : ℤ) + 2 • Pi.single (3 : Fin 7) (1 : ℤ)
        + 3 • Pi.single (4 : Fin 7) (1 : ℤ) + 2 • Pi.single (5 : Fin 7) (1 : ℤ)
        + Pi.single (6 : Fin 7) (1 : ℤ) : NodeLat row') := by
    funext i
    fin_cases i <;> rfl
  have hz0 : (Pi.single (0 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (0 : Fin 7) rfl
  have hz1 : (Pi.single (1 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (1 : Fin 7) rfl
  have hz2 : (Pi.single (2 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (2 : Fin 7) rfl
  have hz3 : (Pi.single (3 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (3 : Fin 7) rfl
  have hz4 : (Pi.single (4 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    apply ltrv4c1_zero_le_nodeSub row' ε q
    exact ltrv4c1_zero_mem row' (4 : Fin 7) rfl
  have hmarks_mem : nodeMarks row' ∈ S := ltrv4c1_marks_mem_nodeSub row' ε q
  let hzsum : NodeLat row' := Pi.single (0 : Fin 7) (1 : ℤ) + Pi.single (1 : Fin 7) (1 : ℤ)
      + 2 • Pi.single (2 : Fin 7) (1 : ℤ) + 2 • Pi.single (3 : Fin 7) (1 : ℤ)
      + 3 • Pi.single (4 : Fin 7) (1 : ℤ)
  have hzsum_mem : hzsum ∈ S := by
    dsimp [hzsum]
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem hz0 hz1) (S.smul_mem 2 hz2))
      (S.smul_mem 2 hz3)) (S.smul_mem 3 hz4)
  have heq : (Pi.single (6 : Fin 7) (1 : ℤ) + 2 • Pi.single (5 : Fin 7) (1 : ℤ) : NodeLat row') =
      nodeMarks row' - hzsum := by
    rw [hmarks_eq]
    dsimp [hzsum]
    funext i
    fin_cases i <;> rfl
  have hrel : (Pi.single (6 : Fin 7) (1 : ℤ) + 2 • Pi.single (5 : Fin 7) (1 : ℤ) : NodeLat row') ∈ S := by
    rw [heq]
    exact S.sub_mem hmarks_mem hzsum_mem
  let g : NodeLat row' := Pi.single (5 : Fin 7) (1 : ℤ)
  have hPg : nodePermMap row' g = g := by
    have h := ltrv4c1_nodePermMap_single row' (5 : Fin 7)
    have hperm' : row'.nodePerm = 1 := hperm
    rw [hperm'] at h
    simpa [g, id] using h
  have hdefect : ((ε - q) • g : NodeLat row') ∈ nodeDefect row' ε q := by
    refine ⟨g, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hPg]
    rw [sub_smul]
  have hdefect_mem : ((ε - q) • g : NodeLat row') ∈ S :=
    ltrv4c1_defect_le_nodeSub row' ε q hdefect
  have hnpos : 0 < q - ε := by
    rcases hε with rfl | rfl <;> linarith
  let n : ℕ := (q - ε).natAbs
  have hn : n ≠ 0 := by
    intro h
    have hcast : (n : ℤ) = 0 := by exact_mod_cast h
    have hncast : (n : ℤ) = q - ε := by
      dsimp [n]
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos)]
    rw [hncast] at hcast
    linarith
  have hkill : ((n : ℤ) • g : NodeLat row') ∈ S := by
    have hcast : (n : ℤ) = q - ε := by
      dsimp [n]
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos)]
    rw [hcast]
    have hqε : q - ε = -(ε - q) := by ring
    rw [hqε, neg_smul]
    exact S.neg_mem hdefect_mem
  have hgen : ∀ i : Fin 7, ∃ k : ℤ, (Pi.single i (1 : ℤ) : NodeLat row') - k • g ∈ S := by
    intro i
    fin_cases i
    · exact ⟨0, by simpa using hz0⟩
    · exact ⟨0, by simpa using hz1⟩
    · exact ⟨0, by simpa using hz2⟩
    · exact ⟨0, by simpa using hz3⟩
    · exact ⟨0, by simpa using hz4⟩
    · exact ⟨1, by simpa [g] using (Submodule.zero_mem S : (0 : NodeLat row') ∈ S)⟩
    · refine ⟨-2, ?_⟩
      convert hrel using 1
      simp [g, neg_smul, sub_eq_add_neg]
      rfl
  have hmain := ltrv4c1_finite_cyclic_of_gen (N := 7) S g n hn hgen hkill
  exact hmain

end CFSG.StandardType.E6Centralizer1585

end
