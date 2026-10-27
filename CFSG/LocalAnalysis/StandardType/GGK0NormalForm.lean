module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
import CFSG.LocalAnalysis.StandardType.GGKacTableShapes

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

@[expose] def K0LangMark.kacMu (A : K0LangMark Omega lab p R I phi) : Fin A.tau.rank → ℤ :=
  fun j => (A.row.s.getD (j.val + 1) 0 : ℤ)

structure K0Normal (A : K0LangMark Omega lab p R I phi) where
  K : KacData A.tau
  facts : K.Facts
  length_eq : A.row.diagram.marks.length = A.tau.rank + 1
  mark_zero : A.row.diagram.marks.getD 0 0 = 1
  θ_eq : ∀ j : Fin A.tau.rank, K.θ j = (A.row.diagram.marks.getD (j.val + 1) 0 : ℤ)
  adj_iff : ∀ i j, i < A.tau.rank + 1 → j < A.tau.rank + 1 →
    (K.Adj (idxNode i) (idxNode j) ↔ 0 < A.row.diagram.adj i j)

private theorem k0DiagOf_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

omit [CharP Omega 2] in
private theorem k0LangMark_marks_length (A : K0LangMark Omega lab p R I phi) :
    A.row.diagram.marks.length = A.tau.rank + 1 := by
  rw [← A.tau_eq]
  exact k0DiagOf_marks_length A.row.T

omit [CharP Omega 2] in
private theorem k0LangMark_weighted_sum (A : K0LangMark Omega lab p R I phi) :
    (∑ i : Fin A.row.diagram.marks.length,
      A.row.diagram.marks.getD i.val 0 * A.row.s.getD i.val 0) = p :=
  ggKacShVecs_sum _ _ _ A.row.s_mem

private theorem k0_rootChar_single {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) (j : Fin τ.rank) :
    rootChar a (Pi.single j 1) = a j := by
  simpa using rootChar_nsmul_single a j 1

omit [CharP Omega 2] in
private theorem k0_a_eq_zeta_kacMu (A : K0LangMark Omega lab p R I phi) :
    A.a = fun j => A.zeta ^ A.kacMu j := by
  funext j
  have hlen := k0LangMark_marks_length A
  have hi : j.val + 1 < A.row.diagram.marks.length := by omega
  let i : Fin A.row.diagram.marks.length := ⟨j.val + 1, hi⟩
  have hstd : A.nodeMap (Pi.single i 1) = Pi.single j 1 := A.node_std i j rfl
  calc A.a j = rootChar A.a (Pi.single j 1) := (k0_rootChar_single A.a j).symm
    _ = rootChar A.a (A.nodeMap (Pi.single i 1)) := by rw [hstd]
    _ = A.zeta ^ (A.row.s.getD i.val 0) := A.node_eval i
    _ = A.zeta ^ A.kacMu j := by
      simp [K0LangMark.kacMu, i]

omit [CharP Omega 2] in
private theorem k0_mark_pos {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (i : Fin A.row.diagram.marks.length) :
    0 < A.row.diagram.marks.getD i.val 0 := by
  obtain ⟨n, hn⟩ := i
  match n with
  | 0 => rw [N.mark_zero]; norm_num
  | k + 1 =>
      have hk : k < A.tau.rank := by
        have hlen := k0LangMark_marks_length A
        omega
      have h := N.facts.θ_pos ⟨k, hk⟩
      rw [N.θ_eq ⟨k, hk⟩] at h
      exact_mod_cast h

omit [CharP Omega 2] in
private theorem k0_s_zero_of_p_zero {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (hp : p = 0) :
    ∀ k : Fin A.row.diagram.marks.length, A.row.s.getD k.val 0 = 0 := by
  intro k
  have hsum := k0LangMark_weighted_sum A
  have hsum0 : (∑ i : Fin A.row.diagram.marks.length,
      A.row.diagram.marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by omega
  have hle := Finset.single_le_sum
    (f := fun k : Fin A.row.diagram.marks.length =>
      A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  rw [hsum0] at hle
  have hterm : A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0 = 0 :=
    Nat.eq_zero_of_le_zero hle
  rcases Nat.mul_eq_zero.1 hterm with h | h
  · have := k0_mark_pos N k; omega
  · exact h

omit [CharP Omega 2] in
private theorem k0_a_eq_one_of_nodes {A : K0LangMark Omega lab p R I phi}
    (h : ∀ j : Fin A.tau.rank,
      A.row.s.getD (j.val + 1) 0 = 0 ∨ A.row.s.getD (j.val + 1) 0 = p) :
    A.a = 1 := by
  funext j
  have hj := congrFun (k0_a_eq_zeta_kacMu A) j
  simp only [K0LangMark.kacMu, zpow_natCast] at hj
  rw [hj]
  rcases h j with h0 | hp
  · rw [h0]; simp
  · rw [hp]
    have hz : A.zeta ^ p = 1 := by
      have h := pow_orderOf_eq_one A.zeta
      rwa [A.zeta_order] at h
    exact hz

omit [CharP Omega 2] in
private theorem k0_zero_lt_aux {A : K0LangMark Omega lab p R I phi} (N : K0Normal A) : 0 < p := by
  by_contra h
  have hp : p = 0 := Nat.eq_zero_of_not_pos h
  have hzeros := k0_s_zero_of_p_zero N hp
  have ha1 : A.a = 1 := k0_a_eq_one_of_nodes (fun j => by
    left
    have hk : j.val + 1 < A.row.diagram.marks.length := by
      have hlen := k0LangMark_marks_length A
      omega
    exact hzeros ⟨j.val + 1, hk⟩)
  exact A.a_ne (by rw [ha1]; exact rootDiagUnit_one)

omit [CharP Omega 2] in
private theorem k0_s_le_p {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {i : ℕ} (hi : i < A.row.diagram.marks.length) :
    A.row.s.getD i 0 ≤ p := by
  have hp := k0_zero_lt_aux N
  have hsum := k0LangMark_weighted_sum A
  have hle := Finset.single_le_sum
    (f := fun k : Fin A.row.diagram.marks.length =>
      A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨i, hi⟩)
  rw [hsum] at hle
  have hmark := k0_mark_pos N ⟨i, hi⟩
  calc A.row.s.getD i 0 = 1 * A.row.s.getD i 0 := (one_mul _).symm
    _ ≤ A.row.diagram.marks.getD i 0 * A.row.s.getD i 0 := Nat.mul_le_mul_right _ hmark
    _ ≤ p := hle

omit [CharP Omega 2] in
private theorem k0_s_eq_p_others {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {i : ℕ} (hi : i < A.row.diagram.marks.length)
    (hsp : A.row.s.getD i 0 = p) :
    ∀ k : Fin A.row.diagram.marks.length, k.val ≠ i → A.row.s.getD k.val 0 = 0 := by
  have hp := k0_zero_lt_aux N
  let I : Fin A.row.diagram.marks.length := ⟨i, hi⟩
  have hsum : (∑ k : Fin A.row.diagram.marks.length,
      A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0) = p := k0LangMark_weighted_sum A
  have hle : A.row.diagram.marks.getD i 0 * A.row.s.getD i 0 ≤ p := by
    have h := Finset.single_le_sum
      (f := fun k : Fin A.row.diagram.marks.length =>
        A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
    rw [hsum] at h
    exact h
  have hm1 : A.row.diagram.marks.getD i 0 = 1 := by
    have hle' : A.row.diagram.marks.getD i 0 * p ≤ p := by
      rw [hsp] at hle
      exact hle
    have hmul : A.row.diagram.marks.getD i 0 * p ≤ 1 * p := by
      rwa [one_mul]
    have hle1 := Nat.le_of_mul_le_mul_right hmul hp
    have hmark : 0 < A.row.diagram.marks.getD i 0 := k0_mark_pos N I
    omega
  have hterm : A.row.diagram.marks.getD i 0 * A.row.s.getD i 0 = p := by
    rw [hm1, hsp, one_mul]
  have hzero : (∑ k ∈ Finset.univ.erase I,
      A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0) = 0 := by
    have h := Finset.add_sum_erase (Finset.univ : Finset (Fin A.row.diagram.marks.length))
      (fun k : Fin A.row.diagram.marks.length =>
        A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0)
      (Finset.mem_univ I)
    rw [hsum, hterm] at h
    omega
  have hk0 : ∀ k ∈ Finset.univ.erase I,
      A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le _)).1 hzero
  intro k hk
  have hne : k ≠ I := fun h => hk (by rw [h])
  have hfk : A.row.diagram.marks.getD k.val 0 * A.row.s.getD k.val 0 = 0 :=
    hk0 k (Finset.mem_erase.2 ⟨hne, Finset.mem_univ k⟩)
  rcases Nat.mul_eq_zero.1 hfk with h1 | h1
  · exact absurd h1 (ne_of_gt (k0_mark_pos N k))
  · exact h1

omit [CharP Omega 2] in
private theorem k0_theta_dot_kacMu {A : K0LangMark Omega lab p R I phi} (N : K0Normal A) :
    N.K.θ ⬝ᵥ A.kacMu = (p : ℤ) - (A.row.s.getD 0 0 : ℤ) := by
  have hsum : (∑ i : Fin A.row.diagram.marks.length,
      ((A.row.diagram.marks.getD i.val 0 : ℤ) * (A.row.s.getD i.val 0 : ℤ))) = (p : ℤ) := by
    have h := k0LangMark_weighted_sum A
    exact_mod_cast h
  have hrange : (∑ i ∈ Finset.range (A.tau.rank + 1),
      ((A.row.diagram.marks.getD i 0 : ℤ) * (A.row.s.getD i 0 : ℤ))) = (p : ℤ) := by
    rw [← N.length_eq, ← Fin.sum_univ_eq_sum_range]
    exact hsum
  rw [Finset.sum_range_succ'] at hrange
  have hf0 : (A.row.diagram.marks.getD 0 0 : ℤ) * (A.row.s.getD 0 0 : ℤ) =
      (A.row.s.getD 0 0 : ℤ) := by
    rw [N.mark_zero]; simp
  rw [hf0] at hrange
  have htail : (∑ k ∈ Finset.range A.tau.rank,
      ((A.row.diagram.marks.getD (k + 1) 0 : ℤ) * (A.row.s.getD (k + 1) 0 : ℤ))) =
      (p : ℤ) - (A.row.s.getD 0 0 : ℤ) := by
    rw [← hrange]
    ring
  have hdot : N.K.θ ⬝ᵥ A.kacMu =
      ∑ i : Fin A.tau.rank,
        ((A.row.diagram.marks.getD (i.val + 1) 0 : ℤ) * (A.row.s.getD (i.val + 1) 0 : ℤ)) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by
      rw [N.θ_eq i, K0LangMark.kacMu]
  have hrange2 : (∑ i : Fin A.tau.rank,
      ((A.row.diagram.marks.getD (i.val + 1) 0 : ℤ) * (A.row.s.getD (i.val + 1) 0 : ℤ))) =
      ∑ k ∈ Finset.range A.tau.rank,
        ((A.row.diagram.marks.getD (k + 1) 0 : ℤ) * (A.row.s.getD (k + 1) 0 : ℤ)) := by
    simpa using Fin.sum_univ_eq_sum_range
      (fun k => ((A.row.diagram.marks.getD (k + 1) 0 : ℤ) * (A.row.s.getD (k + 1) 0 : ℤ)))
      A.tau.rank
  rw [hdot, hrange2, htail]

private theorem k0_pi_eq_sum_single (n : ℕ) (v : Fin n → ℤ) :
    v = ∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℤ) := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [Ne.symm hbk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

omit [CharP Omega 2] in
private theorem k0_nodeMap_weighted_zero {A : K0LangMark Omega lab p R I phi} :
    (∑ i : Fin A.row.diagram.marks.length,
      (A.row.diagram.marks.getD i.val 0 : ℤ) • A.nodeMap (Pi.single i 1)) = 0 := by
  let mv : Fin A.row.diagram.marks.length → ℤ := fun i =>
    (A.row.diagram.marks.getD i.val 0 : ℤ)
  change (∑ i : Fin A.row.diagram.marks.length, mv i • A.nodeMap (Pi.single i 1)) = 0
  have hmem : mv ∈ A.nodeMap.ker := by
    rw [A.nodeMap_ker]
    exact Submodule.subset_span (Set.mem_singleton mv)
  have hdecomp : mv = ∑ i, mv i • (Pi.single i 1 : Fin A.row.diagram.marks.length → ℤ) :=
    k0_pi_eq_sum_single _ mv
  have hmap : A.nodeMap
      (∑ i, mv i • (Pi.single i 1 : Fin A.row.diagram.marks.length → ℤ)) =
      ∑ i, mv i • A.nodeMap (Pi.single i 1) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [← hmap, ← hdecomp]
  exact LinearMap.mem_ker.1 hmem

omit [CharP Omega 2] in
private theorem k0_nodeMap_zero {A : K0LangMark Omega lab p R I phi} (N : K0Normal A) :
    A.nodeMap (Pi.single (Fin.cast N.length_eq.symm (0 : Fin (A.tau.rank + 1))) 1) = -N.K.θ := by
  let mv : Fin A.row.diagram.marks.length → ℤ := fun i =>
    (A.row.diagram.marks.getD i.val 0 : ℤ)
  have hsum0 : (∑ i : Fin A.row.diagram.marks.length, mv i • A.nodeMap (Pi.single i 1)) = 0 := by
    simpa only [mv] using (k0_nodeMap_weighted_zero (A := A))
  let F : Fin A.row.diagram.marks.length → (Fin A.tau.rank → ℤ) :=
    fun i => mv i • A.nodeMap (Pi.single i 1)
  have hreindex : (∑ i : Fin A.row.diagram.marks.length, F i) =
      ∑ i : Fin (A.tau.rank + 1), F (Fin.cast N.length_eq.symm i) := by
    simpa [finCongr_apply] using
      (Equiv.sum_comp (finCongr N.length_eq.symm) F).symm
  have hsumF : (∑ i : Fin A.row.diagram.marks.length, F i) = 0 := hsum0
  rw [Fin.sum_univ_succ] at hreindex
  have hsplit : F (Fin.cast N.length_eq.symm 0) +
      ∑ i : Fin A.tau.rank, F (Fin.cast N.length_eq.symm i.succ) = 0 := by
    rw [← hreindex]
    exact hsumF
  have hfirst : F (Fin.cast N.length_eq.symm 0) =
      A.nodeMap (Pi.single (Fin.cast N.length_eq.symm (0 : Fin (A.tau.rank + 1))) 1) := by
    simp only [F, mv]
    have h0 : (Fin.cast N.length_eq.symm (0 : Fin (A.tau.rank + 1))).val = 0 := rfl
    rw [h0, N.mark_zero]
    simp
  have htail : (∑ i : Fin A.tau.rank, F (Fin.cast N.length_eq.symm i.succ)) = N.K.θ := by
    have hterm : ∀ i : Fin A.tau.rank,
        F (Fin.cast N.length_eq.symm i.succ) = N.K.θ i • (Pi.single i 1 : Fin A.tau.rank → ℤ) := by
      intro i
      have hstd : A.nodeMap (Pi.single (Fin.cast N.length_eq.symm i.succ) 1) = Pi.single i 1 :=
        A.node_std _ i rfl
      have hθ : (A.row.diagram.marks.getD (Fin.cast N.length_eq.symm i.succ).val 0 : ℤ) =
          N.K.θ i := by
        rw [N.θ_eq i]; rfl
      simp only [F, mv, hstd, hθ]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact (k0_pi_eq_sum_single _ N.K.θ).symm
  have hmain : A.nodeMap (Pi.single (Fin.cast N.length_eq.symm (0 : Fin (A.tau.rank + 1))) 1) +
      N.K.θ = 0 := by
    rw [← hfirst, ← htail]
    exact hsplit
  exact eq_neg_of_add_eq_zero_left hmain

omit [CharP Omega 2] in
theorem K0LangMark.rootChar_eq_one_iff (A : K0LangMark Omega lab p R I phi) :
    ∀ γ, IsRoot A.tau γ →
      ((rootCharHom A.a) (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ A.kacMu) := by

  intro γ _hγ
  have hz : rootChar A.a γ = A.zeta ^ (γ ⬝ᵥ A.kacMu) := by
    rw [k0_a_eq_zeta_kacMu A]
    exact KacData.rootChar_eq_zpow A.zeta A.kacMu γ
  change rootChar A.a γ = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ A.kacMu
  rw [hz]
  have hcast : ((orderOf A.zeta : ℕ) : ℤ) = (p : ℤ) := by rw [A.zeta_order]
  constructor
  · intro h1
    have h2 : ((orderOf A.zeta : ℕ) : ℤ) ∣ γ ⬝ᵥ A.kacMu :=
      orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hcast] at h2
  · intro h1
    have h2 : ((orderOf A.zeta : ℕ) : ℤ) ∣ γ ⬝ᵥ A.kacMu := by rwa [hcast]
    exact orderOf_dvd_iff_zpow_eq_one.1 h2

namespace K0Normal

variable {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)

omit [CharP Omega 2] in
include N in
theorem zero_lt : 0 < p := by
  exact k0_zero_lt_aux N

omit [CharP Omega 2] in
include N in
theorem s_lt (i : ℕ) : A.row.s.getD i 0 < p := by

  by_cases hi : i < A.row.diagram.marks.length
  · have hle := k0_s_le_p N hi
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hzeros := k0_s_eq_p_others N hi h
      have hcase : ∀ j : Fin A.tau.rank,
          A.row.s.getD (j.val+1) 0 = 0 ∨ A.row.s.getD (j.val+1) 0 = p := by
        intro j
        have hk : j.val + 1 < A.row.diagram.marks.length := by
          have hlen := k0LangMark_marks_length A
          omega
        let K : Fin A.row.diagram.marks.length := ⟨j.val + 1, hk⟩
        by_cases hKI : K = ⟨i, hi⟩
        · right
          have hval : K.val = i := by rw [hKI]
          change A.row.s.getD K.val 0 = p
          rw [hval]
          exact h
        · left
          exact hzeros K (fun hval => hKI (Fin.ext hval))
      have ha1 := k0_a_eq_one_of_nodes hcase
      exact A.a_ne (by rw [ha1]; exact rootDiagUnit_one)
  · have h0 : A.row.s.getD i 0 = 0 := by
      have hs : A.row.s.length ≤ i := by
        rw [A.row.s_length]
        exact Nat.le_of_not_lt hi
      exact List.getD_eq_default A.row.s 0 hs
    rw [h0]
    exact k0_zero_lt_aux N

omit [CharP Omega 2] in
theorem isNormal : N.K.IsNormal p A.kacMu := by

  refine ⟨fun i => ?_, ?_⟩
  · simp [K0LangMark.kacMu]
  · rw [k0_theta_dot_kacMu N]
    have h := Int.natCast_nonneg (A.row.s.getD 0 0)
    linarith

omit [CharP Omega 2] in
theorem isZ_iff {i : ℕ} (hi : i < A.tau.rank + 1) :
    N.K.IsZ p A.kacMu (idxNode i) ↔ A.row.s.getD i 0 = 0 := by

  match i with
  | 0 =>
      have hidx : idxNode (r := A.tau.rank) 0 = none := by
        have := idxNode_nodeIdx (r := A.tau.rank) (none : Option (Fin A.tau.rank))
        simpa [nodeIdx] using this
      rw [hidx]
      show N.K.θ ⬝ᵥ A.kacMu = (p : ℤ) ↔ A.row.s.getD 0 0 = 0
      rw [k0_theta_dot_kacMu N]
      constructor
      · intro h
        have h' : (A.row.s.getD 0 0 : ℤ) = 0 := by linarith
        exact_mod_cast h'
      · intro h
        rw [h]
        norm_num
  | k + 1 =>
      have hk : k < A.tau.rank := by omega
      have hidx : idxNode (r := A.tau.rank) (k + 1) = some ⟨k, hk⟩ := by
        have := idxNode_nodeIdx (r := A.tau.rank) (some ⟨k, hk⟩)
        simpa [nodeIdx] using this
      rw [hidx]
      show A.kacMu ⟨k, hk⟩ = 0 ↔ A.row.s.getD (k + 1) 0 = 0
      rw [K0LangMark.kacMu]
      constructor
      · intro h; exact_mod_cast h
      · intro h; exact_mod_cast h

omit [CharP Omega 2] in
theorem nodeMap_eq (i : Fin A.row.diagram.marks.length) :
    A.nodeMap (Pi.single i 1) = N.K.extRoot (idxNode i.val) := by

  obtain ⟨n, hn⟩ := i
  match n with
  | 0 =>
      have hidx : idxNode (r := A.tau.rank) 0 = none := by
        have := idxNode_nodeIdx (r := A.tau.rank) (none : Option (Fin A.tau.rank))
        simpa [nodeIdx] using this
      have hzero : (⟨0, hn⟩ : Fin A.row.diagram.marks.length) =
          Fin.cast N.length_eq.symm (0 : Fin (A.tau.rank + 1)) := Fin.ext rfl
      rw [hidx, hzero]
      exact k0_nodeMap_zero N
  | k + 1 =>
      have hk : k < A.tau.rank := by
        have hlen := k0LangMark_marks_length A
        omega
      have hidx : idxNode (r := A.tau.rank) (k + 1) = some ⟨k, hk⟩ := by
        have := idxNode_nodeIdx (r := A.tau.rank) (some ⟨k, hk⟩)
        simpa [nodeIdx] using this
      rw [hidx]
      exact A.node_std ⟨k + 1, hn⟩ ⟨k, hk⟩ rfl

end K0Normal

end CFSG.StandardType.GGK0MarkedKacIface1587

end
