module

public import CFSG.LocalAnalysis.StandardType.GGK0LQShape
public import CFSG.LocalAnalysis.StandardType.GGK0LQNodes
public import CFSG.LocalAnalysis.StandardType.GGK0NormalFrob
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.LocalAnalysis.StandardType.GGK0LQLongest
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private theorem lqKindE_orbit_image {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (Ψ : Set (Fin τ.rank → ℤ)) :
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ]) '' Ψ = Ψ := by
  by_cases h : ({s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}).Nonempty
  · exact (Nat.sInf_mem h).2
  · have h0 : componentOrbitLength S.ρ Ψ = 0 := by
      unfold componentOrbitLength
      rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty]
    rw [h0]
    simp

private theorem lqKindE_frob_nodes_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
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

private theorem lqKindE_rho_iterate_frobLinear (A : K0LangMark Omega lab p R I phi) (n : ℕ)
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

private theorem lqKindE_twistInner_congr {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (h : ∀ γ ∈ Ψ, σ γ = σ' γ) :
    twistInner Ψ σ ↔ twistInner Ψ σ' := by
  unfold twistInner
  constructor
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).symm.trans (hσ γ hγ)⟩
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).trans (hσ γ hγ)⟩

private theorem lqKindE_k0pMul_getD (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
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

private theorem lqKindE_k0pPow_go (a : List ℕ) (f : ℕ) (acc : List ℕ) :
    k0pPow.go a f acc = acc.map ((fun j => a.getD j 0)^[f]) := by
  induction f generalizing acc with
  | zero => simp only [k0pPow.go, Function.iterate_zero, List.map_id]
  | succ f ih =>
      rw [show k0pPow.go a (f+1) acc = k0pPow.go a f (k0pMul a acc) from rfl, ih]
      unfold k0pMul
      rw [List.map_map]
      congr 1

private theorem lqKindE_k0pPow_getD (a : List ℕ) (n : ℕ) {i : ℕ} (hi : i < a.length) :
    (k0pPow a n).getD i 0 = (fun j => a.getD j 0)^[n] i := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lqKindE_k0pPow_go,
    k0pId, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

private theorem lqKindE_rho_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (fun j => A.row.rho.getD j 0)^[n] i.val = (A.row.nodePerm^[n] i).val := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, A.row.rho_apply, Function.iterate_succ_apply']

private theorem lqKindE_k0pPow_getD_nodePerm (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (k0pPow A.row.rho n).getD i.val 0 = (A.row.nodePerm^[n] i).val := by
  rw [lqKindE_k0pPow_getD A.row.rho n (by rw [A.row.rho_length]; exact i.isLt)]
  exact lqKindE_rho_iterate A n i

private theorem lqKindE_bridge_arith {d s o : ℕ} {e : ℤ}
    (hd : d = 1 ∨ d = 2) (he : e = if d = 1 then 1 else -1) (ho : o = 1 ∨ o = 2) :
    (if d = 2 ∧ s % 2 = 1 then (if o = 1 then 2 else if o = 2 then 1 else o) else o) = 1 ↔
      (o = 1 ∧ e ^ s = 1) ∨ (o = 2 ∧ e ^ s = -1) := by
  rcases hd with rfl | rfl
  · have he1 : e = 1 := by rw [he]; rfl
    rcases ho with rfl | rfl <;> simp [he1, one_pow]
  · have he1 : e = -1 := by rw [he]; rfl
    rcases ho with rfl | rfl
    · rcases Nat.even_or_odd s with hev | hod
      · have hmod : s % 2 = 0 := Nat.even_iff.mp hev
        have hpow : (-1 : ℤ) ^ s = 1 := hev.neg_one_pow
        simp [he1, hmod, hpow]
      · have hmod : s % 2 = 1 := Nat.odd_iff.mp hod
        have hpow : (-1 : ℤ) ^ s = -1 := hod.neg_one_pow
        simp [he1, hmod, hpow]
    · rcases Nat.even_or_odd s with hev | hod
      · have hmod : s % 2 = 0 := Nat.even_iff.mp hev
        have hpow : (-1 : ℤ) ^ s = 1 := hev.neg_one_pow
        simp [he1, hmod, hpow]
      · have hmod : s % 2 = 1 := Nat.odd_iff.mp hod
        have hpow : (-1 : ℤ) ^ s = -1 := hod.neg_one_pow
        simp [he1, hmod, hpow]

private def lqKindE_C (i j : Fin 6) : ℤ := Tag.cartanE 6 i j

private def lqKindE_cvec (i : Fin 6) : ℤ := ([4, 3, 5, 6, 4, 2] : List ℤ).getD i.val 0

private def lqKindE_flip : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 2 4

private def lqKindE_lab : GGKacType → List ℕ → List ℕ
  | .E6, [0, 1, 2, 3, 4, 5] => [0, 5, 2, 4, 3, 1]
  | .E6, [0, 2, 3, 4, 5, 6] => [0, 3, 2, 4, 5, 6]
  | _, _ => [1, 2, 3, 4, 5, 6]

private theorem lqKindE_lab_table (T : GGKacType) (hT : T = .E6 ∨ T = .E7 ∨ T = .E8) :
    ∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      zero.length < (k0DiagOf T).marks.length →
      ∀ c ∈ k0Comps (k0DiagOf T) zero,
        (k0CompType (k0DiagOf T) c).1 = .E6 →
        (lqKindE_lab T c).Nodup ∧
        (lqKindE_lab T c).toFinset = c.toFinset ∧
        (∀ i : Fin 6, (lqKindE_lab T c).getD i.val 0 < (k0DiagOf T).marks.length) ∧
        (∀ i j : Fin 6,
          iform (lqExtRoot (absTag T) T ((lqKindE_lab T c).getD i.val 0))
                (lqExtRoot (absTag T) T ((lqKindE_lab T c).getD j.val 0))
            = lqKindE_C i j) := by
  rcases hT with rfl | rfl | rfl <;> decide +kernel

private theorem lqKindE_perm_cases (q : Equiv.Perm (Fin 6))
    (hpres : ∀ i j : Fin 6, lqKindE_C (q i) (q j) = lqKindE_C i j) :
    q = 1 ∨ q = lqKindE_flip := by
  revert q
  decide +kernel

private theorem lqKindE_C_pair (j : Fin 6) :
    (∑ i : Fin 6, lqKindE_cvec i * lqKindE_C i j) = if j = 0 then 3 else 0 := by
  revert j
  decide +kernel

private theorem lqKindE_pair_mu_alpha {τ : Tag} {α : Fin 6 → (Fin τ.rank → ℤ)}
    (hC : ∀ i j : Fin 6, iform (α i) (α j) = lqKindE_C i j) (j : Fin 6) :
    iform (∑ i : Fin 6, lqKindE_cvec i • α i) (α j) =
      3 * (if j = 0 then (1:ℤ) else 0) := by
  rw [iform_finset_sum_left]
  have h : ∀ i : Fin 6, iform (lqKindE_cvec i • α i) (α j) = lqKindE_cvec i * lqKindE_C i j := by
    intro i
    rw [iform_smul_left, hC]
  rw [Finset.sum_congr rfl (fun i _ => h i), lqKindE_C_pair]
  split_ifs <;> ring

private theorem lqKindE_pair_mu_mu {τ : Tag} {α : Fin 6 → (Fin τ.rank → ℤ)}
    (hC : ∀ i j : Fin 6, iform (α i) (α j) = lqKindE_C i j) :
    iform (∑ i : Fin 6, lqKindE_cvec i • α i) (∑ i : Fin 6, lqKindE_cvec i • α i) = 12 := by
  rw [iform_finset_sum_right]
  have h : ∀ j : Fin 6, iform (∑ i : Fin 6, lqKindE_cvec i • α i) (lqKindE_cvec j • α j) =
      lqKindE_cvec j * (3 * (if j = 0 then (1:ℤ) else 0)) := by
    intro j
    rw [iform_smul_right, lqKindE_pair_mu_alpha hC]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  rw [show (∑ j : Fin 6, lqKindE_cvec j * (3 * (if j = 0 then (1:ℤ) else 0))) = 12 by
    decide +kernel]

private theorem lqKindE_li_z {τ : Tag} {ι : Type} [Fintype ι]
    {f : ι → (Fin τ.rank → ℤ)}
    (h : LinearIndependent ℚ (fun i j => ((f i j : ℤ) : ℚ))) : LinearIndependent ℤ f := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hcast : ∑ i, ((g i : ℤ) : ℚ) • (fun j => ((f i j : ℤ) : ℚ)) = 0 := by
    funext j
    have hj := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    have : ((∑ i, g i * f i j : ℤ) : ℚ) = 0 := by exact_mod_cast hj
    simpa [Finset.sum_apply, mul_comm] using this
  intro i
  have := h (fun i => ((g i : ℤ) : ℚ)) hcast i
  exact_mod_cast this

private theorem lqKindE_iform_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) x)
      (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) y) = iform x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]

private theorem lqKindE_k0pPow_length (a : List ℕ) (n : ℕ) :
    (k0pPow a n).length = a.length := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lqKindE_k0pPow_go]
  simp [k0pId]

private theorem lqKindE_symmetrizer_one {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (k : Fin τ.rank) : τ.symmetrizer k k = 1 := by
  rcases hτ with rfl | rfl | rfl <;> fin_cases k <;> decide

private theorem lqKindE_mark_pos (T : GGKacType) (i : Fin (k0DiagOf T).marks.length) :
    0 < (k0DiagOf T).marks.getD i.val 0 := by
  cases T <;> fin_cases i <;> decide

private theorem lqKindE_marks_length (A : K0LangMark Omega lab p R I phi) :
    (k0DiagOf A.row.T).marks.length = A.tau.rank + 1 := by
  rw [← A.tau_eq]
  cases A.row.T <;> rfl

private theorem lqKindE_weighted_sum (A : K0LangMark Omega lab p R I phi) :
    (∑ i : Fin (k0DiagOf A.row.T).marks.length,
      (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = p :=
  ggKacShVecs_sum _ _ _ A.row.s_mem

private theorem lqKindE_a_eq_zeta_kacMu (A : K0LangMark Omega lab p R I phi) :
    A.a = fun j => A.zeta ^ A.kacMu j := by
  funext j
  have hi : j.val + 1 < A.row.diagram.marks.length := by
    show j.val + 1 < (k0DiagOf A.row.T).marks.length
    rw [lqKindE_marks_length A]
    omega
  let i : Fin A.row.diagram.marks.length := ⟨j.val + 1, hi⟩
  have hstd : A.nodeMap (Pi.single i 1) = Pi.single j 1 := A.node_std i j rfl
  calc A.a j = rootChar A.a (Pi.single j 1) := (rootChar_single A.a j).symm
    _ = rootChar A.a (A.nodeMap (Pi.single i 1)) := by rw [hstd]
    _ = A.zeta ^ (A.row.s.getD i.val 0) := A.node_eval i
    _ = A.zeta ^ A.kacMu j := by
      simp [K0LangMark.kacMu, i]

private theorem lqKindE_a_eq_one_of_nodes (A : K0LangMark Omega lab p R I phi)
    (h : ∀ j : Fin A.tau.rank,
      A.row.s.getD (j.val + 1) 0 = 0 ∨ A.row.s.getD (j.val + 1) 0 = p) :
    A.a = 1 := by
  funext j
  have hj := congrFun (lqKindE_a_eq_zeta_kacMu A) j
  simp only [K0LangMark.kacMu, zpow_natCast] at hj
  rw [hj]
  rcases h j with h0 | hp
  · rw [h0]; simp
  · rw [hp]
    have hz : A.zeta ^ p = 1 := by
      have h := pow_orderOf_eq_one A.zeta
      rwa [A.zeta_order] at h
    exact hz

private theorem lqKindE_s_zero_of_p_zero (A : K0LangMark Omega lab p R I phi) (hp : p = 0) :
    ∀ k : Fin (k0DiagOf A.row.T).marks.length, A.row.s.getD k.val 0 = 0 := by
  intro k
  have hsum := lqKindE_weighted_sum A
  have hsum0 : (∑ i : Fin (k0DiagOf A.row.T).marks.length,
      (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by omega
  have hle := Finset.single_le_sum
    (f := fun k : Fin (k0DiagOf A.row.T).marks.length =>
      (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  rw [hsum0] at hle
  have hterm : (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0 = 0 :=
    Nat.eq_zero_of_le_zero hle
  rcases Nat.mul_eq_zero.1 hterm with h | h
  · have := lqKindE_mark_pos A.row.T k; omega
  · exact h

private theorem lqKindE_zero_lt (A : K0LangMark Omega lab p R I phi) : 0 < p := by
  by_contra h
  have hp : p = 0 := Nat.eq_zero_of_not_pos h
  have hzeros := lqKindE_s_zero_of_p_zero A hp
  have ha1 : A.a = 1 := lqKindE_a_eq_one_of_nodes A (fun j => by
    left
    have hk : j.val + 1 < A.row.diagram.marks.length := by
      show j.val + 1 < (k0DiagOf A.row.T).marks.length
      rw [lqKindE_marks_length A]
      omega
    exact hzeros ⟨j.val + 1, hk⟩)
  exact A.a_ne (by rw [ha1]; exact rootDiagUnit_one)

private theorem lqKindE_s_le_p (A : K0LangMark Omega lab p R I phi)
    {i : ℕ} (hi : i < A.row.diagram.marks.length) :
    A.row.s.getD i 0 ≤ p := by
  have hp := lqKindE_zero_lt A
  have hsum := lqKindE_weighted_sum A
  have hle := Finset.single_le_sum
    (f := fun k : Fin (k0DiagOf A.row.T).marks.length =>
      (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨i, hi⟩)
  rw [hsum] at hle
  have hmark := lqKindE_mark_pos A.row.T ⟨i, hi⟩
  calc A.row.s.getD i 0 = 1 * A.row.s.getD i 0 := (one_mul _).symm
    _ ≤ (k0DiagOf A.row.T).marks.getD i 0 * A.row.s.getD i 0 := Nat.mul_le_mul_right _ hmark
    _ ≤ p := hle

private theorem lqKindE_s_eq_p_others (A : K0LangMark Omega lab p R I phi)
    {i : ℕ} (hi : i < A.row.diagram.marks.length)
    (hsp : A.row.s.getD i 0 = p) :
    ∀ k : Fin (k0DiagOf A.row.T).marks.length, k.val ≠ i → A.row.s.getD k.val 0 = 0 := by
  have hp := lqKindE_zero_lt A
  let I : Fin (k0DiagOf A.row.T).marks.length := ⟨i, hi⟩
  have hsum : (∑ k : Fin (k0DiagOf A.row.T).marks.length,
      (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0) = p :=
    lqKindE_weighted_sum A
  have hle : (k0DiagOf A.row.T).marks.getD i 0 * A.row.s.getD i 0 ≤ p := by
    have h := Finset.single_le_sum
      (f := fun k : Fin (k0DiagOf A.row.T).marks.length =>
        (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
    rw [hsum] at h
    exact h
  have hm1 : (k0DiagOf A.row.T).marks.getD i 0 = 1 := by
    have hle' : (k0DiagOf A.row.T).marks.getD i 0 * p ≤ p := by
      rw [hsp] at hle
      exact hle
    have hmul : (k0DiagOf A.row.T).marks.getD i 0 * p ≤ 1 * p := by
      rwa [one_mul]
    have hle1 := Nat.le_of_mul_le_mul_right hmul hp
    have hmark : 0 < (k0DiagOf A.row.T).marks.getD i 0 := lqKindE_mark_pos A.row.T I
    omega
  have hterm : (k0DiagOf A.row.T).marks.getD i 0 * A.row.s.getD i 0 = p := by
    rw [hm1, hsp, one_mul]
  have hzero : (∑ k ∈ Finset.univ.erase I,
      (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0) = 0 := by
    have h := Finset.add_sum_erase (Finset.univ : Finset (Fin (k0DiagOf A.row.T).marks.length))
      (fun k : Fin (k0DiagOf A.row.T).marks.length =>
        (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0)
      (Finset.mem_univ I)
    rw [hsum, hterm] at h
    omega
  have hk0 : ∀ k ∈ Finset.univ.erase I,
      (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le _)).1 hzero
  intro k hk
  have hne : k ≠ I := fun h => hk (by rw [h])
  have hfk : (k0DiagOf A.row.T).marks.getD k.val 0 * A.row.s.getD k.val 0 = 0 :=
    hk0 k (Finset.mem_erase.2 ⟨hne, Finset.mem_univ k⟩)
  rcases Nat.mul_eq_zero.1 hfk with h1 | h1
  · exact absurd h1 (ne_of_gt (lqKindE_mark_pos A.row.T k))
  · exact h1

private theorem lqKindE_s_lt (A : K0LangMark Omega lab p R I phi) (i : ℕ) :
    A.row.s.getD i 0 < p := by
  by_cases hi : i < A.row.diagram.marks.length
  · have hle := lqKindE_s_le_p A hi
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hzeros := lqKindE_s_eq_p_others A hi h
      have hcase : ∀ j : Fin A.tau.rank,
          A.row.s.getD (j.val + 1) 0 = 0 ∨ A.row.s.getD (j.val + 1) 0 = p := by
        intro j
        have hk : j.val + 1 < A.row.diagram.marks.length := by
          show j.val + 1 < (k0DiagOf A.row.T).marks.length
          rw [lqKindE_marks_length A]
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
      have ha1 := lqKindE_a_eq_one_of_nodes A hcase
      exact A.a_ne (by rw [ha1]; exact rootDiagUnit_one)
  · have h0 : A.row.s.getD i 0 = 0 := by
      have hs : A.row.s.length ≤ i := by
        rw [A.row.s_length]
        exact Nat.le_of_not_lt hi
      exact List.getD_eq_default A.row.s 0 hs
    rw [h0]
    exact lqKindE_zero_lt A

private theorem lqKindE_rootChar_zsmul_aux {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (k : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (k • v) = rootChar a v ^ k := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

private theorem lqKindE_p_odd (A : K0LangMark Omega lab p R I phi) (hp : 0 < p) : Odd p := by
  rcases Nat.even_or_odd p with heven | hodd
  · exfalso
    obtain ⟨m, hm⟩ := heven
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hm] at hp; simp at hp
      · exact h
    let u : Omegaˣ := A.zeta ^ m
    have hu2 : u ^ 2 = 1 := by
      dsimp [u]
      rw [← pow_mul, show m * 2 = p by omega]
      have h : A.zeta ^ orderOf A.zeta = 1 := pow_orderOf_eq_one A.zeta
      rwa [A.zeta_order] at h
    have hu1 : u = 1 := by
      apply Units.ext
      have hu2' : ((u : Omega)) ^ 2 = 1 := by
        have := congrArg (fun x : Omegaˣ => (x : Omega)) hu2
        simpa [Units.val_pow_eq_pow_val] using this
      have hsq : ((u : Omega) - 1) ^ 2 = 0 := by
        have h := sub_pow_char (u : Omega) (1 : Omega) (p := 2)
        rw [h, hu2']
        norm_num
      have h : (u : Omega) - 1 = 0 := sq_eq_zero_iff.mp hsq
      exact sub_eq_zero.mp h
    have hdvd : p ∣ m := by
      dsimp [u] at hu1
      rw [← A.zeta_order, orderOf_dvd_iff_pow_eq_one]
      exact hu1
    have : p ≤ m := Nat.le_of_dvd hm_pos hdvd
    omega
  · exact hodd

private theorem lqKindE_hcop (A : K0LangMark Omega lab p R I phi) (hp : 0 < p) :
    Nat.Coprime p A.setup.D.q := by
  rw [A.q_eq]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (lqKindE_p_odd A hp))

private theorem lqKindE_s_nodePerm_eq_zero_iff (A : K0LangMark Omega lab p R I phi)
    (i : Fin A.row.diagram.marks.length) :
    A.row.s.getD (A.row.nodePerm i).val 0 = 0 ↔ A.row.s.getD i.val 0 = 0 := by
  let s_i : ℕ := A.row.s.getD i.val 0
  let s_pi : ℕ := A.row.s.getD (A.row.nodePerm i).val 0
  let q : ℕ := A.setup.D.q
  let ε : ℤ := A.epsilon
  change s_pi = 0 ↔ s_i = 0
  let γ_i : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single i 1)
  let γ_pi : Fin A.tau.rank → ℤ := A.nodeMap (Pi.single (A.row.nodePerm i) 1)
  have hγ_i : IsRoot A.tau γ_i := A.node_isRoot i
  have hρ : A.setup.ρ γ_i = A.epsilon • γ_pi := by
    rw [← A.frob_roots γ_i hγ_i]
    exact A.frob_nodes i
  have hchar := A.setup.frob.rootChar_eq A.a A.a_torus γ_i hγ_i
  rw [hρ, lqKindE_rootChar_zsmul_aux] at hchar
  rw [A.node_eval i, A.node_eval (A.row.nodePerm i)] at hchar
  have hchar_int : A.zeta ^ ((s_pi : ℤ) * ε) = A.zeta ^ ((s_i : ℤ) * q) := by
    dsimp only [s_i, s_pi, q, ε]
    simpa [zpow_natCast, zpow_mul] using hchar
  have hdvd : (p : ℤ) ∣ (s_i : ℤ) * q - (s_pi : ℤ) * ε := by
    have hz : A.zeta ^ ((s_i : ℤ) * q - (s_pi : ℤ) * ε) = 1 := by
      rw [zpow_sub, hchar_int, mul_inv_cancel]
    have hdvd_order : (orderOf A.zeta : ℤ) ∣ (s_i : ℤ) * q - (s_pi : ℤ) * ε :=
      (orderOf_dvd_iff_zpow_eq_one).mpr hz
    have h_eq : (orderOf A.zeta : ℤ) = (p : ℤ) := by exact_mod_cast A.zeta_order
    rwa [h_eq] at hdvd_order
  have hcop : Nat.Coprime p q := by
    dsimp only [q]
    exact lqKindE_hcop A (lqKindE_zero_lt A)
  have hs_i_lt : (s_i : ℤ) < p := by
    dsimp only [s_i]
    exact_mod_cast lqKindE_s_lt A i.val
  have hs_pi_lt : (s_pi : ℤ) < p := by
    dsimp only [s_pi]
    exact_mod_cast lqKindE_s_lt A (A.row.nodePerm i).val
  constructor
  · intro h
    have h' : (s_pi : ℤ) = 0 := by exact_mod_cast h
    have hdvd' : (p : ℤ) ∣ (s_i : ℤ) * q := by
      simpa only [h', zero_mul, sub_zero] using hdvd
    have hdvd'' : p ∣ s_i * q := by
      rw [← Int.natCast_dvd_natCast]
      exact hdvd'
    have h' : p ∣ q * s_i := by
      rwa [Nat.mul_comm]
    have hdvd''' : p ∣ s_i := hcop.dvd_of_dvd_mul_left h'
    have hzero : (s_i : ℤ) = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.natCast_dvd_natCast.mpr hdvd''')
        (by simpa using hs_i_lt)
    exact Nat.cast_eq_zero.mp hzero
  · intro h
    have h' : (s_i : ℤ) = 0 := by exact_mod_cast h
    have hdvd' : (p : ℤ) ∣ - ((s_pi : ℤ) * ε) := by
      simpa only [h', zero_mul, zero_sub] using hdvd
    have hdvd'' : (p : ℤ) ∣ (s_pi : ℤ) * ε := dvd_neg.mp hdvd'
    have hε : ε = 1 ∨ ε = -1 := by
      dsimp only [ε]
      rw [A.epsilon_eq]
      split_ifs <;> simp
    rcases hε with h1 | h1
    · have hdvd''' : (p : ℤ) ∣ (s_pi : ℤ) := by simpa [h1] using hdvd''
      have hdvd4 : p ∣ s_pi := by rw [← Int.natCast_dvd_natCast]; exact hdvd'''
      have hzero : (s_pi : ℤ) = 0 :=
        Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.natCast_dvd_natCast.mpr hdvd4)
          (by simpa using hs_pi_lt)
      exact Nat.cast_eq_zero.mp hzero
    · have hdvd''' : (p : ℤ) ∣ (s_pi : ℤ) := by
        have h2 : (p : ℤ) ∣ - (s_pi : ℤ) := by simpa [h1] using hdvd''
        exact dvd_neg.mp h2
      have hdvd4 : p ∣ s_pi := by rw [← Int.natCast_dvd_natCast]; exact hdvd'''
      have hzero : (s_pi : ℤ) = 0 :=
        Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.natCast_dvd_natCast.mpr hdvd4)
          (by simpa using hs_pi_lt)
      exact Nat.cast_eq_zero.mp hzero

private theorem lqKindE_compRank (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (h6 : (lqNodes A P j).length = 6) :
    compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 6 := by
  classical
  set c := lqNodes A P j with hc
  set Ψ := componentRoots (rootCharHom A.a) (P.repr j) with hΨ
  have hb := lq_nodes_basic A P j
  have hnd : c.Nodup := hb.2.1
  have hcb : ∀ x ∈ c, x < (k0DiagOf A.row.T).marks.length := by
    intro x hx
    have h := (hb.2.2 x hx).1
    rw [lqKindE_marks_length A]; exact h
  have hmarks_ge : 7 ≤ (k0DiagOf A.row.T).marks.length := by
    have hle : c.length ≤ (k0DiagOf A.row.T).marks.length := by
      have hsub : c.toFinset ⊆ Finset.range (k0DiagOf A.row.T).marks.length := by
        intro x hx
        rw [Finset.mem_range]
        exact hcb x (List.mem_toFinset.mp hx)
      have := Finset.card_le_card hsub
      rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
    have hlen5 : (k0DiagOf A.row.T).marks.length = 5 ∨
        7 ≤ (k0DiagOf A.row.T).marks.length := by
      cases A.row.T <;> simp [k0DiagOf, k0E6Diag, k0E7Diag, k0E8Diag, k0F4Diag]
    rcases hlen5 with h | h
    · omega
    · exact h
  have hproper : ∃ i, i < (k0DiagOf A.row.T).marks.length ∧ i ∉ c := by
    by_contra h
    push Not at h
    have hcard := Finset.card_le_card
      (show Finset.range (k0DiagOf A.row.T).marks.length ⊆ c.toFinset from
        fun i hi => List.mem_toFinset.mpr (h i (Finset.mem_range.mp hi)))
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd, h6] at hcard
    omega
  let g : {x // x ∈ c} → (Fin A.tau.rank → ℚ) :=
    fun x i => ((lqExtRoot A.tau A.row.T x.1 i : ℤ) : ℚ)
  have hLI : LinearIndependent ℚ g :=
    lq_extRoot_independent A.tau A.row.T A.tau_eq c hnd hcb hproper
  let S : Set (Fin A.tau.rank → ℤ) := {w | ∃ i : Fin A.row.diagram.marks.length,
    i.val ∈ c ∧ w = A.nodeMap (Pi.single i 1)}
  have hS : (fun γ (i : Fin A.tau.rank) => (γ i : ℚ)) '' S = Set.range g := by
    ext v
    constructor
    · rintro ⟨w, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨⟨i.val, hi⟩, ?_⟩
      funext k
      simp only [g]
      rw [lq_nodeMap_eq A i]
    · rintro ⟨x, rfl⟩
      refine ⟨A.nodeMap (Pi.single ⟨x.1, hcb x.1 x.2⟩ 1),
        ⟨⟨x.1, hcb x.1 x.2⟩, x.2, rfl⟩, ?_⟩
      funext k
      simp only [g]
      rw [lq_nodeMap_eq A ⟨x.1, hcb x.1 x.2⟩]
  have hspan : Submodule.span ℚ (Set.range g) =
      Submodule.span ℚ ((fun γ (i : Fin A.tau.rank) => (γ i : ℚ)) '' Ψ) := by
    rw [← hS]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro v ⟨w, ⟨i, hi, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨A.nodeMap (Pi.single i 1), ?_, rfl⟩
      rw [hΨ, P.repr_roots j]
      exact ⟨A.node_isRoot i, Submodule.subset_span ⟨i, hi, rfl⟩⟩
    · rw [Submodule.span_le]
      rintro v ⟨γ, hγ, rfl⟩
      have hγS : γ ∈ Submodule.span ℤ S := by
        rw [hΨ, P.repr_roots j] at hγ
        exact hγ.2
      let castZ : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℚ) :=
        { toFun := fun v i => (v i : ℚ)
          map_add' := by intro a b; funext i; simp
          map_smul' := by intro n a; funext i; simp }
      have hmap : Submodule.map castZ (Submodule.span ℤ S) ≤
          (Submodule.span ℚ ((fun γ (i : Fin A.tau.rank) => (γ i : ℚ)) '' S)).restrictScalars ℤ := by
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        intro z hz
        exact Submodule.subset_span ⟨z, hz, rfl⟩
      exact hmap (Submodule.mem_map.mpr ⟨γ, hγS, rfl⟩)
  rw [compRank, ← hspan, finrank_span_eq_card hLI]
  have hcard : Fintype.card {x // x ∈ c} = 6 := by
    have := Fintype.card_congr (List.Nodup.getEquiv c hnd)
    rw [Fintype.card_fin] at this
    omega
  exact hcard

private theorem lqKindE_autOrder_eq_one (c rk : List ℕ) (h6 : c.length = 6)
    (hfix : ∀ i ∈ c, rk.getD i 0 = i) : k0AutOrder c rk = 1 := by
  have hall : c.all (fun i => decide (rk.getD i 0 = i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [hfix i hi]
    simp
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl, h6]
  simp only [k0AutOrder.go]
  rw [if_pos hall]

private theorem lqKindE_autOrder_eq_two (c rk : List ℕ) (h6 : c.length = 6)
    (hmove : ∃ i ∈ c, rk.getD i 0 ≠ i)
    (hfix2 : ∀ i ∈ c, (k0pMul rk rk).getD i 0 = i) : k0AutOrder c rk = 2 := by
  have hnot : c.all (fun i => decide (rk.getD i 0 = i)) = false := by
    rw [List.all_eq_false]
    obtain ⟨i, hi, hne⟩ := hmove
    exact ⟨i, hi, by simpa using hne⟩
  have hall : c.all (fun i => decide ((k0pMul rk rk).getD i 0 = i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [hfix2 i hi]
    simp
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl, h6]
  simp only [k0AutOrder.go]
  rw [if_neg (by simpa using hnot), if_pos hall]

private theorem lqKindE_iterate_mem (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (h6 : (lqNodes A P j).length = 6)
    {x : Fin A.row.diagram.marks.length} (hx : x.val ∈ lqNodes A P j) :
    ((A.row.nodePerm^[(P.orbitNodes j).length]) x).val ∈ lqNodes A P j := by
  classical
  set c := lqNodes A P j with hc
  set s := (P.orbitNodes j).length with hs
  set Ψ := componentRoots (rootCharHom A.a) (P.repr j) with hΨ
  have hb := lq_nodes_basic A P j
  have hnd : c.Nodup := hb.2.1
  have hcb : ∀ y ∈ c, y < (k0DiagOf A.row.T).marks.length := by
    intro y hy
    have h := (hb.2.2 y hy).1
    rw [lqKindE_marks_length A]; exact h
  have hxzero : A.row.s.getD x.val 0 = 0 := (hb.2.2 x.val hx).2
  have hzero_iter : ∀ n (i : Fin A.row.diagram.marks.length),
      A.row.s.getD ((A.row.nodePerm^[n]) i).val 0 = 0 ↔ A.row.s.getD i.val 0 = 0 := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
        intro i
        rw [Function.iterate_succ_apply']
        exact (lqKindE_s_nodePerm_eq_zero_iff A (A.row.nodePerm^[n] i)).trans (ih i)
  let z : Fin A.row.diagram.marks.length := (A.row.nodePerm^[s]) x
  have hzzero : A.row.s.getD z.val 0 = 0 := (hzero_iter s x).mpr hxzero
  have hΨroot : IsRootComponent Ψ := hΨ ▸ isRootComponent_componentRoots (P.repr j)
  have hαΨ : A.nodeMap (Pi.single x 1) ∈ Ψ := by
    rw [hΨ, P.repr_roots j]
    exact ⟨A.node_isRoot x, Submodule.subset_span ⟨x, hx, rfl⟩⟩
  have hslen : s = componentOrbitLength A.setup.ρ Ψ := by
    rw [hs, hΨ]; exact (P.orbit_length j).symm
  have hσΨ : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s])
      (A.nodeMap (Pi.single x 1)) ∈ Ψ := by
    have himg : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) '' Ψ = Ψ := by
      rw [hslen]; exact lqKindE_orbit_image A.setup Ψ
    rw [← himg]
    exact ⟨_, hαΨ, rfl⟩
  have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
  have hεs : A.epsilon^s = 1 ∨ A.epsilon^s = -1 := by
    rcases hε with h | h <;> rw [h]
    · exact Or.inl (one_pow _)
    · rcases Nat.even_or_odd s with he | ho
      · exact Or.inl he.neg_one_pow
      · exact Or.inr ho.neg_one_pow
  have hσeq := lqKindE_frob_nodes_iterate A s x
  have hzΨ : A.nodeMap (Pi.single z 1) ∈ Ψ := by
    rw [hσeq] at hσΨ
    rcases hεs with he | he
    · rw [he, one_smul] at hσΨ
      simpa [z] using hσΨ
    · rw [he] at hσΨ
      have h := hΨroot.neg_mem _ hσΨ
      simpa using h
  have hzspan : lqExtRoot A.tau A.row.T z.val ∈
      Submodule.span ℤ {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
        w = lqExtRoot A.tau A.row.T i.val} := by
    have h1 : A.nodeMap (Pi.single z 1) ∈
        Submodule.span ℤ {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
          w = A.nodeMap (Pi.single i 1)} := by
      rw [hΨ, P.repr_roots j] at hzΨ
      exact hzΨ.2
    have hset : {w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
        i.val ∈ c ∧ w = A.nodeMap (Pi.single i 1)} =
        {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
          w = lqExtRoot A.tau A.row.T i.val} := by
      ext w
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, lq_nodeMap_eq A i⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, (lq_nodeMap_eq A i).symm⟩
    rw [hset] at h1
    rwa [lq_nodeMap_eq A z] at h1
  by_contra hznot
  have hTF : A.row.T ≠ .F4 := by
    intro hF
    have hlt : ∀ y ∈ c, y < 5 := by
      intro y hy
      have h := (hb.2.2 y hy).1
      have htau : A.tau = .F4 := by rw [← A.tau_eq, hF]; rfl
      rw [htau] at h
      have h4 : Tag.F4.rank = 4 := rfl
      rw [h4] at h
      omega
    have hsub : c.toFinset ⊆ Finset.range 5 := by
      intro y hy
      rw [Finset.mem_range]
      exact hlt y (List.mem_toFinset.mp hy)
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range, h6] at this
    omega
  have hTcases : A.row.T = .E6 ∨ A.row.T = .E7 ∨ A.row.T = .E8 := by
    have hall : ∀ T : GGKacType, T ≠ .F4 → T = .E6 ∨ T = .E7 ∨ T = .E8 := by
      intro T h
      cases T
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl h
    exact hall A.row.T hTF
  rcases hTcases with hT | hT | hT
  ·
    have hmarks : (k0DiagOf A.row.T).marks.length = 7 := by rw [hT]; rfl
    have hcard : (c.toFinset ∪ {z.val}).card = 7 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem]
      · rw [List.toFinset_card_of_nodup hnd, h6]
      · simpa using hznot
    have hunion : c.toFinset ∪ {z.val} = Finset.range (k0DiagOf A.row.T).marks.length := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        rw [Finset.mem_range]
        rcases Finset.mem_union.mp ha with h | h
        · exact hcb a (List.mem_toFinset.mp h)
        · rw [Finset.mem_singleton.mp h]; exact z.isLt
      · rw [Finset.card_range]
        omega
    have hall : ∀ i : Fin A.row.diagram.marks.length, A.row.s.getD i.val 0 = 0 := by
      intro i
      have hi : i.val ∈ c.toFinset ∪ {z.val} := by
        rw [hunion]; rw [Finset.mem_range]; exact i.isLt
      rcases Finset.mem_union.mp hi with h | h
      · exact (hb.2.2 i.val (List.mem_toFinset.mp h)).2
      · rw [Finset.mem_singleton.mp h]; exact hzzero
    have hsum := ggKacShVecs_sum (k0DiagOf A.row.T).marks p A.row.s A.row.s_mem
    have hsum0 : (∑ i : Fin (k0DiagOf A.row.T).marks.length,
        (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hall i, mul_zero]
    rw [hsum0] at hsum
    have hp := lqKindE_zero_lt A
    omega
  ·
    have hbig : 7 < (k0DiagOf A.row.T).marks.length := by
      rw [hT]; decide
    have hc'nd : (c ++ [z.val]).Nodup :=
      hnd.append (by simp) (by simp [List.disjoint_left, z, hznot])
    have hc'bound : ∀ y ∈ c ++ [z.val], y < (k0DiagOf A.row.T).marks.length := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hcb y h
      · rw [List.mem_singleton] at h; rw [h]; exact z.isLt
    have hproper' : ∃ i, i < (k0DiagOf A.row.T).marks.length ∧ i ∉ c ++ [z.val] := by
      by_contra h
      push Not at h
      have hlen : (c ++ [z.val]).length = 7 := by simp [h6]
      have hsub : Finset.range (k0DiagOf A.row.T).marks.length ⊆
          (c ++ [z.val]).toFinset := by
        intro i hi
        rw [List.mem_toFinset]
        exact h i (Finset.mem_range.mp hi)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range, List.toFinset_card_of_nodup hc'nd, hlen] at hcard
      omega
    have hLIq := lq_extRoot_independent A.tau A.row.T A.tau_eq (c ++ [z.val]) hc'nd
      hc'bound hproper'
    have hLIz : LinearIndependent ℤ
        (fun y : {y // y ∈ c ++ [z.val]} => lqExtRoot A.tau A.row.T y.1) :=
      lqKindE_li_z hLIq
    have hzspan' : lqExtRoot A.tau A.row.T z.val ∈
        Submodule.span ℤ ((fun y : {y // y ∈ c ++ [z.val]} =>
          lqExtRoot A.tau A.row.T y.1) '' {y | y ≠ ⟨z.val, List.mem_append_right _ (by simp)⟩}) := by
      have hset : {w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
          i.val ∈ c ∧ w = lqExtRoot A.tau A.row.T i.val} =
          (fun y : {y // y ∈ c ++ [z.val]} => lqExtRoot A.tau A.row.T y.1) ''
            {y | y ≠ ⟨z.val, List.mem_append_right _ (by simp)⟩} := by
        ext w
        constructor
        · rintro ⟨i, hi, rfl⟩
          refine ⟨⟨i.val, List.mem_append_left _ hi⟩, ?_, rfl⟩
          intro heq
          have hival : i.val = z.val := congrArg Subtype.val heq
          exact hznot (hival ▸ hi)
        · rintro ⟨y, hy, rfl⟩
          have hyc : y.val ∈ c := by
            rcases List.mem_append.mp y.2 with h | h
            · exact h
            · rw [List.mem_singleton] at h
              exact absurd (Subtype.ext h) hy
          exact ⟨⟨y.val, hc'bound y.val y.2⟩, hyc, rfl⟩
      rw [← hset]
      exact hzspan
    exact (LinearIndependent.notMem_span hLIz
      ⟨z.val, List.mem_append_right _ (by simp)⟩) hzspan'
  ·
    have hbig : 7 < (k0DiagOf A.row.T).marks.length := by rw [hT]; decide
    have hc'nd : (c ++ [z.val]).Nodup :=
      hnd.append (by simp) (by simp [List.disjoint_left, z, hznot])
    have hc'bound : ∀ y ∈ c ++ [z.val], y < (k0DiagOf A.row.T).marks.length := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hcb y h
      · rw [List.mem_singleton] at h; rw [h]; exact z.isLt
    have hproper' : ∃ i, i < (k0DiagOf A.row.T).marks.length ∧ i ∉ c ++ [z.val] := by
      by_contra h
      push Not at h
      have hlen : (c ++ [z.val]).length = 7 := by simp [h6]
      have hsub : Finset.range (k0DiagOf A.row.T).marks.length ⊆
          (c ++ [z.val]).toFinset := by
        intro i hi
        rw [List.mem_toFinset]
        exact h i (Finset.mem_range.mp hi)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range, List.toFinset_card_of_nodup hc'nd, hlen] at hcard
      omega
    have hLIq := lq_extRoot_independent A.tau A.row.T A.tau_eq (c ++ [z.val]) hc'nd
      hc'bound hproper'
    have hLIz : LinearIndependent ℤ
        (fun y : {y // y ∈ c ++ [z.val]} => lqExtRoot A.tau A.row.T y.1) :=
      lqKindE_li_z hLIq
    have hzspan' : lqExtRoot A.tau A.row.T z.val ∈
        Submodule.span ℤ ((fun y : {y // y ∈ c ++ [z.val]} =>
          lqExtRoot A.tau A.row.T y.1) '' {y | y ≠ ⟨z.val, List.mem_append_right _ (by simp)⟩}) := by
      have hset : {w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
          i.val ∈ c ∧ w = lqExtRoot A.tau A.row.T i.val} =
          (fun y : {y // y ∈ c ++ [z.val]} => lqExtRoot A.tau A.row.T y.1) ''
            {y | y ≠ ⟨z.val, List.mem_append_right _ (by simp)⟩} := by
        ext w
        constructor
        · rintro ⟨i, hi, rfl⟩
          refine ⟨⟨i.val, List.mem_append_left _ hi⟩, ?_, rfl⟩
          intro heq
          have hival : i.val = z.val := congrArg Subtype.val heq
          exact hznot (hival ▸ hi)
        · rintro ⟨y, hy, rfl⟩
          have hyc : y.val ∈ c := by
            rcases List.mem_append.mp y.2 with h | h
            · exact h
            · rw [List.mem_singleton] at h
              exact absurd (Subtype.ext h) hy
          exact ⟨⟨y.val, hc'bound y.val y.2⟩, hyc, rfl⟩
      rw [← hset]
      exact hzspan
    exact (LinearIndependent.notMem_span hLIz
      ⟨z.val, List.mem_append_right _ (by simp)⟩) hzspan'

theorem lq_kind_E6 (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h6 : (lqNodes A P j).length = 6)
    (hE : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .E6)
    (hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = 72) :
    (lqTw A P j = 1 → twistInner (componentRoots (rootCharHom A.a) (P.repr j))
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[componentOrbitLength A.setup.ρ
        (componentRoots (rootCharHom A.a) (P.repr j))])) ∧
    (lqTw A P j ≠ 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .exc) := by
  classical
  set c := lqNodes A P j with hc
  set s := (P.orbitNodes j).length with hs
  set Ψ := componentRoots (rootCharHom A.a) (P.repr j) with hΨ
  have hb := lq_nodes_basic A P j
  have hnd : c.Nodup := hb.2.1
  have hcb : ∀ y ∈ c, y < (k0DiagOf A.row.T).marks.length := by
    intro y hy
    have h := (hb.2.2 y hy).1
    rw [lqKindE_marks_length A]; exact h
  have hcompRank : compRank Ψ = 6 := lqKindE_compRank A P j h6
  have hncard : Ψ.ncard = 72 := hn
  have hΨroot : IsRootComponent Ψ := hΨ ▸ isRootComponent_componentRoots (P.repr j)
  have hrootΨ : ∀ γ ∈ Ψ, IsRoot A.tau γ := by
    intro γ hγ
    have hγ' := hγ
    rw [hΨ, P.repr_roots j] at hγ'
    exact hγ'.1
  have hspanΨ : ∀ γ ∈ Ψ, γ ∈ Submodule.span ℤ
      {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧ w = A.nodeMap (Pi.single i 1)} := by
    intro γ hγ
    have hγ' := hγ
    rw [hΨ, P.repr_roots j] at hγ'
    exact hγ'.2
  have hTF : A.row.T ≠ .F4 := by
    intro hF
    have hlt : ∀ y ∈ c, y < 5 := by
      intro y hy
      have h := (hb.2.2 y hy).1
      have htau : A.tau = .F4 := by rw [← A.tau_eq, hF]; rfl
      rw [htau] at h
      have h4 : Tag.F4.rank = 4 := rfl
      rw [h4] at h
      omega
    have hsub : c.toFinset ⊆ Finset.range 5 := by
      intro y hy
      rw [Finset.mem_range]
      exact hlt y (List.mem_toFinset.mp hy)
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range, h6] at this
    omega
  have hTcases : A.row.T = .E6 ∨ A.row.T = .E7 ∨ A.row.T = .E8 := by
    have hall : ∀ T : GGKacType, T ≠ .F4 → T = .E6 ∨ T = .E7 ∨ T = .E8 := by
      intro T h
      cases T
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl h
    exact hall A.row.T hTF
  set zero := (List.range (k0DiagOf A.row.T).marks.length).filter
    (fun i => decide (A.row.s.getD i 0 = 0)) with hzero
  have hzs : zero.Sublist (List.range (k0DiagOf A.row.T).marks.length) := List.filter_sublist
  have hzp : zero.length < (k0DiagOf A.row.T).marks.length := by
    by_contra hle
    push Not at hle
    have hle0 : zero.length ≤ (k0DiagOf A.row.T).marks.length := by
      simpa using hzs.length_le
    have hlen : zero.length = (k0DiagOf A.row.T).marks.length := le_antisymm hle0 hle
    have heq : zero = List.range (k0DiagOf A.row.T).marks.length := by
      apply hzs.eq_of_length
      simpa using hlen
    have hall : ∀ i : Fin (k0DiagOf A.row.T).marks.length, A.row.s.getD i.val 0 = 0 := by
      intro i
      have hi : i.val ∈ zero := by
        rw [heq, List.mem_range]
        exact i.isLt
      rw [hzero, List.mem_filter, List.mem_range] at hi
      exact of_decide_eq_true hi.2
    have hsum := lqKindE_weighted_sum A
    have hsum0 : (∑ i : Fin (k0DiagOf A.row.T).marks.length,
        (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hall i, mul_zero]
    rw [hsum0] at hsum
    have hp := lqKindE_zero_lt A
    omega
  have hcM : c ∈ k0Comps (k0DiagOf A.row.T) zero := by
    have := lq_nodes_mem_comps A P j
    simpa [hzero, c, lqNodes] using this
  have hlab := lqKindE_lab_table A.row.T hTcases zero
    (List.mem_sublists.mpr hzs) hzp c hcM hE
  set lob := lqKindE_lab A.row.T c with hlob
  have hlobnd : lob.Nodup := hlab.1
  have hlobset : lob.toFinset = c.toFinset := hlab.2.1
  have hloblt : ∀ i : Fin 6, lob.getD i.val 0 < (k0DiagOf A.row.T).marks.length :=
    hlab.2.2.1
  have hlobC : ∀ i j : Fin 6,
      iform (lqExtRoot (absTag A.row.T) A.row.T (lob.getD i.val 0))
            (lqExtRoot (absTag A.row.T) A.row.T (lob.getD j.val 0)) = lqKindE_C i j :=
    hlab.2.2.2
  have hloblen : lob.length = 6 := by
    have h1 : lob.toFinset.card = lob.length := List.toFinset_card_of_nodup hlobnd
    rw [hlobset, List.toFinset_card_of_nodup hnd, h6] at h1
    omega
  let labN : Fin 6 → ℕ := fun i => lob.getD i.val 0
  let labF : Fin 6 → Fin A.row.diagram.marks.length := fun i => ⟨labN i, hloblt i⟩
  have hlabNmem : ∀ i : Fin 6, labN i ∈ c := by
    intro i
    have hi : i.val < lob.length := by rw [hloblen]; exact i.isLt
    have h1 : labN i ∈ lob := by
      show lob.getD i.val 0 ∈ lob
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _
    rw [← List.mem_toFinset, ← hlobset, List.mem_toFinset]
    exact h1
  have hlabNinj : Function.Injective labN := by
    intro i j hij
    have hi : i.val < lob.length := by rw [hloblen]; exact i.isLt
    have hj : j.val < lob.length := by rw [hloblen]; exact j.isLt
    have h1 : lob[i.val] = lob[j.val] := by
      rw [← List.getD_eq_getElem _ _ hi, ← List.getD_eq_getElem _ _ hj]
      exact hij
    have h2 := (List.Nodup.getElem_inj_iff hlobnd).mp h1
    exact Fin.ext h2
  have hlabNsurj : ∀ x ∈ c, ∃ i : Fin 6, labN i = x := by
    intro x hx
    have hx' : x ∈ lob := by
      rw [← List.mem_toFinset, hlobset, List.mem_toFinset]
      exact hx
    obtain ⟨n, hn, hxn⟩ := List.mem_iff_getElem.mp hx'
    have hn6 : n < 6 := by rw [← hloblen]; exact hn
    refine ⟨⟨n, hn6⟩, ?_⟩
    show lob.getD n 0 = x
    rw [List.getD_eq_getElem _ _ (by rw [hloblen]; exact hn6)]
    exact hxn
  let e : Fin 6 ≃ {x // x ∈ c} :=
    Equiv.ofBijective (fun i => (⟨labN i, hlabNmem i⟩ : {x // x ∈ c}))
      ⟨fun i j hij => hlabNinj (congrArg Subtype.val hij),
       fun x => by
         obtain ⟨i, hi⟩ := hlabNsurj x.val x.2
         exact ⟨i, Subtype.ext hi⟩⟩
  let α : Fin 6 → (Fin A.tau.rank → ℤ) := fun i => A.nodeMap (Pi.single (labF i) 1)
  have hαeq : ∀ i, α i = lqExtRoot A.tau A.row.T (labN i) := fun i => lq_nodeMap_eq A (labF i)
  have hαroot : ∀ i, IsRoot A.tau (α i) := fun i => A.node_isRoot (labF i)
  have hαΨ : ∀ i, α i ∈ Ψ := by
    intro i
    rw [hΨ, P.repr_roots j]
    exact ⟨hαroot i, Submodule.subset_span ⟨labF i, hlabNmem i, rfl⟩⟩
  have hrange : Set.range α = {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
      w = A.nodeMap (Pi.single i 1)} := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨labF i, hlabNmem i, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := hlabNsurj x.val hx
      refine ⟨i, ?_⟩
      show A.nodeMap (Pi.single (labF i) 1) = A.nodeMap (Pi.single x 1)
      rw [show labF i = x from Fin.ext hi]
  have hC : ∀ i j, iform (α i) (α j) = lqKindE_C i j := by
    intro i j
    rw [hαeq i, hαeq j, ← A.tau_eq]
    exact hlobC i j
  have hπmem : ∀ i : Fin 6,
      ((A.row.nodePerm^[s]) (labF i)).val ∈ c :=
    fun i => lqKindE_iterate_mem A P j h6 (x := labF i) (hlabNmem i)
  let qfun : Fin 6 → Fin 6 := fun i =>
    (hlabNsurj ((A.row.nodePerm^[s]) (labF i)).val (hπmem i)).choose
  have hqfun : ∀ i, labN (qfun i) = ((A.row.nodePerm^[s]) (labF i)).val :=
    fun i => (hlabNsurj _ (hπmem i)).choose_spec
  have hqinj : Function.Injective qfun := by
    intro i j hij
    have h1 : labN (qfun i) = labN (qfun j) := congrArg labN hij
    rw [hqfun i, hqfun j] at h1
    have h2 : (A.row.nodePerm^[s]) (labF i) = (A.row.nodePerm^[s]) (labF j) := Fin.ext h1
    have h3 : labF i = labF j := (A.row.nodePerm.injective.iterate s) h2
    exact hlabNinj (congrArg (fun z : Fin A.row.diagram.marks.length => z.val) h3)
  let q : Equiv.Perm (Fin 6) := Equiv.ofBijective qfun ⟨hqinj, Finite.surjective_of_injective hqinj⟩
  have hqf : ∀ i, q i = qfun i := fun i => rfl
  have hlabFq : ∀ i, labF (q i) = (A.row.nodePerm^[s]) (labF i) := by
    intro i
    exact Fin.ext (by rw [hqf]; exact hqfun i)
  have hσi : ∀ i : Fin 6, ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s])
      (α i) = A.epsilon^s • α (q i) := by
    intro i
    have h := lqKindE_frob_nodes_iterate A s (labF i)
    rw [← hlabFq i] at h
    simpa [α] using h
  have hqC : ∀ i j : Fin 6, lqKindE_C (q i) (q j) = lqKindE_C i j := by
    intro i j
    have h := lqKindE_iform_iterate A.setup s (α i) (α j)
    rw [hσi i, hσi j] at h
    rw [iform_smul_left, iform_smul_right] at h
    have he2 : A.epsilon^s * A.epsilon^s = 1 := by
      have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
      rcases hε with h | h <;> rw [h]
      · simp
      · rcases Nat.even_or_odd s with he | ho
        · rw [he.neg_one_pow]; norm_num
        · rw [ho.neg_one_pow]; norm_num
    rw [← mul_assoc, he2, one_mul] at h
    rw [hC (q i) (q j), hC i j] at h
    exact h
  have hqcases : q = 1 ∨ q = lqKindE_flip := lqKindE_perm_cases q hqC
  let rk : List ℕ := k0pPow A.row.rho s
  have hrk : ∀ i : Fin A.row.diagram.marks.length, rk.getD i.val 0 =
      (A.row.nodePerm^[s] i).val := fun i => lqKindE_k0pPow_getD_nodePerm A s i
  have hrklen : rk.length = A.row.diagram.marks.length := by
    rw [show rk = k0pPow A.row.rho s from rfl, lqKindE_k0pPow_length, A.row.rho_length]
  have hεvals : A.epsilon^s = 1 ∨ A.epsilon^s = -1 := by
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
    rcases hε with h | h <;> rw [h]
    · exact Or.inl (one_pow _)
    · rcases Nat.even_or_odd s with he | ho
      · exact Or.inl he.neg_one_pow
      · exact Or.inr ho.neg_one_pow
  let φ : (Fin A.tau.rank → ℤ) →ₗ[ℤ] (Fin A.tau.rank → ℤ) := (A.frobLinear ^ s).toLinearMap
  have hφρ : ∀ γ ∈ Ψ, ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) γ = φ γ := by
    intro γ hγ
    rw [lqKindE_rho_iterate_frobLinear A s (hrootΨ γ hγ)]
    exact (LinearEquiv.pow_apply A.frobLinear s γ).symm
  have hφ_apply : ∀ i : Fin 6, φ (α i) = A.epsilon^s • α (q i) := by
    intro i
    calc φ (α i) = ((A.frobLinear : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) (α i) := by
          simp [φ, LinearEquiv.pow_apply]
      _ = ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) (α i) :=
          (lqKindE_rho_iterate_frobLinear A s (hαroot i)).symm
      _ = A.epsilon^s • α (q i) := hσi i
  let μ : Fin A.tau.rank → ℤ := ∑ i : Fin 6, lqKindE_cvec i • α i
  have hμmem : μ ∈ Submodule.span ℤ Ψ := by
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hαΨ i))
  have hspanα : ∀ γ ∈ Ψ, γ ∈ Submodule.span ℤ (Set.range α) := by
    intro γ hγ
    have h := hspanΨ γ hγ
    rw [hrange]
    exact h
  have hμd : ∀ γ ∈ Ψ, (3:ℤ) ∣ iform μ γ := by
    intro γ hγ
    have hspan := hspanα γ hγ
    refine Submodule.span_induction (p := fun z _ => (3:ℤ) ∣ iform μ z) ?_ ?_ ?_ ?_ hspan
    · intro z hz
      obtain ⟨i, rfl⟩ := hz
      rw [show μ = ∑ i : Fin 6, lqKindE_cvec i • α i from rfl, lqKindE_pair_mu_alpha hC i]
      split_ifs <;> norm_num
    · rw [show iform μ 0 = 0 from by simpa using iform_smul_right (0:ℤ) μ 0]
      exact dvd_zero 3
    · intro a b _ _ ha hb
      rw [iform_add_right]
      exact dvd_add ha hb
    · intro n z _ hz
      rw [iform_smul_right]
      exact Dvd.dvd.mul_left hz n
  have hsl : ∀ γ ∈ Ψ, iform γ γ = 2 := by
    intro γ hγ
    obtain ⟨k, hk⟩ := iform_self_of_isRoot (hrootΨ γ hγ)
    rw [hk]
    have htau : A.tau = .E6 ∨ A.tau = .E7 ∨ A.tau = .E8 := by
      rcases hTcases with h | h | h
      · exact Or.inl (by rw [← A.tau_eq, h]; rfl)
      · exact Or.inr (Or.inl (by rw [← A.tau_eq, h]; rfl))
      · exact Or.inr (Or.inr (by rw [← A.tau_eq, h]; rfl))
    rw [lqKindE_symmetrizer_one htau k]
    norm_num
  have hqnode : ∀ i : Fin 6, ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s])
      (α i) = A.epsilon^s • α (q i) := hσi
  set o := k0AutOrder c rk with ho
  have htw : lqTw A P j =
      (if A.row.d = 2 ∧ s % 2 = 1 then (if o = 1 then 2 else if o = 2 then 1 else o) else o) := by
    simp only [lqTw]
    rw [show (P.orbitNodes j).length = s from rfl]
    rw [show (P.orbitNodes j).headD [] = c from rfl]
    have hct : k0CompType (k0DiagOf A.row.T) c =
        ((.E6 : LargeEvenLieTag), (k0CompType (k0DiagOf A.row.T) c).2) :=
      Prod.ext hE rfl
    rw [hct]
    simp only [k0Tau0Of, and_true]
    rw [ho]
  have hd12 : A.row.d = 1 ∨ A.row.d = 2 := by
    rw [A.row.d_eq]; split <;> simp
  have hflipne : lqKindE_flip ≠ 1 := by decide
  have hproper_c : ∃ i, i < (k0DiagOf A.row.T).marks.length ∧ i ∉ c := by
    by_contra h
    push Not at h
    have hcard := Finset.card_le_card
      (show Finset.range (k0DiagOf A.row.T).marks.length ⊆ c.toFinset from
        fun i hi => List.mem_toFinset.mpr (h i (Finset.mem_range.mp hi)))
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd, h6] at hcard
    rcases hTcases with h | h | h
    · rw [h] at hcard; simp [k0DiagOf, k0E6Diag] at hcard
    · rw [h] at hcard; simp [k0DiagOf, k0E7Diag] at hcard
    · rw [h] at hcard; simp [k0DiagOf, k0E8Diag] at hcard
  have hLIc : LinearIndependent ℚ (fun x : {x // x ∈ c} =>
      fun j => ((lqExtRoot A.tau A.row.T x.val j : ℤ) : ℚ)) :=
    lq_extRoot_independent A.tau A.row.T A.tau_eq c hnd hcb hproper_c
  have hLIα : LinearIndependent ℚ (fun i : Fin 6 =>
      fun j => ((α i j : ℤ) : ℚ)) := by
    refine (linearIndependent_equiv' e ?_).mpr hLIc
    funext i j
    have hval : (↑(e i) : ℕ) = labN i := by
      dsimp only [e]
      rfl
    simp [Function.comp, α, hαeq, hval]
  have hrange' : Set.range α = {w | ∃ x ∈ c, w = lqExtRoot A.tau A.row.T x} := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨labN i, hlabNmem i, hαeq i⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := hlabNsurj x hx
      refine ⟨i, ?_⟩
      rw [hαeq i, hi]
  have hcone : ∀ v, IsRoot A.tau v → v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : Fin 6 → ℕ, v = ∑ i, (n i : ℤ) • α i) ∨
      (∃ n : Fin 6 → ℕ, v = -∑ i, (n i : ℤ) • α i) := by
    intro v hv hvspan
    have hv' : v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot A.tau A.row.T x} := by
      rw [← hrange']
      exact hvspan
    obtain ⟨n, hsupp, hrep | hrep⟩ :=
      lq_cone_table A.tau A.row.T A.tau_eq hzs hzp hcM v hv hv'
    · left
      refine ⟨fun i => n (e i).val, ?_⟩
      rw [hrep, Finset.sum_subtype (p := fun x => x ∈ c) c.toFinset (fun x => by simp)
        (fun x => (n x : ℤ) • lqExtRoot A.tau A.row.T x),
        ← Equiv.sum_comp e (fun y : {x // x ∈ c} =>
          (n y.val : ℤ) • lqExtRoot A.tau A.row.T y.val)]
      apply Finset.sum_congr rfl
      intro i _
      have hval : (↑(e i) : ℕ) = labN i := rfl
      rw [hval, hαeq i]
      simp only [hval]
    · right
      refine ⟨fun i => n (e i).val, ?_⟩
      rw [hrep, Finset.sum_subtype (p := fun x => x ∈ c) c.toFinset (fun x => by simp)
        (fun x => (n x : ℤ) • lqExtRoot A.tau A.row.T x),
        ← Equiv.sum_comp e (fun y : {x // x ∈ c} =>
          (n y.val : ℤ) • lqExtRoot A.tau A.row.T y.val)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hval : (↑(e i) : ℕ) = labN i := rfl
      rw [hval, hαeq i]
      simp only [hval]

  have hrk_lab : ∀ k : Fin 6, rk.getD (labN k) 0 = labN (q k) := by
    intro k
    have h1 : rk.getD (labF k).val 0 = ((A.row.nodePerm^[s]) (labF k)).val := hrk (labF k)
    rw [← hlabFq k] at h1
    exact h1
  let negHom : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ) :=
    { toFun := fun z => -z
      map_zero' := by simp
      map_add' := by intro a b; abel }
  have hnegHom : ∀ z, negHom z = -z := fun z => rfl
  have hnotInnerNeg : ¬ twistInner Ψ (negHom : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) := by
    have hval : iform μ (negHom μ - μ) = -24 := by
      rw [hnegHom]
      have h2 : (-μ) - μ = (-2 : ℤ) • μ := by module
      rw [h2, iform_smul_right, lqKindE_pair_mu_mu hC]
      norm_num
    refine TableCRes.not_twistInner_of_disc hrootΨ hsl negHom (d := 3) hμmem hμd hμd ?_
    rw [hval]
    norm_num
  have hφsum : φ μ = A.epsilon^s • (∑ i : Fin 6, lqKindE_cvec i • α (q i)) := by
    rw [show μ = ∑ i : Fin 6, lqKindE_cvec i • α i from rfl, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, hφ_apply i, smul_comm]
  have hpair_flip : iform μ (∑ i : Fin 6, lqKindE_cvec i • α (lqKindE_flip i)) = 6 := by
    rw [iform_finset_sum_right]
    have h : ∀ i : Fin 6, iform μ (lqKindE_cvec i • α (lqKindE_flip i)) =
        lqKindE_cvec i * (3 * (if lqKindE_flip i = 0 then (1:ℤ) else 0)) := by
      intro i
      rw [iform_smul_right, show μ = ∑ i : Fin 6, lqKindE_cvec i • α i from rfl,
        lqKindE_pair_mu_alpha hC]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    rw [show (∑ i : Fin 6, lqKindE_cvec i * (3 * (if lqKindE_flip i = 0 then (1:ℤ) else 0))) = 6 by
      decide +kernel]
  have hbridge : lqTw A P j = 1 ↔
      ((q = 1 ∧ A.epsilon^s = 1) ∨ (q = lqKindE_flip ∧ A.epsilon^s = -1)) := by
    rw [htw]
    rcases hqcases with hq1 | hqfl
    · have ho1 : o = 1 := by
        rw [ho]
        refine lqKindE_autOrder_eq_one c rk h6 ?_
        intro i hi
        obtain ⟨k, hk⟩ := hlabNsurj i hi
        rw [← hk, hrk_lab k]
        rw [hq1]
        rfl
      rw [ho1]
      rw [lqKindE_bridge_arith hd12 A.epsilon_eq (Or.inl rfl)]
      simp [hq1, hflipne, hflipne.symm]
    · have hqq : ∀ k : Fin 6, q (q k) = k := by
        intro k
        rw [hqfl]
        fin_cases k <;> decide
      have ho2 : o = 2 := by
        rw [ho]
        refine lqKindE_autOrder_eq_two c rk h6 ?_ ?_
        · refine ⟨labN 0, hlabNmem 0, ?_⟩
          rw [hrk_lab 0, hqfl]
          intro h
          have h0 : labN (lqKindE_flip 0) = labN 0 := h
          have h5 : lqKindE_flip 0 = 5 := by decide
          have h50 : (5 : Fin 6) = 0 := by
            rw [← h5]
            exact hlabNinj h0
          exact absurd h50 (by decide)
        · intro i hi
          obtain ⟨k, hk⟩ := hlabNsurj i hi
          rw [← hk]
          have hkey : (k0pMul rk rk).getD (labN k) 0 = rk.getD (rk.getD (labN k) 0) 0 := by
            rw [lqKindE_k0pMul_getD rk rk (by rw [hrklen]; exact hloblt k)]
          rw [hkey, hrk_lab k, hrk_lab (q k), hqq k]
      rw [ho2]
      rw [lqKindE_bridge_arith hd12 A.epsilon_eq (Or.inr rfl)]
      simp [hqfl, hflipne, hflipne.symm]
  constructor
  · intro htw1
    rcases hbridge.mp htw1 with ⟨hq1, he1⟩ | ⟨hqfl, hefl⟩
    ·
      have hslen : componentOrbitLength A.setup.ρ Ψ = s := by rw [hΨ, P.orbit_length j, hs]
      rw [hslen]
      refine (lqKindE_twistInner_congr (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]))
        (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).mpr ?_
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      have hφ1 : ∀ i : Fin 6, φ (α i) = α i := by
        intro i
        rw [hφ_apply i, he1, one_smul, hq1]
        rfl
      have hfixspan : ∀ z ∈ Submodule.span ℤ (Set.range α), φ z = z := by
        intro z hz
        refine Submodule.span_induction (p := fun z _ => φ z = z) ?_ ?_ ?_ ?_ hz
        · intro y hy
          obtain ⟨i, rfl⟩ := hy
          exact hφ1 i
        · simp
        · intro a b _ _ ha hb
          rw [map_add, ha, hb]
        · intro n y _ hy
          rw [map_zsmul, hy]
      intro γ hγ
      rw [hfixspan γ (hspanα γ hγ)]
      simp
    ·
      have hslen : componentOrbitLength A.setup.ρ Ψ = s := by rw [hΨ, P.orbit_length j, hs]
      rw [hslen]
      obtain ⟨w, hw, opp, hwα⟩ :=
        lq_longest (τ := A.tau) (α := α) hαroot hLIα hcone
      have hclosure_sub :
          Subgroup.closure {s : WeylGroup A.tau | ∃ γ : Fin A.tau.rank → ℤ,
              IsRoot A.tau γ ∧ γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ} ≤
            Subgroup.closure {s : WeylGroup A.tau | ∃ γ ∈ Ψ, s = rootReflection γ} := by
        apply Subgroup.closure_mono
        rintro s ⟨γ, hγroot, hγspan, rfl⟩
        refine ⟨γ, ?_, rfl⟩
        rw [hΨ, P.repr_roots j]
        exact ⟨hγroot, by rwa [hrange] at hγspan⟩
      have hoppC : ∀ i j : Fin 6, lqKindE_C (opp i) (opp j) = lqKindE_C i j := by
        intro i j
        have h := iform_smul w (α i) (α j)
        rw [hwα i, hwα j] at h
        rw [show -α (opp i) = (-1:ℤ) • α (opp i) from by simp,
          show -α (opp j) = (-1:ℤ) • α (opp j) from by simp,
          iform_smul_left, iform_smul_right] at h
        have h' : iform (α (opp i)) (α (opp j)) = iform (α i) (α j) := by
          linarith
        rw [hC (opp i) (opp j), hC i j] at h'
        exact h'
      have hoppcases : opp = 1 ∨ opp = lqKindE_flip := lqKindE_perm_cases opp hoppC
      have hwflip : ∀ i : Fin 6, w • α i = -α (lqKindE_flip i) := by
        rcases hoppcases with hopp1 | hoppfl
        · exfalso
          apply hnotInnerNeg
          have hwneg : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = -z := by
            intro z hz
            refine Submodule.span_induction (p := fun z _ => w • z = -z) ?_ ?_ ?_ ?_ hz
            · intro y hy
              obtain ⟨i, rfl⟩ := hy
              rw [hwα i, hopp1]
              simp
            · simp
            · intro a b _ _ ha hb
              rw [smul_add, ha, hb]
              abel
            · intro n y _ hy
              have h1 : w • (n • y) = n • (w • y) := (smul_comm (n:ℤ) w y).symm
              rw [h1, hy, smul_neg]
          refine ⟨w, hclosure_sub hw, fun γ hγ => ?_⟩
          show -γ = w • γ
          rw [hwneg γ (hspanα γ hγ)]
        · intro i
          rw [hwα i, hoppfl]
      have hwfixspan : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = φ z := by
        intro z hz
        refine Submodule.span_induction (p := fun z _ => w • z = φ z) ?_ ?_ ?_ ?_ hz
        · intro y hy
          obtain ⟨i, rfl⟩ := hy
          rw [hwflip i, hφ_apply i, hqfl, hefl]
          simp
        · simp
        · intro a b _ _ ha hb
          rw [smul_add, ha, hb, map_add]
        · intro n y _ hy
          have h1 : w • (n • y) = n • (w • y) := (smul_comm (n:ℤ) w y).symm
          rw [h1, hy, map_zsmul]
      refine (lqKindE_twistInner_congr (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]))
        (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).mpr ?_
      refine ⟨w, hclosure_sub hw, fun γ hγ => ?_⟩
      exact (hwfixspan γ (hspanα γ hγ)).symm
  · intro htwne
    have hqouter : (q = 1 ∧ A.epsilon^s = -1) ∨ (q = lqKindE_flip ∧ A.epsilon^s = 1) := by
      rcases hqcases with hq1 | hqfl
      · rcases hεvals with he | he
        · exact absurd (hbridge.mpr (Or.inl ⟨hq1, he⟩)) htwne
        · exact Or.inl ⟨hq1, he⟩
      · rcases hεvals with he | he
        · exact Or.inr ⟨hqfl, he⟩
        · exact absurd (hbridge.mpr (Or.inr ⟨hqfl, he⟩)) htwne
    have hnot : ¬ twistInner Ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
      rw [lqKindE_twistInner_congr hφρ]
      rcases hqouter with ⟨hq1, he⟩ | ⟨hqfl, he⟩
      · have hval : iform μ (φ.toAddMonoidHom μ - μ) = -24 := by
          have hφμ : φ μ = -μ := by
            rw [hφsum, he, hq1, neg_one_smul]
            simp [μ, neg_smul]
          change iform μ (φ μ - μ) = -24
          rw [hφμ]
          have h2 : (-μ) - μ = (-2 : ℤ) • μ := by module
          rw [h2, iform_smul_right, lqKindE_pair_mu_mu hC]
          norm_num
        refine TableCRes.not_twistInner_of_disc hrootΨ hsl φ.toAddMonoidHom (d := 3)
          hμmem hμd hμd ?_
        rw [hval]
        norm_num
      · have hval : iform μ (φ.toAddMonoidHom μ - μ) = -6 := by
          have hφμ : φ μ = ∑ i : Fin 6, lqKindE_cvec i • α (lqKindE_flip i) := by
            rw [hφsum, he, one_smul, hqfl]
          change iform μ (φ μ - μ) = -6
          rw [hφμ, iform_sub_right, hpair_flip, lqKindE_pair_mu_mu hC]
          norm_num
        refine TableCRes.not_twistInner_of_disc hrootΨ hsl φ.toAddMonoidHom (d := 3)
          hμmem hμd hμd ?_
        rw [hval]
        norm_num
    have hslen : componentOrbitLength A.setup.ρ Ψ = s := by rw [hΨ, P.orbit_length j, hs]
    unfold twistKind
    rw [hslen]
    rw [if_neg hnot, if_pos (Or.inl ⟨hcompRank, hncard⟩)]

end CFSG.StandardType.GGK0LQ

end
