module

public import CFSG.LocalAnalysis.StandardType.GGK0LQTwist
public import CFSG.LocalAnalysis.StandardType.GGK0LQRoots
public import CFSG.LocalAnalysis.StandardType.GGK0LQShape
public import CFSG.LocalAnalysis.StandardType.GGK0LQLongest
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter
import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.Steinberg.Adjoint

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private theorem lqKindD_k0pMul_getD (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
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

private theorem lqKindD_k0pPow_go (a : List ℕ) (f : ℕ) (acc : List ℕ) :
    k0pPow.go a f acc = acc.map ((fun j => a.getD j 0)^[f]) := by
  induction f generalizing acc with
  | zero => simp only [k0pPow.go, Function.iterate_zero, List.map_id]
  | succ f ih =>
      rw [show k0pPow.go a (f+1) acc = k0pPow.go a f (k0pMul a acc) from rfl, ih]
      unfold k0pMul
      rw [List.map_map]
      congr 1

private theorem lqKindD_k0pPow_getD (a : List ℕ) (n : ℕ) {i : ℕ} (hi : i < a.length) :
    (k0pPow a n).getD i 0 = (fun j => a.getD j 0)^[n] i := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lqKindD_k0pPow_go,
    k0pId, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

private theorem lqKindD_k0pPow_length (a : List ℕ) (n : ℕ) :
    (k0pPow a n).length = a.length := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lqKindD_k0pPow_go]
  simp [k0pId]

private theorem lqKindD_rho_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (fun j => A.row.rho.getD j 0)^[n] i.val = (A.row.nodePerm^[n] i).val := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, A.row.rho_apply, Function.iterate_succ_apply']

private theorem lqKindD_k0pPow_getD_nodePerm (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (k0pPow A.row.rho n).getD i.val 0 = (A.row.nodePerm^[n] i).val := by
  rw [lqKindD_k0pPow_getD A.row.rho n (by rw [A.row.rho_length]; exact i.isLt)]
  exact lqKindD_rho_iterate A n i

private theorem lqKindD_frob_nodes_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
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

private theorem lqKindD_iform_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) x) (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) y) =
      iform x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]

private theorem lqKindD_orbit_image {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (Ψ : Set (Fin τ.rank → ℤ)) :
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ]) '' Ψ = Ψ := by
  by_cases h : ({s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}).Nonempty
  · exact (Nat.sInf_mem h).2
  · have h0 : componentOrbitLength S.ρ Ψ = 0 := by
      unfold componentOrbitLength
      rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty]
    rw [h0]
    simp

private theorem lqKindD_rho_iterate_frobLinear (A : K0LangMark Omega lab p R I phi) (n : ℕ)
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

private theorem lqKindD_twistInner_congr {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (h : ∀ γ ∈ Ψ, σ γ = σ' γ) :
    twistInner Ψ σ ↔ twistInner Ψ σ' := by
  unfold twistInner
  constructor
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).symm.trans (hσ γ hγ)⟩
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).trans (hσ γ hγ)⟩

private theorem lqKindD_marks_pos (T : GGKacType) (i : Fin (k0DiagOf T).marks.length) :
    0 < (k0DiagOf T).marks.getD i.val 0 := by
  cases T <;> fin_cases i <;> decide

private theorem lqKindD_pair (T : GGKacType) (hT : T ≠ .F4)
    (x y : Fin (k0DiagOf T).marks.length) :
    iform (lqExtRoot (absTag T) T x.val) (lqExtRoot (absTag T) T y.val) =
      if x = y then 2 else if 0 < (k0DiagOf T).adj x.val y.val then -1 else 0 := by
  cases T
  · fin_cases x <;> fin_cases y <;> decide
  · fin_cases x <;> fin_cases y <;> decide
  · fin_cases x <;> fin_cases y <;> decide
  · exact absurd rfl hT

private lemma lqKindD_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private lemma lqKindD_marks_length_A (A : K0LangMark Omega lab p R I phi) :
    A.row.diagram.marks.length = A.tau.rank + 1 := by
  rw [← A.tau_eq]
  exact lqKindD_marks_length A.row.T

private lemma lqKindD_lt_marks (A : K0LangMark Omega lab p R I phi) {x : ℕ}
    (h : x < A.tau.rank + 1) : x < A.row.diagram.marks.length := by
  rw [show A.row.diagram.marks.length = A.tau.rank + 1 from lqKindD_marks_length_A A]
  exact h
private theorem lqKindD_p_pos (A : K0LangMark Omega lab p R I phi) : 0 < p := by
  obtain ⟨N⟩ := k0Normal_nonempty A
  exact N.zero_lt

private theorem lqKindD_nodes_proper (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    ∃ i < (k0DiagOf A.row.T).marks.length, i ∉ lqNodes A P j := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hnb := lq_nodes_basic A P j
  have hsum := ggKacShVecs_sum (k0DiagOf A.row.T).marks p A.row.s A.row.s_mem
  have hzero : (∑ i : Fin (k0DiagOf A.row.T).marks.length,
      (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hs : A.row.s.getD i.val 0 = 0 := (hnb.2.2 i.val (h i.val i.isLt)).2
    rw [hs, mul_zero]
  rw [hzero] at hsum
  have hp := lqKindD_p_pos A
  omega

private lemma lqKindD_sum_subtype {M : Type*} [AddCommMonoid M] (c : List ℕ) (f : ℕ → M) :
    (∑ x ∈ c.toFinset, f x) = ∑ x : {x // x ∈ c}, f x.1 := by
  rw [← Finset.sum_coe_sort c.toFinset f]
  let e : {x // x ∈ c.toFinset} ≃ {x // x ∈ c} :=
    { toFun := fun x => ⟨x.1, List.mem_toFinset.mp x.2⟩
      invFun := fun x => ⟨x.1, List.mem_toFinset.mpr x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  exact Fintype.sum_equiv e (fun x => f x.1) (fun x => f x.1) (fun x => rfl)

private theorem lqKindD_nodeSpan_relation (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    {w : Fin A.row.diagram.marks.length}
    (hspan : A.nodeMap (Pi.single w 1) ∈ Submodule.span ℤ
      {v | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ lqNodes A P j ∧
        v = A.nodeMap (Pi.single i 1)}) :
    w.val ∈ lqNodes A P j ∨
      ((A.row.diagram.marks.getD w.val 0 : ℤ) = 1 ∧
        ∀ x : Fin A.row.diagram.marks.length, x ≠ w → x.val ∈ lqNodes A P j) := by
  classical
  set c := lqNodes A P j with hc
  by_cases hw : w.val ∈ c
  · exact Or.inl hw
  · right
    have hxlt : ∀ x ∈ c, x < A.row.diagram.marks.length := by
      intro x hx
      have h := (lq_nodes_basic A P j).2.2 x (by simpa [hc] using hx)
      have hlen := lqKindD_marks_length_A A
      omega
    let α : {x // x ∈ c} → (Fin A.tau.rank → ℤ) := fun x =>
      A.nodeMap (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1)
    have hset : {v | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
        v = A.nodeMap (Pi.single i 1)} = Set.range α := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i.val, hi⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨⟨x.1, hxlt x.1 x.2⟩, x.2, rfl⟩
    have hspanα : A.nodeMap (Pi.single w 1) ∈ Submodule.span ℤ (Set.range α) := by
      rw [← hset]
      exact hspan
    obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspanα
    let b : Fin A.row.diagram.marks.length → ℤ := fun i =>
      (if h : i.val ∈ c then - f ⟨i.val, h⟩ else 0) + (if i = w then 1 else 0)
    have hb0 : (fun i => (if h : i.val ∈ c then - f ⟨i.val, h⟩ else 0))
        = ∑ x : {x // x ∈ c},
            (- f x) • (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1 :
              Fin A.row.diagram.marks.length → ℤ) := by
      funext i
      rw [Finset.sum_apply]
      by_cases hi : i.val ∈ c
      · rw [dif_pos hi]
        have hsingle : ∀ x : {x // x ∈ c}, x ≠ ⟨i.val, hi⟩ →
            ((- f x) • (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1 :
              Fin A.row.diagram.marks.length → ℤ)) i = 0 := by
          intro x hx
          have hne : x.1 ≠ i.val := fun h => hx (Subtype.ext h)
          rw [Pi.smul_apply, Pi.single_eq_of_ne]
          · simp
          · intro h; exact hne (congrArg Fin.val h).symm
        rw [Finset.sum_eq_single (⟨i.val, hi⟩ : {x // x ∈ c}) (fun x _ hx => hsingle x hx)]
        · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]; ring
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [dif_neg hi]
        have hzero : ∀ x : {x // x ∈ c},
            ((- f x) • (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1 :
              Fin A.row.diagram.marks.length → ℤ)) i = 0 := by
          intro x
          rw [Pi.smul_apply, Pi.single_eq_of_ne]
          · simp
          · intro h; exact hi (h ▸ x.2)
        rw [Finset.sum_eq_zero (fun x _ => hzero x)]
    have hb : b = (fun i => (if h : i.val ∈ c then - f ⟨i.val, h⟩ else 0))
        + (Pi.single w 1 : Fin A.row.diagram.marks.length → ℤ) := by
      funext i
      by_cases hi : i = w
      · subst hi
        simp [b, hw]
      · simp [b, hi]
    have hnode : A.nodeMap (fun i => (if h : i.val ∈ c then - f ⟨i.val, h⟩ else 0)) =
        - A.nodeMap (Pi.single w 1) := by
      rw [hb0, map_sum]
      calc (∑ x : {x // x ∈ c}, A.nodeMap ((- f x) •
            (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1 : Fin A.row.diagram.marks.length → ℤ)))
          = ∑ x : {x // x ∈ c}, (- f x) • A.nodeMap (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1) := by
              simp only [map_smul]
        _ = ∑ x : {x // x ∈ c},
              -(f x • A.nodeMap (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1)) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [neg_smul]
        _ = -(∑ x : {x // x ∈ c}, f x •
              A.nodeMap (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1)) := by
              rw [Finset.sum_neg_distrib]
        _ = -A.nodeMap (Pi.single w 1) := by rw [hf]
    have hker : b ∈ A.nodeMap.ker := by
      rw [LinearMap.mem_ker, hb, map_add, hnode]
      abel
    rw [A.nodeMap_ker, Submodule.mem_span_singleton] at hker
    obtain ⟨k, hk⟩ := hker
    have hbw : b w = 1 := by
      simp [b, hw]
    have hkw : k * (A.row.diagram.marks.getD w.val 0 : ℤ) = 1 := by
      have h := congrFun hk w
      rw [Pi.smul_apply, smul_eq_mul] at h
      rw [h, hbw]
    have hmwpos : 0 < (A.row.diagram.marks.getD w.val 0 : ℤ) := by
      have := lqKindD_marks_pos A.row.T w
      exact_mod_cast this
    have hmw1 : (A.row.diagram.marks.getD w.val 0 : ℤ) = 1 := by
      have hdvd : (A.row.diagram.marks.getD w.val 0 : ℤ) ∣ 1 :=
        ⟨k, by rw [mul_comm]; exact hkw.symm⟩
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
      · exact h
      · omega
    refine ⟨hmw1, fun x hxw => ?_⟩
    by_contra hxc
    have hbx : b x = 0 := by
      simp [b, hxc, hxw]
    have hx0 : k * (A.row.diagram.marks.getD x.val 0 : ℤ) = 0 := by
      have h := congrFun hk x
      rw [Pi.smul_apply, smul_eq_mul] at h
      rw [h, hbx]
    have hxpos : 0 < (A.row.diagram.marks.getD x.val 0 : ℤ) := by
      have := lqKindD_marks_pos A.row.T x
      exact_mod_cast this
    have hk0 : k = 0 := by
      rcases Int.mul_eq_zero.mp hx0 with h | h
      · exact h
      · exact absurd h (ne_of_gt hxpos)
    have hk1 : k = 1 := by
      have h := hkw
      rw [hmw1, mul_one] at h
      exact h
    rw [hk0] at hk1
    omega

private theorem lqKindD_node_mem_span (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hgap : (lqNodes A P j).length + 1 = A.row.diagram.marks.length →
      ∀ w < A.row.diagram.marks.length, w ∉ lqNodes A P j →
        1 < A.row.diagram.marks.getD w 0)
    {w : Fin A.row.diagram.marks.length}
    (hspan : A.nodeMap (Pi.single w 1) ∈ Submodule.span ℤ
      {v | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ lqNodes A P j ∧
        v = A.nodeMap (Pi.single i 1)}) :
    w.val ∈ lqNodes A P j := by
  classical
  rcases lqKindD_nodeSpan_relation A P j hspan with h | ⟨hm1, hall⟩
  · exact h
  · by_cases hw : w.val ∈ lqNodes A P j
    · exact hw
    · exfalso
      set c := lqNodes A P j with hc
      have hmem : c.Nodup := (lq_nodes_basic A P j).2.1
      have hsub : ∀ x ∈ c, x < A.row.diagram.marks.length := fun x hx =>
        (lq_nodes_basic A P j).2.2 x (by simpa [hc] using hx) |>.1.trans_le (by
          rw [lqKindD_marks_length_A A])
      have hlen : c.length + 1 = A.row.diagram.marks.length := by
        have hnd' : (w.val :: c).Nodup := List.nodup_cons.mpr ⟨by simpa [hc] using hw, hmem⟩
        have hsub' : ∀ x : Fin A.row.diagram.marks.length, x.val ∈ w.val :: c := by
          intro x
          by_cases hx : x = w
          · subst hx; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hall x hx)
        have hfs : (w.val :: c).toFinset = Finset.range A.row.diagram.marks.length := by
          ext x
          rw [List.mem_toFinset, Finset.mem_range]
          constructor
          · intro hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact w.isLt
            · exact hsub x hx
          · intro hx
            exact hsub' ⟨x, hx⟩
        have hcard := congrArg Finset.card hfs
        rw [List.toFinset_card_of_nodup hnd', Finset.card_range, List.length_cons] at hcard
        have hml : A.row.diagram.marks.length = (k0DiagOf A.row.T).marks.length := rfl
        rw [hml] at hcard ⊢
        omega
      have h2 : (1 : ℕ) < A.row.diagram.marks.getD w.val 0 :=
        hgap hlen w.val w.isLt (by simpa [hc] using hw)
      have hm1' : A.row.diagram.marks.getD w.val 0 = 1 := by exact_mod_cast hm1
      omega

private theorem lqKindD_maps_c (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hgap : (lqNodes A P j).length + 1 = A.row.diagram.marks.length →
      ∀ w < A.row.diagram.marks.length, w ∉ lqNodes A P j →
        1 < A.row.diagram.marks.getD w 0) (s : ℕ)
    (hs : s = (P.orbitNodes j).length) {x : ℕ} (hx : x ∈ lqNodes A P j) :
    (A.row.nodePerm^[s] ⟨x, lqKindD_lt_marks A ((lq_nodes_basic A P j).2.2 x hx).1⟩).val ∈
      lqNodes A P j := by
  classical
  set c := lqNodes A P j with hc
  have hxlt : ∀ y ∈ c, y < A.row.diagram.marks.length := by
    intro y hy
    exact lqKindD_lt_marks A ((lq_nodes_basic A P j).2.2 y (by simpa [hc] using hy)).1
  let i : Fin A.row.diagram.marks.length := ⟨x, hxlt x hx⟩
  set ψ := componentRoots (rootCharHom A.a) (P.repr j) with hψ
  have hψroot : IsRootComponent ψ := hψ ▸ isRootComponent_componentRoots (P.repr j)
  have hαψ : A.nodeMap (Pi.single i 1) ∈ ψ := by
    rw [hψ, P.repr_roots j]
    refine ⟨A.node_isRoot i, Submodule.subset_span ⟨i, ?_, rfl⟩⟩
    exact hx
  have hclosed : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) '' ψ = ψ := by
    have hlen : s = componentOrbitLength A.setup.ρ ψ := by
      rw [hs, hψ]; exact (P.orbit_length j).symm
    rw [hlen]; exact lqKindD_orbit_image A.setup ψ
  have hσψ : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s])
      (A.nodeMap (Pi.single i 1)) ∈ ψ := by
    rw [← hclosed]; exact ⟨_, hαψ, rfl⟩
  have hσ := lqKindD_frob_nodes_iterate A s i
  have hes : A.epsilon ^ s = 1 ∨ A.epsilon ^ s = -1 := by
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by
      rw [A.epsilon_eq]; split <;> simp
    rcases hε with hε | hε
    · exact Or.inl (by rw [hε, one_pow])
    · rcases Nat.even_or_odd s with he | ho
      · exact Or.inl (by rw [hε]; exact he.neg_one_pow)
      · exact Or.inr (by rw [hε]; exact ho.neg_one_pow)
  have hα'ψ : A.nodeMap (Pi.single ((A.row.nodePerm^[s]) i) 1) ∈ ψ := by
    rcases hes with h | h
    · rw [h, one_smul] at hσ
      rw [← hσ]; exact hσψ
    · rw [h, neg_one_smul] at hσ
      have : A.nodeMap (Pi.single ((A.row.nodePerm^[s]) i) 1) =
          -(((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (A.nodeMap (Pi.single i 1))) := by
        rw [hσ]; simp
      rw [this]
      exact hψroot.neg_mem _ hσψ
  have hsp : A.nodeMap (Pi.single ((A.row.nodePerm^[s]) i) 1) ∈ Submodule.span ℤ
      {v | ∃ k : Fin A.row.diagram.marks.length, k.val ∈ c ∧
        v = A.nodeMap (Pi.single k 1)} := by
    have h := hα'ψ
    rw [hψ, P.repr_roots j] at h
    exact h.2
  exact lqKindD_node_mem_span A P j hgap hsp

private theorem lqKindD_cone (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (hmem : lqNodes A P j ∈ k0Comps (k0DiagOf A.row.T)
      ((List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0))))
    (hzproper : ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).length
        < (k0DiagOf A.row.T).marks.length) :
    ∀ v : Fin A.tau.rank → ℤ, IsRoot A.tau v →
      v ∈ Submodule.span ℤ (Set.range (fun x : {x // x ∈ lqNodes A P j} =>
        A.nodeMap (Pi.single ⟨x.1, lqKindD_lt_marks A
          ((lq_nodes_basic A P j).2.2 x.1 x.2).1⟩ 1))) →
      (∃ n : {x // x ∈ lqNodes A P j} → ℕ,
          v = ∑ x, (n x : ℤ) • A.nodeMap (Pi.single ⟨x.1, lqKindD_lt_marks A
            ((lq_nodes_basic A P j).2.2 x.1 x.2).1⟩ 1)) ∨
        (∃ n : {x // x ∈ lqNodes A P j} → ℕ,
          v = -∑ x, (n x : ℤ) • A.nodeMap (Pi.single ⟨x.1, lqKindD_lt_marks A
            ((lq_nodes_basic A P j).2.2 x.1 x.2).1⟩ 1)) := by
  classical
  set c := lqNodes A P j with hc
  have hxlt : ∀ x ∈ c, x < A.row.diagram.marks.length := fun x hx =>
    lqKindD_lt_marks A ((lq_nodes_basic A P j).2.2 x (by simpa [hc] using hx)).1
  let α : {x // x ∈ c} → (Fin A.tau.rank → ℤ) := fun x =>
    A.nodeMap (Pi.single ⟨x.1, hxlt x.1 x.2⟩ 1)
  intro v hv hvspan
  have hspan' : v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot A.tau A.row.T x} := by
    have hset : Set.range α = {w | ∃ x ∈ c, w = lqExtRoot A.tau A.row.T x} := by
      ext w
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, lq_nodeMap_eq A ⟨x.1, hxlt x.1 x.2⟩⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, lq_nodeMap_eq A ⟨x, hxlt x hx⟩⟩
    rw [hset] at hvspan
    exact hvspan
  obtain ⟨n, hsupp, hvsum | hvsum⟩ :=
    lq_cone_table A.tau A.row.T A.tau_eq (List.filter_sublist) hzproper hmem v hv hspan'
  · left
    refine ⟨fun x => n x.1, ?_⟩
    rw [hvsum, lqKindD_sum_subtype c (fun x => (n x : ℤ) • lqExtRoot A.tau A.row.T x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lq_nodeMap_eq A ⟨x.1, hxlt x.1 x.2⟩]
  · right
    refine ⟨fun x => n x.1, ?_⟩
    rw [hvsum, lqKindD_sum_subtype c (fun x => (n x : ℤ) • lqExtRoot A.tau A.row.T x)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lq_nodeMap_eq A ⟨x.1, hxlt x.1 x.2⟩]

private lemma lqKindD_symm_one {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    τ.symmetrizer j j = 1 := by
  rcases hτ with rfl | rfl | rfl <;> simp [Tag.symmetrizer]

private lemma lqKindD_absTag_eq_F4 {T : GGKacType} (h : absTag T = .F4) : T = .F4 := by
  cases T <;> simp [absTag] at h ⊢

private def lqKindD_shapes (T : GGKacType) : List (List ℕ) :=
  match T with
  | .E6 => [[2,3,4,5],[0,2,3,4,5],[1,2,3,4,5],[2,3,4,5,6]]
  | .E7 => [[2,3,4,5],[1,2,3,4,5],[0,1,2,3,4,5],[2,3,4,5,6],[2,3,4,5,6,7]]
  | .E8 => [[2,3,4,5],[1,2,3,4,5],[2,3,4,5,6],[2,3,4,5,6,7],
      [2,3,4,5,6,7,8],[0,2,3,4,5,6,7,8]]
  | .F4 => []

private theorem lqKindD_shape_mem (T : GGKacType) :
    ∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      ∀ c ∈ k0Comps (k0DiagOf T) zero,
        (k0CompType (k0DiagOf T) c).1 = .D → 4 ≤ c.length →
        c ∈ lqKindD_shapes T := by
  cases T <;> decide +kernel

private def lqKindD_pairVal (T : GGKacType) (x y : ℕ) : ℤ :=
  if x = y then 2 else if 0 < (k0DiagOf T).adj x y then -1 else 0

private abbrev lqKindD_adjD (r : ℕ) (i j : Fin r) : Prop :=
  ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ max i.val j.val ≤ r - 3) ∨
    ((i.val = r - 3 ∧ (j.val = r - 2 ∨ j.val = r - 1)) ∨
      (j.val = r - 3 ∧ (i.val = r - 2 ∨ i.val = r - 1)))

private abbrev lqKindD_cartan (r : ℕ) (i j : Fin r) : ℤ :=
  if i = j then 2 else if lqKindD_adjD r i j then -1 else 0

private def lqKindD_path : List ℕ → List ℕ
  | [2,3,4,5] => [2,4,3,5]
  | [0,2,3,4,5] => [0,2,4,3,5]
  | [1,2,3,4,5] => [1,3,4,2,5]
  | [2,3,4,5,6] => [6,5,4,2,3]
  | [0,1,2,3,4,5] => [0,1,3,4,2,5]
  | [2,3,4,5,6,7] => [7,6,5,4,2,3]
  | [2,3,4,5,6,7,8] => [8,7,6,5,4,2,3]
  | [0,2,3,4,5,6,7,8] => [0,8,7,6,5,4,2,3]
  | _ => []

private abbrev lqKindD_pathOK (T : GGKacType) (c : List ℕ) : Prop :=
  (lqKindD_path c).length = c.length ∧ (lqKindD_path c).Nodup ∧
    (lqKindD_path c).toFinset = c.toFinset ∧
    (∀ i j : Fin c.length,
      lqKindD_pairVal T ((lqKindD_path c).getD i.val 0) ((lqKindD_path c).getD j.val 0) =
        lqKindD_cartan c.length i j) ∧
    (c.length + 1 = (k0DiagOf T).marks.length →
      ∀ w < (k0DiagOf T).marks.length, w ∉ c → 1 < (k0DiagOf T).marks.getD w 0)

private def lqKindD_pathCheck (T : GGKacType) (c : List ℕ) : Bool :=
  decide (lqKindD_pathOK T c)

private theorem lqKindD_pathOK_table (T : GGKacType) (hT : T ≠ .F4) :
    ∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      ∀ c ∈ k0Comps (k0DiagOf T) zero,
        (k0CompType (k0DiagOf T) c).1 = .D → 4 ≤ c.length →
        lqKindD_pathCheck T c = true := by
  cases T <;> first | exact absurd rfl hT | (decide +kernel)

private def lqKindD_swapLeaf (r : ℕ) : Equiv.Perm (Fin r) :=
  if h : 2 ≤ r then Equiv.swap (⟨r - 2, by omega⟩ : Fin r) ⟨r - 1, by omega⟩ else 1

private theorem lqKindD_perm_five (q : Equiv.Perm (Fin 5))
    (h : ∀ i j : Fin 5, lqKindD_cartan 5 (q i) (q j) = lqKindD_cartan 5 i j) :
    q = 1 ∨ q = Equiv.swap 3 4 := by
  revert q
  decide +kernel

private theorem lqKindD_perm_six (q : Equiv.Perm (Fin 6))
    (h : ∀ i j : Fin 6, lqKindD_cartan 6 (q i) (q j) = lqKindD_cartan 6 i j) :
    q = 1 ∨ q = Equiv.swap 4 5 := by
  revert q
  decide +kernel

private theorem lqKindD_fork_seven :
    ∀ x y z w : Fin 7, y ≠ z → y ≠ w → z ≠ w →
      lqKindD_cartan 7 x y = -1 → lqKindD_cartan 7 x z = -1 →
      lqKindD_cartan 7 x w = -1 → x = 4 := by
  decide +kernel

private theorem lqKindD_entry_seven :
    ∀ y z : Fin 7, lqKindD_cartan 7 4 y = -1 → lqKindD_cartan 7 y z = -1 →
      z ≠ 4 → y = 3 := by
  decide +kernel

private theorem lqKindD_chain_seven_3 :
    ∀ y : Fin 7, lqKindD_cartan 7 3 y = -1 → y ≠ 4 → y = 2 := by
  decide +kernel

private theorem lqKindD_chain_seven_2 :
    ∀ y : Fin 7, lqKindD_cartan 7 2 y = -1 → y ≠ 3 → y = 1 := by
  decide +kernel

private theorem lqKindD_chain_seven_1 :
    ∀ y : Fin 7, lqKindD_cartan 7 1 y = -1 → y ≠ 2 → y = 0 := by
  decide +kernel

private theorem lqKindD_fork_nbr_seven :
    ∀ y : Fin 7, lqKindD_cartan 7 4 y = -1 → y ≠ 3 → y = 5 ∨ y = 6 := by
  decide +kernel

private theorem lqKindD_perm_seven (q : Equiv.Perm (Fin 7))
    (h : ∀ i j : Fin 7, lqKindD_cartan 7 (q i) (q j) = lqKindD_cartan 7 i j) :
    q = 1 ∨ q = Equiv.swap 5 6 := by
  have hadj : ∀ i j : Fin 7, lqKindD_cartan 7 (q i) (q j) = -1 ↔
      lqKindD_cartan 7 i j = -1 := by
    intro i j; rw [h i j]
  have hne : ∀ i j : Fin 7, i ≠ j → q i ≠ q j := fun i j hij he => hij (q.injective he)
  have h4 : q 4 = 4 := by
    refine lqKindD_fork_seven (q 4) (q 3) (q 5) (q 6) ?_ ?_ ?_ ?_ ?_ ?_
    · exact hne 3 5 (by decide)
    · exact hne 3 6 (by decide)
    · exact hne 5 6 (by decide)
    · exact (hadj 4 3).mpr (by decide)
    · exact (hadj 4 5).mpr (by decide)
    · exact (hadj 4 6).mpr (by decide)
  have h3 : q 3 = 3 := by
    refine lqKindD_entry_seven (q 3) (q 2) ?_ ?_ ?_
    · exact h4 ▸ (hadj 4 3).mpr (by decide)
    · exact (hadj 3 2).mpr (by decide)
    · intro hc; exact (by decide : (2 : Fin 7) ≠ 4) (q.injective (hc.trans h4.symm))
  have h2 : q 2 = 2 := by
    refine lqKindD_chain_seven_3 (q 2) ?_ ?_
    · exact h3 ▸ (hadj 3 2).mpr (by decide)
    · intro hc; exact (by decide : (2 : Fin 7) ≠ 4) (q.injective (hc.trans h4.symm))
  have h1 : q 1 = 1 := by
    refine lqKindD_chain_seven_2 (q 1) ?_ ?_
    · exact h2 ▸ (hadj 2 1).mpr (by decide)
    · intro hc; exact (by decide : (1 : Fin 7) ≠ 3) (q.injective (hc.trans h3.symm))
  have h0 : q 0 = 0 := by
    refine lqKindD_chain_seven_1 (q 0) ?_ ?_
    · exact h1 ▸ (hadj 1 0).mpr (by decide)
    · intro hc; exact (by decide : (0 : Fin 7) ≠ 2) (q.injective (hc.trans h2.symm))
  have h5 : q 5 = 5 ∨ q 5 = 6 := by
    refine lqKindD_fork_nbr_seven (q 5) ?_ ?_
    · exact h4 ▸ (hadj 4 5).mpr (by decide)
    · intro hc; exact (by decide : (5 : Fin 7) ≠ 3) (q.injective (hc.trans h3.symm))
  have h6 : q 6 = 5 ∨ q 6 = 6 := by
    refine lqKindD_fork_nbr_seven (q 6) ?_ ?_
    · exact h4 ▸ (hadj 4 6).mpr (by decide)
    · intro hc; exact (by decide : (6 : Fin 7) ≠ 3) (q.injective (hc.trans h3.symm))
  rcases h5 with h5 | h5
  · left
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · rcases h6 with h6 | h6
      · exact absurd (q.injective (h5.trans h6.symm)) (by decide)
      · exact h6
  · right
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · simpa using h5
    · rcases h6 with h6 | h6
      · simpa using h6
      · exact absurd (q.injective (h5.trans h6.symm)) (by decide)

private theorem lqKindD_fork_eight :
    ∀ x y z w : Fin 8, y ≠ z → y ≠ w → z ≠ w →
      lqKindD_cartan 8 x y = -1 → lqKindD_cartan 8 x z = -1 →
      lqKindD_cartan 8 x w = -1 → x = 5 := by
  decide +kernel

private theorem lqKindD_entry_eight :
    ∀ y z : Fin 8, lqKindD_cartan 8 5 y = -1 → lqKindD_cartan 8 y z = -1 →
      z ≠ 5 → y = 4 := by
  decide +kernel

private theorem lqKindD_chain_eight_4 :
    ∀ y : Fin 8, lqKindD_cartan 8 4 y = -1 → y ≠ 5 → y = 3 := by
  decide +kernel

private theorem lqKindD_chain_eight_3 :
    ∀ y : Fin 8, lqKindD_cartan 8 3 y = -1 → y ≠ 4 → y = 2 := by
  decide +kernel

private theorem lqKindD_chain_eight_2 :
    ∀ y : Fin 8, lqKindD_cartan 8 2 y = -1 → y ≠ 3 → y = 1 := by
  decide +kernel

private theorem lqKindD_chain_eight_1 :
    ∀ y : Fin 8, lqKindD_cartan 8 1 y = -1 → y ≠ 2 → y = 0 := by
  decide +kernel

private theorem lqKindD_fork_nbr_eight :
    ∀ y : Fin 8, lqKindD_cartan 8 5 y = -1 → y ≠ 4 → y = 6 ∨ y = 7 := by
  decide +kernel

private theorem lqKindD_perm_eight (q : Equiv.Perm (Fin 8))
    (h : ∀ i j : Fin 8, lqKindD_cartan 8 (q i) (q j) = lqKindD_cartan 8 i j) :
    q = 1 ∨ q = Equiv.swap 6 7 := by
  have hadj : ∀ i j : Fin 8, lqKindD_cartan 8 (q i) (q j) = -1 ↔
      lqKindD_cartan 8 i j = -1 := by
    intro i j; rw [h i j]
  have hne : ∀ i j : Fin 8, i ≠ j → q i ≠ q j := fun i j hij he => hij (q.injective he)
  have h5 : q 5 = 5 := by
    refine lqKindD_fork_eight (q 5) (q 4) (q 6) (q 7) ?_ ?_ ?_ ?_ ?_ ?_
    · exact hne 4 6 (by decide)
    · exact hne 4 7 (by decide)
    · exact hne 6 7 (by decide)
    · exact (hadj 5 4).mpr (by decide)
    · exact (hadj 5 6).mpr (by decide)
    · exact (hadj 5 7).mpr (by decide)
  have h4 : q 4 = 4 := by
    refine lqKindD_entry_eight (q 4) (q 3) ?_ ?_ ?_
    · exact h5 ▸ (hadj 5 4).mpr (by decide)
    · exact (hadj 4 3).mpr (by decide)
    · intro hc; exact (by decide : (3 : Fin 8) ≠ 5) (q.injective (hc.trans h5.symm))
  have h3 : q 3 = 3 := by
    refine lqKindD_chain_eight_4 (q 3) ?_ ?_
    · exact h4 ▸ (hadj 4 3).mpr (by decide)
    · intro hc; exact (by decide : (3 : Fin 8) ≠ 5) (q.injective (hc.trans h5.symm))
  have h2 : q 2 = 2 := by
    refine lqKindD_chain_eight_3 (q 2) ?_ ?_
    · exact h3 ▸ (hadj 3 2).mpr (by decide)
    · intro hc; exact (by decide : (2 : Fin 8) ≠ 4) (q.injective (hc.trans h4.symm))
  have h1 : q 1 = 1 := by
    refine lqKindD_chain_eight_2 (q 1) ?_ ?_
    · exact h2 ▸ (hadj 2 1).mpr (by decide)
    · intro hc; exact (by decide : (1 : Fin 8) ≠ 3) (q.injective (hc.trans h3.symm))
  have h0 : q 0 = 0 := by
    refine lqKindD_chain_eight_1 (q 0) ?_ ?_
    · exact h1 ▸ (hadj 1 0).mpr (by decide)
    · intro hc; exact (by decide : (0 : Fin 8) ≠ 2) (q.injective (hc.trans h2.symm))
  have h6 : q 6 = 6 ∨ q 6 = 7 := by
    refine lqKindD_fork_nbr_eight (q 6) ?_ ?_
    · exact h5 ▸ (hadj 5 6).mpr (by decide)
    · intro hc; exact (by decide : (6 : Fin 8) ≠ 4) (q.injective (hc.trans h4.symm))
  have h7 : q 7 = 6 ∨ q 7 = 7 := by
    refine lqKindD_fork_nbr_eight (q 7) ?_ ?_
    · exact h5 ▸ (hadj 5 7).mpr (by decide)
    · intro hc; exact (by decide : (7 : Fin 8) ≠ 4) (q.injective (hc.trans h4.symm))
  rcases h6 with h6 | h6
  · left
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · rcases h7 with h7 | h7
      · exact absurd (q.injective (h6.trans h7.symm)) (by decide)
      · exact h7
  · right
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · simpa using h6
    · rcases h7 with h7 | h7
      · simpa using h7
      · exact absurd (q.injective (h6.trans h7.symm)) (by decide)

private theorem lqKindD_perm_cases (r : ℕ) (hr5 : 5 ≤ r) (hr8 : r ≤ 8)
    (q : Equiv.Perm (Fin r))
    (h : ∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j) :
    q = 1 ∨ q = lqKindD_swapLeaf r := by
  interval_cases r
  · rcases lqKindD_perm_five q h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; decide)
  · rcases lqKindD_perm_six q h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; decide)
  · rcases lqKindD_perm_seven q h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; decide)
  · rcases lqKindD_perm_eight q h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; decide)

private theorem lqKindD_autOrder_eq_one (c rk : List ℕ)
    (hfix : ∀ i ∈ c, rk.getD i 0 = i) : k0AutOrder c rk = 1 := by
  have hall : c.all (fun i => decide (rk.getD i 0 = i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [hfix i hi]
    simp
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl]
  rw [show c.length + 1 = Nat.succ c.length from rfl]
  simp only [k0AutOrder.go]
  rw [if_pos hall]

private theorem lqKindD_autOrder_eq_two (c rk : List ℕ) (h1 : 1 ≤ c.length)
    (hmove : ∃ i ∈ c, rk.getD i 0 ≠ i)
    (hfix2 : ∀ i ∈ c, (k0pMul rk rk).getD i 0 = i) : k0AutOrder c rk = 2 := by
  have _ := h1
  have hnot : c.all (fun i => decide (rk.getD i 0 = i)) = false := by
    rw [List.all_eq_false]
    obtain ⟨i, hi, hne⟩ := hmove
    exact ⟨i, hi, by simpa using hne⟩
  have hall : c.all (fun i => decide ((k0pMul rk rk).getD i 0 = i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [hfix2 i hi]
    simp
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl]
  rw [show c.length + 1 = Nat.succ (Nat.succ (c.length - 1)) from by omega]
  simp only [k0AutOrder.go]
  rw [if_neg (by simpa using hnot), if_pos hall]

private def lqKindD_mvec (r : ℕ) (hr : 0 < r) (q : Equiv.Perm (Fin r)) : Fin r → ℤ :=
  if h4 : r = 4 then
    (if (q ⟨2, by omega⟩).val = 3 then fun i => ([-1, -2, -2, -1] : List ℤ).getD i.val 0
    else fun i => ([-2, -2, -1, -1] : List ℤ).getD i.val 0)
  else
    fun i => (if r = 5 then ([-2, 0, -2, -1, 1] : List ℤ)
      else if r = 6 then ([-1, 0, -1, 0, -1, 0] : List ℤ)
      else if r = 7 then ([-2, 0, -2, 0, -2, -1, 1] : List ℤ)
      else ([-1, 0, -1, 0, -1, 0, -1, 0] : List ℤ)).getD i.val 0

private def lqKindD_val (r : ℕ) (hr : 0 < r) (q : Equiv.Perm (Fin r)) (e : ℤ) : ℤ :=
  ∑ i : Fin r, ∑ j : Fin r,
    lqKindD_mvec r hr q i *
      (e * lqKindD_mvec r hr q (q.symm j) * lqKindD_cartan r i j -
        lqKindD_mvec r hr q j * lqKindD_cartan r i j)

private theorem lqKindD_dvd_five (q : Equiv.Perm (Fin 5))
    (hq : q = 1 ∨ q = Equiv.swap 3 4) :
    ∀ j : Fin 5, (4 : ℤ) ∣ ∑ i : Fin 5,
      lqKindD_mvec 5 (by norm_num) q i * lqKindD_cartan 5 i j := by
  rcases hq with rfl | rfl <;> decide +kernel

private theorem lqKindD_dvd_six (q : Equiv.Perm (Fin 6))
    (hq : q = 1 ∨ q = Equiv.swap 4 5) :
    ∀ j : Fin 6, (2 : ℤ) ∣ ∑ i : Fin 6,
      lqKindD_mvec 6 (by norm_num) q i * lqKindD_cartan 6 i j := by
  rcases hq with rfl | rfl <;> decide +kernel

private theorem lqKindD_dvd_seven (q : Equiv.Perm (Fin 7))
    (hq : q = 1 ∨ q = Equiv.swap 5 6) :
    ∀ j : Fin 7, (4 : ℤ) ∣ ∑ i : Fin 7,
      lqKindD_mvec 7 (by norm_num) q i * lqKindD_cartan 7 i j := by
  rcases hq with rfl | rfl <;> decide +kernel

private theorem lqKindD_dvd_eight (q : Equiv.Perm (Fin 8))
    (hq : q = 1 ∨ q = Equiv.swap 6 7) :
    ∀ j : Fin 8, (2 : ℤ) ∣ ∑ i : Fin 8,
      lqKindD_mvec 8 (by norm_num) q i * lqKindD_cartan 8 i j := by
  rcases hq with rfl | rfl <;> decide +kernel

private theorem lqKindD_dvd_four (q : Equiv.Perm (Fin 4)) :
    ∀ j : Fin 4, (2 : ℤ) ∣ ∑ i : Fin 4,
      lqKindD_mvec 4 (by norm_num) q i * lqKindD_cartan 4 i j := by
  revert q
  decide +kernel

private theorem lqKindD_val_five :
    ¬ (4 : ℤ) * 4 ∣ lqKindD_val 5 (by norm_num) (Equiv.swap 3 4) 1 ∧
    ¬ (4 : ℤ) * 4 ∣ lqKindD_val 5 (by norm_num) 1 (-1) := by
  decide +kernel

private theorem lqKindD_val_six :
    ¬ (2 : ℤ) * 2 ∣ lqKindD_val 6 (by norm_num) (Equiv.swap 4 5) 1 ∧
    ¬ (2 : ℤ) * 2 ∣ lqKindD_val 6 (by norm_num) (Equiv.swap 4 5) (-1) := by
  decide +kernel

private theorem lqKindD_val_seven :
    ¬ (4 : ℤ) * 4 ∣ lqKindD_val 7 (by norm_num) (Equiv.swap 5 6) 1 ∧
    ¬ (4 : ℤ) * 4 ∣ lqKindD_val 7 (by norm_num) 1 (-1) := by
  decide +kernel

private theorem lqKindD_val_eight :
    ¬ (2 : ℤ) * 2 ∣ lqKindD_val 8 (by norm_num) (Equiv.swap 6 7) 1 ∧
    ¬ (2 : ℤ) * 2 ∣ lqKindD_val 8 (by norm_num) (Equiv.swap 6 7) (-1) := by
  decide +kernel

private theorem lqKindD_val_four (q : Equiv.Perm (Fin 4))
    (hpres : ∀ i j : Fin 4, lqKindD_cartan 4 (q i) (q j) = lqKindD_cartan 4 i j)
    (hq : q ≠ 1) :
    ¬ (2 : ℤ) * 2 ∣ lqKindD_val 4 (by norm_num) q 1 ∧
    ¬ (2 : ℤ) * 2 ∣ lqKindD_val 4 (by norm_num) q (-1) := by
  revert q
  decide +kernel

private theorem lqKindD_cube_four (q : Equiv.Perm (Fin 4))
    (h : ∀ i j : Fin 4, lqKindD_cartan 4 (q i) (q j) = lqKindD_cartan 4 i j) :
    q ^ 2 = 1 ∨ q ^ 3 = 1 := by
  revert q
  decide +kernel

private theorem lqKindD_shape_notF4 (T : GGKacType) (c : List ℕ)
    (hD : (k0CompType (k0DiagOf T) c).1 = .D) (h4 : 4 ≤ c.length)
    (hc : c ∈ lqKindD_shapes T) : T ≠ .F4 := by
  rintro rfl
  simp [lqKindD_shapes] at hc

private theorem lqKindD_shape_len_le (T : GGKacType) (c : List ℕ)
    (hc : c ∈ lqKindD_shapes T) : c.length ≤ 8 := by
  cases T
  · simp [lqKindD_shapes] at hc; rcases hc with rfl | rfl | rfl | rfl <;> simp
  · simp [lqKindD_shapes] at hc; rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [lqKindD_shapes] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [lqKindD_shapes] at hc

private theorem lqKindD_autOrder_go_succ (c rk : List ℕ) (o : ℕ) (cur : List ℕ) (fuel : ℕ) :
    k0AutOrder.go c rk o cur (fuel + 1) =
      if c.all (fun i => decide (cur.getD i 0 = i)) then o
      else k0AutOrder.go c rk (o + 1) (k0pMul rk cur) fuel := rfl

private theorem lqKindD_autOrder_go_ge (c rk : List ℕ) (o : ℕ) (cur : List ℕ) (fuel : ℕ) :
    o ≤ k0AutOrder.go c rk o cur fuel := by
  induction fuel generalizing o cur with
  | zero => simp [k0AutOrder.go]
  | succ fuel ih =>
      rw [lqKindD_autOrder_go_succ]
      split_ifs with h
      · exact le_rfl
      · exact le_trans (Nat.le_succ o) (ih (o + 1) (k0pMul rk cur))

private theorem lqKindD_autOrder_go_fix (c rk : List ℕ) (o : ℕ) (cur : List ℕ) (fuel : ℕ)
    (h : k0AutOrder.go c rk o cur (fuel + 1) = o) :
    c.all (fun i => decide (cur.getD i 0 = i)) = true := by
  rw [lqKindD_autOrder_go_succ] at h
  split_ifs at h with hall
  · exact hall
  · exact absurd (lqKindD_autOrder_go_ge c rk (o + 1) (k0pMul rk cur) fuel) (by omega)

private theorem lqKindD_autOrder_one_fix (c rk : List ℕ) (h : k0AutOrder c rk = 1) :
    ∀ i ∈ c, rk.getD i 0 = i := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl] at h
  have hall := lqKindD_autOrder_go_fix c rk 1 rk c.length h
  rw [List.all_eq_true] at hall
  intro i hi
  exact of_decide_eq_true (hall i hi)

private theorem lqKindD_autOrder_two_fix (c rk : List ℕ) (h1 : 1 ≤ c.length)
    (h : k0AutOrder c rk = 2) :
    ∀ i ∈ c, (k0pMul rk rk).getD i 0 = i := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl] at h
  rw [lqKindD_autOrder_go_succ] at h
  split_ifs at h with hc
  · omega
  have hcl : c.length = (c.length - 1) + 1 := by omega
  rw [hcl] at h
  have hall := lqKindD_autOrder_go_fix c rk 2 (k0pMul rk rk) (c.length - 1) h
  rw [List.all_eq_true] at hall
  intro i hi
  exact of_decide_eq_true (hall i hi)

private theorem lqKindD_autOrder_three_fix (c rk : List ℕ) (h2 : 2 ≤ c.length)
    (h : k0AutOrder c rk = 3) :
    (∀ i ∈ c, (k0pMul rk (k0pMul rk rk)).getD i 0 = i) ∧
    (∃ i ∈ c, rk.getD i 0 ≠ i) ∧ (∃ i ∈ c, (k0pMul rk rk).getD i 0 ≠ i) := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl] at h
  rw [lqKindD_autOrder_go_succ] at h
  split_ifs at h with h1
  · omega
  have hnot1 : c.all (fun i => decide (rk.getD i 0 = i)) = false := by
    cases hb : c.all (fun i => decide (rk.getD i 0 = i)) with
    | false => rfl
    | true => exact absurd hb h1
  have h2' : c.length = (c.length - 1) + 1 := by omega
  rw [h2'] at h
  rw [lqKindD_autOrder_go_succ] at h
  split_ifs at h with h2a
  · omega
  have hnot2 : c.all (fun i => decide ((k0pMul rk rk).getD i 0 = i)) = false := by
    cases hb : c.all (fun i => decide ((k0pMul rk rk).getD i 0 = i)) with
    | false => rfl
    | true => exact absurd hb h2a
  have h3' : c.length - 1 = (c.length - 2) + 1 := by omega
  rw [h3'] at h
  have hall := lqKindD_autOrder_go_fix c rk 3 (k0pMul rk (k0pMul rk rk)) (c.length - 2) h
  rw [List.all_eq_true] at hall
  refine ⟨fun i hi => of_decide_eq_true (hall i hi), ?_, ?_⟩
  · rw [List.all_eq_false] at hnot1
    obtain ⟨i, hi, hne⟩ := hnot1
    exact ⟨i, hi, by simpa using hne⟩
  · rw [List.all_eq_false] at hnot2
    obtain ⟨i, hi, hne⟩ := hnot2
    exact ⟨i, hi, by simpa using hne⟩

private theorem lqKindD_autOrder_le_two (c rk : List ℕ) (h2 : 2 ≤ c.length)
    (hfix2 : ∀ i ∈ c, (k0pMul rk rk).getD i 0 = i) : k0AutOrder c rk ≤ 2 := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl]
  rw [lqKindD_autOrder_go_succ]
  split_ifs with h1
  · omega
  rw [show c.length = (c.length - 1) + 1 from by omega]
  rw [lqKindD_autOrder_go_succ]
  split_ifs with h2'
  · omega
  · exfalso
    apply h2'
    rw [List.all_eq_true]
    intro i hi
    exact decide_eq_true (hfix2 i hi)

private theorem lqKindD_autOrder_le_three (c rk : List ℕ) (h3 : 3 ≤ c.length)
    (hfix3 : ∀ i ∈ c, (k0pMul rk (k0pMul rk rk)).getD i 0 = i) : k0AutOrder c rk ≤ 3 := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl]
  rw [lqKindD_autOrder_go_succ]
  split_ifs with h1
  · omega
  rw [show c.length = (c.length - 1) + 1 from by omega]
  rw [lqKindD_autOrder_go_succ]
  split_ifs with h2
  · omega
  rw [show c.length - 1 = (c.length - 2) + 1 from by omega]
  rw [lqKindD_autOrder_go_succ]
  split_ifs with h3'
  · omega
  · exfalso
    apply h3'
    rw [List.all_eq_true]
    intro i hi
    exact decide_eq_true (hfix3 i hi)

private theorem lqKindD_k0pMul_length (a b : List ℕ) : (k0pMul a b).length = b.length := by
  simp [k0pMul]

private theorem lqKindD_swapLeaf_mul (r : ℕ) (hr : 2 ≤ r) :
    lqKindD_swapLeaf r * lqKindD_swapLeaf r = 1 := by
  ext x
  rw [lqKindD_swapLeaf, dif_pos hr]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases eq_or_ne x ⟨r - 2, by omega⟩ with hx | hx
  · subst hx
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rcases eq_or_ne x ⟨r - 1, by omega⟩ with hy | hy
    · subst hy
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
    · have hxx : Equiv.swap (⟨r - 2, by omega⟩ : Fin r) ⟨r - 1, by omega⟩ x = x := by
        rw [Equiv.swap_apply_def]
        simp [hx, hy]
      rw [hxx, hxx]

private theorem lqKindD_swapLeaf_ne_one (r : ℕ) (hr : 3 ≤ r) :
    lqKindD_swapLeaf r ≠ 1 := by
  intro h
  have h2 : 2 ≤ r := by omega
  rw [lqKindD_swapLeaf, dif_pos h2] at h
  have ha : Equiv.swap (⟨r - 2, by omega⟩ : Fin r) ⟨r - 1, by omega⟩
      (⟨r - 2, by omega⟩ : Fin r) = ⟨r - 1, by omega⟩ := Equiv.swap_apply_left _ _
  rw [h] at ha
  exact absurd (congrArg Fin.val ha) (by simp; omega)

private theorem lqKindD_swapLeaf_five : lqKindD_swapLeaf 5 = Equiv.swap 3 4 := by
  decide +kernel

private theorem lqKindD_swapLeaf_six : lqKindD_swapLeaf 6 = Equiv.swap 4 5 := by
  decide +kernel

private theorem lqKindD_swapLeaf_seven : lqKindD_swapLeaf 7 = Equiv.swap 5 6 := by
  decide +kernel

private theorem lqKindD_swapLeaf_eight : lqKindD_swapLeaf 8 = Equiv.swap 6 7 := by
  decide +kernel

private theorem lqKindD_even_data (r : ℕ) (hr0 : 0 < r) (h4 : 4 ≤ r) (h8 : r ≤ 8)
    (heven : r % 2 = 0) (q : Equiv.Perm (Fin r))
    (hq : ∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j)
    (hq1 : q ≠ 1) :
    (∀ j : Fin r, (2 : ℤ) ∣ ∑ i, lqKindD_mvec r hr0 q i * lqKindD_cartan r i j) ∧
      ¬ (2 : ℤ) * 2 ∣ lqKindD_val r hr0 q (-1) ∧
      ¬ (2 : ℤ) * 2 ∣ lqKindD_val r hr0 q 1 := by
  interval_cases r
  · exact ⟨lqKindD_dvd_four q, (lqKindD_val_four q hq hq1).2, (lqKindD_val_four q hq hq1).1⟩
  · exact absurd heven (by norm_num)
  · rcases lqKindD_perm_cases 6 (by norm_num) (by norm_num) q hq with h | h
    · exact absurd h hq1
    · subst h
      rw [lqKindD_swapLeaf_six]
      exact ⟨lqKindD_dvd_six _ (Or.inr rfl), lqKindD_val_six.2, lqKindD_val_six.1⟩
  · exact absurd heven (by norm_num)
  · rcases lqKindD_perm_cases 8 (by norm_num) (by norm_num) q hq with h | h
    · exact absurd h hq1
    · subst h
      rw [lqKindD_swapLeaf_eight]
      exact ⟨lqKindD_dvd_eight _ (Or.inr rfl), lqKindD_val_eight.2, lqKindD_val_eight.1⟩

private theorem lqKindD_odd_data (r : ℕ) (hr0 : 0 < r) (h5 : 5 ≤ r) (h8 : r ≤ 8)
    (hodd : r % 2 = 1) (q : Equiv.Perm (Fin r))
    (hq : ∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j) :
    (q = 1 ∨ q = lqKindD_swapLeaf r) ∧
      (∀ j : Fin r, (4 : ℤ) ∣ ∑ i, lqKindD_mvec r hr0 q i * lqKindD_cartan r i j) ∧
      (q = 1 → ¬ (4 : ℤ) * 4 ∣ lqKindD_val r hr0 q (-1)) ∧
      (q = lqKindD_swapLeaf r → ¬ (4 : ℤ) * 4 ∣ lqKindD_val r hr0 q 1) := by
  interval_cases r
  · have hc := lqKindD_perm_cases 5 (by norm_num) (by norm_num) q hq
    refine ⟨hc, ?_, ?_, ?_⟩
    · rcases hc with rfl | rfl
      · exact lqKindD_dvd_five 1 (Or.inl rfl)
      · rw [lqKindD_swapLeaf_five]
        exact lqKindD_dvd_five _ (Or.inr rfl)
    · intro hq1
      subst hq1
      exact lqKindD_val_five.2
    · intro hsw
      rw [hsw, lqKindD_swapLeaf_five]
      exact lqKindD_val_five.1
  · exact absurd hodd (by norm_num)
  · have hc := lqKindD_perm_cases 7 (by norm_num) (by norm_num) q hq
    refine ⟨hc, ?_, ?_, ?_⟩
    · rcases hc with rfl | rfl
      · exact lqKindD_dvd_seven 1 (Or.inl rfl)
      · rw [lqKindD_swapLeaf_seven]
        exact lqKindD_dvd_seven _ (Or.inr rfl)
    · intro hq1
      subst hq1
      exact lqKindD_val_seven.2
    · intro hsw
      rw [hsw, lqKindD_swapLeaf_seven]
      exact lqKindD_val_seven.1
  · exact absurd hodd (by norm_num)

private theorem lqKindD_four_data (r : ℕ) (hr0 : 0 < r) (hr4 : r = 4)
    (q : Equiv.Perm (Fin r))
    (hq : ∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j) (hq1 : q ≠ 1) :
    (∀ j : Fin r, (2 : ℤ) ∣ ∑ i, lqKindD_mvec r hr0 q i * lqKindD_cartan r i j) ∧
      ¬ (2 : ℤ) * 2 ∣ lqKindD_val r hr0 q 1 := by
  subst hr4
  exact ⟨lqKindD_dvd_four q, (lqKindD_val_four q hq hq1).1⟩

private theorem lqKindD_four_order (r : ℕ) (hr4 : r = 4) (q : Equiv.Perm (Fin r))
    (hq : ∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j) :
    q * q = 1 ∨ q * q * q = 1 := by
  subst hr4
  rcases lqKindD_cube_four q hq with h | h
  · left; simpa [pow_two] using h
  · right; simpa [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] using h

private theorem lqKindD_val_of_action {r : ℕ} (hr : 0 < r)
    {τ : Tag} {α : Fin r → (Fin τ.rank → ℤ)}
    (hpair : ∀ i j, iform (α i) (α j) = lqKindD_cartan r i j)
    {q : Equiv.Perm (Fin r)} {e' : ℤ}
    (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hf : ∀ i, f (α i) = e' • α (q i)) :
    iform (∑ i, lqKindD_mvec r hr q i • α i)
        (f (∑ i, lqKindD_mvec r hr q i • α i) - ∑ i, lqKindD_mvec r hr q i • α i) =
      lqKindD_val r hr q e' := by
  classical
  have hpairμ : ∀ j : Fin r,
      iform (∑ i, lqKindD_mvec r hr q i • α i) (α j) =
        ∑ i, lqKindD_mvec r hr q i * lqKindD_cartan r i j := by
    intro j
    rw [iform_finset_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_left, hpair i j]
  have hfμ : f (∑ i, lqKindD_mvec r hr q i • α i) =
      e' • ∑ j, lqKindD_mvec r hr q j • α (q j) := by
    rw [show f (∑ i, lqKindD_mvec r hr q i • α i) =
        ∑ i, f (lqKindD_mvec r hr q i • α i) from
      map_sum f (fun i => lqKindD_mvec r hr q i • α i) Finset.univ]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hf i, smul_comm]
  have hμμ : iform (∑ i, lqKindD_mvec r hr q i • α i)
      (∑ i, lqKindD_mvec r hr q i • α i) = ∑ i, lqKindD_mvec r hr q i *
        (∑ j, lqKindD_mvec r hr q j * lqKindD_cartan r i j) := by
    rw [iform_finset_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_left, iform_finset_sum_right]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iform_smul_right, hpair i j]
  have hfμμ : iform (∑ i, lqKindD_mvec r hr q i • α i)
      (f (∑ i, lqKindD_mvec r hr q i • α i)) = e' * ∑ i, lqKindD_mvec r hr q i *
        (∑ j, lqKindD_mvec r hr q j * lqKindD_cartan r i (q j)) := by
    rw [hfμ, iform_smul_right]
    congr 1
    rw [iform_finset_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_left, iform_finset_sum_right]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iform_smul_right, hpair i (q j)]
  have hreindex : ∀ i : Fin r,
      (∑ j, lqKindD_mvec r hr q j * lqKindD_cartan r i (q j)) =
        ∑ j, lqKindD_mvec r hr q (q.symm j) * lqKindD_cartan r i j := by
    intro i
    refine Fintype.sum_equiv q
      (fun j => lqKindD_mvec r hr q j * lqKindD_cartan r i (q j))
      (fun j => lqKindD_mvec r hr q (q.symm j) * lqKindD_cartan r i j) ?_
    intro j
    rw [Equiv.symm_apply_apply]
  have hA : (∑ i, lqKindD_mvec r hr q i *
        (∑ j, lqKindD_mvec r hr q j * lqKindD_cartan r i (q j))) =
      ∑ i, lqKindD_mvec r hr q i *
        (∑ j, lqKindD_mvec r hr q (q.symm j) * lqKindD_cartan r i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hreindex i]
  rw [iform_sub_right, hfμμ, hμμ, hA, lqKindD_val]
  simp only [Finset.mul_sum, mul_assoc]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem lqKindD_mu_dvd {r : ℕ} (hr : 0 < r)
    {τ : Tag} {α : Fin r → (Fin τ.rank → ℤ)}
    (hpair : ∀ i j, iform (α i) (α j) = lqKindD_cartan r i j)
    {q : Equiv.Perm (Fin r)} {d : ℤ}
    (hdiv : ∀ j : Fin r, d ∣ ∑ i, lqKindD_mvec r hr q i * lqKindD_cartan r i j) :
    ∀ γ ∈ Submodule.span ℤ (Set.range α),
      d ∣ iform (∑ i, lqKindD_mvec r hr q i • α i) γ := by
  classical
  intro γ hγ
  have hpairμ : ∀ j : Fin r,
      iform (∑ i, lqKindD_mvec r hr q i • α i) (α j) =
        ∑ i, lqKindD_mvec r hr q i * lqKindD_cartan r i j := by
    intro j
    rw [iform_finset_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_left, hpair i j]
  refine Submodule.span_induction
    (p := fun γ _ => d ∣ iform (∑ i, lqKindD_mvec r hr q i • α i) γ) ?_ ?_ ?_ ?_ hγ
  · rintro y ⟨j, rfl⟩
    rw [hpairμ j]
    exact hdiv j
  · rw [show iform (∑ i, lqKindD_mvec r hr q i • α i) 0 = 0 by
      simpa using iform_smul_right (0 : ℤ) _ 0]
    exact dvd_zero d
  · intro a b _ _ ha hb
    rw [iform_add_right]
    exact dvd_add ha hb
  · intro n y _ hy
    rw [iform_smul_right]
    exact Dvd.dvd.mul_left hy n

private theorem lqKindD_outer_of_val {r : ℕ} (hr : 0 < r)
    {τ : Tag} {ψ : Set (Fin τ.rank → ℤ)} {α : Fin r → (Fin τ.rank → ℤ)}
    {d e' : ℤ} {q : Equiv.Perm (Fin r)}
    (hroot : ∀ γ ∈ ψ, IsRoot τ γ) (hsl : ∀ γ ∈ ψ, iform γ γ = 2)
    (hpair : ∀ i j, iform (α i) (α j) = lqKindD_cartan r i j)
    (hαψ : ∀ i, α i ∈ ψ)
    (hψspan : ∀ γ ∈ ψ, γ ∈ Submodule.span ℤ (Set.range α))
    (hdiv : ∀ j : Fin r, d ∣ ∑ i, lqKindD_mvec r hr q i * lqKindD_cartan r i j)
    (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hf : ∀ i, f (α i) = e' • α (q i))
    (hval : ¬ d * d ∣ lqKindD_val r hr q e') :
    ¬ twistInner ψ (f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) := by
  have hμd := lqKindD_mu_dvd hr hpair hdiv
  have hμspan : (∑ i, lqKindD_mvec r hr q i • α i) ∈ Submodule.span ℤ ψ := by
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (hαψ i)
  refine TableCRes.not_twistInner_of_disc hroot hsl f (d := d)
    (μ := ∑ i, lqKindD_mvec r hr q i • α i)
    (ν := ∑ i, lqKindD_mvec r hr q i • α i) hμspan ?_ ?_ ?_
  · intro γ hγ
    exact hμd γ (hψspan γ hγ)
  · intro γ hγ
    exact hμd γ (hψspan γ hγ)
  · rw [lqKindD_val_of_action hr hpair f hf]
    exact hval

private theorem lqKindD_inner_of_node_fix {r : ℕ} {τ : Tag} {ψ : Set (Fin τ.rank → ℤ)}
    {α : Fin r → (Fin τ.rank → ℤ)}
    (hψspan : ∀ γ ∈ ψ, γ ∈ Submodule.span ℤ (Set.range α))
    (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (φ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hσφ : ∀ γ ∈ ψ, σ γ = φ γ)
    (hφ : ∀ i, φ (α i) = α i) :
    twistInner ψ σ := by
  refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
  have hfix : ∀ z ∈ Submodule.span ℤ (Set.range α), φ z = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => φ z = z) ?_ ?_ ?_ ?_ hz
    · rintro y ⟨i, rfl⟩
      exact hφ i
    · simp
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro n y _ hy
      rw [map_zsmul, hy]
  rw [hσφ γ hγ, hfix γ (hψspan γ hγ)]
  simp

private theorem lqKindD_inner_neg_even {τ : Tag} {r : ℕ} (hr0 : 0 < r) (h4 : 4 ≤ r)
    {ψ : Set (Fin τ.rank → ℤ)} {α : Fin r → (Fin τ.rank → ℤ)}
    (hψeq : ∀ v, v ∈ ψ ↔ IsRoot τ v ∧ v ∈ Submodule.span ℤ (Set.range α))
    (hroot : ∀ i, IsRoot τ (α i))
    (hsl : ∀ γ ∈ ψ, iform γ γ = 2)
    (hpair : ∀ i j, iform (α i) (α j) = lqKindD_cartan r i j)
    (hind : LinearIndependent ℚ (fun i => fun j => ((α i j : ℤ) : ℚ)))
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v → v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : Fin r → ℕ, v = ∑ i, (n i : ℤ) • α i) ∨
      (∃ n : Fin r → ℕ, v = -∑ i, (n i : ℤ) • α i))
    (hdat : ∀ q : Equiv.Perm (Fin r),
      (∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j) → q ≠ 1 →
      (∀ j : Fin r, (2 : ℤ) ∣ ∑ i, lqKindD_mvec r hr0 q i * lqKindD_cartan r i j) ∧
        ¬ (2 : ℤ) * 2 ∣ lqKindD_val r hr0 q (-1))
    (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (φ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hσφ : ∀ γ ∈ ψ, σ γ = φ γ)
    (hφneg : ∀ i, φ (α i) = -α i) :
    twistInner ψ σ := by
  classical
  have hrootψ : ∀ γ ∈ ψ, IsRoot τ γ := fun γ hγ => (hψeq γ).mp hγ |>.1
  have hψspan : ∀ γ ∈ ψ, γ ∈ Submodule.span ℤ (Set.range α) :=
    fun γ hγ => (hψeq γ).mp hγ |>.2
  obtain ⟨w, hw, opp, hwα⟩ := lq_longest (τ := τ) (α := α) hroot hind hcone
  have hclosure_sub : Subgroup.closure {s : WeylGroup τ | ∃ γ : Fin τ.rank → ℤ,
      IsRoot τ γ ∧ γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ} ≤
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ ψ, s = rootReflection γ} := by
    apply Subgroup.closure_mono
    rintro s ⟨γ, hγroot, hγspan, rfl⟩
    exact ⟨γ, (hψeq γ).mpr ⟨hγroot, hγspan⟩, rfl⟩
  have hopp_cartan : ∀ i j : Fin r,
      lqKindD_cartan r (opp i) (opp j) = lqKindD_cartan r i j := by
    intro i j
    have h := iform_smul w (α i) (α j)
    rw [hwα i, hwα j] at h
    rw [show -α (opp i) = (-1 : ℤ) • α (opp i) from by simp,
      show -α (opp j) = (-1 : ℤ) • α (opp j) from by simp,
      iform_smul_left, iform_smul_right] at h
    have h' : iform (α (opp i)) (α (opp j)) = iform (α i) (α j) := by linarith
    rw [hpair (opp i) (opp j), hpair i j] at h'
    exact h'
  have hφneg' : ∀ z ∈ Submodule.span ℤ (Set.range α), φ z = -z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => φ z = -z) ?_ ?_ ?_ ?_ hz
    · rintro y ⟨i, rfl⟩
      exact hφneg i
    · simp
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]; abel
    · intro n y _ hy
      rw [map_zsmul, hy, smul_neg]
  by_cases hopp1 : opp = 1
  · have hwneg : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = -z := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => w • z = -z) ?_ ?_ ?_ ?_ hz
      · rintro y ⟨i, rfl⟩
        rw [hwα i, hopp1]
        simp
      · simp
      · intro a b _ _ ha hb
        rw [smul_add, ha, hb]; abel
      · intro n y _ hy
        rw [show w • (n • y) = n • (w • y) from (smul_comm (n : ℤ) w y).symm, hy, smul_neg]
    refine ⟨w, hclosure_sub hw, fun γ hγ => ?_⟩
    rw [hσφ γ hγ, hφneg' γ (hψspan γ hγ), hwneg γ (hψspan γ hγ)]
  · exfalso
    obtain ⟨hdvd, hval⟩ := hdat opp hopp_cartan hopp1
    let f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
      { toFun := fun z => w • z
        map_zero' := smul_zero w
        map_add' := fun a b => smul_add w a b }
    have hf : ∀ i, f (α i) = (-1 : ℤ) • α (opp i) := by
      intro i
      change w • α i = (-1 : ℤ) • α (opp i)
      rw [hwα i, neg_one_smul]
    have hnot := lqKindD_outer_of_val hr0 hrootψ hsl hpair
      (fun i => (hψeq (α i)).mpr ⟨hroot i, Submodule.subset_span (Set.mem_range_self i)⟩)
      hψspan hdvd f hf hval
    exact hnot ⟨w, hclosure_sub hw, fun γ _ => rfl⟩

private theorem lqKindD_inner_neg_odd {τ : Tag} {r : ℕ}
    {ψ : Set (Fin τ.rank → ℤ)} {α : Fin r → (Fin τ.rank → ℤ)}
    (hψeq : ∀ v, v ∈ ψ ↔ IsRoot τ v ∧ v ∈ Submodule.span ℤ (Set.range α))
    (hroot : ∀ i, IsRoot τ (α i))
    (hpair : ∀ i j, iform (α i) (α j) = lqKindD_cartan r i j)
    (hind : LinearIndependent ℚ (fun i => fun j => ((α i j : ℤ) : ℚ)))
    (hcone : ∀ v : Fin τ.rank → ℤ, IsRoot τ v → v ∈ Submodule.span ℤ (Set.range α) →
      (∃ n : Fin r → ℕ, v = ∑ i, (n i : ℤ) • α i) ∨
      (∃ n : Fin r → ℕ, v = -∑ i, (n i : ℤ) • α i))
    (qq : Equiv.Perm (Fin r))
    (hclass : ∀ q : Equiv.Perm (Fin r),
      (∀ i j : Fin r, lqKindD_cartan r (q i) (q j) = lqKindD_cartan r i j) → q = 1 ∨ q = qq)
    (hnotInnerNeg : ¬ twistInner ψ (fun z => -z))
    (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (φ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hσφ : ∀ γ ∈ ψ, σ γ = φ γ)
    (hφneg : ∀ i, φ (α i) = -α (qq i)) :
    twistInner ψ σ := by
  classical
  have hrootψ : ∀ γ ∈ ψ, IsRoot τ γ := fun γ hγ => (hψeq γ).mp hγ |>.1
  have hψspan : ∀ γ ∈ ψ, γ ∈ Submodule.span ℤ (Set.range α) :=
    fun γ hγ => (hψeq γ).mp hγ |>.2
  obtain ⟨w, hw, opp, hwα⟩ := lq_longest (τ := τ) (α := α) hroot hind hcone
  have hclosure_sub : Subgroup.closure {s : WeylGroup τ | ∃ γ : Fin τ.rank → ℤ,
      IsRoot τ γ ∧ γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ} ≤
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ ψ, s = rootReflection γ} := by
    apply Subgroup.closure_mono
    rintro s ⟨γ, hγroot, hγspan, rfl⟩
    exact ⟨γ, (hψeq γ).mpr ⟨hγroot, hγspan⟩, rfl⟩
  have hopp_cartan : ∀ i j : Fin r,
      lqKindD_cartan r (opp i) (opp j) = lqKindD_cartan r i j := by
    intro i j
    have h := iform_smul w (α i) (α j)
    rw [hwα i, hwα j] at h
    rw [show -α (opp i) = (-1 : ℤ) • α (opp i) from by simp,
      show -α (opp j) = (-1 : ℤ) • α (opp j) from by simp,
      iform_smul_left, iform_smul_right] at h
    have h' : iform (α (opp i)) (α (opp j)) = iform (α i) (α j) := by linarith
    rw [hpair (opp i) (opp j), hpair i j] at h'
    exact h'
  rcases hclass opp hopp_cartan with hopp1 | hoppq
  · exfalso
    apply hnotInnerNeg
    have hwneg : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = -z := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => w • z = -z) ?_ ?_ ?_ ?_ hz
      · rintro y ⟨i, rfl⟩
        rw [hwα i, hopp1]
        simp
      · simp
      · intro a b _ _ ha hb
        rw [smul_add, ha, hb]; abel
      · intro n y _ hy
        rw [show w • (n • y) = n • (w • y) from (smul_comm (n : ℤ) w y).symm, hy, smul_neg]
    refine (lqKindD_twistInner_congr (σ := fun z => -z) (σ' := fun z => w • z) ?_).mpr ?_
    · intro γ hγ
      rw [hwneg γ (hψspan γ hγ)]
    · exact ⟨w, hclosure_sub hw, fun γ _ => rfl⟩
  · have hwφ : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = φ z := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => w • z = φ z) ?_ ?_ ?_ ?_ hz
      · rintro y ⟨i, rfl⟩
        rw [hwα i, hoppq, hφneg i]
      · simp
      · intro a b _ _ ha hb
        rw [smul_add, ha, hb, map_add]
      · intro n y _ hy
        rw [show w • (n • y) = n • (w • y) from (smul_comm (n : ℤ) w y).symm, hy, map_zsmul]
    refine ⟨w, hclosure_sub hw, fun γ hγ => ?_⟩
    rw [hσφ γ hγ, ← hwφ γ (hψspan γ hγ)]

theorem lq_kind_D (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h4 : 4 ≤ (lqNodes A P j).length)
    (hD : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .D)
    (hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      2 * (lqNodes A P j).length * ((lqNodes A P j).length - 1)) :
    (lqTw A P j = 1 → twistInner (componentRoots (rootCharHom A.a) (P.repr j))
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[componentOrbitLength A.setup.ρ
        (componentRoots (rootCharHom A.a) (P.repr j))])) ∧
    (lqTw A P j = 2 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .twoD) ∧
    (3 ≤ lqTw A P j → (lqNodes A P j).length = 4 ∧
      twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .exc) := by
  classical
  set T := A.row.T with hT
  set c := lqNodes A P j with hc
  set s := (P.orbitNodes j).length with hs
  set ψ := componentRoots (rootCharHom A.a) (P.repr j) with hψ
  have h4' : 4 ≤ c.length := by simpa [hc] using h4
  have hnb := lq_nodes_basic A P j
  have hnd : c.Nodup := by simpa [hc] using hnb.2.1
  have hxlt : ∀ x ∈ c, x < A.row.diagram.marks.length := fun x hx =>
    lqKindD_lt_marks A ((hnb.2.2 x (by simpa [hc] using hx)).1)
  have hproper : ∃ i < A.row.diagram.marks.length, i ∉ c := by
    obtain ⟨i, hi, hni⟩ := lqKindD_nodes_proper A P j
    exact ⟨i, by simpa [hT] using hi, by simpa [hc] using hni⟩
  set zero := ((List.range (k0DiagOf T).marks.length).filter
    (fun i => decide (A.row.s.getD i 0 = 0))) with hzero
  have hzsub : zero.Sublist (List.range (k0DiagOf T).marks.length) := by
    rw [hzero]; exact List.filter_sublist
  have hzproper : zero.length < (k0DiagOf T).marks.length := by
    have hle : zero.length ≤ (k0DiagOf T).marks.length := by
      simpa [hzero] using List.length_filter_le (fun i => decide (A.row.s.getD i 0 = 0))
        (List.range (k0DiagOf T).marks.length)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have heq : zero = List.range (k0DiagOf T).marks.length :=
        List.Sublist.eq_of_length hzsub (by rw [h, List.length_range])
      have hall : ∀ i : Fin (k0DiagOf T).marks.length, A.row.s.getD i.val 0 = 0 := by
        intro i
        have hi : i.val ∈ zero := by rw [heq]; exact List.mem_range.mpr i.isLt
        rw [hzero, List.mem_filter] at hi
        exact of_decide_eq_true hi.2
      have h0 : (∑ i : Fin (k0DiagOf T).marks.length,
          (k0DiagOf T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hall i, mul_zero]
      have hsum := ggKacShVecs_sum (k0DiagOf T).marks p A.row.s A.row.s_mem
      rw [h0] at hsum
      have hp := lqKindD_p_pos A
      omega
  have hmem : c ∈ k0Comps (k0DiagOf T) zero := by
    have := lq_nodes_mem_comps A P j
    simpa [hT, hc, hzero, lqNodes] using this
  have hcD : (k0CompType (k0DiagOf T) c).1 = .D := by simpa [hT, hc] using hD
  have hcShape : c ∈ lqKindD_shapes T :=
    lqKindD_shape_mem T zero (List.mem_sublists.mpr hzsub) c hmem hcD h4'
  have hTne : T ≠ .F4 := lqKindD_shape_notF4 T c hcD h4' hcShape
  have hr8 : c.length ≤ 8 := lqKindD_shape_len_le T c hcShape
  have hpathOK : lqKindD_pathOK T c :=
    of_decide_eq_true (lqKindD_pathOK_table T hTne zero (List.mem_sublists.mpr hzsub)
      c hmem hcD h4')
  obtain ⟨hp_len, hp_nd, hp_fs, hmat, hgap⟩ := hpathOK
  set pth := lqKindD_path c with hpth
  have hpth_len : pth.length = c.length := hp_len
  have hpth_nd : pth.Nodup := hp_nd
  have hpth_fs : pth.toFinset = c.toFinset := hp_fs
  have hgap' : c.length + 1 = A.row.diagram.marks.length →
      ∀ w < A.row.diagram.marks.length, w ∉ c → 1 < A.row.diagram.marks.getD w 0 := hgap
  let pathAt : Fin c.length → ℕ := fun i => pth.getD i.val 0
  have hpathAt_get : ∀ i : Fin c.length, pathAt i =
      pth.get ⟨i.val, by rw [hpth_len]; exact i.isLt⟩ := fun i =>
    List.getD_eq_getElem _ _ (by rw [hpth_len]; exact i.isLt)
  have hpathAt_mem : ∀ i : Fin c.length, pathAt i ∈ c := by
    intro i
    have h1 : pathAt i ∈ pth.toFinset := by
      rw [List.mem_toFinset]
      rw [hpathAt_get i]
      exact List.get_mem _ _
    rw [hpth_fs] at h1
    exact List.mem_toFinset.mp h1
  have hpathAt_inj : Function.Injective pathAt := by
    intro i j hij
    have h1 : pth.get ⟨i.val, by rw [hpth_len]; exact i.isLt⟩ =
        pth.get ⟨j.val, by rw [hpth_len]; exact j.isLt⟩ := by
      rw [← hpathAt_get i, ← hpathAt_get j, hij]
    have h2 := (List.Nodup.get_inj_iff hpth_nd).mp h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  let efun : Fin c.length → {x // x ∈ c} := fun i => ⟨pathAt i, hpathAt_mem i⟩
  have he_inj : Function.Injective efun := fun i j h => hpathAt_inj (congrArg Subtype.val h)
  have he_surj : Function.Surjective efun := by
    intro x
    have hx : x.1 ∈ pth := by
      have h1 : x.1 ∈ pth.toFinset := by rw [hpth_fs]; exact List.mem_toFinset.mpr x.2
      exact List.mem_toFinset.mp h1
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx
    refine ⟨⟨n.val, by omega⟩, ?_⟩
    refine Subtype.ext ?_
    change pathAt ⟨n.val, by omega⟩ = x.1
    rw [hpathAt_get]
    exact hn
  let e : Fin c.length ≃ {x // x ∈ c} := Equiv.ofBijective efun ⟨he_inj, he_surj⟩
  have he_val : ∀ i, (e i).val = pathAt i := fun i => rfl
  let ι : {x // x ∈ c} → Fin A.row.diagram.marks.length := fun x => ⟨x.1, hxlt x.1 x.2⟩
  let α : {x // x ∈ c} → (Fin A.tau.rank → ℤ) := fun x => A.nodeMap (Pi.single (ι x) 1)
  have hα_node : ∀ x : {x // x ∈ c}, α x = lqExtRoot A.tau T x.1 := fun x => lq_nodeMap_eq A (ι x)
  have hα_path : ∀ i : Fin c.length, α (e i) = lqExtRoot A.tau T (pathAt i) := by
    intro i
    rw [hα_node, he_val]
  have hαroot : ∀ x : {x // x ∈ c}, IsRoot A.tau (α x) := fun x => A.node_isRoot (ι x)
  have hLIα : LinearIndependent ℚ (fun x : {x // x ∈ c} =>
      fun k => ((α x k : ℤ) : ℚ)) := by
    have h := lq_extRoot_independent A.tau T (by rw [hT]; exact A.tau_eq) c hnd
      (by simpa [hT] using hxlt) (by simpa [hT] using hproper)
    simpa [hα_node] using h
  have hψeq : ψ = {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ (Set.range α)} := by
    rw [hψ, P.repr_roots j]
    change {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ
      {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
        w = A.nodeMap (Pi.single i 1)}} = _
    have hset : {v | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
        v = A.nodeMap (Pi.single i 1)} = Set.range α := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i.val, hi⟩, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨ι x, x.2, rfl⟩
    rw [hset]
  have hroots : ∀ γ ∈ ψ, IsRoot A.tau γ := fun γ hγ => (hψeq ▸ hγ).1
  have hspan_path : ∀ γ ∈ ψ, γ ∈ Submodule.span ℤ (Set.range α) :=
    fun γ hγ => (hψeq ▸ hγ).2
  have hcone := lqKindD_cone A P j hmem hzproper
  have hmaps : ∀ x : {x // x ∈ c}, (A.row.nodePerm^[s] (ι x)).val ∈ c := by
    rintro ⟨x, hx⟩
    have h := lqKindD_maps_c A P j hgap' s hs (x := x) (by simpa [hc] using hx)
    simpa [ι, hc] using h
  let ffun : {x // x ∈ c} → {x // x ∈ c} := fun x => ⟨(A.row.nodePerm^[s] (ι x)).val, hmaps x⟩
  have hfinj : Function.Injective ffun := by
    intro x y hxy
    have hv : (A.row.nodePerm^[s] (ι x)).val = (A.row.nodePerm^[s] (ι y)).val :=
      congrArg Subtype.val hxy
    have hfin : (A.row.nodePerm^[s] (ι x)) = (A.row.nodePerm^[s] (ι y)) := Fin.ext hv
    have h1 := (A.row.nodePerm.injective.iterate s) hfin
    exact Subtype.ext (congrArg Fin.val h1)
  let p : Equiv.Perm {x // x ∈ c} :=
    Equiv.ofBijective ffun (Finite.injective_iff_bijective.mp hfinj)
  have hpv : ∀ x, (p x).val = (A.row.nodePerm^[s] (ι x)).val := fun x => rfl
  let qfun : Fin c.length → Fin c.length := fun i => e.symm (p (e i))
  have hqinj : Function.Injective qfun := by
    intro i j hij
    have h1 : p (e i) = p (e j) := by
      have := congrArg e hij
      simpa [qfun] using this
    exact e.injective (p.injective h1)
  let q : Equiv.Perm (Fin c.length) :=
    Equiv.ofBijective qfun (Finite.injective_iff_bijective.mp hqinj)
  have hq_apply : ∀ i, e (q i) = p (e i) := fun i => e.apply_symm_apply _
  have hppair : ∀ x y : {x // x ∈ c}, iform (α (p x)) (α (p y)) = iform (α x) (α y) := by
    intro x y
    have hσx := lqKindD_frob_nodes_iterate A s (ι x)
    have hσy := lqKindD_frob_nodes_iterate A s (ι y)
    have hes : A.epsilon ^ s = 1 ∨ A.epsilon ^ s = -1 := by
      have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by
        rw [A.epsilon_eq]; split <;> simp
      rcases hε with hε | hε
      · exact Or.inl (by rw [hε, one_pow])
      · rcases Nat.even_or_odd s with he | ho
        · exact Or.inl (by rw [hε]; exact he.neg_one_pow)
        · exact Or.inr (by rw [hε]; exact ho.neg_one_pow)
    have hnx : (A.row.nodePerm^[s] (ι x)) = ι (p x) := Fin.ext (by rw [← hpv x])
    have hny : (A.row.nodePerm^[s] (ι y)) = ι (p y) := Fin.ext (by rw [← hpv y])
    rw [hnx] at hσx
    rw [hny] at hσy
    change iform (A.nodeMap (Pi.single ((A.row.nodePerm^[s] (ι x))) 1))
      (A.nodeMap (Pi.single ((A.row.nodePerm^[s] (ι y))) 1)) = iform (α x) (α y)
    rw [hnx, hny]
    rcases hes with h | h
    · rw [h, one_smul] at hσx hσy
      rw [← hσx, ← hσy]
      exact lqKindD_iform_iterate A.setup s _ _
    · rw [h, neg_one_smul] at hσx hσy
      have e1 : A.nodeMap (Pi.single (ι (p x)) 1) =
          -(((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (A.nodeMap (Pi.single (ι x) 1))) := by
        rw [hσx]; simp
      have e2 : A.nodeMap (Pi.single (ι (p y)) 1) =
          -(((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (A.nodeMap (Pi.single (ι y) 1))) := by
        rw [hσy]; simp
      rw [e1, e2]
      have f1 : -(((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (A.nodeMap (Pi.single (ι x) 1))) =
          (-1 : ℤ) • ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s])
            (A.nodeMap (Pi.single (ι x) 1)) := by rw [neg_one_smul]
      have f2 : -(((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (A.nodeMap (Pi.single (ι y) 1))) =
          (-1 : ℤ) • ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s])
            (A.nodeMap (Pi.single (ι y) 1)) := by rw [neg_one_smul]
      rw [f1, f2, iform_smul_left, iform_smul_right, lqKindD_iform_iterate A.setup s]
      ring
  have hmat' : ∀ i j : Fin c.length,
      iform (α (e i)) (α (e j)) = lqKindD_cartan c.length i j := by
    intro i j
    rw [hα_path i, hα_path j]
    have hτ : absTag T = A.tau := A.tau_eq
    have h1 : iform (lqExtRoot A.tau T (pathAt i)) (lqExtRoot A.tau T (pathAt j)) =
        lqKindD_pairVal T (pathAt i) (pathAt j) := by
      have h := lqKindD_pair T hTne
        (⟨pathAt i, by simpa using hxlt (pathAt i) (hpathAt_mem i)⟩ :
          Fin (k0DiagOf T).marks.length)
        ⟨pathAt j, by simpa using hxlt (pathAt j) (hpathAt_mem j)⟩
      rw [hτ] at h
      simpa [lqKindD_pairVal, Fin.ext_iff] using h
    exact h1.trans (hmat i j)
  have hq_cartan : ∀ i j : Fin c.length,
      lqKindD_cartan c.length (q i) (q j) = lqKindD_cartan c.length i j := by
    intro i j
    have h1 : lqKindD_cartan c.length (q i) (q j) = iform (α (e (q i))) (α (e (q j))) :=
      (hmat' (q i) (q j)).symm
    have h2 : iform (α (e (q i))) (α (e (q j))) = iform (α (e i)) (α (e j)) := by
      simp only [hq_apply]
      exact hppair (e i) (e j)
    exact h1.trans (h2.trans (hmat' i j))
  have hcls : q = 1 ∨ (c.length = 4 ∧ q ≠ 1) ∨
      (5 ≤ c.length ∧ q = lqKindD_swapLeaf c.length) := by
    by_cases h5 : 5 ≤ c.length
    · rcases lqKindD_perm_cases c.length h5 hr8 q hq_cartan with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h5, h⟩)
    · have hr4 : c.length = 4 := by omega
      by_cases hq1 : q = 1
      · exact Or.inl hq1
      · exact Or.inr (Or.inl ⟨hr4, hq1⟩)
  have htaucases : A.tau = .E6 ∨ A.tau = .E7 ∨ A.tau = .E8 ∨ A.tau = .F4 := by
    cases hT' : A.row.T
    · exact Or.inl (by rw [← A.tau_eq, hT']; rfl)
    · exact Or.inr (Or.inl (by rw [← A.tau_eq, hT']; rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← A.tau_eq, hT']; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [← A.tau_eq, hT']; rfl)))
  have hsl : ∀ γ ∈ ψ, iform (τ := A.tau) γ γ = 2 := by
    intro γ hγ
    obtain ⟨k, hk⟩ := iform_self_of_isRoot (hroots γ hγ)
    have h1 : A.tau.symmetrizer k k = 1 := by
      rcases htaucases with h | h | h | h
      · exact lqKindD_symm_one (Or.inl h) k
      · exact lqKindD_symm_one (Or.inr (Or.inl h)) k
      · exact lqKindD_symm_one (Or.inr (Or.inr h)) k
      · exfalso
        have habs : absTag T = .F4 := by rw [hT, A.tau_eq]; exact h
        exact hTne (lqKindD_absTag_eq_F4 habs)
    rw [h1] at hk
    simpa using hk
  let φ : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ) :=
    ((A.frobLinear ^ s : (Fin A.tau.rank → ℤ) ≃ₗ[ℤ] (Fin A.tau.rank → ℤ)).toLinearMap
      ).toAddMonoidHom
  have hφρ : ∀ γ ∈ ψ, ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ = φ γ := by
    intro γ hγ
    rw [lqKindD_rho_iterate_frobLinear A s (hroots γ hγ)]
    exact (LinearEquiv.pow_apply A.frobLinear s γ).symm
  set el : ℤ := A.epsilon ^ s with hel
  have hel12 : el = 1 ∨ el = -1 := by
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
    rcases hε with hε | hε
    · exact Or.inl (by rw [hel, hε, one_pow])
    · rcases Nat.even_or_odd s with he | ho
      · exact Or.inl (by rw [hel, hε]; exact he.neg_one_pow)
      · exact Or.inr (by rw [hel, hε]; exact ho.neg_one_pow)
  have hel_d : el = (if A.row.d = 1 then (1 : ℤ) else -1) ^ s := by
    rw [hel, A.epsilon_eq]
  have hd12 : A.row.d = 1 ∨ A.row.d = 2 := by
    rw [A.row.d_eq]; split <;> simp
  have hσi : ∀ i : Fin c.length,
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) (α (e i)) =
        el • α (e (q i)) := by
    intro i
    have h := lqKindD_frob_nodes_iterate A s (ι (e i))
    have hnx : (A.row.nodePerm^[s] (ι (e i))) = ι (e (q i)) := by
      refine Fin.ext ?_
      rw [hq_apply i]
      exact (hpv (e i)).symm
    simpa [hel, hnx] using h
  have hαψ_e : ∀ i : Fin c.length, α (e i) ∈ ψ := by
    intro i
    rw [hψeq]
    exact ⟨A.node_isRoot (ι (e i)), Submodule.subset_span (Set.mem_range_self (e i))⟩
  have hφ_apply : ∀ i : Fin c.length, φ (α (e i)) = el • α (e (q i)) := by
    intro i
    rw [← hφρ (α (e i)) (hαψ_e i)]
    exact hσi i

  have hrange : Set.range (fun i : Fin c.length => α (e i)) = Set.range α := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by show α (e (e.symm x)) = α x; rw [e.apply_symm_apply]⟩
  have hroots_e : ∀ i : Fin c.length, IsRoot A.tau (α (e i)) := fun i => A.node_isRoot (ι (e i))
  have hspan_e : ∀ γ ∈ ψ,
      γ ∈ Submodule.span ℤ (Set.range (fun i : Fin c.length => α (e i))) := by
    intro γ hγ
    rw [hrange]
    exact hspan_path γ hγ
  have hψeq_e : ∀ v, v ∈ ψ ↔ IsRoot A.tau v ∧
      v ∈ Submodule.span ℤ (Set.range (fun i : Fin c.length => α (e i))) := by
    intro v
    rw [hψeq]
    simp only [Set.mem_setOf_eq]
    rw [hrange]
  have hind_e : LinearIndependent ℚ (fun i : Fin c.length =>
      fun k => ((α (e i) k : ℤ) : ℚ)) :=
    hLIα.comp (fun i => e i) e.injective
  have hcone_e : ∀ v : Fin A.tau.rank → ℤ, IsRoot A.tau v →
      v ∈ Submodule.span ℤ (Set.range (fun i : Fin c.length => α (e i))) →
      (∃ n : Fin c.length → ℕ, v = ∑ i, (n i : ℤ) • α (e i)) ∨
      (∃ n : Fin c.length → ℕ, v = -∑ i, (n i : ℤ) • α (e i)) := by
    intro v hv hvs
    rw [hrange] at hvs
    rcases hcone v hv hvs with ⟨n, hrep⟩ | ⟨n, hrep⟩
    · refine Or.inl ⟨fun i => n (e i), ?_⟩
      rw [hrep]
      exact Fintype.sum_equiv e.symm (fun x : {x // x ∈ c} => (n x : ℤ) • α x)
        (fun i : Fin c.length => (n (e i) : ℤ) • α (e i)) (fun x => by simp)
    · refine Or.inr ⟨fun i => n (e i), ?_⟩
      rw [hrep]
      rw [Fintype.sum_equiv e.symm (fun x : {x // x ∈ c} => (n x : ℤ) • α x)
        (fun i : Fin c.length => (n (e i) : ℤ) • α (e i)) (fun x => by simp)]
  set rk := k0pPow A.row.rho s with hrk
  have hrank : (k0CompType (k0DiagOf T) c).2 = c.length :=
    lq_compType_rank_ACD (k0DiagOf T) c (Or.inr (Or.inr hcD))
  have hct : k0CompType (k0DiagOf T) c = (.D, c.length) := Prod.ext hcD hrank
  set o := k0AutOrder c rk with ho
  have htw : lqTw A P j =
      (if A.row.d = 2 ∧ s % 2 = 1 ∧ (decide (c.length % 2 = 1) = true) then
        (if o = 1 then 2 else if o = 2 then 1 else o) else o) := by
    simp only [lqTw]
    rw [← hs]
    have hct' : k0CompType (k0DiagOf A.row.T) ((P.orbitNodes j).headD []) = (.D, c.length) := by
      change k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.D, c.length)
      rw [← hc]
      exact hct
    rw [hct']
    rfl
  have hslen : componentOrbitLength A.setup.ρ ψ = s := by
    rw [hψ, P.orbit_length j, ← hs]
  have hcard : ψ.ncard = 2 * c.length * (c.length - 1) := hn
  have hcompRank : compRank ψ = c.length := lq_compRank A P j
  have htwoD : 4 ≤ compRank ψ ∧ ψ.ncard = 2 * compRank ψ * (compRank ψ - 1) := by
    constructor
    · rw [hcompRank]; omega
    · rw [hcompRank, hcard]
  have hclosed : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) '' ψ = ψ := by
    have hlen : s = componentOrbitLength A.setup.ρ ψ := by
      rw [hs, hψ]; exact (P.orbit_length j).symm
    rw [hlen]; exact lqKindD_orbit_image A.setup ψ
  have heq_rk : ∀ i : Fin c.length, (e (q i)).val = rk.getD (e i).val 0 := by
    intro i
    rw [hq_apply i, hpv (e i)]
    exact (lqKindD_k0pPow_getD_nodePerm A s (ι (e i))).symm
  have hfix_of_q1 : q = 1 → ∀ x ∈ c, rk.getD x 0 = x := by
    intro hq1 x hx
    let k : Fin c.length := e.symm ⟨x, hx⟩
    have hk : (e k).val = x := congrArg Subtype.val (e.apply_symm_apply _)
    have h1 := heq_rk k
    rw [hq1] at h1
    simp only [Equiv.Perm.one_apply] at h1
    rw [hk] at h1
    exact h1.symm
  have hq_of_rk1 : (∀ x ∈ c, rk.getD x 0 = x) → q = 1 := by
    intro hfix
    ext i
    show (q i).val = i.val
    have h1 := heq_rk i
    rw [hfix (e i).val (e i).2] at h1
    exact congrArg Fin.val (e.injective (Subtype.ext h1))
  have hfix_of_qsq : q * q = 1 → ∀ x ∈ c, (k0pMul rk rk).getD x 0 = x := by
    intro hqq x hx
    let k : Fin c.length := e.symm ⟨x, hx⟩
    have hk : (e k).val = x := congrArg Subtype.val (e.apply_symm_apply _)
    have h1 : (k0pMul rk rk).getD (e k).val 0 = (e (q (q k))).val := by
      rw [lqKindD_k0pMul_getD _ _
        (by rw [lqKindD_k0pPow_length, A.row.rho_length]; exact hxlt (e k).val (e k).2)]
      rw [show rk.getD (e k).val 0 = (e (q k)).val from (heq_rk k).symm]
      exact (heq_rk (q k)).symm
    have h2 : q (q k) = k := by
      have := congrArg (fun f : Equiv.Perm (Fin c.length) => f k) hqq
      simpa [Equiv.Perm.mul_apply] using this
    rw [← hk, h1, h2]
  have hqsq_of_rk2 :
      (∀ x ∈ c, (k0pMul rk rk).getD x 0 = x) → q * q = 1 := by
    intro hfix
    ext i
    have hxi := hfix (e i).val (e i).2
    have h1 : (k0pMul rk rk).getD (e i).val 0 = (e (q (q i))).val := by
      rw [lqKindD_k0pMul_getD _ _
        (by rw [lqKindD_k0pPow_length, A.row.rho_length]; exact hxlt (e i).val (e i).2)]
      rw [show rk.getD (e i).val 0 = (e (q i)).val from (heq_rk i).symm]
      exact (heq_rk (q i)).symm
    rw [h1] at hxi
    have h2 := e.injective (Subtype.ext hxi)
    show ((q * q) i).val = (i : Fin c.length).val
    rw [show (q * q) i = q (q i) from rfl]
    exact congrArg Fin.val h2
  have hfix_of_qcube : q * q * q = 1 → ∀ x ∈ c,
      (k0pMul rk (k0pMul rk rk)).getD x 0 = x := by
    intro hqq x hx
    let k : Fin c.length := e.symm ⟨x, hx⟩
    have hk : (e k).val = x := congrArg Subtype.val (e.apply_symm_apply _)
    have h1 : (k0pMul rk (k0pMul rk rk)).getD (e k).val 0 = (e (q (q (q k)))).val := by
      rw [lqKindD_k0pMul_getD _ _
        (by rw [lqKindD_k0pMul_length, lqKindD_k0pPow_length, A.row.rho_length]
            exact hxlt (e k).val (e k).2)]
      rw [show (k0pMul rk rk).getD (e k).val 0 = (e (q (q k))).val from by
        rw [lqKindD_k0pMul_getD _ _
          (by rw [lqKindD_k0pPow_length, A.row.rho_length]; exact hxlt (e k).val (e k).2)]
        rw [show rk.getD (e k).val 0 = (e (q k)).val from (heq_rk k).symm]
        exact (heq_rk (q k)).symm]
      exact (heq_rk (q (q k))).symm
    have h2 : q (q (q k)) = k := by
      have := congrArg (fun f : Equiv.Perm (Fin c.length) => f k) hqq
      simpa [Equiv.Perm.mul_apply] using this
    rw [← hk, h1, h2]

  have hmove_of_qne : q ≠ 1 → ∃ x ∈ c, rk.getD x 0 ≠ x := by
    intro hqne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    refine hqne (Equiv.ext fun i => ?_)
    have h1 : rk.getD (e i).val 0 = (e i).val := hcon (e i).val (e i).2
    have h2 : (e (q i)).val = (e i).val := (heq_rk i).trans h1
    exact e.injective (Subtype.ext h2)
  have ho_of_q1 : q = 1 → o = 1 := by
    intro hq1
    rw [ho]
    exact lqKindD_autOrder_eq_one c rk (hfix_of_q1 hq1)
  have hqq_of_o2 : o = 2 → q * q = 1 := by
    intro ho2
    rw [ho] at ho2
    exact hqsq_of_rk2 (lqKindD_autOrder_two_fix c rk (by omega) ho2)
  have ho_of_qq (qq : Equiv.Perm (Fin c.length)) (hmul : qq * qq = 1) (hne : qq ≠ 1)
      (hqeq : q = qq) : o = 2 := by
    have hqne : q ≠ 1 := by rw [hqeq]; exact hne
    have hqmul : q * q = 1 := by rw [hqeq]; exact hmul
    rw [ho]
    exact lqKindD_autOrder_eq_two c rk (by omega) (hmove_of_qne hqne) (hfix_of_qsq hqmul)
  have ho_le_two : (∀ x ∈ c, (k0pMul rk rk).getD x 0 = x) → o ≤ 2 := by
    intro hfix2
    rw [ho]
    exact lqKindD_autOrder_le_two c rk (by omega) hfix2
  have ho_le_three : (∀ x ∈ c, (k0pMul rk (k0pMul rk rk)).getD x 0 = x) → o ≤ 3 := by
    intro hfix3
    rw [ho]
    exact lqKindD_autOrder_le_three c rk (by omega) hfix3
  have hinner_two_s : q * q = 1 → twistInner ψ
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) := by
    intro hqq
    have hel2 : el * el = 1 := by
      rcases hel12 with h | h <;> rw [h] <;> norm_num
    have hfφ : ∀ i : Fin c.length, (φ.comp φ) (α (e i)) = α (e i) := by
      intro i
      rw [AddMonoidHom.comp_apply, hφ_apply i, map_zsmul, hφ_apply (q i), smul_smul, hel2,
        one_smul]
      have h2 : q (q i) = i := by
        have := congrArg (fun f : Equiv.Perm (Fin c.length) => f i) hqq
        simpa [Equiv.Perm.mul_apply] using this
      rw [h2]
    have hφφρ : ∀ γ ∈ ψ,
        ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) γ = (φ.comp φ) γ := by
      intro γ hγ
      have h1 : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ = φ γ := hφρ γ hγ
      have hmem : φ γ ∈ ψ := by
        rw [← h1, ← hclosed]
        exact ⟨γ, hγ, rfl⟩
      calc ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) γ
          = ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s])
              (((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ) := by
            rw [show 2 * s = s + s from by ring, Function.iterate_add_apply]
        _ = ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (φ γ) := by rw [h1]
        _ = φ (φ γ) := hφρ (φ γ) hmem
        _ = (φ.comp φ) γ := rfl
    refine (lqKindD_twistInner_congr
      (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]))
      (σ' := ((φ.comp φ : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ)) :
        (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφφρ).mpr ?_
    refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
    have hfix : ∀ z ∈ Submodule.span ℤ (Set.range (fun i : Fin c.length => α (e i))),
        (φ.comp φ) z = z := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => (φ.comp φ) z = z) ?_ ?_ ?_ ?_ hz
      · rintro y ⟨i, rfl⟩
        exact hfφ i
      · simp
      · intro a b _ _ ha hb
        rw [map_add, ha, hb]
      · intro n y _ hy
        rw [map_zsmul, hy]
    rw [hfix γ (hspan_e γ hγ)]
    simp
  have hexc_false : (c.length = 4 → twistInner ψ
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s])) →
      ¬ ((compRank ψ = 6 ∧ ψ.ncard = 72) ∨
        (compRank ψ = 4 ∧ ψ.ncard = 24 ∧ ¬ twistInner ψ
          ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]))) := by
    intro h2s
    rintro (⟨h6, h72⟩ | ⟨h4c, h24, hnt⟩)
    · rw [hcompRank] at h6
      rw [hcard, h6] at h72
      norm_num at h72
    · rw [hcompRank] at h4c
      exact hnt (h2s h4c)

  by_cases hpar : c.length % 2 = 0
  ·
    have htw_e : lqTw A P j = o := by rw [htw]; simp [hpar]
    have ho_le3 : o ≤ 3 := by
      rcases hcls with hq1 | ⟨hr4, hqne⟩ | ⟨h5, hqsw⟩
      · rw [ho_of_q1 hq1]; norm_num
      · rcases lqKindD_four_order c.length hr4 q hq_cartan with h2 | h3
        · exact le_trans (ho_le_two (hfix_of_qsq h2)) (by norm_num)
        · exact ho_le_three (hfix_of_qcube h3)
      · exact le_trans (le_of_eq (ho_of_qq _ (lqKindD_swapLeaf_mul c.length (by omega))
          (lqKindD_swapLeaf_ne_one c.length (by omega)) hqsw)) (by norm_num)
    constructor
    ·
      intro htw1
      rw [hslen]
      have ho1 : o = 1 := by rw [htw_e] at htw1; exact htw1
      have hq1 : q = 1 := hq_of_rk1 (lqKindD_autOrder_one_fix c rk ho1)
      rcases hel12 with hel1 | helm1
      · refine lqKindD_inner_of_node_fix hspan_e _ φ hφρ ?_
        intro i
        rw [hφ_apply i, hel1, hq1]
        simp
      · refine lqKindD_inner_neg_even (r := c.length) (by omega) h4' hψeq_e hroots_e hsl
          hmat' hind_e hcone_e ?_ _ φ hφρ ?_
        · intro q' hq' hq'1
          exact ⟨(lqKindD_even_data c.length (by omega) h4' hr8 hpar q' hq' hq'1).1,
            (lqKindD_even_data c.length (by omega) h4' hr8 hpar q' hq' hq'1).2.1⟩
        · intro i
          rw [hφ_apply i, helm1, hq1]
          simp
    constructor
    ·
      intro htw2
      have ho2 : o = 2 := by rw [htw_e] at htw2; exact htw2
      have hqne : q ≠ 1 := by
        intro hq1
        rw [ho_of_q1 hq1] at ho2
        omega
      have hdat := lqKindD_even_data c.length (by omega) h4' hr8 hpar q hq_cartan hqne
      have hnot : ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) := by
        refine (lqKindD_twistInner_congr
          (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]))
          (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).not.mpr ?_
        rcases hel12 with hel1 | helm1
        · refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
            hspan_e (d := 2) (q := q) (e' := 1) hdat.1 φ ?_ hdat.2.2
          intro i
          rw [hφ_apply i, hel1]
        · refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
            hspan_e (d := 2) (q := q) (e' := -1) hdat.1 φ ?_ hdat.2.1
          intro i
          rw [hφ_apply i, helm1]
      have h2s : c.length = 4 → twistInner ψ
          ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) :=
        fun _ => hinner_two_s (hqq_of_o2 ho2)
      have hexc := hexc_false h2s
      unfold twistKind
      rw [hslen, if_neg hnot, if_neg hexc, if_pos htwoD]
    ·
      intro htw3
      have ho3 : o = 3 := by
        have h1 : 3 ≤ o := by rw [htw_e] at htw3; exact htw3
        omega
      obtain ⟨hfix3, -, hnot2fix⟩ := lqKindD_autOrder_three_fix c rk (by omega) ho3
      have hq2ne : q * q ≠ 1 := by
        intro hqq
        obtain ⟨i, hi, hne⟩ := hnot2fix
        exact hne (hfix_of_qsq hqq i hi)
      have hr4 : c.length = 4 := by
        rcases hcls with hq1 | ⟨hr4, -⟩ | ⟨h5, hqsw⟩
        · rw [ho_of_q1 hq1] at ho3
          omega
        · exact hr4
        · rw [ho_of_qq _ (lqKindD_swapLeaf_mul c.length (by omega))
            (lqKindD_swapLeaf_ne_one c.length (by omega)) hqsw] at ho3
          omega
      have hqne : q ≠ 1 := by
        intro hq1
        exact hq2ne (by rw [hq1]; simp)
      have hdat := lqKindD_even_data c.length (by omega) h4' hr8 hpar q hq_cartan hqne
      have hnot : ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) := by
        refine (lqKindD_twistInner_congr
          (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]))
          (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).not.mpr ?_
        rcases hel12 with hel1 | helm1
        · refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
            hspan_e (d := 2) (q := q) (e' := 1) hdat.1 φ ?_ hdat.2.2
          intro i
          rw [hφ_apply i, hel1]
        · refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
            hspan_e (d := 2) (q := q) (e' := -1) hdat.1 φ ?_ hdat.2.1
          intro i
          rw [hφ_apply i, helm1]
      have hel2 : el * el = 1 := by
        rcases hel12 with h | h <;> rw [h] <;> norm_num
      have hq2_cartan : ∀ i j : Fin c.length,
          lqKindD_cartan c.length ((q * q) i) ((q * q) j) = lqKindD_cartan c.length i j := by
        intro i j
        rw [show (q * q) i = q (q i) from rfl, show (q * q) j = q (q j) from rfl,
          hq_cartan (q i) (q j), hq_cartan i j]
      have hfour := lqKindD_four_data c.length (by omega) hr4 (q * q) hq2_cartan hq2ne
      have hφφρ : ∀ γ ∈ ψ,
          ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) γ = (φ.comp φ) γ := by
        intro γ hγ
        have h1 : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ = φ γ := hφρ γ hγ
        have hmem : φ γ ∈ ψ := by
          rw [← h1, ← hclosed]
          exact ⟨γ, hγ, rfl⟩
        calc ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) γ
            = ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s])
                (((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ) := by
              rw [show 2 * s = s + s from by ring, Function.iterate_add_apply]
          _ = ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) (φ γ) := by rw [h1]
          _ = φ (φ γ) := hφρ (φ γ) hmem
          _ = (φ.comp φ) γ := rfl
      have hnot2s : ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) := by
        refine (lqKindD_twistInner_congr
          (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]))
          (σ' := ((φ.comp φ : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ)) :
            (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφφρ).not.mpr ?_
        refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
          hspan_e (d := 2) (q := q * q) (e' := 1) hfour.1 (φ.comp φ) ?_ hfour.2
        intro i
        rw [AddMonoidHom.comp_apply, hφ_apply i, map_zsmul, hφ_apply (q i), smul_smul, hel2]
        simp
      have hexc : (compRank ψ = 6 ∧ ψ.ncard = 72) ∨
          (compRank ψ = 4 ∧ ψ.ncard = 24 ∧
            ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s])) := by
        refine Or.inr ⟨?_, ?_, hnot2s⟩
        · rw [hcompRank]; exact hr4
        · rw [hcard, hr4]
      refine ⟨hr4, ?_⟩
      unfold twistKind
      rw [hslen, if_neg hnot, if_pos hexc]
  ·
    have hodd : c.length % 2 = 1 := by
      have := Nat.mod_two_eq_zero_or_one c.length
      omega
    have h5 : 5 ≤ c.length := by omega
    have htw_o : lqTw A P j =
        (if A.row.d = 2 ∧ s % 2 = 1 then
          (if o = 1 then 2 else if o = 2 then 1 else o) else o) := by
      rw [htw]; simp [hodd]
    have hqcases : q = 1 ∨ q = lqKindD_swapLeaf c.length := by
      rcases hcls with h | ⟨h4, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exfalso; omega
      · exact Or.inr h
    have hmul_sw : lqKindD_swapLeaf c.length * lqKindD_swapLeaf c.length = 1 :=
      lqKindD_swapLeaf_mul c.length (by omega)
    have hne_sw : lqKindD_swapLeaf c.length ≠ 1 :=
      lqKindD_swapLeaf_ne_one c.length (by omega)
    have ho12 : o = 1 ∨ o = 2 := by
      rcases hqcases with h1 | hsw
      · exact Or.inl (ho_of_q1 h1)
      · exact Or.inr (ho_of_qq _ hmul_sw hne_sw hsw)
    have hdat := lqKindD_odd_data c.length (by omega) h5 hr8 hodd q hq_cartan
    have hdat1 := lqKindD_odd_data c.length (by omega) h5 hr8 hodd
      (1 : Equiv.Perm (Fin c.length)) (by intro i j; simp)
    let negHom : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ) :=
      { toFun := fun z => -z
        map_zero' := by simp
        map_add' := by intro a b; abel }
    have hneg : ∀ z, negHom z = -z := fun z => rfl
    have hnotInnerNeg : ¬ twistInner ψ (fun z => -z) := by
      have hnot : ¬ twistInner ψ (negHom : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) := by
        refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
          hspan_e (d := 4) (q := 1) (e' := -1) hdat1.2.1 negHom ?_ (hdat1.2.2.1 rfl)
        intro i
        rw [Equiv.Perm.one_apply, hneg, neg_one_smul]
      exact (lqKindD_twistInner_congr (σ := fun z => -z)
        (σ' := (negHom : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)))
        (fun γ _ => (hneg γ).symm)).not.mpr hnot
    have hlq12 : lqTw A P j = 1 ∨ lqTw A P j = 2 := by
      rw [htw_o]
      by_cases hcorr : A.row.d = 2 ∧ s % 2 = 1
      · rw [if_pos hcorr]
        rcases ho12 with h | h
        · right; rw [h]; norm_num
        · left; rw [h]; norm_num
      · rw [if_neg hcorr]
        rcases ho12 with h | h
        · left; exact h
        · right; exact h
    constructor
    ·
      intro htw1
      rw [hslen]
      rw [htw_o] at htw1
      by_cases hcorr : A.row.d = 2 ∧ s % 2 = 1
      · rw [if_pos hcorr] at htw1
        have ho2 : o = 2 := by
          rcases ho12 with h | h
          · exfalso
            rw [h] at htw1
            norm_num at htw1
          · exact h
        have hqsw : q = lqKindD_swapLeaf c.length := by
          rcases hqcases with h1 | hsw
          · rw [ho_of_q1 h1] at ho2; omega
          · exact hsw
        have helm1 : el = -1 := by
          rw [hel_d, hcorr.1, if_neg (by norm_num : ¬ (2 : ℕ) = 1)]
          exact (Nat.odd_iff.mpr hcorr.2).neg_one_pow
        refine lqKindD_inner_neg_odd hψeq_e hroots_e hmat' hind_e hcone_e
          (lqKindD_swapLeaf c.length) (fun q' hq' => ?_) hnotInnerNeg _ φ hφρ ?_
        · exact (lqKindD_odd_data c.length (by omega) h5 hr8 hodd q' hq').1
        · intro i
          rw [hφ_apply i, helm1, hqsw]
          simp
      · rw [if_neg hcorr] at htw1
        have ho1 : o = 1 := by
          rcases ho12 with h | h
          · exact h
          · rw [h] at htw1; omega
        have hq1 : q = 1 := hq_of_rk1 (lqKindD_autOrder_one_fix c rk (by rw [← ho]; exact ho1))
        have hel1 : el = 1 := by
          rw [hel_d]
          by_cases hd : A.row.d = 1
          · rw [if_pos hd, one_pow]
          · rw [if_neg hd]
            have hd2 : A.row.d = 2 := by
              rcases hd12 with h1 | h2
              · exact absurd h1 hd
              · exact h2
            have hse : s % 2 = 0 := by
              rcases Nat.mod_two_eq_zero_or_one s with h | h
              · exact h
              · exact absurd ⟨hd2, h⟩ hcorr
            rcases Nat.even_or_odd s with he | ho
            · exact he.neg_one_pow
            · exfalso
              have h1 := Nat.odd_iff.mp ho
              rw [hse] at h1
              simp at h1
        refine lqKindD_inner_of_node_fix hspan_e _ φ hφρ ?_
        intro i
        rw [hφ_apply i, hel1, hq1]
        simp
    constructor
    ·
      intro htw2
      rw [htw_o] at htw2
      by_cases hcorr : A.row.d = 2 ∧ s % 2 = 1
      · rw [if_pos hcorr] at htw2
        have ho1 : o = 1 := by
          rcases ho12 with h | h
          · exact h
          · exfalso
            rw [h] at htw2
            norm_num at htw2
        have hq1 : q = 1 := hq_of_rk1 (lqKindD_autOrder_one_fix c rk (by rw [← ho]; exact ho1))
        have helm1 : el = -1 := by
          rw [hel_d, hcorr.1, if_neg (by norm_num : ¬ (2 : ℕ) = 1)]
          exact (Nat.odd_iff.mpr hcorr.2).neg_one_pow
        have hnot : ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) := by
          refine (lqKindD_twistInner_congr
            (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]))
            (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).not.mpr ?_
          refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
            hspan_e (d := 4) (q := 1) (e' := -1) hdat1.2.1 φ ?_ (hdat1.2.2.1 rfl)
          intro i
          rw [Equiv.Perm.one_apply, hφ_apply i, hq1, helm1, neg_one_smul]
          simp
        have h2s : c.length = 4 → twistInner ψ
            ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) :=
          fun hr4 => absurd hr4 (by omega)
        have hexc := hexc_false h2s
        unfold twistKind
        rw [hslen, if_neg hnot, if_neg hexc, if_pos htwoD]
      · rw [if_neg hcorr] at htw2
        have ho2 : o = 2 := htw2
        have hqsw : q = lqKindD_swapLeaf c.length := by
          rcases hqcases with h1 | hsw
          · rw [ho_of_q1 h1] at ho2; omega
          · exact hsw
        have hel1 : el = 1 := by
          rw [hel_d]
          by_cases hd : A.row.d = 1
          · rw [if_pos hd, one_pow]
          · rw [if_neg hd]
            have hd2 : A.row.d = 2 := by
              rcases hd12 with h1 | h2
              · exact absurd h1 hd
              · exact h2
            rcases Nat.even_or_odd s with he | ho
            · exact he.neg_one_pow
            · exfalso; exact hcorr ⟨hd2, Nat.odd_iff.mp ho⟩
        have hnot : ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) := by
          refine (lqKindD_twistInner_congr
            (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]))
            (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).not.mpr ?_
          refine lqKindD_outer_of_val (r := c.length) (by omega) hroots hsl hmat' hαψ_e
            hspan_e (d := 4) (q := q) (e' := 1) hdat.2.1 φ ?_ (hdat.2.2.2 hqsw)
          intro i
          rw [hφ_apply i, hel1]
        have h2s : c.length = 4 → twistInner ψ
            ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * s]) :=
          fun hr4 => absurd hr4 (by omega)
        have hexc := hexc_false h2s
        unfold twistKind
        rw [hslen, if_neg hnot, if_neg hexc, if_pos htwoD]
    ·
      intro htw3
      rcases hlq12 with h | h <;> omega

end CFSG.StandardType.GGK0LQ

end
