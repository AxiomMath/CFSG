module

public import CFSG.LocalAnalysis.StandardType.GGK0LQTwist
public import CFSG.LocalAnalysis.StandardType.GGK0LQRoots
public import CFSG.LocalAnalysis.StandardType.GGK0LQShape
public import CFSG.LocalAnalysis.StandardType.GGK0LQLongest
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.Steinberg.Adjoint

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private def lqKindA_cartan (r : ℕ) (i j : Fin r) : ℤ :=
  if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

private def lqKindA_comps : GGKacType → List (List ℕ)
  | .E6 => [[0,1,2,3,4],[0,2,3,4],[0,2,4],[0,2,4,5],[0,2,4,5,6],[1,2,3,4],[1,3,4],
      [1,3,4,5],[1,3,4,5,6],[2,3,4],[2,4,5],[2,4,5,6],[3,4,5],[3,4,5,6],[4,5,6]]
  | .E7 => [[0,1,2,3,4],[0,1,3],[0,1,3,4],[0,1,3,4,5],[0,1,3,4,5,6],[0,1,3,4,5,6,7],
      [1,2,3,4],[1,3,4],[1,3,4,5],[1,3,4,5,6],[1,3,4,5,6,7],[2,3,4],[2,4,5],[2,4,5,6],
      [2,4,5,6,7],[3,4,5],[3,4,5,6],[3,4,5,6,7],[4,5,6],[4,5,6,7],[5,6,7]]
  | .E8 => [[0,1,3,4,5,6,7,8],[0,2,4,5,6,7,8],[0,3,4,5,6,7,8],[0,4,5,6,7,8],[0,5,6,7,8],
      [0,6,7,8],[0,7,8],[1,2,3,4],[1,3,4],[1,3,4,5],[1,3,4,5,6],[1,3,4,5,6,7],
      [1,3,4,5,6,7,8],[2,3,4],[2,4,5],[2,4,5,6],[2,4,5,6,7],[2,4,5,6,7,8],[3,4,5],
      [3,4,5,6],[3,4,5,6,7],[3,4,5,6,7,8],[4,5,6],[4,5,6,7],[4,5,6,7,8],[5,6,7],
      [5,6,7,8],[6,7,8]]
  | .F4 => [[0,1,2]]

private def lqKindA_degree (T : GGKacType) (c : List ℕ) (x : ℕ) : ℕ :=
  (c.filter (fun y => decide (y ≠ x ∧ 0 < (k0DiagOf T).adj x y))).length

private def lqKindA_start (T : GGKacType) (c : List ℕ) : ℕ :=
  (c.filter (fun x => decide (lqKindA_degree T c x = 1))).headD (c.headD 0)

private def lqKindA_walk (T : GGKacType) (c : List ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, acc => acc
  | f + 1, prev, cur, acc =>
      match c.filter (fun y => decide (y ≠ prev ∧ 0 < (k0DiagOf T).adj cur y)) with
      | [] => acc
      | nxt :: _ => lqKindA_walk T c f cur nxt (acc ++ [nxt])

private def lqKindA_path (T : GGKacType) (c : List ℕ) : List ℕ :=
  let s := lqKindA_start T c
  lqKindA_walk T c c.length s s [s]

private def lqKindA_scale (τ : Tag) (T : GGKacType) (c : List ℕ) : ℤ :=
  let p := lqKindA_path T c
  if h : p ≠ [] then
    iform (τ := τ) (lqExtRoot τ T (p.head h)) (lqExtRoot τ T (p.head h)) / 2
  else 1

private def lqKindA_mu (τ : Tag) (T : GGKacType) (c : List ℕ) : Fin τ.rank → ℤ :=
  ∑ i : Fin c.length, ((c.length - i.val : ℕ) : ℤ) •
    lqExtRoot τ T ((lqKindA_path T c).getD i.val 0)

private abbrev lqKindA_GoodPath (τ : Tag) (T : GGKacType) (c : List ℕ) : Prop :=
  let p := lqKindA_path T c
  let r := c.length
  let m := lqKindA_scale τ T c
  p.length = r ∧ p.Nodup ∧ p.toFinset = c.toFinset ∧
    (m = 1 ∨ m = 2) ∧ (T = .F4 → m = 2) ∧ (m = 2 → T = .F4) ∧
    (c.all (fun x => decide (iform (τ := τ) (lqExtRoot τ T x)
      (lqExtRoot τ T x) = 2 * m)) = true) ∧
    (∀ i j : Fin r, iform (τ := τ) (lqExtRoot τ T (p.getD i.val 0))
      (lqExtRoot τ T (p.getD j.val 0)) = m * lqKindA_cartan r i j) ∧
    (c.all (fun x => decide (iform (τ := τ) (lqKindA_mu τ T c) (lqExtRoot τ T x) =
      m * ((r : ℤ) + 1) * (if x = p.headD 0 then 1 else 0))) = true) ∧
    (c.length + 1 = (k0DiagOf T).marks.length →
      (((List.range (k0DiagOf T).marks.length).filter (fun w => decide (w ∉ c))).all
        (fun w => decide (1 < (k0DiagOf T).marks.getD w 0))) = true)

private def lqKindA_checkPath (τ : Tag) (T : GGKacType) (c : List ℕ) : Bool :=
  decide (lqKindA_GoodPath τ T c)

private theorem lqKindA_checkPath_all (τ : Tag) (T : GGKacType) (hτ : absTag T = τ) :
    (lqKindA_comps T).all (lqKindA_checkPath τ T) = true := by
  cases T <;> subst hτ <;> decide +kernel

private theorem lqKindA_covers (T : GGKacType) :
    ∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      zero.length < (k0DiagOf T).marks.length →
      ∀ c ∈ k0Comps (k0DiagOf T) zero,
        (k0CompType (k0DiagOf T) c).1 = .A → 3 ≤ c.length → c ∈ lqKindA_comps T := by
  cases T <;> decide +kernel

private lemma lqKindA_cartan_adj {r : ℕ} {i j : Fin r} (h : lqKindA_cartan r i j = -1) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  unfold lqKindA_cartan at h
  by_cases hij : i = j
  · rw [if_pos hij] at h; omega
  · rw [if_neg hij] at h
    by_cases hc : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · exact hc
    · rw [if_neg hc] at h; omega

private lemma lqKindA_cartan_neighbour {r : ℕ} {i j : Fin r} :
    lqKindA_cartan r i j = -1 ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  refine ⟨lqKindA_cartan_adj, fun h => ?_⟩
  have hne : i ≠ j := by rintro rfl; omega
  unfold lqKindA_cartan
  rw [if_neg hne, if_pos h]

private lemma lqKindA_cartan_left {r : ℕ} {i : Fin r} (h : 0 < i.val) :
    lqKindA_cartan r i ⟨i.val - 1, by omega⟩ = -1 := by
  rw [lqKindA_cartan_neighbour]
  right
  change i.val - 1 + 1 = i.val
  omega

private lemma lqKindA_cartan_right {r : ℕ} {i : Fin r} (h : i.val + 1 < r) :
    lqKindA_cartan r i ⟨i.val + 1, by omega⟩ = -1 := by
  rw [lqKindA_cartan_neighbour]
  left
  change i.val + 1 = i.val + 1
  rfl

private def lqKindA_rev (r : ℕ) : Equiv.Perm (Fin r) where
  toFun i := ⟨r - 1 - i.val, by have := i.isLt; omega⟩
  invFun i := ⟨r - 1 - i.val, by have := i.isLt; omega⟩
  left_inv i := by ext; simp; omega
  right_inv i := by ext; simp; omega

private lemma lqKindA_rev_apply (r : ℕ) (i : Fin r) : (lqKindA_rev r i).val = r - 1 - i.val := rfl

private lemma lqKindA_rev_invol (r : ℕ) (i : Fin r) : lqKindA_rev r (lqKindA_rev r i) = i := by
  ext
  rw [lqKindA_rev_apply, lqKindA_rev_apply]
  omega

private lemma lqKindA_cartan_rev (r : ℕ) (i j : Fin r) :
    lqKindA_cartan r (lqKindA_rev r i) (lqKindA_rev r j) = lqKindA_cartan r i j := by
  unfold lqKindA_cartan
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl]
  · have hrevne : ¬ (lqKindA_rev r i = lqKindA_rev r j) :=
      fun h => hij ((lqKindA_rev r).injective h)
    rw [if_neg hrevne, if_neg hij]
    by_cases hc : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hc' : (lqKindA_rev r i).val + 1 = (lqKindA_rev r j).val ∨
          (lqKindA_rev r j).val + 1 = (lqKindA_rev r i).val := by
        rw [lqKindA_rev_apply, lqKindA_rev_apply]; omega
      rw [if_pos hc', if_pos hc]
    · have hc' : ¬ ((lqKindA_rev r i).val + 1 = (lqKindA_rev r j).val ∨
          (lqKindA_rev r j).val + 1 = (lqKindA_rev r i).val) := by
        rw [lqKindA_rev_apply, lqKindA_rev_apply]; omega
      rw [if_neg hc', if_neg hc]

private lemma lqKindA_perm_cartan_fix {r : ℕ} (hr : 2 ≤ r) (p : Equiv.Perm (Fin r))
    (h : ∀ i j, lqKindA_cartan r (p i) (p j) = lqKindA_cartan r i j)
    (h0 : p ⟨0, by omega⟩ = ⟨0, by omega⟩) :
    p = 1 := by
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, by omega⟩
  have hz : z.val = 0 := rfl
  have ho : o.val = 1 := rfl
  have h0z : p z = z := h0
  have h0adj : ∀ j : Fin r, lqKindA_cartan r z j = -1 ↔ j = o := by
    intro j
    rw [lqKindA_cartan_neighbour]
    constructor
    · rintro (hj | hj)
      · exact Fin.ext (by rw [ho]; omega)
      · exfalso; omega
    · rintro rfl; left; rw [hz, ho]
  have hadj : ∀ i j, lqKindA_cartan r (p i) (p j) = -1 ↔ lqKindA_cartan r i j = -1 := by
    intro i j; rw [h i j]
  have hfix : ∀ k : Fin r, p k = k := by
    intro k
    refine Fin.strong_induction_on (motive := fun k => p k = k) ?_ k
    intro k ih
    rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
    · have hk : k = z := Fin.ext (by rw [hz]; omega)
      rw [hk, h0z]
    · let i : Fin r := ⟨k.val - 1, by have := k.isLt; omega⟩
      have hi : i.val = k.val - 1 := rfl
      have hik : i < k := by rw [Fin.lt_def, hi]; omega
      have hpi : p i = i := ih i hik
      have hik_adj : lqKindA_cartan r i k = -1 := by
        rw [lqKindA_cartan_neighbour]; left; rw [hi]; omega
      have h1 : lqKindA_cartan r i (p k) = -1 := by
        have h2 := (hadj i k).mpr hik_adj
        rwa [hpi] at h2
      rcases (lqKindA_cartan_neighbour.mp h1) with hcase | hcase
      · have hpk : (p k).val = k.val := by rw [hi] at hcase; omega
        exact Fin.ext hpk
      · exfalso
        have hpk : (p k).val = k.val - 2 := by rw [hi] at hcase; omega
        let j : Fin r := ⟨k.val - 2, by have := k.isLt; omega⟩
        have hjv : j.val = k.val - 2 := rfl
        have hjk : j < k := by rw [Fin.lt_def, hjv]; omega
        have hpj : p j = j := ih j hjk
        have heq : p k = p j := by rw [hpj]; exact Fin.ext (by rw [hjv]; exact hpk)
        have hkj : k = j := p.injective heq
        have hval : k.val = j.val := by rw [hkj]
        rw [hjv] at hval
        omega
  exact Equiv.ext (fun k => hfix k)

private theorem lqKindA_perm_cartan {r : ℕ} (hr : 2 ≤ r) (p : Equiv.Perm (Fin r))
    (h : ∀ i j, lqKindA_cartan r (p i) (p j) = lqKindA_cartan r i j) :
    p = 1 ∨ p = lqKindA_rev r := by
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, by omega⟩
  have hz : z.val = 0 := rfl
  have ho : o.val = 1 := rfl
  have hzadj : ∀ j : Fin r, lqKindA_cartan r z j = -1 ↔ j = o := by
    intro j
    rw [lqKindA_cartan_neighbour]
    constructor
    · rintro (hj | hj)
      · exact Fin.ext (by rw [ho]; omega)
      · exfalso; omega
    · rintro rfl; left; rw [hz, ho]
  have hend : ∀ k : Fin r, lqKindA_cartan r (p z) k = -1 ↔ k = p o := by
    intro k
    have h1 : lqKindA_cartan r (p z) k = lqKindA_cartan r z (p.symm k) := by
      have := h z (p.symm k)
      simpa using this
    rw [h1, hzadj]
    constructor
    · intro hk; rw [← hk]; simp
    · intro hk; rw [hk]; simp
  have hp0val : (p z).val = 0 ∨ (p z).val = r - 1 := by
    by_contra hcon
    push Not at hcon
    let p0 : Fin r := p z
    have hp0v : p0.val = (p z).val := rfl
    have hpos : 0 < p0.val := by omega
    have hlt : p0.val < r - 1 := by omega
    let a : Fin r := ⟨p0.val - 1, by omega⟩
    let b : Fin r := ⟨p0.val + 1, by omega⟩
    have hav : a.val = p0.val - 1 := rfl
    have hbv : b.val = p0.val + 1 := rfl
    have ha : lqKindA_cartan r (p z) a = -1 :=
      lqKindA_cartan_left (r := r) (i := p z) hpos
    have hb : lqKindA_cartan r (p z) b = -1 :=
      lqKindA_cartan_right (r := r) (i := p z) (by omega)
    have hab : a = b := ((hend a).mp ha).trans ((hend b).mp hb).symm
    have hval : a.val = b.val := by rw [hab]
    rw [hav, hbv] at hval
    omega
  rcases hp0val with hp0 | hp0
  · left
    refine lqKindA_perm_cartan_fix hr p h ?_
    exact Fin.ext (by rw [hz]; exact hp0)
  · right
    let q : Equiv.Perm (Fin r) := p.trans (lqKindA_rev r)
    have hq0 : q z = z := by
      change lqKindA_rev r (p z) = z
      ext
      rw [lqKindA_rev_apply, hz, hp0]
      omega
    have hq : ∀ i j, lqKindA_cartan r (q i) (q j) = lqKindA_cartan r i j := by
      intro i j
      change lqKindA_cartan r (lqKindA_rev r (p i)) (lqKindA_rev r (p j)) =
        lqKindA_cartan r i j
      rw [lqKindA_cartan_rev, h i j]
    have hq1 : q = 1 := lqKindA_perm_cartan_fix hr q hq hq0
    refine Equiv.ext (fun i => ?_)
    have h1 : lqKindA_rev r (p i) = i := by
      have := congrArg (fun e : Equiv.Perm (Fin r) => e i) hq1
      simpa only [q, Equiv.trans_apply, Equiv.Perm.one_apply] using this
    have h2 : lqKindA_rev r (lqKindA_rev r (p i)) = lqKindA_rev r i := congrArg _ h1
    rwa [lqKindA_rev_invol] at h2

private theorem lqKindA_iform_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) x) (((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) y) =
      iform x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]

private theorem lqKindA_orbit_image {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (Ψ : Set (Fin τ.rank → ℤ)) :
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ]) '' Ψ = Ψ := by
  by_cases h : ({s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}).Nonempty
  · exact (Nat.sInf_mem h).2
  · have h0 : componentOrbitLength S.ρ Ψ = 0 := by
      unfold componentOrbitLength
      rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty]
    rw [h0]
    simp

private theorem lqKindA_frob_nodes_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
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

private theorem lqKindA_k0pMul_getD (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
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

private theorem lqKindA_k0pPow_go (a : List ℕ) (f : ℕ) (acc : List ℕ) :
    k0pPow.go a f acc = acc.map ((fun j => a.getD j 0)^[f]) := by
  induction f generalizing acc with
  | zero => simp only [k0pPow.go, Function.iterate_zero, List.map_id]
  | succ f ih =>
      rw [show k0pPow.go a (f+1) acc = k0pPow.go a f (k0pMul a acc) from rfl, ih]
      unfold k0pMul
      rw [List.map_map]
      congr 1

private theorem lqKindA_k0pPow_getD (a : List ℕ) (n : ℕ) {i : ℕ} (hi : i < a.length) :
    (k0pPow a n).getD i 0 = (fun j => a.getD j 0)^[n] i := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lqKindA_k0pPow_go,
    k0pId, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

private theorem lqKindA_rho_iterate (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (fun j => A.row.rho.getD j 0)^[n] i.val = (A.row.nodePerm^[n] i).val := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, A.row.rho_apply, Function.iterate_succ_apply']

private theorem lqKindA_rho_iterate_frobLinear (A : K0LangMark Omega lab p R I phi) (n : ℕ)
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

private theorem lqKindA_k0pPow_length (a : List ℕ) (n : ℕ) :
    (k0pPow a n).length = a.length := by
  rw [show k0pPow a n = k0pPow.go a n (k0pId a.length) from rfl, lqKindA_k0pPow_go]
  simp [k0pId]

private theorem lqKindA_k0pPow_getD_nodePerm (A : K0LangMark Omega lab p R I phi) (n : ℕ)
    (i : Fin A.row.diagram.marks.length) :
    (k0pPow A.row.rho n).getD i.val 0 = (A.row.nodePerm^[n] i).val := by
  rw [lqKindA_k0pPow_getD A.row.rho n (by rw [A.row.rho_length]; exact i.isLt)]
  exact lqKindA_rho_iterate A n i

private lemma lqKindA_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private lemma lqKindA_marks_length_A (A : K0LangMark Omega lab p R I phi) :
    A.row.diagram.marks.length = A.tau.rank + 1 := by
  rw [← A.tau_eq]
  exact lqKindA_marks_length A.row.T

private lemma lqKindA_lt_marks (A : K0LangMark Omega lab p R I phi) {x : ℕ}
    (h : x < A.tau.rank + 1) : x < A.row.diagram.marks.length := by
  rw [show A.row.diagram.marks.length = A.tau.rank + 1 from lqKindA_marks_length_A A]
  exact h

private theorem lqKindA_marks_pos (T : GGKacType) (i : Fin (k0DiagOf T).marks.length) :
    0 < (k0DiagOf T).marks.getD i.val 0 := by
  cases T <;> fin_cases i <;> decide

private theorem lqKindA_p_pos (A : K0LangMark Omega lab p R I phi) : 0 < p := by
  obtain ⟨N⟩ := k0Normal_nonempty A
  exact N.zero_lt

private theorem lqKindA_nodes_proper (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
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
  have hp := lqKindA_p_pos A
  omega

private theorem lqKindA_twistInner_congr {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (h : ∀ γ ∈ Ψ, σ γ = σ' γ) :
    twistInner Ψ σ ↔ twistInner Ψ σ' := by
  unfold twistInner
  constructor
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).symm.trans (hσ γ hγ)⟩
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).trans (hσ γ hγ)⟩

private theorem lqKindA_weyl_disc_step
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
  · rw [hrs, iform_sub_left, iform_smul_left]
    refine dvd_sub (h1 γ' hγ') ?_
    obtain ⟨t, ht⟩ := dvd_mul_of_dvd_right (hpair γ hγ γ' hγ') k
    refine ⟨t, ?_⟩
    rw [hd]
    calc e * k * iform γ γ' = e * (k * iform γ γ') := by ring
      _ = e * (m * t) := by rw [ht]
      _ = (m * e) * t := by ring
  · have hsub' : (y • x - (e * k) • γ) - x = (y • x - x) - (e * k) • γ := by abel
    rw [hrs, hsub', h2, smul_sub, smul_smul]

private theorem lqKindA_weyl_disc_invariant
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
    exact lqKindA_weyl_disc_step m hm hroot hsl hpair hd hγ ih x hx
  | inv_mul_cancel s hs y hy ih =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    rw [rootReflection_inv (hroot γ hγ)]
    exact lqKindA_weyl_disc_step m hm hroot hsl hpair hd hγ ih x hx

private theorem lqKindA_not_twistInner_of_disc
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
    lqKindA_weyl_disc_invariant m hm hroot hsl hpair hd hw μ hμd
  have hσμ : σ μ = w • μ := by
    refine Submodule.span_induction (p := fun z _ => σ z = w • z) ?_ ?_ ?_ ?_ hμ
    · intro z hz; exact hσ z hz
    · simp
    · intro a b _ _ ha hb; rw [map_add, smul_add, ha, hb]
    · intro a z _ hz; rw [map_zsmul, smul_comm, hz]
  have hdv : d ∣ iform ν v := by
    refine Submodule.span_induction (p := fun z _ => d ∣ iform ν z) ?_ ?_ ?_ ?_ hv
    · intro z hz; exact hνd z hz
    · have h0 : iform ν 0 = 0 := by simpa using iform_smul_right (0 : ℤ) ν 0
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

private lemma lqKindA_sum_subtype {M : Type*} [AddCommMonoid M] (c : List ℕ) (f : ℕ → M) :
    (∑ x ∈ c.toFinset, f x) = ∑ x : {x // x ∈ c}, f x.1 := by
  rw [← Finset.sum_coe_sort c.toFinset f]
  let e : {x // x ∈ c.toFinset} ≃ {x // x ∈ c} :=
    { toFun := fun x => ⟨x.1, List.mem_toFinset.mp x.2⟩
      invFun := fun x => ⟨x.1, List.mem_toFinset.mpr x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  exact Fintype.sum_equiv e (fun x => f x.1) (fun x => f x.1) (fun x => rfl)

private lemma lqKindA_bridge_arith {d s o : ℕ} {e : ℤ}
    (hd : d = 1 ∨ d = 2) (he : e = (if d = 1 then (1 : ℤ) else -1) ^ s)
    (ho : o = 1 ∨ o = 2) :
    (if d = 2 ∧ s % 2 = 1 then (if o = 1 then 2 else if o = 2 then 1 else o) else o) = 1 ↔
      (o = 1 ∧ e = 1) ∨ (o = 2 ∧ e = -1) := by
  rcases hd with rfl | rfl
  · have he1 : e = 1 := by rw [he]; simp
    rcases ho with rfl | rfl <;> simp [he1]
  · have he1 : e = (-1 : ℤ) ^ s := by rw [he]; simp
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

private lemma lqKindA_cartan_even (r : ℕ) (hr : r ≤ 8) (n : Fin r → ℤ) :
    ∃ K : ℤ, (∑ i, ∑ j, n i * lqKindA_cartan r i j * n j) = 2 * K := by
  interval_cases r
  · exact ⟨0, by simp⟩
  · exact ⟨n 0 ^ 2, by simp [lqKindA_cartan]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 - n 0 * n 1, by
      simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 - n 0 * n 1 - n 1 * n 2, by
      simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 - n 0 * n 1 - n 1 * n 2 - n 2 * n 3, by
      simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 + n 4 ^ 2 - n 0 * n 1 - n 1 * n 2
      - n 2 * n 3 - n 3 * n 4, by simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 + n 4 ^ 2 + n 5 ^ 2 - n 0 * n 1 - n 1 * n 2
      - n 2 * n 3 - n 3 * n 4 - n 4 * n 5, by simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 + n 4 ^ 2 + n 5 ^ 2 + n 6 ^ 2 - n 0 * n 1
      - n 1 * n 2 - n 2 * n 3 - n 3 * n 4 - n 4 * n 5 - n 5 * n 6, by
      simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩
  · exact ⟨n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 + n 4 ^ 2 + n 5 ^ 2 + n 6 ^ 2 + n 7 ^ 2
      - n 0 * n 1 - n 1 * n 2 - n 2 * n 3 - n 3 * n 4 - n 4 * n 5 - n 5 * n 6 - n 6 * n 7, by
      simp [lqKindA_cartan, Fin.sum_univ_succ]; ring⟩

private theorem lqKindA_nodeSpan_relation (A : K0LangMark Omega lab p R I phi)
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
      have hlen := lqKindA_marks_length_A A
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
      have := lqKindA_marks_pos A.row.T w
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
      have := lqKindA_marks_pos A.row.T x
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

private theorem lqKindA_node_mem_span (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hτ : absTag A.row.T = A.tau)
    (hcTable : lqNodes A P j ∈ lqKindA_comps A.row.T)
    {w : Fin A.row.diagram.marks.length}
    (hspan : A.nodeMap (Pi.single w 1) ∈ Submodule.span ℤ
      {v | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ lqNodes A P j ∧
        v = A.nodeMap (Pi.single i 1)}) :
    w.val ∈ lqNodes A P j := by
  classical
  rcases lqKindA_nodeSpan_relation A P j hspan with h | ⟨hm1, hall⟩
  · exact h
  · by_cases hw : w.val ∈ lqNodes A P j
    · exact hw
    · exfalso
      set c := lqNodes A P j with hc
      have hgood : lqKindA_GoodPath A.tau A.row.T c :=
        of_decide_eq_true ((List.all_eq_true.mp (lqKindA_checkPath_all A.tau A.row.T hτ)) c hcTable)
      obtain ⟨-, -, -, -, -, -, -, -, -, hgap⟩ := hgood
      have hmem : c.Nodup := (lq_nodes_basic A P j).2.1
      have hsub : ∀ x ∈ c, x < A.row.diagram.marks.length := fun x hx =>
        (lq_nodes_basic A P j).2.2 x (by simpa [hc] using hx) |>.1.trans_le (by
          rw [lqKindA_marks_length_A A])
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
      have hgapw := List.all_eq_true.mp (hgap hlen)
      have hwmem : w.val ∈ (List.range A.row.diagram.marks.length).filter
          (fun x => decide (x ∉ c)) := by
        rw [List.mem_filter]
        exact ⟨List.mem_range.mpr w.isLt, decide_eq_true (by simpa [hc] using hw)⟩
      have h2 : (1 : ℕ) < A.row.diagram.marks.getD w.val 0 :=
        of_decide_eq_true (hgapw w.val hwmem)
      have hm1' : A.row.diagram.marks.getD w.val 0 = 1 := by exact_mod_cast hm1
      omega

private theorem lqKindA_maps_c (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hτ : absTag A.row.T = A.tau)
    (hcTable : lqNodes A P j ∈ lqKindA_comps A.row.T) (s : ℕ)
    (hs : s = (P.orbitNodes j).length) {x : ℕ} (hx : x ∈ lqNodes A P j) :
    (A.row.nodePerm^[s] ⟨x, lqKindA_lt_marks A ((lq_nodes_basic A P j).2.2 x hx).1⟩).val ∈
      lqNodes A P j := by
  classical
  set c := lqNodes A P j with hc
  have hxlt : ∀ y ∈ c, y < A.row.diagram.marks.length := by
    intro y hy
    exact lqKindA_lt_marks A ((lq_nodes_basic A P j).2.2 y (by simpa [hc] using hy)).1
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
    rw [hlen]; exact lqKindA_orbit_image A.setup ψ
  have hσψ : ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s])
      (A.nodeMap (Pi.single i 1)) ∈ ψ := by
    rw [← hclosed]; exact ⟨_, hαψ, rfl⟩
  have hσ := lqKindA_frob_nodes_iterate A s i
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
  exact lqKindA_node_mem_span A P j hτ hcTable hsp

private theorem lqKindA_cone (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (hmem : lqNodes A P j ∈ k0Comps (k0DiagOf A.row.T)
      ((List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0))))
    (hzproper : ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).length
        < (k0DiagOf A.row.T).marks.length) :
    ∀ v : Fin A.tau.rank → ℤ, IsRoot A.tau v →
      v ∈ Submodule.span ℤ (Set.range (fun x : {x // x ∈ lqNodes A P j} =>
        A.nodeMap (Pi.single ⟨x.1, lqKindA_lt_marks A
          ((lq_nodes_basic A P j).2.2 x.1 x.2).1⟩ 1))) →
      (∃ n : {x // x ∈ lqNodes A P j} → ℕ,
          v = ∑ x, (n x : ℤ) • A.nodeMap (Pi.single ⟨x.1, lqKindA_lt_marks A
            ((lq_nodes_basic A P j).2.2 x.1 x.2).1⟩ 1)) ∨
        (∃ n : {x // x ∈ lqNodes A P j} → ℕ,
          v = -∑ x, (n x : ℤ) • A.nodeMap (Pi.single ⟨x.1, lqKindA_lt_marks A
            ((lq_nodes_basic A P j).2.2 x.1 x.2).1⟩ 1)) := by
  classical
  set c := lqNodes A P j with hc
  have hxlt : ∀ x ∈ c, x < A.row.diagram.marks.length := fun x hx =>
    lqKindA_lt_marks A ((lq_nodes_basic A P j).2.2 x (by simpa [hc] using hx)).1
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
    rw [hvsum, lqKindA_sum_subtype c (fun x => (n x : ℤ) • lqExtRoot A.tau A.row.T x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lq_nodeMap_eq A ⟨x.1, hxlt x.1 x.2⟩]
  · right
    refine ⟨fun x => n x.1, ?_⟩
    rw [hvsum, lqKindA_sum_subtype c (fun x => (n x : ℤ) • lqExtRoot A.tau A.row.T x)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lq_nodeMap_eq A ⟨x.1, hxlt x.1 x.2⟩]

private theorem lqKindA_autOrder_one (c rk : List ℕ) (hfix : ∀ i ∈ c, rk.getD i 0 = i) :
    k0AutOrder c rk = 1 := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl]
  have hall : c.all (fun i => decide (rk.getD i 0 = i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    exact decide_eq_true (hfix i hi)
  rw [k0AutOrder.go, if_pos hall]

private theorem lqKindA_autOrder_two (c rk : List ℕ)
    (hnot : ¬ ∀ i ∈ c, rk.getD i 0 = i)
    (hfix2 : ∀ i ∈ c, (k0pMul rk rk).getD i 0 = i) :
    k0AutOrder c rk = 2 := by
  rw [show k0AutOrder c rk = k0AutOrder.go c rk 1 rk (c.length + 1) from rfl]
  have hall : c.all (fun i => decide (rk.getD i 0 = i)) = false := by
    cases hb : c.all (fun i => decide (rk.getD i 0 = i)) with
    | false => rfl
    | true => exact absurd (fun i hi => of_decide_eq_true ((List.all_eq_true.mp hb) i hi)) hnot
  have hall2 : c.all (fun i => decide ((k0pMul rk rk).getD i 0 = i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    exact decide_eq_true (hfix2 i hi)
  rw [k0AutOrder.go, if_neg (by rw [hall]; simp)]
  cases hc : c.length with
  | zero => rw [k0AutOrder.go]
  | succ n => rw [k0AutOrder.go, if_pos hall2]

private lemma lqKindA_symm_one {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    τ.symmetrizer j j = 1 := by
  rcases hτ with rfl | rfl | rfl <;> simp [Tag.symmetrizer]

private lemma lqKindA_symm_F4 {τ : Tag} (hτ : τ = .F4) (j : Fin τ.rank) :
    τ.symmetrizer j j = 2 ∨ τ.symmetrizer j j = 1 := by
  subst hτ
  fin_cases j <;> decide

private lemma lqKindA_absTag_eq_F4 {T : GGKacType} (h : absTag T = .F4) : T = .F4 := by
  cases T <;> simp [absTag] at h ⊢

private lemma lqKindA_not_dvd_two (n : ℕ) (hn : 3 ≤ n) :
    ¬ ((n : ℤ) + 1) ∣ 2 * (n : ℤ) := by
  intro h
  have h1 : ((n : ℤ) + 1) ∣ 2 * ((n : ℤ) + 1) := dvd_mul_left _ _
  have h2 : ((n : ℤ) + 1) ∣ 2 := by
    have h3 : 2 * ((n : ℤ) + 1) - 2 * (n : ℤ) = 2 := by ring
    rw [← h3]
    exact dvd_sub h1 h
  have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h2
  omega

private lemma lqKindA_not_dvd_pred (n : ℕ) (hn : 3 ≤ n) :
    ¬ ((n : ℤ) + 1) ∣ ((n : ℤ) - 1) := by
  intro h
  have hpos : (0 : ℤ) < (n : ℤ) - 1 := by omega
  have hle := Int.le_of_dvd hpos h
  omega

private theorem lqKindA_aux (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h3 : 3 ≤ (lqNodes A P j).length)
    (hA : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A)
    (hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      (lqNodes A P j).length * ((lqNodes A P j).length + 1)) :
    (lqTw A P j = 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner) ∧
      (lqTw A P j ≠ 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .suN) := by
  classical
  set T := A.row.T with hT
  set c := lqNodes A P j with hc
  set s := (P.orbitNodes j).length with hs
  set ψ := componentRoots (rootCharHom A.a) (P.repr j) with hψ
  have h3' : 3 ≤ c.length := by simpa [hc] using h3
  have hnb := lq_nodes_basic A P j
  have hnd : c.Nodup := by simpa [hc] using hnb.2.1
  have hxlt : ∀ x ∈ c, x < A.row.diagram.marks.length := fun x hx =>
    lqKindA_lt_marks A ((hnb.2.2 x (by simpa [hc] using hx)).1)
  have hproper : ∃ i < A.row.diagram.marks.length, i ∉ c := by
    obtain ⟨i, hi, hni⟩ := lqKindA_nodes_proper A P j
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
      have hp := lqKindA_p_pos A
      omega
  have hmem : c ∈ k0Comps (k0DiagOf T) zero := by
    have := lq_nodes_mem_comps A P j
    simpa [hT, hc, hzero, lqNodes] using this
  have hcA : (k0CompType (k0DiagOf T) c).1 = .A := by simpa [hT, hc] using hA
  have hcTable : c ∈ lqKindA_comps T :=
    lqKindA_covers T zero (List.mem_sublists.mpr hzsub) hzproper c hmem hcA (by simpa [hc] using h3)
  have hgood : lqKindA_GoodPath A.tau T c :=
    of_decide_eq_true ((List.all_eq_true.mp (lqKindA_checkPath_all A.tau T A.tau_eq)) c hcTable)
  obtain ⟨hp_len, hp_nd, hp_fs, hm12, hmF4, hmF4', hsq, hmat, hmu, hgap⟩ := hgood
  set pth := lqKindA_path T c with hpth
  set m := lqKindA_scale A.tau T c with hm
  have hpth_len : pth.length = c.length := by simpa [hpth] using hp_len
  have hpth_nd : pth.Nodup := by simpa [hpth] using hp_nd
  have hpth_fs : pth.toFinset = c.toFinset := by simpa [hpth] using hp_fs
  have hm12' : m = 1 ∨ m = 2 := by simpa [hm] using hm12
  have hm_ne : m ≠ 0 := by rcases hm12' with h | h <;> omega
  have hm_pos : 0 < m := by rcases hm12' with h | h <;> omega
  have hsq' : c.all (fun x => decide (iform (τ := A.tau) (lqExtRoot A.tau T x)
      (lqExtRoot A.tau T x) = 2 * m)) = true := by simpa [hm] using hsq
  have hmu' : c.all (fun x => decide (iform (τ := A.tau) (lqKindA_mu A.tau T c)
      (lqExtRoot A.tau T x) = m * ((c.length : ℤ) + 1) *
        (if x = pth.headD 0 then 1 else 0))) = true := by simpa [hm] using hmu
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
  have hq_apply_eta : ∀ i, e (e.symm (e i)) = e i := fun i => e.apply_symm_apply (e i)
  let ι : {x // x ∈ c} → Fin A.row.diagram.marks.length := fun x => ⟨x.1, hxlt x.1 x.2⟩
  let α : {x // x ∈ c} → (Fin A.tau.rank → ℤ) := fun x => A.nodeMap (Pi.single (ι x) 1)
  have hα_node : ∀ x : {x // x ∈ c}, α x = lqExtRoot A.tau T x.1 := fun x => lq_nodeMap_eq A (ι x)
  have hα_path : ∀ i : Fin c.length, α (e i) = lqExtRoot A.tau T (pathAt i) := by
    intro i
    rw [hα_node, he_val]
  have hψeq : ψ = {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ (Set.range α)} := by
    rw [hψ, P.repr_roots j]
    change {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ
      {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧ w = A.nodeMap (Pi.single i 1)}} = _
    have hset : {v | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
        v = A.nodeMap (Pi.single i 1)} = Set.range α := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i.val, hi⟩, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨ι x, x.2, rfl⟩
    rw [hset]
  have hroots : ∀ γ ∈ ψ, IsRoot A.tau γ := fun γ hγ => (hψeq ▸ hγ).1
  have hspan_path : ∀ γ ∈ ψ, γ ∈ Submodule.span ℤ (Set.range α) := fun γ hγ => (hψeq ▸ hγ).2
  have hcone := lqKindA_cone A P j hmem hzproper
  have hmaps : ∀ x : {x // x ∈ c}, (A.row.nodePerm^[s] (ι x)).val ∈ c := by
    rintro ⟨x, hx⟩
    have h := lqKindA_maps_c A P j A.tau_eq (by simpa [hT, hc] using hcTable) s hs
      (x := x) (by simpa [hc] using hx)
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
    have hσx := lqKindA_frob_nodes_iterate A s (ι x)
    have hσy := lqKindA_frob_nodes_iterate A s (ι y)
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
      exact lqKindA_iform_iterate A.setup s _ _
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
      rw [f1, f2, iform_smul_left, iform_smul_right, lqKindA_iform_iterate A.setup s]
      ring
  have hq_cartan : ∀ i j : Fin c.length,
      lqKindA_cartan c.length (q i) (q j) = lqKindA_cartan c.length i j := by
    intro i j
    have h1 : m * lqKindA_cartan c.length (q i) (q j) = iform (α (e (q i))) (α (e (q j))) := by
      rw [hα_path (q i), hα_path (q j)]
      exact (hmat (q i) (q j)).symm
    have h2 : iform (α (e (q i))) (α (e (q j))) = iform (α (e i)) (α (e j)) := by
      simp only [hq_apply]
      exact hppair (e i) (e j)
    have h3 : iform (α (e i)) (α (e j)) = m * lqKindA_cartan c.length i j := by
      rw [hα_path i, hα_path j]
      exact hmat i j
    exact mul_left_cancel₀ hm_ne (h1.trans (h2.trans h3))
  have hcls : (∀ i : Fin c.length, (A.row.nodePerm^[s] (ι (e i))).val = pathAt i) ∨
      (∀ i : Fin c.length,
        (A.row.nodePerm^[s] (ι (e i))).val = pathAt (lqKindA_rev c.length i)) := by
    rcases lqKindA_perm_cartan (r := c.length) (by omega) q hq_cartan with hq1 | hqrev
    · left
      intro i
      have h1 : q i = i := by rw [hq1]; rfl
      have h2 := hq_apply i
      rw [h1] at h2
      have h3 : (p (e i)).val = (e i).val := congrArg Subtype.val h2.symm
      rw [hpv (e i)] at h3
      exact h3
    · right
      intro i
      have h1 : q i = lqKindA_rev c.length i := by rw [hqrev]
      have h2 := hq_apply i
      rw [h1] at h2
      have h3 : (p (e i)).val = (e (lqKindA_rev c.length i)).val := congrArg Subtype.val h2.symm
      rw [hpv (e i)] at h3
      rw [h3]
      simp only [he_val, pathAt, lqKindA_rev_apply]
  have hscale_sum : ∀ n : {x // x ∈ c} → ℕ,
      iform (τ := A.tau) (∑ x, (n x : ℤ) • α x) (∑ x, (n x : ℤ) • α x) =
        m * (∑ i : Fin c.length, ∑ j : Fin c.length,
          (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ)) := by
    intro n
    have hsum : (∑ x : {x // x ∈ c}, (n x : ℤ) • α x) =
        ∑ i : Fin c.length, (n (e i) : ℤ) • α (e i) :=
      Fintype.sum_equiv (M := Fin A.tau.rank → ℤ) (e := e.symm)
        (f := fun x : {x // x ∈ c} => (n x : ℤ) • α x)
        (g := fun i : Fin c.length => (n (e i) : ℤ) • α (e i))
        (fun x => by rw [e.apply_symm_apply])
    rw [hsum, iform_finset_sum_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [iform_finset_sum_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [iform_smul_left, iform_smul_right, hα_path i, hα_path j, hmat i j]
    ring
  have hr8 : c.length ≤ 8 := by
    have hlt : c.length < A.row.diagram.marks.length := by
      have hsubs : c.toFinset ⊆ Finset.range A.row.diagram.marks.length := by
        intro x hx
        rw [List.mem_toFinset] at hx
        exact Finset.mem_range.mpr (hxlt x hx)
      have hne : c.toFinset ≠ Finset.range A.row.diagram.marks.length := by
        intro heq
        obtain ⟨i, hi, hni⟩ := hproper
        have : i ∈ c.toFinset := by rw [heq]; exact Finset.mem_range.mpr hi
        exact hni (List.mem_toFinset.mp this)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubs, hne⟩)
      rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
    have hml := lqKindA_marks_length_A A
    have hrank : A.tau.rank ≤ 8 := by
      rw [← A.tau_eq]
      cases hT' : A.row.T <;> simp [absTag, Tag.rank]
    omega
  have hQ2 : ∀ (n : {x // x ∈ c} → ℕ), 0 < (∑ i : Fin c.length, ∑ j : Fin c.length,
        (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ)) →
      2 ≤ ∑ i : Fin c.length, ∑ j : Fin c.length,
            (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ) := by
    intro n hpos
    obtain ⟨K, hK⟩ := lqKindA_cartan_even c.length hr8 (fun i => (n (e i) : ℤ))
    rw [hK] at hpos ⊢
    omega
  have htaucases : A.tau = .E6 ∨ A.tau = .E7 ∨ A.tau = .E8 ∨ A.tau = .F4 := by
    cases hT' : A.row.T
    · exact Or.inl (by rw [← A.tau_eq, hT']; rfl)
    · exact Or.inr (Or.inl (by rw [← A.tau_eq, hT']; rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← A.tau_eq, hT']; rfl)))
    · exact Or.inr (Or.inr (Or.inr (by rw [← A.tau_eq, hT']; rfl)))
  have hroot_norm2 : T ≠ .F4 → ∀ γ ∈ ψ, iform (τ := A.tau) γ γ = 2 := by
    intro hTne γ hγ
    obtain ⟨j, hj⟩ := iform_self_of_isRoot (hroots γ hγ)
    have h1 : A.tau.symmetrizer j j = 1 := by
      rcases htaucases with h | h | h | h
      · exact lqKindA_symm_one (Or.inl h) j
      · exact lqKindA_symm_one (Or.inr (Or.inl h)) j
      · exact lqKindA_symm_one (Or.inr (Or.inr h)) j
      · exfalso
        have habs : absTag T = .F4 := by rw [hT, A.tau_eq]; exact h
        exact hTne (lqKindA_absTag_eq_F4 habs)
    rw [h1] at hj
    simpa using hj
  have hroot_norm4 : T = .F4 → ∀ γ ∈ ψ, iform (τ := A.tau) γ γ = 2 ∨
      iform (τ := A.tau) γ γ = 4 := by
    intro hT4 γ hγ
    obtain ⟨j, hj⟩ := iform_self_of_isRoot (hroots γ hγ)
    have hτF4 : A.tau = .F4 := by rw [← A.tau_eq, ← hT, hT4]; rfl
    rcases lqKindA_symm_F4 hτF4 j with h2 | h1
    · right; rw [h2] at hj; simpa using hj
    · left; rw [h1] at hj; simpa using hj
  have hsl : ∀ γ ∈ ψ, iform (τ := A.tau) γ γ = 2 * m := by
    intro γ hγ
    have hvroot : IsRoot A.tau γ := hroots γ hγ
    have hγspan : γ ∈ Submodule.span ℤ (Set.range α) := hspan_path γ hγ
    have hpos := iform_self_pos_of_isRoot hvroot
    rcases hcone γ hvroot hγspan with ⟨n, hn⟩ | ⟨n, hn⟩
    ·
      have hQpos : 0 < ∑ i : Fin c.length, ∑ j : Fin c.length,
          (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ) := by
        rw [hn, hscale_sum n] at hpos
        rcases hm12' with h | h <;> nlinarith
      rcases hm12' with h | h
      ·
        have hTne : T ≠ .F4 := by intro h4; have := hmF4 h4; rw [h] at this; omega
        rw [h]
        have := hroot_norm2 hTne γ hγ
        simpa using this
      ·
        have hT4 : T = .F4 := hmF4' h
        have hQ2' := hQ2 n hQpos
        have heq : iform (τ := A.tau) γ γ = m * (∑ i : Fin c.length, ∑ j : Fin c.length,
            (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ)) := by
          rw [hn, hscale_sum n]
        rcases hroot_norm4 hT4 γ hγ with h2n | h4n
        · exfalso
          rw [h2n, h] at heq
          nlinarith [hQ2']
        · rw [h4n, h]; norm_num
    ·
      have hw : iform (τ := A.tau) (-(∑ x, (n x : ℤ) • α x)) (-(∑ x, (n x : ℤ) • α x)) =
          iform (τ := A.tau) (∑ x, (n x : ℤ) • α x) (∑ x, (n x : ℤ) • α x) := by
        have e1 : -(∑ x : {x // x ∈ c}, (n x : ℤ) • α x) =
            (-1 : ℤ) • (∑ x : {x // x ∈ c}, (n x : ℤ) • α x) := by rw [neg_one_smul]
        rw [e1, iform_smul_left, iform_smul_right]
        ring
      have hQpos : 0 < ∑ i : Fin c.length, ∑ j : Fin c.length,
          (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ) := by
        rw [hn, hw, hscale_sum n] at hpos
        rcases hm12' with h | h <;> nlinarith
      rcases hm12' with h | h
      · have hTne : T ≠ .F4 := by intro h4; have := hmF4 h4; rw [h] at this; omega
        rw [hn, hw, h]
        have hgn := hroot_norm2 hTne γ hγ
        rw [hn, hw] at hgn
        simpa using hgn
      · have hT4 : T = .F4 := hmF4' h
        have hQ2' := hQ2 n hQpos
        have heq : iform (τ := A.tau) γ γ = m * (∑ i : Fin c.length, ∑ j : Fin c.length,
            (n (e i) : ℤ) * lqKindA_cartan c.length i j * (n (e j) : ℤ)) := by
          rw [hn, hw, hscale_sum n]
        rcases hroot_norm4 hT4 γ hγ with h2n | h4n
        · exfalso
          rw [h2n, h] at heq
          nlinarith [hQ2']
        · rw [h4n, h]; norm_num
  have hpair_m : ∀ γ ∈ ψ, ∀ γ' ∈ ψ, m ∣ iform (τ := A.tau) γ γ' := by
    intro γ hγ γ' hγ'
    have hγspan : γ ∈ Submodule.span ℤ (Set.range α) := hspan_path γ hγ
    have hnode : ∀ x : {x // x ∈ c}, ∀ z ∈ ψ, m ∣ iform (τ := A.tau) (α x) z := by
      intro x z hz
      have hzspan : z ∈ Submodule.span ℤ (Set.range α) := hspan_path z hz
      refine Submodule.span_induction (p := fun w _ => m ∣ iform (τ := A.tau) (α x) w)
        ?_ ?_ ?_ ?_ hzspan
      · intro w hw
        obtain ⟨y, rfl⟩ := hw
        have hxe : x = e (e.symm x) := (e.apply_symm_apply x).symm
        have hye : y = e (e.symm y) := (e.apply_symm_apply y).symm
        rw [hxe, hye, hα_path (e.symm x), hα_path (e.symm y), hmat (e.symm x) (e.symm y)]
        exact dvd_mul_right m _
      · have h0 : iform (τ := A.tau) (α x) 0 = 0 := by
          simpa using iform_smul_right (0 : ℤ) (α x) 0
        rw [h0]; exact dvd_zero m
      · intro a b _ _ ha hb
        rw [iform_add_right]; exact dvd_add ha hb
      · intro a w _ hw
        rw [iform_smul_right]; exact Dvd.dvd.mul_left hw a
    refine (Submodule.span_induction (p := fun w _ => ∀ z ∈ ψ, m ∣ iform (τ := A.tau) w z)
      ?_ ?_ ?_ ?_ hγspan) γ' hγ'
    · intro w hw
      obtain ⟨x, rfl⟩ := hw
      exact hnode x
    · intro z hz
      have h0 : iform (τ := A.tau) 0 z = 0 := by
        simpa using iform_smul_left (0 : ℤ) 0 z
      rw [h0]; exact dvd_zero m
    · intro a b _ _ ha hb z hz
      rw [iform_add_left]; exact dvd_add (ha z hz) (hb z hz)
    · intro a w _ hw z hz
      rw [iform_smul_left]; exact Dvd.dvd.mul_left (hw z hz) a
  set μ : Fin A.tau.rank → ℤ := lqKindA_mu A.tau T c with hμ
  have hμ_eq : μ = ∑ i : Fin c.length, (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e i) := by
    rw [hμ]
    change (∑ i : Fin c.length, ((c.length - i.val : ℕ) : ℤ) •
      lqExtRoot A.tau T ((lqKindA_path T c).getD i.val 0)) = _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hα_path i]
  have hpth_ne : pth ≠ [] := by
    intro h
    have hlen := hpth_len
    rw [h] at hlen
    simp at hlen
    omega
  have hhead : (e ⟨0, by omega⟩).1 = pth.headD 0 := by
    rw [he_val]
    show pth.getD 0 0 = pth.headD 0
    cases pth <;> rfl

  have hmu_node : ∀ x : {x // x ∈ c}, iform (τ := A.tau) μ (α x) =
      m * ((c.length : ℤ) + 1) * (if x.1 = pth.headD 0 then 1 else 0) := by
    intro x
    have h := List.all_eq_true.mp hmu' x.1 x.2
    have hxe : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hxe, hα_path (e.symm x), e.apply_symm_apply]
    have hpath : pathAt (e.symm x) = x.1 := by
      rw [← he_val (e.symm x)]
      exact congrArg Subtype.val (e.apply_symm_apply x)
    rw [hpath]
    exact of_decide_eq_true h
  have hμd : ∀ z ∈ ψ, (m * ((c.length : ℤ) + 1)) ∣ iform (τ := A.tau) μ z := by
    intro z hz
    have hzspan : z ∈ Submodule.span ℤ (Set.range α) := hspan_path z hz
    refine Submodule.span_induction (p := fun w _ => (m * ((c.length : ℤ) + 1)) ∣
      iform (τ := A.tau) μ w) ?_ ?_ ?_ ?_ hzspan
    · intro w hw
      obtain ⟨x, rfl⟩ := hw
      rw [hmu_node x]
      exact dvd_mul_right _ _
    · have h0 : iform (τ := A.tau) μ 0 = 0 := by
        simpa using iform_smul_right (0 : ℤ) μ 0
      rw [h0]; exact dvd_zero _
    · intro a b _ _ ha hb
      rw [iform_add_right]; exact dvd_add ha hb
    · intro a w _ hw
      rw [iform_smul_right]; exact Dvd.dvd.mul_left hw a
  have hμspan : μ ∈ Submodule.span ℤ ψ := by
    rw [hμ_eq]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h1 : α (e i) ∈ {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ (Set.range α)} :=
      ⟨A.node_isRoot (ι (e i)), Submodule.subset_span (Set.mem_range_self (e i))⟩
    rw [← hψeq] at h1
    exact Submodule.subset_span h1
  have hμμ : iform (τ := A.tau) μ μ = (c.length : ℤ) * m * ((c.length : ℤ) + 1) := by
    have hstep : iform (τ := A.tau) μ μ = iform (τ := A.tau) μ
        (∑ i : Fin c.length, (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e i)) := by rw [hμ_eq]
    rw [hstep, iform_finset_sum_right]
    have hstep2 : (∑ i : Fin c.length,
        iform (τ := A.tau) μ ((((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e i))) =
        ∑ i : Fin c.length,
          ((((c.length : ℕ) - i.val : ℕ) : ℤ) * iform (τ := A.tau) μ (α (e i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [iform_smul_right]
    rw [hstep2, Finset.sum_eq_single (a := (⟨0, by omega⟩ : Fin c.length))]
    · have h0 := hmu_node (e ⟨0, by omega⟩)
      rw [if_pos hhead] at h0
      have hv : (((c.length : ℕ) - (⟨0, by omega⟩ : Fin c.length).val : ℕ) : ℤ) =
          (c.length : ℤ) := by simp
      rw [hv, h0]
      ring
    · intro b _ hb
      have hb0 := hmu_node (e b)
      have hbe : (e b).1 ≠ pth.headD 0 := by
        intro h
        have h1 : e b = e ⟨0, by omega⟩ := Subtype.ext (by rw [h, hhead])
        exact hb (e.injective h1)
      rw [if_neg hbe] at hb0
      rw [hb0]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  let φ : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ) :=
    ((A.frobLinear ^ s : (Fin A.tau.rank → ℤ) ≃ₗ[ℤ] (Fin A.tau.rank → ℤ)).toLinearMap
      ).toAddMonoidHom
  have hφρ : ∀ γ ∈ ψ, ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[s]) γ = φ γ := by
    intro γ hγ
    rw [lqKindA_rho_iterate_frobLinear A s (hroots γ hγ)]
    exact (LinearEquiv.pow_apply A.frobLinear s γ).symm
  set el : ℤ := A.epsilon ^ s with hel
  have hel12 : el = 1 ∨ el = -1 := by
    have hε : A.epsilon = 1 ∨ A.epsilon = -1 := by rw [A.epsilon_eq]; split <;> simp
    rcases hε with hε | hε
    · exact Or.inl (by rw [hel, hε, one_pow])
    · rcases Nat.even_or_odd s with he | ho
      · exact Or.inl (by rw [hel, hε]; exact he.neg_one_pow)
      · exact Or.inr (by rw [hel, hε]; exact ho.neg_one_pow)
  set ee : ℤ := (c.length : ℤ) + 1 with hee
  set d : ℤ := m * ee with hd
  have hd_ne : d ≠ 0 := by
    rw [hd, hee]
    rcases hm12' with h | h <;> rw [h] <;> (have := h3'; nlinarith)
  have hd_pos : 0 < d := by
    rw [hd, hee]
    rcases hm12' with h | h <;> rw [h] <;> (have := h3'; nlinarith)
  have hct : k0CompType (k0DiagOf T) c = (.A, c.length) := by
    refine Prod.ext hcA ?_
    have := lq_compType_A_rank (k0DiagOf T) c hcA
    simpa using this
  have htau0 : k0Tau0Of (k0CompType (k0DiagOf T) c).1 (k0CompType (k0DiagOf T) c).2 = true := by
    rw [hct]; simp [k0Tau0Of]; omega
  have hct' : k0CompType (k0DiagOf T) ((P.orbitNodes j).headD []) = (.A, c.length) := by
    change k0CompType (k0DiagOf T) (lqNodes A P j) = (.A, c.length)
    rw [← hc]
    exact hct
  have htau0A : k0Tau0Of .A c.length = true := by
    rw [k0Tau0Of]
    exact decide_eq_true (by omega)
  have ho_one : (∀ i : Fin c.length, (A.row.nodePerm^[s] (ι (e i))).val = pathAt i) →
      k0AutOrder c (k0pPow A.row.rho s) = 1 := by
    intro hfix
    refine lqKindA_autOrder_one c (k0pPow A.row.rho s) ?_
    intro x hx
    rw [lqKindA_k0pPow_getD_nodePerm A s ⟨x, hxlt x hx⟩]
    let k : Fin c.length := e.symm ⟨x, hx⟩
    have hk : e k = ⟨x, hx⟩ := e.apply_symm_apply _
    have h := hfix k
    rw [hk] at h
    have hkval : pathAt k = x := by rw [← he_val k, hk]
    rw [hkval] at h
    exact h
  have ho_two : (∀ i : Fin c.length, (A.row.nodePerm^[s] (ι (e i))).val =
      pathAt (lqKindA_rev c.length i)) → k0AutOrder c (k0pPow A.row.rho s) = 2 := by
    intro hrev
    refine lqKindA_autOrder_two c (k0pPow A.row.rho s) ?_ ?_
    · intro hfix
      let i0 : Fin c.length := ⟨0, by omega⟩
      have hx : pathAt i0 ∈ c := hpathAt_mem i0
      have h0 : (A.row.nodePerm^[s] (ι (e i0))).val = pathAt i0 := by
        have h := hfix (ι (e i0)).val hx
        rw [lqKindA_k0pPow_getD_nodePerm A s (ι (e i0))] at h
        exact h
      have h1 := hrev i0
      have h2 : pathAt (lqKindA_rev c.length i0) = pathAt i0 := h1.symm.trans h0
      have h3 := hpathAt_inj h2
      have h4 : (lqKindA_rev c.length i0).val = i0.val := congrArg Fin.val h3
      rw [lqKindA_rev_apply] at h4
      have hi0 : i0.val = 0 := rfl
      rw [hi0] at h4
      omega
    · intro x hx
      rw [lqKindA_k0pMul_getD _ _
        (by rw [lqKindA_k0pPow_length, A.row.rho_length]; exact hxlt x hx)]
      rw [lqKindA_k0pPow_getD_nodePerm A s ⟨x, hxlt x hx⟩]
      let k : Fin c.length := e.symm ⟨x, hx⟩
      have hk : e k = ⟨x, hx⟩ := e.apply_symm_apply _
      have h1 := hrev k
      have h2 := hrev (lqKindA_rev c.length k)
      have hkk : (A.row.nodePerm^[s] (ι (e k))).val = pathAt (lqKindA_rev c.length k) := h1
      have hnode1 : A.row.nodePerm^[s] (ι (e k)) = ι (e (lqKindA_rev c.length k)) := by
        apply Fin.ext
        show (A.row.nodePerm^[s] (ι (e k))).val =
          (e (lqKindA_rev c.length k)).val
        rw [h1, he_val]
      have hnode2 : A.row.nodePerm^[s] (ι (e (lqKindA_rev c.length k))) =
          ι (e (lqKindA_rev c.length (lqKindA_rev c.length k))) := by
        apply Fin.ext
        show (A.row.nodePerm^[s] (ι (e (lqKindA_rev c.length k)))).val =
          (e (lqKindA_rev c.length (lqKindA_rev c.length k))).val
        rw [h2, he_val]
      have hperm2 : A.row.nodePerm^[s] (A.row.nodePerm^[s] (ι (e k))) =
          ι (e (lqKindA_rev c.length (lqKindA_rev c.length k))) := by
        rw [hnode1, hnode2]
      have hrev2 : lqKindA_rev c.length (lqKindA_rev c.length k) = k :=
        lqKindA_rev_invol c.length k
      have hxe : (⟨x, hx⟩ : {x // x ∈ c}) = e k := hk.symm
      have hgoal : (A.row.nodePerm^[s] (A.row.nodePerm^[s] (ι ⟨x, hx⟩))).val = x := by
        rw [hxe, hperm2, hrev2, hk]
      have hy : (A.row.nodePerm^[s] (ι ⟨x, hx⟩)).val ∈ c := hmaps ⟨x, hx⟩
      rw [lqKindA_k0pPow_getD_nodePerm A s
        ⟨(A.row.nodePerm^[s] (ι ⟨x, hx⟩)).val, hxlt _ hy⟩]
      have hii : (⟨(A.row.nodePerm^[s] (ι ⟨x, hx⟩)).val, hxlt _ hy⟩
          : Fin A.row.diagram.marks.length) = A.row.nodePerm^[s] (ι ⟨x, hx⟩) := Fin.ext rfl
      rw [hii]
      exact hgoal
  have htw : lqTw A P j =
      (if A.row.d = 2 ∧ (P.orbitNodes j).length % 2 = 1 then
        (if k0AutOrder c (k0pPow A.row.rho (P.orbitNodes j).length) = 1 then 2
         else if k0AutOrder c (k0pPow A.row.rho (P.orbitNodes j).length) = 2 then 1
         else k0AutOrder c (k0pPow A.row.rho (P.orbitNodes j).length))
       else k0AutOrder c (k0pPow A.row.rho (P.orbitNodes j).length)) := by
    simp only [lqTw]
    rw [hct']
    simp only [htau0A, eq_self_iff_true, and_true]
    rfl
  have hel_bridge : el = (if A.row.d = 1 then (1 : ℤ) else -1) ^ s := by
    rw [hel, A.epsilon_eq]
  have hbridge : lqTw A P j = 1 ↔
      (k0AutOrder c (k0pPow A.row.rho s) = 1 ∧ el = 1) ∨
      (k0AutOrder c (k0pPow A.row.rho s) = 2 ∧ el = -1) := by
    rw [htw, ← hs]
    exact lqKindA_bridge_arith (d := A.row.d) (s := s)
      (o := k0AutOrder c (k0pPow A.row.rho s)) (e := el)
      (by rw [A.row.d_eq]; split <;> simp) hel_bridge
      (by
        rcases hcls with hfix | hrev
        · exact Or.inl (ho_one hfix)
        · exact Or.inr (ho_two hrev))
  have hαroot : ∀ x : {x // x ∈ c}, IsRoot A.tau (α x) := fun x => A.node_isRoot (ι x)
  have hαψ : ∀ x : {x // x ∈ c}, α x ∈ ψ := by
    intro x
    rw [hψeq]
    exact ⟨hαroot x, Submodule.subset_span (Set.mem_range_self x)⟩
  have hLIα : LinearIndependent ℚ (fun x : {x // x ∈ c} =>
      fun j => ((α x j : ℤ) : ℚ)) := by
    have h := lq_extRoot_independent A.tau T (by rw [hT]; exact A.tau_eq) c hnd
      (by simpa [hT] using hxlt) (by simpa [hT] using hproper)
    simpa [hα_node] using h
  have hσi : ∀ i : Fin c.length,
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) (α (e i)) =
        el • α (e (q i)) := by
    intro i
    have h := lqKindA_frob_nodes_iterate A s (ι (e i))
    have hnx : (A.row.nodePerm^[s] (ι (e i))) = ι (e (q i)) := by
      refine Fin.ext ?_
      rw [hq_apply i]
      exact (hpv (e i)).symm
    simpa [hel, hnx] using h
  have hφ_apply : ∀ i : Fin c.length, φ (α (e i)) = el • α (e (q i)) := by
    intro i
    rw [← hφρ (α (e i)) (hαψ (e i))]
    exact hσi i
  have hφsum : φ μ = el • ∑ i : Fin c.length,
      (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e (q i)) := by
    rw [hμ_eq, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hφ_apply i, smul_comm]
  have hpair_gen : ∀ n : Fin c.length → ℤ,
      iform (τ := A.tau) μ (∑ i, n i • α (e i)) = m * ee * n ⟨0, by omega⟩ := by
    intro n
    rw [iform_finset_sum_right]
    rw [Finset.sum_eq_single (a := (⟨0, by omega⟩ : Fin c.length))]
    · rw [iform_smul_right]
      have h := hmu_node (e ⟨0, by omega⟩)
      rw [if_pos hhead] at h
      rw [h, hee]
      ring
    · intro b _ hb
      have hb0 := hmu_node (e b)
      have hbe : (e b).1 ≠ pth.headD 0 := by
        intro h
        have h1 : e b = e ⟨0, by omega⟩ := Subtype.ext (by rw [h, hhead])
        exact hb (e.injective h1)
      rw [if_neg hbe] at hb0
      rw [iform_smul_right, hb0]
      ring
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hvec0 : (((c.length : ℕ) -
      (lqKindA_rev c.length (⟨0, by omega⟩ : Fin c.length)).val : ℕ) : ℤ) = 1 := by
    rw [lqKindA_rev_apply]
    simp only [Fin.val_zero]
    have h : c.length - (c.length - 1 - 0) = 1 := by omega
    rw [h]
    norm_num
  have hpair_rev : iform (τ := A.tau) μ
      (∑ i : Fin c.length,
        (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e (lqKindA_rev c.length i))) = m * ee := by
    have hre : (∑ i : Fin c.length,
        (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e (lqKindA_rev c.length i))) =
        ∑ i : Fin c.length,
          (((c.length : ℕ) - (lqKindA_rev c.length i).val : ℕ) : ℤ) • α (e i) := by
      refine Fintype.sum_equiv (lqKindA_rev c.length)
        (fun i => (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e (lqKindA_rev c.length i)))
        (fun j => (((c.length : ℕ) - (lqKindA_rev c.length j).val : ℕ) : ℤ) • α (e j)) ?_
      intro i
      rw [lqKindA_rev_invol]
    rw [hre,
      hpair_gen (fun i => (((c.length : ℕ) - (lqKindA_rev c.length i).val : ℕ) : ℤ)), hvec0]
    ring
  have hee_pos : 0 < ee := by rw [hee]; positivity
  have hmul_ne : m * ee ≠ 0 := mul_ne_zero (ne_of_gt hm_pos) (ne_of_gt hee_pos)
  have hμd' : ∀ z ∈ ψ, d ∣ iform (τ := A.tau) μ z := by
    intro z hz
    rw [hd, hee]
    exact hμd z hz
  have hnot_dvd_two : ¬ (d * ee : ℤ) ∣ -2 * ((c.length : ℤ) * m * ee) := by
    intro hdiv
    have hd' : d * ee = m * ee * ee := by rw [hd]
    rw [hd'] at hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hk' : m * ee * (-2 * (c.length : ℤ)) = m * ee * (ee * k) := by
      calc m * ee * (-2 * (c.length : ℤ)) = -2 * ((c.length : ℤ) * m * ee) := by ring
        _ = (m * ee * ee) * k := hk
        _ = m * ee * (ee * k) := by ring
    have h2 := mul_left_cancel₀ hmul_ne hk'
    have hdvd : ee ∣ 2 * (c.length : ℤ) := ⟨-k, by linear_combination -h2⟩
    exact lqKindA_not_dvd_two c.length h3' (hee ▸ hdvd)
  have hnot_dvd_pred : ¬ (d * ee : ℤ) ∣ m * ee * (1 - (c.length : ℤ)) := by
    intro hdiv
    have hd' : d * ee = m * ee * ee := by rw [hd]
    rw [hd'] at hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hk' : m * ee * (1 - (c.length : ℤ)) = m * ee * (ee * k) := by
      calc m * ee * (1 - (c.length : ℤ)) = m * ee * ee * k := hk
        _ = m * ee * (ee * k) := by ring
    have h2 := mul_left_cancel₀ hmul_ne hk'
    have hdvd : ee ∣ (c.length : ℤ) - 1 := ⟨-k, by linear_combination -h2⟩
    exact lqKindA_not_dvd_pred c.length h3' (hee ▸ hdvd)
  let negHom : (Fin A.tau.rank → ℤ) →+ (Fin A.tau.rank → ℤ) :=
    { toFun := fun z => -z
      map_zero' := by simp
      map_add' := by intro a b; abel }
  have hnegHom : ∀ z, negHom z = -z := fun z => rfl
  have hnotInnerNeg : ¬ twistInner ψ (negHom : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) := by
    refine lqKindA_not_twistInner_of_disc (Ψ := ψ) m hm_pos hroots hsl hpair_m negHom
      (d := d) (e := ee) hd (μ := μ) (ν := μ) hμspan hμd' hμd' ?_
    have hval : iform (τ := A.tau) μ (negHom μ - μ) = -2 * ((c.length : ℤ) * m * ee) := by
      rw [hnegHom]
      have h2 : -μ - μ = (-2 : ℤ) • μ := by module
      rw [h2, iform_smul_right, hμμ]
    rw [hval]
    exact hnot_dvd_two
  have hinner_id (hq : q = 1) (hel : el = 1) :
      twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
    have hφ1 : ∀ x : {x // x ∈ c}, φ (α x) = α x := by
      intro x
      obtain ⟨i, rfl⟩ := e.surjective x
      rw [hφ_apply i, hq, hel]
      simp
    have hφfix : ∀ z ∈ Submodule.span ℤ (Set.range α), φ z = z := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => φ z = z) ?_ ?_ ?_ ?_ hz
      · intro y hy
        obtain ⟨x, rfl⟩ := hy
        exact hφ1 x
      · simp
      · intro a b _ _ ha hb
        rw [map_add, ha, hb]
      · intro n y _ hy
        rw [map_zsmul, hy]
    refine (lqKindA_twistInner_congr
      (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]))
      (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).mpr ?_
    refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
    rw [hφfix γ (hspan_path γ hγ)]
    simp
  have houter_id (hq : q = 1) (hel : el = -1) :
      ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
    have hφμ : φ μ = -μ := by
      rw [hφsum, hq, hel]
      simp only [Equiv.Perm.one_apply]
      rw [neg_one_smul, ← hμ_eq]
    have hval : iform (τ := A.tau) μ (φ μ - μ) = -2 * ((c.length : ℤ) * m * ee) := by
      rw [hφμ]
      have h2 : -μ - μ = (-2 : ℤ) • μ := by module
      rw [h2, iform_smul_right, hμμ]
    refine (lqKindA_twistInner_congr
      (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]))
      (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).not.mpr ?_
    refine lqKindA_not_twistInner_of_disc (Ψ := ψ) m hm_pos hroots hsl hpair_m φ
      (d := d) (e := ee) hd (μ := μ) (ν := μ) hμspan hμd' hμd' ?_
    rw [hval]
    exact hnot_dvd_two
  have houter_rev (hq : q = lqKindA_rev c.length) (hel : el = 1) :
      ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
    have hφμ : φ μ = ∑ i : Fin c.length,
        (((c.length : ℕ) - i.val : ℕ) : ℤ) • α (e (lqKindA_rev c.length i)) := by
      rw [hφsum, hq, hel]
      simp
    have hval : iform (τ := A.tau) μ (φ μ - μ) = m * ee * (1 - (c.length : ℤ)) := by
      rw [hφμ, iform_sub_right, hpair_rev, hμμ]
      ring
    refine (lqKindA_twistInner_congr
      (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]))
      (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).not.mpr ?_
    refine lqKindA_not_twistInner_of_disc (Ψ := ψ) m hm_pos hroots hsl hpair_m φ
      (d := d) (e := ee) hd (μ := μ) (ν := μ) hμspan hμd' hμd' ?_
    rw [hval]
    exact hnot_dvd_pred
  have hinner_rev (hq : q = lqKindA_rev c.length) (hel : el = -1) :
      twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]) := by
    obtain ⟨w, hw, opp, hwα⟩ := lq_longest (τ := A.tau) (α := α) hαroot hLIα hcone
    let qopp : Equiv.Perm (Fin c.length) := (e.trans opp).trans e.symm
    have hqopp_apply : ∀ i : Fin c.length, e (qopp i) = opp (e i) := by
      intro i
      simp [qopp]
    have hqopp_cartan : ∀ i j : Fin c.length,
        lqKindA_cartan c.length (qopp i) (qopp j) = lqKindA_cartan c.length i j := by
      intro i j
      have h1 : iform (τ := A.tau) (α (e (qopp i))) (α (e (qopp j))) =
          iform (τ := A.tau) (α (e i)) (α (e j)) := by
        have h := iform_smul w (α (e i)) (α (e j))
        rw [hwα (e i), hwα (e j)] at h
        have h' : iform (τ := A.tau) (α (opp (e i))) (α (opp (e j))) =
            iform (τ := A.tau) (α (e i)) (α (e j)) := by
          have e1 : -α (opp (e i)) = (-1 : ℤ) • α (opp (e i)) := by rw [neg_one_smul]
          have e2 : -α (opp (e j)) = (-1 : ℤ) • α (opp (e j)) := by rw [neg_one_smul]
          rw [e1, e2, iform_smul_left, iform_smul_right] at h
          norm_num at h
          exact h
        rw [hqopp_apply i, hqopp_apply j]
        exact h'
      have h2 : m * lqKindA_cartan c.length (qopp i) (qopp j) =
          iform (τ := A.tau) (α (e (qopp i))) (α (e (qopp j))) := by
        rw [hα_path (qopp i), hα_path (qopp j)]
        exact (hmat (qopp i) (qopp j)).symm
      have h3 : m * lqKindA_cartan c.length i j =
          iform (τ := A.tau) (α (e i)) (α (e j)) := by
        rw [hα_path i, hα_path j]
        exact (hmat i j).symm
      exact mul_left_cancel₀ hm_ne (h2.trans (h1.trans h3.symm))
    have hclosure_sub : Subgroup.closure {s : WeylGroup A.tau | ∃ γ : Fin A.tau.rank → ℤ,
          IsRoot A.tau γ ∧ γ ∈ Submodule.span ℤ (Set.range α) ∧ s = rootReflection γ} ≤
        Subgroup.closure {s : WeylGroup A.tau | ∃ γ ∈ ψ, s = rootReflection γ} := by
      apply Subgroup.closure_mono
      rintro s ⟨γ, hγroot, hγspan, rfl⟩
      refine ⟨γ, ?_, rfl⟩
      rw [hψeq]
      exact ⟨hγroot, hγspan⟩
    rcases lqKindA_perm_cartan (r := c.length) (by omega) qopp hqopp_cartan with
      hqopp1 | hqopprev
    · exfalso
      have hopp1 : opp = 1 := by
        ext x
        obtain ⟨i, rfl⟩ := e.surjective x
        rw [← hqopp_apply i, hqopp1]
        simp
      apply hnotInnerNeg
      refine ⟨w, hclosure_sub hw, fun γ hγ => ?_⟩
      have hwneg : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = -z := by
        intro z hz
        refine Submodule.span_induction (p := fun z _ => w • z = -z) ?_ ?_ ?_ ?_ hz
        · intro y hy
          obtain ⟨x, rfl⟩ := hy
          rw [hwα x, hopp1]
          simp
        · simp
        · intro a b _ _ ha hb
          rw [smul_add, ha, hb]
          abel
        · intro n y _ hy
          rw [show w • (n • y) = n • (w • y) from (smul_comm (n : ℤ) w y).symm, hy,
            smul_neg]
      show negHom γ = w • γ
      rw [hnegHom, hwneg γ (hspan_path γ hγ)]
    · have hwφ : ∀ z ∈ Submodule.span ℤ (Set.range α), w • z = φ z := by
        intro z hz
        refine Submodule.span_induction (p := fun z _ => w • z = φ z) ?_ ?_ ?_ ?_ hz
        · intro y hy
          obtain ⟨x, rfl⟩ := hy
          obtain ⟨i, rfl⟩ := e.surjective x
          have h1 : opp (e i) = e (lqKindA_rev c.length i) := by
            rw [← hqopp_apply i, hqopprev]
          rw [hwα (e i), h1, hφ_apply i, hq, hel]
          simp
        · simp
        · intro a b _ _ ha hb
          rw [smul_add, map_add, ha, hb]
        · intro n y _ hy
          rw [show w • (n • y) = n • (w • y) from (smul_comm (n : ℤ) w y).symm, hy,
            map_zsmul]
      refine (lqKindA_twistInner_congr
        (σ := ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[s]))
        (σ' := (φ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))) hφρ).mpr ?_
      refine ⟨w, hclosure_sub hw, fun γ hγ => ?_⟩
      exact (hwφ γ (hspan_path γ hγ)).symm
  have hcompRank : compRank ψ = c.length := by
    let toRat : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℚ) := fun γ i => (γ i : ℚ)
    have htoRat_zero : toRat (0 : Fin A.tau.rank → ℤ) = 0 := by
      funext i
      simp [toRat]
    have htoRat_add : ∀ a b, toRat (a + b) = toRat a + toRat b := by
      intro a b
      funext i
      simp [toRat]
    have htoRat_smul : ∀ (n : ℤ) (a), toRat (n • a) = (n : ℚ) • toRat a := by
      intro n a
      funext i
      simp [toRat]
    have hmem : ∀ γ ∈ ψ, toRat γ ∈
        Submodule.span ℚ (Set.range (fun i : Fin c.length => toRat (α (e i)))) := by
      intro γ hγ
      have hγspan := hspan_path γ hγ
      refine Submodule.span_induction
        (p := fun z _ => toRat z ∈
          Submodule.span ℚ (Set.range (fun i : Fin c.length => toRat (α (e i)))))
        ?_ ?_ ?_ ?_ hγspan
      · intro y hy
        obtain ⟨x, rfl⟩ := hy
        obtain ⟨i, rfl⟩ := e.surjective x
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [htoRat_zero]
        exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [htoRat_add]
        exact Submodule.add_mem _ ha hb
      · intro n y _ hy
        rw [htoRat_smul]
        exact Submodule.smul_mem _ _ hy
    have hgen : ∀ i : Fin c.length, toRat (α (e i)) ∈ Submodule.span ℚ (toRat '' ψ) :=
      fun i => Submodule.subset_span ⟨α (e i), hαψ (e i), rfl⟩
    have hspan_eq : Submodule.span ℚ (toRat '' ψ) =
        Submodule.span ℚ (Set.range (fun i : Fin c.length => toRat (α (e i)))) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro v ⟨γ, hγ, rfl⟩
        exact hmem γ hγ
      · rw [Submodule.span_le]
        rintro v ⟨i, rfl⟩
        exact hgen i
    have hLIg : LinearIndependent ℚ (fun i : Fin c.length => toRat (α (e i))) :=
      hLIα.comp (fun i => e i) e.injective
    unfold compRank
    show Module.finrank ℚ (Submodule.span ℚ (toRat '' ψ)) = c.length
    rw [hspan_eq, finrank_span_eq_card hLIg, Fintype.card_fin]
  have hcard : ψ.ncard = c.length * (c.length + 1) := by
    rw [hψ]
    exact hn
  have hslen : componentOrbitLength A.setup.ρ ψ = s := by
    rw [hψ, P.orbit_length j, ← hs]
  have hexc : ¬ ((compRank ψ = 6 ∧ ψ.ncard = 72) ∨
      (compRank ψ = 4 ∧ ψ.ncard = 24 ∧
        ¬ twistInner ψ ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[2 * s]))) := by
    rintro (⟨h6, h72⟩ | ⟨h4, h24, -⟩)
    · rw [hcompRank] at h6
      rw [hcard, h6] at h72
      norm_num at h72
    · rw [hcompRank] at h4
      rw [hcard, h4] at h24
      norm_num at h24
  have htwoD : ¬ (4 ≤ compRank ψ ∧
      ψ.ncard = 2 * compRank ψ * (compRank ψ - 1)) := by
    rintro ⟨h4, hcard2⟩
    rw [hcompRank] at h4
    rw [hcard, hcompRank] at hcard2
    have hlin : c.length + 1 = 2 * (c.length - 1) := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < c.length) ?_
      calc c.length * (c.length + 1) = 2 * c.length * (c.length - 1) := hcard2
        _ = c.length * (2 * (c.length - 1)) := by ring
    omega
  have hsuN : 2 ≤ compRank ψ ∧ ψ.ncard = compRank ψ * (compRank ψ + 1) := by
    constructor
    · rw [hcompRank]; omega
    · rw [hcard, hcompRank]
  have hq1_of_fix : (∀ i : Fin c.length,
      (A.row.nodePerm^[s] (ι (e i))).val = pathAt i) → q = 1 := by
    intro hfix
    refine Equiv.ext fun i => ?_
    have h1 : e (q i) = e i := by
      apply Subtype.ext
      rw [hq_apply i, hpv (e i), hfix i, he_val i]
    exact e.injective h1
  have hqrev_of_rev : (∀ i : Fin c.length,
      (A.row.nodePerm^[s] (ι (e i))).val = pathAt (lqKindA_rev c.length i)) →
      q = lqKindA_rev c.length := by
    intro hrev
    refine Equiv.ext fun i => ?_
    have h1 : e (q i) = e (lqKindA_rev c.length i) := by
      apply Subtype.ext
      rw [hq_apply i, hpv (e i), hrev i, he_val (lqKindA_rev c.length i)]
    exact e.injective h1
  rcases hcls with hfix | hrev
  · have hq1 : q = 1 := hq1_of_fix hfix
    constructor
    · intro htw1
      have hel1 : el = 1 := by
        rcases hbridge.mp htw1 with ⟨-, he1⟩ | ⟨ho2, -⟩
        · exact he1
        · exfalso
          have h1 := ho_one hfix
          omega
      unfold twistKind
      rw [hslen, if_pos (hinner_id hq1 hel1)]
    · intro htwne
      have helm1 : el = -1 := by
        rcases hel12 with he | he
        · exfalso
          exact htwne (hbridge.mpr (Or.inl ⟨ho_one hfix, he⟩))
        · exact he
      unfold twistKind
      rw [hslen, if_neg (houter_id hq1 helm1), if_neg hexc, if_neg htwoD, if_pos hsuN]
  · have hqrev : q = lqKindA_rev c.length := hqrev_of_rev hrev
    constructor
    · intro htw1
      have helm1 : el = -1 := by
        rcases hbridge.mp htw1 with ⟨ho1, -⟩ | ⟨-, he2⟩
        · exfalso
          have h2 := ho_two hrev
          omega
        · exact he2
      unfold twistKind
      rw [hslen, if_pos (hinner_rev hqrev helm1)]
    · intro htwne
      have hel1 : el = 1 := by
        rcases hel12 with he | he
        · exact he
        · exfalso
          exact htwne (hbridge.mpr (Or.inr ⟨ho_two hrev, he⟩))
      unfold twistKind
      rw [hslen, if_neg (houter_rev hqrev hel1), if_neg hexc, if_neg htwoD, if_pos hsuN]

theorem lq_kind_A (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h3 : 3 ≤ (lqNodes A P j).length)
    (hA : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A)
    (hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      (lqNodes A P j).length * ((lqNodes A P j).length + 1)) :
    (lqTw A P j = 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner) ∧
      (lqTw A P j ≠ 1 → twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .suN) := by
  exact lqKindA_aux A P j h3 hA hn

end CFSG.StandardType.GGK0LQ

end
