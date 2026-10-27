module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLabel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSimple
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ROrbLen

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Aux

theorem gk_fold_zipWith_getD (j : ℕ) : ∀ (l : List (List ℤ)) (acc : List ℤ),
    (∀ x ∈ l, j < x.length) → j < acc.length →
    (l.foldl (List.zipWith (· + ·)) acc).getD j 0 =
      acc.getD j 0 + (l.map fun x => x.getD j 0).sum := by
  intro l
  induction l with
  | nil => intro acc _ _; simp
  | cons x l ih =>
    intro acc hx hacc
    have hxj : j < x.length := hx x List.mem_cons_self
    have hzip : j < (List.zipWith (· + ·) acc x).length := by
      simp only [List.length_zipWith]; omega
    rw [List.foldl_cons, ih _ (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hzip]
    have hz : (List.zipWith (· + ·) acc x).getD j 0 = acc.getD j 0 + x.getD j 0 := by
      rw [List.getD_eq_getElem _ _ hzip, List.getD_eq_getElem _ _ hacc,
        List.getD_eq_getElem _ _ hxj, List.getElem_zipWith]
    rw [hz, List.map_cons, List.sum_cons]
    ring

theorem gk_getD_map_mul (c : ℤ) (v : List ℤ) (j : ℕ) :
    (v.map fun x => c * x).getD j 0 = c * v.getD j 0 := by
  by_cases hj : j < v.length
  · have hj' : j < (v.map fun x => c * x).length := by simpa using hj
    rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj, List.getElem_map]
  · have hj' : (v.map fun x => c * x).length ≤ j := by simp; omega
    have hj'' : v.length ≤ j := by omega
    rw [List.getD_eq_default _ _ hj', List.getD_eq_default _ _ hj'']
    simp

theorem gk_zipWith_smul_getD (j : ℕ) : ∀ (cs : List ℤ) (vs : List (List ℤ)),
    (List.zipWith (fun c v => v.map fun x => c * x) cs vs).map (fun x => x.getD j 0) =
      List.zipWith (fun c v => c * v.getD j 0) cs vs := by
  intro cs
  induction cs with
  | nil => intro vs; simp
  | cons c cs ih =>
    intro vs
    cases vs with
    | nil => simp
    | cons v vs => simp only [List.zipWith_cons_cons, List.map_cons, ih vs, gk_getD_map_mul]

theorem gk_zipWith_eq_range (f : ℤ → List ℤ → ℤ) (cs : List ℤ) (vs : List (List ℤ))
    (hlen : cs.length = vs.length) :
    List.zipWith f cs vs = (List.range cs.length).map fun k => f (cs.getD k 0) (vs.getD k []) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro k h1 h2
    have hk : k < cs.length := by
      simp only [List.length_zipWith] at h1
      omega
    have hk' : k < vs.length := by omega
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk']

theorem gk_list_sum_range (g : ℕ → ℤ) (m : ℕ) :
    ((List.range m).map g).sum = ∑ k ∈ Finset.range m, g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem gk_mem_zipWith_smul : ∀ (cs : List ℤ) (vs : List (List ℤ)) (x : List ℤ),
    x ∈ List.zipWith (fun c v => v.map fun y => c * y) cs vs →
      ∃ v ∈ vs, x.length = v.length := by
  intro cs
  induction cs with
  | nil => intro vs x hx; simp at hx
  | cons c cs ih =>
    intro vs x hx
    cases vs with
    | nil => simp at hx
    | cons v vs =>
      rw [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨v, List.mem_cons_self, by simp⟩
      · obtain ⟨v', hv', hl⟩ := ih vs x hx
        exact ⟨v', List.mem_cons_of_mem _ hv', hl⟩

theorem gk_fold_length (n : ℕ) : ∀ (l : List (List ℤ)) (acc : List ℤ),
    (∀ x ∈ l, x.length = n) → acc.length = n →
    (l.foldl (List.zipWith (· + ·)) acc).length = n := by
  intro l
  induction l with
  | nil => intro acc _ h; simpa using h
  | cons x l ih =>
    intro acc hx hacc
    rw [List.foldl_cons]
    apply ih _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    simp [hacc, hx x List.mem_cons_self]

theorem gk_lincomb_length (n : ℕ) (cs : List ℤ) (vs : List (List ℤ))
    (hv : ∀ v ∈ vs, v.length = n) : (tcrLincomb n cs vs).length = n := by
  unfold tcrLincomb
  apply gk_fold_length n
  · intro x hx
    obtain ⟨v, hv', hl⟩ := gk_mem_zipWith_smul cs vs x hx
    rw [hl, hv v hv']
  · simp

theorem gk_lincomb_getD (n : ℕ) (cs : List ℤ) (vs : List (List ℤ)) (hlen : cs.length = vs.length)
    (hv : ∀ v ∈ vs, v.length = n) (j : ℕ) (hj : j < n) :
    (tcrLincomb n cs vs).getD j 0 =
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 * (vs.getD k []).getD j 0 := by
  have hx : ∀ x ∈ List.zipWith (fun c v => v.map fun y => c * y) cs vs, j < x.length := by
    intro x hx
    obtain ⟨v, hv', hl⟩ := gk_mem_zipWith_smul cs vs x hx
    rw [hl, hv v hv']
    exact hj
  have hacc : j < (List.replicate n (0 : ℤ)).length := by simpa using hj
  unfold tcrLincomb
  rw [gk_fold_zipWith_getD j _ _ hx hacc, gk_zipWith_smul_getD,
    gk_zipWith_eq_range (fun c v => c * v.getD j 0) cs vs hlen, gk_list_sum_range]
  simp [hj]

@[expose] def gkVec {n : ℕ} (L : List ℤ) : Fin n → ℤ := fun j => L.getD j.val 0

theorem gkVec_lincomb {n : ℕ} (cs : List ℤ) (vs : List (List ℤ)) (hlen : cs.length = vs.length)
    (hv : ∀ v ∈ vs, v.length = n) :
    (gkVec (tcrLincomb n cs vs) : Fin n → ℤ) =
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 • (gkVec (vs.getD k []) : Fin n → ℤ) := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, gkVec]
  exact gk_lincomb_getD n cs vs hlen hv j.val j.2

theorem gkVec_vsub {n : ℕ} (X Y : List ℤ) (hX : X.length = n) (hY : Y.length = n) :
    (gkVec (tcrVsubL X Y) : Fin n → ℤ) = gkVec X - gkVec Y := by
  funext j
  have hj : j.val < n := j.2
  have h1 : j.val < (tcrVsubL X Y).length := by
    simp only [tcrVsubL, List.length_zipWith]; omega
  have h2 : j.val < X.length := by omega
  have h3 : j.val < Y.length := by omega
  simp only [gkVec, Pi.sub_apply]
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h3]
  simp [tcrVsubL]

theorem gkVec_eq_sum {n : ℕ} (L : List ℤ) :
    (gkVec L : Fin n → ℤ) = ∑ k : Fin n, L.getD k.val 0 • (Pi.single k 1 : Fin n → ℤ) := by
  funext j
  simp [gkVec, Finset.sum_apply, Pi.single_apply]

theorem gkVec_ofFn {n : ℕ} (L : List ℤ) (hL : L.length = n) :
    List.ofFn (gkVec L : Fin n → ℤ) = L := by
  apply List.ext_getElem
  · simp [hL]
  · intro k h1 h2
    simp only [List.length_ofFn] at h1
    have hk : k < L.length := by omega
    simp only [List.getElem_ofFn, gkVec]
    rw [List.getD_eq_getElem _ _ hk]

theorem gk_getD_tcrCmul (A : Array Int) (n : ℕ) (u : List ℤ) (i : ℕ) (hi : i < n) :
    (tcrCmul A n u).getD i 0 = ∑ j ∈ Finset.range n, A[n * i + j]! * u.getD j 0 := by
  have hi' : i < (tcrCmul A n u).length := by simp [tcrCmul, hi]
  rw [List.getD_eq_getElem _ _ hi']
  unfold tcrCmul
  simp only [List.getElem_map, List.getElem_range, tc_foldl_range_add]

theorem gk_dotZZ_eq : ∀ (a b : List ℤ), a.length ≤ b.length →
    tcrDotZZ a b = ∑ i ∈ Finset.range a.length, a.getD i 0 * b.getD i 0 := by
  intro a
  induction a with
  | nil => intro b _; simp [tcrDotZZ]
  | cons x a ih =>
    intro b hl
    cases b with
    | nil => simp at hl
    | cons y b =>
      have hl' : a.length ≤ b.length := by simpa using hl
      rw [show tcrDotZZ (x :: a) (y :: b) = x * y + tcrDotZZ a b from rfl, ih b hl',
        List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

theorem gk_dot_cmul (A : Array Int) (n : ℕ) (u v : List ℤ) (hv : v.length = n) :
    tcrDotZZ (tcrCmul A n u) v = tcrFormL A n v u := by
  have hc : (tcrCmul A n u).length = n := by simp [tcrCmul]
  rw [gk_dotZZ_eq (tcrCmul A n u) v (by omega), hc]
  unfold tcrFormL
  simp only [tc_foldl_range_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [gk_getD_tcrCmul A n u i (Finset.mem_range.1 hi)]
  ring

theorem gk_dot_vec {τ : Tag} (S : TcrSys)
    (hc : ∀ i j : Fin τ.rank, S.cartan[τ.rank * i.val + j.val]! = τ.cartan i j)
    (hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.cartan i j)
    (u x : List ℤ) (hu : u.length = τ.rank) (hx : x.length = τ.rank) :
    tcrDotZZ (tcrCmul S.cartan τ.rank u) x =
      iform (gkVec x : Fin τ.rank → ℤ) (gkVec u : Fin τ.rank → ℤ) := by
  rw [gk_dot_cmul S.cartan τ.rank u x hx]
  have h1 := tcrFormL_ofFn hc hsym (gkVec x : Fin τ.rank → ℤ) (gkVec u : Fin τ.rank → ℤ)
  rw [gkVec_ofFn x hx, gkVec_ofFn u hu] at h1
  exact h1

theorem gk_foldl_set_true : ∀ (m : List ℕ) (a : Array Bool) (i : ℕ),
    (m.foldl (fun a j => a.set! j true) a)[i]! = true → a[i]! = true ∨ i ∈ m := by
  intro m
  induction m with
  | nil => intro a i h; exact Or.inl h
  | cons j m ih =>
    intro a i h
    rcases ih _ i h with h1 | h1
    · by_cases hij : j = i
      · subst hij
        exact Or.inr List.mem_cons_self
      · rw [Array.getElem!_set!_ne a j i true hij] at h1
        exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem gk_mask_mem {n : ℕ} {l : List ℕ} {i : ℕ} (h : (tcrMaskOf n l)[i]! = true) : i ∈ l := by
  rcases gk_foldl_set_true l _ i h with h1 | h1
  · have h2 : (Array.replicate n false)[i]! = false := by
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      by_cases hi : i < n
      · simp [hi]
      · simp [hi]
    rw [h2] at h1
    exact absurd h1 (by decide)
  · exact h1

theorem gk_set_isRoot {τ : Tag} {S : TcrSys} (hG : TcrGood τ S) (psi : List ℕ) :
    ∀ γ ∈ tcrSet S τ psi, IsRoot τ γ := by
  rintro γ ⟨i, _, hiN, rfl⟩
  exact (hG.rv_spec hiN).1

theorem gk_vec_mem_span {τ : Tag} {S : TcrSys} (hG : TcrGood τ S) (psi delta : List ℕ)
    (hlt : ∀ i ∈ psi, i < S.tcrN) (hdelta : ∀ g ∈ delta, g ∈ psi) (cs : List ℤ)
    (hcs : cs.length = delta.length) :
    (gkVec (tcrLincomb τ.rank cs (delta.map fun a => S.roots[a]!)) : Fin τ.rank → ℤ) ∈
      Submodule.span ℤ (tcrSet S τ psi) := by
  have hv : ∀ v ∈ delta.map (fun a => S.roots[a]!), v.length = τ.rank := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    rw [(hG.rv_spec (hlt a (hdelta a ha))).2, List.length_ofFn]
  rw [gkVec_lincomb (n := τ.rank) cs (delta.map fun a => S.roots[a]!) (by simp [hcs]) hv]
  apply Submodule.sum_mem
  intro k hk
  rw [Finset.mem_range] at hk
  have hkd : k < delta.length := by omega
  have hmem : delta.getD k 0 ∈ delta := by
    rw [List.getD_eq_getElem _ _ hkd]
    exact List.getElem_mem _
  have hψ : delta.getD k 0 ∈ psi := hdelta _ hmem
  have hvec : (delta.map fun a => S.roots[a]!).getD k [] = S.roots[delta.getD k 0]! := by
    rw [List.getD_eq_getElem _ _ (by simp [hkd]), List.getElem_map,
      List.getD_eq_getElem _ _ hkd]
  apply Submodule.smul_mem
  rw [hvec]
  exact Submodule.subset_span ⟨delta.getD k 0, hψ, hlt _ hψ, rfl⟩

@[expose] def gkDisc (S : TcrSys) (delta : List Nat) : Int × List (List Int) :=
  let r := delta.length
  let G : List (List Int) := delta.map fun a => delta.map fun b => (S.ip[a]!)[b]!
  let det := tcrDetF r G
  let sgn : Int := if det > 0 then 1 else -1
  let dvecs := delta.map fun a => S.roots[a]!
  ((det.natAbs : Int), (List.range r).map fun i => tcrLincomb S.rank ((List.range r).map fun j =>
    sgn * ((if (i + j) % 2 == 0 then 1 else -1) * tcrDetF (r - 1) (tcrMinorL G i j))) dvecs)

theorem gk_outer_split (S : TcrSys) (cols : List (List Int)) (psi delta : List Nat)
    (h : tcrOuterDisc S cols psi delta = true) :
    (∀ mu ∈ (gkDisc S delta).2, ∃ cs : List ℤ, cs.length = delta.length ∧
      mu = tcrLincomb S.rank cs (delta.map fun a => S.roots[a]!)) ∧
    (∀ mu ∈ (gkDisc S delta).2, ∀ γ ∈ psi,
      tcrDotZZ (tcrCmul S.cartan S.rank mu) S.roots[γ]! % (gkDisc S delta).1 = 0) ∧
    (∃ mu ∈ (gkDisc S delta).2, ∃ mu' ∈ (gkDisc S delta).2,
      tcrDotZZ (tcrCmul S.cartan S.rank mu') (tcrVsubL (tcrLincomb S.rank mu cols) mu) %
        ((gkDisc S delta).1 * (gkDisc S delta).1) ≠ 0) := by
  unfold tcrOuterDisc at h
  unfold gkDisc
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h ⊢
  obtain ⟨⟨-, hcm⟩, hdiff⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro mu hmu
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hmu
    exact ⟨_, by simp, rfl⟩
  · intro mu hmu γ hγ
    exact hcm _ (List.mem_map.2 ⟨mu, hmu, rfl⟩) γ hγ
  · obtain ⟨c, hc, df, hdf, hne⟩ := hdiff
    obtain ⟨mu', hmu', rfl⟩ := List.mem_map.1 hc
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hdf
    exact ⟨mu, hmu, mu', hmu', hne⟩

end Aux

section Kind

variable {τ : Tag} {S : TcrSys}

theorem twistInner_congr {Ψ : Set (Fin τ.rank → ℤ)}
    {σ σ' : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (h : ∀ γ ∈ Ψ, σ γ = σ' γ) :
    twistInner Ψ σ ↔ twistInner Ψ σ' := by
  unfold twistInner
  constructor
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).symm.trans (hσ γ hγ)⟩
  · rintro ⟨w, hw, hσ⟩
    exact ⟨w, hw, fun γ hγ => (h γ hγ).trans (hσ γ hγ)⟩

theorem gk_move_claim
    (hG : TcrGood τ S) (psi : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN) :
    ∀ (wd : List ℕ), (∀ g ∈ wd, g ∈ psi) →
      ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ tcrSet S τ psi, s = rootReflection γ},
        ∀ v < S.tcrN, (wd.foldl (fun v g => (S.refl[g]!)[v]!) v) < S.tcrN ∧
          tcrRv S τ (wd.foldl (fun v g => (S.refl[g]!)[v]!) v) = u • tcrRv S τ v := by
  intro wd
  induction wd with
  | nil => intro _; exact ⟨1, Subgroup.one_mem _, fun v hv => ⟨hv, by simp⟩⟩
  | cons g wd ih =>
    intro hwd
    have hg : g ∈ psi := hwd g List.mem_cons_self
    have hgN : g < S.tcrN := hlt g hg
    obtain ⟨u, hu, hall⟩ := ih (fun x hx => hwd x (List.mem_cons_of_mem _ hx))
    refine ⟨u * rootReflection (tcrRv S τ g), Subgroup.mul_mem _ hu
      (Subgroup.subset_closure ⟨tcrRv S τ g, ⟨g, hg, hgN, rfl⟩, rfl⟩), fun v hv => ?_⟩
    obtain ⟨h1, h2⟩ := hall _ (hG.refl_spec hgN hv).1
    simp only [List.foldl_cons]
    refine ⟨h1, ?_⟩
    rw [h2, hG.refl_rootReflection hgN hv, mul_smul]

theorem tcrInnerW_sound
    (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ)) (pe : Array ℕ) (e : ℕ)
    (hpe : ∀ i < S.tcrN, pe[i]! < S.tcrN ∧ tcrRv S τ pe[i]! = (φ ^ e) (tcrRv S τ i))
    (psi delta : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN) (h : tcrInnerW S pe psi delta = true) :
    twistInner (tcrSet S τ psi) (fun γ => (φ ^ e) γ) := by
  unfold tcrInnerW at h
  try dsimp only at h
  split at h
  · simp at h
  · rename_i _ wd _
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hmask, hpsi⟩ := h
    obtain ⟨u, hu, hall⟩ :=
      gk_move_claim hG psi hlt wd (fun g hg => gk_mask_mem (hmask g hg))
    unfold twistInner
    refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    rintro γ ⟨i, hi, hiN, rfl⟩
    have hfold : wd.foldl (fun v g => (S.refl[g]!)[v]!) pe[i]! = i := by
      exact hpsi i hi
    obtain ⟨hpN, hpr⟩ := hpe i hiN
    have key := (hall pe[i]! hpN).2
    rw [hfold, hpr] at key
    calc (φ ^ e) (tcrRv S τ i) = u⁻¹ • (u • ((φ ^ e) (tcrRv S τ i))) :=
          (inv_smul_smul u _).symm
      _ = u⁻¹ • tcrRv S τ i := by rw [← key]

theorem gk_disc_core
    (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ)) (pe : Array ℕ) (e : ℕ)
    (hpe : ∀ i < S.tcrN, pe[i]! < S.tcrN ∧ tcrRv S τ pe[i]! = (φ ^ e) (tcrRv S τ i))
    (psi delta : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN) (hdelta : ∀ g ∈ delta, g ∈ psi)
    (dv : ℤ) (mus : List (List ℤ))
    (hmus : ∀ mu ∈ mus, ∃ cs : List ℤ, cs.length = delta.length ∧
      mu = tcrLincomb S.rank cs (delta.map fun a => S.roots[a]!))
    (hcm : ∀ mu ∈ mus, ∀ γ ∈ psi, tcrDotZZ (tcrCmul S.cartan S.rank mu) S.roots[γ]! % dv = 0)
    {mu mu' : List ℤ} (hmu : mu ∈ mus) (hmu' : mu' ∈ mus)
    (hnd : tcrDotZZ (tcrCmul S.cartan S.rank mu')
      (tcrVsubL (tcrLincomb S.rank mu (tcrColsOf S pe)) mu) % (dv * dv) ≠ 0) :
    ¬ twistInner (tcrSet S τ psi) (fun γ => (φ ^ e) γ) := by
  intro hinner
  have hrk : S.rank = τ.rank := hG.rank
  rw [hrk] at hmus hcm hnd
  have hroot_len : ∀ i, i < S.tcrN → (S.roots[i]!).length = τ.rank := by
    intro i hi
    rw [(hG.rv_spec hi).2, List.length_ofFn]
  have hdv_len : ∀ v ∈ delta.map (fun a => S.roots[a]!), v.length = τ.rank := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
    exact hroot_len a (hlt a (hdelta a ha))
  have hmu_len : ∀ x ∈ mus, x.length = τ.rank := by
    intro x hx
    obtain ⟨cs, _, hxe⟩ := hmus x hx
    rw [hxe]
    exact gk_lincomb_length τ.rank cs _ hdv_len
  have hcolsL : (tcrColsOf S pe).length = τ.rank := by
    unfold tcrColsOf
    simp [hrk]
  have hbas : ∀ k (hk : k < S.rank), S.basis[k]! = k := by
    intro k hk
    exact (hG.basis_spec ⟨k, by rw [← hG.rank]; exact hk⟩).1
  have hcols_get : ∀ k < S.rank, (tcrColsOf S pe).getD k [] = S.roots[pe[S.basis[k]!]!]! := by
    intro k hk
    unfold tcrColsOf
    rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_map, List.getElem_range]
  have hcols_len : ∀ v ∈ tcrColsOf S pe, v.length = τ.rank := by
    intro v hv
    unfold tcrColsOf at hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
    have hk' : k < S.rank := List.mem_range.1 hk
    have hbN : S.basis[k]! < S.tcrN := by
      rw [hbas k hk']
      exact hG.tcrRank_le hk'
    exact hroot_len _ (hpe _ hbN).1
  set σ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    φ ^ e
  have hσ : ∀ x : Fin τ.rank → ℤ, σ x = (φ ^ e) x := fun x => rfl
  have hcol : ∀ k : Fin τ.rank,
      (gkVec ((tcrColsOf S pe).getD k.val []) : Fin τ.rank → ℤ) = σ (Pi.single k 1) := by
    intro k
    have hk' : k.val < S.rank := by rw [hrk]; exact k.2
    have hb : S.basis[k.val]! = k.val := hbas k.val hk'
    have hbN : S.basis[k.val]! < S.tcrN := by
      rw [hb]
      exact hG.tcrRank_le hk'
    have hp := hpe _ hbN
    have hr1 : tcrRv S τ (S.basis[k.val]!) = Pi.single k 1 := by
      rw [hb]
      exact (hG.basis_spec k).2
    rw [hcols_get k.val hk', hσ]
    show tcrRv S τ (pe[S.basis[k.val]!]!) = (φ ^ e) (Pi.single k 1 : Fin τ.rank → ℤ)
    rw [hp.2, hr1]
  have hlin : ∀ x ∈ mus, (gkVec (tcrLincomb τ.rank x (tcrColsOf S pe)) : Fin τ.rank → ℤ) =
      σ (gkVec x) := by
    intro x hx
    have hxl := hmu_len x hx
    rw [gkVec_lincomb x (tcrColsOf S pe) (by rw [hxl, hcolsL]) hcols_len]
    rw [hxl, Finset.sum_range]
    simp only [hcol]
    rw [gkVec_eq_sum (n := τ.rank) x, map_sum]
    simp only [map_zsmul]
  have hdf_len : ∀ x ∈ mus,
      (tcrVsubL (tcrLincomb τ.rank x (tcrColsOf S pe)) x).length = τ.rank := by
    intro x hx
    unfold tcrVsubL
    rw [List.length_zipWith, gk_lincomb_length τ.rank x _ hcols_len, hmu_len x hx, min_self]
  have hdf : ∀ x ∈ mus, (gkVec (tcrVsubL (tcrLincomb τ.rank x (tcrColsOf S pe)) x) :
      Fin τ.rank → ℤ) = σ (gkVec x) - gkVec x := by
    intro x hx
    rw [gkVec_vsub _ _ (gk_lincomb_length τ.rank x _ hcols_len) (hmu_len x hx), hlin x hx]
  have hmem : ∀ x ∈ mus, (gkVec x : Fin τ.rank → ℤ) ∈ Submodule.span ℤ (tcrSet S τ psi) := by
    intro x hx
    obtain ⟨cs, hcs, hxe⟩ := hmus x hx
    rw [hxe]
    exact gk_vec_mem_span hG psi delta hlt hdelta cs hcs
  have hdiv : ∀ x ∈ mus, ∀ γ ∈ tcrSet S τ psi, dv ∣ iform (gkVec x : Fin τ.rank → ℤ) γ := by
    intro x hx γ hγ
    obtain ⟨i, hi, hiN, rfl⟩ := hγ
    have h1 := Int.dvd_of_emod_eq_zero (hcm x hx i hi)
    rw [gk_dot_vec S hG.cartan hG.sym x _ (hmu_len x hx) (hroot_len i hiN)] at h1
    rw [iform_comm]
    exact h1
  have hnd2 : ¬ dv * dv ∣ iform (gkVec mu' : Fin τ.rank → ℤ) (σ (gkVec mu) - gkVec mu) := by
    intro hd
    apply hnd
    apply Int.emod_eq_zero_of_dvd
    rw [gk_dot_vec S hG.cartan hG.sym mu' (tcrVsubL (tcrLincomb τ.rank mu (tcrColsOf S pe)) mu)
      (hmu_len mu' hmu') (hdf_len mu hmu), hdf mu hmu, iform_comm]
    exact hd
  exact (not_twistInner_of_disc (Ψ := tcrSet S τ psi) (gk_set_isRoot hG psi)
    (fun γ hγ => hG.iform_self (gk_set_isRoot hG psi γ hγ)) σ (hmem mu hmu) (hdiv mu hmu)
    (hdiv mu' hmu') hnd2) hinner

theorem tcrOuterDisc_sound
    (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ)) (pe : Array ℕ) (e : ℕ)
    (hpe : ∀ i < S.tcrN, pe[i]! < S.tcrN ∧ tcrRv S τ pe[i]! = (φ ^ e) (tcrRv S τ i))
    (psi delta : List ℕ) (hlt : ∀ i ∈ psi, i < S.tcrN) (hdelta : ∀ g ∈ delta, g ∈ psi)
    (h : tcrOuterDisc S (tcrColsOf S pe) psi delta = true) :
    ¬ twistInner (tcrSet S τ psi) (fun γ => (φ ^ e) γ) := by
  obtain ⟨h1, h2, mu, hmu, mu', hmu', hnd⟩ := gk_outer_split S (tcrColsOf S pe) psi delta h
  exact gk_disc_core hG φ pe e hpe psi delta hlt hdelta _ _ h1 h2 hmu hmu' hnd

theorem tcrKindOf_sound
    (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (hφr : ∀ γ, IsRoot τ γ → IsRoot τ (φ γ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (pows : Array (Array ℕ))
    (hpows : ∀ e ≤ 24, ∀ i < S.tcrN, (pows[e]!)[i]! < S.tcrN ∧
      tcrRv S τ ((pows[e]!)[i]!) = (φ ^ e) (tcrRv S τ i))
    (psi : List ℕ) (hnd : psi.Nodup) (hlt : ∀ i ∈ psi, i < S.tcrN)
    (hΨ : IsRootComponent (tcrSet S τ psi)) {e : ℕ}
    (hc : e = componentOrbitLength ρ (tcrSet S τ psi))
    (he : e ≤ 12) {k : TcrKind}
    (hk : tcrKindOf S pows e psi (tcrSimpleSys S psi) (tcrSimpleSys S psi).length psi.length =
      some k) :
    tcrKindOfK (twistKindOf ρ (tcrSet S τ psi)) = k := by
  have hr := tcrSimpleSys_length hG psi hnd hlt hΨ
  have hN := tcrSet_ncard hG psi hnd hlt
  have hdelta : ∀ g ∈ tcrSimpleSys S psi, g ∈ psi := fun g hg =>
    ((mem_tcrSimpleSys_iff hG psi hnd hlt hΨ).1 hg).1
  have hroot := gk_set_isRoot hG psi
  have hpowρ : ∀ m : ℕ, ∀ γ, IsRoot τ γ → (⇑ρ)^[m] γ = (φ ^ m) γ ∧ IsRoot τ ((φ ^ m) γ) := by
    intro m
    induction m with
    | zero => intro γ hγ; exact ⟨by simp, by simpa using hγ⟩
    | succ m ih =>
      intro γ hγ
      obtain ⟨h1, h2⟩ := ih γ hγ
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply', h1, hρ _ h2, pow_succ']
        rfl
      · rw [pow_succ']
        exact hφr _ h2
  have hρe : ∀ m : ℕ, (twistInner (tcrSet S τ psi) (⇑ρ)^[m] ↔
      twistInner (tcrSet S τ psi) (fun γ => (φ ^ m) γ)) := fun m =>
    twistInner_congr fun γ hγ => (hpowρ m γ (hroot γ hγ)).1
  have h24e : e ≤ 24 := by omega
  have h24 : 2 * e ≤ 24 := by omega
  have fa : tcrInnerW S (pows[e]!) psi (tcrSimpleSys S psi) = true →
      twistInner (tcrSet S τ psi) (fun γ => (φ ^ e) γ) := fun h =>
    tcrInnerW_sound hG φ (pows[e]!) e (hpows e h24e) psi _ hlt h
  have fb : tcrOuterDisc S (tcrColsOf S (pows[e]!)) psi (tcrSimpleSys S psi) = true →
      ¬ twistInner (tcrSet S τ psi) (fun γ => (φ ^ e) γ) := fun h =>
    tcrOuterDisc_sound hG φ (pows[e]!) e (hpows e h24e) psi _ hlt hdelta h
  have fa2 : tcrInnerW S (pows[2 * e]!) psi (tcrSimpleSys S psi) = true →
      twistInner (tcrSet S τ psi) (fun γ => (φ ^ (2 * e)) γ) := fun h =>
    tcrInnerW_sound hG φ (pows[2 * e]!) (2 * e) (hpows (2 * e) h24) psi _ hlt h
  have fb2 : tcrOuterDisc S (tcrColsOf S (pows[2 * e]!)) psi (tcrSimpleSys S psi) = true →
      ¬ twistInner (tcrSet S τ psi) (fun γ => (φ ^ (2 * e)) γ) := fun h =>
    tcrOuterDisc_sound hG φ (pows[2 * e]!) (2 * e) (hpows (2 * e) h24) psi _ hlt hdelta h
  have fa' : tcrInnerW S (pows[e]!) psi (tcrSimpleSys S psi) = true →
      twistInner (tcrSet S τ psi) (⇑ρ)^[e] := fun h => (hρe e).2 (fa h)
  have fb' : tcrOuterDisc S (tcrColsOf S (pows[e]!)) psi (tcrSimpleSys S psi) = true →
      ¬ twistInner (tcrSet S τ psi) (⇑ρ)^[e] := fun h hX => fb h ((hρe e).1 hX)
  have fa2' : tcrInnerW S (pows[2 * e]!) psi (tcrSimpleSys S psi) = true →
      twistInner (tcrSet S τ psi) (⇑ρ)^[2 * e] := fun h => (hρe (2 * e)).2 (fa2 h)
  have fb2' : tcrOuterDisc S (tcrColsOf S (pows[2 * e]!)) psi (tcrSimpleSys S psi) = true →
      ¬ twistInner (tcrSet S τ psi) (⇑ρ)^[2 * e] := fun h hY => fb2 h ((hρe (2 * e)).1 hY)
  clear fa fb fa2 fb2 hρe hpowρ
  unfold twistKindOf
  rw [← hc]
  unfold tcrKindOf at hk
  simp only [hr, ← hN, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  try dsimp only at hk
  clear hc he h24e h24 hr hN hdelta hroot hΨ hnd hlt hpows hρ hG
  generalize hRdef : compRank (tcrSet S τ psi) = R at hk ⊢
  generalize hNdef : (tcrSet S τ psi).ncard = Nc at hk ⊢
  clear hRdef hNdef
  generalize tcrInnerW S (pows[e]!) psi (tcrSimpleSys S psi) = A at hk fa'
  generalize tcrOuterDisc S (tcrColsOf S (pows[e]!)) psi (tcrSimpleSys S psi) = B at hk fb'
  generalize tcrInnerW S (pows[2 * e]!) psi (tcrSimpleSys S psi) = A2 at hk fa2'
  generalize tcrOuterDisc S (tcrColsOf S (pows[2 * e]!)) psi (tcrSimpleSys S psi) = B2 at hk fb2'
  generalize twistInner (tcrSet S τ psi) (⇑ρ)^[e] = X at fa' fb' ⊢
  generalize twistInner (tcrSet S τ psi) (⇑ρ)^[2 * e] = Y at fa2' fb2' ⊢
  by_cases hX : X
  · rw [if_pos hX]
    have hB0 : B = false := Bool.eq_false_iff.2 (fun hb => fb' hb hX)
    subst hB0
    clear fa' fb' fa2' fb2'
    simp only [Bool.false_eq_true, ↓reduceIte] at hk
    split_ifs at hk <;> simp_all [tcrKindOfK]
  · rw [if_neg hX]
    have hA0 : A = false := Bool.eq_false_iff.2 (fun ha => hX (fa' ha))
    subst hA0
    simp only [Bool.false_eq_true, ↓reduceIte] at hk
    by_cases hY : Y
    · have hB20 : B2 = false := Bool.eq_false_iff.2 (fun hb => fb2' hb hY)
      subst hB20
      clear fa' fb' fa2' fb2' hX
      simp only [hY, not_true_eq_false, and_false, or_false, Bool.false_eq_true,
        ↓reduceIte] at hk ⊢
      split_ifs at hk ⊢ <;> simp_all [tcrKindOfK]
    · have hA20 : A2 = false := Bool.eq_false_iff.2 (fun ha => hY (fa2' ha))
      subst hA20
      clear fa' fb' fa2' fb2' hX
      simp only [hY, not_false_eq_true, and_true, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      split_ifs at hk ⊢ with h1 h2 h3 h4 h5 h6 h7 h8 <;>
        (try obtain ⟨rfl, rfl⟩ := h1) <;> (try obtain ⟨rfl, rfl⟩ := h2) <;>
        (try obtain ⟨rfl, rfl⟩ := h3) <;> (try obtain ⟨rfl, rfl⟩ := h4) <;>
        (try obtain ⟨rfl, rfl⟩ := h5) <;> (try obtain ⟨rfl, rfl⟩ := h6) <;>
        (try obtain ⟨rfl, rfl⟩ := h8) <;> (try obtain ⟨-, rfl⟩ := h7) <;>
        simp_all [tcrKindOfK]

end Kind

end CFSG.StandardType.TableCRes

end
