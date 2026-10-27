module

public import CFSG.LocalAnalysis.StandardType.GGResIICert
public import CFSG.LocalAnalysis.StandardType.GGResIIWStar

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

inductive GGCellWit (n : ℕ) where
  | tv (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (i₀ : Fin (n + 1)) (z : Fin (n + 2))
  | tvk (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (o₀ i : Fin (n + 1))
  | tri (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1))
  | wstar (e6 : Bool) (ts : List (Fin (n + 1) × List (Fin (n + 1)))) (d : List ℕ)
      (lam : List (List ℕ))

@[expose] def ggWStarCartan (n : ℕ) (e6 : Bool) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  if e6 then CartanMatrix.E (n + 1) else CartanMatrix.A (n + 1)

section Check

variable {R : Type} [CommRing R] [DecidableEq R] {n : ℕ}

@[expose] def ggFAV (T : Fin (n + 1) → Vector R (n + 2)) (t : Fin (n + 1) × List (Fin (n + 1))) :
    Vector R (n + 1) :=
  (fun H => Vector.ofFn fun j => ggFDot (T j) H) (ggFWord T t.2 (ggFUnit t.1.castSucc))

omit [DecidableEq R] in
theorem ggFAV_get (T : Fin (n + 1) → Vector R (n + 2)) (t : Fin (n + 1) × List (Fin (n + 1)))
    (j : Fin (n + 1)) : (ggFAV T t).get j = ggFA T t j := by
  rw [ggFAV, Vector.get_ofFn, ggFA]

@[expose] def ggCellWitCheck (T : Fin (n + 1) → Vector R (n + 2)) (ib : Fin n) :
    GGCellWit n → Bool
  | .tv t₁ t₂ i₀ z =>
    (fun a₁ a₂ : Vector R (n + 1) =>
      (List.finRange (n + 1)).all
          (fun j => decide (a₂.get i₀ * a₁.get j - a₁.get i₀ * a₂.get j = 0))
        && decide (a₁.get i₀ ≠ 0) && decide (a₂.get i₀ ≠ 0) &&
        decide (a₁.get i₀ * ggFRootAt T (ggFC T t₁) (ggFUnit z) -
          a₂.get i₀ * ggFRootAt T (ggFC T t₂) (ggFUnit z) ≠ 0))
      (ggFAV T t₁) (ggFAV T t₂)
  | .tvk t₁ t₂ o₀ i =>
    (fun c₁ c₂ : Vector R (n + 1) =>
      (List.finRange (n + 1)).all
          (fun o => decide (c₂.get o₀ * c₁.get o - c₁.get o₀ * c₂.get o = 0))
        && decide (c₂.get o₀ ≠ 0) && decide (c₁.get o₀ ≠ 0) &&
        decide (c₁.get o₀ * (ggFAV T t₁).get i - c₂.get o₀ * (ggFAV T t₂).get i ≠ 0))
      (ggFC T t₁) (ggFC T t₂)
  | .tri t j' =>
    inJ ib t.1 && inJ ib j' &&
      (fun P : R => decide (P ≠ 0) && decide (P ≠ 1) && decide (P ≠ 2) && decide (P ≠ 3) &&
        decide (P ≠ 4)) ((ggFAV T t).get j' * ggFDualAt T (ggFC T t) j')
  | .wstar e6 ts d lam =>
    (!e6 || decide (n + 1 = 6)) &&
    (fun (t : Fin (n + 1) → Fin (n + 1) × List (Fin (n + 1))) (dd : Fin (n + 1) → R)
        (ll : Fin (n + 1) → Fin (n + 1) → R) (av cv : Vector (Vector R (n + 1)) (n + 1)) =>
      (List.finRange (n + 1)).all (fun i => decide (dd i ≠ 0)) &&
      (List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun j =>
        decide (dd i * ∑ o, (cv.get j).get o * (av.get i).get o =
          dd j * (ggWStarCartan n e6 i j : R))) &&
      (List.finRange (n + 1)).all (fun o => (List.finRange (n + 1)).all fun o' =>
        decide (∑ i, ll o i * (cv.get i).get o' = if o = o' then 1 else 0)) &&
      (List.finRange (n + 1)).all (fun k =>
        (List.finRange (n + 1)).any (fun m => decide (t m = (k, []))) ||
        (List.finRange (n + 1)).any (fun i => decide ((t i).1 = k) && (t i).2.all fun l =>
          (List.finRange (n + 1)).any fun m => decide (t m = (l, [])))))
      (fun i => ts.getD i.val (0, [])) (fun i => (d.getD i.val 0 : R))
      (fun o i => ((lam.getD o.val []).getD i.val 0 : R))
      (Vector.ofFn fun i => ggFAV T (ts.getD i.val (0, [])))
      (Vector.ofFn fun i => ggFC T (ts.getD i.val (0, [])))

end Check

@[expose] def ggConicVal {R : Type} [CommRing R] {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (ib ic : Fin n) (u v : R) : R :=
  (adj ic ic : R) - u * adj ib ic - v * adj ic ib + u * v * adj ib ib - 2 * d

@[expose] def ggCellAt (q : ℕ) [NeZero q] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (wits : List (ℕ × ℕ × GGCellWit n)) (u v : ZMod q) : Bool :=
  match wits.find? (fun w => w.1 == u.val && w.2.1 == v.val) with
  | some w => ggCellWitCheck (ggStdTable (Int.cast) C ib ic u v) ib w.2.2
  | none => false

@[expose] def GGCellCheck (q : ℕ) [NeZero q] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (adj : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) (wits : List (ℕ × ℕ × GGCellWit n)) : Prop :=
  ∀ u v : ZMod q, ggConicVal adj d ib ic u v = 0 → ggCellAt q C ib ic wits u v = true

theorem ggResII_mem_of_dvd_prod {p : ℕ} (hp : p.Prime) {L : List ℕ} (hL : ∀ q ∈ L, q.Prime)
    (e : ℕ) (h : p ∣ (L.map (· ^ e)).prod) : p ∈ L := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h hp.one_lt.ne'
  | cons q L ih =>
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq hp (hL q (List.mem_cons_self ..))).mp
        (hp.dvd_of_dvd_pow h1)
      rw [this]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h1)

theorem ggResII_prod_ne_zero {p : ℕ} [Fact p.Prime] {L : List ℕ} (hL : ∀ q ∈ L, q.Prime) (e : ℕ)
    (hp : p ∉ L) : (((L.map (· ^ e)).prod : ℕ) : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact fun h => hp (ggResII_mem_of_dvd_prod Fact.out hL e h)

section Sound

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResII_isWeyl_A {m : ℕ} (hm : 1 ≤ m) : GGIsWeylMatrix (CoxeterMatrix.A m) :=
  Or.inl ⟨m, Equiv.refl _, hm, Or.inl (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl))⟩

theorem ggResII_isWeyl_E6 : GGIsWeylMatrix CoxeterMatrix.E₆ :=
  Or.inr (Or.inl ⟨Equiv.refl _, CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)⟩)

theorem ggResII_wstar_sound {n : ℕ} {T : Fin (n + 1) → Vector (ZMod p) (n + 2)} {ib : Fin n}
    (hp2 : p ≠ 2) [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = n + 1)
    {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) T h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0) (e6 : Bool)
    (ts : List (Fin (n + 1) × List (Fin (n + 1)))) (d : List ℕ) (lam : List (List ℕ))
    (hchk : ggCellWitCheck T ib (.wstar e6 ts d lam) = true) :
    ZS.LinWeyl p (Subgroup.closure (Set.range g)) := by
  simp only [ggCellWitCheck] at hchk
  obtain ⟨he6, hchk⟩ := Bool.and_eq_true _ _ |>.mp hchk
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_finRange, true_implies, true_and, decide_eq_true_eq, Vector.get_ofFn] at hchk
  obtain ⟨⟨⟨hd0, hpair⟩, hlam⟩, hgen⟩ := hchk
  let w : Fin (n + 1) → (V ≃ₗ[ZMod p] V) := fun i => ((ts.getD i.val (0, [])).2.map g).prod
  let t' : Fin (n + 1) → (V ≃ₗ[ZMod p] V) := fun i => w i * g (ts.getD i.val (0, [])).1 * (w i)⁻¹
  let H : Fin (n + 1) → V := fun i =>
    ((d.getD i.val 0 : ℕ) : ZMod p) • ggFPi (RingHom.id (ZMod p)) h x
      (ggFWord T (ts.getD i.val (0, [])).2 (ggFUnit (ts.getD i.val (0, [])).1.castSucc))
  let A : Fin (n + 1) → Module.Dual (ZMod p) V := fun i =>
    (((d.getD i.val 0 : ℕ) : ZMod p))⁻¹ •
      ggFFun (RingHom.id (ZMod p)) α (ggFC T (ts.getD i.val (0, [])))
  have ht' : ∀ i z, t' i z = z - A i z • H i := by
    intro i z
    rw [show t' i = ((ts.getD i.val (0, [])).2.map g).prod * g (ts.getD i.val (0, [])).1 *
        (((ts.getD i.val (0, [])).2.map g).prod)⁻¹ from rfl,
      ggF_conj' hT hg h2 (ts.getD i.val (0, [])) z]
    have hd := hd0 i
    simp only [A, H, LinearMap.smul_apply, smul_eq_mul, smul_smul]
    congr 2
    field_simp
  have hP' : ∀ i j, A j (H i) = (ggWStarCartan n e6 i j : ZMod p) := by
    intro i j
    simp only [A, H, LinearMap.smul_apply, map_smul, smul_eq_mul, ggFFun_pi hT, RingHom.id_apply]
    have hij := hpair i j
    simp only [ggFAV_get, ggFA] at hij
    rw [ggFRootAt, mul_left_comm, inv_mul_eq_iff_eq_mul₀ (hd0 j)]
    exact hij
  have hsep' : ∀ z : V, (∀ i, A i z = 0) → z = 0 := by
    intro z hz
    have hz' : ∀ i : Fin (n + 1),
        ggFFun (RingHom.id (ZMod p)) α (ggFC T (ts.getD i.val (0, []))) z = 0 := by
      intro i
      have := hz i
      simp only [A, LinearMap.smul_apply, smul_eq_mul] at this
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (inv_ne_zero (hd0 i))
      · exact h0
    apply hsep
    intro o
    have hcomb : α o = ∑ i : Fin (n + 1), (((lam.getD o.val []).getD i.val 0 : ℕ) : ZMod p) •
        ggFFun (RingHom.id (ZMod p)) α (ggFC T (ts.getD i.val (0, []))) := by
      simp only [ggFFun, Finset.smul_sum, smul_smul, RingHom.id_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      rw [Finset.sum_eq_single o]
      · rw [hlam o o, if_pos rfl, one_smul]
      · intro o' _ ho'
        rw [hlam o o', if_neg (Ne.symm ho'), zero_smul]
      · intro ho; exact absurd (Finset.mem_univ o) ho
    rw [hcomb, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [LinearMap.smul_apply, hz' i, smul_zero]
  have hmem : ∀ i, t' i ∈ Subgroup.closure (Set.range g) := fun i =>
    ggF_conj_mem (ts.getD i.val (0, [])).1 (ts.getD i.val (0, [])).2
  have hplain : ∀ m k : Fin (n + 1), ts.getD m.val (0, []) = (k, []) →
      g k ∈ Subgroup.closure (Set.range t') := by
    intro m k hm
    have : t' m = g k := by
      simp only [t', w, hm, List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
    rw [← this]
    exact Subgroup.subset_closure (Set.mem_range_self m)
  have hgen' : Subgroup.closure (Set.range t') = Subgroup.closure (Set.range g) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr hmem)
    · refine (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr fun k => ?_)
      rcases hgen k with ⟨m, hm⟩ | ⟨i, hik, hl⟩
      · exact hplain m k hm
      · have hw : w i ∈ Subgroup.closure (Set.range t') := by
          refine (Subgroup.closure (Set.range t')).list_prod_mem fun s hs => ?_
          obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hs
          obtain ⟨m, hm⟩ := hl l hl'
          exact hplain m l hm
        have hti : t' i ∈ Subgroup.closure (Set.range t') :=
          Subgroup.subset_closure (Set.mem_range_self i)
        have : g k = (w i)⁻¹ * t' i * w i := by
          simp only [t', ← hik]
          group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hti) hw
  rw [← hgen']
  have hcard : Module.finrank (ZMod p) V = Fintype.card (Fin (n + 1)) := by
    rw [hdim, Fintype.card_fin]
  cases e6 with
  | false =>
    exact ggResII_linWeyl_dual hp2 (TauCeti.isFiniteType_cartanMatrix_A (n + 1))
      (ggIntCartan_A (n + 1)) (ggResII_isWeyl_A (by omega)) t' H A ht' hP' hsep' hcard
  | true =>
    have hn : n = 5 := by simp at he6; omega
    subst hn
    have hFT : TauCeti.IsFiniteType (CartanMatrix.E 6) := by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
      rwa [TauCeti.DynkinType.cartanMatrix_E6] at h
    exact ggResII_linWeyl_dual hp2 hFT ggIntCartan_E₆ ggResII_isWeyl_E6 t' H A ht' hP' hsep' hcard

@[expose] def GGCellWit.notW {n : ℕ} : GGCellWit n → Bool
  | .wstar .. => false
  | _ => true

theorem ggResII_cellWit_sound_nw {n : ℕ} {T : Fin (n + 1) → Vector (ZMod p) (n + 2)} {ib : Fin n}
    (hp2 : p ≠ 2) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) T h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0) (wt : GGCellWit n) (hnw : wt.notW = true)
    (hchk : ggCellWitCheck T ib wt = true) :
    GGResIIConcl g h α ib := by
  cases wt with
  | tv t₁ t₂ i₀ z =>
    simp only [ggCellWitCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq, ggFAV_get] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnY⟩ := hchk
    exact Or.inl (ggF_tv (φ := RingHom.id (ZMod p)) hp2 hT hg h2 hsep t₁ t₂ i₀ (ggFUnit z) hmin hn₁
      hn₂ hnY)
  | tvk t₁ t₂ o₀ i =>
    simp only [ggCellWitCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq, ggFAV_get] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnC⟩ := hchk
    exact Or.inl (ggF_tvk (φ := RingHom.id (ZMod p)) hp2 hT hg h2 t₁ t₂ o₀ i hmin hn₁ hn₂ hnC)
  | tri t j' =>
    simp only [ggCellWitCheck, Bool.and_eq_true, decide_eq_true_eq, ggFAV_get] at hchk
    obtain ⟨⟨ht, hj'⟩, ⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩, h4⟩ := hchk
    obtain ⟨tk, tws⟩ := t
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    have hpair := ggF_tri (φ := RingHom.id (ZMod p)) hT hg h2 (j.castSucc, tws) j₂.castSucc
    rw [RingHom.id_apply] at hpair
    have hP : α j₂.castSucc (((j.castSucc, tws).2.map g).prod (h (j.castSucc, tws).1)) *
        α (j.castSucc, tws).1 ((((j.castSucc, tws).2.map g).prod)⁻¹ (h j₂.castSucc)) ∉
          ({0, 1, 2, 3, 4} : Set (ZMod p)) := by
      rw [hpair]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h0, h1, h2', h3, h4⟩
    right; left
    refine ⟨ggResII_five_le_of_not_mem hP, _, ?_, j, j₂, hj, hj₂, hP⟩
    exact (Subgroup.closure (Set.range g)).list_prod_mem fun s hs => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs
      exact Subgroup.subset_closure ⟨i, rfl⟩
  | wstar e6 ts d lam => exact absurd hnw (by simp [GGCellWit.notW])

theorem ggResII_cellWit_sound {n : ℕ} {T : Fin (n + 1) → Vector (ZMod p) (n + 2)} {ib : Fin n}
    (hp2 : p ≠ 2) [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = n + 1)
    {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) T h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0) (wt : GGCellWit n)
    (hchk : ggCellWitCheck T ib wt = true) :
    GGResIIConcl g h α ib := by
  cases hw : wt.notW
  · cases wt with
    | wstar e6 ts d lam =>
      exact Or.inr (Or.inr (ggResII_wstar_sound hp2 hdim hg h2 hT hsep e6 ts d lam hchk))
    | _ => simp [GGCellWit.notW] at hw
  · exact ggResII_cellWit_sound_nw hp2 hg h2 hT hsep wt hw hchk

theorem ggResII_cell_sound {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} (hbc : ib ≠ ic)
    {adj : Matrix (Fin n) (Fin n) ℤ} {d : ℤ} (hadj : adj * C = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    {wits : List (ℕ × ℕ × GGCellWit n)} (hcell : GGCellCheck p C ib ic adj d wits)
    (hp2 : p ≠ 2) [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = n + 1)
    {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0)
    (hdep : h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc)) :
    GGResIIConcl g h α ib := by
  have hconic : ggConicVal adj d ib ic u v = 0 := by
    rw [ggConicVal]
    have := ggResII_conic hbc hT hdep adj d hadj
    linear_combination this
  have hat := hcell u v hconic
  unfold ggCellAt at hat
  split at hat
  · exact ggResII_cellWit_sound hp2 hdim hg h2 hT hsep _ hat
  · exact absurd hat (by simp)

end Sound

end CFSG.StandardType
