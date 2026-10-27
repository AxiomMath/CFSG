module

public import CFSG.LocalAnalysis.StandardType.GGResIIStd
public import CFSG.LocalAnalysis.StandardType.GGResIISmallDefs
public import CFSG.YGroups.Y443.Native.Hom

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GGPoly

structure CertV where
  c : ℤ
  A : List GGPoly

structure CertNV where
  a : GGPoly
  B : List GGPoly
  N : ℤ

@[expose] def lc (A E : List GGPoly) : GGPoly := (List.zipWith mul A E).foldr add []

@[expose] def pow (s : GGPoly) (m : ℕ) : GGPoly := (List.replicate m s).foldr mul (const 1)

@[expose] def goodInt (M : ℕ) (c : ℤ) : Bool := c != 0 && M % c.natAbs == 0

@[expose] def checkV (M : ℕ) (E : List GGPoly) (F : GGPoly) (cv : CertV) : Bool :=
  goodInt M cv.c && (sub (mul (const cv.c) F) (lc cv.A E)).isEmpty

@[expose] def checkNV (M : ℕ) (E : List GGPoly) (F : GGPoly) (cn : CertNV) : Bool :=
  goodInt M cn.N && (sub (add (mul cn.a F) (lc cn.B E)) (const cn.N)).isEmpty

section Sound

variable {p : ℕ} [Fact p.Prime] (u v : ZMod p)

theorem eval_lc_eq_zero (A : List GGPoly) {E : List GGPoly} (hE : ∀ e ∈ E, eval u v e = 0) :
    eval u v (lc A E) = 0 := by
  induction A generalizing E with
  | nil => rfl
  | cons a A ih =>
    cases E with
    | nil => rfl
    | cons e E =>
      change eval u v (add (mul a e) (lc A E)) = 0
      rw [eval_add, eval_mul, hE e (List.mem_cons_self ..), mul_zero, zero_add,
        ih fun e' he' => hE e' (List.mem_cons_of_mem _ he')]

theorem eval_pow (s : GGPoly) (m : ℕ) : eval u v (pow s m) = eval u v s ^ m := by
  induction m with
  | zero => simp [pow, eval_const]
  | succ m ih =>
    change eval u v (mul s (pow s m)) = _
    rw [eval_mul, ih, pow_succ, mul_comm]

theorem goodInt_ne_zero {M : ℕ} (hM : (M : ZMod p) ≠ 0) {c : ℤ} (hc : goodInt M c = true) :
    (c : ZMod p) ≠ 0 := by
  simp only [goodInt, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  obtain ⟨-, hdvd⟩ := hc
  have hd : c.natAbs ∣ M := Nat.dvd_of_mod_eq_zero hdvd
  intro h0
  apply hM
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  rw [ZMod.natCast_eq_zero_iff]
  exact dvd_trans (Int.ofNat_dvd_left.mp h0) hd

theorem checkV_sound {M : ℕ} (hM : (M : ZMod p) ≠ 0) {E : List GGPoly} {F : GGPoly} {cv : CertV}
    (h : checkV M E F cv = true) (hE : ∀ e ∈ E, eval u v e = 0) : eval u v F = 0 := by
  simp only [checkV, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨hc, hz⟩ := h
  have h1 := eval_eq_zero_of_eq_nil u v hz
  rw [eval_sub, eval_mul, eval_const, eval_lc_eq_zero u v _ hE, sub_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 (goodInt_ne_zero hM hc)
  · exact h2

theorem checkNV_sound {M : ℕ} (hM : (M : ZMod p) ≠ 0) {E : List GGPoly} {F : GGPoly}
    {cn : CertNV} (h : checkNV M E F cn = true) (hE : ∀ e ∈ E, eval u v e = 0) :
    eval u v F ≠ 0 := by
  simp only [checkNV, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨hN, hz⟩ := h
  have h1 := eval_eq_zero_of_eq_nil u v hz
  rw [eval_sub, eval_add, eval_mul, eval_const, eval_lc_eq_zero u v _ hE, add_zero] at h1
  intro hF
  rw [hF, mul_zero, zero_sub, neg_eq_zero] at h1
  exact goodInt_ne_zero hM hN h1

end Sound

end GGPoly

open GGPoly

inductive GGTree (n : ℕ) where
  | tv (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (i₀ : Fin (n + 1)) (z : Fin (n + 2))
      (cs : List CertV) (n₁ n₂ nY : CertNV)
  | tvk (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (o₀ i : Fin (n + 1)) (cs : List CertV)
      (n₁ n₂ nC : CertNV)
  | tri (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) (cs : List CertNV)
  | split (s₁ s₂ : GGPoly) (m₁ m₂ : ℕ) (cv : CertV) (l r : GGTree n)
  | empty (cv : CertV)
  | triOr (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) (c₀ c₁ c₂ c₃ c₄ : GGTree n)

@[expose] def GGPoly.CertV.dflt : CertV := ⟨0, []⟩

@[expose] def GGPoly.CertNV.dflt : CertNV := ⟨[], [], 0⟩

section Check

variable {n : ℕ} (M : ℕ) (Ts : Fin (n + 1) → Vector GGPoly (n + 2)) (ib : Fin n)

@[expose] def checkTV (E : List GGPoly) (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1)))
    (i₀ : Fin (n + 1)) (z : Fin (n + 2)) (cs : List CertV) (n₁ n₂ nY : CertNV) : Bool :=
  (fun a₁ a₂ : Vector GGPoly (n + 1) =>
    (List.finRange (n + 1)).all (fun j =>
      checkV M E (sub (mul (a₂.get i₀) (a₁.get j)) (mul (a₁.get i₀) (a₂.get j)))
        (cs.getD j.val CertV.dflt)) &&
    checkNV M E (a₁.get i₀) n₁ && checkNV M E (a₂.get i₀) n₂ &&
    checkNV M E (sub (mul (a₁.get i₀) (frootAt Ts (fC Ts t₁) (funit z)))
      (mul (a₂.get i₀) (frootAt Ts (fC Ts t₂) (funit z)))) nY)
  (fA Ts t₁) (fA Ts t₂)

@[expose] def checkTVk (E : List GGPoly) (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1)))
    (o₀ i : Fin (n + 1)) (cs : List CertV) (n₁ n₂ nC : CertNV) : Bool :=
  (fun c₁ c₂ : Vector GGPoly (n + 1) =>
    (List.finRange (n + 1)).all (fun o =>
      checkV M E (sub (mul (c₂.get o₀) (c₁.get o)) (mul (c₁.get o₀) (c₂.get o)))
        (cs.getD o.val CertV.dflt)) &&
    checkNV M E (c₂.get o₀) n₁ && checkNV M E (c₁.get o₀) n₂ &&
    checkNV M E (sub (mul (c₁.get o₀) ((fA Ts t₁).get i)) (mul (c₂.get o₀) ((fA Ts t₂).get i))) nC)
  (fC Ts t₁) (fC Ts t₂)

@[expose] def pairPoly (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1)) : GGPoly :=
  mul ((fA Ts t).get j') (fdualAt Ts (fC Ts t) j')

@[expose] def inJ (k : Fin (n + 1)) : Bool := decide (k.val < n) && decide (k.val ≠ ib.val)

@[expose] def checkTRI (E : List GGPoly) (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1))
    (cs : List CertNV) : Bool :=
  inJ ib t.1 && inJ ib j' &&
    (fun P => (List.range 5).all fun k => checkNV M E (sub P (const k)) (cs.getD k CertNV.dflt))
      (pairPoly Ts t j')

@[expose] def checkTree : List GGPoly → GGTree n → Bool
  | E, .tv t₁ t₂ i₀ z cs n₁ n₂ nY => checkTV M Ts E t₁ t₂ i₀ z cs n₁ n₂ nY
  | E, .tvk t₁ t₂ o₀ i cs n₁ n₂ nC => checkTVk M Ts E t₁ t₂ o₀ i cs n₁ n₂ nC
  | E, .tri t j' cs => checkTRI M Ts ib E t j' cs
  | E, .split s₁ s₂ m₁ m₂ cv l r =>
    checkV M E (mul (pow s₁ m₁) (pow s₂ m₂)) cv && checkTree (E ++ [s₁]) l &&
      checkTree (E ++ [s₂]) r
  | E, .empty cv => checkV M E (const 1) cv
  | E, .triOr t j' c₀ c₁ c₂ c₃ c₄ =>
    inJ ib t.1 && inJ ib j' &&
      (fun P => checkTree (E ++ [sub P (const 0)]) c₀ && checkTree (E ++ [sub P (const 1)]) c₁ &&
        checkTree (E ++ [sub P (const 2)]) c₂ && checkTree (E ++ [sub P (const 3)]) c₃ &&
        checkTree (E ++ [sub P (const 4)]) c₄) (pairPoly Ts t j')

end Check

section Sound

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem inJ_spec {n : ℕ} {ib : Fin n} {k : Fin (n + 1)} (h : inJ ib k = true) :
    ∃ j : Fin n, k = j.castSucc ∧ j ≠ ib := by
  simp only [inJ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨k.val, h.1⟩, Fin.ext rfl, fun he => h.2 (by rw [← he])⟩

theorem ggResII_concl_of_tri {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    {t : Fin (n + 1) × List (Fin (n + 1))} {j' : Fin (n + 1)} (ht : inJ ib t.1 = true)
    (hj' : inJ ib j' = true)
    (hP : eval u v (pairPoly (ggStdTableSym C ib ic) t j') ∉ ({0, 1, 2, 3, 4} : Set (ZMod p))) :
    GGResIIConcl g h α ib := by
  obtain ⟨tk, tws⟩ := t
  obtain ⟨j, rfl, hj⟩ := inJ_spec ht
  obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
  have hpair := ggF_tri (φ := RingHom.id (ZMod p)) hT hg h2 (j.castSucc, tws) j₂.castSucc
  rw [RingHom.id_apply] at hpair
  rw [pairPoly, eval_mul, eval_fA, eval_fdualAt, evalV_fC, ggStdTable_eval, ← hpair] at hP
  right; left
  refine ⟨ggResII_five_le_of_not_mem hP, _, ?_, j, j₂, hj, hj₂, hP⟩
  exact (Subgroup.closure (Set.range g)).list_prod_mem fun s hs => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs
    exact Subgroup.subset_closure ⟨i, rfl⟩

theorem ggResII_checkTree_sound {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {M : ℕ}
    (hp2 : p ≠ 2) (hM : (M : ZMod p) ≠ 0) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0) :
    ∀ (Tr : GGTree n) (E : List GGPoly), checkTree M (ggStdTableSym C ib ic) ib E Tr = true →
      (∀ e ∈ E, eval u v e = 0) → GGResIIConcl g h α ib := by
  have hev : evalT u v (ggStdTableSym C ib ic) = ggStdTable (Int.cast) C ib ic u v :=
    ggStdTable_eval u v C ib ic
  intro Tr
  induction Tr with
  | tv t₁ t₂ i₀ z cs n₁ n₂ nY =>
    intro E hchk hE
    simp only [checkTree, checkTV, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnY⟩ := hchk
    left
    refine ggF_tv (φ := RingHom.id (ZMod p)) hp2 hT hg h2 hsep t₁ t₂ i₀ (ggFUnit z) ?_ ?_ ?_ ?_
    · intro j
      have := checkV_sound u v hM (hmin j) hE
      rw [eval_sub, eval_mul, eval_mul, eval_fA, eval_fA, eval_fA, eval_fA, hev] at this
      exact this
    · have := checkNV_sound u v hM hn₁ hE
      rwa [eval_fA, hev] at this
    · have := checkNV_sound u v hM hn₂ hE
      rwa [eval_fA, hev] at this
    · have := checkNV_sound u v hM hnY hE
      rw [eval_sub, eval_mul, eval_mul, eval_fA, eval_fA, eval_frootAt, eval_frootAt, evalV_fC,
        evalV_fC, evalV_funit, hev] at this
      exact this
  | tvk t₁ t₂ o₀ i cs n₁ n₂ nC =>
    intro E hchk hE
    simp only [checkTree, checkTVk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnC⟩ := hchk
    left
    refine ggF_tvk (φ := RingHom.id (ZMod p)) hp2 hT hg h2 t₁ t₂ o₀ i ?_ ?_ ?_ ?_
    · intro o
      have := checkV_sound u v hM (hmin o) hE
      rw [eval_sub, eval_mul, eval_mul, eval_fC, eval_fC, eval_fC, eval_fC, hev] at this
      exact this
    · have := checkNV_sound u v hM hn₁ hE
      rwa [eval_fC, hev] at this
    · have := checkNV_sound u v hM hn₂ hE
      rwa [eval_fC, hev] at this
    · have := checkNV_sound u v hM hnC hE
      rw [eval_sub, eval_mul, eval_mul, eval_fC, eval_fC, eval_fA, eval_fA, hev] at this
      exact this
  | tri t j' cs =>
    intro E hchk hE
    obtain ⟨tk, tws⟩ := t
    simp only [checkTree, checkTRI, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hchk
    obtain ⟨⟨ht, hj'⟩, hcs⟩ := hchk
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    set P := pairPoly (ggStdTableSym C ib ic) (j.castSucc, tws) j₂.castSucc with hPdef
    have hk : ∀ k : ℕ, k < 5 → eval u v P ≠ (k : ZMod p) := by
      intro k hk heq
      have := checkNV_sound u v hM (hcs k hk) hE
      rw [eval_sub, eval_const, heq] at this
      exact this (by push_cast; ring)
    have hP : eval u v P ∉ ({0, 1, 2, 3, 4} : Set (ZMod p)) := by
      intro hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h0 | h0 | h0 | h0 | h0
      · exact hk 0 (by norm_num) (by rw [h0]; norm_num)
      · exact hk 1 (by norm_num) (by rw [h0]; norm_num)
      · exact hk 2 (by norm_num) (by rw [h0]; norm_num)
      · exact hk 3 (by norm_num) (by rw [h0]; norm_num)
      · exact hk 4 (by norm_num) (by rw [h0]; norm_num)
    have hpair := ggF_tri (φ := RingHom.id (ZMod p)) hT hg h2 (j.castSucc, tws) j₂.castSucc
    rw [RingHom.id_apply] at hpair
    rw [hPdef, pairPoly, eval_mul, eval_fA, eval_fdualAt, evalV_fC, hev, ← hpair] at hP
    right; left
    refine ⟨ggResII_five_le_of_not_mem hP, _, ?_, j, j₂, hj, hj₂, hP⟩
    exact (Subgroup.closure (Set.range g)).list_prod_mem fun s hs => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs
      exact Subgroup.subset_closure ⟨i, rfl⟩
  | split s₁ s₂ m₁ m₂ cv l r ihl ihr =>
    intro E hchk hE
    simp only [checkTree, Bool.and_eq_true] at hchk
    obtain ⟨⟨hcv, hl⟩, hr⟩ := hchk
    have h0 := checkV_sound u v hM hcv hE
    rw [eval_mul, eval_pow, eval_pow] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · refine ihl (E ++ [s₁]) hl fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact hE e he
      · rw [List.mem_singleton.mp he]
        by_contra hs
        exact pow_ne_zero _ hs h1
    · refine ihr (E ++ [s₂]) hr fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact hE e he
      · rw [List.mem_singleton.mp he]
        by_contra hs
        exact pow_ne_zero _ hs h1
  | empty cv =>
    intro E hchk hE
    have h0 := checkV_sound u v hM hchk hE
    rw [eval_const, Int.cast_one] at h0
    exact absurd h0 one_ne_zero
  | triOr t j' c₀ c₁ c₂ c₃ c₄ ih₀ ih₁ ih₂ ih₃ ih₄ =>
    intro E hchk hE
    simp only [checkTree, Bool.and_eq_true] at hchk
    obtain ⟨⟨ht, hj'⟩, ⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩⟩ := hchk
    set P := pairPoly (ggStdTableSym C ib ic) t j'
    have hext : ∀ k : ℕ, eval u v P = (k : ZMod p) →
        ∀ e ∈ E ++ [sub P (const (k : ℤ))], eval u v e = 0 := by
      intro k hk e he
      rcases List.mem_append.mp he with he | he
      · exact hE e he
      · rw [List.mem_singleton.mp he, eval_sub, eval_const, hk]
        push_cast
        ring
    by_cases hP : eval u v P ∈ ({0, 1, 2, 3, 4} : Set (ZMod p))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with h0 | h0 | h0 | h0 | h0
      · exact ih₀ _ h₀ (hext 0 (by rw [h0]; norm_num))
      · exact ih₁ _ h₁ (hext 1 (by rw [h0]; norm_num))
      · exact ih₂ _ h₂ (hext 2 (by rw [h0]; norm_num))
      · exact ih₃ _ h₃ (hext 3 (by rw [h0]; norm_num))
      · exact ih₄ _ h₄ (hext 4 (by rw [h0]; norm_num))
    · exact ggResII_concl_of_tri hg h2 hT ht hj' hP

@[expose] def conicPoly {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) (ib ic : Fin n) : GGPoly :=
  add (add (const (adj ic ic - 2 * d)) (mul (const (-adj ib ic)) GGPoly.U))
    (add (mul (const (-adj ic ib)) GGPoly.V) (mul (const (adj ib ib)) (mul GGPoly.U GGPoly.V)))

theorem eval_conicPoly {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) (ib ic : Fin n)
    (u v : ZMod p) :
    eval u v (conicPoly adj d ib ic) =
      (adj ic ic : ZMod p) - u * adj ib ic - v * adj ic ib + u * v * adj ib ib - 2 * d := by
  simp only [conicPoly, eval_add, eval_mul, eval_const, eval_U, eval_V]
  push_cast
  ring

theorem ggResII_shape_sound {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} (hbc : ib ≠ ic)
    {adj : Matrix (Fin n) (Fin n) ℤ} {d : ℤ} (hadj : adj * C = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    {M : ℕ} {Tr : GGTree n}
    (hchk : checkTree M (ggStdTableSym C ib ic) ib [conicPoly adj d ib ic] Tr = true)
    (hp2 : p ≠ 2) (hM : (M : ZMod p) ≠ 0) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α)
    (hsep : ∀ w : V, (∀ k, α k w = 0) → w = 0)
    (hdep : h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc)) :
    GGResIIConcl g h α ib := by
  refine ggResII_checkTree_sound hp2 hM hg h2 hT hsep Tr _ hchk fun e he => ?_
  rw [List.mem_singleton.mp he, eval_conicPoly]
  have := ggResII_conic hbc hT hdep adj d hadj
  linear_combination this

end Sound

end CFSG.StandardType
