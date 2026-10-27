module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNF
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriTable

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small Module

section Sign

variable {R : Type*} [CommRing R]

@[expose] def zSgn (R : Type*) [CommRing R] (r : Bool) : R := if r then 1 else -1

@[simp] theorem zSgn_true : zSgn R true = 1 := rfl

@[simp] theorem zSgn_false : zSgn R false = -1 := rfl

theorem zSgn_ne_zero [Nontrivial R] (r : Bool) : zSgn R r ≠ 0 := by
  cases r <;> simp

variable {b₀ : R} [Nontrivial R]

theorem two_ne_zero_of_two_mul (hb : 2 * b₀ = 1) : (2 : R) ≠ 0 := by
  intro h
  rw [h, zero_mul] at hb
  exact zero_ne_one hb

theorem zSgn_mul_eq_iff (hb : 2 * b₀ = 1) (p r : Bool) :
    zSgn R p * b₀ = zSgn R r * b₀ ↔ p = r := by
  cases p <;> cases r <;> simp
  all_goals first
    | exact fun h => absurd (by linear_combination -hb - h) one_ne_zero
    | exact fun h => absurd (by linear_combination -hb + h) one_ne_zero

theorem zSgn_mul_add_mul_eq_zero_iff (hb : 2 * b₀ = 1) (p q : Bool) :
    zSgn R p * b₀ + zSgn R q * b₀ = 0 ↔ p = !q := by
  cases p <;> cases q <;> simp
  all_goals first
    | exact fun h => absurd (by linear_combination -hb - h) one_ne_zero
    | exact fun h => absurd (by linear_combination -hb + h) one_ne_zero

theorem zSgn_mul_add_mul_self (hb : 2 * b₀ = 1) (p : Bool) :
    zSgn R p * b₀ + zSgn R p * b₀ = zSgn R p := by
  linear_combination zSgn R p * hb

theorem zSgn_mul_add_zSgn_eq_iff (hb : 2 * b₀ = 1) (p q r : Bool) :
    zSgn R p * b₀ + zSgn R q = zSgn R r * b₀ ↔ p = !q ∧ r = q := by
  have h2 := two_ne_zero_of_two_mul hb
  cases p <;> cases q <;> cases r <;> simp
  · intro h
    exact h2 (by linear_combination -h - hb)
  · linear_combination -hb
  · linear_combination hb
  · intro h
    exact h2 (by linear_combination h - hb)

end Sign

section Weights

variable {N : ℕ}

@[expose] def hsWeight (b₀ : ZMod N) (s : SignVec) : Fin 4 → ZMod N :=
  fun i => zSgn (ZMod N) (s i) * b₀

theorem hsWeight_apply (b₀ : ZMod N) (s : SignVec) (i : Fin 4) :
    hsWeight b₀ s i = zSgn (ZMod N) (s i) * b₀ := rfl

@[expose] def rootZ (i j : Fin 4) (u v : Bool) : Fin 4 → ℤ :=
  Pi.single i (if u then 1 else -1) + Pi.single j (if v then 1 else -1)

theorem isD4Root_rootZ {i j : Fin 4} (hij : i ≠ j) (u v : Bool) : IsD4Root (rootZ i j u v) :=
  isD4Root_single_add_single hij (by cases u <;> simp) (by cases v <;> simp)

theorem exists_rootZ {α : Fin 4 → ℤ} (h : IsD4Root α) :
    ∃ (i j : Fin 4) (u v : Bool), i ≠ j ∧ α = rootZ i j u v := by
  obtain ⟨i, j, hij, hi, hj, hα⟩ := isD4Root_iff.1 h
  refine ⟨i, j, decide (α i = 1), decide (α j = 1), hij, ?_⟩
  have hi' : α i = if decide (α i = 1) = true then 1 else -1 := by
    rcases hi with hi | hi <;> simp [hi]
  have hj' : α j = if decide (α j = 1) = true then 1 else -1 := by
    rcases hj with hj | hj <;> simp [hj]
  calc α = Pi.single i (α i) + Pi.single j (α j) := hα
    _ = rootZ i j (decide (α i = 1)) (decide (α j = 1)) := by rw [rootZ, ← hi', ← hj']

theorem castW_rootZ_apply {i j : Fin 4} (hij : i ≠ j) (u v : Bool) (k : Fin 4) :
    castW N (rootZ i j u v) k =
      (if k = i then zSgn (ZMod N) u else 0) + (if k = j then zSgn (ZMod N) v else 0) := by
  simp only [castW, rootZ, Pi.add_apply, Pi.single_apply, Int.cast_add]
  have hu : (((if u = true then (1 : ℤ) else -1 : ℤ)) : ZMod N) = zSgn (ZMod N) u := by
    cases u <;> simp
  have hv : (((if v = true then (1 : ℤ) else -1 : ℤ)) : ZMod N) = zSgn (ZMod N) v := by
    cases v <;> simp
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hu, hv]

theorem bool_eq_not_of_ne : ∀ {a b : Bool}, a ≠ b → a = !b := by decide

theorem bool_ne_self_not : ∀ {a : Bool}, a ≠ !a := by decide

variable [Nontrivial (ZMod N)] {b₀ : ZMod N}

theorem hsWeight_injective (hb : 2 * b₀ = 1) : Function.Injective (hsWeight b₀) := by
  intro s t h
  funext i
  have := congrFun h i
  rw [hsWeight_apply, hsWeight_apply, zSgn_mul_eq_iff hb] at this
  exact this

theorem hsWeight_ne_neg (hb : 2 * b₀ = 1) : b₀ ≠ -b₀ := by
  intro h
  have := (zSgn_mul_eq_iff hb true false).1 (by simpa using h)
  exact absurd this (by decide)

theorem isSpinWt_hsWeight (hb : 2 * b₀ = 1) {e : ℕ} {s : SignVec} :
    IsSpinWt b₀ e (hsWeight b₀ s) ↔ s.minusCount % 2 = e % 2 := by
  have hf : Finset.univ.filter (fun i => hsWeight b₀ s i = -b₀) =
      Finset.univ.filter (fun i => s i = false) :=
    Finset.filter_congr fun i _ => by
      rw [hsWeight_apply]
      cases hsi : s i
      · simp
      · simp only [zSgn_true, one_mul, Bool.true_eq_false, iff_false]
        exact hsWeight_ne_neg hb
  unfold IsSpinWt
  rw [hf]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [hsWeight_apply]
  cases s i <;> simp

theorem exists_hsWeight_of_isSpinWt (hb : 2 * b₀ = 1) {e : ℕ} {a : Fin 4 → ZMod N}
    (h : IsSpinWt b₀ e a) : ∃ s : SignVec, s.minusCount % 2 = e % 2 ∧ a = hsWeight b₀ s := by
  have ha : a = hsWeight b₀ (fun i => decide (a i = b₀)) := by
    funext i
    rw [hsWeight_apply]
    by_cases hc : a i = b₀
    · rw [decide_eq_true hc, zSgn_true, one_mul, hc]
    · have hneg : a i = -b₀ := (h.1 i).resolve_left hc
      rw [decide_eq_false hc, zSgn_false, neg_one_mul, hneg]
  refine ⟨_, ?_, ha⟩
  rw [← isSpinWt_hsWeight hb, ← ha]
  exact h

theorem hsWeight_add_eq_zero_iff (hb : 2 * b₀ = 1) (s t : SignVec) :
    hsWeight b₀ s + hsWeight b₀ t = 0 ↔ t = s.neg := by
  constructor
  · intro h
    funext i
    have h1 := congrFun h i
    simp only [Pi.add_apply, hsWeight_apply, Pi.zero_apply] at h1
    have h2 := (zSgn_mul_add_mul_eq_zero_iff hb (s i) (t i)).1 h1
    rw [SignVec.neg_apply, h2, Bool.not_not]
  · rintro rfl
    funext i
    simp only [Pi.add_apply, hsWeight_apply, Pi.zero_apply]
    exact (zSgn_mul_add_mul_eq_zero_iff hb _ _).2 (by rw [SignVec.neg_apply, Bool.not_not])

theorem hsWeight_add_self_ne_zero (hb : 2 * b₀ = 1) (s : SignVec) :
    hsWeight b₀ s + hsWeight b₀ s ≠ 0 := by
  rw [Ne, hsWeight_add_eq_zero_iff hb]
  intro h
  have h0 := congrFun h 0
  rw [SignVec.neg_apply] at h0
  exact bool_ne_self_not h0

theorem hsWeight_add_castW_rootZ_eq_iff (hb : 2 * b₀ = 1) {i j : Fin 4} (hij : i ≠ j)
    (u v : Bool) (s s' : SignVec) :
    hsWeight b₀ s + castW N (rootZ i j u v) = hsWeight b₀ s' ↔
      SignVec.step i j u v s = some s' := by
  constructor
  · intro h
    have hi := congrFun h i
    have hj := congrFun h j
    simp only [Pi.add_apply, hsWeight_apply, castW_rootZ_apply hij, if_pos rfl, if_neg hij,
      if_neg hij.symm, add_zero, zero_add] at hi hj
    obtain ⟨hi1, hi2⟩ := (zSgn_mul_add_zSgn_eq_iff hb _ _ _).1 hi
    obtain ⟨hj1, hj2⟩ := (zSgn_mul_add_zSgn_eq_iff hb _ _ _).1 hj
    have hk : ∀ k, k ≠ i → k ≠ j → s k = s' k := by
      intro k hki hkj
      have hk := congrFun h k
      simp only [Pi.add_apply, hsWeight_apply, castW_rootZ_apply hij, if_neg hki, if_neg hkj,
        add_zero] at hk
      exact (zSgn_mul_eq_iff hb _ _).1 hk
    rw [SignVec.step, if_pos ⟨hi1, hj1⟩]
    congr 1
    funext k
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self, hj2]
    · rw [Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self, hi2]
      · rw [Function.update_of_ne hki, hk k hki hkj]
  · intro h
    by_cases hc : s i = !u ∧ s j = !v
    · rw [SignVec.step, if_pos hc, Option.some.injEq] at h
      subst h
      funext k
      simp only [Pi.add_apply, hsWeight_apply, castW_rootZ_apply hij]
      by_cases hkj : k = j
      · subst hkj
        rw [if_neg hij.symm, if_pos rfl, Function.update_self, zero_add]
        exact (zSgn_mul_add_zSgn_eq_iff hb _ _ _).2 ⟨hc.2, rfl⟩
      · rw [Function.update_of_ne hkj, if_neg hkj, add_zero]
        by_cases hki : k = i
        · subst hki
          rw [if_pos rfl, Function.update_self]
          exact (zSgn_mul_add_zSgn_eq_iff hb _ _ _).2 ⟨hc.1, rfl⟩
        · rw [if_neg hki, Function.update_of_ne hki, add_zero]
    · rw [SignVec.step, if_neg hc] at h
      exact absurd h (by simp)

theorem hsWeight_add_hsWeight_of_agree (hb : 2 * b₀ = 1) {s t : SignVec} {k : Fin 4}
    (h : ∀ i, s i = t i ↔ i = k) :
    hsWeight b₀ s + hsWeight b₀ t = Pi.single k (zSgn (ZMod N) (s k)) := by
  funext i
  simp only [Pi.add_apply, hsWeight_apply, Pi.single_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, ← (h i).2 rfl]
    exact zSgn_mul_add_mul_self hb _
  · rw [if_neg hik]
    have h1 : s i ≠ t i := fun h' => hik ((h i).1 h')
    exact (zSgn_mul_add_mul_eq_zero_iff hb _ _).2 (bool_eq_not_of_ne h1)

theorem agree_of_hsWeight_add (hb : 2 * b₀ = 1) {s t : SignVec} {k : Fin 4} {r : Bool}
    (h : hsWeight b₀ s + hsWeight b₀ t = Pi.single k (zSgn (ZMod N) r)) :
    ∀ i, s i = t i ↔ i = k := by
  intro i
  have h1 := congrFun h i
  simp only [Pi.add_apply, hsWeight_apply, Pi.single_apply] at h1
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl] at h1
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    by_contra hne
    have h0 := (zSgn_mul_add_mul_eq_zero_iff hb (s i) (t i)).2 (bool_eq_not_of_ne hne)
    rw [h0] at h1
    exact zSgn_ne_zero r h1.symm
  · rw [if_neg hik] at h1
    have h0 := (zSgn_mul_add_mul_eq_zero_iff hb _ _).1 h1
    exact ⟨fun h' => absurd (h'.symm.trans h0) bool_ne_self_not, fun h' => absurd h' hik⟩

end Weights

section Module

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {X : Type*} [AddCommGroup X] [Module K X]

structure SpinNF (D : D4Datum G K) (ρ : Representation K G X) (e : ℕ)
    (b₀ : ZMod (Nat.card Kˣ)) (C : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
    (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X) : Prop where
  two_mul : 2 * b₀ = 1
  two_le : 2 ≤ Nat.card Kˣ
  mem_iff : ∀ a, a ∈ C ↔ IsSpinWt b₀ e a
  nf : NF D ρ 0 C b

variable {D : D4Datum G K} {ρ : Representation K G X} {e : ℕ} {b₀ : ZMod (Nat.card Kˣ)}
  {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X}

theorem SpinNF.nontrivial (hN : SpinNF D ρ e b₀ C b) : Nontrivial (ZMod (Nat.card Kˣ)) :=
  haveI : Fact (1 < Nat.card Kˣ) := ⟨hN.two_le⟩
  inferInstance

@[expose] def ZLab.Rel {e : ℕ} (L : ZLab e) (i j : Fin 4) (u v : Bool) (m m' : Fin 4 ⊕ Fin 4) :
    Prop :=
  SignVec.step i j u v (L.lab m) = some (L.lab m')

instance {e : ℕ} (L : ZLab e) (i j : Fin 4) (u v : Bool) (m m' : Fin 4 ⊕ Fin 4) :
    Decidable (L.Rel i j u v m m') :=
  inferInstanceAs (Decidable (SignVec.step i j u v (L.lab m) = some (L.lab m')))

theorem ZLab.Rel.unique {e : ℕ} {L : ZLab e} {i j : Fin 4} {u v : Bool}
    {m m' m'' : Fin 4 ⊕ Fin 4} (h : L.Rel i j u v m m') (h' : L.Rel i j u v m m'') :
    m' = m'' :=
  L.injective (Option.some.inj (h.symm.trans h'))

variable (hN : SpinNF D ρ e b₀ C b) (L : ZLab e)

include hN

theorem SpinNF.hsWeight_mem (m : Fin 4 ⊕ Fin 4) : hsWeight b₀ (L.lab m) ∈ C := by
  haveI := hN.nontrivial
  exact (hN.mem_iff _).2 ((isSpinWt_hsWeight hN.two_mul).2 (L.minusCount_mod m))

theorem SpinNF.exists_lab_of_mem {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) :
    ∃ m, a = hsWeight b₀ (L.lab m) := by
  haveI := hN.nontrivial
  obtain ⟨s, hs, rfl⟩ := exists_hsWeight_of_isSpinWt hN.two_mul ((hN.mem_iff a).1 ha)
  obtain ⟨m, rfl⟩ := L.surjective s hs
  exact ⟨m, rfl⟩

theorem SpinNF.linearIndependent :
    LinearIndependent K (fun m => b (hsWeight b₀ (L.lab m))) := by
  haveI := hN.nontrivial
  have hinj : Function.Injective (fun m => hsWeight b₀ (L.lab m)) :=
    (hsWeight_injective hN.two_mul).comp L.injective
  exact iSupIndep.linearIndependent _ ((D4Datum.iSupIndep_wtSpace D ρ).comp hinj)
    (fun m => hN.nf.mem_wtSpace _ (hN.hsWeight_mem L m))
    (fun m => hN.nf.ne_zero _ (hN.hsWeight_mem L m))

theorem SpinNF.span_range :
    ⊤ ≤ Submodule.span K (Set.range (fun m => b (hsWeight b₀ (L.lab m)))) := by
  refine le_trans (le_of_eq hN.nf.span_eq.symm) (Submodule.span_mono ?_)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨m, rfl⟩ := hN.exists_lab_of_mem L ha
  exact ⟨m, rfl⟩

@[expose] noncomputable def SpinNF.basis : Basis (Fin 4 ⊕ Fin 4) K X :=
  Basis.mk (hN.linearIndependent L) (hN.span_range L)

theorem SpinNF.basis_apply (m : Fin 4 ⊕ Fin 4) :
    hN.basis L m = b (hsWeight b₀ (L.lab m)) := by
  rw [SpinNF.basis, Basis.mk_apply]

@[expose] noncomputable def SpinNF.equiv : X ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  (hN.basis L).equivFun

theorem SpinNF.equiv_basis (m : Fin 4 ⊕ Fin 4) :
    hN.equiv L (hN.basis L m) = Pi.single m 1 := by
  funext j
  rw [SpinNF.equiv, Basis.equivFun_self, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

theorem SpinNF.torus_apply (t : Fin 4 → Kˣ) (m : Fin 4 ⊕ Fin 4) :
    ρ (D.h t) (hN.basis L m) =
      ((D4Datum.wtChar (hsWeight b₀ (L.lab m)) t : Kˣ) : K) • hN.basis L m := by
  rw [hN.basis_apply L]
  exact (D4Datum.mem_wtSpace D ρ).1 (hN.nf.mem_wtSpace _ (hN.hsWeight_mem L m)) t

theorem SpinNF.root_apply_of_rel {i j : Fin 4} (hij : i ≠ j) {u v : Bool}
    {m m' : Fin 4 ⊕ Fin 4} (h : L.Rel i j u v m m') (c : K) :
    ρ (D.x (rootZ i j u v) c) (hN.basis L m) = hN.basis L m + c • hN.basis L m' := by
  haveI := hN.nontrivial
  have hα := isD4Root_rootZ hij u v
  have h1 := hN.nf.root _ hα c _ (hN.hsWeight_mem L m)
  have hw : hsWeight b₀ (L.lab m) + castW (Nat.card Kˣ) (rootZ i j u v) =
      hsWeight b₀ (L.lab m') := (hsWeight_add_castW_rootZ_eq_iff hN.two_mul hij u v _ _).2 h
  simp only [pow_zero, one_smul, pow_one] at h1
  rw [hN.basis_apply L, hN.basis_apply L, h1, hw, if_pos (hN.hsWeight_mem L m')]

theorem SpinNF.root_apply_of_not_rel {i j : Fin 4} (hij : i ≠ j) {u v : Bool}
    {m : Fin 4 ⊕ Fin 4} (h : ∀ m', ¬ L.Rel i j u v m m') (c : K) :
    ρ (D.x (rootZ i j u v) c) (hN.basis L m) = hN.basis L m := by
  haveI := hN.nontrivial
  have hα := isD4Root_rootZ hij u v
  have h1 := hN.nf.root _ hα c _ (hN.hsWeight_mem L m)
  simp only [pow_zero, one_smul, pow_one] at h1
  have hn : hsWeight b₀ (L.lab m) + castW (Nat.card Kˣ) (rootZ i j u v) ∉ C := by
    intro hmem
    obtain ⟨s', hs', hs'e⟩ := exists_hsWeight_of_isSpinWt hN.two_mul ((hN.mem_iff _).1 hmem)
    have hstep := (hsWeight_add_castW_rootZ_eq_iff hN.two_mul hij u v _ _).1 hs'e
    obtain ⟨m', rfl⟩ := L.surjective s' hs'
    exact h m' hstep
  rw [hN.basis_apply L, h1, if_neg hn, add_zero]

end Module

end CFSG.RankThree.GF2n.Stroth80.Tri

end
