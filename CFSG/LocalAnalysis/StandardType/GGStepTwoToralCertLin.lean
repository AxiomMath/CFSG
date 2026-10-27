module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertVec
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralLemmaI

public section

namespace CFSG.StandardType.StepTwoToralCert

variable {p n : ℕ}

section Generic

variable {F : Type*} [Field F]

theorem linearIndependent_of_tri {k : ℕ} (v : Fin k → Fin n → F) (c : Fin k → Fin n)
    (hd : ∀ j, v j (c j) ≠ 0) (ht : ∀ i j, i < j → v j (c i) = 0) :
    LinearIndependent F v := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg
  have key : ∀ m : ℕ, ∀ i : Fin k, i.val < m → g i = 0 := by
    intro m
    induction m with
    | zero => intro i hi; omega
    | succ m ih =>
      intro i hi
      by_cases hlt : i.val < m
      · exact ih i hlt
      · have hprev : ∀ j : Fin k, j < i → g j = 0 := fun j hj => ih j (by
          have : (j : ℕ) < i := hj
          omega)
        have h1 := congrFun hg (c i)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
        have hsum : ∑ j, g j * v j (c i) = g i * v i (c i) := by
          rw [Finset.sum_eq_single i]
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with h | h
            · rw [hprev j h, zero_mul]
            · rw [ht i j h, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
        rw [hsum] at h1
        exact (mul_eq_zero.mp h1).resolve_right (hd i)
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem card_le_finrank_of_tri {k : ℕ} (v : Fin k → Fin n → F) (c : Fin k → Fin n)
    (hd : ∀ j, v j (c j) ≠ 0) (ht : ∀ i j, i < j → v j (c i) = 0)
    (W : Submodule F (Fin n → F)) (hW : ∀ j, v j ∈ W) : k ≤ Module.finrank F W := by
  have hli := linearIndependent_of_tri v c hd ht
  have hli' : LinearIndependent F (fun j => (⟨v j, hW j⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  haveI : Module.Finite F W := Module.Finite.of_injective W.subtype W.injective_subtype
  simpa using hli'.fintype_card_le_finrank

theorem finrank_ker_mulVecLin_le {m : ℕ} (M : Matrix (Fin m) (Fin n) F) {k : ℕ}
    (hk : k ≤ M.rank) : Module.finrank F (LinearMap.ker M.mulVecLin) ≤ n - k := by
  have hrank := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrank
  have hrk : M.rank = Module.finrank F (LinearMap.range M.mulVecLin) := rfl
  omega

theorem finrank_mono_gen {A B : Submodule F (Fin n → F)} (h : A ≤ B) :
    Module.finrank F A ≤ Module.finrank F B := by
  haveI : Module.Finite F B := Module.Finite.of_injective B.subtype B.injective_subtype
  exact Submodule.finrank_mono h

theorem eq_of_le_of_finrank_le_gen {A B : Submodule F (Fin n → F)} (h : A ≤ B)
    (hd : Module.finrank F B ≤ Module.finrank F A) : A = B := by
  haveI : Module.Finite F B := Module.Finite.of_injective B.subtype B.injective_subtype
  exact Submodule.eq_of_le_of_finrank_le h hd

theorem natCard_ge_pow_gen [Finite F] (W : Submodule F (Fin n → F)) {k : ℕ}
    (hk : k ≤ Module.finrank F W) : Nat.card F ^ k ≤ Nat.card W := by
  have h := Module.natCard_eq_pow_finrank (K := F) (V := W)
  have : 1 ≤ Nat.card F := Nat.card_pos
  rw [h]
  exact Nat.pow_le_pow_right this hk

theorem finrank_eq_of_natCard_gen [Finite F] (W : Submodule F (Fin n → F)) {k : ℕ}
    (hk : 2 ≤ Nat.card F) (h : Nat.card W = Nat.card F ^ k) : Module.finrank F W = k := by
  have h' := Module.natCard_eq_pow_finrank (K := F) (V := W)
  rw [h'] at h
  exact Nat.pow_right_injective hk h

theorem tcExists_two_independent_gen (D : Submodule F (Fin n → F)) (h2 : Module.finrank F D = 2) :
    ∃ d1 ∈ D, d1 ≠ 0 ∧ ∃ d2 ∈ D, ∀ c : F, d2 ≠ c • d1 := by
  haveI : Module.Finite F D := Module.Finite.of_injective D.subtype D.injective_subtype
  have hpos : 0 < Module.finrank F D := by omega
  obtain ⟨⟨d1, hd1⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hne' : d1 ≠ 0 := fun h => hne (Subtype.ext h)
  refine ⟨d1, hd1, hne', ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : D ≤ Submodule.span F {d1} := fun x hx => by
    obtain ⟨c, rfl⟩ := hcon x hx
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self d1)
  have h1 : Module.finrank F D ≤ Module.finrank F (Submodule.span F {d1}) := by
    haveI : Module.Finite F (Submodule.span F {d1}) :=
      Module.Finite.of_injective _ (Submodule.injective_subtype _)
    exact Submodule.finrank_mono hle
  rw [finrank_span_singleton hne'] at h1
  omega

end Generic

theorem intCast_ne_zero_iff {x : ℤ} : ((x : ℤ) : ZMod p) ≠ 0 ↔ x % (p : ℤ) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]

theorem intCast_eq_zero_iff' {x : ℤ} : ((x : ℤ) : ZMod p) = 0 ↔ x % (p : ℤ) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]

theorem tcIsZero_iff {a : Array ℤ} : tcIsZero p n a = true ↔ tcVec p n a = 0 := by
  simp only [tcIsZero, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    funext i
    exact (intCast_eq_zero_iff'.mpr (h i i.2))
  · intro h i hi
    have := congrFun h ⟨i, hi⟩
    exact intCast_eq_zero_iff'.mp this

theorem tcEqMod_iff {a b : Array ℤ} : tcEqMod p n a b = true ↔ tcVec p n a = tcVec p n b := by
  simp only [tcEqMod, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    funext i
    have := intCast_eq_zero_iff'.mpr (h i i.2)
    simpa [tcVec, sub_eq_zero] using this
  · intro h i hi
    have := congrFun h ⟨i, hi⟩
    apply intCast_eq_zero_iff'.mp
    simpa [tcVec, sub_eq_zero] using this

theorem tcFun_zero_iff (l v : Array ℤ) :
    tcFun p n l (tcVec p n v) = 0 ↔ tcDot n l v % (p : ℤ) = 0 :=
  (tcDot_mod_eq_zero_iff l v).symm

theorem tcVec_tcLinComb_mem (cs : List ℤ) (vs : List (Array ℤ)) :
    tcVec p n (tcLinComb n cs vs) ∈
      Submodule.span (ZMod p) {f | ∃ g ∈ vs, f = tcVec p n g} := by
  induction vs generalizing cs with
  | nil =>
    have : tcVec p n (tcLinComb n cs []) = 0 := by
      funext i
      simp [tcVec, tcLinComb, tcEnt]
    rw [this]
    exact Submodule.zero_mem _
  | cons v vs ih =>
    cases cs with
    | nil =>
      have : tcVec p n (tcLinComb n [] (v :: vs)) = 0 := by
        funext i
        simp [tcVec, tcLinComb, tcEnt]
      rw [this]
      exact Submodule.zero_mem _
    | cons c cs =>
      have hsplit : tcVec p n (tcLinComb n (c :: cs) (v :: vs)) =
          (c : ZMod p) • tcVec p n v + tcVec p n (tcLinComb n cs vs) := by
        funext i
        simp only [tcVec, tcLinComb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tcEnt_ofFn,
          List.zipWith_cons_cons, List.sum_cons]
        push_cast
        ring
      rw [hsplit]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, by simp, rfl⟩))
        (Submodule.span_mono ?_ (ih cs))
      rintro f ⟨g, hg, rfl⟩
      exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩

theorem tcKerOK_sound (hp : p.Prime) {rows : List (Array ℤ)} {vs : List (Array ℤ × ℕ)}
    (h : tcKerOK p n rows vs = true) :
    (∀ v ∈ vs, tcVec p n v.1 ∈ tcKerSub p n rows) ∧
      ∀ W : Submodule (ZMod p) (Fin n → ZMod p), (∀ v ∈ vs, tcVec p n v.1 ∈ W) →
        vs.length ≤ Module.finrank (ZMod p) W := by
  simp only [tcKerOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hker, htri⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun v hv r hr => (tcFun_zero_iff r v.1).mpr (hker v hv r hr), fun W hW => ?_⟩
  have hget : ∀ j : Fin vs.length, vs.getD j (#[], 0) = vs.get j := fun j => by
    simp
  refine card_le_finrank_of_tri (fun j : Fin vs.length => tcVec p n (vs.get j).1)
    (fun j => ⟨(vs.get j).2, by have := (htri j j.2).1.1; rwa [hget] at this⟩) ?_ ?_ W ?_
  · intro j
    have h1 := (htri j j.2).1.2
    rw [hget] at h1
    simp only [tcVec]
    exact intCast_ne_zero_iff.mpr h1
  · intro i j hij
    have h1 := (htri j j.2).2 i hij
    rw [hget, hget ⟨i, by omega⟩] at h1
    simp only [tcVec]
    exact intCast_eq_zero_iff'.mpr h1
  · intro j
    exact hW _ (List.get_mem _ _)

theorem tcEchOK_sound (hp : p.Prime) {gens : List (Array ℤ)} {rows : List TcEch}
    (h : tcEchOK p n gens rows = true) :
    (∀ r ∈ rows, tcVec p n r.vec ∈
        Submodule.span (ZMod p) {f | ∃ g ∈ gens, f = tcVec p n g}) ∧
      ∀ W : Submodule (ZMod p) (Fin n → ZMod p), (∀ r ∈ rows, tcVec p n r.vec ∈ W) →
        rows.length ≤ Module.finrank (ZMod p) W := by
  simp only [tcEchOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hcomb, htri⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun r hr => ?_, fun W hW => ?_⟩
  · have := tcEqMod_iff.mp (hcomb r hr)
    rw [this]
    exact tcVec_tcLinComb_mem _ _
  · have hget : ∀ j : Fin rows.length, rows.getD j ⟨#[], 0, #[]⟩ = rows.get j := fun j => by
      simp
    refine card_le_finrank_of_tri (fun j : Fin rows.length => tcVec p n (rows.get j).vec)
      (fun j => ⟨(rows.get j).piv, by have := (htri j j.2).1.1; rwa [hget] at this⟩) ?_ ?_ W ?_
    · intro j
      have h1 := (htri j j.2).1.2
      rw [hget] at h1
      simp only [tcVec]
      exact intCast_ne_zero_iff.mpr h1
    · intro i j hij
      have h1 := (htri j j.2).2 i hij
      rw [hget, hget ⟨i, by omega⟩] at h1
      simp only [tcVec]
      exact intCast_eq_zero_iff'.mpr h1
    · intro j
      exact hW _ (List.get_mem _ _)

theorem finrank_tcKerSub_le (hp : p.Prime) {L : List (Array ℤ)}
    (hL : tcEchOK p n L (tcEchelon p n L) = true ∧ (tcEchelon p n L).length = L.length) :
    Module.finrank (ZMod p) (tcKerSub p n L) ≤ n - L.length := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M : Matrix (Fin L.length) (Fin n) (ZMod p) := fun j i => ((tcEnt (L.get j) i : ℤ) : ZMod p)
  have hker : tcKerSub p n L = LinearMap.ker M.mulVecLin := by
    ext f
    simp only [mem_tcKerSub, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h
      funext j
      simpa [Matrix.mulVec, dotProduct, tcFun, M] using h _ (List.get_mem _ _)
    · intro h r hr
      obtain ⟨j, rfl⟩ := List.get_of_mem hr
      simpa [Matrix.mulVec, dotProduct, tcFun, M] using congrFun h j
  have hspan := Matrix.rank_eq_finrank_span_row M
  have hrange : Set.range M.row = {f | ∃ g ∈ L, f = tcVec p n g} := by
    ext f
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨L.get j, List.get_mem _ _, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem hg
      exact ⟨j, rfl⟩
  have hge : L.length ≤ M.rank := by
    rw [hspan, hrange, ← hL.2]
    exact (tcEchOK_sound hp hL.1).2 _ (tcEchOK_sound hp hL.1).1
  rw [hker]
  exact finrank_ker_mulVecLin_le M hge

theorem natCard_ge_pow (hp : p.Prime) (W : Submodule (ZMod p) (Fin n → ZMod p)) {k : ℕ}
    (hk : k ≤ Module.finrank (ZMod p) W) : p ^ k ≤ Nat.card W := by
  haveI : Fact p.Prime := ⟨hp⟩
  have := natCard_ge_pow_gen (F := ZMod p) W hk
  rwa [Nat.card_zmod] at this

theorem finrank_eq_two_of_natCard (hp : p.Prime) (D : Submodule (ZMod p) (Fin n → ZMod p))
    (h : Nat.card D = p ^ 2) : Module.finrank (ZMod p) D = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : Nat.card D = Nat.card (ZMod p) ^ 2 := by rw [Nat.card_zmod]; exact h
  exact finrank_eq_of_natCard_gen (F := ZMod p) D (by rw [Nat.card_zmod]; exact hp.two_le) h2

theorem tcExists_two_independent (hp : p.Prime) (D : Submodule (ZMod p) (Fin n → ZMod p))
    (h2 : Module.finrank (ZMod p) D = 2) :
    ∃ d1 ∈ D, d1 ≠ 0 ∧ ∃ d2 ∈ D, ∀ c : ZMod p, d2 ≠ c • d1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact tcExists_two_independent_gen (F := ZMod p) D h2

theorem finrank_mono_zmod (hp : p.Prime) {A B : Submodule (ZMod p) (Fin n → ZMod p)}
    (h : A ≤ B) : Module.finrank (ZMod p) A ≤ Module.finrank (ZMod p) B := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact finrank_mono_gen (F := ZMod p) h

theorem tcKerOK_finrank_ge (hp : p.Prime) {rows : List (Array ℤ)} {vs : List (Array ℤ × ℕ)}
    (h : tcKerOK p n rows vs = true) :
    vs.length ≤ Module.finrank (ZMod p) (tcKerSub p n rows) :=
  (tcKerOK_sound hp h).2 _ (tcKerOK_sound hp h).1

theorem inf_ne_bot_gen {F : Type*} [Field F] {V D S : Submodule F (Fin n → F)}
    (hD : D ≤ V) (hS : S ≤ V)
    (h : Module.finrank F V < Module.finrank F D + Module.finrank F S) : D ⊓ S ≠ ⊥ :=
  CFSG.StandardType.GGStepTwoToralLemmaI.inf_ne_bot_of_finrank hD hS h

theorem inf_ne_bot_of_finrank_zmod (hp : p.Prime) {V D S : Submodule (ZMod p) (Fin n → ZMod p)}
    (hD : D ≤ V) (hS : S ≤ V)
    (h : Module.finrank (ZMod p) V < Module.finrank (ZMod p) D + Module.finrank (ZMod p) S) :
    D ⊓ S ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact inf_ne_bot_gen (F := ZMod p) hD hS h

theorem eq_of_le_of_finrank_le_zmod (hp : p.Prime) {A B : Submodule (ZMod p) (Fin n → ZMod p)}
    (h : A ≤ B) (hd : Module.finrank (ZMod p) B ≤ Module.finrank (ZMod p) A) : A = B := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact eq_of_le_of_finrank_le_gen (F := ZMod p) h hd

end CFSG.StandardType.StepTwoToralCert
