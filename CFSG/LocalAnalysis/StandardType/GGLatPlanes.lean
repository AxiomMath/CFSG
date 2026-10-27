module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Generic

variable {U' : Type} [Group U']

private lemma latChar_single {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (m : Fin N) :
    latChar p f (Pi.single m 1) = f m := by
  unfold latChar
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

private lemma latChar_add {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (α β : Fin N → ℤ) :
    latChar p f (α + β) = latChar p f α + latChar p f β := by
  simp only [latChar, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private lemma latChar_neg {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (α : Fin N → ℤ) :
    latChar p f (-α) = -latChar p f α := by
  simp only [latChar, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

private lemma latChar_sub {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (α β : Fin N → ℤ) :
    latChar p f (α - β) = latChar p f α - latChar p f β := by
  rw [sub_eq_add_neg, latChar_add, latChar_neg, sub_eq_add_neg]

private lemma latChar_smul {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (c : ℤ) (α : Fin N → ℤ) :
    latChar p f (c • α) = (c : ZMod p) * latChar p f α := by
  simp only [latChar, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma latChar_reflection_single {N : ℕ} (p : ℕ) (f : Fin N → ZMod p)
    (A : Matrix (Fin N) (Fin N) ℤ) (a b : Fin N) :
    latChar p f (reflection A a (Pi.single b 1)) = f b - (A a b : ZMod p) * f a := by
  rw [reflection_apply_coroot, coroot_single, latChar_sub, latChar_smul, latChar_single,
    latChar_single]

private lemma latGram_single_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (m m' : Fin N) :
    latGram S (Pi.single m 1) (Pi.single m' 1) = S m m' := by
  simp only [latGram]
  rw [Finset.sum_eq_single m (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  rw [Finset.sum_eq_single m' (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

private lemma latGram_add_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β γ : Fin N → ℤ) :
    latGram S (α + β) γ = latGram S α γ + latGram S β γ := by
  simp only [latGram, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_assoc]

private lemma latGram_neg_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram S (-α) β = -latGram S α β := by
  simp only [latGram, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private lemma latGram_neg_right {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram S α (-β) = -latGram S α β := by
  simp only [latGram, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

private lemma latGram_smul_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (c : ℤ) (α β : Fin N → ℤ) :
    latGram S (c • α) β = c * latGram S α β := by
  simp only [latGram, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma latGram_sub_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β γ : Fin N → ℤ) :
    latGram S (α - β) γ = latGram S α γ - latGram S β γ := by
  rw [sub_eq_add_neg, latGram_add_left, latGram_neg_left, sub_eq_add_neg]

private lemma latGram_reflection_single_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (A : Matrix (Fin N) (Fin N) ℤ) (hsym : ∀ i j, S i j = S j i)
    (hcart : ∀ i j, 2 * S i j = A i j * S i i) (a b : Fin N) :
    latGram S (reflection A a (Pi.single b 1)) (Pi.single a 1) = -S a b := by
  rw [reflection_apply_coroot, coroot_single, latGram_sub_left, latGram_smul_left,
    latGram_single_single, latGram_single_single, hsym b a, ← hcart a b]
  ring

private lemma latPerm_single {N : ℕ} (π : Equiv.Perm (Fin N)) {k : Fin N} (hk : π k = k) :
    latPerm π (Pi.single k 1) = Pi.single k 1 := by
  have hsymm : π.symm k = k := by
    have h' := congrArg π.symm hk
    rw [Equiv.symm_apply_apply] at h'
    exact h'.symm
  ext i
  simp only [latPerm, Pi.single_apply]
  have hiff : π.symm i = k ↔ i = k := by
    constructor
    · intro h
      have := congrArg π h
      simpa [hk] using this
    · intro h
      rw [h]
      exact hsymm
  by_cases h : i = k
  · rw [hiff.mpr h, h]
  · have h' : π.symm i ≠ k := fun hh => h (hiff.mp hh)
    rw [if_neg h', if_neg h]

private lemma latLinked_symm {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {α β : Fin N → ℤ} (h : latLinked S Φ α β) : latLinked S Φ β α :=
  Relation.EqvGen.symm _ _ h

private lemma latLinked_trans {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {α β γ : Fin N → ℤ} (h1 : latLinked S Φ α β) (h2 : latLinked S Φ β γ) :
    latLinked S Φ α γ :=
  Relation.EqvGen.trans _ _ _ h1 h2

private lemma latLinked_of_reflTransGen {N : ℕ} {α : Type*} (S : Matrix (Fin N) (Fin N) ℤ)
    (Φ : Set (Fin N → ℤ)) (e : α → (Fin N → ℤ)) (r : α → α → Prop)
    (hstep : ∀ a b, r a b → latLinked S Φ (e a) (e b))
    {a b : α} (h : Relation.ReflTransGen r a b) : latLinked S Φ (e a) (e b) := by
  have key : ∀ {a b : α}, Relation.ReflTransGen r a b → latLinked S Φ (e a) (e b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.EqvGen.refl _
    | tail hab hbc ih => exact Relation.EqvGen.trans _ _ _ ih (hstep _ _ hbc)
  exact key h

private lemma latLinked_iff_mem {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {α β : Fin N → ℤ} (h : latLinked S Φ α β) : (α ∈ Φ ↔ β ∈ Φ) := by
  letI : IsEquiv (Fin N → ℤ) (fun x y => x ∈ Φ ↔ y ∈ Φ) :=
    { refl := fun x => Iff.rfl
      symm := fun _ _ h => h.symm
      trans := fun _ _ _ h1 h2 => h1.trans h2 }
  exact Relation.EqvGen.eqvGen_le
    (r := fun x y : Fin N → ℤ => x ∈ Φ ∧ y ∈ Φ ∧ latGram S x y ≠ 0)
    (r' := fun x y : Fin N → ℤ => x ∈ Φ ↔ y ∈ Φ)
    (fun x y hxy => ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩) α β h

private lemma latLinked_right_mem {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {α β : Fin N → ℤ} (h : latLinked S Φ α β) (hα : α ∈ Φ) : β ∈ Φ :=
  (latLinked_iff_mem h).mp hα

private lemma lat_neg_single_mem_roots {N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ}
    (hA : TauCeti.IsFiniteType A) (D : Set (Fin N)) (m : Fin N) :
    -Pi.single m 1 ∈ roots hA D := by
  have hΦ := isCTRootSystem hA D
  have h := hΦ.smul_mem ((coxeterMatrix hA).toCoxeterSystem.simple m) (Pi.single m 1)
    (hΦ.single_mem m)
  rwa [weylAction_simple_single hA m] at h

private lemma lat_reflection_single_mem_roots {N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ}
    (hA : TauCeti.IsFiniteType A) (D : Set (Fin N)) (a b : Fin N) :
    reflection A a (Pi.single b 1) ∈ roots hA D := by
  have hΦ := isCTRootSystem hA D
  have h := hΦ.smul_mem ((coxeterMatrix hA).toCoxeterSystem.simple a) (Pi.single b 1)
    (hΦ.single_mem b)
  rwa [weylAction_simple] at h

private lemma lat_neg_mem_roots {N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ}
    (hA : TauCeti.IsFiniteType A) (D : Set (Fin N)) {α : Fin N → ℤ} (hα : α ∈ roots hA D) :
    -α ∈ roots hA D := by
  rcases hα with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact Or.inl ⟨w * (coxeterMatrix hA).toCoxeterSystem.simple i, i, by
      rw [weylAction_mul_apply, weylAction_simple_single, map_neg]⟩
  · exact Or.inr ⟨w * (coxeterMatrix hA).toCoxeterSystem.simple i, i, hi, by
      rw [weylAction_mul_apply, weylAction_simple_single, map_neg, smul_neg]⟩

private lemma single_one_injective {N : ℕ} : Function.Injective
    (fun m : Fin N => (Pi.single m (1 : ℤ) : Fin N → ℤ)) := by
  intro m m' h
  by_contra hne
  have := congrFun h m
  dsimp only at this
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
  exact one_ne_zero this

private lemma single_ne_single {N : ℕ} {a b : Fin N} (h : a ≠ b) :
    (Pi.single a 1 : Fin N → ℤ) ≠ Pi.single b 1 :=
  fun he => h (single_one_injective he)

private lemma single_ne_neg_single {N : ℕ} (a b : Fin N) :
    (Pi.single a 1 : Fin N → ℤ) ≠ -Pi.single b 1 := by
  intro he
  have h := congrFun he a
  by_cases hab : a = b
  · subst hab; simp [Pi.single_eq_same] at h
  · rw [Pi.single_eq_same, Pi.neg_apply, Pi.single_eq_of_ne hab] at h
    norm_num at h

private lemma injective_case3 {N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ} {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hA : A a b ≤ -1) :
    Function.Injective (![ (Pi.single a 1 : Fin N → ℤ), -Pi.single a 1,
      Pi.single b 1, -Pi.single b 1, Pi.single c 1, -Pi.single c 1,
      reflection A a (Pi.single b 1), -reflection A a (Pi.single b 1)] :
        Fin 8 → (Fin N → ℤ)) := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;>
    first
      | rfl
      | (exfalso
         have ha := congrFun hpq a
         have hb := congrFun hpq b
         have hc := congrFun hpq c
         simp [Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_of_ne hab,
           Pi.single_eq_of_ne (Ne.symm hac), Pi.single_eq_of_ne hac,
           Pi.single_eq_of_ne (Ne.symm hbc), Pi.single_eq_of_ne hbc,
           reflection_apply_coroot, coroot_single] at ha hb hc
         try omega)

private lemma injective_case2 {N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ} {a b : Fin N}
    (hab : a ≠ b) (hA : 2 ≤ A a b * A b a) (hale : A a b ≤ 0) (hble : A b a ≤ 0) :
    Function.Injective (![ (Pi.single a 1 : Fin N → ℤ), -Pi.single a 1,
      Pi.single b 1, -Pi.single b 1,
      reflection A a (Pi.single b 1), -reflection A a (Pi.single b 1),
      reflection A b (Pi.single a 1), -reflection A b (Pi.single a 1)] :
        Fin 8 → (Fin N → ℤ)) := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;>
    first
      | rfl
      | (exfalso
         have ha := congrFun hpq a
         have hb := congrFun hpq b
         simp [Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_of_ne hab,
           reflection_apply_coroot, coroot_single] at ha hb
         try omega
         try nlinarith)

private lemma ncard_le_of_injective_range {N : ℕ} {O : Set (Fin N → ℤ)}
    {w : Fin 8 → (Fin N → ℤ)} (hw : Function.Injective w) (hrange : Set.range w ⊆ O)
    (hO : O.Finite) : 8 ≤ O.ncard := by
  have h8 : (Set.range w).ncard = 8 := by
    rw [Set.ncard_range_of_injective hw, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← h8]
  exact Set.ncard_le_ncard hrange hO

private lemma apply_pow_eq_of_invariant {N : ℕ} {p : ℕ} {f : Equiv.Perm (Fin N)}
    {g : Fin N → ZMod p} (hg : ∀ i, g (f i) = g i) (n : ℕ) (x : Fin N) :
    g ((f ^ n) x) = g x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hg, ih]

private lemma eq_of_sameCycle_of_invariant {N : ℕ} {p : ℕ} {f : Equiv.Perm (Fin N)}
    {g : Fin N → ZMod p} (hg : ∀ i, g (f i) = g i) {x y : Fin N}
    (h : f.SameCycle x y) : g y = g x := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact apply_pow_eq_of_invariant hg n x

theorem latAdmPlane_of_latPlane (Δ : UniversalRootDatum U') (hΔ : Δ.divisible = ∅)
    (S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ) (hS : IsRootGram Δ S)
    (π : Equiv.Perm (Fin Δ.rank)) (hπ : IsDiagAut Δ π) (hplane : LatPlane Δ π)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (q2 : Prop)
    (hspan : ∀ i, (fun m => if π.SameCycle i m then (1 : ZMod p) else 0) ∈ LatCorootSpan Δ p) :
    LatAdmPlane Δ S p q2 π := by
  classical
  obtain ⟨i, j, k, hij, hk, hik, hjk, hconn, hlast⟩ := hplane
  let e : Fin Δ.rank → (Fin Δ.rank → ℤ) := fun m => Pi.single m 1
  let f1 : Fin Δ.rank → ZMod p := fun m => if π.SameCycle i m then 1 else 0
  let f2 : Fin Δ.rank → ZMod p := fun m => if π.SameCycle j m then 1 else 0
  let C : Set (Fin Δ.rank) := {m | ¬ π.SameCycle i m ∧ ¬ π.SameCycle j m}
  have hkC : k ∈ C := ⟨hik, hjk⟩
  have hf1fix : ∀ m, f1 (π m) = f1 m := by
    intro m; simp only [f1, Equiv.Perm.sameCycle_apply_right]
  have hf2fix : ∀ m, f2 (π m) = f2 m := by
    intro m; simp only [f2, Equiv.Perm.sameCycle_apply_right]
  have hf1i : f1 i = 1 := by
    simp only [f1]
    rw [if_pos (Equiv.Perm.SameCycle.refl π i)]
  have hf2i : f2 i = 0 := by
    simp only [f2]
    rw [if_neg (fun h => hij h.symm)]
  have hf1j : f1 j = 0 := by
    simp only [f1]
    rw [if_neg hij]
  have hf2j : f2 j = 1 := by
    simp only [f2]
    rw [if_pos (Equiv.Perm.SameCycle.refl π j)]
  have hindep : ∀ a b : ZMod p, a • f1 + b • f2 = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hai := congrFun hab i
    have hbj := congrFun hab j
    constructor
    · simpa [Pi.add_apply, Pi.smul_apply, hf1i, hf2i] using hai
    · simpa [Pi.add_apply, Pi.smul_apply, hf1j, hf2j] using hbj
  have hfke : latChar p f1 (e k) = 0 := by
    change latChar p f1 (Pi.single k 1) = 0
    rw [latChar_single]
    simp only [f1]; rw [if_neg hik]
  have hfke2 : latChar p f2 (e k) = 0 := by
    change latChar p f2 (Pi.single k 1) = 0
    rw [latChar_single]
    simp only [f2]; rw [if_neg hjk]
  have hek_mem : e k ∈ Δ.roots := by
    change Pi.single k 1 ∈ Δ.roots
    exact (isCTRootSystem Δ.isFiniteType Δ.divisible).single_mem k
  have hlatPerm_ek : latPerm π (e k) = e k := by
    change latPerm π (Pi.single k 1) = Pi.single k 1
    exact latPerm_single π hk
  refine ⟨f1, f2, hf1fix, hf2fix, hspan i, hspan j, hindep,
    ⟨e k, hek_mem, hlatPerm_ek, hfke, hfke2⟩, ?_⟩
  intro a b hab
  let f : Fin Δ.rank → ZMod p := a • f1 + b • f2
  let Φ : Set (Fin Δ.rank → ℤ) := latPhi Δ.roots p f
  have hfC : ∀ m ∈ C, f m = 0 := by
    intro m hm
    simp only [f, Pi.add_apply, Pi.smul_apply]
    rw [show f1 m = 0 from by simp only [f1]; rw [if_neg hm.1],
      show f2 m = 0 from by simp only [f2]; rw [if_neg hm.2]]
    simp
  have hfke' : latChar p f (e k) = 0 := by
    change latChar p f (Pi.single k 1) = 0
    rw [latChar_single]
    exact hfC k hkC
  have hekΦ : e k ∈ Φ := ⟨hek_mem, hfke'⟩
  let O : Set (Fin Δ.rank → ℤ) :=
    {β | ∃ n : ℕ, latLinked S Φ ((latPerm π)^[n] (e k)) β}
  have hO_isComp : IsCompOrbit S π Φ O := ⟨e k, hekΦ, rfl⟩
  have hiter : ∀ n : ℕ, (latPerm π)^[n] (e k) = e k :=
    fun n => Function.iterate_fixed hlatPerm_ek n
  have he_m_Φ : ∀ m ∈ C, e m ∈ Φ := by
    intro m hm
    refine ⟨?_, ?_⟩
    · change Pi.single m 1 ∈ Δ.roots
      exact (isCTRootSystem Δ.isFiniteType Δ.divisible).single_mem m
    · change latChar p f (Pi.single m 1) = 0
      rw [latChar_single]
      exact hfC m hm
  have hneg_m_Φ : ∀ m ∈ C, -e m ∈ Φ := by
    intro m hm
    refine ⟨?_, ?_⟩
    · change -Pi.single m 1 ∈ Δ.roots
      exact lat_neg_single_mem_roots Δ.isFiniteType Δ.divisible m
    · change latChar p f (-Pi.single m 1) = 0
      rw [latChar_neg, latChar_single, hfC m hm, neg_zero]
  have hadj_link : ∀ m ∈ C, ∀ m' ∈ C, Δ.cartan m m' ≠ 0 → latLinked S Φ (e m) (e m') := by
    intro m hm m' hm' hcart
    have hgram : latGram S (e m) (e m') ≠ 0 := by
      change latGram S (Pi.single m 1) (Pi.single m' 1) ≠ 0
      rw [latGram_single_single]
      intro hzero
      have h2 := hS.2.1 m m'
      rw [hzero, mul_zero] at h2
      exact hcart ((mul_eq_zero.mp h2.symm).resolve_right (ne_of_gt (hS.2.2 m)))
    exact Relation.EqvGen.rel _ _ ⟨he_m_Φ m hm, he_m_Φ m' hm', hgram⟩
  have hlink_C : ∀ m ∈ C, latLinked S Φ (e m) (e k) := by
    intro m hm
    have hreach := hconn.preconnected ⟨m, hm⟩ ⟨k, hkC⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    refine latLinked_of_reflTransGen S Φ (fun x : C => e x.1) _ ?_ hreach
    intro x y hxy
    have hxy' : (SimpleGraph.fromRel fun i j : Fin Δ.rank => Δ.cartan i j ≠ 0).Adj x.1 y.1 :=
      hxy
    rw [SimpleGraph.fromRel_adj] at hxy'
    obtain ⟨-, hcase⟩ := hxy'
    rcases hcase with h | h
    · exact hadj_link x.1 x.2 y.1 y.2 h
    · exact latLinked_symm (hadj_link y.1 y.2 x.1 x.2 h)
  have hneg_link : ∀ m ∈ C, latLinked S Φ (e m) (-e m) := by
    intro m hm
    have hgram : latGram S (e m) (-e m) ≠ 0 := by
      change latGram S (Pi.single m 1) (-Pi.single m 1) ≠ 0
      rw [latGram_neg_right, latGram_single_single]
      exact neg_ne_zero.mpr (ne_of_gt (hS.2.2 m))
    exact Relation.EqvGen.rel _ _ ⟨he_m_Φ m hm, hneg_m_Φ m hm, hgram⟩
  have href_link : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → Δ.cartan m m' ≠ 0 →
      latLinked S Φ (reflection Δ.cartan m (e m')) (e m) := by
    intro m hm m' hm' hne hcart
    have hΦm : reflection Δ.cartan m (e m') ∈ Φ := by
      refine ⟨?_, ?_⟩
      · change reflection Δ.cartan m (Pi.single m' 1) ∈ Δ.roots
        exact lat_reflection_single_mem_roots Δ.isFiniteType Δ.divisible m m'
      · change latChar p f (reflection Δ.cartan m (Pi.single m' 1)) = 0
        rw [latChar_reflection_single, hfC m hm, hfC m' hm']
        ring
    have hgram : latGram S (reflection Δ.cartan m (e m')) (e m) ≠ 0 := by
      change latGram S (reflection Δ.cartan m (Pi.single m' 1)) (Pi.single m 1) ≠ 0
      rw [latGram_reflection_single_single S Δ.cartan hS.1 hS.2.1 m m']
      intro hzero
      have hSne : S m m' = 0 := neg_eq_zero.mp hzero
      have h2 := hS.2.1 m m'
      rw [hSne, mul_zero] at h2
      exact hcart ((mul_eq_zero.mp h2.symm).resolve_right (ne_of_gt (hS.2.2 m)))
    exact Relation.EqvGen.rel _ _ ⟨hΦm, he_m_Φ m hm, hgram⟩
  have href_neg_link : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → Δ.cartan m m' ≠ 0 →
      latLinked S Φ (-reflection Δ.cartan m (e m')) (-e m) := by
    intro m hm m' hm' hne hcart
    have hnegΦ : -reflection Δ.cartan m (e m') ∈ Φ := by
      refine ⟨?_, ?_⟩
      · change -reflection Δ.cartan m (Pi.single m' 1) ∈ Δ.roots
        exact lat_neg_mem_roots Δ.isFiniteType Δ.divisible (by
          change reflection Δ.cartan m (Pi.single m' 1) ∈ Δ.roots
          exact lat_reflection_single_mem_roots Δ.isFiniteType Δ.divisible m m')
      · change latChar p f (-reflection Δ.cartan m (Pi.single m' 1)) = 0
        rw [latChar_neg]
        have hz : latChar p f (reflection Δ.cartan m (Pi.single m' 1)) = 0 := by
          rw [latChar_reflection_single, hfC m hm, hfC m' hm']
          ring
        rw [hz, neg_zero]
    have hgram : latGram S (-reflection Δ.cartan m (e m')) (-e m) ≠ 0 := by
      rw [show latGram S (-reflection Δ.cartan m (e m')) (-e m) =
          latGram S (reflection Δ.cartan m (e m')) (e m) from by
        rw [latGram_neg_left, latGram_neg_right, neg_neg]]
      change latGram S (reflection Δ.cartan m (Pi.single m' 1)) (Pi.single m 1) ≠ 0
      rw [latGram_reflection_single_single S Δ.cartan hS.1 hS.2.1 m m']
      intro hzero
      have hSne : S m m' = 0 := neg_eq_zero.mp hzero
      have h2 := hS.2.1 m m'
      rw [hSne, mul_zero] at h2
      exact hcart ((mul_eq_zero.mp h2.symm).resolve_right (ne_of_gt (hS.2.2 m)))
    exact Relation.EqvGen.rel _ _ ⟨hnegΦ, hneg_m_Φ m hm, hgram⟩
  have he_m_O : ∀ m ∈ C, e m ∈ O := by
    intro m hm
    refine ⟨0, ?_⟩
    rw [hiter 0]
    exact latLinked_symm (hlink_C m hm)
  have hneg_m_O : ∀ m ∈ C, -e m ∈ O := by
    intro m hm
    refine ⟨0, ?_⟩
    rw [hiter 0]
    exact latLinked_symm (latLinked_trans (latLinked_symm (hneg_link m hm)) (hlink_C m hm))
  have href_O : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → Δ.cartan m m' ≠ 0 →
      reflection Δ.cartan m (e m') ∈ O := by
    intro m hm m' hm' hne hcart
    refine ⟨0, ?_⟩
    rw [hiter 0]
    exact latLinked_symm (latLinked_trans (href_link m hm m' hm' hne hcart) (hlink_C m hm))
  have href_neg_O : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → Δ.cartan m m' ≠ 0 →
      -reflection Δ.cartan m (e m') ∈ O := by
    intro m hm m' hm' hne hcart
    refine ⟨0, ?_⟩
    rw [hiter 0]
    exact latLinked_symm (latLinked_trans (href_neg_link m hm m' hm' hne hcart)
      (latLinked_trans (latLinked_symm (hneg_link m hm)) (hlink_C m hm)))
  have hCtwo : ∃ a b : Fin Δ.rank, a ∈ C ∧ b ∈ C ∧ a ≠ b := by
    rcases hlast with h3 | ⟨m, m', hne, hm, hm', -⟩
    · have h3C : 3 ≤ C.ncard := h3
      obtain ⟨a, ha, -⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
        (s := (∅ : Set (Fin Δ.rank))) (t := C) (by rw [Set.ncard_empty]; omega)
      obtain ⟨b, hb, hbnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {a}) (t := C)
        (by rw [Set.ncard_singleton]; omega)
      exact ⟨a, b, ha, hb, fun hab => hbnot (by rw [Set.mem_singleton_iff]; exact hab.symm)⟩
    · exact ⟨m, m', hm, hm', hne⟩
  have hOsub : O ⊆ Δ.roots := by
    rintro β ⟨n, hn⟩
    exact (latLinked_right_mem hn (by rw [hiter n]; exact hekΦ)).1
  have hO_finite : O.Finite :=
    (finite_roots Δ.isFiniteType Δ.divisible).subset hOsub
  have h8 : 8 ≤ O.ncard := by
    rcases hlast with h3 | ⟨m, m', hne, hm, hm', hbond⟩
    · have h3C : 3 ≤ C.ncard := h3
      obtain ⟨a0, b0, ha0, hb0, hne0⟩ := hCtwo
      haveI : Nontrivial C := ⟨⟨⟨a0, ha0⟩, ⟨b0, hb0⟩, fun h => hne0 (congrArg Subtype.val h)⟩⟩
      obtain ⟨u, hu⟩ := hconn.preconnected.exists_adj_of_nontrivial ⟨a0, ha0⟩
      have hune : a0 ≠ u.1 := hu.1
      have hcart : Δ.cartan a0 u.1 ≠ 0 := by
        rcases hu.2 with h | h
        · exact h
        · exact fun hz => h (Δ.isFiniteType.apply_eq_zero_symm hz)
      have hAle : Δ.cartan a0 u.1 ≤ -1 := by
        have := Δ.isFiniteType.apply_le_zero_of_ne hune
        omega
      obtain ⟨c, hc, hcnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
        (s := ({a0, u.1} : Set (Fin Δ.rank))) (t := C)
        (by rw [Set.ncard_pair hune]; omega)
      have hcne1 : a0 ≠ c := fun h => hcnot (by rw [Set.mem_insert_iff]; exact Or.inl h.symm)
      have hcne2 : u.1 ≠ c := fun h => hcnot (by
        rw [Set.mem_insert_iff]
        exact Or.inr (by rw [Set.mem_singleton_iff]; exact h.symm))
      have hw : Function.Injective
          (![e a0, -e a0, e u.1, -e u.1, e c, -e c,
            reflection Δ.cartan a0 (e u.1), -reflection Δ.cartan a0 (e u.1)] :
              Fin 8 → (Fin Δ.rank → ℤ)) :=
        injective_case3 hune hcne1 hcne2 hAle
      have hrange : Set.range (![e a0, -e a0, e u.1, -e u.1, e c, -e c,
            reflection Δ.cartan a0 (e u.1), -reflection Δ.cartan a0 (e u.1)] :
              Fin 8 → (Fin Δ.rank → ℤ)) ⊆ O := by
        rintro v ⟨t, rfl⟩
        fin_cases t
        · exact he_m_O a0 ha0
        · exact hneg_m_O a0 ha0
        · exact he_m_O u.1 u.2
        · exact hneg_m_O u.1 u.2
        · exact he_m_O c hc
        · exact hneg_m_O c hc
        · exact href_O a0 ha0 u.1 u.2 hune hcart
        · exact href_neg_O a0 ha0 u.1 u.2 hune hcart
      exact ncard_le_of_injective_range hw hrange hO_finite
    · have hAle : Δ.cartan m m' ≤ 0 := Δ.isFiniteType.apply_le_zero_of_ne hne
      have hBle : Δ.cartan m' m ≤ 0 := Δ.isFiniteType.apply_le_zero_of_ne hne.symm
      have hcart : Δ.cartan m m' ≠ 0 := by
        intro h; rw [h, zero_mul] at hbond; omega
      have hcart' : Δ.cartan m' m ≠ 0 := by
        intro h; rw [h, mul_zero] at hbond; omega
      have hw : Function.Injective
          (![e m, -e m, e m', -e m',
            reflection Δ.cartan m (e m'), -reflection Δ.cartan m (e m'),
            reflection Δ.cartan m' (e m), -reflection Δ.cartan m' (e m)] :
              Fin 8 → (Fin Δ.rank → ℤ)) :=
        injective_case2 hne hbond hAle hBle
      have hrange : Set.range (![e m, -e m, e m', -e m',
            reflection Δ.cartan m (e m'), -reflection Δ.cartan m (e m'),
            reflection Δ.cartan m' (e m), -reflection Δ.cartan m' (e m)] :
              Fin 8 → (Fin Δ.rank → ℤ)) ⊆ O := by
        rintro v ⟨t, rfl⟩
        fin_cases t
        · exact he_m_O m hm
        · exact hneg_m_O m hm
        · exact he_m_O m' hm'
        · exact hneg_m_O m' hm'
        · exact href_O m hm m' hm' hne hcart
        · exact href_neg_O m hm m' hm' hne hcart
        · exact href_O m' hm' m hm hne.symm hcart'
        · exact href_neg_O m' hm' m hm hne.symm hcart'
      exact ncard_le_of_injective_range hw hrange hO_finite
  have hnotSolv : ¬ LatSolv q2 π O := by
    intro hsolv
    obtain ⟨-, hdisj⟩ := hsolv
    rcases hdisj with ⟨γ, hOγ⟩ | ⟨hncard, -⟩
    · obtain ⟨a0, b0, ha0, hb0, hne0⟩ := hCtwo
      have hea : e a0 ∈ O := he_m_O a0 ha0
      have heb : e b0 ∈ O := he_m_O b0 hb0
      rw [hOγ] at hea heb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hea heb
      have hcase : e a0 = e b0 ∨ e a0 = -e b0 := by
        rcases hea with h | h <;> rcases heb with h' | h'
        · exact Or.inl (h.trans h'.symm)
        · exact Or.inr (by rw [h, h']; ring)
        · exact Or.inr (by rw [h, h'])
        · exact Or.inl (h.trans h'.symm)
      rcases hcase with h | h
      · exact single_ne_single hne0 h
      · exact single_ne_neg_single a0 b0 h
    · exact absurd (hncard ▸ h8) (by norm_num)
  refine ⟨O, hO_isComp, hnotSolv, ?_⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let φ : {g : Fin Δ.rank → ZMod p //
      (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0} → ZMod p × ZMod p :=
    fun g => (g.1 i, g.1 j)
  have hφ : Function.Injective φ := by
    intro g g' hgg
    apply Subtype.ext
    funext m
    by_cases hmi : π.SameCycle i m
    · calc g.1 m = g.1 i := eq_of_sameCycle_of_invariant g.2.1 hmi
        _ = g'.1 i := congrArg Prod.fst hgg
        _ = g'.1 m := (eq_of_sameCycle_of_invariant g'.2.1 hmi).symm
    · by_cases hmj : π.SameCycle j m
      · calc g.1 m = g.1 j := eq_of_sameCycle_of_invariant g.2.1 hmj
          _ = g'.1 j := congrArg Prod.snd hgg
          _ = g'.1 m := (eq_of_sameCycle_of_invariant g'.2.1 hmj).symm
      · have hmC : m ∈ C := ⟨hmi, hmj⟩
        have hmem : e m ∈ O := he_m_O m hmC
        have h1 : g.1 m = 0 := by
          have := g.2.2 (e m) hmem
          change latChar p g.1 (Pi.single m 1) = 0 at this
          rwa [latChar_single] at this
        have h2 : g'.1 m = 0 := by
          have := g'.2.2 (e m) hmem
          change latChar p g'.1 (Pi.single m 1) = 0 at this
          rwa [latChar_single] at this
        rw [h1, h2]
  calc Nat.card {g : Fin Δ.rank → ZMod p //
        (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0}
      ≤ Nat.card (ZMod p × ZMod p) := Nat.card_le_card_of_injective φ hφ
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_zmod]; ring

end Generic

end CFSG.StandardType
