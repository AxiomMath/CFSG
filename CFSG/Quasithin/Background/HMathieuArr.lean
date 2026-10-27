module

public import CFSG.Quasithin.Background.HMathieuEnum
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.MinimalAxioms

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

@[expose] def InvPairOK (d : ℕ) (a b : Array ℕ) : Bool :=
  (List.range d).all fun i =>
    decide (a[i]! < d) && decide (b[i]! < d) && a[b[i]!]! == i && b[a[i]!]! == i

theorem invPairOK_spec {d : ℕ} {a b : Array ℕ} (h : InvPairOK d a b = true) (i : ℕ)
    (hi : i < d) : a[i]! < d ∧ b[i]! < d ∧ a[b[i]!]! = i ∧ b[a[i]!]! = i := by
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

@[expose] def arrFun (d : ℕ) (a : Array ℕ) (i : Fin d) : Fin d :=
  ⟨a[(i : ℕ)]! % d, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

theorem arrFun_val {d : ℕ} {a b : Array ℕ} (h : InvPairOK d a b = true) (i : Fin d) :
    (arrFun d a i : ℕ) = a[(i : ℕ)]! :=
  Nat.mod_eq_of_lt (invPairOK_spec h i i.2).1

@[expose] def permOfArr (d : ℕ) (a b : Array ℕ) (h : InvPairOK d a b = true) :
    Equiv.Perm (Fin d) where
  toFun := arrFun d a
  invFun := arrFun d b
  left_inv i := by
    have hab : InvPairOK d b a = true := by
      unfold InvPairOK at h ⊢
      rw [List.all_eq_true] at h ⊢
      intro i hi
      have := h i hi
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this ⊢
      exact ⟨⟨⟨this.1.1.2, this.1.1.1⟩, this.2⟩, this.1.2⟩
    apply Fin.ext
    rw [arrFun_val hab, arrFun_val h]
    exact (invPairOK_spec h i i.2).2.2.2
  right_inv i := by
    have hab : InvPairOK d b a = true := by
      unfold InvPairOK at h ⊢
      rw [List.all_eq_true] at h ⊢
      intro i hi
      have := h i hi
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this ⊢
      exact ⟨⟨⟨this.1.1.2, this.1.1.1⟩, this.2⟩, this.1.2⟩
    apply Fin.ext
    rw [arrFun_val h, arrFun_val hab]
    exact (invPairOK_spec h i i.2).2.2.1

theorem permOfArr_val {d : ℕ} {a b : Array ℕ} (h : InvPairOK d a b = true) (i : Fin d) :
    (permOfArr d a b h i : ℕ) = a[(i : ℕ)]! :=
  arrFun_val h i

structure PT (d : ℕ) where
  n : ℕ
  elems : Array (Array ℕ)
  mulT : Array (Array ℕ)
  invT : Array ℕ
  one : ℕ

namespace PT

variable {d : ℕ} (T : PT d)

@[expose] def mulIdx (p q : ℕ) : ℕ := (T.mulT[p]!)[q]! % T.n

@[expose] def invIdx (p : ℕ) : ℕ := T.invT[p]! % T.n

@[expose] def check : Bool :=
  T.elems.size == T.n && decide (T.one < T.n) &&
    ((List.range d).all fun i => (T.elems[T.one]!)[i]! == i) &&
    ((List.range T.n).all fun p => InvPairOK d T.elems[p]! T.elems[T.invIdx p]!) &&
    ((List.range T.n).all fun p => (List.range T.n).all fun q =>
      (List.range d).all fun i =>
        (T.elems[T.mulIdx p q]!)[i]! == (T.elems[p]!)[(T.elems[q]!)[i]!]!) &&
    ((List.range T.n).all fun p => (List.range T.n).all fun q =>
      p == q || (List.range d).any fun i => (T.elems[p]!)[i]! != (T.elems[q]!)[i]!)

variable {T}

theorem check_spec (h : T.check = true) :
    T.elems.size = T.n ∧ T.one < T.n ∧ (∀ i < d, (T.elems[T.one]!)[i]! = i) ∧
      (∀ p < T.n, InvPairOK d T.elems[p]! T.elems[T.invIdx p]! = true) ∧
      (∀ p < T.n, ∀ q < T.n, ∀ i < d,
        (T.elems[T.mulIdx p q]!)[i]! = (T.elems[p]!)[(T.elems[q]!)[i]!]!) ∧
      (∀ p < T.n, ∀ q < T.n, p ≠ q → ∃ i < d, (T.elems[p]!)[i]! ≠ (T.elems[q]!)[i]!) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq, Bool.or_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h0, h1, h2, h3, h4, fun p hp q hq hpq => ?_⟩
  rcases h5 p hp q hq with h | ⟨i, hi, hne⟩
  · exact absurd h hpq
  · exact ⟨i, hi, hne⟩

structure Elem (T : PT d) where
  idx : ℕ
  lt : idx < T.n
deriving DecidableEq

theorem Elem.ext' {p q : T.Elem} (h : p.idx = q.idx) : p = q := by
  cases p
  cases q
  cases h
  rfl

@[expose] def elemEquiv (T : PT d) : T.Elem ≃ Fin T.n where
  toFun p := ⟨p.idx, p.lt⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype T.Elem := Fintype.ofEquiv _ T.elemEquiv.symm

theorem card_elem (T : PT d) : Nat.card T.Elem = T.n := by
  rw [Nat.card_congr T.elemEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem n_pos (p : T.Elem) : 0 < T.n := Nat.lt_of_le_of_lt (Nat.zero_le _) p.lt

theorem idx_lt (p : T.Elem) : p.idx < T.n := p.lt

instance : Mul T.Elem := ⟨fun p q => ⟨T.mulIdx p.idx q.idx, Nat.mod_lt _ (n_pos p)⟩⟩

instance : Inv T.Elem := ⟨fun p => ⟨T.invIdx p.idx, Nat.mod_lt _ (n_pos p)⟩⟩

theorem idx_mul (p q : T.Elem) : (p * q).idx = T.mulIdx p.idx q.idx := rfl

theorem idx_inv (p : T.Elem) : p⁻¹.idx = T.invIdx p.idx := rfl

variable [hT : Fact (T.check = true)]

instance : One T.Elem := ⟨⟨T.one, (check_spec hT.out).2.1⟩⟩

theorem idx_one : (1 : T.Elem).idx = T.one := rfl

theorem size_elems : T.elems.size = T.n := (check_spec hT.out).1

@[expose] def arr (p : T.Elem) : Array ℕ := T.elems[p.idx]!

theorem invPairOK_arr (p : T.Elem) : InvPairOK d (T.arr p) (T.arr p⁻¹) = true :=
  (check_spec hT.out).2.2.2.1 _ p.lt

@[expose] def perm (p : T.Elem) : Equiv.Perm (Fin d) :=
  permOfArr d (T.arr p) (T.arr p⁻¹) (T.invPairOK_arr p)

theorem perm_val (p : T.Elem) (i : Fin d) : (T.perm p i : ℕ) = (T.arr p)[(i : ℕ)]! :=
  permOfArr_val _ i

theorem perm_mul (p q : T.Elem) : T.perm (p * q) = T.perm p * T.perm q := by
  ext i
  rw [perm_val, Equiv.Perm.mul_apply, perm_val, perm_val]
  exact (check_spec hT.out).2.2.2.2.1 _ p.lt _ q.lt _ i.2

theorem perm_one : T.perm (1 : T.Elem) = 1 := by
  ext i
  rw [perm_val, Equiv.Perm.one_apply]
  exact (check_spec hT.out).2.2.1 _ i.2

theorem perm_injective : Function.Injective T.perm := by
  intro p q h
  by_contra hpq
  have hne : p.idx ≠ q.idx := fun e => hpq (Elem.ext' e)
  obtain ⟨i, hi, hdiff⟩ := (check_spec hT.out).2.2.2.2.2 _ p.lt _ q.lt hne
  apply hdiff
  have := congrArg (fun σ : Equiv.Perm (Fin d) => ((σ ⟨i, hi⟩ : Fin d) : ℕ)) h
  simp only [perm_val] at this
  exact this

theorem perm_inv (p : T.Elem) : T.perm p⁻¹ = (T.perm p)⁻¹ := by
  ext i
  have h := T.invPairOK_arr p
  rw [perm_val]
  have hi : ((T.perm p)⁻¹ i : ℕ) = (T.arr p⁻¹)[(i : ℕ)]! := by
    rw [Equiv.Perm.inv_def, perm, permOfArr]
    exact arrFun_val (by
      unfold InvPairOK at h ⊢
      rw [List.all_eq_true] at h ⊢
      intro i hi
      have := h i hi
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this ⊢
      exact ⟨⟨⟨this.1.1.2, this.1.1.1⟩, this.2⟩, this.1.2⟩) i
  rw [hi]

instance instGroup : Group T.Elem :=
  Group.ofLeftAxioms
    (fun a b c => T.perm_injective (by rw [perm_mul, perm_mul, perm_mul, perm_mul, mul_assoc]))
    (fun a => T.perm_injective (by rw [perm_mul, perm_one, one_mul]))
    (fun a => T.perm_injective (by rw [perm_mul, perm_inv, perm_one, inv_mul_cancel]))

@[expose] def toPerm : T.Elem →* Equiv.Perm (Fin d) where
  toFun := T.perm
  map_one' := T.perm_one
  map_mul' := T.perm_mul

theorem toPerm_apply (p : T.Elem) : T.toPerm p = T.perm p := rfl

theorem toPerm_injective : Function.Injective T.toPerm := T.perm_injective

@[expose] def invols : List T.Elem :=
  ((List.finRange T.n).map T.elemEquiv.symm).filter fun p => p ≠ 1 && p * p == 1

theorem mem_invols {x : T.Elem} (h1 : x ≠ 1) (h2 : x * x = 1) : x ∈ T.invols := by
  rw [invols, List.mem_filter]
  refine ⟨List.mem_map.2 ⟨T.elemEquiv x, List.mem_finRange _, T.elemEquiv.symm_apply_apply x⟩,
    ?_⟩
  simp [h1, h2]

end PT

@[expose] def compArr (a b : Array ℕ) : Array ℕ := b.map fun i => a[i]!

@[expose] def bfsClosure (d : ℕ) (gens : List (Array ℕ)) (fuel : ℕ) : Array (Array ℕ) :=
  let id : Array ℕ := (Array.range d)
  let rec go : ℕ → Array (Array ℕ) → Std.HashMap (Array ℕ) ℕ → List (Array ℕ) →
      Array (Array ℕ)
    | 0, acc, _, _ => acc
    | _ + 1, acc, _, [] => acc
    | f + 1, acc, seen, frontier =>
      let (acc', seen', next) := frontier.foldl (fun (st : Array (Array ℕ) ×
          Std.HashMap (Array ℕ) ℕ × List (Array ℕ)) x =>
        gens.foldl (fun (st' : Array (Array ℕ) × Std.HashMap (Array ℕ) ℕ × List (Array ℕ)) g =>
          let y := compArr g x
          if st'.2.1.contains y then st'
          else (st'.1.push y, st'.2.1.insert y st'.1.size, y :: st'.2.2)) st) (acc, seen, [])
      go f acc' seen' next.reverse
  go fuel #[id] ((∅ : Std.HashMap (Array ℕ) ℕ).insert id 0) [id]

@[expose] def PT.ofGens (d : ℕ) (gens : List (Array ℕ)) (fuel : ℕ) : PT d :=
  let els := bfsClosure d gens fuel
  let index : Std.HashMap (Array ℕ) ℕ :=
    (List.range els.size).foldl (fun m i => m.insert els[i]! i) ∅
  let invArr (a : Array ℕ) : Array ℕ :=
    (List.range d).foldl (fun b i => b.set! (a[i]!) i) (Array.replicate d 0)
  { n := els.size
    elems := els
    mulT := els.map fun a => els.map fun b => index.getD (compArr a b) 0
    invT := els.map fun a => index.getD (invArr a) 0
    one := 0 }

section Sylow

open scoped Pointwise

variable {P K X : Type*} [Group P] [Finite P] [Group K] [Finite K] [Group X]

omit [Finite P] in
theorem exists_conj_le_range {p : ℕ} [hp : Fact p.Prime] (φ : P →* K)
    (hφ : Function.Injective φ) (hsyl : Nat.card P = p ^ (Nat.card K).factorization p)
    {H : Subgroup K} (hH : IsPGroup p H) : ∃ g : K, ∀ y ∈ H, g * y * g⁻¹ ∈ φ.range := by
  have hcard : Nat.card φ.range = p ^ (Nat.card K).factorization p := by
    rw [← hsyl, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q (Sylow.ofCard φ.range hcard)
  refine ⟨g, fun y hy => ?_⟩
  have h1 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup K) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) Q (hQ hy)
  rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard] at h1
  exact h1

omit [Finite P] in
theorem exists_conj_of_prime {p : ℕ} [Fact p.Prime] (φ : P →* K) (hφ : Function.Injective φ)
    (hsyl : Nat.card P = p ^ (Nat.card K).factorization p) {y : K} (hy : orderOf y = p) :
    ∃ g : K, ∃ s : P, s ≠ 1 ∧ g * y * g⁻¹ = φ s := by
  have hH : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_le_range φ hφ hsyl hH
  obtain ⟨s, hs⟩ := hg y (Subgroup.mem_zpowers y)
  refine ⟨g, s, fun h1 => ?_, hs.symm⟩
  rw [h1, map_one] at hs
  have hy1 : y = 1 := by
    have : g * y * g⁻¹ = 1 := hs.symm
    simpa using this
  rw [hy1, orderOf_one] at hy
  exact (Fact.out : p.Prime).one_lt.ne hy

variable [DecidableEq P]

theorem exists_conj_chain (φ : P →* K) (hφ : Function.Injective φ) (ψ : K →* X)
    (hψ : Function.Injective ψ) (hsyl : Nat.card P = 2 ^ (Nat.card K).factorization 2)
    {Rinv : List P} (hR : ∀ x : P, x ≠ 1 → x * x = 1 → x ∈ Rinv)
    {pred : List P → Bool} {k : ℕ} (hg : forallGreedy Rinv pred k [] = true)
    (E : Subgroup X) (hE : E ≤ ψ.range) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1) (hcard : Nat.card E = 2 ^ k) :
    ∃ g : K, ∃ l : List P, IndepList l ∧ pred l = true ∧
      ∀ x : X, x ∈ E ↔ ∃ s ∈ subprods l, ψ g * x * (ψ g)⁻¹ = ψ (φ s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set EK := E.comap ψ with hEK
  have hmapEK : EK.map ψ = E := Subgroup.map_comap_eq_self hE
  have hcardEK : Nat.card EK = 2 ^ k := by
    rw [← hcard, ← hmapEK, Subgroup.card_map_of_injective hψ]
  obtain ⟨g, hgE⟩ := exists_conj_le_range φ hφ hsyl (H := EK) (IsPGroup.of_card hcardEK)
  let B : Subgroup P := (EK.map (MulAut.conj g).toMonoidHom).comap φ
  have hmemB : ∀ s : P, s ∈ B ↔ ∃ y ∈ EK, g * y * g⁻¹ = φ s := by
    intro s
    simp only [B, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  have hBmap : B.map φ = EK.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.map_comap_eq_self ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hgE y hy
  have hcardB : Nat.card B = 2 ^ k := by
    rw [← hcardEK, ← Subgroup.card_map_of_injective hφ, hBmap,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hEψ : ∀ y ∈ EK, ψ y ∈ E := fun y hy => hy
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := (hmemB x).1 hx
    obtain ⟨b, hb, hby⟩ := (hmemB y).1 hy
    apply hφ
    rw [map_mul, map_mul, ← hax, ← hby]
    have hab : a * b = b * a := hψ (by rw [map_mul, map_mul]; exact hEc _ ha _ hb)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := (hmemB x).1 hx
    apply hφ
    rw [map_mul, ← hax, map_one]
    have haa : a * a = 1 := hψ (by rw [map_mul, map_one]; exact hE2 _ ha)
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [haa, mul_one, mul_inv_cancel]
  have hBR : ∀ x ∈ B, x ≠ 1 → x ∈ Rinv := fun x hx h1 => hR x h1 (hB2 x hx)
  obtain ⟨l, -, hind, hsub, hpred⟩ := forallGreedy_sound hg B hBc hB2 hBR hcardB
  refine ⟨g, l, hind, hpred, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hE hx
    obtain ⟨s, hs⟩ := hgE y hx
    refine ⟨s, (hsub s).1 ((hmemB s).2 ⟨y, hx, hs.symm⟩), ?_⟩
    rw [hs, ← map_inv, ← map_mul, ← map_mul]
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy, hys⟩ := (hmemB s).1 ((hsub s).2 hs)
    have : x = ψ y := by
      have h2 : ψ g * x * (ψ g)⁻¹ = ψ g * ψ y * (ψ g)⁻¹ := by
        rw [hx, ← hys, map_mul, map_mul, map_inv]
      simpa using h2
    rw [this]
    exact hEψ y hy

end Sylow

end CFSG.Quasithin.H.Mathieu
