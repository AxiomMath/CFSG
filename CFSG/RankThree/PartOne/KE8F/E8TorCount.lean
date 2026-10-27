module

public import CFSG.RankThree.PartOne.KE8F.E8Tor

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {L : Type} [Field L]

section Coordinates

theorem fin8_ev_or_od (k : Fin Tag.E8.rank) : (∃ j : Fin 4, k = ev j) ∨ (∃ j : Fin 4, k = od j) := by
  have hk : k.val < 8 := k.isLt
  by_cases h : k.val % 2 = 0
  · refine Or.inl ⟨⟨k.val / 2, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [ev]
    omega
  · refine Or.inr ⟨⟨k.val / 2, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [od]
    omega

theorem cg_injective {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {b b' : Fin Tag.E8.rank → Lˣ} (hb : b ∈ fixedCharTuples e8P4V Fr)
    (hb' : b' ∈ fixedCharTuples e8P4V Fr) (h : ∀ j, cg b j = cg b' j) : b = b' := by
  have hj := (mem_fixedCharTuples_e8P4_iff hFr b).1 hb
  have hj' := (mem_fixedCharTuples_e8P4_iff hFr b').1 hb'
  have hbs : bs b = bs b' := by
    funext k
    rcases fin8_ev_or_od k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact h j
    · rw [(hj j).1, (hj' j).1]
      exact congrArg (· ^ q) (h j)
  rw [← ofBasis_bs b, ← ofBasis_bs b', hbs]

@[expose] def gaussBasis (q : ℕ) (c : Fin 4 → Lˣ) : Fin Tag.E8.rank → Lˣ := fun k =>
  if k.val % 2 = 0 then c ⟨k.val / 2, by have := k.isLt; have : Tag.E8.rank = 8 := rfl; omega⟩
  else c ⟨k.val / 2, by have := k.isLt; have : Tag.E8.rank = 8 := rfl; omega⟩ ^ q

theorem gaussBasis_ev (q : ℕ) (c : Fin 4 → Lˣ) (j : Fin 4) : gaussBasis q c (ev j) = c j := by
  simp only [gaussBasis, ev]
  have h1 : (2 * j.val) % 2 = 0 := by omega
  have h2 : (2 * j.val) / 2 = j.val := by omega
  simp [h1, h2]

theorem gaussBasis_od (q : ℕ) (c : Fin 4 → Lˣ) (j : Fin 4) : gaussBasis q c (od j) = c j ^ q := by
  simp only [gaussBasis, od]
  have h1 : (2 * j.val + 1) % 2 = 1 := by omega
  have h2 : (2 * j.val + 1) / 2 = j.val := by omega
  simp [h1, h2]

@[expose] def torusOfGauss (q : ℕ) (c : Fin 4 → Lˣ) : Fin Tag.E8.rank → Lˣ :=
  ofBasis (gaussBasis q c)

theorem cg_torusOfGauss (q : ℕ) (c : Fin 4 → Lˣ) (j : Fin 4) : cg (torusOfGauss q c) j = c j := by
  rw [cg, torusOfGauss, bs_ofBasis, gaussBasis_ev]

theorem torusOfGauss_mem {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {c : Fin 4 → Lˣ}
    (hc : ∀ j, c j ^ (q * q + 1) = 1) : torusOfGauss q c ∈ fixedCharTuples e8P4V Fr := by
  rw [mem_fixedCharTuples_e8P4_iff hFr]
  intro j
  rw [torusOfGauss, bs_ofBasis, bs_ofBasis, gaussBasis_ev, gaussBasis_od]
  exact ⟨rfl, hc j⟩

theorem exists_T0_of_gauss {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (c : Fin 4 → Lˣ)
    (hc : ∀ j, c j ^ (q * q + 1) = 1) :
    ∃ b ∈ fixedCharTuples e8P4V Fr, ∀ j, cg b j = c j :=
  ⟨torusOfGauss q c, torusOfGauss_mem hFr hc, cg_torusOfGauss q c⟩

theorem cg_pow_eq_one {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {b : Fin Tag.E8.rank → Lˣ} (hb : b ∈ fixedCharTuples e8P4V Fr) (j : Fin 4) :
    cg b j ^ (q * q + 1) = 1 := ((mem_fixedCharTuples_e8P4_iff hFr b).1 hb j).2

end Coordinates

section Count

variable [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

omit [Fact ℓ.Prime] in
theorem card_rootsOfUnity_pos {m : ℕ} (hm : ¬ ℓ ∣ m) (hm0 : m ≠ 0) :
    Nat.card {u : Lˣ // u ^ m = 1} = m := by
  have hm' : (m : L) ≠ 0 := fun h => hm ((CharP.cast_eq_zero_iff L ℓ m).1 h)
  have : NeZero m := ⟨hm0⟩
  have : NeZero (m : L) := ⟨hm'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  have h := hζ.card_rootsOfUnity
  have e : {u : Lˣ // u ^ m = 1} ≃ rootsOfUnity m L :=
    { toFun := fun u => ⟨u.1, (mem_rootsOfUnity m u.1).2 u.2⟩
      invFun := fun u => ⟨u.1, (mem_rootsOfUnity m u.1).1 u.2⟩
      left_inv := fun u => rfl
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact h

theorem card_T0 {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hℓq : ℓ ∣ q) :
    Nat.card (fixedCharTuples e8P4V Fr) = (q * q + 1) ^ 4 := by
  have hn : ¬ ℓ ∣ q * q + 1 := fun h => by
    have h1 : ℓ ∣ q * q := Dvd.dvd.mul_right hℓq q
    have := (Nat.dvd_add_right h1).1 h
    exact (Fact.out : ℓ.Prime).one_lt.ne' (Nat.dvd_one.1 this)
  let e : fixedCharTuples e8P4V Fr ≃ (Fin 4 → {u : Lˣ // u ^ (q * q + 1) = 1}) :=
    { toFun := fun b j => ⟨cg b.1 j, cg_pow_eq_one hFr b.2 j⟩
      invFun := fun c => ⟨torusOfGauss q (fun j => (c j).1),
        torusOfGauss_mem hFr (fun j => (c j).2)⟩
      left_inv := fun b => by
        apply Subtype.ext
        exact cg_injective hFr (torusOfGauss_mem hFr (fun j => cg_pow_eq_one hFr b.2 j)) b.2
          (fun j => cg_torusOfGauss q _ j)
      right_inv := fun c => by
        funext j
        apply Subtype.ext
        exact cg_torusOfGauss q _ j }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_rootsOfUnity_pos hn (by positivity)]


@[expose] def ptors (p : ℕ) : Subgroup (Fin Tag.E8.rank → Lˣ) where
  carrier := {b | ∀ i, b i ^ p = 1}
  mul_mem' {a b} ha hb := fun i => by
    rw [Pi.mul_apply, mul_pow, ha i, hb i, mul_one]
  one_mem' := fun i => by simp
  inv_mem' {a} ha := fun i => by
    rw [Pi.inv_apply, inv_pow, ha i, inv_one]

@[expose] def T0tors (Fr : L →+* L) (p : ℕ) : Subgroup (Fin Tag.E8.rank → Lˣ) :=
  fixedCharTuples e8P4V Fr ⊓ ptors p

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem mem_T0tors_iff {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    {b : Fin Tag.E8.rank → Lˣ} :
    b ∈ T0tors Fr p ↔ b ∈ fixedCharTuples e8P4V Fr ∧ ∀ j, cg b j ^ p = 1 := by
  constructor
  · rintro ⟨hb, hp⟩
    exact ⟨hb, fun j => CTTorus.rootChar_pow_eq_one hp (e8P4col (ev j))⟩
  · rintro ⟨hb, hp⟩
    refine ⟨hb, fun i => ?_⟩
    have h := rootChar_T0 hFr hb (Pi.single i 1)
    rw [CTTorus.rootChar_single] at h
    rw [h, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hp j,
      _root_.one_zpow]

omit [Fact ℓ.Prime] in
theorem card_T0tors {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q * q + 1) (hpℓ : ¬ ℓ ∣ p) : Nat.card (T0tors Fr p) = p ^ 4 := by
  have hcn : ∀ c : Lˣ, c ^ p = 1 → c ^ (q * q + 1) = 1 := fun c hc => by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hc, one_pow]
  let e : T0tors Fr p ≃ (Fin 4 → {u : Lˣ // u ^ p = 1}) :=
    { toFun := fun b j => ⟨cg b.1 j, ((mem_T0tors_iff hFr).1 b.2).2 j⟩
      invFun := fun c => ⟨torusOfGauss q (fun j => (c j).1),
        (mem_T0tors_iff hFr).2 ⟨torusOfGauss_mem hFr (fun j => hcn _ (c j).2),
          fun j => by rw [cg_torusOfGauss]; exact (c j).2⟩⟩
      left_inv := fun b => by
        apply Subtype.ext
        exact cg_injective hFr (torusOfGauss_mem hFr
          (fun j => hcn _ (((mem_T0tors_iff hFr).1 b.2).2 j))) ((mem_T0tors_iff hFr).1 b.2).1
          (fun j => cg_torusOfGauss q _ j)
      right_inv := fun c => by
        funext j
        apply Subtype.ext
        exact cg_torusOfGauss q _ j }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_rootsOfUnity_pos hpℓ hp.ne_zero]

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem sq_eq_one_dichotomy (u : Lˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h1 : ((u : L)) * (u : L) = 1 := by
    have := congrArg (fun x : Lˣ => (x : L)) hu
    simpa [pow_two] using this
  rcases mul_self_eq_one_iff.1 h1 with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by simpa using h))

section SignDichotomy

attribute [local instance] Classical.propDecidable

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem sq_eq_one_inj : Function.Injective
    (fun u : {u : Lˣ // u ^ 2 = 1} => decide (u.1 = 1)) := by
  intro u w h
  have h' : decide (u.1 = 1) = decide (w.1 = 1) := h
  apply Subtype.ext
  by_cases h1 : (-1 : Lˣ) = 1
  · have e : ∀ x : {u : Lˣ // u ^ 2 = 1}, x.1 = 1 := fun x => by
      rcases sq_eq_one_dichotomy x.1 x.2 with hx | hx
      · exact hx
      · rw [hx, h1]
    rw [e u, e w]
  · rcases sq_eq_one_dichotomy u.1 u.2 with hu | hu <;>
      rcases sq_eq_one_dichotomy w.1 w.2 with hw | hw
    · rw [hu, hw]
    · rw [hu, hw] at h'
      simp [h1] at h'
    · rw [hu, hw] at h'
      simp [h1] at h'
    · rw [hu, hw]

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem finite_sq_eq_one : Finite {u : Lˣ // u ^ 2 = 1} :=
  Finite.of_injective _ sq_eq_one_inj

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem card_sq_eq_one_le_two : Nat.card {u : Lˣ // u ^ 2 = 1} ≤ 2 := by
  classical
  calc Nat.card {u : Lˣ // u ^ 2 = 1} ≤ Nat.card Bool :=
        Nat.card_le_card_of_injective _ sq_eq_one_inj
    _ = 2 := by simp

end SignDichotomy

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem card_two_torsion_le_sixteen {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {V : Type*} [Group V] (ψ : V →* (Fin Tag.E8.rank → Lˣ)) (hψ : Function.Injective ψ)
    (hT : ∀ v, ψ v ∈ fixedCharTuples e8P4V Fr) : Nat.card {v : V // v ^ 2 = 1} ≤ 16 := by
  classical
  have hsq : ∀ v : {v : V // v ^ 2 = 1}, ∀ j, cg (ψ v.1) j ^ 2 = 1 := by
    intro v j
    have h1 : ψ v.1 * ψ v.1 = 1 := by rw [← map_mul, ← pow_two, v.2, map_one]
    have h2 := CTTorus.rootChar_mul (ψ v.1) (ψ v.1) (e8P4col (ev j))
    rw [h1, CTTorus.rootChar_one] at h2
    rw [pow_two]
    exact h2.symm
  let φ : {v : V // v ^ 2 = 1} → (Fin 4 → {u : Lˣ // u ^ 2 = 1}) :=
    fun v j => ⟨cg (ψ v.1) j, hsq v j⟩
  have hφ : Function.Injective φ := by
    intro v w h
    apply Subtype.ext
    apply hψ
    refine cg_injective hFr (hT _) (hT _) fun j => ?_
    exact congrArg Subtype.val (congrFun h j)
  have : Finite {u : Lˣ // u ^ 2 = 1} := finite_sq_eq_one
  calc Nat.card {v : V // v ^ 2 = 1} ≤ Nat.card (Fin 4 → {u : Lˣ // u ^ 2 = 1}) :=
        Nat.card_le_card_of_injective φ hφ
    _ = (Nat.card {u : Lˣ // u ^ 2 = 1}) ^ 4 := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_left card_sq_eq_one_le_two 4
    _ = 16 := by norm_num

end Count

end CFSG.RankThree.PartOne.KE8F
