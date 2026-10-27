module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueBasic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace NoOffUO

open MulAction

theorem mul_le_pow_self {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : p * k ≤ p ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    calc p * (k + 1) = p * k + p := by ring
      _ ≤ p ^ k + p ^ k := by omega
      _ ≤ p ^ k * p := by nlinarith
      _ = p ^ (k + 1) := by ring

theorem mul_lt_pow_self {p k : ℕ} (hp : 3 ≤ p) (hk : 2 ≤ k) : p * k < p ^ k := by
  induction k, hk using Nat.le_induction with
  | base => nlinarith
  | succ k hk ih =>
    have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    calc p * (k + 1) = p * k + p := by ring
      _ < p ^ k + p ^ k := by omega
      _ ≤ p ^ k * p := by nlinarith
      _ = p ^ (k + 1) := by ring

section Count

variable {X : Type} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
theorem smul_smul_eq_of_comm {A : Subgroup (Equiv.Perm X)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {a : A} (b : A) {x : X} (hx : a • x = x) : a • (b • x) = b • x := by
  rw [smul_smul, show a * b = b * a from Subtype.ext (hA _ a.2 _ b.2), mul_smul, hx]

omit [Fintype X] [DecidableEq X] in
theorem mem_orbit_out (A : Subgroup (Equiv.Perm X)) (x : X) :
    x ∈ orbit A (Quotient.mk'' x : orbitRel.Quotient A X).out := by
  have h : (Quotient.mk'' (Quotient.mk'' x : orbitRel.Quotient A X).out :
      orbitRel.Quotient A X) = Quotient.mk'' x := Quotient.out_eq' _
  have h2 : (Quotient.mk'' x : orbitRel.Quotient A X).out ∈ orbit A x := Quotient.exact h
  exact mem_orbit_symm.mp h2

omit [Fintype X] [DecidableEq X] in
theorem card_le_prod_card_orbit {A : Subgroup (Equiv.Perm X)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) [Fintype (orbitRel.Quotient A X)] :
    Nat.card A ≤ ∏ ω : orbitRel.Quotient A X, Nat.card (orbit A ω.out) := by
  have hbot : (⨅ ω : orbitRel.Quotient A X, stabilizer A ω.out) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨b, hb⟩ := mem_orbit_out A x
    change b • _ = x at hb
    have hfix : a • (Quotient.mk'' x : orbitRel.Quotient A X).out =
        (Quotient.mk'' x : orbitRel.Quotient A X).out :=
      Subgroup.mem_iInf.mp ha _
    have h := smul_smul_eq_of_comm hA b hfix
    rw [hb] at h
    exact h
  have h1 : Nat.card A = (⨅ ω : orbitRel.Quotient A X, stabilizer A ω.out).index := by
    rw [hbot, Subgroup.index_bot]
  rw [h1]
  refine (Subgroup.index_iInf_le _).trans_eq (Finset.prod_congr rfl fun ω _ => ?_)
  rw [index_stabilizer, Nat.card_coe_set_eq]

omit [DecidableEq X] in
theorem sum_card_orbit (A : Subgroup (Equiv.Perm X)) [Fintype (orbitRel.Quotient A X)] :
    ∑ ω : orbitRel.Quotient A X, Nat.card (orbit A ω.out) = Fintype.card X := by
  have h := Nat.card_congr (selfEquivSigmaOrbits A X)
  rw [Nat.card_sigma] at h
  rw [← h, Nat.card_eq_fintype_card]

omit [DecidableEq X] in
theorem exists_two_le_card_orbit {A : Subgroup (Equiv.Perm X)} (hne : A ≠ ⊥) :
    ∃ ω : orbitRel.Quotient A X, 2 ≤ Nat.card (orbit A ω.out) := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨x, hx⟩ : ∃ x, (a : Equiv.Perm X) x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact ha1 (Subtype.ext (Equiv.ext hcon))
  refine ⟨Quotient.mk'' x, ?_⟩
  obtain ⟨b, hb⟩ := mem_orbit_out A x
  change b • _ = x at hb
  have hxo : x ∈ orbit A (Quotient.mk'' x : orbitRel.Quotient A X).out := ⟨b, hb⟩
  have hax : (a • x) ∈ orbit A (Quotient.mk'' x : orbitRel.Quotient A X).out :=
    ⟨a * b, by show (a * b) • _ = _; rw [mul_smul, hb]⟩
  have hne' : (⟨x, hxo⟩ : orbit A (Quotient.mk'' x : orbitRel.Quotient A X).out) ≠ ⟨a • x, hax⟩ :=
    fun h => hx (congrArg Subtype.val h).symm
  have : Nontrivial (orbit A (Quotient.mk'' x : orbitRel.Quotient A X).out) := ⟨⟨_, _, hne'⟩⟩
  exact Finite.one_lt_card

omit [DecidableEq X] in
theorem card_mul_card_lt_pow {p : ℕ} (hp : 3 ≤ p) {A : Subgroup (Equiv.Perm X)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hne : A ≠ ⊥) {F : Set (X → ZMod p)}
    (hF : ∀ s ∈ F, ∀ s' ∈ F, ∀ a ∈ A, ∀ x, s x = s' x → s (a x) = s' (a x)) :
    Nat.card F * Nat.card A < p ^ Fintype.card X := by
  have : NeZero p := ⟨by omega⟩
  let _ : Fintype (orbitRel.Quotient A X) := Fintype.ofFinite _
  have hk1 : ∀ ω : orbitRel.Quotient A X, 1 ≤ Nat.card (orbit A ω.out) := fun ω => by
    have : Nonempty (orbit A ω.out) := ⟨⟨ω.out, mem_orbit_self _⟩⟩
    exact Nat.card_pos
  have h1 : Nat.card F ≤ p ^ Fintype.card (orbitRel.Quotient A X) := by
    have hinj : Function.Injective
        (fun (s : F) (ω : orbitRel.Quotient A X) => (s : X → ZMod p) ω.out) := by
      intro s s' h
      apply Subtype.ext
      funext x
      obtain ⟨a, ha⟩ := mem_orbit_out A x
      change a • _ = x at ha
      have := hF s s.2 s' s'.2 a a.2 _ (congrFun h (Quotient.mk'' x))
      rw [← ha]
      exact this
    calc Nat.card F ≤ Nat.card (orbitRel.Quotient A X → ZMod p) :=
          Nat.card_le_card_of_injective _ hinj
      _ = p ^ Fintype.card (orbitRel.Quotient A X) := by
          rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  obtain ⟨ω₀, hω₀⟩ := exists_two_le_card_orbit hne
  calc Nat.card F * Nat.card A
      ≤ p ^ Fintype.card (orbitRel.Quotient A X) *
          ∏ ω : orbitRel.Quotient A X, Nat.card (orbit A ω.out) :=
        Nat.mul_le_mul h1 (card_le_prod_card_orbit hA)
    _ = ∏ ω : orbitRel.Quotient A X, (p * Nat.card (orbit A ω.out)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ < ∏ ω : orbitRel.Quotient A X, p ^ Nat.card (orbit A ω.out) := by
        refine Finset.prod_lt_prod₀ (fun ω _ => by have := hk1 ω; positivity)
          (fun ω _ => mul_le_pow_self (by omega) (hk1 ω)) ⟨ω₀, Finset.mem_univ _, ?_⟩
        exact mul_lt_pow_self hp hω₀
    _ = p ^ Fintype.card X := by rw [Finset.prod_pow_eq_pow_sum, sum_card_orbit]

end Count

section Group

variable {G : Type} [Group G] {p r : ℕ}

open Multiplicative

@[expose] def GGMonoAct (ι : Multiplicative (Fin r → ZMod p) →* G) (g : G) : Prop :=
  ∃ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ), ∀ s : Fin r → ZMod p,
    g⁻¹ * ι (ofAdd s) * g = ι (ofAdd fun i => (η i : ZMod p) * s (π i))

theorem monoAct_unique [Fact p.Prime] {ι : Multiplicative (Fin r → ZMod p) →* G}
    (hinj : Function.Injective ι) {g : G} {π π' : Equiv.Perm (Fin r)} {η η' : Fin r → (ZMod p)ˣ}
    (h : ∀ s : Fin r → ZMod p, g⁻¹ * ι (ofAdd s) * g = ι (ofAdd fun i => (η i : ZMod p) * s (π i)))
    (h' : ∀ s : Fin r → ZMod p,
      g⁻¹ * ι (ofAdd s) * g = ι (ofAdd fun i => (η' i : ZMod p) * s (π' i))) :
    π = π' ∧ η = η' := by
  classical
  have key : ∀ i, π' i = π i ∧ η i = η' i := by
    intro i
    have e := hinj ((h (Pi.single (π i) 1)).symm.trans (h' (Pi.single (π i) 1)))
    have e2 := congrFun (congrArg toAdd e) i
    simp only [toAdd_ofAdd, Pi.single_eq_same, mul_one] at e2
    by_cases hπ : π' i = π i
    · rw [hπ, Pi.single_eq_same, mul_one] at e2
      exact ⟨hπ, Units.ext e2⟩
    · rw [Pi.single_eq_of_ne hπ, mul_zero] at e2
      exact absurd e2 (η i).ne_zero
  exact ⟨Equiv.ext fun i => (key i).1.symm, funext fun i => (key i).2⟩

theorem card_range_eq [NeZero p] {ι : Multiplicative (Fin r → ZMod p) →* G}
    (hinj : Function.Injective ι) : Nat.card ι.range = p ^ r := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem noOffender_of_monoAct [Finite G] (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Multiplicative (Fin r → ZMod p) →* G} (hinj : Function.Injective ι)
    {N Bs : Subgroup G} (hrange : ι.range = Bs)
    (hmono : ∀ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 → GGMonoAct ι g) :
    GGNoOffender p N Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  intro E hEN hEB hE
  have hdata : ∀ e : E, ∃ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ),
      ∀ s : Fin r → ZMod p,
        (e : G)⁻¹ * ι (ofAdd s) * e = ι (ofAdd fun i => (η i : ZMod p) * s (π i)) :=
    fun e => hmono e (hEN e.2) (hEB e.2) (hE.2 e e.2)
  choose π η hπη using hdata
  let ρ : E →* Equiv.Perm (Fin r) :=
    { toFun := π
      map_one' := by
        refine (monoAct_unique hinj (hπη 1) (π' := 1) (η' := 1) fun s => ?_).1
        simp
      map_mul' := fun e e' => by
        refine (monoAct_unique hinj (hπη (e * e')) (π' := π e * π e')
          (η' := fun i => η e' i * η e (π e' i)) fun s => ?_).1
        calc ((e * e' : E) : G)⁻¹ * ι (ofAdd s) * (e * e' : E)
            = (e' : G)⁻¹ * ((e : G)⁻¹ * ι (ofAdd s) * e) * e' := by
              simp only [Subgroup.coe_mul]
              group
          _ = _ := by rw [hπη e s, hπη e' _]
          _ = _ := by
              congr 2
              funext i
              simp only [Units.val_mul, Equiv.Perm.mul_apply]
              ring }
  have hρ : ∀ e, ρ e = π e := fun _ => rfl
  have hdiag : ∀ e : E, π e = 1 → ∀ b ∈ Bs, (e : G) * b = b * e := by
    intro e he b hb
    have hpow : ∀ k : ℕ, ∀ s : Fin r → ZMod p, ((e : G) ^ k)⁻¹ * ι (ofAdd s) * (e : G) ^ k =
        ι (ofAdd fun i => (η e i : ZMod p) ^ k * s i) := by
      intro k
      induction k with
      | zero => intro s; simp
      | succ k ih =>
        intro s
        calc ((e : G) ^ (k + 1))⁻¹ * ι (ofAdd s) * (e : G) ^ (k + 1)
            = (e : G)⁻¹ * (((e : G) ^ k)⁻¹ * ι (ofAdd s) * (e : G) ^ k) * e := by group
          _ = _ := by
              rw [ih, hπη e, he]
              congr 2
              funext i
              simp only [Equiv.Perm.coe_one, id, pow_succ]
              ring
    have h1 : ∀ i, (η e i : ZMod p) = 1 := by
      intro i
      have h2 := hpow p (Pi.single i 1)
      rw [hE.2 e e.2, inv_one, one_mul, mul_one] at h2
      have h3 := congrFun (congrArg toAdd (hinj h2)) i
      simp only [toAdd_ofAdd, Pi.single_eq_same, mul_one, ZMod.pow_card] at h3
      exact h3.symm
    rw [← hrange] at hb
    obtain ⟨t, rfl⟩ := hb
    have h4 : (e : G)⁻¹ * ι t * e = ι t := by
      have := hπη e (toAdd t)
      simp only [ofAdd_toAdd, h1, one_mul, he, Equiv.Perm.coe_one, id] at this
      exact this
    calc (e : G) * ι t = (e : G) * ((e : G)⁻¹ * ι t * e) := by rw [h4]
      _ = ι t * e := by group
  have hAcomm : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, a * b = b * a := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (TableB.IsElemAbelian.comm hE e.2 e'.2)
  by_cases hA : ρ.range = ⊥
  · left
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : π ⟨e, he⟩ = 1 := by
      have : ρ ⟨e, he⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hA, Subgroup.mem_bot] at this
      exact this
    exact (hdiag ⟨e, he⟩ h1 b hb).symm
  right
  set F : Set (Fin r → ZMod p) := {s | ι (ofAdd s) ∈ Subgroup.centralizer (E : Set G)} with hFdef
  have hFprop : ∀ s ∈ F, ∀ s' ∈ F, ∀ a ∈ ρ.range, ∀ x, s x = s' x → s (a x) = s' (a x) := by
    rintro s hs s' hs' _ ⟨e, rfl⟩ x hx
    have key : ∀ t ∈ F, ∀ i, t i = (η e i : ZMod p) * t (π e i) := by
      intro t ht i
      have h1 : (e : G)⁻¹ * ι (ofAdd t) * e = ι (ofAdd t) := by
        have h0 := Subgroup.mem_centralizer_iff.mp ht e e.2
        calc (e : G)⁻¹ * ι (ofAdd t) * e = (e : G)⁻¹ * (e * ι (ofAdd t)) := by
              rw [mul_assoc, h0]
          _ = ι (ofAdd t) := by group
      have h2 := hinj ((hπη e t).symm.trans h1)
      have h3 := congrFun (congrArg toAdd h2) i
      simp only [toAdd_ofAdd] at h3
      exact h3.symm
    have e1 := key s hs x
    have e2 := key s' hs' x
    rw [hx] at e1
    exact mul_left_cancel₀ (η e x).ne_zero (e1.symm.trans e2)
  have hcount := card_mul_card_lt_pow hp3 hAcomm hA hFprop
  have hCF : Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) = Nat.card F := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun s : F => (⟨ι (ofAdd (s : Fin r → ZMod p)), hrange ▸ ⟨_, rfl⟩, s.2⟩ :
        (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G)))
          ⟨fun s s' h => ?_, fun b => ?_⟩)).symm
    · exact Subtype.ext (by simpa using hinj (congrArg Subtype.val h))
    · obtain ⟨t, ht⟩ : (b : G) ∈ ι.range := hrange ▸ b.2.1
      refine ⟨⟨toAdd t, ?_⟩, Subtype.ext ?_⟩
      · show ι (ofAdd (toAdd t)) ∈ Subgroup.centralizer (E : Set G)
        rw [ofAdd_toAdd, ht]
        exact b.2.2
      · change ι (ofAdd (toAdd t)) = b
        rw [ofAdd_toAdd, ht]
  have hker : Nat.card ρ.ker ≤ Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun k : ρ.ker => (⟨((k : E) : G), (k : E).2, Subgroup.mem_centralizer_iff.mpr
        fun b hb => (hdiag k k.2 b hb).symm⟩ :
          (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G))) fun k k' h => ?_
    have h' := congrArg (fun y : (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) =>
      (y : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hE' := Subgroup.card_ker_mul_card_range ρ
  have hBs : Nat.card Bs = p ^ r := by
    have : NeZero p := ⟨hp.ne_zero⟩
    rw [← hrange, card_range_eq hinj]
  have hpos : 0 < Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := Nat.card_pos
  rw [Fintype.card_fin] at hcount
  rw [hCF, hBs, ← hE']
  calc Nat.card F * (Nat.card ρ.ker * Nat.card ρ.range)
      ≤ Nat.card F * (Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) *
          Nat.card ρ.range) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hker)
    _ = Nat.card F * Nat.card ρ.range *
          Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by ring
    _ < p ^ r * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) :=
        Nat.mul_lt_mul_of_pos_right hcount hpos

end Group

end NoOffUO

end CFSG.StandardType
