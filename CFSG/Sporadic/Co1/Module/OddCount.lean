module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open MulAction

section DoubleCount

variable {G X Ω : Type*} [Group G] [MulAction G X] [MulAction G Ω]

theorem card_stabilizer_mul_ncard_orbit (G : Type*) {Y : Type*} [Group G] [MulAction G Y] (y : Y) :
    Nat.card (stabilizer G y) * (orbit G y).ncard = Nat.card G := by
  have h3 := Subgroup.card_mul_index (stabilizer G y)
  rw [MulAction.index_stabilizer G y] at h3
  exact h3

theorem ncard_orbit_filter_smul (R : X → Ω → Prop)
    (hR : ∀ (g : G) (x : X) (ω : Ω), R (g • x) (g • ω) ↔ R x ω) (x₀ : X) (ω₀ : Ω) (g : G) :
    {ω ∈ orbit G ω₀ | R (g • x₀) ω}.ncard = {ω ∈ orbit G ω₀ | R x₀ ω}.ncard := by
  have h : {ω ∈ orbit G ω₀ | R (g • x₀) ω} = (fun ω => g • ω) '' {ω ∈ orbit G ω₀ | R x₀ ω} := by
    ext ω
    constructor
    · rintro ⟨⟨h, rfl⟩, hr⟩
      refine ⟨(g⁻¹ * h) • ω₀, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · have := (hR g⁻¹ (g • x₀) (h • ω₀)).2 hr
        rwa [← mul_smul, ← mul_smul, inv_mul_cancel, one_smul] at this
      · show g • (g⁻¹ * h) • ω₀ = h • ω₀
        rw [← mul_smul, mul_inv_cancel_left]
    · rintro ⟨ω', ⟨⟨h, rfl⟩, hr⟩, rfl⟩
      exact ⟨⟨g * h, by show (g * h) • ω₀ = g • h • ω₀; rw [mul_smul]⟩, (hR g x₀ _).2 hr⟩
  rw [h, Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem ncard_orbit_filter_smul' (R : X → Ω → Prop)
    (hR : ∀ (g : G) (x : X) (ω : Ω), R (g • x) (g • ω) ↔ R x ω) (x₀ : X) (ω₀ : Ω) (g : G) :
    {x ∈ orbit G x₀ | R x (g • ω₀)}.ncard = {x ∈ orbit G x₀ | R x ω₀}.ncard := by
  have h : {x ∈ orbit G x₀ | R x (g • ω₀)} = (fun x => g • x) '' {x ∈ orbit G x₀ | R x ω₀} := by
    ext x
    constructor
    · rintro ⟨⟨h, rfl⟩, hr⟩
      refine ⟨(g⁻¹ * h) • x₀, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · have := (hR g⁻¹ (h • x₀) (g • ω₀)).2 hr
        rwa [← mul_smul, ← mul_smul, inv_mul_cancel, one_smul] at this
      · show g • (g⁻¹ * h) • x₀ = h • x₀
        rw [← mul_smul, mul_inv_cancel_left]
    · rintro ⟨x', ⟨⟨h, rfl⟩, hr⟩, rfl⟩
      exact ⟨⟨g * h, by show (g * h) • x₀ = g • h • x₀; rw [mul_smul]⟩, (hR g _ ω₀).2 hr⟩
  rw [h, Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem card_stabilizer_mul_ncard_eq [Finite G] (R : X → Ω → Prop)
    (hR : ∀ (g : G) (x : X) (ω : Ω), R (g • x) (g • ω) ↔ R x ω) (x₀ : X) (ω₀ : Ω) :
    Nat.card (stabilizer G x₀) * {x ∈ orbit G x₀ | R x ω₀}.ncard =
      Nat.card (stabilizer G ω₀) * {ω ∈ orbit G ω₀ | R x₀ ω}.ncard := by
  classical
  have hfX : (orbit G x₀).Finite := Set.finite_range _
  have hfΩ : (orbit G ω₀).Finite := Set.finite_range _
  set s : Finset X := hfX.toFinset with hs
  set t : Finset Ω := hfΩ.toFinset with ht
  have hmem_s : ∀ x, x ∈ s ↔ x ∈ orbit G x₀ := fun x => hfX.mem_toFinset
  have hmem_t : ∀ ω, ω ∈ t ↔ ω ∈ orbit G ω₀ := fun ω => hfΩ.mem_toFinset
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s) (t := t) R
  have hA : ∀ x ∈ s, (t.bipartiteAbove R x).card = {ω ∈ orbit G ω₀ | R x₀ ω}.ncard := by
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem_s x).1 hx
    rw [← ncard_orbit_filter_smul R hR x₀ ω₀ g, ← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, hmem_t]
  have hB : ∀ ω ∈ t, (s.bipartiteBelow R ω).card = {x ∈ orbit G x₀ | R x ω₀}.ncard := by
    intro ω hω
    obtain ⟨g, rfl⟩ := (hmem_t ω).1 hω
    rw [← ncard_orbit_filter_smul' R hR x₀ ω₀ g, ← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, hmem_s]
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul] at hdc
  have hsc : s.card = (orbit G x₀).ncard := by
    rw [hs, Set.ncard_eq_toFinset_card _ hfX]
  have htc : t.card = (orbit G ω₀).ncard := by
    rw [ht, Set.ncard_eq_toFinset_card _ hfΩ]
  have h1 := card_stabilizer_mul_ncard_orbit G x₀
  have h2 := card_stabilizer_mul_ncard_orbit G ω₀
  rw [← hsc] at h1
  rw [← htc] at h2
  have hpos : 0 < t.card := by
    rw [Finset.card_pos]
    exact ⟨ω₀, (hmem_t ω₀).2 (mem_orbit_self ω₀)⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  generalize Nat.card (stabilizer G x₀) = C at *
  generalize Nat.card (stabilizer G ω₀) = H at *
  generalize {x ∈ orbit G x₀ | R x ω₀}.ncard = S at *
  generalize {ω ∈ orbit G ω₀ | R x₀ ω}.ncard = F at *
  calc t.card * (C * S) = C * (t.card * S) := by ring
    _ = C * (s.card * F) := by rw [hdc]
    _ = (C * s.card) * F := by ring
    _ = (H * t.card) * F := by rw [h1, h2]
    _ = t.card * (H * F) := by ring

end DoubleCount

section Conj

variable {G : Type*} [Group G]

structure ConjSet (G : Type*) where
  val : G

structure ConjPair (G : Type*) where
  fst : G
  snd : G

instance : MulAction G (ConjSet G) where
  smul g x := ⟨g * x.val * g⁻¹⟩
  one_smul x := by
    show ConjSet.mk (1 * x.val * 1⁻¹) = x
    simp
  mul_smul g h x := by
    show ConjSet.mk (g * h * x.val * (g * h)⁻¹) = ConjSet.mk (g * (h * x.val * h⁻¹) * g⁻¹)
    simp [mul_assoc]

instance : MulAction G (ConjPair G) where
  smul g x := ⟨g * x.fst * g⁻¹, g * x.snd * g⁻¹⟩
  one_smul x := by
    show ConjPair.mk (1 * x.fst * 1⁻¹) (1 * x.snd * 1⁻¹) = x
    simp
  mul_smul g h x := by
    show ConjPair.mk (g * h * x.fst * (g * h)⁻¹) (g * h * x.snd * (g * h)⁻¹) =
      ConjPair.mk (g * (h * x.fst * h⁻¹) * g⁻¹) (g * (h * x.snd * h⁻¹) * g⁻¹)
    simp [mul_assoc]

theorem ConjSet.smul_val (g : G) (x : ConjSet G) : (g • x).val = g * x.val * g⁻¹ := rfl

theorem ConjPair.smul_fst (g : G) (x : ConjPair G) : (g • x).fst = g * x.fst * g⁻¹ := rfl

theorem ConjPair.smul_snd (g : G) (x : ConjPair G) : (g • x).snd = g * x.snd * g⁻¹ := rfl

omit [Group G] in
theorem ConjSet.injective_val : Function.Injective (ConjSet.val : ConjSet G → G) := by
  rintro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

omit [Group G] in
theorem ConjPair.injective_mk :
    Function.Injective (fun p : G × G => (⟨p.1, p.2⟩ : ConjPair G)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [ConjPair.mk.injEq] at h
  rw [h.1, h.2]

theorem stabilizer_conjSet (a : G) : stabilizer G (⟨a⟩ : ConjSet G) = Subgroup.centralizer {a} := by
  ext g
  rw [mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  show ConjSet.mk (g * a * g⁻¹) = ConjSet.mk a ↔ g * a = a * g
  constructor
  · intro h
    have h' : g * a * g⁻¹ = a := congrArg ConjSet.val h
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h']
  · intro h
    rw [h]
    congr 1
    group

theorem stabilizer_conjPair (a b : G) :
    stabilizer G (⟨a, b⟩ : ConjPair G) = Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := by
  ext g
  rw [Subgroup.mem_inf, ← stabilizer_conjSet, ← stabilizer_conjSet, mem_stabilizer_iff,
    mem_stabilizer_iff, mem_stabilizer_iff]
  show ConjPair.mk (g * a * g⁻¹) (g * b * g⁻¹) = ConjPair.mk a b ↔
    ConjSet.mk (g * a * g⁻¹) = ConjSet.mk a ∧ ConjSet.mk (g * b * g⁻¹) = ConjSet.mk b
  simp only [ConjPair.mk.injEq, ConjSet.mk.injEq]

variable {Ω : Type*} [MulAction G Ω]

theorem card_centralizer_mul_ncard_conj_inter [Finite G] (a : G) (ω₀ : Ω) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) *
        {t : G | t ∈ stabilizer G ω₀ ∧ IsConj a t}.ncard =
      Nat.card (stabilizer G ω₀) * {ω ∈ orbit G ω₀ | a • ω = ω}.ncard := by
  have h := card_stabilizer_mul_ncard_eq (G := G) (X := ConjSet G) (Ω := Ω)
    (fun x ω => x.val • ω = ω) (by
      intro g x ω
      show (g * x.val * g⁻¹) • g • ω = g • ω ↔ x.val • ω = ω
      rw [mul_smul, mul_smul, inv_smul_smul]
      exact (MulAction.injective g).eq_iff) ⟨a⟩ ω₀
  rw [stabilizer_conjSet] at h
  have hset : {x ∈ orbit G (⟨a⟩ : ConjSet G) | x.val • ω₀ = ω₀} =
      (fun t : G => (⟨t⟩ : ConjSet G)) '' {t : G | t ∈ stabilizer G ω₀ ∧ IsConj a t} := by
    ext x
    constructor
    · rintro ⟨⟨g, rfl⟩, hx⟩
      refine ⟨g * a * g⁻¹, ⟨hx, isConj_iff.2 ⟨g, rfl⟩⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
      obtain ⟨g, hg⟩ := isConj_iff.1 hc
      exact ⟨⟨g, by show ConjSet.mk (g * a * g⁻¹) = ConjSet.mk t; rw [hg]⟩, ht⟩
  rw [hset, Set.ncard_image_of_injective _ (fun u v h => by simpa using congrArg ConjSet.val h)]
    at h
  exact h

theorem card_centralizer_inf_mul_ncard_pairs [Finite G] (a b : G) (ω₀ : Ω) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b}) *
        {p : G × G | p.1 ∈ stabilizer G ω₀ ∧ p.2 ∈ stabilizer G ω₀ ∧
          ∃ g : G, g * a * g⁻¹ = p.1 ∧ g * b * g⁻¹ = p.2}.ncard =
      Nat.card (stabilizer G ω₀) * {ω ∈ orbit G ω₀ | a • ω = ω ∧ b • ω = ω}.ncard := by
  have h := card_stabilizer_mul_ncard_eq (G := G) (X := ConjPair G) (Ω := Ω)
    (fun x ω => x.fst • ω = ω ∧ x.snd • ω = ω) (by
      intro g x ω
      show (g * x.fst * g⁻¹) • g • ω = g • ω ∧ (g * x.snd * g⁻¹) • g • ω = g • ω ↔
        x.fst • ω = ω ∧ x.snd • ω = ω
      rw [mul_smul, mul_smul, inv_smul_smul, mul_smul, mul_smul, inv_smul_smul]
      rw [(MulAction.injective g).eq_iff, (MulAction.injective g).eq_iff]) ⟨a, b⟩ ω₀
  rw [stabilizer_conjPair] at h
  have hset : {x ∈ orbit G (⟨a, b⟩ : ConjPair G) | x.fst • ω₀ = ω₀ ∧ x.snd • ω₀ = ω₀} =
      (fun p : G × G => (⟨p.1, p.2⟩ : ConjPair G)) ''
        {p : G × G | p.1 ∈ stabilizer G ω₀ ∧ p.2 ∈ stabilizer G ω₀ ∧
          ∃ g : G, g * a * g⁻¹ = p.1 ∧ g * b * g⁻¹ = p.2} := by
    ext x
    constructor
    · rintro ⟨⟨g, rfl⟩, hx1, hx2⟩
      exact ⟨(g * a * g⁻¹, g * b * g⁻¹), ⟨hx1, hx2, g, rfl, rfl⟩, rfl⟩
    · rintro ⟨⟨t, t'⟩, ⟨h1, h2, g, hg1, hg2⟩, rfl⟩
      exact ⟨⟨g, by
        show ConjPair.mk (g * a * g⁻¹) (g * b * g⁻¹) = ConjPair.mk t t'
        rw [hg1, hg2]⟩, h1, h2⟩
  rw [hset, Set.ncard_image_of_injective _ ConjPair.injective_mk] at h
  exact h

end Conj

section Subgroups

variable {G : Type*} [Group G]

theorem card_stabilizer_pair_mul_ncard_orbit [Finite G] (H : Subgroup G) (a b : G) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b}) *
        {p : G × G | ∃ n ∈ H, p = (n * a * n⁻¹, n * b * n⁻¹)}.ncard = Nat.card ↥H := by
  have h := Subgroup.card_mul_index (stabilizer H (⟨a, b⟩ : ConjPair G))
  rw [MulAction.index_stabilizer H (⟨a, b⟩ : ConjPair G)] at h
  have e1 : Nat.card (stabilizer H (⟨a, b⟩ : ConjPair G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b}) := by
    refine Nat.card_congr ?_
    refine ⟨fun n => ⟨(n.1 : G), ?_⟩, fun n => ⟨⟨(n.1 : G), ?_⟩, ?_⟩, fun n => ?_, fun n => ?_⟩
    · obtain ⟨n, hn⟩ := n
      have hn' := mem_stabilizer_iff.1 hn
      have h2 : (n : G) ∈ stabilizer G (⟨a, b⟩ : ConjPair G) := by
        rw [mem_stabilizer_iff]
        exact hn'
      rw [stabilizer_conjPair] at h2
      exact ⟨⟨n.2, (Subgroup.mem_inf.1 h2).1⟩, (Subgroup.mem_inf.1 h2).2⟩
    · exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 n.2).1).1
    · rw [mem_stabilizer_iff]
      have h2 : (n.1 : G) ∈ stabilizer G (⟨a, b⟩ : ConjPair G) := by
        rw [stabilizer_conjPair]
        exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 n.2).1.2, (Subgroup.mem_inf.1 n.2).2⟩
      exact mem_stabilizer_iff.1 h2
    · rfl
    · rfl
  have e2 : (orbit H (⟨a, b⟩ : ConjPair G)).ncard =
      {p : G × G | ∃ n ∈ H, p = (n * a * n⁻¹, n * b * n⁻¹)}.ncard := by
    have : {p : G × G | ∃ n ∈ H, p = (n * a * n⁻¹, n * b * n⁻¹)} =
        (fun x : ConjPair G => (x.fst, x.snd)) '' (orbit H (⟨a, b⟩ : ConjPair G)) := by
      ext p
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
        exact ⟨n, hn, rfl⟩
    rw [this, Set.ncard_image_of_injective]
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]
  rw [← e1, ← e2]
  exact h

end Subgroups

end CFSG.Sporadic.Co1.Module.Odd
