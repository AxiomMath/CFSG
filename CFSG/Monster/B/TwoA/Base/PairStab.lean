module

public import CFSG.Monster.CodeAut.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code MulAction

open scoped Pointwise

theorem bridgeQ_zero : bridgeQ 0 = 0 := by decide

theorem bridgeQ_one : bridgeQ 1 = 1 := by decide

theorem bridgeQ_two : bridgeQ 2 = 2 := by decide

theorem bridgeQ_three : bridgeQ 3 = 3 := by decide

theorem bridgeQ_inv_apply (i : Fin 24) : bridgeQ⁻¹ (bridgeQ i) = i := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

theorem conj_mem_AutPerm
    {g : Equiv.Perm (Fin 24)} (hg : g ∈ CFSG.Blueprint.NativeSporadic.M24) :
    bridgeQ⁻¹ * g * bridgeQ ∈ AutPerm :=
  (mem_AutPerm_iff_conj _).2 ⟨g, hg, fun i => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]⟩

theorem autPerm_maps_two (u v : Fin 24) (huv : u ≠ v) :
    ∃ p ∈ AutPerm, p 0 = u ∧ p 1 = v := by
  obtain ⟨g, g0, g1⟩ := CFSG.Sporadic.Mathieu.exists_smul_eq_two
    CFSG.Sporadic.Mathieu.m24_hyp (by decide) (by norm_num) (bridgeQ u) (bridgeQ v)
    (bridgeQ.injective.ne huv)
  refine ⟨bridgeQ⁻¹ * (g : Equiv.Perm (Fin 24)) * bridgeQ, conj_mem_AutPerm g.2, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_zero]
    have h : (g : Equiv.Perm (Fin 24)) 0 = bridgeQ u := g0
    rw [h, bridgeQ_inv_apply]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_one]
    have h : (g : Equiv.Perm (Fin 24)) 1 = bridgeQ v := g1
    rw [h, bridgeQ_inv_apply]

theorem autPerm_maps_four
    (u v w z : Fin 24) (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ∃ p ∈ AutPerm, p 0 = u ∧ p 1 = v ∧ p 2 = w ∧ p 3 = z := by
  have hq := bridgeQ.injective
  obtain ⟨g, g0, g1, g2, g3⟩ := CFSG.Sporadic.Mathieu.exists_smul_eq_four
    CFSG.Sporadic.Mathieu.m24_hyp (by decide) (by norm_num) (bridgeQ u) (bridgeQ v)
    (bridgeQ w) (bridgeQ z) (hq.ne huv) (hq.ne huw) (hq.ne huz) (hq.ne hvw) (hq.ne hvz)
    (hq.ne hwz)
  refine ⟨bridgeQ⁻¹ * (g : Equiv.Perm (Fin 24)) * bridgeQ, conj_mem_AutPerm g.2, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_zero]
    have h : (g : Equiv.Perm (Fin 24)) 0 = bridgeQ u := g0
    rw [h, bridgeQ_inv_apply]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_one]
    have h : (g : Equiv.Perm (Fin 24)) 1 = bridgeQ v := g1
    rw [h, bridgeQ_inv_apply]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_two]
    have h : (g : Equiv.Perm (Fin 24)) 2 = bridgeQ w := g2
    rw [h, bridgeQ_inv_apply]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_three]
    have h : (g : Equiv.Perm (Fin 24)) 3 = bridgeQ z := g3
    rw [h, bridgeQ_inv_apply]

theorem smul_autPerm (p : AutPerm) (i : Fin 24) : p • i = (p : Equiv.Perm (Fin 24)) i := rfl

@[expose] def pair01 : Set.powersetCard (Fin 24) 2 := CFSG.Sporadic.Mathieu.duad 0 1 (by decide)

@[expose] def Ppair : Subgroup AutPerm := MulAction.stabilizer AutPerm pair01

theorem smul_pair01 (p : AutPerm) :
    ((p • pair01 : Set.powersetCard (Fin 24) 2) : Finset (Fin 24)) =
      {(p : Equiv.Perm (Fin 24)) 0, (p : Equiv.Perm (Fin 24)) 1} := by
  change p • ((pair01 : Set.powersetCard (Fin 24) 2) : Finset (Fin 24)) = _
  rw [pair01, CFSG.Sporadic.Mathieu.duad_val, Finset.smul_finset_insert,
    Finset.smul_finset_singleton]
  rfl

private theorem pair_eq_iff (a b : Fin 24) (hab : a ≠ b) :
    ({a, b} : Finset (Fin 24)) = {0, 1} ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have ha : a ∈ ({0, 1} : Finset (Fin 24)) := h ▸ Finset.mem_insert_self a {b}
    have hb : b ∈ ({0, 1} : Finset (Fin 24)) := h ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self b)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
    · exact absurd rfl hab
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm 1 0

theorem mem_Ppair_iff (p : AutPerm) :
    p ∈ Ppair ↔ ((p : Equiv.Perm (Fin 24)) 0 = 0 ∧ (p : Equiv.Perm (Fin 24)) 1 = 1) ∨
      ((p : Equiv.Perm (Fin 24)) 0 = 1 ∧ (p : Equiv.Perm (Fin 24)) 1 = 0) := by
  rw [Ppair, MulAction.mem_stabilizer_iff, ← Subtype.coe_inj, smul_pair01, pair01,
    CFSG.Sporadic.Mathieu.duad_val]
  exact pair_eq_iff _ _ ((p : Equiv.Perm (Fin 24)).injective.ne (by decide))

theorem mem_Ppair_of_fix (p : AutPerm) (h0 : (p : Equiv.Perm (Fin 24)) 0 = 0)
    (h1 : (p : Equiv.Perm (Fin 24)) 1 = 1) : p ∈ Ppair :=
  (mem_Ppair_iff p).2 (.inl ⟨h0, h1⟩)

theorem Ppair_apply_mem {p : AutPerm} (hp : p ∈ Ppair) {i : Fin 24} (hi : i = 0 ∨ i = 1) :
    (p : Equiv.Perm (Fin 24)) i = 0 ∨ (p : Equiv.Perm (Fin 24)) i = 1 := by
  rcases (mem_Ppair_iff p).1 hp with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hi with rfl | rfl <;> simp_all

theorem Ppair_apply_ne {p : AutPerm} (hp : p ∈ Ppair) {i : Fin 24} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (p : Equiv.Perm (Fin 24)) i ≠ 0 ∧ (p : Equiv.Perm (Fin 24)) i ≠ 1 := by
  have hinj := (p : Equiv.Perm (Fin 24)).injective
  rcases (mem_Ppair_iff p).1 hp with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · exact ⟨fun h => h0 (hinj (h.trans e0.symm)), fun h => h1 (hinj (h.trans e1.symm))⟩
  · exact ⟨fun h => h1 (hinj (h.trans e1.symm)), fun h => h0 (hinj (h.trans e0.symm))⟩

instance isPretransitive_duads :
    MulAction.IsPretransitive AutPerm (Set.powersetCard (Fin 24) 2) where
  exists_smul_eq s t := by
    have key : ∀ s : Set.powersetCard (Fin 24) 2, ∃ p : AutPerm, p • pair01 = s := by
      intro s
      obtain ⟨u, v, huv, rfl⟩ := CFSG.Sporadic.Mathieu.exists_duad s
      obtain ⟨p, hp, h0, h1⟩ := autPerm_maps_two u v huv
      refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
      rw [smul_pair01, CFSG.Sporadic.Mathieu.duad_val]
      change ({p 0, p 1} : Finset (Fin 24)) = {u, v}
      rw [h0, h1]
    obtain ⟨a, ha⟩ := key s
    obtain ⟨b, hb⟩ := key t
    exact ⟨b * a⁻¹, by rw [← ha, ← hb, mul_smul, inv_smul_smul]⟩

theorem natCard_duads : Nat.card (Set.powersetCard (Fin 24) 2) = 276 := by
  rw [Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem natCard_Ppair : Nat.card Ppair = 887040 := by
  have h1 := Subgroup.index_mul_card Ppair
  rw [Ppair, MulAction.index_stabilizer_of_transitive, natCard_duads, card_AutPerm] at h1
  rw [Ppair]
  omega

abbrev Rest : Type := {i : Fin 24 // i ≠ 0 ∧ i ≠ 1}

@[expose, instance_reducible] def restAction : MulAction Ppair Rest where
  smul p i := ⟨((p : AutPerm) : Equiv.Perm (Fin 24)) i, Ppair_apply_ne p.2 i.2.1 i.2.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] restAction

theorem coe_smul_rest (p : Ppair) (i : Rest) :
    ((p • i : Rest) : Fin 24) = ((p : AutPerm) : Equiv.Perm (Fin 24)) i := rfl

@[expose] def toPpair (p : Equiv.Perm (Fin 24)) (hp : p ∈ AutPerm) (h0 : p 0 = 0) (h1 : p 1 = 1) :
    Ppair :=
  ⟨⟨p, hp⟩, mem_Ppair_of_fix ⟨p, hp⟩ h0 h1⟩

theorem isMultiplyPretransitive_rest :
    MulAction.IsMultiplyPretransitive Ppair Rest 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  have key : ∀ x y : Rest, x ≠ y → ∃ g : Ppair,
      ((g : AutPerm) : Equiv.Perm (Fin 24)) 2 = x ∧
        ((g : AutPerm) : Equiv.Perm (Fin 24)) 3 = y := by
    intro x y hxy
    have hxy' : (x : Fin 24) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨p, hp, h0, h1, h2, h3⟩ := autPerm_maps_four 0 1 x y (by decide) (Ne.symm x.2.1)
      (Ne.symm y.2.1) (Ne.symm x.2.2) (Ne.symm y.2.2) hxy'
    exact ⟨toPpair p hp h0 h1, h2, h3⟩
  obtain ⟨g, g2, g3⟩ := key a b hab
  obtain ⟨g', g2', g3'⟩ := key c d hcd
  refine ⟨g' * g⁻¹, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [mul_smul, coe_smul_rest]
    have : ((g⁻¹ • a : Rest) : Fin 24) = 2 := by
      rw [coe_smul_rest, ← g2]
      change ((g : AutPerm) : Equiv.Perm (Fin 24))⁻¹ (((g : AutPerm) : Equiv.Perm (Fin 24)) 2) = 2
      exact Equiv.symm_apply_apply _ _
    rw [this, g2']
  · rw [mul_smul, coe_smul_rest]
    have : ((g⁻¹ • b : Rest) : Fin 24) = 3 := by
      rw [coe_smul_rest, ← g3]
      change ((g : AutPerm) : Equiv.Perm (Fin 24))⁻¹ (((g : AutPerm) : Equiv.Perm (Fin 24)) 3) = 3
      exact Equiv.symm_apply_apply _ _
    rw [this, g3']

private theorem swap01_not_mem : B 1 ∘ ⇑(Equiv.swap (0 : Fin 24) 1) ∉ C := by decide +kernel

private theorem B1_mem : B 1 ∈ C := B_mem_C 1

theorem eq_one_of_fix_rest {p : Ppair} (h : ∀ i : Rest, p • i = i) : p = 1 := by
  set q : Equiv.Perm (Fin 24) := ((p : AutPerm) : Equiv.Perm (Fin 24)) with hq
  have hfix : ∀ i : Fin 24, i ≠ 0 → i ≠ 1 → q i = i := fun i h0 h1 =>
    congrArg Subtype.val (h ⟨i, h0, h1⟩)
  rcases (mem_Ppair_iff (p : AutPerm)).1 p.2 with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases h0 : i = 0
    · subst h0; exact e0
    by_cases h1 : i = 1
    · subst h1; exact e1
    exact hfix i h0 h1
  · exfalso
    have hqs : q = Equiv.swap 0 1 := by
      apply Equiv.ext
      intro i
      by_cases h0 : i = 0
      · subst h0; rw [e0]; rfl
      by_cases h1 : i = 1
      · subst h1; rw [e1]; rfl
      rw [hfix i h0 h1, Equiv.swap_apply_of_ne_of_ne h0 h1]
    have hmem : B 1 ∘ ⇑q ∈ C := comp_mem_of_mem_AutPerm (p : AutPerm).2 B1_mem
    rw [hqs] at hmem
    exact swap01_not_mem hmem

instance faithfulSMul_rest : FaithfulSMul Ppair Rest where
  eq_of_smul_eq_smul {p p'} h := by
    have h1 : p'⁻¹ * p = 1 := eq_one_of_fix_rest fun i => by
      rw [mul_smul, h i, inv_smul_smul]
    exact (inv_mul_eq_one.1 h1).symm

theorem natCard_rest : Nat.card Rest = 22 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem eq_bot_of_normal_twoGroup {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] (hprim : MulAction.IsPreprimitive G X) (hX : Nat.card X = 22)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  rw [one_smul]
  have hB := MulAction.IsBlock.orbit_of_normal (G := G) (N := N) x
  rcases hprim.isTrivialBlock_of_isBlock hB with hsub | huniv
  · exact hsub (MulAction.mem_orbit x (⟨n, hn⟩ : N)) (MulAction.mem_orbit_self x)
  · exfalso
    have hcard : (MulAction.orbit N x).ncard = 22 := by
      rw [huniv, Set.ncard_univ, hX]
    have hdvd : (MulAction.orbit N x).ncard ∣ Nat.card N := by
      rw [← MulAction.index_stabilizer N x]
      exact Subgroup.index_dvd_card _
    rw [hcard] at hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk] at hdvd
    have h11 : 11 ∣ 2 ^ k := Nat.dvd_trans (by norm_num : 11 ∣ 22) hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h11
    omega

theorem pCore_Ppair : CFSG.pCore 2 Ppair = ⊥ :=
  eq_bot_of_normal_twoGroup (isPreprimitive_of_is_two_pretransitive isMultiplyPretransitive_rest)
    natCard_rest (CFSG.pCore_isPGroup)

theorem native_pair_stabilizer_two_core_trivial :
    (∀ p : AutPerm, p ∈ Ppair ↔ ((p : Equiv.Perm (Fin 24)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 24)) 1 = 1) ∨ ((p : Equiv.Perm (Fin 24)) 0 = 1 ∧
      (p : Equiv.Perm (Fin 24)) 1 = 0)) ∧
    FaithfulSMul Ppair Rest ∧ MulAction.IsMultiplyPretransitive Ppair Rest 2 ∧
    (∀ p : Ppair, (∀ i : Fin 24, i ≠ 0 → i ≠ 1 → ((p : AutPerm) : Equiv.Perm (Fin 24)) i = i) →
      p = 1) ∧
    (∀ a b c d : Fin 24, a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 → c ≠ 0 → c ≠ 1 → d ≠ 0 → d ≠ 1 →
      a ≠ b → c ≠ d → ∃ p ∈ Ppair, ((p : AutPerm) : Equiv.Perm (Fin 24)) a = c ∧
        ((p : AutPerm) : Equiv.Perm (Fin 24)) b = d) ∧
    CFSG.pCore 2 Ppair = ⊥ ∧ Nat.card Ppair = 887040 := by
  refine ⟨mem_Ppair_iff, faithfulSMul_rest, isMultiplyPretransitive_rest,
    fun p hp => eq_one_of_fix_rest fun i => Subtype.ext (hp i i.2.1 i.2.2), ?_, pCore_Ppair,
    natCard_Ppair⟩
  intro a b c d ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 hab hcd
  have h2 := isMultiplyPretransitive_rest
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨g, ga, gb⟩ := h2 (a := (⟨a, ha0, ha1⟩ : Rest)) (b := ⟨b, hb0, hb1⟩) (c := ⟨c, hc0, hc1⟩)
    (d := ⟨d, hd0, hd1⟩) (fun h => hab (congrArg Subtype.val h))
    (fun h => hcd (congrArg Subtype.val h))
  exact ⟨g, g.2, congrArg Subtype.val ga, congrArg Subtype.val gb⟩

end CFSG.Monster.B.TwoA
