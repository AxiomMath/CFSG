module

public import CFSG.Quasithin.H13.A6Statements
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

structure IsDSystemIn (D : DType) (Es : Fin 3 → Subgroup G) : Prop where
  d1A3 : D = .A3 → quasithinO2QuotientIso (Es 0) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  d1C3 : D = .C3 → quasithinO2QuotientIso (Es 0) ↥(alternatingGroup (Fin 6)) ∨
    quasithinO2QuotientIso (Es 0) (Equiv.Perm (Fin 6))
  d2one : quasithinO2QuotientIso (Es 1)
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
  d2two : quasithinO2QuotientIso (Es 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  d3sylow : ∀ i : Fin 3, QuasithinUnique.IsSylowTwoOf (Es 0 ⊓ Es 1 ⊓ Es 2) (Es i)
  d3max : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    Es i ⊓ Es j ≠ Es i ⊓ Es k ∧
      ∀ X : Subgroup G, (Es 0 ⊓ Es 1 ⊓ Es 2 ≤ X ∧ IsMaxSubgroupIn X (Es i)) ↔
        (X = Es i ⊓ Es j ∨ X = Es i ⊓ Es k)
  d4core : ∀ N : Subgroup G, N ≤ Es 0 ⊓ Es 1 ⊓ Es 2 →
    Es 0 ⊔ Es 1 ⊔ Es 2 ≤ Subgroup.normalizer (N : Set G) → N = ⊥
  d5 : D = .C3 → Subgroup.center ↥(Es 0) ≠ ⊥ ∨ 2 ^ 5 < Nat.card ↥(pCoreOf 2 (Es 0))

section Transport

variable {E : Subgroup G}

theorem quasithinO2QuotientIso_subgroupOf {L : Subgroup G} (hLE : L ≤ E) (Q : Type*) [Group Q] :
    quasithinO2QuotientIso (L.subgroupOf E) Q ↔ quasithinO2QuotientIso L Q := by
  rw [H13.quasithinO2QuotientIso_iff, H13.quasithinO2QuotientIso_iff]
  have he := CFSG.LieType.SteinbergBR.pCore_map_equiv 2 (Subgroup.subgroupOfEquivOfLe hLE)
  let f : (↥(L.subgroupOf E) ⧸ CFSG.pCore 2 ↥(L.subgroupOf E)) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLE) he
  exact ⟨fun ⟨φ⟩ => ⟨f.symm.trans φ⟩, fun ⟨φ⟩ => ⟨f.trans φ⟩⟩

theorem map_subtype_subgroupOf {A : Subgroup G} (hA : A ≤ E) :
    (A.subgroupOf E).map E.subtype = A := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA]

theorem inf_subgroupOf' (A B : Subgroup G) :
    (A ⊓ B).subgroupOf E = A.subgroupOf E ⊓ B.subgroupOf E := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem isMaxSubgroupIn_map_iff (X Y : Subgroup ↥E) :
    IsMaxSubgroupIn X Y ↔ IsMaxSubgroupIn (X.map E.subtype) (Y.map E.subtype) := by
  have hinj := E.subtype_injective
  constructor
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).2 hlt, fun W hXW hWY => ?_⟩
    have hWE : W ≤ E := hWY.trans (Subgroup.map_subtype_le _)
    have h1 : X ≤ W.subgroupOf E := by
      rw [← Subgroup.map_subtype_le_map_subtype, map_subtype_subgroupOf hWE]
      exact hXW
    have h2 : W.subgroupOf E ≤ Y := by
      rw [← Subgroup.map_subtype_le_map_subtype, map_subtype_subgroupOf hWE]
      exact hWY
    rcases hmax _ h1 h2 with h | h
    · left
      rw [← h, map_subtype_subgroupOf hWE]
    · right
      rw [← h, map_subtype_subgroupOf hWE]
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).1 hlt, fun W hXW hWY => ?_⟩
    rcases hmax _ ((Subgroup.map_subtype_le_map_subtype).2 hXW)
      ((Subgroup.map_subtype_le_map_subtype).2 hWY) with h | h
    · exact Or.inl (Subgroup.map_injective hinj h)
    · exact Or.inr (Subgroup.map_injective hinj h)

end Transport

theorem IsDSystemIn.isDSystem {D : DType} {Es : Fin 3 → Subgroup G} (h : IsDSystemIn D Es) :
    IsDSystem D fun i => (Es i).subgroupOf (Es 0 ⊔ Es 1 ⊔ Es 2) := by
  set E := Es 0 ⊔ Es 1 ⊔ Es 2 with hE
  have hle : ∀ i : Fin 3, Es i ≤ E := fun i => by
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hinj := E.subtype_injective
  have hT : Es 0 ⊓ Es 1 ⊓ Es 2 ≤ E := inf_le_left.trans (inf_le_left.trans (hle 0))
  have hTsub : (Es 0).subgroupOf E ⊓ (Es 1).subgroupOf E ⊓ (Es 2).subgroupOf E =
      (Es 0 ⊓ Es 1 ⊓ Es 2).subgroupOf E := by
    rw [inf_subgroupOf', inf_subgroupOf']
  have hmapT : ((Es 0).subgroupOf E ⊓ (Es 1).subgroupOf E ⊓ (Es 2).subgroupOf E).map E.subtype =
      Es 0 ⊓ Es 1 ⊓ Es 2 := by
    rw [hTsub, map_subtype_subgroupOf hT]
  refine ⟨fun hD => (quasithinO2QuotientIso_subgroupOf (hle 0) _).2 (h.d1A3 hD),
    fun hD => ?_, (quasithinO2QuotientIso_subgroupOf (hle 1) _).2 h.d2one,
    (quasithinO2QuotientIso_subgroupOf (hle 2) _).2 h.d2two, fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rcases h.d1C3 hD with h1 | h1
    · exact Or.inl ((quasithinO2QuotientIso_subgroupOf (hle 0) _).2 h1)
    · exact Or.inr ((quasithinO2QuotientIso_subgroupOf (hle 0) _).2 h1)
  ·
    obtain ⟨h1, h2, h3⟩ := h.d3sylow i
    refine ⟨?_, ?_, ?_⟩
    · rw [← Subgroup.map_subtype_le_map_subtype, hmapT, map_subtype_subgroupOf (hle i)]
      exact h1
    · have e := (Subgroup.equivMapOfInjective
        ((Es 0).subgroupOf E ⊓ (Es 1).subgroupOf E ⊓ (Es 2).subgroupOf E) E.subtype hinj)
      rw [hmapT] at e
      exact h2.of_equiv e.symm
    · have := Subgroup.relIndex_map_map_of_injective
        ((Es 0).subgroupOf E ⊓ (Es 1).subgroupOf E ⊓ (Es 2).subgroupOf E)
        ((Es i).subgroupOf E) hinj
      rw [hmapT, map_subtype_subgroupOf (hle i)] at this
      rw [← Subgroup.relIndex, ← this]
      exact h3
  ·
    intro i j k hij hik hjk
    obtain ⟨hne, hiff⟩ := h.d3max i j k hij hik hjk
    have hij' : (Es i).subgroupOf E ⊓ (Es j).subgroupOf E = (Es i ⊓ Es j).subgroupOf E :=
      (inf_subgroupOf' _ _).symm
    have hik' : (Es i).subgroupOf E ⊓ (Es k).subgroupOf E = (Es i ⊓ Es k).subgroupOf E :=
      (inf_subgroupOf' _ _).symm
    have hmij : ((Es i).subgroupOf E ⊓ (Es j).subgroupOf E).map E.subtype = Es i ⊓ Es j := by
      rw [hij', map_subtype_subgroupOf (inf_le_left.trans (hle i))]
    have hmik : ((Es i).subgroupOf E ⊓ (Es k).subgroupOf E).map E.subtype = Es i ⊓ Es k := by
      rw [hik', map_subtype_subgroupOf (inf_le_left.trans (hle i))]
    refine ⟨fun heq => hne (by rw [← hmij, ← hmik, heq]), fun X => ?_⟩
    have key := hiff (X.map E.subtype)
    rw [isMaxSubgroupIn_map_iff, map_subtype_subgroupOf (hle i)]
    constructor
    · rintro ⟨hTX, hmax⟩
      have hTX' : Es 0 ⊓ Es 1 ⊓ Es 2 ≤ X.map E.subtype := by
        rw [← hmapT]
        exact (Subgroup.map_subtype_le_map_subtype).2 hTX
      rcases key.1 ⟨hTX', hmax⟩ with h' | h'
      · left
        apply Subgroup.map_injective hinj
        rw [h', hmij]
      · right
        apply Subgroup.map_injective hinj
        rw [h', hmik]
    · intro hX
      have hX' : X.map E.subtype = Es i ⊓ Es j ∨ X.map E.subtype = Es i ⊓ Es k := by
        rcases hX with rfl | rfl
        · exact Or.inl hmij
        · exact Or.inr hmik
      obtain ⟨hTX, hmax⟩ := key.2 hX'
      refine ⟨?_, hmax⟩
      rw [← Subgroup.map_subtype_le_map_subtype, hmapT]
      exact hTX
  ·
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subtype_subgroupOf (hle 0),
      map_subtype_subgroupOf (hle 1), map_subtype_subgroupOf (hle 2), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  ·
    intro N hN hNT
    have hNE : N.map E.subtype ≤ Es 0 ⊓ Es 1 ⊓ Es 2 := by
      rw [← hmapT]
      exact (Subgroup.map_subtype_le_map_subtype).2 hNT
    have hnorm : E ≤ Subgroup.normalizer ((N.map E.subtype : Subgroup G) : Set G) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨e, he⟩ * n * ⟨e, he⟩⁻¹, hN.conj_mem n hn _, rfl⟩
      · rintro ⟨n, hn, hn'⟩
        refine ⟨⟨e, he⟩⁻¹ * n * ⟨e, he⟩, ?_, ?_⟩
        · have := hN.conj_mem n hn ⟨e, he⟩⁻¹
          simpa using this
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hn' ⊢
          rw [hn']
          group
    have h0 := h.d4core _ hNE hnorm
    apply Subgroup.map_injective hinj
    rw [h0, Subgroup.map_bot]
  ·
    intro hD
    let e0 := Subgroup.subgroupOfEquivOfLe (hle 0)
    rcases h.d5 hD with h1 | h1
    · left
      obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h1
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨e0.symm (x : ↥(Es 0)), Subgroup.mem_center_iff.2 fun g => ?_⟩, ?_⟩
      · apply e0.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_center_iff.1 x.2 (e0 g)
      · intro h0
        apply hx1
        have := congrArg (fun y : ↥(Subgroup.center ↥((Es 0).subgroupOf E)) => e0 (y : _)) h0
        simp only [MulEquiv.apply_symm_apply, OneMemClass.coe_one, map_one] at this
        exact Subtype.ext this
    · right
      have hc : Nat.card ↥(pCoreOf 2 ((Es 0).subgroupOf E)) = Nat.card ↥(pCoreOf 2 (Es 0)) := by
        rw [pCoreOf, pCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
          Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
        have he := CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e0
        rw [← he, Subgroup.card_map_of_injective e0.injective]
      rw [hc]
      exact h1

end CFSG.Quasithin.H13.A6
