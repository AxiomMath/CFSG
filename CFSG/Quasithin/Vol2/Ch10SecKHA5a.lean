module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

structure IsSL25Group (X : Type) [Group X] : Prop where
  alt : ∃ α : X →* alternatingGroup (Fin 5), Function.Surjective α ∧ α.ker = CFSG.pCore 2 X
  comm : ∀ a ∈ CFSG.pCore 2 X, ∀ b ∈ CFSG.pCore 2 X, a * b = b * a
  sq : ∀ a ∈ CFSG.pCore 2 X, a * a = 1
  card_pCore : Nat.card (CFSG.pCore 2 X) = 32
  three : ∀ u ∈ CFSG.pCore 2 X, ∃ y : X, orderOf y = 3 ∧ y * u = u * y
  four : ∃ y : X, orderOf y = 3 ∧ ∃ a ∈ CFSG.pCore 2 X, ∃ b ∈ CFSG.pCore 2 X,
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ y * a = a * y ∧ y * b = b * y
  five : ∃ x : X, orderOf x = 5 ∧ ∃ u ∈ CFSG.pCore 2 X, x * u ≠ u * x
  perfect : commutator X = ⊤

namespace IsSL25Group

variable {X : Type} [Group X]

theorem card [Finite X] (h : IsSL25Group X) : Nat.card X = 1920 := by
  obtain ⟨α, hαs, hαk⟩ := h.alt
  have h1 := Subgroup.card_mul_index α.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hαs, Subgroup.card_top,
    A5.Delta5.a5_card, hαk, h.card_pCore] at h1
  omega

theorem isAlt_modO2 (h : IsSL25Group X) : IsAlt 5 (X ⧸ CFSG.pCore 2 X) := by
  obtain ⟨α, hαs, hαk⟩ := h.alt
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩

theorem solvableRadical_eq [Finite X] (h : IsSL25Group X) :
    CFSG.solvableRadical X = CFSG.pCore 2 X := by
  obtain ⟨α, hαs, hαk⟩ := h.alt
  let e : (X ⧸ CFSG.pCore 2 X) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := e.isSimpleGroup
  have hna : ∃ a b : X ⧸ CFSG.pCore 2 X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply A5.G3.not_solvable_alt5
    apply Group.isSolvable_of_comm
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hcon _ _
  exact A314.solvableRadical_eq_of_simple A5.G3.IsDelta5Group.solvable_pCore hs hna

theorem isAlt_modRadical [Finite X] (h : IsSL25Group X) :
    IsAlt 5 (X ⧸ CFSG.solvableRadical X) := by
  obtain ⟨e⟩ := h.isAlt_modO2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h.solvableRadical_eq).trans e⟩

theorem isElemAbelian_pCore (h : IsSL25Group X) : IsElemAbelian 2 (CFSG.pCore 2 X) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (h.comm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact h.sq x hx

theorem exists_three_comm [Finite X] (h : IsSL25Group X) :
    ∃ y u : X, orderOf y = 3 ∧ u ∈ CFSG.pCore 2 X ∧ u ≠ 1 ∧ y * u = u * y := by
  obtain ⟨y, hy3, a, ha, b, -, ha1, -, -, hya, -⟩ := h.four
  exact ⟨y, a, hy3, ha, ha1, hya⟩

theorem of_equiv {Y : Type} [Group Y] (e : X ≃* Y) (h : IsSL25Group X) : IsSL25Group Y := by
  have hP : (CFSG.pCore 2 X).map e.toMonoidHom = CFSG.pCore 2 Y := CFSG.pCore_map_iso 2 e
  have hmem : ∀ y : Y, y ∈ CFSG.pCore 2 Y ↔ e.symm y ∈ CFSG.pCore 2 X := by
    intro y
    rw [← hP]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
  obtain ⟨α, hαs, hαk⟩ := h.alt
  refine ⟨⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk, hmem]
    rfl
  · intro a ha b hb
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.comm _ ((hmem a).1 ha) _ ((hmem b).1 hb)
  · intro a ha
    apply e.symm.injective
    rw [map_mul, map_one]
    exact h.sq _ ((hmem a).1 ha)
  · rw [← hP, Subgroup.card_map_of_injective e.injective, h.card_pCore]
  · intro u hu
    obtain ⟨y, hy3, hyu⟩ := h.three _ ((hmem u).1 hu)
    refine ⟨e y, by rw [MulEquiv.orderOf_eq, hy3], ?_⟩
    apply e.symm.injective
    simpa using hyu
  · obtain ⟨y, hy3, a, ha, b, hb, ha1, hb1, hab, hya, hyb⟩ := h.four
    refine ⟨e y, by rw [MulEquiv.orderOf_eq, hy3], e a, (hmem _).2 (by simpa using ha), e b,
      (hmem _).2 (by simpa using hb), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h1 => ha1 (e.injective (h1.trans (map_one e).symm))
    · exact fun h1 => hb1 (e.injective (h1.trans (map_one e).symm))
    · exact fun h1 => hab (e.injective h1)
    · rw [← map_mul, ← map_mul, hya]
    · rw [← map_mul, ← map_mul, hyb]
  · obtain ⟨x, hx5, u, hu, hxu⟩ := h.five
    refine ⟨e x, by rw [MulEquiv.orderOf_eq, hx5], e u, (hmem _).2 (by simpa using hu), ?_⟩
    intro h1
    apply hxu
    apply e.injective
    rw [map_mul, map_mul]
    exact h1
  · have h1 := h.perfect
    have h2 : (commutator X).map e.toMonoidHom = commutator Y := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h2, h1, Subgroup.map_top_of_surjective _ e.surjective]

end IsSL25Group

theorem not_isSL25_bot {G : Type} [Group G] [Finite G] :
    ¬ IsSL25Group ↥(⊥ : Subgroup G) := by
  intro h
  have := h.card
  rw [Subgroup.card_bot] at this
  omega

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
