module

public import CFSG.Timmesfeld.ARS.BasicRankOne

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section Commuting

variable {A B C : Subgroup G}

theorem commuting_iff_le_centralizer : Commuting A B ↔ B ≤ Subgroup.centralizer (A : Set G) :=
  ⟨fun h b hb => Subgroup.mem_centralizer_iff.2 fun a ha => (h a ha b hb).eq,
    fun h a ha _ hb => (Subgroup.mem_centralizer_iff.1 (h hb) a ha)⟩

theorem Commuting.symm (h : Commuting A B) : Commuting B A :=
  fun b hb a ha => (h a ha b hb).symm

theorem commuting_iff_commutator_eq_bot : Commuting A B ↔ ⁅A, B⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← commuting_iff_le_centralizer]
  exact ⟨Commuting.symm, Commuting.symm⟩

theorem Commuting.sup_right (hB : Commuting A B) (hC : Commuting A C) : Commuting A (B ⊔ C) :=
  commuting_iff_le_centralizer.2
    (sup_le (commuting_iff_le_centralizer.1 hB) (commuting_iff_le_centralizer.1 hC))

theorem Commuting.sup_left (hA : Commuting A C) (hB : Commuting B C) : Commuting (A ⊔ B) C :=
  (hA.symm.sup_right hB.symm).symm

theorem Commuting.mono {A' B' : Subgroup G} (h : Commuting A B) (hA : A' ≤ A) (hB : B' ≤ B) :
    Commuting A' B' :=
  fun a ha b hb => h a (hA ha) b (hB hb)

theorem Commuting.conjSub (h : Commuting A B) (g : G) : Commuting (conjSub A g) (conjSub B g) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact (h a ha b hb).map (MulAut.conj g).toMonoidHom

end Commuting

namespace IsRootClass

variable (hR : IsRootClass R)
include hR

theorem conjSub_mem {A : Subgroup G} (hA : A ∈ R) (g : G) : conjSub A g ∈ R := by
  obtain ⟨A₀, rfl⟩ := hR.conj_class
  obtain ⟨x, rfl⟩ := hA
  exact ⟨g * x, conjSub_mul A₀ g x⟩

theorem exists_conjSub_eq {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) :
    ∃ g : G, conjSub A g = B := by
  obtain ⟨A₀, rfl⟩ := hR.conj_class
  obtain ⟨x, rfl⟩ := hA
  obtain ⟨y, rfl⟩ := hB
  exact ⟨y * x⁻¹, by rw [← conjSub_mul, inv_mul_cancel_right]⟩

theorem card_eq {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) : Nat.card A = Nat.card B := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hB
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

theorem commute {A : Subgroup G} (hA : A ∈ R) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    Commute a b :=
  commute_of_mul_self (hR.mul_self A hA) ha hb

theorem commuting_self {A : Subgroup G} (hA : A ∈ R) : Commuting A A :=
  fun _ ha _ hb => hR.commute hA ha hb

theorem inv_eq {A : Subgroup G} (hA : A ∈ R) {a : G} (ha : a ∈ A) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (hR.mul_self A hA a ha)

theorem isPGroup {A : Subgroup G} (hA : A ∈ R) : IsPGroup 2 A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
  exact hR.mul_self A hA _ a.2

theorem exists_ne_one {A : Subgroup G} (hA : A ∈ R) : ∃ a ∈ A, a ≠ 1 := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hR.ne_bot A hA)
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem commutator_self_eq_bot {A : Subgroup G} (hA : A ∈ R) : ⁅A, A⁆ = ⊥ :=
  commuting_iff_commutator_eq_bot.1 (hR.commuting_self hA)

end IsRootClass

namespace Special

variable {A B : Subgroup G}

theorem symm (h : Special R A B) : Special R B A := by
  unfold Special at *
  rw [Subgroup.commutator_comm]
  exact ⟨h.1, h.2.2, h.2.1⟩

theorem commutator_ne_bot (hR : IsRootClass R) (h : Special R A B) : ⁅A, B⁆ ≠ ⊥ :=
  hR.ne_bot _ h.1

theorem not_commuting (hR : IsRootClass R) (h : Special R A B) : ¬ Commuting A B :=
  fun hc => h.commutator_ne_bot hR (commuting_iff_commutator_eq_bot.1 hc)

theorem ne (hR : IsRootClass R) (hA : A ∈ R) (h : Special R A B) : A ≠ B := by
  rintro rfl
  exact h.not_commuting hR (hR.commuting_self hA)

theorem ne_commutator (hR : IsRootClass R) (h : Special R A B) : A ≠ ⁅A, B⁆ := by
  intro heq
  apply h.not_commuting hR
  have := h.2.2
  rwa [← heq] at this

theorem _root_.CFSG.Timmesfeld.ARS.conj_eq_commutator_mul (g a : G) :
    g * a * g⁻¹ = ⁅g, a⁆ * a := by
  rw [commutatorElement_def]
  group

theorem _root_.CFSG.Timmesfeld.ARS.conjSub_le_commutator_sup {b : G} (hb : b ∈ B) :
    conjSub A b ≤ ⁅A, B⁆ ⊔ A := by
  rintro _ ⟨a, ha, rfl⟩
  change b * a * b⁻¹ ∈ _
  rw [conj_eq_commutator_mul]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ha)
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hb ha

theorem not_opposite (hR : IsRootClass R) (hA : A ∈ R) (h : Special R A B) :
    ¬ Opposite A B := by
  intro hop
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  obtain ⟨b, hb, hb1, -⟩ := hop.2.1 a ha ha1
  have hne : conjSub A 1 ≠ conjSub A b := by
    rw [conjSub_one]
    intro heq
    exact hb1 (hop.symm.eq_one_of_conjSub_eq hb heq.symm)
  have hsup := hop.sup_conjSub_eq (hR.mul_self A hA) (one_mem _) (Subgroup.mem_sup_right hb) hne
  rw [conjSub_one] at hsup
  have hle : A ⊔ B ≤ ⁅A, B⁆ ⊔ A := hsup ▸ sup_le le_sup_right (conjSub_le_commutator_sup hb)
  have hcomm : Commuting (⁅A, B⁆ ⊔ A) A := Commuting.sup_left h.2.1 (hR.commuting_self hA)
  exact hop.not_commuting (hR.ne_bot A hA) (hcomm.mono (le_sup_right.trans hle) le_rfl).symm

end Special

namespace Opposite

variable {A B : Subgroup G}

theorem isElemAbRankOne (hR : IsRootClass R) (hA : A ∈ R) (h : Opposite A B) :
    IsElemAbRankOne (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) :=
  h.isElemAbRankOne_of_mul_self (hR.mul_self A hA)

theorem exists_mulEquiv_SL2 [Finite G] (hR : IsRootClass R) (hA : A ∈ R) (h : Opposite A B)
    (hq : 4 ≤ Nat.card A) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : ↥(A ⊔ B) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  have hcard := card_subgroupOf_of_le (le_sup_left : A ≤ A ⊔ B)
  rw [← hcard] at hq ⊢
  exact ElemAbRankOne.exists_mulEquiv_SL2 (h.isElemAbRankOne hR hA) hq

theorem exists_mulEquiv_SL2_two [Finite G] (hR : IsRootClass R) (hA : A ∈ R) (h : Opposite A B)
    (hq : Nat.card A = 2) :
    ∃ φ : ↥(A ⊔ B) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
      (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 1) ∧
      (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 1) :=
  ElemAbRankOne.exists_mulEquiv_SL2_two (h.isElemAbRankOne hR hA)
    ((card_subgroupOf_of_le le_sup_left).trans hq)

theorem exists_mulEquiv_SL2' [Finite G] (hR : IsRootClass R) (hA : A ∈ R) (h : Opposite A B) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : ↥(A ⊔ B) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  have hcard := card_subgroupOf_of_le (le_sup_left : A ≤ A ⊔ B)
  rw [← hcard]
  exact ElemAbRankOne.exists_mulEquiv_SL2' (h.isElemAbRankOne hR hA)

theorem card_sup_eq_six [Finite G] (hR : IsRootClass R) (hA : A ∈ R) (h : Opposite A B)
    (hq : Nat.card A = 2) : Nat.card ↥(A ⊔ B) = 6 :=
  (h.isElemAbRankOne hR hA).card_eq_six ((card_subgroupOf_of_le le_sup_left).trans hq)

end Opposite

theorem inf_eq_bot_of_opposite (hR : IsRootClass R) {A B C : Subgroup G} (hB : B ∈ R)
    (hC : C ∈ R) (hAC : Opposite A C) (hAB : A ≠ B) : A ⊓ B = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  by_contra ha1
  obtain ⟨haA, haB⟩ := ha
  have hnorm : conjSub C a ≠ C := fun h => ha1 (hAC.eq_one_of_conjSub_eq haA h)
  by_cases hBC : B = C
  · subst hBC
    have : a ∈ A ⊓ B := ⟨haA, haB⟩
    rw [hAC.inf_eq_bot, Subgroup.mem_bot] at this
    exact ha1 this
  rcases hR.rel B hB C hC hBC with hcomm | hopp | hspec
  · exact hnorm (conjSub_of_forall_commute fun c hc => hcomm a haB c hc)
  · obtain ⟨c, hc, -, hc'⟩ := hAC.2.1 a haA ha1
    obtain ⟨c', hc'', -, hc'''⟩ := hopp.2.1 a haB ha1
    have e : A = conjSub B (c⁻¹ * c') := by
      rw [conjSub_mul, hc''', ← hc', ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hy : c⁻¹ * c' ∈ B ⊔ C := Subgroup.mem_sup_right (C.mul_mem (C.inv_mem hc) hc'')
    have hne : conjSub B 1 ≠ conjSub B (c⁻¹ * c') := by
      rw [conjSub_one, ← e]
      exact hAB.symm
    have hbot := hopp.inf_conjSub_eq_bot (hR.mul_self B hB) (one_mem _) hy hne
    rw [conjSub_one, ← e] at hbot
    have : a ∈ B ⊓ A := ⟨haB, haA⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  · obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hC
    have hw : a * c * a⁻¹ ∈ conjSub C a := conj_mem_conjSub a hc
    have hw1 : a * c * a⁻¹ ≠ 1 := fun h1 => hc1 (conj_eq_one_iff.1 h1)
    have hcomm : Commute c (a * c * a⁻¹) := by
      rw [conj_eq_commutator_mul]
      have hd : Commute ⁅a, c⁆ c :=
        hspec.2.2 _ (Subgroup.commutator_mem_commutator haB hc) c hc
      exact hd.symm.mul_right (Commute.refl c)
    have := hAC.symm.conjSub_eq_of_commute (hR.mul_self C hC) (x := 1) (y := a) (one_mem _)
      (Subgroup.mem_sup_right haA) (by rwa [conjSub_one]) hc1 hw hw1 hcomm
    exact hnorm (this.trans (conjSub_one C))

theorem inf_eq_bot (hR : IsRootClass R) (hiso : NoIsolated R) {A B : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ R) (hAB : A ≠ B) : A ⊓ B = ⊥ := by
  obtain ⟨C, hC, hAC⟩ := hiso A hA
  exact inf_eq_bot_of_opposite hR hB hC hAC hAB

end CFSG.Timmesfeld.ARS
