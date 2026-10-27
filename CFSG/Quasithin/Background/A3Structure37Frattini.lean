
module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

namespace A37

open scoped commutatorElement

theorem frattiniQuotient_mul_comm {q : ℕ} (hq : q.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup q P) (a b : P ⧸ frattini P) : a * b = b * a := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q P) := ⟨hP⟩
  exact (CFSG.isElementaryAbelian_quotient_frattini (p := q)
    (R := P)).toIsMulCommutative.is_comm.comm a b

theorem card_frattini_quotient_of_elem {q : ℕ} (hq : q.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup q P) (h : IsElemAbelianOfRank q 2 P) :
    Nat.card (P ⧸ frattini P) = q ^ 2 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q P) := ⟨hP⟩
  obtain ⟨e⟩ := h
  have hcard : Nat.card P = q ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hel : CFSG.IsElementaryAbelian q P := by
    refine { toIsMulCommutative := ⟨⟨fun a b => e.injective ?_⟩⟩, exponent_dvd_p := ?_ }
    · simp only [map_mul]
      exact mul_comm _ _
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => e.injective ?_
      rw [map_pow, map_one]
      ext i
      simp
  have hbot : frattini P = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (p := q)
  rw [← hcard]
  exact Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).toEquiv

theorem card_frattini_quotient_of_onePlusTwo {q : ℕ} (hq : q.Prime) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup q P) (h : IsPOnePlusTwo q P) :
    Nat.card (P ⧸ frattini P) = q ^ 2 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q P) := ⟨hP⟩
  obtain ⟨hext, hcard, hexp⟩ := h
  have hZcard : Nat.card (Subgroup.center P) = q := CFSG.IsExtraspecial.center_order_p q P
  have hΦ : frattini P = _root_.commutator P := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := q)]
    have : Set.range (fun x : P => x ^ q) = {1} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl⟩
        exact hexp x
      · rintro rfl
        exact ⟨1, one_pow _⟩
    rw [this]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · exact hy
      · rw [Set.mem_singleton_iff.1 hy]
        exact (_root_.commutator P).one_mem
    · intro y hy
      exact Subgroup.subset_closure (Or.inl hy)
  have hcommle : _root_.commutator P ≤ Subgroup.center P := by
    have hel := CFSG.IsExtraspecial.quotient_elementary_abelian q P
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center P)).1
      hel.toIsMulCommutative
  have hne : _root_.commutator P ≠ ⊥ := by
    intro hbot
    have hcen : Subgroup.center P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have : ⁅y, x⁆ ∈ _root_.commutator P :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hnt := CFSG.IsExtraspecial.quotient_nontrivial q P
    have : Subsingleton (P ⧸ Subgroup.center P) := QuotientGroup.subsingleton_iff.mpr hcen
    exact (not_subsingleton _) this
  have hΦcard : Nat.card (frattini P) = q := by
    rw [hΦ]
    have h1 : Nat.card (_root_.commutator P) ∣ q := hZcard ▸ Subgroup.card_dvd_of_le hcommle
    rcases (Nat.dvd_prime hq).1 h1 with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hne
    · exact h
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini P)
  rw [hcard, hΦcard, pow_succ] at h
  have := Nat.eq_of_mul_eq_mul_right hq.pos h.symm
  rw [← this]

theorem card_frattini_quotient_two {q : ℕ} (hq : q.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup q P) (h : IsElemAbelianOfRank q 2 P ∨ IsPOnePlusTwo q P) :
    Nat.card (P ⧸ frattini P) = q ^ 2 :=
  h.elim (card_frattini_quotient_of_elem hq hP) (card_frattini_quotient_of_onePlusTwo hq hP)

theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (ι : P ≃* Q) :
    (frattini P).map ι.toMonoidHom = frattini Q := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective ι.surjective
  · intro y hy
    have h : frattini Q ≤ (frattini P).comap ι.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective ι.symm.surjective
    exact ⟨ι.symm y, h hy, by simp⟩

variable {X : Type} [Group X]

theorem frattiniIn_map_subtype (R : Subgroup X) (P : Subgroup R) :
    frattiniIn (P.map R.subtype) = (frattiniIn P).map R.subtype := by
  let e : P ≃* P.map R.subtype := P.equivMapOfInjective R.subtype R.subtype_injective
  have h1 : frattini ↥(P.map R.subtype) = (frattini ↥P).map e.toMonoidHom :=
    (map_frattini_mulEquiv e).symm
  unfold frattiniIn
  rw [h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

section Action

variable (R : Subgroup X) [R.Characteristic] (P : Subgroup R) [P.Characteristic]

@[expose] noncomputable def frattiniActionX : MulAut X →* MulAut (P ⧸ frattini P) :=
  (CFSG.SectionRank.Ccomm.frattiniAction P).comp (MulAut.characteristic R)

theorem mem_ker_frattiniActionX {α : MulAut X} :
    α ∈ (frattiniActionX R P).ker ↔
      ∀ x ∈ P, x⁻¹ * MulAut.characteristic R α x ∈ frattiniIn P := by
  rw [frattiniActionX, ← MonoidHom.comap_ker, Subgroup.mem_comap]
  exact mem_ker_frattiniAction_iff P _

theorem conj_mem_ker_frattiniActionX_iff (x : X) :
    MulAut.conj x ∈ (frattiniActionX R P).ker ↔
      ActsTriviallyOnFrattiniQuotient (P.map R.subtype) x := by
  rw [mem_ker_frattiniActionX]
  unfold ActsTriviallyOnFrattiniQuotient
  rw [frattiniIn_map_subtype]
  constructor
  · intro h d hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    refine ⟨_, h d₀ hd₀, ?_⟩
    simp
  · intro h d hd
    obtain ⟨y, hy, hyd⟩ := h (R.subtype d) ⟨d, hd, rfl⟩
    have hy' : y = d⁻¹ * MulAut.characteristic R (MulAut.conj x) d := by
      apply Subtype.ext
      have := hyd
      simpa using this
    rw [← hy']
    exact hy

end Action

end A37

end CFSG.Quasithin
