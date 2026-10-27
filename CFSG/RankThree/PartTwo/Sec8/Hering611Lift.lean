module

public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def actHom (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (thetaQuotMulAut L).comp (compAction L)

noncomputable abbrev qL (L : Subgroup G) : L →* L ⧸ aschbacherSolvableCore 3 L :=
  QuotientGroup.mk' (aschbacherSolvableCore 3 L)

theorem actHom_qL (L : Subgroup G) (g : Subgroup.normalizer (L : Set G)) (l : L) :
    actHom L g (qL L l) = qL L (compAction L g l) := rfl

theorem coe_compAction (L : Subgroup G) (g : Subgroup.normalizer (L : Set G)) (l : L) :
    ((compAction L g l : L) : G) = (g : G) * l * (g : G)⁻¹ := rfl

theorem exists_invariant_lift {L E : Subgroup G}
    (hodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    (hE3 : IsPGroup 3 E) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hV4 : Nat.card V = 4)
    (hinv : ∀ (g : G) (hg : g ∈ E), ∀ v ∈ V, actHom L ⟨g, hEN hg⟩ v ∈ V) :
    ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ Nat.card T = 4 ∧
      E ≤ Subgroup.normalizer (T : Set G) ∧
      T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ ∧
      (∀ t : L, (t : G) ∈ T → qL L t ∈ V) ∧ (∀ v ∈ V, ∃ t : L, (t : G) ∈ T ∧ qL L t = v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  set θ' := inSubgroup (aschbacherSolvableCore 3) L with hθ'
  set q := qL L with hq
  set P : Subgroup L := V.comap q with hP
  set W : Subgroup G := P.map L.subtype with hW
  have hWL : W ≤ L := Subgroup.map_subtype_le _
  have hmemW : ∀ y : L, (y : G) ∈ W ↔ q y ∈ V := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hθP : θL ≤ P := by
    intro x hx
    change q x ∈ V
    rw [hq, qL, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact V.one_mem
  have hcardP : Nat.card P = Nat.card θL * Nat.card V := by
    have h1 := Subgroup.card_ker_mul_card_range (q.comp P.subtype)
    have hker : (q.comp P.subtype).ker = θL.subgroupOf P := by
      rw [← MonoidHom.comap_ker, hq, qL, QuotientGroup.ker_mk']
      rfl
    have hrange : (q.comp P.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θL) V
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθP).toEquiv] at h1
    exact h1.symm
  have hθcard : Nat.card θ' = Nat.card θL := by
    rw [hθ', inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  have hWcard : Nat.card W = Nat.card θ' * 4 := by
    rw [hW, Subgroup.card_map_of_injective L.subtype_injective, hcardP, hθcard, hV4]
  have hθ3 : ¬ 3 ∣ Nat.card θ' := (Sec6.theta_solvable_and_not_dvd L).2
  have hW3 : ¬ 3 ∣ Nat.card W := by
    rw [hWcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hθ3 h
    · omega
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ E, ∀ y : G, y ∈ W → g * y * g⁻¹ ∈ W := by
      intro g hg
      rintro _ ⟨y, hy, rfl⟩
      have hyV : q y ∈ V := hy
      have h1 := hinv g hg (q y) hyV
      change g * (y : G) * g⁻¹ ∈ W
      have h2 : g * (y : G) * g⁻¹ = ((compAction L ⟨g, hEN hg⟩ y : L) : G) := rfl
      rw [h2, hmemW]
      exact h1
    intro y
    constructor
    · exact key g hg y
    · intro hy
      have := key g⁻¹ (E.inv_mem hg) _ hy
      simpa [mul_assoc] using this
  obtain ⟨Q, hEQ⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three E W hE3 hW3 hEW 2 Nat.prime_two
  set T : Subgroup G := (Q : Subgroup W).map W.subtype with hT
  have hTW : T ≤ W := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := Q.isPGroup'.map W.subtype
  have hTcard : Nat.card T = 4 := by
    rw [hT, Subgroup.card_map_of_injective W.subtype_injective, Sylow.card_eq_multiplicity,
      hWcard]
    have hodd' : Odd (Nat.card θ') := hodd
    have h0 : Nat.card θ' ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul h0 (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd'),
      zero_add, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have hTθ : T ⊓ θ' = ⊥ := by
    have h1 : Nat.card (T ⊓ θ' : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (T ⊓ θ' : Subgroup G) ∣ Nat.card θ' := Subgroup.card_dvd_of_le inf_le_right
    rw [hTcard] at h1
    have hodd' : Odd (Nat.card θ') := hodd
    have hcop : Nat.Coprime 4 (Nat.card θ') := by
      have : Nat.Coprime 2 (Nat.card θ') := (Nat.coprime_two_left).mpr hodd'
      simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using this.pow_left 2
    have h3 : Nat.card (T ⊓ θ' : Subgroup G) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (Subgroup.card_eq_one).mp h3
  have hTV : ∀ t : L, (t : G) ∈ T → q t ∈ V := fun t ht => (hmemW t).mp (hTW ht)
  have hTL : T ≤ L := hTW.trans hWL
  set f : T →* L ⧸ aschbacherSolvableCore 3 L :=
    q.comp (Subgroup.inclusion hTL : T →* L) with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : (Subgroup.inclusion hTL t : L) ∈ θL := (QuotientGroup.eq_one_iff _).mp ht
    have h2 : (t : G) ∈ T ⊓ θ' := ⟨t.2, ⟨_, h1, rfl⟩⟩
    rw [hTθ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hfcard : Nat.card f.range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hTcard]
  have hrangeV : f.range ≤ V := by
    rintro _ ⟨t, rfl⟩
    exact hTV (Subgroup.inclusion hTL t) t.2
  have hrange_eq : f.range = V := Subgroup.eq_of_le_of_card_ge hrangeV (by rw [hfcard, hV4])
  refine ⟨T, hTL, hT2, hTcard, hEQ, hTθ, hTV, fun v hv => ?_⟩
  obtain ⟨t, ht⟩ := (hrange_eq ▸ hv : v ∈ f.range)
  exact ⟨Subgroup.inclusion hTL t, t.2, ht⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
