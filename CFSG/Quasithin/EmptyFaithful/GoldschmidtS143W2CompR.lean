module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompQ
public import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_sylow_sub {K : Subgroup Y} (hp : Group.IsPerfect K) (hn : K ≠ ⊥) :
    ∃ S : Subgroup Y, S ≤ K ∧ IsPGroup 2 S ∧ 4 ≤ Nat.card S ∧ ¬ IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hn
  obtain ⟨Sy⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨h4, hnc⟩ := sylow_perfect_facts Sy
  refine ⟨(Sy : Subgroup K).map K.subtype, Subgroup.map_subtype_le _,
    Sy.isPGroup'.map K.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]; exact h4
  · intro hcyc
    exact hnc (((Sy : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).isCyclic.mpr
      hcyc)

omit [Finite Y] in
theorem inf_eq_bot_of_commute {A B : Subgroup Y} (hA : Subgroup.center A = ⊥)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨haA, haB⟩
  have : (⟨a, haA⟩ : ↥A) ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (h g g.2 a haB)
  rw [hA, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem exists_exp_two_of_three {K₁ K₂ K₃ : Subgroup Y} (hp₁ : Group.IsPerfect K₁)
    (hp₂ : Group.IsPerfect K₂) (hp₃ : Group.IsPerfect K₃) (hn₁ : K₁ ≠ ⊥) (hn₂ : K₂ ≠ ⊥)
    (hn₃ : K₃ ≠ ⊥) (hc₁ : Subgroup.center K₁ = ⊥) (hc₃ : Subgroup.center K₃ = ⊥)
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (h13 : ∀ a ∈ K₁, ∀ b ∈ K₃, a * b = b * a) (h23 : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a)
    (hbound : ∀ B : Subgroup Y, IsPGroup 2 B → Nat.card B ≤ 64) :
    ∃ A : Subgroup Y, IsPGroup 2 A ∧ Nat.card A = 64 ∧ ∀ a ∈ A, a * a = 1 := by
  obtain ⟨S₁, hS₁K, hS₁2, hS₁4, hS₁c⟩ := exists_sylow_sub hp₁ hn₁
  obtain ⟨S₂, hS₂K, hS₂2, hS₂4, hS₂c⟩ := exists_sylow_sub hp₂ hn₂
  obtain ⟨S₃, hS₃K, hS₃2, hS₃4, hS₃c⟩ := exists_sylow_sub hp₃ hn₃
  have hcen12 : S₁ ≤ Subgroup.centralizer (S₂ : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (h12 a (hS₁K ha) b (hS₂K hb)).symm
  have hK₁₃ : K₁ ≤ Subgroup.centralizer (K₃ : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (h13 a ha b hb).symm
  have hK₂₃ : K₂ ≤ Subgroup.centralizer (K₃ : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (h23 a ha b hb).symm
  have hcen3 : S₁ ⊔ S₂ ≤ Subgroup.centralizer (S₃ : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (h13 a (hS₁K ha) b (hS₃K hb)).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (h23 a (hS₂K ha) b (hS₃K hb)).symm
  have hint12 : S₁ ⊓ S₂ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hS₁K hS₂K).trans (inf_eq_bot_of_commute hc₁ h12).le)
  have hint3 : (S₁ ⊔ S₂) ⊓ S₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haS, haS₃⟩
    have haK₃ : a ∈ K₃ := hS₃K haS₃
    have hcomm : ∀ b ∈ K₃, b * a = a * b := fun b hb => by
      have : a ∈ Subgroup.centralizer (K₃ : Set Y) :=
        (sup_le (hS₁K.trans hK₁₃) (hS₂K.trans hK₂₃)) haS
      exact Subgroup.mem_centralizer_iff.mp this b hb
    have : (⟨a, haK₃⟩ : ↥K₃) ∈ Subgroup.center K₃ := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hcomm g g.2)
    rw [hc₃, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcard12 : Nat.card ↥(S₁ ⊔ S₂) = Nat.card S₁ * Nat.card S₂ := by
    have := card_sup_mul_card_inf_of_le_centralizer hcen12
    rw [hint12, Subgroup.card_bot, mul_one] at this; exact this
  have hcard123 : Nat.card ↥(S₁ ⊔ S₂ ⊔ S₃) = Nat.card S₁ * Nat.card S₂ * Nat.card S₃ := by
    have := card_sup_mul_card_inf_of_le_centralizer hcen3
    rw [hint3, Subgroup.card_bot, mul_one, hcard12] at this; exact this
  have hA2 : IsPGroup 2 ↥(S₁ ⊔ S₂ ⊔ S₃) := by
    have h12' : IsPGroup 2 ↥(S₁ ⊔ S₂) :=
      hS₁2.to_sup_of_normal_right' hS₂2 (hcen12.trans (Subgroup.centralizer_le_normalizer _))
    exact h12'.to_sup_of_normal_right' hS₃2 (hcen3.trans (Subgroup.centralizer_le_normalizer _))
  have hle := hbound _ hA2
  rw [hcard123] at hle
  have hc1 : Nat.card S₁ = 4 := by nlinarith
  have hc2 : Nat.card S₂ = 4 := by nlinarith
  have hc3 : Nat.card S₃ = 4 := by nlinarith
  have hsq : ∀ (S : Subgroup Y), Nat.card S = 4 → ¬ IsCyclic S → ∀ s ∈ S, s * s = 1 :=
    fun S hc hnc s hs => congrArg Subtype.val (sq_eq_one_of_card_four hc hnc ⟨s, hs⟩)
  have e1 := hsq S₁ hc1 hS₁c
  have e2 := hsq S₂ hc2 hS₂c
  have e3 := hsq S₃ hc3 hS₃c
  refine ⟨S₁ ⊔ S₂ ⊔ S₃, hA2, by rw [hcard123, hc1, hc2, hc3], ?_⟩
  intro a ha
  obtain ⟨u, hu, c, hc, rfl⟩ := mem_sup_of_commute hcen3 ha
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcen12 hu
  have c12 : Commute a₁ a₂ := h12 a₁ (hS₁K ha₁) a₂ (hS₂K ha₂)
  have c13 : Commute a₁ c := h13 a₁ (hS₁K ha₁) c (hS₃K hc)
  have c23 : Commute a₂ c := h23 a₂ (hS₂K ha₂) c (hS₃K hc)
  rw [← pow_two, (c13.mul_left c23).mul_pow, c12.mul_pow, pow_two a₁, pow_two a₂, pow_two c,
    e1 a₁ ha₁, e2 a₂ ha₂, e3 c hc]
  simp

end InspW2

end S143

end CFSG.Quasithin
