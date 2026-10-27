module

public import CFSG.Quasithin.Vol2.Ch4Sec2NoSum2

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Setting28 (T M L Mm I H K : Subgroup G) (n : ℕ) : Prop where
  hy : Hyp4_2_3 G T M L Mm I
  hIH : InM I H
  c : Conf4212 G T M L I H K
  hn : IsPSL 2 2 n (ModO2 (perfectCore (L ⊓ H)))
  hn1 : 1 < n
  h2 : IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K
  hKH : H ≤ Subgroup.normalizer (K : Set G)
  hVL : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥
  hVcard : Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = 2 ^ (4 * n)

variable {T M L Mm I H K : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem mem_sup_of_le_normalizer_centKU1 {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, (a₂⁻¹ * b₁ * a₂) * b₂, B.mul_mem ?_ hb₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha₂)) b₁).1 hb₁
        simpa using this
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA ha) b⁻¹).1 (B.inv_mem hb)
        exact this }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact (_root_.sup_le hAS hBS) hx

theorem LH_inf_eq (s : Setting28 T M L Mm I H K n) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {H₁ K₁ : Subgroup G} (hIH₁ : I ≤ H₁) (hKH₁ : K ≤ H₁)
    (c₁ : Conf4212 G T M L I H₁ K₁) : L ⊓ H₁ = L ⊓ H := by
  have hLHL : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
  have hLHH : perfectCore (L ⊓ H) ≤ H := (perfectCore_le _).trans inf_le_right
  have hLHH₁ : perfectCore (L ⊓ H) ≤ H₁ := s.c.LH_le.trans hKH₁
  have hN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    s.c.hyp421.sup_le.trans (s.c.normal.trans (normalizer_le_normalizer_pCoreOf 2 L))
  have hL2 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hN
      (pCoreOf_isPGroup 2 L)
  have hdec : ∀ x ∈ L, ∃ a ∈ perfectCore (L ⊓ H), ∃ o ∈ pCoreOf 2 L, x = a * o := by
    intro x hx
    exact mem_sup_of_le_normalizer_centKU1 (hLHL.trans (le_normalizer_pCoreOf 2 L))
      (s.c.L_le hx)
  apply le_antisymm
  ·
    rintro x ⟨hxL, hxH₁⟩
    obtain ⟨a, ha, o, ho, rfl⟩ := hdec x hxL
    have hoH₁ : o ∈ H₁ := by
      have h1 := H₁.mul_mem (H₁.inv_mem (hLHH₁ ha)) hxH₁
      rwa [inv_mul_cancel_left] at h1
    have hoRH₁ : o ∈ pCoreOf 2 (L ⊔ T) ⊓ H₁ := ⟨hL2 ho, hoH₁⟩
    have hoR : o ∈ pCoreOf 2 I := c₁.inf_le_pCoreOf_I s.hy h37 h38 h39 hoRH₁
    have hoH : o ∈ H := (pCoreOf_le 2 I).trans s.c.inH.1 hoR
    exact ⟨hxL, H.mul_mem (hLHH ha) hoH⟩
  ·
    rintro x ⟨hxL, hxH⟩
    obtain ⟨a, ha, o, ho, rfl⟩ := hdec x hxL
    have hoH : o ∈ H := by
      have h1 := H.mul_mem (H.inv_mem (hLHH ha)) hxH
      rwa [inv_mul_cancel_left] at h1
    have hoRH : o ∈ pCoreOf 2 (L ⊔ T) ⊓ H := ⟨hL2 ho, hoH⟩
    have hoR : o ∈ pCoreOf 2 I := s.c.inf_le_pCoreOf_I s.hy h37 h38 h39 hoRH
    have hoH₁ : o ∈ H₁ := (pCoreOf_le 2 I).trans hIH₁ hoR
    exact ⟨hxL, H₁.mul_mem (hLHH₁ ha) hoH₁⟩

end CFSG.Quasithin.H13.Ch4.CentK
