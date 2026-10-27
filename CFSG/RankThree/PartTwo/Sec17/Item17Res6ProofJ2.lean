module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22S

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

@[expose] def KS1717J2Inner : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ B : Subgroup X, Nat.card B = 9 → ∀ Q : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Q →
      B.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Q : Set (MulAut X)) →
        Q ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def Claim1720InnerL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P → omegaA A = {Subgroup.zpowers c} →
      (∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) →
      S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀)

theorem claim1720InnerL3_of (h : Claim1720Inner) : Claim1720InnerL3 :=
  fun G _ _ A c L Y₀ Y₁ S p P hY _ _ => h G A c L Y₀ Y₁ S p P hY

namespace Proof17Res6

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

theorem center_eq_bot_of_equiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  refine le_bot_iff.mp fun z hz => ?_
  have hez : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, hz w']
  rw [hY, Subgroup.mem_bot, map_eq_one_iff e e.injective] at hez
  exact hez

theorem actQ_le_range_of {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (haut : ∀ Q : Subgroup (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)), ¬ 3 ∣ Nat.card Q →
      (kimg Y₀ (A ⊓ L)).map (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* _) ≤
        Subgroup.normalizer (Q : Set _) →
      Q ≤ (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)).range) :
    (S.subgroupOf (Subgroup.normalizer (Y₀ : Set G))).map (actQ Y₀) ≤
      (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  refine haut _ ?_ ?_
  · intro h3
    have hd := Subgroup.card_map_dvd (S.subgroupOf M) (actQ Y₀)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv] at hd
    exact Proof171.not_three_dvd_of_isPGroup_two hS2 (h3.trans hd)
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hbAL : (b : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨s, hs, rfl⟩ := hz
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    set b' : M := ⟨b, Y₀.le_normalizer b.2⟩ with hb'
    refine ⟨b' * s * b'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hSQ.1.2.2 hbAL.1) (s : G)).mp hsS
      simpa [hb'] using this
    · rw [map_mul, map_mul, map_inv, hb', actQ_of_mem]

end Proof17Res6

end CFSG.RankThree.PartTwo.Sec17
