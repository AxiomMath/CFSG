module

public import CFSG.LocalAnalysis.QuasithinUnique.AGFusion

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique

section Fixed

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_of_unique_fixed {X Y P : Subgroup G} {z : G} (hXY : X ≤ Y)
    (hP : IsSylowTwoOf P X) (hzP : z ∈ P) (H1 : ∀ g ∈ Y, g⁻¹ * z * g ∈ X → g ∈ X) :
    IsSylowTwoOf P Y := by
  have hPX : P ≤ X := hP.1
  have hPY : P ≤ Y := hPX.trans hXY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X' : Subgroup ↥Y := X.subgroupOf Y with hX'
  set P' : Subgroup ↥Y := P.subgroupOf Y with hP'
  have hP2 : IsPGroup 2 ↥P' := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
  have hmod := hP2.card_modEq_card_fixedPoints (↥Y ⧸ X')
  have hfix : MulAction.fixedPoints ↥P' (↥Y ⧸ X') = {((1 : ↥Y) : ↥Y ⧸ X')} := by
    ext c
    induction c using QuotientGroup.induction_on with
    | H g =>
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro h
        have hz : (⟨z, hPY hzP⟩ : ↥Y) ∈ P' := hzP
        have h1 := h ⟨⟨z, hPY hzP⟩, hz⟩
        have h2 : ((⟨z, hPY hzP⟩ * g : ↥Y) : ↥Y ⧸ X') = (g : ↥Y ⧸ X') := h1
        rw [QuotientGroup.eq] at h2
        have hg : (g : G)⁻¹ * z * (g : G) ∈ X := by
          have := X.inv_mem (Subgroup.mem_subgroupOf.1 h2)
          simpa [mul_assoc] using this
        have hgX : (g : G) ∈ X := H1 g g.2 hg
        rw [QuotientGroup.eq]
        have : (g : ↥Y) ∈ X' := Subgroup.mem_subgroupOf.2 hgX
        simpa using this
      · intro h m
        have hg : (g : ↥Y) ∈ X' := by
          rw [QuotientGroup.eq] at h
          simpa using X'.inv_mem h
        have hm : ((m : ↥P') : ↥Y) ∈ X' := hPX m.2
        show (((m : ↥P') : ↥Y) * g : ↥Y) = (g : ↥Y ⧸ X')
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using X'.mul_mem (X'.mul_mem (X'.inv_mem hg) (X'.inv_mem hm)) hg
  rw [hfix] at hmod
  have hcard : Nat.card (↥Y ⧸ X') % 2 = 1 := by
    have h1 : Nat.card (↥(({((1 : ↥Y) : ↥Y ⧸ X')} : Set (↥Y ⧸ X')))) = 1 := by simp
    have := hmod
    unfold Nat.ModEq at this
    rw [h1] at this
    simpa using this
  refine ⟨hPY, hP.2.1, ?_⟩
  have hodd : ¬ 2 ∣ X.relIndex Y := by
    rw [Subgroup.relIndex]
    change ¬ 2 ∣ Nat.card (↥Y ⧸ X')
    omega
  have hX2 : ¬ 2 ∣ P.relIndex X := hP.2.2
  intro h
  have : 2 ∣ P.relIndex X * X.relIndex Y := by
    rw [Subgroup.relIndex_mul_relIndex P X Y hPX hXY]
    exact h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 this with h1 | h1
  · exact hX2 h1
  · exact hodd h1

theorem exists_conj_of_unique_fixed {X P : Subgroup G} {z : G} (hPG : IsSylowTwoOf P ⊤)
    (hPX : P ≤ X) (hzP : z ∈ P) (hzc : ∀ y ∈ P, y * z = z * y)
    (H1 : ∀ g : G, g⁻¹ * z * g ∈ X → g ∈ X) {a g : G} (ha : a ∈ X) (ha2 : ∃ k : ℕ, a ^ 2 ^ k = 1)
    (hag : g⁻¹ * a * g ∈ X) : ∃ x ∈ X, g⁻¹ * a * g = x⁻¹ * a * x := by
  refine exists_conj_eq_of_ag hPG hPX (fun D hD n hn => ?_) ha ha2 hag
  have hzD : z ∈ D := hD.center_le hPG ⟨hzP, Subgroup.mem_centralizer_iff.2 hzc⟩
  have h1 : n⁻¹ * z * n ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (D : Set G)).inv_mem hn) z).mp
      hzD
    simpa using this
  exact H1 n (hPX (hD.1 h1))

end Fixed

end CFSG.Quasithin.H13.F431.Un
