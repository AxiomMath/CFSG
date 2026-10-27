module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup CFSG.RankThree.PartOne.OutStructure

theorem card_le_of_comparable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ g : G, g ^ p = 1)
    (hcmp : ∀ a b : G, a ∈ Subgroup.zpowers b ∨ b ∈ Subgroup.zpowers a) : Nat.card G ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  rw [not_le] at hlt
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by have := hp.two_le; omega)
  obtain ⟨g, hg1⟩ := exists_ne (1 : G)
  have hog : orderOf g = p := orderOf_eq_prime (hexp g) hg1
  have hex : ∃ a : G, a ∉ Subgroup.zpowers g := by
    by_contra hall
    have hall' : ∀ a : G, a ∈ Subgroup.zpowers g := fun a => by_contra fun h => hall ⟨a, h⟩
    have htop : Subgroup.zpowers g = ⊤ := eq_top_iff.2 fun a _ => hall' a
    have hcardtop : Nat.card (Subgroup.zpowers g) = Nat.card G := by
      rw [htop, Subgroup.card_top]
    rw [Nat.card_zpowers, hog] at hcardtop
    omega
  obtain ⟨a, ha⟩ := hex
  rcases hcmp a g with h | h
  · exact ha h
  · have ha1 : a ≠ 1 := by
      rintro rfl
      apply hg1
      simpa using h
    have hoa : orderOf a = p := orderOf_eq_prime (hexp a) ha1
    have hle : Subgroup.zpowers g ≤ Subgroup.zpowers a := (Subgroup.zpowers_le).2 h
    have heq : Subgroup.zpowers g = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hog, hoa])
    exact ha (heq ▸ Subgroup.mem_zpowers a)

theorem relIndex_le_of_outPChain {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (h : OutPChain p S) (P : Subgroup (MulAut S)) (hP : ∀ x ∈ P, x ^ p = 1) :
    (P ⊓ (MulAut.conj : S →* MulAut S).range).relIndex P ≤ p := by
  obtain ⟨D, E, hInnD, hD, hE, hcmp⟩ := h
  have hpow : ∀ α ∈ P, ∃ k : ℕ, α ^ (p ^ k) ∈ D := fun α hα =>
    ⟨1, by rw [pow_one, hP α hα]; exact D.one_mem⟩
  have hPE : ∀ α ∈ P, α ∈ E := fun α hα => hE α (hpow α hα)
  have hPD : ∀ z : MulAut S, z ∈ P → z ∈ D → z ∈ Inn S := fun z hz hzD =>
    hD z hzD 1 (by rw [pow_one, hP z hz]; exact (Inn S).one_mem)
  rw [Subgroup.inf_relIndex_left]
  haveI : (Inn S).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  change ((Inn S).subgroupOf P).index ≤ p
  have hidx : ((Inn S).subgroupOf P).index = Nat.card (↥P ⧸ (Inn S).subgroupOf P) := rfl
  rw [hidx]
  refine card_le_of_comparable hp ?_ ?_
  · intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_pow]
    have hx : x ^ p = 1 := Subtype.ext (by simpa using hP x x.2)
    rw [hx, QuotientGroup.mk_one]
  · intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hmem : ∀ (u v : ↥P) (m : ℤ), ((u : MulAut S) * (v : MulAut S) ^ m ∈ D) →
        (QuotientGroup.mk u : ↥P ⧸ (Inn S).subgroupOf P) ∈
          Subgroup.zpowers (QuotientGroup.mk v : ↥P ⧸ (Inn S).subgroupOf P) := by
      intro u v m hm
      have hu : u * v ^ m ∈ (Inn S).subgroupOf P := by
        rw [Subgroup.mem_subgroupOf]
        exact hPD _ (P.mul_mem u.2 (P.zpow_mem v.2 m)) hm
      have h1 : (QuotientGroup.mk (u * v ^ m) : ↥P ⧸ (Inn S).subgroupOf P) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hu
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
      refine Subgroup.mem_zpowers_iff.2 ⟨-m, ?_⟩
      rw [zpow_neg]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rcases hcmp (x : MulAut S) (hPE x x.2) (y : MulAut S) (hPE y y.2) (hpow x x.2) (hpow y y.2) with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl (hmem x y m hm)
    · exact Or.inr (hmem y x m hm)

end CFSG.RankThree.PartTwo.Sec13.F135Last
