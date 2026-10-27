module

public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C1PackClassG

public section

namespace CFSG.Quasithin.C58NS.Emb

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.C58 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isBlock2 {X T N K : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (hK : IsBlock2 X K) (h3 : 3 ∣ Nat.card K) (hNX : N ≤ X) (hTN : IsSylowTwoOf T N)
    (hTK : T ≤ normalizer (K : Set G)) : N ≤ normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ : Subgroup N := (N ⊓ normalizer (K : Set G)).subgroupOf N with hH₀
  have hTH₀ : T.subgroupOf N ≤ H₀ := fun t ht =>
    Subgroup.mem_subgroupOf.mpr ⟨t.2, hTK (Subgroup.mem_subgroupOf.mp ht)⟩
  have hodd : ¬ 2 ∣ H₀.index := fun h2 => hTN.2.2 (h2.trans (Subgroup.index_dvd_of_le hTH₀))
  have hcommute : ∀ g ∈ X, ∀ g' ∈ X, conjSubgroup K g ≠ conjSubgroup K g' →
      ⁅conjSubgroup K g, conjSubgroup K g'⁆ = ⊥ := fun g hg g' hg' hne =>
    distinctBlocksCommuteStatement (G := G) X _ _ hX (isBlock2_conjSubgroup hK hg)
      (isBlock2_conjSubgroup hK hg') hne
  have hindex : H₀.index ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have hcard : 2 < Nat.card (↥N ⧸ H₀) := hlt
    have : Fintype (↥N ⧸ H₀) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hcard
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
    set ta : N := Quotient.out a
    set tb : N := Quotient.out b
    set tc : N := Quotient.out c
    have hta : (ta : ↥N ⧸ H₀) = a := Quotient.out_eq a
    have htb : (tb : ↥N ⧸ H₀) = b := Quotient.out_eq b
    have htc : (tc : ↥N ⧸ H₀) = c := Quotient.out_eq c
    have hdist : ∀ x y : N, (x : ↥N ⧸ H₀) ≠ (y : ↥N ⧸ H₀) →
        conjSubgroup K ((x : G))⁻¹ ≠ conjSubgroup K ((y : G))⁻¹ := by
      intro x y hxy heq
      apply hxy
      rw [QuotientGroup.eq]
      have h1 := congrArg (fun A => conjSubgroup A (y : G)) heq
      simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
      have h2 : ((x⁻¹ * y : N) : G) ∈ normalizer (K : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.mp (by simpa using h1)
      exact mem_subgroupOf.mpr ⟨(x⁻¹ * y).2, h2⟩
    have hab' := hdist ta tb (by rw [hta, htb]; exact hab)
    have hac' := hdist ta tc (by rw [hta, htc]; exact hac)
    have hbc' := hdist tb tc (by rw [htb, htc]; exact hbc)
    have hmemX : ∀ x : N, ((x : G))⁻¹ ∈ X := fun x => inv_mem (hNX x.2)
    set S₃ : Finset (Subgroup G) := {conjSubgroup K ((ta : G))⁻¹, conjSubgroup K ((tb : G))⁻¹,
      conjSubgroup K ((tc : G))⁻¹} with hS₃
    have hS₃card : S₃.card = 3 := Finset.card_eq_three.2 ⟨_, _, _, hab', hac', hbc', rfl⟩
    have hconj : ∀ L ∈ S₃, ∃ x : N, L = conjSubgroup K ((x : G))⁻¹ := by
      intro L hL
      simp only [hS₃, Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl | rfl
      exacts [⟨ta, rfl⟩, ⟨tb, rfl⟩, ⟨tc, rfl⟩]
    obtain ⟨E, hEle, hE, hEcard⟩ := C1GN.exists_elemAbelian_three_pow (fun L : Subgroup G => L)
      S₃
      (fun L hL => by
        obtain ⟨x, rfl⟩ := hconj L hL
        exact (isBlock2_conjSubgroup hK (hmemX x)).1.2.1)
      (fun L hL => by
        obtain ⟨x, rfl⟩ := hconj L hL
        rw [E3.card_conjSubgroup]
        exact h3)
      (fun L hL L' hL' hne => by
        obtain ⟨x, rfl⟩ := hconj L hL
        obtain ⟨y, rfl⟩ := hconj L' hL'
        exact hcommute _ (hmemX x) _ (hmemX y) hne)
    have hEX : E ≤ X := hEle.trans (iSup₂_le fun L hL => by
      obtain ⟨x, rfl⟩ := hconj L hL
      exact (isBlock2_conjSubgroup hK (hmemX x)).2.1)
    rw [hS₃card] at hEcard
    have h3r := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEX hE hEcard
    have := C1Pack.pRank_le_two_of_isSQTKTC hSQ 3 Nat.prime_three (by norm_num)
    omega
  have h1 : H₀.index = 1 := by
    have hpos : H₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  intro n hn
  have hmem : (⟨n, hn⟩ : N) ∈ H₀ := by
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp hmem).2

end CFSG.Quasithin.C58NS.Emb
