module

public import CFSG.LocalAnalysis.UniquenessCase.UC6L620Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621a
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621L3
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621M11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)

theorem exists_inverting_quotient {L : Type} [Group L] [Finite L] (N : Subgroup L) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (hI : InvNormalizer 3 (L ⧸ N)) {E : Subgroup L} (hE : Nat.card E = 9)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∃ x : L, x ∈ normalizer (E : Set L) ∧ ∀ e ∈ E, x * x * e * (x * x)⁻¹ = e⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn, hpn, E₀, hE₀, -, x₀, hx₀, hinv₀⟩ := hI
  have hcardL : Nat.card L = 3 ^ 2 * (Nat.card N * n) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hn]
    ring
  have hdvd : ¬ 3 ∣ Nat.card N * n := fun h =>
    ((Nat.Prime.dvd_mul Nat.prime_three).1 h).elim hN hpn
  have hEsyl : IsSylowOf 3 E ⊤ := isSylowOf_top_of_card (by rw [hE]; norm_num) hcardL hdvd
  have hE₀syl : IsSylowOf 3 E₀ ⊤ := isSylowOf_top_of_card hE₀ hn hpn
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' N).ker := by rwa [QuotientGroup.ker_mk']
  exact exists_inverting_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker
    hEsyl hEab hE₀syl hx₀ hinv₀

theorem invNormalizer_of_lieModel_psl_two_of_eq {X : Type} [Group X] {p : ℕ} (hp : p = 3)
    (h : LieModel X .PSL 2 p 2) : InvNormalizer 3 X := by
  subst hp
  exact invNormalizer_of_lieModel_psl_two h

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem invNormalizer_Lbar (hr3 : m.r = 3) (hL : m.L620) :
    InvNormalizer 3 m.Lbar := by
  obtain ⟨-, h | ⟨-, h | h⟩ | ⟨h5, -⟩⟩ := hL
  · exact invNormalizer_of_lieModel_psl_two_of_eq hr3 h
  · exact invNormalizer_of_isSpor_m11 h
  · exact invNormalizer_of_lieModel_psl_three h
  · omega

theorem exists_inverting_of_invNormalizer (hr3 : m.r = 3) (h620 : m.C620)
    (hI : InvNormalizer 3 m.Lbar) :
    ∃ x : G, x ∈ m.L ∧ x ∈ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G) ∧
      ∀ e ∈ m.A ⊓ m.L, x * x * e * (x * x)⁻¹ = e⁻¹ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hcop := CFSG.pPrimeCore_coprime_card (p := m.r) (G := ↥m.L)
  have hN : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore m.r ↥m.L) := by
    intro hdiv
    have h3r : m.r ∣ 3 := by rw [hr3]
    exact ((m.hr.coprime_iff_not_dvd).1 hcop) (dvd_trans h3r hdiv)
  have hE : Nat.card ((m.A ⊓ m.L).subgroupOf m.L) = 9 := by
    rw [show Nat.card ((m.A ⊓ m.L).subgroupOf m.L) = Nat.card ↥(m.A ⊓ m.L) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      m.card_A_inf_L h620, hr3]
    norm_num
  have hEab : ∀ a ∈ (m.A ⊓ m.L).subgroupOf m.L, ∀ b ∈ (m.A ⊓ m.L).subgroupOf m.L, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    have ha' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
    have hb' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hb)).1
    have h := congrArg Subtype.val
      (m.isElemAbelian_A.1.is_comm.comm ⟨(a : G), ha'⟩ ⟨(b : G), hb'⟩)
    exact h
  obtain ⟨x, hxN, hinv⟩ := exists_inverting_quotient (CFSG.pPrimeCore m.r ↥m.L) hN hI hE hEab
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · refine mem_normalizer_of_forward_uc6 fun w hw => ?_
    have hmem : (⟨w, hw.2⟩ : ↥m.L) ∈ (m.A ⊓ m.L).subgroupOf m.L := Subgroup.mem_subgroupOf.2 hw
    exact Subgroup.mem_subgroupOf.1 ((mem_normalizer_iff.1 hxN ⟨w, hw.2⟩).1 hmem)
  · intro e he
    have hmem : (⟨e, he.2⟩ : ↥m.L) ∈ (m.A ⊓ m.L).subgroupOf m.L := Subgroup.mem_subgroupOf.2 he
    exact congrArg Subtype.val (hinv ⟨e, he.2⟩ hmem)

theorem c621x_of_L620 (hr3 : m.r = 3) (hL : m.L620) : m.C621x := by
  obtain ⟨x, hxL, hxN, hinv⟩ :=
    m.exists_inverting_of_invNormalizer hr3 hL.1 (m.invNormalizer_Lbar hr3 hL)
  exact m.c621x_of_inverting hL.1 hxL hxN hinv

theorem c621_of_L620 (hr3 : m.r = 3) (hL : m.L620) : m.C621 := by
  obtain ⟨x, hxL, hxN, hinv⟩ :=
    m.exists_inverting_of_invNormalizer hr3 hL.1 (m.invNormalizer_Lbar hr3 hL)
  exact m.c621_of_inverting hr3 hL.1 hxL hxN hinv

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
