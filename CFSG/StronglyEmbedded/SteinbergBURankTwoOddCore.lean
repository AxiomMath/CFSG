module

public import CFSG.StronglyEmbedded.SteinbergBKSylowInheritance
public import CFSG.GroupTheory.StronglyEmbeddedInvolution
public import CFSG.LocalAnalysis.Asc75.Helpers
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StronglyEmbedded.SteinbergBU

open Subgroup

variable {G : Type*} [Group G]

theorem isElementaryAbelian_of_forall {p : ℕ} {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1) :
    IsElementaryAbelian p A := CFSG.IsElementaryAbelian.of_forall hcomm hexp

variable [Finite G]

theorem exists_four_group_of_two_le_pRank (h : 2 ≤ CFSG.pRank 2 G) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  exact ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hE, hcard⟩

theorem exists_conj_four_group_le {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {E : Subgroup G} (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 2 ^ 2) :
    ∃ A : Subgroup G, A ≤ H ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hEP⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (CFSG.StronglyEmbedded.SteinbergBK.strongly_embedded_sylow_inheritance hH).1
    (default : Sylow 2 H)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  set f : G →* G := (MulAut.conj g).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  refine ⟨E.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have hxQ : MulAut.conj g • a ∈ ((g • P : Sylow 2 G) : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (P : Subgroup G) (hEP ha)
    rw [hg, hQ] at hxQ
    exact Subgroup.map_subtype_le _ hxQ
  · refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg f (congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian a ha, map_one]
  · rw [Subgroup.card_map_of_injective hfinj, hcard]

theorem rank_two_odd_core_containment (hrank : 2 ≤ CFSG.pRank 2 G) {H : Subgroup G}
    (hH : IsStronglyEmbedded H) :
    pPrimeCore 2 G ≤ H ∧ pPrimeCore 2 G = ⨅ g : G, conjugate H g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE, hEcard⟩ := exists_four_group_of_two_le_pRank hrank
  obtain ⟨A, hAH, hA, hAcard⟩ := exists_conj_four_group_le hH hE hEcard
  have hRn : (pPrimeCore 2 G).Normal := pPrimeCore_normal
  have hRodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 G) :=
    (Nat.prime_two.coprime_iff_not_dvd).1 pPrimeCore_coprime_card
  have hRH : pPrimeCore 2 G ≤ H := by
    refine CFSG.Asc75.le_of_forall_inf_centralizer_le' hA hAcard.ge hRodd ?_ ?_
    · rw [normalizer_eq_top_iff.2 hRn]
      exact le_top
    · intro b hb hb1
      have hb2 : orderOf b = 2 :=
        orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian b hb) hb1
      exact inf_le_right.trans (strong_embedding_involution_centralizers hH (hAH hb) hb2)
  refine ⟨hRH, le_antisymm (le_iInf fun g => fun x hx => ?_)
    (CFSG.GroupTheory.SteinbergBK.core_odd hH).2⟩
  refine ⟨g * x * g⁻¹, hRH (hRn.conj_mem x hx g), ?_⟩
  change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
  group

end CFSG.StronglyEmbedded.SteinbergBU
