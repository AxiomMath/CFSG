module

public import CFSG.Quasithin.Background.A3Structure313SL2
public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Background.A3Structure39Odd
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin

namespace C11P9B

section General

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem oddCore_eq_of_isSL2 {F : Subgroup Λ} [F.Normal] (hF : Odd (Nat.card F)) {r : ℕ}
    (hr : r.Prime) (h5 : 5 ≤ r) (hS : IsSL2 r (Λ ⧸ F)) : CFSG.oddCore Λ = F := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hF⟩)
  have hN : ((CFSG.oddCore Λ).map (QuotientGroup.mk' F)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card ((CFSG.oddCore Λ).map (QuotientGroup.mk' F))) :=
    (A38.odd_card_oddCore Λ).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have h0 := A313.IsSL2.eq_bot_of_odd hr h5 hS hodd
  intro x hx
  have hx' : QuotientGroup.mk' F x ∈ (CFSG.oddCore Λ).map (QuotientGroup.mk' F) := ⟨x, hx, rfl⟩
  rwa [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'

omit [Finite Λ] in
theorem not_isQuasisimple_of_fitting
    (hF : CFSG.generalizedFitting Λ = CFSG.fittingSubgroup Λ)
    (hs : Group.IsSolvable ↥(CFSG.fittingSubgroup Λ)) : ¬ CFSG.IsQuasisimple Λ := by
  intro hQ
  have htop := A36A.generalizedFitting_eq_top hQ
  rw [hF] at htop
  have : Group.IsPerfect Λ := hQ.1
  have : Nontrivial Λ := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hs' : Group.IsSolvable ↥(⊤ : Subgroup Λ) := by
    rw [← htop]
    exact hs
  exact Group.IsPerfect.not_isSolvable Λ
    (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := Λ)).toMonoidHom)
      (Subgroup.topEquiv (G := Λ)).surjective)

end General

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem case1_of_fitting {r : ℕ} (hr : r.Prime) (hr5 : r = 5 ∨ 11 ≤ r)
    (hodd : Odd (Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))))
    (hS : IsSL2 r ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    Case11_1_2One K := by
  have h5 : 5 ≤ r := by omega
  have hO := oddCore_eq_of_isSL2 hodd hr h5 hS
  obtain ⟨e⟩ := hS
  refine ⟨r, hr, hr5, (e.toMonoidHom.comp (QuotientGroup.mk' _)).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)), ?_, ?_⟩
  · exact (e.surjective.comp (QuotientGroup.mk'_surjective _)).comp
      (QuotientGroup.mk'_surjective _)
  · have h2 : (oTwoTwoPrime K).subgroupOf K =
        (CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [h2, hO]
    ext k
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem case1_of_A36Case4 (h : A36Case4 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    Case11_1_2One K ∧ ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨hF, hnil, h5, hprimes⟩ := h
  have hodd : Odd (Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) := by
    rcases Nat.even_or_odd (Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) with
      he | ho
    · have := (hprimes 2 Nat.prime_two (even_iff_two_dvd.mp he)).1
      omega
    · exact ho
  exact ⟨case1_of_fitting Nat.prime_five (Or.inl rfl) hodd h5,
    not_isQuasisimple_of_fitting hF inferInstance⟩

theorem case1_of_natural (h : ∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧
      (p % 8 = 3 ∨ p % 8 = 5) ∧
      CFSG.generalizedFitting (↥K ⧸ CFSG.pCore 2 ↥K) =
        CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
      NaturalSL2Action p (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    Case11_1_2One K ∧ ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨p, hp, h5, h8, hF, ⟨eF⟩, -, ψ, hψs, hψk, -⟩ := h
  have hp11 : 11 ≤ p := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) = p ^ 2 := by
    rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_multiplicative, ZMod.card]
  have hodd : Odd (Nat.card ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) := by
    rw [hcard]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hS : IsSL2 p ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩
  have hs : Group.IsSolvable ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Group.isSolvable_of_isSolvable_injective (f := eF.toMonoidHom) eF.injective
  exact ⟨case1_of_fitting hp (Or.inr hp11) hodd hS, not_isQuasisimple_of_fitting hF hs⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
