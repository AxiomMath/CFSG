module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.5.1 normalizer-growth core
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v


/-- If a replacement Burnside field data has a strictly larger concrete
normalizer denominator, then its minimized index is strictly smaller.  This is
the pure arithmetic part of the Burnside IV.5.1 minimal-index contradiction. -/
public theorem hkt_burnside_iv51_index_lt_of_denominator_card_lt
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (T T' : Sylow q Q) (M M' : Subgroup Q)
    (hden_lt :
      Nat.card (↥((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) <
        Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q)))) :
    Nat.card (T' : Subgroup Q) / Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q))) < Nat.card (T : Subgroup Q) / Nat.card (↥((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) := by
  classical
  let D : Subgroup Q := (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)
  let D' : Subgroup Q := (T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q)
  have hTcard : Nat.card (T' : Subgroup Q) = Nat.card (T : Subgroup Q) := by
    rw [Sylow.card_eq_multiplicity T', Sylow.card_eq_multiplicity T]
  have hDdvd : Nat.card D ∣ Nat.card (T : Subgroup Q) :=
    Subgroup.card_dvd_of_le (show D ≤ (T : Subgroup Q) from inf_le_left)
  have hD'dvd : Nat.card D' ∣ Nat.card (T' : Subgroup Q) :=
    Subgroup.card_dvd_of_le (show D' ≤ (T' : Subgroup Q) from inf_le_left)
  have hD'dvdT : Nat.card D' ∣ Nat.card (T : Subgroup Q) := by
    simpa [hTcard] using hD'dvd
  have hTne : Nat.card (T : Subgroup Q) ≠ 0 := Nat.card_pos.ne'
  have hdiv_lt :
      Nat.card (T : Subgroup Q) / Nat.card D' <
        Nat.card (T : Subgroup Q) / Nat.card D := by
    exact (Nat.div_lt_div_left hTne hD'dvdT hDdvd).2 (by simpa [D, D'] using hden_lt)
  simpa [D, D', hTcard] using hdiv_lt


/-- Burnside IV.5.1, step 1: replace the original `P` by a Sylow subgroup of
`N_G(M)` containing `S = P* ∩ N_G(M)`. -/
public theorem hkt_burnside_iv51_prepared_minimal_choice_of_minimal_choice
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (M_p : IsPGroup q M)
    (M_le_T : M ≤ (T : Subgroup Q))
    (S_le_normalizer_M : (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (minimal_index :
      ∀ S' T' : Sylow q Q, ∀ M' : Subgroup Q,
        IsPGroup q M' →
        M' ≤ (S' : Subgroup Q) →
        (S' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        M' ≤ (T' : Subgroup Q) →
        ¬ (T' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        Nat.card (T : Subgroup Q) / Nat.card (↥((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) ≤
          Nat.card (T' : Subgroup Q) / Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q)))) :
    ∃ Snew : Sylow q Q,
      (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) ≤ (Snew : Subgroup Q) ∧
      IsPGroup q M ∧
      M ≤ (Snew : Subgroup Q) ∧
      (Snew : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) ∧
      M ≤ (T : Subgroup Q) ∧
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) ∧
      ∀ S' T' : Sylow q Q, ∀ M' : Subgroup Q,
        IsPGroup q M' →
        M' ≤ (S' : Subgroup Q) →
        (S' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        M' ≤ (T' : Subgroup Q) →
        ¬ (T' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        Nat.card (T : Subgroup Q) / Nat.card (↥((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) ≤
          Nat.card (T' : Subgroup Q) / Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q))) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (M : Set Q)
  let D : Subgroup Q := (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)
  have hD_le_N : D ≤ N := by
    intro x hx
    exact hx.2
  let DN : Subgroup N := D.subgroupOf N
  have hD_p : IsPGroup q D := by
    exact IsPGroup.to_le T.isPGroup' (by
      intro x hx
      exact hx.1)
  have hDN_p : IsPGroup q DN := by
    simpa [DN, D, N] using
      hD_p.of_equiv ((Subgroup.subgroupOfEquivOfLe (H := D) (K := N) hD_le_N).symm)
  obtain ⟨PN, hDN_le_PN⟩ := IsPGroup.exists_le_sylow (G := N) (p := q) hDN_p
  have hS_le_N : (S : Subgroup Q) ≤ N := by
    simpa [N] using S_le_normalizer_M
  let SN : Sylow q N := S.subtype hS_le_N
  have hPN_card : Nat.card (PN : Subgroup N) = Nat.card (S : Subgroup Q) := by
    have hSN_card : Nat.card (SN : Subgroup N) = Nat.card (S : Subgroup Q) := by
      simpa [SN, Sylow.coe_subtype] using
        (natCard_subgroupOf_eq (H := (S : Subgroup Q)) (K := N) hS_le_N)
    calc
      Nat.card (PN : Subgroup N) = Nat.card (SN : Subgroup N) := by
        rw [Sylow.card_eq_multiplicity PN, Sylow.card_eq_multiplicity SN]
      _ = Nat.card (S : Subgroup Q) := hSN_card
  let Pambient : Subgroup Q := (PN : Subgroup N).map N.subtype
  have hPambient_card : Nat.card Pambient = Nat.card (S : Subgroup Q) := by
    calc
      Nat.card Pambient = Nat.card (PN : Subgroup N) := by
        simpa [Pambient, N] using
          (Subgroup.card_map_of_injective (K := (PN : Subgroup N))
            (f := N.subtype) N.subtype_injective)
      _ = Nat.card (S : Subgroup Q) := hPN_card
  have hPambient_sylow_card :
      Nat.card Pambient = q ^ Nat.factorization (Nat.card Q) q := by
    simp [hPambient_card, Sylow.card_eq_multiplicity S]
  let Snew : Sylow q Q := Sylow.ofCard Pambient hPambient_sylow_card
  have hSnew_coe : (Snew : Subgroup Q) = Pambient := by
    simp [Snew]
  have hD_le_Snew : D ≤ (Snew : Subgroup Q) := by
    intro x hxD
    have hxDN : (⟨x, hD_le_N hxD⟩ : N) ∈ DN := by
      simpa [DN, Subgroup.mem_subgroupOf] using hxD
    have hxPN : (⟨x, hD_le_N hxD⟩ : N) ∈ (PN : Subgroup N) := hDN_le_PN hxDN
    have hxPambient : x ∈ Pambient := by
      exact ⟨⟨x, hD_le_N hxD⟩, hxPN, rfl⟩
    simpa [hSnew_coe] using hxPambient
  exact ⟨Snew,
    by simpa [D] using hD_le_Snew,
    M_p,
    by
      intro x hxM
      have hxD : x ∈ D := by
        exact ⟨M_le_T hxM, Subgroup.le_normalizer hxM⟩
      exact hD_le_Snew hxD,
    by
      intro x hxSnew
      have hxPambient : x ∈ Pambient := by simpa [hSnew_coe] using hxSnew
      rcases hxPambient with ⟨xN, _hxPN, hx_eq⟩
      rw [← hx_eq]
      exact xN.property,
    M_le_T,
    not_T_le_normalizer_M,
    minimal_index⟩

public theorem hkt_burnside_iv51_first_growth_subgroup_of_minimal_choice
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (_M_le_T : M ≤ (T : Subgroup Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (denominator_le_S :
      (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) ≤ (S : Subgroup Q)) :
    (∃ Dsub : Subgroup Q, ∃ Esub : Subgroup Q,
      Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) ∧
      Dsub ≤ (S : Subgroup Q) ∧
      Esub = (Subgroup.normalizer
        ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf
          (S : Subgroup Q) : Set (S : Subgroup Q)))).map (S : Subgroup Q).subtype ∧
      Dsub ≤ Esub ∧
      Nat.card (↥Dsub) < Nat.card (↥Esub) ∧
      IsPGroup q Esub) := by
  classical
  let D : Subgroup Q := (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)
  have hD_le_S : D ≤ (S : Subgroup Q) := by
    simpa [D] using denominator_le_S
  have hD_lt_T : D < (T : Subgroup Q) := by
    have hD_le_T : D ≤ (T : Subgroup Q) := by
      intro x hx
      exact hx.1
    have hD_ne_T : D ≠ (T : Subgroup Q) := by
      intro hD_eq_T
      apply not_T_le_normalizer_M
      intro x hxT
      have hxD : x ∈ D := by simpa [hD_eq_T] using hxT
      exact hxD.2
    exact lt_of_le_of_ne hD_le_T hD_ne_T
  have hD_lt_S : D < (S : Subgroup Q) := by
    refine lt_of_le_of_ne hD_le_S ?_
    intro hD_eq_S
    have hScard : Nat.card (S : Subgroup Q) = Nat.card (T : Subgroup Q) := by
      rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity T]
    have hcard_lt : Nat.card D < Nat.card (T : Subgroup Q) :=
      natCard_lt_of_subgroup_lt (G := Q) hD_lt_T
    have hcard_eq : Nat.card D = Nat.card (S : Subgroup Q) := by
      rw [hD_eq_S]
    exact (not_lt_of_ge (le_of_eq (hcard_eq.trans hScard).symm)) hcard_lt
  let Ssub : Subgroup Q := (S : Subgroup Q)
  let Dsub : Subgroup Q := D
  have hD_le_Ssub : Dsub ≤ Ssub := by simpa [Dsub, Ssub] using hD_le_S
  let D_S : Subgroup Ssub := Dsub.subgroupOf Ssub
  let NS : Subgroup Ssub := Subgroup.normalizer (D_S : Set Ssub)
  have hD_S_lt_top : D_S < (⊤ : Subgroup Ssub) := by
    have hlt : Dsub < Ssub := by simpa [Dsub, Ssub] using hD_lt_S
    constructor
    · intro x hx
      trivial
    · intro htop_le
      have hS_le_D : Ssub ≤ Dsub := by
        intro x hxS
        let xS : Ssub := ⟨x, hxS⟩
        have hxTop : xS ∈ (⊤ : Subgroup Ssub) := by trivial
        have hxDS : xS ∈ D_S := htop_le hxTop
        simpa [D_S, Dsub, Ssub, Subgroup.mem_subgroupOf, xS] using hxDS
      exact (not_le_of_gt hlt) hS_le_D
  have hnc : NormalizerCondition Ssub := by
    have hnc0 : NormalizerCondition (S : Subgroup Q) := by
      letI : Group.IsNilpotent (S : Subgroup Q) := S.isPGroup'.isNilpotent
      exact Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup Q))
    simpa [Ssub] using hnc0
  have hD_S_lt_NS : D_S < NS := by simpa [NS] using hnc D_S hD_S_lt_top
  let Esub : Subgroup Q := NS.map Ssub.subtype
  have hD_le_E : Dsub ≤ Esub := by
    intro x hxD
    let xS : Ssub := ⟨x, hD_le_Ssub hxD⟩
    have hxDS : xS ∈ D_S := by simpa [D_S, Subgroup.mem_subgroupOf, xS] using hxD
    have hxNS : xS ∈ NS := (Subgroup.le_normalizer (H := D_S)) hxDS
    exact ⟨xS, hxNS, rfl⟩
  have hE_p : IsPGroup q Esub := by
    have hNS_p : IsPGroup q NS := S.isPGroup'.to_subgroup NS
    exact hNS_p.map Ssub.subtype
  have hD_card_lt_E : Nat.card Dsub < Nat.card Esub := by
    have hcardD_eq : Nat.card Dsub = Nat.card D_S := by
      exact (by simpa [Dsub, D_S, Ssub] using
        (natCard_subgroupOf_eq (H := Dsub) (K := Ssub) hD_le_Ssub).symm)
    have hcardNS_eq : Nat.card Esub = Nat.card NS := by
      exact (by simpa [Esub, NS, Ssub] using
        (Subgroup.card_map_of_injective (K := NS) (f := Ssub.subtype) Ssub.subtype_injective))
    have hltNS : Nat.card D_S < Nat.card NS := natCard_lt_of_subgroup_lt (G := Ssub) hD_S_lt_NS
    rw [hcardD_eq, hcardNS_eq]
    exact hltNS
  exact ⟨Dsub, Esub,
    by simp [Dsub, D],
    by simpa [Dsub, Ssub] using hD_le_S,
    by simp [Esub, NS, D_S, Dsub, Ssub, D],
    hD_le_E,
    hD_card_lt_E,
    hE_p⟩

public theorem hkt_burnside_iv51_second_growth_subgroup_of_minimal_choice
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (T : Sylow q Q) (M Dsub : Subgroup Q)
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (Dsub_eq_denominator : Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)) :
    (∃ EstarSub : Subgroup Q,
      EstarSub = (Subgroup.normalizer
        ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf
          (T : Subgroup Q) : Set (T : Subgroup Q)))).map (T : Subgroup Q).subtype ∧
      Dsub ≤ EstarSub ∧
      Nat.card (↥Dsub) < Nat.card (↥EstarSub)) := by
  classical
  let D : Subgroup Q := (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)
  have hD_lt_T : D < (T : Subgroup Q) := by
    have hD_le_T : D ≤ (T : Subgroup Q) := by
      intro x hx
      exact hx.1
    have hD_ne_T : D ≠ (T : Subgroup Q) := by
      intro hD_eq_T
      apply not_T_le_normalizer_M
      intro x hxT
      have hxD : x ∈ D := by simpa [hD_eq_T] using hxT
      exact hxD.2
    exact lt_of_le_of_ne hD_le_T hD_ne_T
  have hDsub_lt_Tstar : Dsub < (T : Subgroup Q) := by
    simpa [D, Dsub_eq_denominator] using hD_lt_T
  let Tstar : Subgroup Q := (T : Subgroup Q)
  have hD_le_Tstar : Dsub ≤ Tstar := le_of_lt hDsub_lt_Tstar
  let D_T : Subgroup Tstar := Dsub.subgroupOf Tstar
  let NT : Subgroup Tstar := Subgroup.normalizer (D_T : Set Tstar)
  have hD_T_lt_top : D_T < (⊤ : Subgroup Tstar) := by
    constructor
    · intro x hx
      trivial
    · intro htop_le
      have hT_le_D : Tstar ≤ Dsub := by
        intro x hxT
        let xT : Tstar := ⟨x, hxT⟩
        have hxTop : xT ∈ (⊤ : Subgroup Tstar) := by trivial
        have hxDT : xT ∈ D_T := htop_le hxTop
        simpa [D_T, Tstar, Subgroup.mem_subgroupOf, xT] using hxDT
      exact (not_le_of_gt hDsub_lt_Tstar) hT_le_D
  have hnc : NormalizerCondition Tstar := by
    have hnc0 : NormalizerCondition (T : Subgroup Q) := by
      letI : Group.IsNilpotent (T : Subgroup Q) := T.isPGroup'.isNilpotent
      exact Group.normalizerCondition_of_isNilpotent (G := (T : Subgroup Q))
    simpa [Tstar] using hnc0
  have hD_T_lt_NT : D_T < NT := by simpa [NT] using hnc D_T hD_T_lt_top
  let Estar : Subgroup Q := NT.map Tstar.subtype
  have hD_le_Estar : Dsub ≤ Estar := by
    intro x hxD
    let xT : Tstar := ⟨x, hD_le_Tstar hxD⟩
    have hxDT : xT ∈ D_T := by simpa [D_T, Subgroup.mem_subgroupOf, xT] using hxD
    have hxNT : xT ∈ NT := (Subgroup.le_normalizer (H := D_T)) hxDT
    exact ⟨xT, hxNT, rfl⟩
  have hD_card_lt_Estar : Nat.card Dsub < Nat.card Estar := by
    have hcardD_eq : Nat.card Dsub = Nat.card D_T := by
      exact (by simpa [D_T, Tstar] using
        (natCard_subgroupOf_eq (H := Dsub) (K := Tstar) hD_le_Tstar).symm)
    have hcardNT_eq : Nat.card Estar = Nat.card NT := by
      exact (by simpa [Estar, NT, Tstar] using
        (Subgroup.card_map_of_injective (K := NT) (f := Tstar.subtype) Tstar.subtype_injective))
    have hltNT : Nat.card D_T < Nat.card NT := natCard_lt_of_subgroup_lt (G := Tstar) hD_T_lt_NT
    rw [hcardD_eq, hcardNT_eq]
    exact hltNT
  exact ⟨Estar,
    by simp [Estar, NT, D_T, Tstar, Dsub_eq_denominator],
    hD_le_Estar,
    hD_card_lt_Estar⟩

public theorem hkt_burnside_iv51_minimal_index_choice_exists
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (M_p : IsPGroup q M)
    (M_le_S : M ≤ (S : Subgroup Q))
    (S_le_normalizer_M : (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (M_le_T : M ≤ (T : Subgroup Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q)) :
    ∃ Smin : Sylow q Q, ∃ Tmin : Sylow q Q, ∃ Mmin : Subgroup Q,
      IsPGroup q Mmin ∧
      Mmin ≤ (Smin : Subgroup Q) ∧
      (Smin : Subgroup Q) ≤ Subgroup.normalizer (Mmin : Set Q) ∧
      Mmin ≤ (Tmin : Subgroup Q) ∧
      ¬ (Tmin : Subgroup Q) ≤ Subgroup.normalizer (Mmin : Set Q) ∧
      ∀ S' T' : Sylow q Q, ∀ M' : Subgroup Q,
        IsPGroup q M' →
        M' ≤ (S' : Subgroup Q) →
        (S' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        M' ≤ (T' : Subgroup Q) →
        ¬ (T' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        Nat.card (Tmin : Subgroup Q) / Nat.card (↥((Tmin : Subgroup Q) ⊓ Subgroup.normalizer (Mmin : Set Q))) ≤
          Nat.card (T' : Subgroup Q) / Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q))) := by
  classical
  let idx (T0 : Sylow q Q) (M0 : Subgroup Q) : ℕ :=
    Nat.card (T0 : Subgroup Q) / Nat.card (↥((T0 : Subgroup Q) ⊓ Subgroup.normalizer (M0 : Set Q)))
  have hExists : ∃ n : ℕ, ∃ S0 T0 : Sylow q Q, ∃ M0 : Subgroup Q,
      IsPGroup q M0 ∧
      M0 ≤ (S0 : Subgroup Q) ∧
      (S0 : Subgroup Q) ≤ Subgroup.normalizer (M0 : Set Q) ∧
      M0 ≤ (T0 : Subgroup Q) ∧
      ¬ (T0 : Subgroup Q) ≤ Subgroup.normalizer (M0 : Set Q) ∧
      idx T0 M0 = n := by
    exact ⟨idx T M, S, T, M, M_p, M_le_S, S_le_normalizer_M,
      M_le_T, not_T_le_normalizer_M, rfl⟩
  obtain ⟨Smin, Tmin, Mmin, hMmin_p, hMmin_le_S, hSmin_norm,
      hMmin_le_T, hTmin_not, hidx_min⟩ := Nat.find_spec hExists
  exact ⟨Smin, Tmin, Mmin, hMmin_p, hMmin_le_S, hSmin_norm,
    hMmin_le_T, hTmin_not,
    fun S' T' M' hM'_p hM'_le_S hS'_norm hM'_le_T hT'_not => by
      have hcandidate :
          (∃ S0 T0 : Sylow q Q, ∃ M0 : Subgroup Q,
            IsPGroup q M0 ∧
            M0 ≤ (S0 : Subgroup Q) ∧
            (S0 : Subgroup Q) ≤ Subgroup.normalizer (M0 : Set Q) ∧
            M0 ≤ (T0 : Subgroup Q) ∧
            ¬ (T0 : Subgroup Q) ≤ Subgroup.normalizer (M0 : Set Q) ∧
            idx T0 M0 = idx T' M') := by
        exact ⟨S', T', M', hM'_p, hM'_le_S, hS'_norm,
          hM'_le_T, hT'_not, rfl⟩
      have hmin : Nat.find hExists ≤ idx T' M' :=
        Nat.find_min' hExists hcandidate
      have hmin' : idx Tmin Mmin ≤ idx T' M' := by
        rw [hidx_min]
        exact hmin
      simpa [idx] using hmin'⟩

public theorem hkt_burnside_iv51_growth_subgroups_of_prepared_minimal_choice
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (M_p : IsPGroup q M)
    (M_le_S : M ≤ (S : Subgroup Q))
    (S_le_normalizer_M : (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (M_le_T : M ≤ (T : Subgroup Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (minimal_index :
      ∀ S' T' : Sylow q Q, ∀ M' : Subgroup Q,
        IsPGroup q M' →
        M' ≤ (S' : Subgroup Q) →
        (S' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        M' ≤ (T' : Subgroup Q) →
        ¬ (T' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        Nat.card (T : Subgroup Q) / Nat.card (↥((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) ≤
          Nat.card (T' : Subgroup Q) / Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q))))
    (denominator_le_S :
      (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) ≤ (S : Subgroup Q)) :
    (∃ Dsub : Subgroup Q, ∃ Esub : Subgroup Q, ∃ EstarSub : Subgroup Q,
      Dsub = (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q) ∧
      Dsub ≤ (S : Subgroup Q) ∧
      Esub = (Subgroup.normalizer
        ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf
          (S : Subgroup Q) : Set (S : Subgroup Q)))).map (S : Subgroup Q).subtype ∧
      EstarSub = (Subgroup.normalizer
        ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf
          (T : Subgroup Q) : Set (T : Subgroup Q)))).map (T : Subgroup Q).subtype ∧
      Dsub ≤ Esub ∧
      Nat.card (↥Dsub) < Nat.card (↥Esub) ∧
      Dsub ≤ EstarSub ∧
      Nat.card (↥Dsub) < Nat.card (↥EstarSub) ∧
      IsPGroup q Esub ∧
      (∀ B : Subgroup Q,
        Esub ≤ B → IsPGroup q B → B ≤ Subgroup.normalizer (M : Set Q))) := by
  classical
  obtain ⟨Dsub, Esub, hDsub_eq_denominator, hDsub_le_selected_sylow,
      hEsub_eq_firstNormalizer, hDsub_le_Esub, hDsub_card_lt_Esub, hEsub_p⟩ :=
    hkt_burnside_iv51_first_growth_subgroup_of_minimal_choice
      (Q := Q) (q := q) S T M M_le_T not_T_le_normalizer_M denominator_le_S
  obtain ⟨EstarSub, hEstarSub_eq_secondNormalizer,
      hDsub_le_EstarSub, hDsub_card_lt_EstarSub⟩ :=
    hkt_burnside_iv51_second_growth_subgroup_of_minimal_choice
      (Q := Q) (q := q) T M Dsub not_T_le_normalizer_M hDsub_eq_denominator
  have hcontrol : ∀ B : Subgroup Q,
      Esub ≤ B → IsPGroup q B → B ≤ Subgroup.normalizer (M : Set Q) := by
    intro B hE_le_B hB_p
    let N : Subgroup Q := Subgroup.normalizer (M : Set Q)
    have hE_le_N : Esub ≤ N := by
      intro x hxE
      have hxFirst : x ∈ (Subgroup.normalizer
          ((((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)).subgroupOf
            (S : Subgroup Q) : Set (S : Subgroup Q)))).map (S : Subgroup Q).subtype := by
        simpa [hEsub_eq_firstNormalizer] using hxE
      rcases hxFirst with ⟨y, _hy, rfl⟩
      exact S_le_normalizer_M y.property
    by_contra hB_not
    obtain ⟨Pss, hB_le_Pss⟩ := IsPGroup.exists_le_sylow (G := Q) (p := q) hB_p
    have hPss_not : ¬ (Pss : Subgroup Q) ≤ N := by
      intro hPss_le_N
      exact hB_not (fun x hxB => hPss_le_N (hB_le_Pss hxB))
    have hM_le_Pss : M ≤ (Pss : Subgroup Q) := by
      intro x hxM
      have hxD : x ∈ Dsub := by
        rw [hDsub_eq_denominator]
        exact ⟨M_le_T hxM, Subgroup.le_normalizer hxM⟩
      exact hB_le_Pss (hE_le_B (hDsub_le_Esub hxD))
    let oldD : Subgroup Q := (T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)
    let newD : Subgroup Q := (Pss : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q)
    have hE_le_newD : Esub ≤ newD := by
      intro x hxE
      exact ⟨hB_le_Pss (hE_le_B hxE), by simpa [N, newD] using hE_le_N hxE⟩
    have hold_card : Nat.card oldD = Nat.card Dsub := by
      simpa [oldD] using congrArg (fun H : Subgroup Q => Nat.card H) hDsub_eq_denominator.symm
    have hden_lt_old : Nat.card oldD < Nat.card newD := by
      calc
        Nat.card oldD = Nat.card Dsub := hold_card
        _ < Nat.card Esub := hDsub_card_lt_Esub
        _ ≤ Nat.card newD := Subgroup.card_le_of_le hE_le_newD
    have hden_lt :
        Nat.card (↥((T : Subgroup Q) ⊓
          Subgroup.normalizer (M : Set Q))) <
        Nat.card (↥((Pss : Subgroup Q) ⊓
          Subgroup.normalizer (M : Set Q))) := by
      simpa [oldD, newD] using hden_lt_old
    have hstrict :
        Nat.card (Pss : Subgroup Q) / Nat.card (↥((Pss : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) <
          Nat.card (T : Subgroup Q) / Nat.card (↥((T : Subgroup Q) ⊓ Subgroup.normalizer (M : Set Q))) :=
      hkt_burnside_iv51_index_lt_of_denominator_card_lt
        (Q := Q) (q := q) T Pss M M hden_lt
    exact (not_lt_of_ge
      (minimal_index S Pss M
        M_p M_le_S S_le_normalizer_M
        hM_le_Pss hPss_not)) hstrict
  exact ⟨Dsub, Esub, EstarSub,
    hDsub_eq_denominator,
    hDsub_le_selected_sylow,
    hEsub_eq_firstNormalizer,
    hEstarSub_eq_secondNormalizer,
    hDsub_le_Esub,
    hDsub_card_lt_Esub,
    hDsub_le_EstarSub,
    hDsub_card_lt_EstarSub,
    hEsub_p,
    hcontrol⟩

public theorem hkt_burnside_iv51_growth_subgroups_of_minimal_choice
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (M_p : IsPGroup q M)
    (M_le_S : M ≤ (S : Subgroup Q))
    (S_le_normalizer_M : (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (M_le_T : M ≤ (T : Subgroup Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q)) :
    ∃ Smin : Sylow q Q, ∃ Tmin : Sylow q Q, ∃ Mmin : Subgroup Q,
      IsPGroup q Mmin ∧
      Mmin ≤ (Smin : Subgroup Q) ∧
      (Smin : Subgroup Q) ≤ Subgroup.normalizer (Mmin : Set Q) ∧
      Mmin ≤ (Tmin : Subgroup Q) ∧
      ¬ (Tmin : Subgroup Q) ≤ Subgroup.normalizer (Mmin : Set Q) ∧
      (∀ S' T' : Sylow q Q, ∀ M' : Subgroup Q,
        IsPGroup q M' →
        M' ≤ (S' : Subgroup Q) →
        (S' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        M' ≤ (T' : Subgroup Q) →
        ¬ (T' : Subgroup Q) ≤ Subgroup.normalizer (M' : Set Q) →
        Nat.card (Tmin : Subgroup Q) / Nat.card (↥((Tmin : Subgroup Q) ⊓ Subgroup.normalizer (Mmin : Set Q))) ≤
          Nat.card (T' : Subgroup Q) / Nat.card (↥((T' : Subgroup Q) ⊓ Subgroup.normalizer (M' : Set Q)))) ∧
      (∃ Dsub : Subgroup Q, ∃ Esub : Subgroup Q, ∃ EstarSub : Subgroup Q,
        Dsub = (Tmin : Subgroup Q) ⊓ Subgroup.normalizer (Mmin : Set Q) ∧
        Dsub ≤ (Smin : Subgroup Q) ∧
        Esub = (Subgroup.normalizer
          ((((Tmin : Subgroup Q) ⊓ Subgroup.normalizer (Mmin : Set Q)).subgroupOf
            (Smin : Subgroup Q) : Set (Smin : Subgroup Q)))).map (Smin : Subgroup Q).subtype ∧
        EstarSub = (Subgroup.normalizer
          ((((Tmin : Subgroup Q) ⊓ Subgroup.normalizer (Mmin : Set Q)).subgroupOf
            (Tmin : Subgroup Q) : Set (Tmin : Subgroup Q)))).map (Tmin : Subgroup Q).subtype ∧
        Dsub ≤ Esub ∧
        Nat.card (↥Dsub) < Nat.card (↥Esub) ∧
        Dsub ≤ EstarSub ∧
        Nat.card (↥Dsub) < Nat.card (↥EstarSub) ∧
        IsPGroup q Esub ∧
        (∀ B : Subgroup Q,
          Esub ≤ B → IsPGroup q B → B ≤ Subgroup.normalizer (Mmin : Set Q))) := by
  classical
  obtain ⟨Smin, Tmin, Mmin, hMmin_p, hMmin_le_S, hSmin_norm,
      hMmin_le_T, hTmin_not, hminimal⟩ :=
    hkt_burnside_iv51_minimal_index_choice_exists
      (Q := Q) (q := q) S T M M_p M_le_S S_le_normalizer_M M_le_T not_T_le_normalizer_M
  obtain ⟨Sprep, hdenominator_le_S, hMprep_p, hMprep_le_S,
      hSprep_norm, hMprep_le_T, hTprep_not, hminimal_prep⟩ :=
    hkt_burnside_iv51_prepared_minimal_choice_of_minimal_choice
      (Q := Q) (q := q) Smin Tmin Mmin hMmin_p hMmin_le_T hSmin_norm hTmin_not hminimal
  obtain ⟨Dsub, Esub, EstarSub, hDsub_eq_denominator, hDsub_le_selected_sylow,
      hEsub_eq_firstNormalizer, hEstarSub_eq_secondNormalizer, hDsub_le_Esub,
      hDsub_card_lt_Esub, hDsub_le_EstarSub, hDsub_card_lt_EstarSub, hEsub_p,
      hcontrol⟩ :=
    hkt_burnside_iv51_growth_subgroups_of_prepared_minimal_choice
      (Q := Q) (q := q) Sprep Tmin Mmin hMprep_p hMprep_le_S hSprep_norm
      hMprep_le_T hTprep_not hminimal_prep hdenominator_le_S
  exact ⟨Sprep, Tmin, Mmin,
    hMprep_p,
    hMprep_le_S,
    hSprep_norm,
    hMprep_le_T,
    hTprep_not,
    hminimal_prep,
    Dsub, Esub, EstarSub,
    hDsub_eq_denominator,
    hDsub_le_selected_sylow,
    hEsub_eq_firstNormalizer,
    hEstarSub_eq_secondNormalizer,
    hDsub_le_Esub,
    hDsub_card_lt_Esub,
    hDsub_le_EstarSub,
    hDsub_card_lt_EstarSub,
    hEsub_p,
    hcontrol⟩

end External
end CFSG.BenderSuzuki
