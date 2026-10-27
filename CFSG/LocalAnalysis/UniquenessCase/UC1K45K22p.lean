module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pRestrict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open K22p

theorem exists_isMinInv {M : Type} [Group M] [Finite M] (σ : MulAut M) [Nontrivial M] :
    ∃ N : Subgroup M, IsMinInv σ N := by
  let S : Set (Subgroup M) := {N | N.Normal ∧ (∀ x ∈ N, σ x ∈ N) ∧ N ≠ ⊥}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty :=
    ⟨⊤, inferInstance, (fun x _ => Subgroup.mem_top (σ x)), top_ne_bot⟩
  obtain ⟨N, hNmem, hNmin⟩ := hSfin.exists_minimal hSne
  refine ⟨N, ?_⟩
  exact
    { normal := hNmem.1
      invariant := hNmem.2.1
      ne_bot := hNmem.2.2
      minimal := by
        intro N' hN'n hN'inv hN'le
        rcases eq_or_ne N' ⊥ with h | h
        · exact Or.inl h
        · exact Or.inr (le_antisymm hN'le (hNmin ⟨hN'n, hN'inv, h⟩ hN'le)) }

theorem sylow_map_invariant_of_isMinInv {M : Type} [Group M] [Finite M] {σ : MulAut M}
    {N : Subgroup M} (hN : IsMinInv σ N) (hNab : IsMulCommutative ↥N) {r : ℕ} [Fact r.Prime]
    (R : Sylow r ↥N) :
    ∀ x ∈ (R : Subgroup ↥N).map N.subtype, σ x ∈ (R : Subgroup ↥N).map N.subtype := by
  letI : IsMulCommutative ↥N := hNab
  have hRchar : (R : Subgroup ↥N).Characteristic :=
    Sylow.characteristic_of_normal R (inferInstance : (R : Subgroup ↥N).Normal)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let hNmap := map_eq_of_pointwise_invariant σ N hN.invariant
  let σN : MulAut ↥N := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ N hNmap
  have hfixR : σN y ∈ (R : Subgroup ↥N) := by
    have : y ∈ (R : Subgroup ↥N).comap σN.toMonoidHom := by
      rw [hRchar.fixed σN]; exact hy
    exact this
  exact Subgroup.mem_map.mpr ⟨σN y, hfixR,
    CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_apply σ N hNmap y⟩

theorem isPGroup_of_isMinInv_of_isMulCommutative {M : Type} [Group M] [Finite M]
    {σ : MulAut M} {N : Subgroup M} (hN : IsMinInv σ N) (hNab : IsMulCommutative ↥N) :
    ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥N := by
  letI : IsMulCommutative ↥N := hNab
  haveI : N.Normal := hN.normal
  have hNcard : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN.ne_bot
  obtain ⟨r, hrprime, hrdiv⟩ := Nat.exists_prime_and_dvd hNcard.ne'
  letI : Fact r.Prime := ⟨hrprime⟩
  let R : Sylow r ↥N := Sylow.nonempty.some
  have hRchar : (R : Subgroup ↥N).Characteristic :=
    Sylow.characteristic_of_normal R (inferInstance : (R : Subgroup ↥N).Normal)
  letI : (R : Subgroup ↥N).Characteristic := hRchar
  have hRnorm : ((R : Subgroup ↥N).map N.subtype).Normal := inferInstance
  have hRinv := sylow_map_invariant_of_isMinInv hN hNab R
  have hRne : (R : Subgroup ↥N) ≠ ⊥ := by
    intro hbot
    have hidx : (R : Subgroup ↥N).index = Nat.card ↥N := by
      rw [show (R : Subgroup ↥N) = ⊥ from hbot, Subgroup.index_bot]
    exact R.not_dvd_index (hidx.symm ▸ hrdiv)
  have hR'ne : ((R : Subgroup ↥N).map N.subtype) ≠ ⊥ := fun h =>
    hRne ((Subgroup.map_eq_bot_iff_of_injective (H := (R : Subgroup ↥N))
      N.subtype_injective).mp h)
  have hR'eq : ((R : Subgroup ↥N).map N.subtype) = N := by
    rcases hN.minimal ((R : Subgroup ↥N).map N.subtype) hRnorm hRinv
      (Subgroup.map_subtype_le _) with h | h
    · exact absurd h hR'ne
    · exact h
  refine ⟨r, hrprime, ?_⟩
  have hRpg : IsPGroup r ↥((R : Subgroup ↥N).map N.subtype) := (R.isPGroup').map N.subtype
  rwa [hR'eq] at hRpg

theorem quotient_good_of_commSub_top {p : ℕ} {M : Type} [Group M] [Finite M] (σ : MulAut M)
    (hGood : Good p M σ) (hcomm : commSub σ = ⊤) {N : Subgroup M} [N.Normal]
    (hNmap : N.map σ.toMonoidHom = N) (hNne : N ≠ ⊥) :
    Good p (M ⧸ N) (quotientAutomorphism σ N hNmap) ∧
      commSub (quotientAutomorphism σ N hNmap) = ⊤ ∧ Nat.card (M ⧸ N) < Nat.card M := by
  have hNinv : ∀ x ∈ N, σ x ∈ N :=
    fun x hx => Subgroup.map_le_iff_le_comap.mp (le_of_eq hNmap) hx
  refine ⟨quotient_good hGood N hNinv, ?_, ?_⟩
  · rw [quotient_commSub_eq σ N hNmap, hcomm]
    exact Subgroup.map_top_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · have hNcard : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
    have hprod : Nat.card (M ⧸ N) * Nat.card ↥N = Nat.card M := by
      rw [← Subgroup.index_eq_card (H := N), Subgroup.index_mul_card]
    calc Nat.card (M ⧸ N) < Nat.card (M ⧸ N) * Nat.card ↥N :=
          lt_mul_of_one_lt_right Nat.card_pos hNcard
      _ = Nat.card M := hprod

theorem prime_eq_two_or_p_of_isPGroup_of_isMinInv (hAb : ChiefAb) {p : ℕ} {M : Type}
    [Group M] [Finite M] {σ : MulAut M} (hGood : Good p M σ) (hcomm : commSub σ = ⊤)
    {N : Subgroup M} [N.Normal] (hN : IsMinInv σ N) {r : ℕ} (hr : r.Prime)
    (hrpg : IsPGroup r ↥N)
    (hQuot : ∀ s : ℕ, s.Prime → s ∣ Nat.card (M ⧸ N) → s = 2 ∨ s = p) :
    r = 2 ∨ r = p := by
  by_cases hr2 : r = 2
  · exact Or.inl hr2
  by_cases hrp : r = p
  · exact Or.inr hrp
  · exfalso
    have hfixr : FixesSylow σ r := hGood.fixesSylow r hr hr2 hrp
    have hnotdvd : ¬ r ∣ N.index := by
      rw [Subgroup.index_eq_card]
      intro hd
      rcases hQuot r hr hd with h | h
      · exact hr2 h
      · exact hrp h
    exact hN.ne_bot (hAb r hr M σ hcomm N hN.normal hrpg hnotdvd hfixr)

theorem prime_dvd_card_eq_two_or_p {p : ℕ} {M : Type} [Group M] [Finite M] {N : Subgroup M}
    [N.Normal] {r q : ℕ} (hr : r.Prime) (hrpg : IsPGroup r ↥N) (hr2p : r = 2 ∨ r = p)
    (hQuot : ∀ s : ℕ, s.Prime → s ∣ Nat.card (M ⧸ N) → s = 2 ∨ s = p)
    (hq : q.Prime) (hqdiv : q ∣ Nat.card M) : q = 2 ∨ q = p := by
  have hprod : Nat.card M = Nat.card (M ⧸ N) * Nat.card ↥N := by
    rw [← Subgroup.index_eq_card (H := N), Subgroup.index_mul_card]
  rw [hprod] at hqdiv
  rcases hq.dvd_or_dvd hqdiv with hqQ | hqN
  · exact hQuot q hq hqQ
  · letI : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := hrpg.exists_card_eq
    rw [hn] at hqN
    have hqr : q = r := Nat.prime_eq_prime_of_dvd_pow hq hr hqN
    rcases hr2p with h | h
    · exact Or.inl (by rw [hqr, h])
    · exact Or.inr (by rw [hqr, h])

theorem k22p_of_commSub_top (hAb : ChiefAb) (hS1 : SimpleThreePrimeIsSz) (hS2 : SzOrder3Aut)
    (hNon : ChiefNon) {p : ℕ} {M : Type} [Group M] [Finite M] (σ : MulAut M)
    (hGood : Good p M σ) (hcomm : commSub σ = ⊤) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card M → q = 2 ∨ q = p := by
  have main : ∀ n, ∀ (M : Type) [Group M] [Finite M] (σ : MulAut M),
      Nat.card M = n → Good p M σ → commSub σ = ⊤ →
      ∀ q : ℕ, q.Prime → q ∣ Nat.card M → q = 2 ∨ q = p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro M _ _ σ hcard hGood hcomm q hq hqdiv
      by_cases htriv : Nat.card M = 1
      · rw [htriv] at hqdiv
        exact (hq.not_dvd_one hqdiv).elim
      · haveI : Nontrivial M := by
          rw [← Finite.one_lt_card_iff_nontrivial]
          exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') (Ne.symm htriv)
        obtain ⟨N, hN⟩ := exists_isMinInv σ
        by_cases hNab : IsMulCommutative ↥N
        · letI : N.Normal := hN.normal
          let hNmap := map_eq_of_pointwise_invariant σ N hN.invariant
          let σbar : MulAut (M ⧸ N) := quotientAutomorphism σ N hNmap
          obtain ⟨hGoodQuot, hcommQuot, hquotlt⟩ :=
            quotient_good_of_commSub_top σ hGood hcomm hNmap hN.ne_bot
          have hQuotPrimes : ∀ s : ℕ, s.Prime → s ∣ Nat.card (M ⧸ N) → s = 2 ∨ s = p :=
            ih (Nat.card (M ⧸ N)) (hcard ▸ hquotlt) (M ⧸ N) σbar rfl hGoodQuot hcommQuot
          obtain ⟨r, hr, hrpg⟩ := isPGroup_of_isMinInv_of_isMulCommutative hN hNab
          have hr2p : r = 2 ∨ r = p :=
            prime_eq_two_or_p_of_isPGroup_of_isMinInv hAb hGood hcomm hN hr hrpg hQuotPrimes
          exact prime_dvd_card_eq_two_or_p hr hrpg hr2p hQuotPrimes hq hqdiv
        · exact (hNon hS1 hS2 p M hGood.isKGroup hGood.not_dvd_three σ hGood.pow_three
            hcomm hGood.fixesSylow N hN hNab).elim
  exact main (Nat.card M) M σ rfl hGood hcomm

theorem k22pAbs_of (hAb : ChiefAb) (hNon : ChiefNon) : K22pAbs := by
  intro hS1 hS2 p M _ _ hK h3 σ hσ hfix q hq hqdiv
  have hGood : Good p M σ := ⟨hK, h3, hσ, hfix⟩
  let L : Subgroup M := commAct σ
  have hcomm : commSub σ = L := (commAct_eq_commSub σ).symm
  have hLn : L.Normal := commAct_normal σ
  letI : L.Normal := hLn
  have hLinv : ∀ x ∈ L, σ x ∈ L := fun x hx => commAct_invariant σ hx
  let hLmap := map_eq_of_pointwise_invariant σ L hLinv
  let τ : MulAut L := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ L hLmap
  have hLgood : Good p L τ := good_restrict hGood hLinv
  have hLtop : commSub τ = ⊤ := commSub_commAct_restrict_eq_top σ hσ h3
  have hLprimes : ∀ s : ℕ, s.Prime → s ∣ Nat.card L → s = 2 ∨ s = p :=
    k22p_of_commSub_top hAb hS1 hS2 hNon τ hLgood hLtop
  have hcard : Nat.card L = Nat.card ↥(commSub σ) :=
    (Nat.card_congr (MulEquiv.subgroupCongr hcomm)).symm
  exact hLprimes q hq (by rwa [hcard])

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
