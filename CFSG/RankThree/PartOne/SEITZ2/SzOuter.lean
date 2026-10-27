module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.RankThree.PartOne.KE.SuzukiFixedCard
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartOne.CTP.SeitzThree

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Subgroup CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.RankThree.PartOne.KE (fixField)

@[expose] def SubfieldPairSz : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
    ∀ (σ : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → orderOf σ = p → (a = 2 → p ≠ 5) →
      ∀ g : suzukiGroup a K,
        (fixedSubgroup (szFieldAut a K σ)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (szFieldAut a K σ) →
        Subgroup.closure ((fixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) ∪
          ((fixedSubgroup (szFieldAut a K σ)).map (MulAut.conj g).toMonoidHom :
            Set (suzukiGroup a K))) = ⊤ ∨ ¬ p ∣ Nat.card (fixedSubgroup (szFieldAut a K σ))

section Basic

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_conj_mem_of_plane_suzuki {p : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (E : Subgroup (MulAut (suzukiGroup a K)))
    [IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2) :
    ∃ g : suzukiGroup a K, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  exact exists_conj_mem_of_plane_of_cyclic_outer hp
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).1 E hEc

omit [Finite K] in
theorem card_fixField_suzuki {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    ∃ b m : ℕ, a = b + (2 * b + 1) * m ∧ (2 * b + 1) * p = 2 * a + 1 ∧
      Nat.card (fixField σ) = 2 ^ (2 * b + 1) :=
  KE.card_fixField_suzuki_odd hp (by omega) hK hσ

omit [Finite K] in
theorem fixedSubgroup_eq_eqLocus (σ : K ≃+* K) :
    fixedSubgroup (szFieldAut a K σ) =
      (szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
  ext x
  rfl

theorem eq_one_of_central_fixed_szFieldAut {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hne : a = 2 → p ≠ 5) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hdvd : p ∣ Nat.card (fixedSubgroup (szFieldAut a K σ)))
    {x : suzukiGroup a K} (hx : x ∈ fixedSubgroup (szFieldAut a K σ))
    (hc : ∀ y ∈ fixedSubgroup (szFieldAut a K σ), x * y = y * x) : x = 1 := by
  classical
  obtain ⟨b, m, hab, hbp, hk⟩ := card_fixField_suzuki hp hp5 hK hσ
  obtain ⟨e⟩ := KE.fixed_szFieldAut_equiv hK hk hab
  rw [← fixedSubgroup_eq_eqLocus] at e
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · exfalso
    subst hb0
    have hk2 : Nat.card (fixField σ) = 2 := by simpa using hk
    have h20 : Nat.card (fixedSubgroup (szFieldAut a K σ)) = 20 := by
      rw [Nat.card_congr e.toEquiv]
      exact (suzuki_two_normal_five_complement_core_trivial hk2).1
    rw [h20] at hdvd
    have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
    have hp5' : p = 5 := by
      interval_cases p <;> omega
    subst hp5'
    have ha2 : a = 2 := by omega
    exact hne ha2 rfl
  · have hz : e ⟨x, hx⟩ ∈ Subgroup.center (suzukiGroup b (fixField σ)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, hy⟩ : ∃ y : ↥(fixedSubgroup (szFieldAut a K σ)), e y = g :=
        ⟨e.symm g, by simp⟩
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc y y.2).symm
    rw [KE.suzuki_center_eq_bot hb1 hk, Subgroup.mem_bot] at hz
    have h1 : (⟨x, hx⟩ : ↥(fixedSubgroup (szFieldAut a K σ))) = 1 :=
      e.injective (by rw [hz, map_one])
    exact congrArg Subtype.val h1

theorem fieldAutData_suzuki (hpair : SubfieldPairSz) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hne : a = 2 → p ≠ 5) :
    FieldAutData (suzukiGroup a K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  refine fieldAutData_of_standard (MulAut.conj : suzukiGroup a K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = szFieldAut a K σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane_suzuki hp ha hK E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    obtain ⟨σ, h, b, k, _, _, hσord, hbp, hkcard, hconj, -⟩ :=
      KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 α hord (fun ⟨g, hg⟩ => hout g hg.symm)
    refine ⟨(MulAut.conj h)⁻¹, ?_, szFieldAut a K σ, ⟨σ, hσord, rfl⟩, ?_⟩
    · exact (MulAut.conj : suzukiGroup a K →* MulAut _).range.inv_mem ⟨h, rfl⟩
    · rw [← hconj]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (szFieldAut a K)
      (zpowers_ringEquiv_eq_of_orderOf Nat.prime_two (by omega) hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ hdvd x hx hc
    exact eq_one_of_central_fixed_szFieldAut hp hp5 hK hne hσ hdvd hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d ⟨g, rfl⟩ hne'
    exact hpair a ha K hK σ p hp hp5 hσ hne g hne'

end Basic

section Index


theorem extSeitzAtOuter_suzuki_of_pair (hpair : SubfieldPairSz) (m : ℕ) :
    ExtSeitzAtOuter (.suzuki m) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hc hout
  by_cases hex : m = 2 ∧ p = 5
  · right
    exact ⟨hex.2, Or.inr (by rw [hex.1])⟩
  · left
    obtain ⟨-, a, ha, X, _, _, hfa, hXcard, ⟨e⟩⟩ := suzukiModel_of_isoLie m hiso
    have ham : a = m := by omega
    have hX : Nat.card X = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hXcard
    have hne : a = 2 → p ≠ 5 := fun h h5 => hex ⟨ham ▸ h, h5⟩
    have hd : FieldAutData K p := (fieldAutData_suzuki hpair hp hp5 ha hX hne).of_mulEquiv e hp
    exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end Index

end CFSG.RankThree.PartOne.SEITZ2
