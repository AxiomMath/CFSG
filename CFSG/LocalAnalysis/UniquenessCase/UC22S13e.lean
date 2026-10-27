module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S13d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.Quasithin.Vol2.KGFact838
import CFSG.RankThree.PartOne.S11c.Sec66PSL2
import CFSG.RankThree.PartOne.S11c.Sec66Sz
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Blueprint
open scoped commutatorElement
open CFSG.RankThree.PartOne.Sec66T (fixSub fixSubEquiv sz_coset_data psl_two_exists_fixSub_equiv)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (coordinateG pslEquivCoordinateG)

theorem uc22s13e_inner_of_odd {T : Type} [Group T] [Finite T]
    (hT : (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd T p) ∨ IsJ1 T) {m : ℕ} (hm : Odd m)
    {α : MulAut T} (hα : α ^ m = 1) : α ∈ (MulAut.conj : T →* MulAut T).range := by
  rcases hT with ⟨p, -, -, hp⟩ | hJ
  · exact uc22s13d_out_mem_of_isPGroup (CFSG.Quasithin.H13.KG838.isPGroup_outer_psl_two_prime
      (LieModel.statedClassicalModel hp (by decide))) hm hα
  · obtain ⟨x, hx⟩ := (kJ1_holds T hJ).2.2 α
    exact ⟨x, hx.symm⟩

theorem uc22s13e_perfect_of_equiv {T W : Type*} [Group T] [Finite T] [Group W] [Nontrivial W]
    [Group.IsPerfect W] {F : Subgroup T} (E : ↥F ≃* W) :
    ⁅F, F⁆ = F ∧ ∃ z ∈ F, ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf z = q := by
  haveI : Group.IsPerfect ↥F :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  haveI : Nontrivial ↥F := E.symm.injective.nontrivial
  obtain ⟨z, q, hq, hq2, hz⟩ := uc22s13d_exists_odd_prime (F := ↥F)
  exact ⟨Subgroup.isPerfect_iff.1 inferInstance, z, z.2, q, hq, hq2,
    by rw [Subgroup.orderOf_coe, hz]⟩

theorem uc22s13e_witness_of_equiv {T W : Type*} [Group T] [Group W] {F : Subgroup T}
    (E : ↥F ≃* W) {z₀ t₀ : W} {k q : ℕ} (ht : t₀ ^ (2 ^ k) = 1) (hq : q.Prime) (hq2 : q ≠ 2)
    (hc : orderOf ⁅z₀, t₀⁆ = q) :
    ∃ z ∈ F, ∃ t ∈ F, (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf ⁅z, t⁆ = q := by
  refine ⟨E.symm z₀, (E.symm z₀).2, E.symm t₀, (E.symm t₀).2, ⟨k, ?_⟩, q, hq, hq2, ?_⟩
  · have h1 : E.symm t₀ ^ (2 ^ k) = 1 := by rw [← map_pow, ht, map_one]
    simpa using congrArg (fun x : ↥F => (x : T)) h1
  · have h1 : ((E.symm ⁅z₀, t₀⁆ : ↥F) : T) = ⁅(E.symm z₀ : T), (E.symm t₀ : T)⁆ := by
      rw [map_commutatorElement]
      simp [commutatorElement_def]
    rw [← h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc]

theorem uc22s13e_fix {T : Type} [Group T] [Finite T] {a : ℕ}
    (hT : IsL2 T a ∨ IsSz T a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {α : MulAut T}
    (hord : orderOf α = r) (hinn : α ∉ (MulAut.conj : T →* MulAut T).range) :
    (a ≠ r → ⁅fixSub α, fixSub α⁆ = fixSub α ∧
        ∃ z ∈ fixSub α, ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf z = q) ∧
      (a = r → ∃ z ∈ fixSub α, ∃ t ∈ fixSub α, (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf ⁅z, t⁆ = q) := by
  rcases hT with hL2 | hSz
  · obtain ⟨ha2, F, _, _, hF, _, ⟨e⟩⟩ := uc22p22g_isL2_psl hL2
    let ψ : T ≃* coordinateG F := e.trans (pslEquivCoordinateG F)
    obtain ⟨⟨m, hm⟩, k, hkcard, ⟨eX⟩⟩ :=
      psl_two_exists_fixSub_equiv hr hr2 (by omega) hF ψ hord hinn
    have hfm : a / r = m := by
      rw [hm]
      exact Nat.mul_div_cancel_left m hr.pos
    rw [hfm] at hkcard
    haveI : Fintype k := Fintype.ofFinite k
    haveI : CharP k 2 :=
      charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hkcard])
    refine ⟨fun har => ?_, fun har => ?_⟩
    · have hm2 : 2 ≤ m := by
        by_contra hlt
        interval_cases m <;> omega
      have h4k : 4 ≤ Nat.card k := by
        rw [hkcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      haveI := CFSG.RankThree.PartOne.KCRootAxis.sl2_isPerfect h4k
      haveI := (CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup h4k).toNontrivial
      exact uc22s13e_perfect_of_equiv (eX.trans ((pslEquivCoordinateG k).symm.trans
        (CFSG.RankThree.PartOne.KCRootAxis.slEquivPSL k).symm))
    · have hm1 : m = 1 := by
        have h1 : r * m = r * 1 := by rw [← hm, har, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hr.pos h1
      subst hm1
      obtain ⟨e3⟩ := CFSG.BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two (K := ↥k)
        (by rw [hkcard, pow_one])
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact uc22s13e_witness_of_equiv (eX.trans ((pslEquivCoordinateG k).symm.trans e3))
        (z₀ := Equiv.swap (0 : Fin 3) 1) (t₀ := Equiv.swap (1 : Fin 3) 2) (k := 1) (by decide)
        Nat.prime_three (by norm_num) (orderOf_eq_prime (by decide) (by decide))
  · obtain ⟨-, -, b₀, hb₀, K, _, _, rfl, hK, ⟨e⟩⟩ := LieModel.suzukiModel hSz
    obtain ⟨b, k, _, _, β, ψ, hbr, hkcard, hψ, ⟨efix⟩⟩ :=
      sz_coset_data hb₀ hK e hr hr2 hord hinn
    have hψ' : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β := by rw [hψ]
    let E : ↥(fixSub α) ≃* suzukiGroup b k :=
      (((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
        (MulEquiv.subgroupCongr hψ')).trans efix
    refine ⟨fun har => ?_, fun har => ?_⟩
    · have hb : 1 ≤ b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · subst h
          omega
        · exact h
      haveI := (CFSG.LieType.Ree.suzuki_perfect hb hkcard).2
      haveI := (CFSG.LieType.Ree.suzuki_simple hb hkcard).2.1
      exact uc22s13e_perfect_of_equiv E
    · have hb0 : b = 0 := by
        have h1 : (2 * b + 1) * r = 1 * r := by rw [hbr, one_mul, har]
        have h2 := Nat.eq_of_mul_eq_mul_right hr.pos h1
        omega
      subst hb0
      have hk2 : Nat.card k = 2 := by
        rw [hkcard]
        norm_num
      obtain ⟨h20, P, hPn, hP5, hPC, -⟩ :=
        CFSG.LieType.Ree.suzuki_two_normal_five_complement_core_trivial hk2
      haveI : Finite (suzukiGroup 0 k) := CFSG.LieType.Ree.finite_suzukiGroup hkcard
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := suzukiGroup 0 k) 2
        (by rw [h20]; norm_num)
      have ht₀P : t₀ ∉ centralizer (P : Set (suzukiGroup 0 k)) := by
        rw [hPC]
        intro h
        have h1 := Subgroup.orderOf_dvd_natCard P h
        rw [ht₀, hP5] at h1
        norm_num at h1
      obtain ⟨z₀, hz₀P, hz₀t⟩ : ∃ z₀ ∈ P, z₀ * t₀ ≠ t₀ * z₀ := by
        by_contra h
        exact ht₀P (mem_centralizer_iff.2 fun z hz => by_contra fun hne => h ⟨z, hz, hne⟩)
      have hcP : ⁅z₀, t₀⁆ ∈ P := by
        have h1 : ⁅z₀, t₀⁆ = z₀ * (t₀ * z₀⁻¹ * t₀⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [h1]
        exact P.mul_mem hz₀P (hPn.conj_mem _ (P.inv_mem hz₀P) t₀)
      have hc1 : ⁅z₀, t₀⁆ ≠ 1 := fun h => hz₀t (commutatorElement_eq_one_iff_mul_comm.1 h)
      have hc5 : orderOf ⁅z₀, t₀⁆ = 5 := by
        have h1 := Subgroup.orderOf_dvd_natCard P hcP
        rw [hP5] at h1
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h1 with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hc1
        · exact h
      have ht₀2 : t₀ ^ (2 ^ 1) = 1 := by rw [pow_one, ← ht₀, pow_orderOf_eq_one]
      exact uc22s13e_witness_of_equiv E ht₀2 (by norm_num) (by norm_num) hc5

end CFSG.LocalAnalysis.UniquenessCase.UC22
