module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoInAlpha
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19ResProof

open TauCeti CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section Cover

variable {X : Type} [Group X]

theorem closure_fixSet_eq_top_of_cover {D : Subgroup (MulAut X)}
    (hgen : Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x * x⁻¹ ∈ Subgroup.center X} = ⊤)
    (hcov : ∀ φ ∈ D, φ ≠ 1 → ∀ x : X, φ x * x⁻¹ ∈ Subgroup.center X →
      ∃ t ∈ Subgroup.closure (fixSet D), φ t * t⁻¹ = φ x * x⁻¹) :
    Subgroup.closure (fixSet D) = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro x ⟨φ, hφ, hφ1, hx⟩
  obtain ⟨t, ht, htx⟩ := hcov φ hφ hφ1 x hx
  have hxt : x * t⁻¹ ∈ fixSet D := by
    refine ⟨φ, hφ, hφ1, ?_⟩
    have hz := Subgroup.mem_center_iff.mp hx
    have h1 : φ x = (φ x * x⁻¹) * x := by group
    have h2 : φ t = (φ x * x⁻¹) * t := by rw [← htx]; group
    rw [map_mul, map_inv, h1, h2]
    have h3 : (φ x * x⁻¹) * x * ((φ x * x⁻¹) * t)⁻¹ = (φ x * x⁻¹) * (x * t⁻¹) *
        (φ x * x⁻¹)⁻¹ := by group
    rw [h3, ← hz (x * t⁻¹)]
    group
  have h := Subgroup.mul_mem _ (Subgroup.subset_closure hxt) ht
  simpa using h

theorem closure_fixSet_of_inner [Finite X] (hZ3 : Nat.card (Subgroup.center X) = 3)
    (hgen : CFSG.AGLEmbedding.KGenTwoMod 3 X) {D : Subgroup (MulAut X)}
    (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hinn : D ≤ (MulAut.conj : X →* MulAut X).range)
    (hnfix : ∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) :
    Subgroup.closure (fixSet D) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup X := D.comap (MulAut.conj : X →* MulAut X) with hHdef
  have hZH : Subgroup.center X ≤ H := fun z hz => by
    rw [Subgroup.mem_comap]
    have : MulAut.conj z = 1 := by
      ext y
      simp [MulAut.conj_apply, (Subgroup.mem_center_iff.mp hz y).symm]
    rw [this]
    exact one_mem D
  have hker : (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
    ext z
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut X => φ y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * z = z * y * z⁻¹ * z := by rw [this]
        _ = z * y := by group
    · intro hz
      ext y
      simp [MulAut.conj_apply, (Subgroup.mem_center_iff.mp hz y).symm]
  obtain ⟨φ₀, hφ₀D, hφ₀1⟩ : ∃ φ ∈ D, φ ≠ 1 := by
    by_contra h
    push Not at h
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [this, Subgroup.card_bot] at hD9
    omega
  have hHfix : H ≤ Subgroup.closure (fixSet D) := by
    intro t ht
    by_cases h1 : MulAut.conj t = 1
    · apply Subgroup.subset_closure
      refine ⟨φ₀, hφ₀D, hφ₀1, ?_⟩
      obtain ⟨h₀, hh₀⟩ := hinn hφ₀D
      have htZ : t ∈ Subgroup.center X := hker ▸ h1
      rw [← hh₀, MulAut.conj_apply, Subgroup.mem_center_iff.mp htZ h₀]
      group
    · exact Subgroup.subset_closure ⟨MulAut.conj t, ht, h1, by simp [MulAut.conj_apply]⟩
  have hH27 : Nat.card H = 27 := by
    set f := (MulAut.conj : X →* MulAut X).domRestrict H with hf
    have hrange : f.range = D := by
      rw [hf, MonoidHom.domRestrict_range, Subgroup.map_comap_eq_self hinn]
    have hkerf : f.ker = (Subgroup.center X).subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      rfl
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hD9, hkerf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv, hZ3] at h1
    exact h1
  obtain ⟨e, heD, s, hs3, hsD, hes⟩ := hnfix
  obtain ⟨t₀, rfl⟩ := hinn heD
  have ht₀H : t₀ ∈ H := heD
  have hsH : s ∈ H := hsD
  have hst : t₀ * s ≠ s * t₀ := by
    intro h
    apply hes
    rw [MulAut.conj_apply, h]
    group
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X := by
    intro a ha b hb
    rw [← hker, MonoidHom.mem_ker]
    have h1 := hD.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩
    have h2 : MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a :=
      congrArg Subtype.val h1
    simp only [map_mul, map_inv]
    rw [h2]
    group
  have hZcenter : ∀ h ∈ H, h ∉ Subgroup.center X → ∃ t ∈ H, h * t ≠ t * h := by
    intro h hh hhZ
    by_contra hall
    push Not at hall
    apply hst
    set N : Subgroup H := (Subgroup.center X ⊔ Subgroup.zpowers h).subgroupOf H with hN
    have hNZ : N ≤ Subgroup.center H := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hx' : (x : X) ∈ Subgroup.center X ⊔ Subgroup.zpowers h := Subgroup.mem_subgroupOf.mp hx
      have hcent : (x : X) ∈ Subgroup.centralizer (H : Set X) := by
        have hle : Subgroup.center X ⊔ Subgroup.zpowers h ≤
            Subgroup.centralizer (H : Set X) := by
          refine sup_le (fun z hz => Subgroup.mem_centralizer_iff.mpr fun y _ =>
            (Subgroup.mem_center_iff.mp hz y)) ?_
          rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro y hy
          exact (hall y hy).symm
        exact hle hx'
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent y y.2)
    have hN9 : Nat.card N = 9 := by
      have hle : Subgroup.center X ⊔ Subgroup.zpowers h ≤ H :=
        sup_le hZH (Subgroup.zpowers_le.mpr hh)
      rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      have h1 : Nat.card (Subgroup.center X) ∣
          Nat.card (Subgroup.center X ⊔ Subgroup.zpowers h : Subgroup X) :=
        Subgroup.card_dvd_of_le le_sup_left
      have h2 : Nat.card (Subgroup.center X ⊔ Subgroup.zpowers h : Subgroup X) ∣ 27 :=
        hH27 ▸ Subgroup.card_dvd_of_le hle
      have h3 : Nat.card (Subgroup.center X ⊔ Subgroup.zpowers h : Subgroup X) ≠ 3 := by
        intro h3
        have heq : Subgroup.center X = Subgroup.center X ⊔ Subgroup.zpowers h :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hZ3])
        exact hhZ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers h))
      have h4 : Nat.card (Subgroup.center X ⊔ Subgroup.zpowers h : Subgroup X) ≠ 27 := by
        intro h4
        have heq : Subgroup.center X ⊔ Subgroup.zpowers h = H :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hH27])
        apply hst
        have ht₀' : (⟨t₀, ht₀H⟩ : H).1 ∈ Subgroup.center X ⊔ Subgroup.zpowers h := by
          rw [heq]
          exact ht₀H
        have hc1 := hNZ (Subgroup.mem_subgroupOf.mpr ht₀')
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hc1 ⟨s, hsH⟩).symm
      rw [hZ3] at h1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show _ ∣ 3 ^ 3 by norm_num; exact h2)
      interval_cases k
      · rw [hk'] at h1; norm_num at h1
      · exact absurd hk' h3
      · rw [hk']; norm_num
      · exact absurd hk' h4
    exact congrArg Subtype.val (commute_of_le_center hH27 hN9 hNZ ⟨t₀, ht₀H⟩ ⟨s, hsH⟩)
  refine closure_fixSet_eq_top_of_cover (hgen D hD (by rw [hD9]; norm_num)) ?_
  intro φ hφD hφ1 x hx
  obtain ⟨h, rfl⟩ := hinn hφD
  have hhH : h ∈ H := hφD
  have hhZ : h ∉ Subgroup.center X := fun hz => hφ1 (by rw [← hker] at hz; exact hz)
  set z := MulAut.conj h x * x⁻¹ with hz
  by_cases hz1 : z = 1
  · exact ⟨1, one_mem _, by rw [map_one, inv_one, mul_one, hz1]⟩
  obtain ⟨t, htH, hht⟩ := hZcenter h hhH hhZ
  set w := h * t * h⁻¹ * t⁻¹ with hw
  have hwZ : w ∈ Subgroup.center X := hcomm h hhH t htH
  have hw1 : w ≠ 1 := by
    intro h1
    apply hht
    calc h * t = w * t * h := by rw [hw]; group
      _ = t * h := by rw [h1, one_mul]
  have hZw : Subgroup.center X = Subgroup.zpowers w := by
    have hle : Subgroup.zpowers w ≤ Subgroup.center X := Subgroup.zpowers_le.mpr hwZ
    have hw3 : orderOf w = 3 := by
      have h1 : orderOf w ∣ 3 := by
        have := orderOf_dvd_natCard (⟨w, hwZ⟩ : Subgroup.center X)
        rwa [Subgroup.orderOf_mk, hZ3] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hw3, hZ3])).symm
  have hzZ : z ∈ Subgroup.zpowers w := hZw ▸ hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzZ
  refine ⟨t ^ k, Subgroup.zpow_mem _ (hHfix htH) k, ?_⟩
  have hwc : Commute w t := (Subgroup.mem_center_iff.mp hwZ t).symm
  have hct : MulAut.conj h t = w * t := by rw [MulAut.conj_apply, hw]; group
  rw [← hk, map_zpow, hct, hwc.mul_zpow k]
  group

end Cover

section Transport

@[expose] noncomputable def slCongr {K L : Type} [Field K] [Field L] (φ : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 3) K ≃* Matrix.SpecialLinearGroup (Fin 3) L :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map φ.toRingHom)
    (Matrix.SpecialLinearGroup.map φ.symm.toRingHom)
    (by
      ext g i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by
      ext g i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])

end Transport

end CFSG.RankThree.PartTwo.Sec19.Item19ResProof
