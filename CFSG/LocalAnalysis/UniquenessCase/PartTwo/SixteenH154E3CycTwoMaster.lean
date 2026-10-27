module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoHline
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCoreB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoIdx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoSelf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABBAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

theorem s16h_e3_CycTwoMaster
    [Finite X] [Finite (MulAut X)]
    (F : s16h_CycFrame Mb ψ z U) {u₀ : X} (hu₀ : u₀ ∈ U) (hu₁ : u₀ ≠ 1)
    (hK : ∀ R : Subgroup (MulAut X), R ≤ Mb → IsElemAbelian 3 R →
      (∀ r ∈ R, r u₀ = u₀) → Nat.card ↥R ≤ 3)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (autSub (s16h_CycN Mb z) U)) :
    ∃ P : Subgroup (MulAut X), P ≤ Mb ∧ Mb ≤ Subgroup.normalizer (P : Set (MulAut X)) ∧
      ¬ 3 ∣ P.relIndex Mb ∧ IsPGroup 3 P ∧ IsElemAbelianOfRank 3 3 ↥P ∧
      Subgroup.centralizer (P : Set (MulAut X)) ⊓ Mb ≤ P := by
  classical
  let z₁ : MulAut ↥U := F.rho ⟨z, F.z_mem_N⟩
  have hexpU : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by
    simpa using F.exp2 (w : X))
  have hcardU : Nat.card ↥U = 2 ^ 4 := F.card_u
  have hz₁A : z₁ ∈ autSub (s16h_CycN Mb z) U := by
    rw [← F.rho_range]
    exact MonoidHom.mem_range.2 ⟨⟨z, F.z_mem_N⟩, rfl⟩
  have hz₁_pow : z₁ ^ 3 = 1 := by
    have hz3 : z ^ 3 = 1 := by rw [← F.z_ord]; exact pow_orderOf_eq_one z
    have hzN3 : (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    change (F.rho ⟨z, F.z_mem_N⟩) ^ 3 = 1
    rw [← map_pow, hzN3, map_one]
  have hz₁_ne : z₁ ≠ 1 := by
    intro h1
    have hnt : Nontrivial ↥U := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardU]
      norm_num
    obtain ⟨u, hu⟩ := exists_ne (1 : ↥U)
    have hfix : z (u : X) = (u : X) := by
      have h := F.fix_of_rho_eq_one (n := ⟨z, F.z_mem_N⟩) h1 (u : X) u.2
      simpa using h
    exact hu (Subtype.ext (F.z_fpf (u : X) u.2 hfix))
  have hzord₁ : orderOf z₁ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hz₁_pow hz₁_ne
  have hfpf₁ : ∀ w : ↥U, z₁ w = w → w = 1 := by
    intro w hw
    have h2' : z (w : X) = (w : X) := by
      have h := congrArg (fun v : ↥U => (v : X)) hw
      rw [F.rho_apply] at h
      exact h
    exact Subtype.ext (F.z_fpf (w : X) w.2 h2')
  have hAn : autSub (s16h_CycN Mb z) U ≤
      Subgroup.normalizer (Subgroup.zpowers z₁ : Set (MulAut ↥U)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha k hk
    rw [← F.rho_range] at ha
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hconjN : (n : MulAut X) * z * (n : MulAut X)⁻¹ ∈ Subgroup.zpowers z := by
      have hnorm : (n : MulAut X) ∈
          Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut X)) :=
        (inf_le_right : s16h_CycN Mb z ≤
          Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut X))) n.2
      exact (Subgroup.mem_normalizer_iff.1 hnorm z).mp (Subgroup.mem_zpowers z)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hconjN
    have hzpow : F.rho n * z₁ * (F.rho n)⁻¹ = z₁ ^ i := by
      have he : n * (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) * n⁻¹ =
          (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) ^ i := Subtype.ext (by
        show (n : MulAut X) * z * (n : MulAut X)⁻¹ = z ^ i
        exact hi.symm)
      have h1 : F.rho (n * (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) * n⁻¹) =
          F.rho n * z₁ * (F.rho n)⁻¹ := by
        simp only [map_mul, map_inv]
        rfl
      have h2 : F.rho (n * (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) * n⁻¹) = z₁ ^ i := by
        rw [he]
        exact map_zpow F.rho (⟨z, F.z_mem_N⟩ : ↥(s16h_CycN Mb z)) i
      exact h1.symm.trans h2
    have hconjpow : F.rho n * z₁ ^ j * (F.rho n)⁻¹ =
        (F.rho n * z₁ * (F.rho n)⁻¹) ^ j := by
      have h := map_zpow (MulAut.conj (F.rho n)) z₁ j
      rw [MulAut.conj_apply, MulAut.conj_apply] at h
      exact h
    rw [hconjpow, hzpow, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers z₁ (i * j)
  have hline : ∃ w : ↥U, w ≠ 1 ∧ ∀ b ∈ autSub (s16h_CycN Mb z) U, b ≠ 1 →
      orderOf b = 3 → b w = w → b ∈ Subgroup.zpowers z₁ := by
    refine ⟨⟨u₀, hu₀⟩, ?_, ?_⟩
    · intro h
      exact hu₁ (Subtype.ext_iff.mp h)
    · intro b hb hb1 hb3 hbw
      exact absurd hbw (s16h_e3_CycTwoHline_not_fixed F hu₀ hK h2 b hb hb1 hb3)
  obtain ⟨D, hDA, hDab, hDn, hzDle⟩ :=
    s16h_e3_CycTwoP3M4AA2AABBAA_normal_e9 hexpU hcardU hz₁A hzord₁ hfpf₁ hAn hline h2
  have hzD' : z₁ ∈ D := hzDle (Subgroup.mem_zpowers z₁)
  have hDcard : Nat.card ↥D = 9 := by
    obtain ⟨e⟩ := hDab
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
  have hDcomm : IsMulCommutative ↥D :=
    ⟨⟨fun a b => hDab.some.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)⟩⟩
  have hDpow : ∀ x ∈ D, x ^ 3 = 1 := by
    intro x hx
    have h3 : hDab.some ⟨x, hx⟩ ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have h4 : (⟨x, hx⟩ : ↥D) ^ 3 = 1 := by
      apply hDab.some.injective
      simp only [map_pow, map_one, h3]
    simpa using congrArg Subtype.val h4
  have hDe : IsElemAbelian 3 D := ⟨hDcomm, hDpow⟩
  have hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U,
      (∃ k : ℕ, orderOf a = 3 ^ k) → a ∈ D :=
    fun a ha h3 => s16h_e3_CycTwoExp3_mem_of_normal hexpU hcardU hDA hDab hDn ha h3
  have hreg : ∀ d ∈ D, d ≠ 1 → d ⟨u₀, hu₀⟩ ≠ ⟨u₀, hu₀⟩ := by
    intro d hd hd1 hdfix
    have hdA : d ∈ autSub (s16h_CycN Mb z) U := hDA hd
    have hd3 : orderOf d = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime (hDe.2 d hd) hd1
    exact s16h_e3_CycTwoHline_not_fixed F hu₀ hK h2 d hdA hd1 hd3 hdfix
  have hcent : ∀ c ∈ autSub (s16h_CycN Mb z) U,
      c ∈ Subgroup.centralizer (D : Set (MulAut ↥U)) → c ∈ D :=
    fun c _ hc => s16h_e3_CycTwoCent_centralizer_le hcardU hDcard hreg c hc
  have hP : IsElemAbelian 3 (F.core D) := s16h_e3_CycTwoCoreA_isElemAbelian F hDe
  have hcardP : Nat.card ↥(F.core D) = 27 :=
    s16h_e3_CycTwoCoreB_card F hDA hDe hDcard hzD' hSyl hu₀ hK
  refine ⟨F.core D, F.core_le D, F.core_normalizes D, ?_, ?_, ?_, ?_⟩
  · exact s16h_e3_CycTwoIdx_not_dvd Nat.prime_three (by norm_num) (F.core_le_N D) F.N_le
      F.idx (fun n hn h3 => s16h_e3_CycTwoCoreA_mem_of_three F hSyl hn h3)
  · exact CFSG.Open.IsElemAbelian.isPGroup hP
  · refine CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) (n := 3) ?_ ?_ ?_
    · intro a b
      exact hP.1.is_comm.comm a b
    · intro x
      exact Subtype.ext (hP.2 x x.2)
    · rw [hcardP]
      norm_num
  · exact s16h_e3_CycTwoSelf_centralizer_le F hDA hDe hzD' hSyl hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
