module

public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofHJInner
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofEps
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes148

open Res148 Main148

omit [Finite G] in
theorem pow_conj_mul_inv_mem {K N : Subgroup G} {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (h : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ N) :
    ∀ n : ℕ, ∀ k ∈ K, b ^ n * k * (b ^ n)⁻¹ * k⁻¹ ∈ N := by
  intro n
  induction n with
  | zero => intro k _; simp
  | succ n ih =>
    intro k hk
    have hk' : b ^ n * k * (b ^ n)⁻¹ ∈ K := by
      have hpow : b ^ n ∈ Subgroup.normalizer (K : Set G) := pow_mem hbK n
      exact (Subgroup.mem_normalizer_iff.mp hpow k).mp hk
    have h1 := h _ hk'
    have e : b ^ (n + 1) * k * (b ^ (n + 1))⁻¹ * k⁻¹ =
        (b * (b ^ n * k * (b ^ n)⁻¹) * b⁻¹ * (b ^ n * k * (b ^ n)⁻¹)⁻¹) *
          (b ^ n * k * (b ^ n)⁻¹ * k⁻¹) := by
      rw [pow_succ']
      group
    rw [e]
    exact N.mul_mem h1 (ih k hk)

theorem nonempty_theta_quot_equiv_of_mem_sectionCentralizer {Y B YB Yd : Subgroup G} {b d : G}
    (hb3 : b ^ 3 = 1) (hCB : Subgroup.centralizer (B : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G))
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (h3YB : 3 ∣ Nat.card YB)
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hbYd : b ∈ Subgroup.normalizer (Yd : Set G))
    (hbc : ∀ y ∈ Yd, b * y * b⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Yd) :
    Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* ↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) := by
  set θd := inSubgroup (aschbacherSolvableCore 3) Yd with hθd
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Yd) with hπ
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Yd) Nat.prime_three
  have hθdYd : θd ≤ Yd := Subgroup.map_subtype_le _
  have hθd3 : Nat.Coprime 3 (Nat.card θd) := by
    rw [hθd, inSubgroup, Subgroup.card_map_of_injective Yd.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hbθ : b ∈ Subgroup.normalizer (θd : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _ hbYd
  have hYdYC : Yd ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) := le_of_mem_thetaComponentsIn hYd
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYdp : Group.IsPerfect Yd := isPerfect_of_mem_thetaComponentsIn hYd
  have hYdq : IsQuasisimple (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd
  have hYBp : Group.IsPerfect YB := isPerfect_of_mem_thetaComponentsIn hYB
  have hYBq : IsQuasisimple (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB
  set D := Yd ⊓ Subgroup.centralizer ({b} : Set G) with hD
  have hDYd : D ≤ Yd := inf_le_left
  set ρ : ↥D →* ↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd := π.comp (Subgroup.inclusion hDYd) with hρ
  have hB3 : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_three_of_pow148 fun x hx => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hBN : Subgroup.zpowers b ≤ Subgroup.normalizer (θd : Set G) :=
    Subgroup.zpowers_le.mpr hbθ
  have hpow := pow_conj_mul_inv_mem hbYd hbc
  have hρs : Function.Surjective ρ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥Yd) q
    have hk : ∀ x ∈ Subgroup.zpowers b, (y : G)⁻¹ * (x * y * x⁻¹) ∈ θd := by
      intro x hx
      obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hx)
      have h1 := hpow n y y.2
      have h2 : ((y : G)⁻¹ * (b ^ n * y * (b ^ n)⁻¹ * (y : G)⁻¹)) * (y : G) ∈ θd := by
        have hyθ : (y : G) ∈ Subgroup.normalizer (θd : Set G) :=
          (Subgroup.le_normalizer.trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) y.2
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyθ) _).mp h1
        simpa [mul_assoc] using this
      have e : (y : G)⁻¹ * (b ^ n * y * (b ^ n)⁻¹) =
          ((y : G)⁻¹ * (b ^ n * y * (b ^ n)⁻¹ * (y : G)⁻¹)) * (y : G) := by group
      rw [e]
      exact h2
    obtain ⟨y', hy', hy'c⟩ := exists_commute_mem_coset148 hB3 hθd3 hBN hk
    have hy'Yd : y' ∈ Yd := by
      have := Yd.mul_mem y.2 (hθdYd hy')
      rwa [mul_inv_cancel_left] at this
    have hy'b : y' ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hy'c b (Subgroup.mem_zpowers b)).symm
    have hy'D : y' ∈ D := Subgroup.mem_inf.mpr ⟨hy'Yd, hy'b⟩
    refine ⟨⟨y', hy'D⟩, ?_⟩
    rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    obtain ⟨t, ht, hty⟩ := hy'
    have hty' : (t : G) = (y : G)⁻¹ * y' := hty
    have : (Subgroup.inclusion hDYd ⟨y', hy'D⟩)⁻¹ * y = t⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hty', mul_inv_rev,
        inv_inv]
    rw [this]
    exact inv_mem ht
  have hYBD : YB ≤ D := le_inf hYBYd (hYBC.trans (inf_le_right.trans (hCB ▸ inf_le_left)))
  have hDC : D ≤ Y ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_inf (hDYd.trans (hYdYC.trans inf_le_left)) ?_
    rw [hCB]
    exact le_inf inf_le_right (hDYd.trans (hYdYC.trans inf_le_right))
  have hYBsubD : (YB.subgroupOf D).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hYB).2.2.1
    have h2 := h1.comap (Subgroup.inclusion hDC)
    have heq : (YB.subgroupOf (Y ⊓ Subgroup.centralizer (B : Set G))).comap
        (Subgroup.inclusion hDC) = YB.subgroupOf D := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  set ψ : ↥YB →* ↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd := π.comp (Subgroup.inclusion hYBYd)
    with hψ
  have hψrange : ψ.range = (YB.subgroupOf D).map ρ := by
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y, hYBD y.2⟩, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hsn : ψ.range.IsSubnormal := by
    rw [hψrange]
    exact hYBsubD.map (f := ρ) hρs
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    intro h3
    apply hθ3
    refine h3.trans ?_
    have hle : ψ.ker.map (Subgroup.inclusion hYBYd) ≤ aschbacherSolvableCore 3 ↥Yd := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : ψ y = 1 := hy
      rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
      exact hy'
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYBYd)]
    exact Subgroup.card_dvd_of_le hle
  have hrange1 : Nontrivial ψ.range := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hker3
    have htop : ψ.ker = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have : (⟨ψ y, y, rfl⟩ : ψ.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val this
    rw [htop, Subgroup.card_top]
    exact h3YB
  have hrangep : Group.IsPerfect ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hψtop : ψ.range = ⊤ := by
    rcases eq_top_or_le_center_of_isSubnormal hYdq hsn with htop | hcen
    · exact htop
    · exfalso
      have hcomm : ∀ a b : ↥ψ.range, a * b = b * a := by
        intro a b
        exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcen b.2)) a)
      exact Group.IsPerfect.not_isSolvable ↥ψ.range (Group.isSolvable_of_comm hcomm)
  have hψs : Function.Surjective ψ := MonoidHom.range_eq_top.mp hψtop
  have hYdQp : Group.IsPerfect (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) := hYdq.1
  have hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 ↥YB := by
    rcases ker_le_theta_or_subsingleton ψ hψs hYdQp hYBq hker3 with hle | hsub
    · exact hle
    · exfalso
      have : Nontrivial (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) :=
        CFSG.LocalCores.isQuasisimple_nontrivial hYdq
      exact not_subsingleton_iff_nontrivial.mpr this hsub
  obtain ⟨-, ⟨η⟩⟩ := theta_quot_of_ker_le ψ hψs hkerθ hker3
  have hθQ : aschbacherSolvableCore 3 (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = ⊥ :=
    (CFSG.RankThree.theta_quotient_core_and_ranks (G := ↥Yd)).1
  exact ⟨η.trans ((QuotientGroup.quotientMulEquivOfEq hθQ).trans QuotientGroup.quotientBot)⟩

end HJRes148

open HJRes148 Main148

section Certificates

@[expose] def Step148HJTypeYdOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        b ∉ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
      ∀ J ∈ thetaComponentsIn Y, Yd ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        YdType148 d Yd

theorem step148HJTypeYd_of_outer (hO : Step148HJTypeYdOuter) : Step148HJTypeYd := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd J hJ
    hYdJ hAJ
  by_cases hbc : b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd)
  swap
  · exact hO G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd hbc J
      hJ hYdJ hAJ
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨hbB, -, -, -, hCB⟩ := lbConfig_points hB hA.2 hc
  have hb : b ∈ A := hB.1 hbB
  have hb3 : b ^ 3 = 1 := hA.1.2 b hb
  have h3YB : 3 ∣ Nat.card YB := by
    rcases htype with hA6 | hA5
    · exact three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))
    · exact three_dvd_card_of_ydType148 (d := d) (Or.inl hA5)
  obtain ⟨η⟩ := nonempty_theta_quot_equiv_of_mem_sectionCentralizer hb3 hCB hYB h3YB hYd hYBYd
    (hAYd hb) hbc.2
  rcases htype with hA6 | ⟨⟨φ⟩⟩
  · exact Or.inr (Or.inl (KFacts.KS14.isTripleCover_congr η hA6))
  · exact Or.inl ⟨η.symm.trans φ⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec14
