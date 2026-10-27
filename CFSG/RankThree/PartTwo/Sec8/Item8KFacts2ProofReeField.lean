module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCore
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
public import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LieType.Ree
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G}

theorem exists_quotEquiv_imageModTheta (hKL : K ≤ L)
    (hθ : ∀ N : Subgroup (imageModTheta L K), N.Normal → Group.IsSolvable N →
      ¬ 3 ∣ Nat.card N → N = ⊥) :
    ∃ χ : K ⧸ aschbacherSolvableCore 3 K ≃* imageModTheta L K,
      ∀ k : K, (χ (k : K ⧸ aschbacherSolvableCore 3 K) : L ⧸ aschbacherSolvableCore 3 L) =
        ((Subgroup.inclusion hKL k : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set τ := Item87Res2Proof.toQuot hKL with hτ
  have hτS : ∀ k : K, τ k ∈ Sec8.imageModTheta L K := fun k => by
    rw [← Item87Res2Proof.range_toQuot hKL]
    exact ⟨k, rfl⟩
  set ρ : K →* Sec8.imageModTheta L K := τ.codRestrict _ hτS with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← Item87Res2Proof.range_toQuot hKL] at hq
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, rfl⟩
  have hkerρ : ρ.ker = τ.ker := by
    ext k
    simp only [MonoidHom.mem_ker, hρ, MonoidHom.codRestrict_apply]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 K).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := hθ M hMn hMs hM3
  have hker : ρ.ker = aschbacherSolvableCore 3 K := by
    refine le_antisymm (hkerρ ▸ Item87Res2Proof.ker_toQuot_le hKL) ?_
    intro k hk
    rw [MonoidHom.mem_ker]
    have : ρ k ∈ M := Subgroup.mem_map_of_mem ρ hk
    rwa [hM1, Subgroup.mem_bot] at this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs), fun k => rfl⟩


theorem inducesStdKind_field_of_ree {a : G} (hKL : K ≤ L)
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) {k : ℕ} (hk : 1 ≤ k) {Kf : Type} [Field Kf]
    [Finite Kf] [CharP Kf ReeTag.F4.prime] (hKf : Nat.card Kf = 2 ^ (2 * k + 1))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* ReeTag.F4.reeGamma Kf k)
    (hKbar : Sec8.IsoSUThree (Sec8.imageModTheta L K) (2 ^ (2 * k + 1))) :
    KFacts.InducesStdKind K a .field := by
  classical
  set α := thetaQuotMulAut L (compAction L ⟨a, haL⟩) with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, ← map_pow]
    have : (⟨a, haL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa)
    rw [this, map_one, map_one]
  have hα1 : α ≠ 1 := by
    obtain ⟨hN, hnot⟩ := hout
    intro h1
    apply hnot
    rw [show (⟨a, hN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, haL⟩ from rfl, ← hαdef, h1]
    exact ⟨1, map_one _⟩
  obtain ⟨b, k', _, _, _, hk', ⟨φ₀⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk hKf e ha3 hout
  have hfixeq : Sec8.barCentralizer (Subgroup.zpowers a) L = Sec4.autFix α :=
    Sec4.barCentralizer_zpowers_eq_autFix haL
  set φ : Sec4.autFix α ≃* ReeTag.F4.reeGamma k' b :=
    (MulEquiv.subgroupCongr hfixeq.symm).trans φ₀ with hφ
  set S := Sec8.imageModTheta L K with hS
  have hSinv : ∀ s ∈ S, α s ∈ S := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨compAction L ⟨a, haL⟩ x, ?_, rfl⟩
    have hx' : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    show a * (x : G) * a⁻¹ ∈ K
    exact (Subgroup.mem_normalizer_iff.mp haK _).mp hx'
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := hKbar
  obtain ⟨⟨s, hsS, hsα⟩, u, huS, hαu, hu4, hu2⟩ :=
    exists_fixed_pow_four_of_ree hk hKf e hα3 hα1 hk' φ hSinv hF ψ
  have hU : UnitaryFieldData 2 (2 * k + 1) F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hθ : ∀ N : Subgroup S, N.Normal → Group.IsSolvable N → ¬ 3 ∣ Nat.card N → N = ⊥ :=
    Item87Proof.NoThetaNormal.of_mulEquiv ψ (Item87Proof.noThetaNormal_statedSU hF (by omega))
  obtain ⟨χ, hχ⟩ := exists_quotEquiv_imageModTheta hKL hθ
  set β := thetaQuotMulAut K (compAction K ⟨a, haK⟩) with hβdef
  have hequiv : ∀ y, (χ (β y) : L ⧸ aschbacherSolvableCore 3 L) = α (χ y) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [hβdef, Sec4.thetaQuotMulAut_mk, hχ, hχ, hαdef, Sec4.thetaQuotMulAut_mk]
      rfl
  set eK : K ⧸ aschbacherSolvableCore 3 K ≃* unitarySU 2 (2 * k + 1) F 3 := χ.trans ψ with heK
  set β' := KFacts.inducedAutHom K eK ⟨a, haK⟩ with hβ'
  have hβ'3 : β' ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one K eK haK ha3
  have hβ'1 : β' ≠ 1 := by
    intro h1
    apply hsα
    have hβ1 : β = 1 := by
      have h2 : MulAut.congr eK β = 1 := h1
      rwa [MulEquiv.map_eq_one_iff] at h2
    set y := χ.symm ⟨s, hsS⟩
    have h3 := hequiv y
    rw [hβ1, MulAut.one_apply, MulEquiv.apply_symm_apply] at h3
    exact h3.symm
  set y := χ.symm ⟨u, huS⟩ with hy
  have hβy : β y = y := by
    apply χ.injective
    apply Subtype.ext
    rw [hequiv, hy, MulEquiv.apply_symm_apply]
    exact hαu
  set u' := eK y with hu'
  have hβ'u : β' u' = u' := by
    rw [hβ', KFacts.inducedAutHom_apply]
    show eK (β (eK.symm u')) = u'
    rw [hu', MulEquiv.symm_apply_apply, hβy]
  have huS4 : (⟨u, huS⟩ : S) ^ 4 = 1 := Subtype.ext (by simpa using hu4)
  have huS2 : (⟨u, huS⟩ : S) ^ 2 ≠ 1 := fun h1 => hu2 (by simpa using congrArg Subtype.val h1)
  have hu'4 : u' ^ 4 = 1 := by
    rw [hu', hy, heK, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, ← map_pow, huS4,
      map_one]
  have hu'2 : u' ^ 2 ≠ 1 := by
    intro h1
    apply huS2
    rw [hu', hy, heK, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, ← map_pow] at h1
    exact (MulEquiv.map_eq_one_iff ψ).mp h1
  have hq : 2 < 2 ^ (2 * k + 1) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 2 * k + 1))
  have hfield := hasKind_field_of_fixed_order_four hU (odd_two_mul_add_one k) hq hβ'3 hβ'1
    hβ'u hu'4 hu'2
  exact .su3 hU hq ⟨eK, haK, hfield⟩

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
