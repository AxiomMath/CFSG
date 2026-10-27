module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

theorem tup_sq {L : Type} [Field L] {ζ : Lˣ} (hζ3 : ζ ^ 3 = 1) (β : Exp3) :
    tup (ζ ^ 2) β = tup ζ (fun i => 2 * β i) := by
  rw [tup_two_mul hζ3]
  funext i
  simp only [tup, Pi.pow_apply]
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem twistHom_tup {L : Type}
    [Field L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : q % 3 = 1 ∨ q % 3 = 2)
    {ζ : Lˣ} (hζ3 : ζ ^ 3 = 1) (γ : Exp3) :
    twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (tup ζ γ)) =
        rootDiagUnit TwistTag.D4.tag (tup ζ (rhoExp γ)) ∨
      twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (tup ζ γ)) =
        rootDiagUnit TwistTag.D4.tag (tup ζ (fun i => 2 * rhoExp γ i)) := by
  rw [twistHom_rootDiagUnit_eq]
  have hFζ : Units.map Fr.toMonoidHom ζ = ζ ^ q := Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hFr _)
  have e : (fun i => Units.map Fr.toMonoidHom (tup ζ γ (TwistTag.D4.perm.symm i))) =
      tup (ζ ^ q) (rhoExp γ) := by
    funext i
    simp only [tup, rhoExp, map_pow, hFζ]
  rw [e, pow_eq_pow_mod q hζ3]
  rcases hq with h | h
  · left
    rw [h, pow_one]
  · right
    rw [h, tup_sq hζ3]


theorem exists_conj_dA_or_dB {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {z : ModGL TwistTag.D4.tag K} (hz : z ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ (ζ : Lˣ) (x : ModGL TwistTag.D4.tag L), orderOf ζ = 3 ∧
      x ∈ adjointGroup TwistTag.D4.tag L ∧
      (baseChangeGL (algebraMap K L) z = x * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * x⁻¹ ∨
        baseChangeGL (algebraMap K L) z = x * rootDiagUnit TwistTag.D4.tag (tup ζ gB) * x⁻¹) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  obtain ⟨ζ, g, hζ, hg, hcomm⟩ := exists_conj_commute_tup_gA2 hf hℓ3 hK hσ L hz hz3
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  set zL := baseChangeGL (algebraMap K L) z with hzL
  obtain ⟨hzC, hzF⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1
    (graphFixedRootGroup_le _ _ _ hz)
  have hzLC : zL ∈ adjointGroup TwistTag.D4.tag L :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hzC
  have hzL3 : zL ^ 3 = 1 := by rw [hzL, ← map_pow, hz3, map_one]
  have hzL1 : zL ≠ 1 := fun h =>
    hz1 (baseChangeGL_injective (algebraMap K L) (h.trans (map_one _).symm))
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [1, 2, 3, 2, 1]) with hn
  have hnC : n ∈ adjointGroup TwistTag.D4.tag L := canonicalRep_mem_adjointGroup _ L _
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gA2) =
      n⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * n := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [1, 2, 3, 2, 1] gA2,
      show wordExp [1, 2, 3, 2, 1] gA2 = gA by decide]
  set Y := g * zL * g⁻¹ with hY
  set Y' := n * Y * n⁻¹ with hY'
  have hY'C : Y' ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem hnC (mul_mem (mul_mem hg hzLC) (inv_mem hg))) (inv_mem hnC)
  have hY'3 : Y' ^ 3 = 1 := by
    rw [hY', conj_pow, hY, conj_pow, hzL3]
    group
  have hY'cent : Y' ∈ graphCentralizer TwistTag.D4.tag L
      (rootDiagUnit TwistTag.D4.tag (tup ζ gA)) := by
    refine Subgroup.mem_inf.2 ⟨hY'C, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : Y * (n⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * n) =
        n⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * n * Y := by
      rw [← hd]
      exact hcomm
    calc Y' * rootDiagUnit TwistTag.D4.tag (tup ζ gA) =
        n * (Y * (n⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * n)) * n⁻¹ := by
          rw [hY']
          group
      _ = n * (n⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * n * Y) * n⁻¹ := by rw [h1]
      _ = rootDiagUnit TwistTag.D4.tag (tup ζ gA) * Y' := by
          rw [hY']
          group
  obtain ⟨g', hg', hT⟩ := exists_conj_torus_of_cent_gA hζ hY'cent hY'3
  obtain ⟨X, hX⟩ : ∃ X : ModGL TwistTag.D4.tag L, X = g' * n * g := ⟨_, rfl⟩
  have hXC : X ∈ adjointGroup TwistTag.D4.tag L := hX ▸ mul_mem (mul_mem hg' hnC) hg
  have ht : X * zL * X⁻¹ = g' * Y' * g'⁻¹ := by
    rw [hX, hY', hY]
    group
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hl3 : rootDiagUnit TwistTag.D4.tag l ^ 3 = 1 := by
    rw [← hl, conj_pow, hY'3]
    group
  obtain ⟨γ, rfl⟩ := exists_tup_of_rootDiagUnit_pow hζ hl3
  have htX : rootDiagUnit TwistTag.D4.tag (tup ζ γ) = X * zL * X⁻¹ := by rw [ht, hl]
  have hzLeq : zL = X⁻¹ * rootDiagUnit TwistTag.D4.tag (tup ζ γ) * X := by
    rw [htX]
    group
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    apply hzL1
    have h0 : tup ζ 0 = 1 := by
      funext i
      simp [tup]
    rw [hzLeq, h0, rootDiagUnit_one]
    group
  have hcommFr : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    refine RingHom.ext fun c => ?_
    change algebraMap K L (σ c) = Fr (algebraMap K L c)
    rw [hσ, hFr, map_pow]
  have hFz : twistHom TwistTag.D4 L Fr zL = zL := by
    rw [hzL, twistHom_baseChangeGL (algebraMap K L) hcommFr, hzF]
  have hFX : twistHom TwistTag.D4 L Fr X ∈ adjointGroup TwistTag.D4.tag L :=
    twistHom_mem_adjointGroup TwistTag.D4 L Fr hXC
  have hconj : X * (twistHom TwistTag.D4 L Fr X)⁻¹ *
      twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (tup ζ γ)) *
        (X * (twistHom TwistTag.D4 L Fr X)⁻¹)⁻¹ = rootDiagUnit TwistTag.D4.tag (tup ζ γ) := by
    have hFt : twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (tup ζ γ)) =
        twistHom TwistTag.D4 L Fr X * zL * (twistHom TwistTag.D4 L Fr X)⁻¹ := by
      rw [htX, map_mul, map_mul, map_inv, hFz]
    rw [hFt, htX]
    group
  have hXF : X * (twistHom TwistTag.D4 L Fr X)⁻¹ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem hXC (inv_mem hFX)
  have hq3 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
    have : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
    omega
  have hw : ∃ w : WeylGroup TwistTag.D4.tag,
      weylTuple w (tup ζ (rhoExp γ)) = tup ζ γ ∨
        weylTuple w (tup ζ (fun i => 2 * rhoExp γ i)) = tup ζ γ := by
    rcases twistHom_tup hFr hq3 hζ3 γ with h | h
    · rw [h] at hconj
      obtain ⟨w, hw⟩ := exists_weyl_of_conj_rootDiagUnit (rootDiagUnit_mem_torusGroup _)
        (rootDiagUnit_mem_torusGroup _) hXF hconj
      exact ⟨w, Or.inl hw⟩
    · rw [h] at hconj
      obtain ⟨w, hw⟩ := exists_weyl_of_conj_rootDiagUnit (rootDiagUnit_mem_torusGroup _)
        (rootDiagUnit_mem_torusGroup _) hXF hconj
      exact ⟨w, Or.inr hw⟩
  obtain ⟨w, hw⟩ := hw
  obtain ⟨ω, hω⟩ := exists_word_of_rho hζ hγ0 hw
  have htconj := rootDiagUnit_tup_eq_conj (L := L) hζ3 ω γ
  set m := canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd ω) with hm
  have hmC : m ∈ adjointGroup TwistTag.D4.tag L := canonicalRep_mem_adjointGroup _ L _
  refine ⟨ζ, X⁻¹ * m⁻¹, hζ, mul_mem (inv_mem hXC) (inv_mem hmC), ?_⟩
  rcases hω with h | h
  · left
    rw [hzLeq, htconj, h]
    group
  · right
    rw [hzLeq, htconj, h]
    group

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
