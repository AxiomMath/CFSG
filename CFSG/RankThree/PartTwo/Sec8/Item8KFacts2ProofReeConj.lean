module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2Proof
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.BRANCH
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.LargeReeOrder
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley ReeF4Conj2Proof
  CFSG.ClassicalGroups.UnitaryFlag


theorem orderThreeConj_reeGamma (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (y y' : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3)
    (hy' : orderOf y' = 3) : ∃ g : ReeTag.F4.reeGamma K a, g * y * g⁻¹ = y' := by
  classical
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  set L := AlgebraicClosure K with hL
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := L) hK
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ z : adjointGroup ReeTag.F4.tag L, ((D.F (D.F z) : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) z := by
    intro z
    rw [D.sq z]
    have hFr : D.Frq = iterateFrobenius L 2 (2 * a + 1) := by
      ext c
      rw [D.Frq_pow, hK, iterateFrobenius_def]
    rw [hFr]
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L wPhi2
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  set ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    (MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a) with hψ
  have hψapp : ∀ γ, ψ γ = g₀⁻¹ * thetaGamma L a γ * g₀ := by
    intro γ
    simp [hψ]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g₀⁻¹).injective.comp (thetaGamma_injective (K := K) L)
  have hψR : ∀ γ, ψ γ ∈ twistedFixed D.F n := by
    intro γ
    rw [hψapp]
    exact conj_mem_twistedFixed D.F hg₀adj hFg₀ (thetaGamma_mem_adjointGroup _ _)
      (D.fext_theta _)
  have hψsurj : ∀ u ∈ twistedFixed D.F n, ∃ γ, ψ γ = u := by
    intro u hu
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ hu
    obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
    refine ⟨γ, ?_⟩
    rw [hψapp, hγ]
    group
  have h3m : 3 ∣ mPhi2 a := three_dvd_mPhi2 a
  obtain ⟨ζm, hζm3, hζm⟩ := exists_pTors_elt (L := L) Nat.prime_three (by norm_num) h3m
  set ζ : Lˣ := (ζm : Lˣ) with hζdef
  have hζ : orderOf ζ = 3 := by
    refine orderOf_eq_prime hζm3 fun h1 => ?_
    have := hζm 1 (by rw [zpow_one]; exact h1)
    norm_num at this
  have hζ3 : ζ ^ 3 = 1 := hζm3
  obtain ⟨Φ, hΦinj, hΦ, -, hΦF⟩ := (torusParam_phi2 D.isFrob).param
  have hΦrange : Φ.range ≤ twistedFixed D.F n := by
    rintro _ ⟨z, rfl⟩
    exact hΦF z
  obtain ⟨T, hTmem, hTsurj, hTcard⟩ := exists_twisted_embedding D hg₀adj hFg₀ Φ.range hΦrange
  have hψT : ∀ γ, γ ∈ T ↔ ψ γ ∈ Φ.range := by
    intro γ
    rw [hTmem γ, hψapp]
  have hTcomm : ∀ x ∈ T, ∀ x' ∈ T, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨w, hw⟩ := (hψT x).1 hx
    obtain ⟨w', hw'⟩ := (hψT x').1 hx'
    apply hψinj
    rw [map_mul, map_mul, ← hw, ← hw', ← map_mul, ← map_mul, mul_comm]
  have hTm : Nat.card T = mPhi2 a ^ 2 := by
    rw [hTcard, card_range_of_odd (odd_mPhi2' a) Φ hΦinj]
  have horder := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1
  have hmod3 : (2 ^ (2 * a + 1)) % 3 = 2 := two_pow_odd_mod_three a
  have hQ2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hindex : ¬ 9 ∣ T.index := by
    have h1 := T.index_mul_card
    rw [hTm] at h1
    exact not_nine_dvd_ree_twisted hQ2 hmod3 (by
      rw [mPhi2] at h1
      rw [horder] at h1
      rw [mul_comm] at h1
      exact h1)
  have hmem : ∀ ξ : Lˣ, ξ ^ 3 = 1 → ξ ∈ rootsOfUnity (mPhi2 a) L := by
    intro ξ hξ
    rw [mem_rootsOfUnity]
    obtain ⟨k, hk⟩ := h3m
    rw [hk, pow_mul, hξ, one_pow]
  set w₀ : (rootsOfUnity (mPhi2 a) L) × (rootsOfUnity (mPhi2 a) L) :=
    (⟨ζ, hmem ζ hζ3⟩, 1) with hw₀
  obtain ⟨y₀, hy₀T, hy₀⟩ := hTsurj (Φ w₀) ⟨w₀, rfl⟩
  have hψy₀ : ψ y₀ = rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ 1) (ζ ^ 0) (uPhi2 a)) := by
    rw [hψapp, hy₀, hΦ, pow_one, pow_zero]
    rfl
  have hbR : ∀ i j : ℕ, rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) ∈
      twistedFixed D.F n := by
    intro i j
    have := hΦF (⟨ζ ^ i, hmem _ (by rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow])⟩,
      ⟨ζ ^ j, hmem _ (by rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow])⟩)
    rw [hΦ] at this
    exact this
  have hlang : ∀ {i j : ℕ}, i < 3 → j < 3 → ¬ (i = 0 ∧ j = 0) →
      ∀ c ∈ adjointGroup ReeTag.F4.tag L,
      c * rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) =
        rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) * c →
      ∃ z ∈ adjointGroup ReeTag.F4.tag L,
        z * rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) =
          rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) * z ∧
        z⁻¹ * twistMap D.F n z = c := by
    intro i j hi hj hij c hc hcomm
    obtain ⟨v, hv⟩ := exists_transport_expTuple hζ a hi hj hij
    exact exists_lang_cent D.isFrob hsq hζ (expTuple_pow_three hζ3 i j _) (hbR i j) hv hc hcomm
  have hconj0 : ∀ {i j : ℕ}, i < 3 → j < 3 → ¬ (i = 0 ∧ j = 0) →
      ∃ r ∈ twistedFixed D.F n,
        r * rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) * r⁻¹ =
          rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ 1) (ζ ^ 0) (uPhi2 a)) := by
    intro i j hi hj hij
    obtain ⟨v, hv⟩ := exists_transport_expTuple hζ a hi hj hij
    obtain ⟨v₀, hv₀⟩ := exists_transport_expTuple hζ a (i := 1) (j := 0) (by norm_num)
      (by norm_num) (by norm_num)
    have e1 := (rootDiagUnit_eq_conj_canonicalRep_iff
      (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) (bStd ζ) v).2 hv
    have e0 := (rootDiagUnit_eq_conj_canonicalRep_iff
      (expTuple (ζ ^ 1) (ζ ^ 0) (uPhi2 a)) (bStd ζ) v₀).2 hv₀
    set N := canonicalRep (coxeterSystem ReeTag.F4.tag) L v₀ *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L v)⁻¹ with hN
    have hNG : N ∈ adjointGroup ReeTag.F4.tag L :=
      mul_mem (canonicalRep_mem_adjointGroup _ L v₀)
        (inv_mem (canonicalRep_mem_adjointGroup _ L v))
    refine exists_twisted_conj_of_lang hnadj (hbR i j) (hbR 1 0) hNG ?_
      (hlang (by norm_num) (by norm_num) (by norm_num))
    rw [e1, e0, hN]
    group
  suffices key : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = 3 → ∃ g, g * x * g⁻¹ = y₀ by
    obtain ⟨g, hg⟩ := key y hy
    obtain ⟨g', hg'⟩ := key y' hy'
    refine ⟨g'⁻¹ * g, ?_⟩
    calc g'⁻¹ * g * y * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * y * g⁻¹) * g' := by group
      _ = g'⁻¹ * (g' * y' * g'⁻¹) * g' := by rw [hg, hg']
      _ = y' := by group
  intro x hx
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    have : ψ y₀ = 1 := by rw [h1, map_one]
    rw [hψapp, hy₀] at this
    have h2 : Φ w₀ = Φ 1 := by rw [this, map_one]
    have h3 := congrArg (fun w => ((w.1 : rootsOfUnity (mPhi2 a) L) : Lˣ)) (hΦinj h2)
    simp only [hw₀, Prod.fst_one, OneMemClass.coe_one] at h3
    rw [h3, orderOf_one] at hζ
    norm_num at hζ
  have hy₀3 : y₀ ^ 3 = 1 := by
    apply hψinj
    rw [map_pow, hψapp, hy₀, ← map_pow, map_one]
    have : w₀ ^ 3 = 1 := by
      ext
      · simp [hw₀, hζ3]
      · simp [hw₀]
    rw [this, map_one]
  obtain ⟨g, z, hzT, hz1, hz3, hcomm⟩ :=
    exists_conj_commute_torsion T hTcomm hindex hy₀T hy₀1 hy₀3 hx3
  set x₁ := g⁻¹ * x * g with hx₁
  obtain ⟨wz, hwz⟩ := (hψT z).1 hzT
  have hwz3 : wz ^ 3 = 1 := by
    apply hΦinj
    rw [map_pow, hwz, ← map_pow, hz3, map_one, map_one]
  have hwz1 : (wz.1 : Lˣ) ^ 3 = 1 := by
    have := congrArg (fun w => ((w.1 : rootsOfUnity (mPhi2 a) L) : Lˣ)) hwz3
    simpa using this
  have hwz2 : (wz.2 : Lˣ) ^ 3 = 1 := by
    have := congrArg (fun w => ((w.2 : rootsOfUnity (mPhi2 a) L) : Lˣ)) hwz3
    simpa using this
  obtain ⟨i, hi, hiζ⟩ := exists_pow_eq_of_pow_three hζ hwz1
  obtain ⟨j, hj, hjζ⟩ := exists_pow_eq_of_pow_three hζ hwz2
  have hψz : ψ z = rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) := by
    rw [← hwz, hΦ, hiζ, hjζ]
  have hij : ¬ (i = 0 ∧ j = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hz1
    apply hψinj
    rw [hψz, map_one, pow_zero]
    have : expTuple (1 : Lˣ) 1 (uPhi2 a) = 1 := by
      funext k
      simp [expTuple]
    rw [this]
    exact rootDiagUnit_one
  obtain ⟨v, hv⟩ := exists_transport_expTuple hζ a hi hj hij
  have hs3 : ψ x₁ ^ 3 = 1 := by
    rw [← map_pow, hx₁, show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3]
    simp
  have hscomm : ψ x₁ * rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) =
      rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) * ψ x₁ := by
    rw [← hψz, ← map_mul, ← map_mul, hcomm]
  obtain ⟨gG, hgG, c, hc3, hcR, hgc⟩ := exists_conj_torsion D.isFrob hsq hζ
    (expTuple_pow_three hζ3 i j _) (hbR i j) hv (hψR x₁) hscomm hs3
  obtain ⟨ξ₁, ξ₂, hξ₁, hξ₂, hcξ⟩ := exists_expTuple_of_torsion D.isFrob hc3 hcR
  obtain ⟨i', hi', hi'ξ⟩ := exists_pow_eq_of_pow_three hζ hξ₁
  obtain ⟨j', hj', hj'ξ⟩ := exists_pow_eq_of_pow_three hζ hξ₂
  rw [← hi'ξ, ← hj'ξ] at hcξ
  have hij' : ¬ (i' = 0 ∧ j' = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hx1
    have h1 : ψ x₁ = 1 := by
      have : rootDiagUnit ReeTag.F4.tag c = 1 := by
        rw [hcξ, pow_zero]
        have : expTuple (1 : Lˣ) 1 (uPhi2 a) = 1 := by
          funext k
          simp [expTuple]
        rw [this]
        exact rootDiagUnit_one
      rw [this] at hgc
      calc ψ x₁ = gG * (gG⁻¹ * ψ x₁ * gG) * gG⁻¹ := by group
        _ = 1 := by rw [hgc]; group
    have h2 : x₁ = 1 := hψinj (h1.trans (map_one ψ).symm)
    calc x = g * x₁ * g⁻¹ := by rw [hx₁]; group
      _ = 1 := by rw [h2]; group
  have hcR' : rootDiagUnit ReeTag.F4.tag (expTuple (ζ ^ i') (ζ ^ j') (uPhi2 a)) ∈
      twistedFixed D.F n := hbR i' j'
  obtain ⟨r₁, hr₁, hr₁s⟩ := exists_twisted_conj_of_lang hnadj (hψR x₁) hcR' (inv_mem hgG)
    (by rw [← hcξ, inv_inv]; exact hgc) (hlang hi' hj' hij')
  obtain ⟨r₂, hr₂, hr₂s⟩ := hconj0 hi' hj' hij'
  obtain ⟨γ, hγ⟩ := hψsurj (r₂ * r₁) (mul_mem hr₂ hr₁)
  refine ⟨γ * g⁻¹, ?_⟩
  have hconj : γ * g⁻¹ * x * (γ * g⁻¹)⁻¹ = γ * x₁ * γ⁻¹ := by
    rw [hx₁]
    group
  apply hψinj
  rw [hψy₀, ← hr₂s, ← hr₁s, hconj, map_mul, map_mul, map_inv, hγ]
  group

theorem centralizer_mulEquiv_unitarySU (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (y : ReeTag.F4.reeGamma K a)
    (hy : orderOf y = 3) :
    Nonempty (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) ≃*
      unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3) := by
  obtain ⟨y₀, hy₀, ⟨e⟩⟩ := exists_centralizer_mulEquiv_unitarySU a K hK
  obtain ⟨g, rfl⟩ := orderThreeConj_reeGamma a K hK y₀ y hy₀ hy
  rw [ReeF4ThreeLocalProof.centralizer_conj_eq_map]
  exact ⟨((Subgroup.centralizer ({y₀} : Set (ReeTag.F4.reeGamma K a))).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e⟩

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
