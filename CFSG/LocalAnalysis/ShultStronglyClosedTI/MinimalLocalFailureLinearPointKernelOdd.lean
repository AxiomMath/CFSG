module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelSemilinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearHullOvergroups

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_pointTwoCoreImage {Z A : Subgroup G} (hAZ : A ≤ Z) (hAn : (A.subgroupOf Z).Normal)
    (hA : IsPGroup 2 A) : A ≤ TwoCoreGrowth.pointTwoCoreImage Z := by
  have htwo : IsPGroup 2 (A.subgroupOf Z) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAZ).symm
  have hcore : A.subgroupOf Z ≤ CFSG.pCore 2 Z := le_sSup ⟨hAn, htwo⟩
  have hmap := Subgroup.map_mono (f := Z.subtype) hcore
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAZ] at hmap

theorem centralizer_singleton_lt_top (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {y : G} (hy : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  have hyZ : y ∈ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton y)
  rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hbot | htopZ
  · exact hy (by rwa [hbot, Subgroup.mem_bot] at hyZ)
  · obtain ⟨a, b, hab⟩ := hnonab
    have hb : b ∈ Subgroup.center G := htopZ ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem mem_centralizer_of_commute_regular {Q X : Subgroup G}
    (hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hXodd : Odd (Nat.card X))
    (hXregular : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃! x : X, (x : G)⁻¹ * a * x = b)
    {p : G} (hpQ : ∀ v ∈ Q, p⁻¹ * v * p ∈ Q) (hpX : ∀ x ∈ X, p * x = x * p) {n : ℕ}
    (hp : p ^ (2 ^ n) = 1) : p ∈ Subgroup.centralizer (Q : Set G) := by
  by_cases hQ1 : ∃ s, s ∈ (Q : Set G) \ {1}
  swap
  · push Not at hQ1
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv1 : v = 1 := by
      by_contra hv1
      exact hQ1 v ⟨hv, hv1⟩
    rw [hv1, one_mul, mul_one]
  obtain ⟨s, hs⟩ := hQ1
  have hps : p⁻¹ * s * p ∈ (Q : Set G) \ {1} :=
    ⟨hpQ s hs.1, fun h => hs.2 (by
      rw [show s = p * (p⁻¹ * s * p) * p⁻¹ by group, h]
      simp)⟩
  obtain ⟨x, hx, -⟩ := hXregular s hs _ hps
  have hsame : ∀ r ∈ Q, p⁻¹ * r * p = (x : G)⁻¹ * r * x := by
    intro r hr
    by_cases hr1 : r = 1
    · rw [hr1]
      group
    obtain ⟨w, hw, -⟩ := hXregular s hs r ⟨hr, hr1⟩
    have hpw : p * w = w * p := hpX w w.2
    have hxw : (x : G) * w = w * x := hXcomm x x.2 w w.2
    rw [← hw]
    calc p⁻¹ * ((w : G)⁻¹ * s * w) * p = ((w : G) * p)⁻¹ * s * ((w : G) * p) := by group
      _ = (p * w)⁻¹ * s * (p * w) := by rw [hpw]
      _ = (w : G)⁻¹ * (p⁻¹ * s * p) * w := by group
      _ = (w : G)⁻¹ * ((x : G)⁻¹ * s * x) * w := by rw [hx]
      _ = ((x : G) * w)⁻¹ * s * ((x : G) * w) := by group
      _ = ((w : G) * x)⁻¹ * s * ((w : G) * x) := by rw [hxw]
      _ = (x : G)⁻¹ * ((w : G)⁻¹ * s * w) * x := by group
  set c := p * (x : G)⁻¹ with hcdef
  have hcQ : c ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := hsame r hr
    have h2 : c⁻¹ * r * c = r := by
      rw [hcdef]
      calc (p * (x : G)⁻¹)⁻¹ * r * (p * (x : G)⁻¹) = (x : G) * (p⁻¹ * r * p) * (x : G)⁻¹ := by
            group
        _ = r := by rw [h1]; group
    calc r * c = c * (c⁻¹ * r * c) := by group
      _ = c * r := by rw [h2]
  have hpxc : p = c * x := by rw [hcdef, inv_mul_cancel_right]
  have hcx : Commute c (x : G) := by
    have hpx : p * x = x * p := hpX x x.2
    show c * x = x * c
    rw [hcdef, inv_mul_cancel_right, ← mul_assoc, ← hpx, mul_inv_cancel_right]
  have hxpow : (x : G) ^ (2 ^ n) ∈ Subgroup.centralizer (Q : Set G) := by
    have h1 : c ^ (2 ^ n) * (x : G) ^ (2 ^ n) = 1 := by
      rw [← hcx.mul_pow, ← hpxc, hp]
    have h2 : (x : G) ^ (2 ^ n) = (c ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcQ _)
  have hx1 : (x : G) ^ (2 ^ n) = 1 :=
    eq_one_of_regular_of_mem_centralizer hXregular hs (X.pow_mem x.2 _) hxpow
  have hxord : orderOf x = 1 := by
    have h1 : orderOf x ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using hx1)
    have h2 : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
    have hcop : Nat.Coprime (2 ^ n) (Nat.card X) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hXodd)
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hxe : (x : G) = 1 := by
    rw [orderOf_eq_one_iff] at hxord
    rw [hxord, OneMemClass.coe_one]
  rw [hpxc, hxe, mul_one]
  exact hcQ

variable [Finite G]

theorem pair_centralizer_odd_two_core_trivial
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    {y : G} (hyJ : y ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hy1 : y ≠ 1) (hyodd : Odd (orderOf y)) :
    TwoCoreGrowth.pointTwoCoreImage
      (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G)) = ⊥ := by
  set B := pairPointStabilizer H beta with hBdef
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set J := Subgroup.centralizer (K : Set G) with hJdef
  set Y := Subgroup.centralizer ({y} : Set G) with hYdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  obtain ⟨hQ, ⟨e, hQe⟩, hQ4, -, hXB, hXnormal, hXcyclic, hXcard, hXreg, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, -, hXodd, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hQH, -, hQnormal, -, -, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hJ : J = B ⊓ Subgroup.centralizer (Q : Set G) :=
    pair_hull_centralizer_eq h hcomm hsmallerR1 hbeta ht hproper hlin
  obtain ⟨u, huB, hu⟩ := proper_pair_stabilizer_exists_involution h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨f, hfinj⟩⟩ :=
    proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl
      huB hu
  obtain ⟨k, _, _, hkq, ⟨ψ⟩⟩ := hlin
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  have hBX : B ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXB).mp hXnormal
  have hXY : X ≤ Y := by
    intro x hx
    rw [hYdef, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hyJ x (hXK hx))
  set P := TwoCoreGrowth.pointTwoCoreImage (B ⊓ Y) with hPdef
  have hP2 : IsPGroup 2 P := TwoCoreGrowth.pointTwoCoreImage_isPGroup _
  have hPBY : P ≤ B ⊓ Y := TwoCoreGrowth.pointTwoCoreImage_le _
  have hPN : B ⊓ Y ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPBY).mp
      (TwoCoreGrowth.pointTwoCoreImage_normal _)
  have hPX0 : P ⊓ X = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := hP2.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hXodd)
  have hPX : ∀ p ∈ P, ∀ x ∈ X, p * x = x * p := by
    intro p hp x hx
    have hxBY : x ∈ B ⊓ Y := ⟨hXB hx, hXY hx⟩
    have h1 : p * x * p⁻¹ * x⁻¹ ∈ P := by
      have hmem := (Subgroup.mem_normalizer_iff.mp (hPN hxBY) p⁻¹).mp (P.inv_mem hp)
      rw [show p * x * p⁻¹ * x⁻¹ = p * (x * p⁻¹ * x⁻¹) by group]
      exact P.mul_mem hp hmem
    have h2 : p * x * p⁻¹ * x⁻¹ ∈ X := by
      have hmem := (Subgroup.mem_normalizer_iff.mp (hBX (hPBY hp).1) x).mp hx
      exact X.mul_mem hmem (X.inv_mem hx)
    have h3 : p * x * p⁻¹ * x⁻¹ = 1 := by
      have hmem : p * x * p⁻¹ * x⁻¹ ∈ P ⊓ X := ⟨h1, h2⟩
      rwa [hPX0, Subgroup.mem_bot] at hmem
    calc p * x = p * x * p⁻¹ * x⁻¹ * (x * p) := by group
      _ = x * p := by rw [h3, one_mul]
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := X)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXodd' : Odd (Nat.card X) := hXodd
  have hPJ : ∀ p ∈ P, p ∈ J := by
    intro p hp
    rw [hJ]
    refine ⟨(hPBY hp).1, ?_⟩
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hP2 ⟨p, hp⟩
    have hpn : p ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hpQ : ∀ v ∈ Q, p⁻¹ * v * p ∈ Q := by
      intro v hv
      have hmem := (Subgroup.mem_normalizer_iff.mp
        (hHQ (H.inv_mem (hBH (hPBY hp).1))) v).mp hv
      simpa only [inv_inv] using hmem
    exact mem_centralizer_of_commute_regular hXcomm hXodd' hXreg hpQ (fun x hx => hPX p hp x hx)
      hpn
  have hfy : f ⟨y, hyJ⟩ ≠ 1 := fun h1 => hy1 (congrArg Subtype.val (hfinj (h1.trans
    (map_one f).symm)))
  have hq4 : 4 ≤ Nat.card k := by rw [hkq]; exact hQ4
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [hQe, pow_zero] at hQ4
    omega
  obtain ⟨e', he', hke'⟩ := TwoCoreGrowth.even_field_binary_size (by
    rw [hkq, hQe]; exact (Nat.even_pow' he0).mpr even_two) hq4
  set x₀ := ψ (f ⟨y, hyJ⟩) with hx₀def
  have hx₀1 : x₀ ≠ 1 := fun h1 => hfy (by rwa [MulEquiv.map_eq_one_iff] at h1)
  have hx₀odd : Odd (orderOf x₀) := by
    rw [hx₀def, MulEquiv.orderOf_eq, orderOf_injective f hfinj, Subgroup.orderOf_mk]
    exact hyodd
  obtain ⟨-, hcard, -⟩ :=
    TwoCoreGrowth.psl2_even_odd_element_full_centralizer e' he' hke' x₀ hx₀1 hx₀odd
  have hkeven : Even (Nat.card k) := by rw [hke']; exact (Nat.even_pow' (by omega)).mpr even_two
  have hCodd : Odd (Nat.card (Subgroup.centralizer ({x₀} : Set (PSL2MatrixGroup k)))) := by
    rcases hcard with hc | hc <;> rw [hc]
    · exact Nat.Even.sub_odd (by omega) hkeven odd_one
    · exact hkeven.add_one
  apply le_bot_iff.mp
  intro p hp
  rw [Subgroup.mem_bot]
  have hpJ := hPJ p hp
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP2 ⟨p, hp⟩
  have hpn : p ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hpy : p * y = y * p := Subgroup.mem_centralizer_singleton_iff.mp (hPBY hp).2
  have hxmem : ψ (f ⟨p, hpJ⟩) ∈ Subgroup.centralizer ({x₀} : Set (PSL2MatrixGroup k)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hx₀def, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul]
    exact congrArg (fun w => ψ (f w)) (Subtype.ext hpy)
  have hdvd : orderOf (ψ (f ⟨p, hpJ⟩)) ∣
      Nat.card (Subgroup.centralizer ({x₀} : Set (PSL2MatrixGroup k))) := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hxmem
    exact h1
  rw [MulEquiv.orderOf_eq, orderOf_injective f hfinj, Subgroup.orderOf_mk] at hdvd
  have h2 : orderOf p ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpn
  have hcop : Nat.Coprime (2 ^ n) (Nat.card (Subgroup.centralizer ({x₀} :
      Set (PSL2MatrixGroup k)))) := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hCodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 hdvd)

theorem odd_pair_centralizer_structure
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    {y : G} (hyJ : y ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hy1 : y ≠ 1) (hyodd : Odd (orderOf y)) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let Y := Subgroup.centralizer ({y} : Set G)
    H ⊓ Y = Q ⊔ (B ⊓ Y) ∧ TwoCoreGrowth.pointTwoCoreImage (H ⊓ Y) = Q ∧
      TwoCoreGrowth.pointTwoCoreImage H ⊓ Y = Q := by
  intro B Q Y
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  obtain ⟨hQH, -, hQnormal, -, hQp, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨hNeq, -, -⟩ := point_normalizer_eq_root_sup h hcomm hsmallerR1 hbeta ht hproper hlin
  have hJ := pair_hull_centralizer_eq h hcomm hsmallerR1 hbeta ht hproper hlin
  obtain ⟨-, -, -, hY⟩ := minimalLocalFailure_linear_hull_proper_overgroups_normalize_of_conclusions
    h hcomm hsmallerR1 hbeta ht hproper hlin hexcl
  have hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyJ k hk)
  have hYN := (hY Y hKY (centralizer_singleton_lt_top hsimple hnonab hy1)).2
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBH.trans hHQ
  have hyQ : y ∈ Subgroup.centralizer (Q : Set G) := by
    rw [hJ] at hyJ
    exact hyJ.2
  have hQY : Q ≤ Y := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyQ a ha)
  have hHY : H ⊓ Y = Q ⊔ (B ⊓ Y) := by
    apply le_antisymm
    · rintro g ⟨hgH, hgY⟩
      have hgQB : g ∈ Q ⊔ B := by
        rw [← hNeq]
        exact ⟨hYN hgY, hgH⟩
      have hg' : g ∈ (Q : Set G) * (B : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q B hBQ]
        exact hgQB
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      have hbY : b ∈ Y := by
        have hmem := Y.mul_mem (Y.inv_mem (hQY ha)) hgY
        rwa [inv_mul_cancel_left] at hmem
      exact Subgroup.mul_mem_sup ha ⟨hb, hbY⟩
    · exact sup_le (le_inf hQH hQY) (inf_le_inf_right Y hBH)
  have hP := pair_centralizer_odd_two_core_trivial h hcomm hsmallerR1 hbeta ht hproper hlin hexcl
    hyJ hy1 hyodd
  set R := TwoCoreGrowth.pointTwoCoreImage (H ⊓ Y) with hRdef
  have hRle : R ≤ H ⊓ Y := TwoCoreGrowth.pointTwoCoreImage_le _
  have hR2 : IsPGroup 2 R := TwoCoreGrowth.pointTwoCoreImage_isPGroup _
  have hRn := (Subgroup.normal_subgroupOf_iff hRle).mp (TwoCoreGrowth.pointTwoCoreImage_normal _)
  have hQR : Q ≤ R := by
    refine le_pointTwoCoreImage (le_inf hQH hQY) ((Subgroup.normal_subgroupOf_iff
      (le_inf hQH hQY)).mpr fun a g ha hg => ?_) hQp
    exact (Subgroup.mem_normalizer_iff.mp (hHQ hg.1) a).mp ha
  have hRQ : R ≤ Q := by
    have hmod := sup_inf_eq_of_le_normalizer (Q := Q) (B := B ⊓ Y) (L := R)
      (inf_le_left.trans hBQ) hQR
    rw [← hHY, inf_eq_right.mpr hRle] at hmod
    have hBYR : B ⊓ Y ⊓ R ≤ TwoCoreGrowth.pointTwoCoreImage (B ⊓ Y) := by
      refine le_pointTwoCoreImage inf_le_left ((Subgroup.normal_subgroupOf_iff
        inf_le_left).mpr fun a g ha hg => ⟨(B ⊓ Y).mul_mem ((B ⊓ Y).mul_mem hg ha.1)
          ((B ⊓ Y).inv_mem hg), hRn a g ha.2 ⟨hBH hg.1, hg.2⟩⟩) (hR2.to_le inf_le_right)
    rw [hP, le_bot_iff] at hBYR
    rw [hmod, hBYR, sup_bot_eq]
  have hMn := (Subgroup.normal_subgroupOf_iff (TwoCoreGrowth.pointTwoCoreImage_le H)).mp
    (TwoCoreGrowth.pointTwoCoreImage_normal H)
  have hMY : TwoCoreGrowth.pointTwoCoreImage H ⊓ Y ≤ R := by
    refine le_pointTwoCoreImage (inf_le_inf_right Y (TwoCoreGrowth.pointTwoCoreImage_le H))
      ((Subgroup.normal_subgroupOf_iff (inf_le_inf_right Y
        (TwoCoreGrowth.pointTwoCoreImage_le H))).mpr fun a g ha hg =>
          ⟨hMn a g ha.1 hg.1, Y.mul_mem (Y.mul_mem hg.2 ha.2) (Y.inv_mem hg.2)⟩)
      ((TwoCoreGrowth.pointTwoCoreImage_isPGroup H).to_le inf_le_left)
  have hQM : Q ≤ TwoCoreGrowth.pointTwoCoreImage H :=
    TwoCoreGrowth.original_point_hull_le_two_core h.local_datum hQp
  exact ⟨hHY, le_antisymm hRQ hQR, le_antisymm (hMY.trans hRQ) (le_inf hQM hQY)⟩

end CFSG.ShultStronglyClosedTI.LinearChain
