module

public import CFSG.RankThree.PartTwo.Sec8.HeringD4Weyl
public import CFSG.RankThree.PartTwo.Sec8.HeringD4G2Conj
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open CFSG.Assembly.RankThreeEven (projSL)


section Certs


namespace CFSG.RankThree.PartTwo.Sec8.HeringD4

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem nonempty_residual_conj {G : Type*} [Group G] (g x : G) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) ≃*
      inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set G))) := by
  have h : (MulAut.conj g⁻¹) (g * x * g⁻¹) = x := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  exact ⟨(Sec21.Item228Census3Proof.perfectResidualCentralizerEquiv (MulAut.conj g⁻¹)
    (g * x * g⁻¹)).trans (MulEquiv.subgroupCongr (by rw [h]))⟩

theorem exists_order_three_long_short (k : Type) [Field k] :
    ∃ y₁ y₂ : adjointGroup Tag.G2 k, y₁ ∈ KS11Lie4Proof.g2LongSL2 k ∧
      y₂ ∈ KS11Lie4Proof.g2ShortSL2 k ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 := by
  obtain ⟨eM⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := k)
  obtain ⟨eS⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := k)
  have hM3 := KS11Lie2Proof.sl2Three_pow_three k
  have hM1 : KS11Lie2Proof.sl2Three k ≠ 1 := by
    intro h
    apply KS11Lie2Proof.sl2Three_ne_smul (k := k) 1
    rw [h, one_smul]
    rfl
  refine ⟨((eM (KS11Lie2Proof.sl2Three k) : KS11Lie4Proof.g2LongSL2 k) :
      adjointGroup Tag.G2 k),
    ((eS (KS11Lie2Proof.sl2Three k) : KS11Lie4Proof.g2ShortSL2 k) : adjointGroup Tag.G2 k),
    (eM _).2, (eS _).2, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hM3, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ← map_pow, hM3, map_one, Subgroup.coe_one]
  · intro h
    apply hM1
    apply eM.injective
    rw [map_one]
    exact Subtype.ext h
  · intro h
    apply hM1
    apply eS.injective
    rw [map_one]
    exact Subtype.ext h

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem residual_iota_of_mem_long (P : D4Par n X σ) (hK : ringChar X = 2)
    {y : adjointGroup Tag.G2 (fixSubfield σ)}
    (hy : y ∈ KS11Lie4Proof.g2LongSL2 (fixSubfield σ)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nonempty (inSubgroup perfectResidual
      (Subgroup.centralizer ({KFacts.trialityG2Incl σ hK y} : Set (C0 σ))) ≃*
        projSL 2 (GaloisField 2 (3 * n))) := by
  obtain ⟨w₀, -, hwB⟩ := g2_pair_conj_AB' σ P hK
  have hinj : Function.Injective (KFacts.trialityG2Incl σ hK) :=
    KFacts.trialityG2Incl_injective σ hK
  set y' := w₀ * y * w₀⁻¹ with hy'
  have hy'M : y' ∈ (KS11Lie4Proof.g2LongSL2 (fixSubfield σ)).map (MulAut.conj w₀).toMonoidHom :=
    ⟨y, hy, rfl⟩
  have hιB : KFacts.trialityG2Incl σ hK y' ∈ Bsub σ := hwB ⟨y', hy'M, rfl⟩
  have hι3 : KFacts.trialityG2Incl σ hK y' ^ 3 = 1 := by
    rw [← map_pow, hy', conj_pow, hy3, mul_one, mul_inv_cancel, map_one]
  have hι1 : KFacts.trialityG2Incl σ hK y' ≠ 1 := by
    intro h
    apply hy1
    have h' := hinj (h.trans (map_one _).symm)
    have : y = w₀⁻¹ * y' * w₀ := by rw [hy']; group
    rw [this, h']
    group
  have hq3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨hcomm, -⟩ := KS11Lie6Proof.d4ThreeBCent_holds X (2 ^ n) σ P.card P.frob hq3
    (KFacts.trialityG2Incl σ hK y') hιB hι3 hι1
  have hσ3 := P.sigma_pow_three
  have hSC : (KS11Lie4Proof.d4ShortSL2 X σ.toRingHom : Subgroup (C0 σ)) ≤
      Subgroup.centralizer ({KFacts.trialityG2Incl σ hK y'} : Set (C0 σ)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hιB s hs
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
  have : Finite (orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer) :=
    Subtype.finite
  have hF : Nat.card (orbitField TwistTag.D4 X σ.toRingHom KS11Lie4Proof.d4Outer) =
      2 ^ (3 * n) := by
    rw [KS11Lie4Proof.natCard_orbitField_d4Outer hσ3, P.card, ← pow_mul, mul_comm]
  obtain ⟨φ⟩ := Item8KFacts3.residual_projSL_of_threeB hSC hcomm hF
    (by have := P.one_le; omega) e
  have hιy : KFacts.trialityG2Incl σ hK y =
      (KFacts.trialityG2Incl σ hK w₀)⁻¹ * KFacts.trialityG2Incl σ hK y' *
        ((KFacts.trialityG2Incl σ hK w₀)⁻¹)⁻¹ := by
    rw [hy', map_mul, map_mul, map_inv]
    group
  rw [hιy]
  obtain ⟨ψ⟩ := nonempty_residual_conj (KFacts.trialityG2Incl σ hK w₀)⁻¹
    (KFacts.trialityG2Incl σ hK y')
  exact ⟨ψ.trans φ⟩

theorem exists_E9 [CharP (fixSubfield σ) 2] (P : D4Par n X σ) (hK : ringChar X = 2)
    (c : adjointGroup Tag.G2 (fixSubfield σ)) {m s : adjointGroup Tag.G2 (fixSubfield σ)}
    (hm : m ∈ KS11Lie4Proof.g2LongSL2 (fixSubfield σ))
    (hs : s ∈ KS11Lie4Proof.g2ShortSL2 (fixSubfield σ)) (hm3 : m ^ 3 = 1) (hs3 : s ^ 3 = 1)
    (hm1 : m ≠ 1) (hs1 : s ≠ 1) :
    (c⁻¹ * m * c) ^ 3 = 1 ∧ (c⁻¹ * s * c) ^ 3 = 1 ∧
      (c⁻¹ * m * c) * (c⁻¹ * s * c) = (c⁻¹ * s * c) * (c⁻¹ * m * c) ∧ c⁻¹ * m * c ≠ 1 ∧
      c⁻¹ * s * c ∉ Subgroup.zpowers (c⁻¹ * m * c) ∧
      Nonempty (inSubgroup perfectResidual
        (Subgroup.centralizer ({KFacts.trialityG2Incl σ hK (c⁻¹ * m * c)} : Set (C0 σ))) ≃*
          projSL 2 (GaloisField 2 (3 * n))) := by
  have hconj3 : ∀ {t : adjointGroup Tag.G2 (fixSubfield σ)}, t ^ 3 = 1 → (c⁻¹ * t * c) ^ 3 = 1 :=
    fun {t} ht => by
      have := conj_pow (a := c⁻¹) (b := t) (i := 3)
      rw [inv_inv] at this
      rw [this, ht]
      group
  have hconj1 : ∀ {t : adjointGroup Tag.G2 (fixSubfield σ)}, t ≠ 1 → c⁻¹ * t * c ≠ 1 :=
    fun {t} ht h => ht (by
      have : t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      rw [this, h]
      group)
  refine ⟨hconj3 hm3, hconj3 hs3, ?_, hconj1 hm1, ?_, ?_⟩
  · have h := (KS11Lie4Proof.g2Short_commute_g2Long hs hm).symm
    calc c⁻¹ * m * c * (c⁻¹ * s * c) = c⁻¹ * (m * s) * c := by group
      _ = c⁻¹ * (s * m) * c := by rw [h]
      _ = c⁻¹ * s * c * (c⁻¹ * m * c) := by group
  · intro hmem
    apply hs1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hsm : s = m ^ j := by
      have h1 : (c⁻¹ * m * c) ^ j = c⁻¹ * m ^ j * c := by
        have := conj_zpow (a := c⁻¹) (b := m) (i := j)
        rwa [inv_inv] at this
      rw [h1] at hj
      have : s = c * (c⁻¹ * s * c) * c⁻¹ := by group
      rw [this, ← hj]
      group
    have hsM : s ∈ KS11Lie4Proof.g2LongSL2 (fixSubfield σ) := hsm ▸ zpow_mem hm j
    exact Item83Proof.eq_one_of_mem_g2LongSL2_of_mem_g2ShortSL2 hsM hs
  · have hιm : KFacts.trialityG2Incl σ hK (c⁻¹ * m * c) =
        (KFacts.trialityG2Incl σ hK c)⁻¹ * KFacts.trialityG2Incl σ hK m *
          ((KFacts.trialityG2Incl σ hK c)⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv, inv_inv]
    rw [hιm]
    obtain ⟨ψ⟩ := nonempty_residual_conj (KFacts.trialityG2Incl σ hK c)⁻¹
      (KFacts.trialityG2Incl σ hK m)
    obtain ⟨φ⟩ := residual_iota_of_mem_long P hK hm hm3 hm1
    exact ⟨ψ.trans φ⟩

end CFSG.RankThree.PartTwo.Sec8.HeringD4

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

theorem kF83TrialityD4_holds : KF83TrialityD4 := by
  intro n hn K _ _ σ hK2 hcard hσ z hz3
  have hn1 : 1 ≤ n := hn.pos
  have P : D4Par n K σ := ⟨hn1, hcard, hσ⟩
  have : CharP K 2 := ringChar.of_eq hK2
  have : Finite (fixSubfield σ) := Subtype.finite
  have : CharP (fixSubfield σ) 2 :=
    RingHom.charP (fixSubfield σ).subtype (fixSubfield σ).subtype.injective 2
  have hkc : Nat.card (fixSubfield σ) = 2 ^ n := KFacts.card_fixSubfield_of_cube hn1 hcard hσ
  have h3k : 3 ∣ Nat.card (fixSubfield σ) + 1 := by
    rw [hkc]
    have := HeringD4.two_pow_mod_three_of_odd hn
    omega
  obtain ⟨m, s, hmM, hsS, hm3, hs3, hm1, hs1⟩ :=
    HeringD4.exists_order_three_long_short (fixSubfield σ)
  by_cases hz1 : z = 1
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := HeringD4.exists_E9 P hK2 1 hmM hsS hm3 hs3 hm1 hs1
    simp only [inv_one, one_mul, mul_one] at h1 h2 h3 h4 h5 h6
    exact ⟨m, s, h1, h2, h3, h4, h5, by rw [hz1]; exact Subgroup.one_mem _, h6⟩
  · obtain ⟨c, hc⟩ := HeringD4.g2ThreeConjSL2Minus_all (fixSubfield σ) h3k hz3 hz1
    have hz'3 : (c * z * c⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3]
      group
    have hz'1 : c * z * c⁻¹ ≠ 1 := fun h => hz1 (by
      have : z = c⁻¹ * (c * z * c⁻¹) * c := by group
      rw [this, h]
      group)
    have hz : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    rcases hc with hcS | hcM
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := HeringD4.exists_E9 P hK2 c hmM hcS hm3 hz'3 hm1 hz'1
      rw [hz] at h2 h3 h5
      exact ⟨c⁻¹ * m * c, z, h1, h2, h3, h4, h5,
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)), h6⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := HeringD4.exists_E9 P hK2 c hcM hsS hz'3 hs3 hz'1 hs1
      rw [hz] at h1 h3 h4 h5 h6
      exact ⟨z, c⁻¹ * s * c, h1, h2, h3, h4, h5,
        Subgroup.subset_closure (Set.mem_insert _ _), h6⟩

end CFSG.RankThree.PartTwo.Sec8.Item83Proof

end Certs
