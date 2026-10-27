module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Sec11

section D4


variable {K : Type} [Field K]

theorem isQuasisimple_d4Short [Finite K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (hK4 : 4 ≤ Nat.card K) :
    IsQuasisimple (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) := by
  have hinj := orbitRankOneHom_injective_D4 hσ KS11Lie4Proof.d4Outer
  have hle := range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    KS11Lie4Proof.d4Outer
  have e : Matrix.SpecialLinearGroup (Fin 2)
      (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) ≃*
        KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
    (MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hle).symm
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer := by
    intro c
    rw [orbitField_D4_zero_eq_top σ h3]
    exact Subfield.mem_top c
  have hcard : Nat.card (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) =
      Nat.card K := Nat.card_congr (Equiv.subtypeUnivEquiv hmem)
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) := Subtype.finite
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (KS11Lie4Proof.isQuasisimple_sl2 (by rw [hcard]; exact hK4))

theorem d4T0_pow_three {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    KS11Lie5Proof.d4T0 σ ^ 3 = 1 ∧ KS11Lie5Proof.d4T0 σ ≠ 1 := by
  have hinj := orbitRankOneHom_injective_D4 hσ KS11Lie5Proof.d4Middle
  obtain ⟨hA3, hA1⟩ := KS11Lie4Proof.sl2Three_pow_three
    (orbitField TwistTag.D4 K σ.toRingHom KS11Lie5Proof.d4Middle)
  refine ⟨?_, fun h => hA1 (hinj ?_)⟩
  · rw [KS11Lie5Proof.d4T0, conj_pow, ← map_pow, hA3, map_one, mul_one, mul_inv_cancel]
  · have h1 : orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie5Proof.d4Middle
        (KS11Lie4Proof.sl2Three _) = 1 := by
      rw [KS11Lie5Proof.d4T0] at h
      exact conj_eq_one_iff.mp h
    rw [h1, map_one]

theorem d4T0_not_mem_short {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    (⟨KS11Lie5Proof.d4T0 σ, KS11Lie5Proof.d4T0_mem σ⟩ :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∉ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
  intro hmem
  obtain ⟨h3, h1⟩ := d4T0_pow_three hσ
  have hcent := KS11Lie5Proof.d4T0_mem_centralizer σ
  set R := orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer with hRdef
  have hinj : Function.Injective R := orbitRankOneHom_injective_D4 hσ KS11Lie4Proof.d4Outer
  have hle := range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    KS11Lie4Proof.d4Outer
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp (show KS11Lie5Proof.d4T0 σ ∈ R.range from hmem)
  have hB1 : B = 1 := by
    apply KS11Lie4Proof.eq_one_of_central_of_pow_three
    · apply hinj
      rw [map_pow, hB, h3, map_one]
    · intro A
      apply hinj
      have hRA : R A ∈ R.range := MonoidHom.mem_range.mpr ⟨A, rfl⟩
      have hA : (⟨R A, hle hRA⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
          KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
        Subgroup.mem_comap.mpr hRA
      have h' := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcent _ hA)
      simp only [Subgroup.coe_mul] at h'
      rw [map_mul, map_mul, hB]
      exact h'
  apply h1
  rw [← hB, hB1, map_one]

theorem false_of_le_normalizer_of_odd [Finite K] [CharP K 2] {f : ℕ} (hf : Odd f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1)
    {F T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hF3 : ∀ y ∈ F, y ^ 3 = 1) (hF9 : 9 ≤ Nat.card F) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hFT : F ≤ Subgroup.normalizer (T : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set ψ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective
  have hψC : ∀ x, ψ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun x => x.2
  have hT'1 : T.map ψ ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hT'C : T.map ψ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hF'C : F.map ψ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hF'T' : F.map ψ ≤ Subgroup.normalizer ((T.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hFT).trans (Subgroup.le_normalizer_map ψ)
  have hF'3 : ∀ y ∈ F.map ψ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF3 x hx, map_one]
  have hF'p : IsPGroup 3 (F.map ψ) := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hF'3 _ y.2)⟩
  obtain ⟨x, -, J, hJ, hle⟩ := Res417Seven.exists_conj_le_graphFixedParabolicLevi TwistTag.D4
    (r := 2) (p := 3) (by norm_num) σ hσ3 hF'C hF'p hT'C (hT2.map ψ) hT'1 hF'T'
  have hcard := Res417Seven.card_le_three_of_le_graphFixedParabolicLevi σ hσ3
    (Res417Seven.not_three_dvd_card_units_of_odd hf hK) hJ hle (by
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hF'3 y hy, map_one])
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
    Subgroup.card_map_of_injective hψ] at hcard
  omega

theorem not_pullDatum_threeA_odd [Finite K] [CharP K 2] {f : ℕ} (hf : Odd f)
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ¬ PullDatum (MulAut.conj z) := by
  rintro ⟨R, U, -, hnorm, -, h3, hUR, hU2, hUnc⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ⟨KS11Lie5Proof.d4T0 σ, KS11Lie5Proof.d4T0_mem σ⟩ with htdef
  obtain ⟨ht3', ht1'⟩ := d4T0_pow_three hσ3
  have ht3 : t ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact ht3')
  have ht1 : t ≠ 1 := fun h => ht1' (congrArg Subtype.val h)
  have hzt : Commute z t :=
    Subgroup.mem_centralizer_iff.mp (KS11Lie5Proof.d4T0_mem_centralizer σ) z hzS
  have htz : t ∉ Subgroup.zpowers z := fun h =>
    d4T0_not_mem_short hσ3 ((Subgroup.zpowers_le.mpr hzS) h)
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hot : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hdisj : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers t) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(Subgroup.zpowers z ⊓ Subgroup.zpowers t) ∣ 3 := by
      rw [← hot, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers z ⊓ Subgroup.zpowers t = Subgroup.zpowers t :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3', Nat.card_zpowers, hot])
      have hmem : t ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers t := by
        rw [heq]
        exact Subgroup.mem_zpowers t
      exact htz (Subgroup.mem_inf.mp hmem).1
  have hcomm : ∀ (a : Subgroup.zpowers z) (b : Subgroup.zpowers t),
      Commute ((Subgroup.zpowers z).subtype a) ((Subgroup.zpowers t).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hzt.zpow_left i).zpow_right j
  set φ := MonoidHom.noncommCoprod (Subgroup.zpowers z).subtype (Subgroup.zpowers t).subtype
    hcomm with hφdef
  have hφinj : Function.Injective φ := fun a b hab =>
    Subgroup.mul_injective_of_disjoint hdisj hab
  set F := φ.range with hFdef
  have hF9 : 9 ≤ Nat.card F := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hoz, hot]
  have hF3 : ∀ y ∈ F, y ^ 3 = 1 := by
    rintro _ ⟨p, rfl⟩
    have h1 : ∀ a : Subgroup.zpowers z, a ^ 3 = 1 := fun a => by
      rw [← hoz, ← Nat.card_zpowers]
      exact pow_card_eq_one'
    have h2 : ∀ b : Subgroup.zpowers t, b ^ 3 = 1 := fun b => by
      rw [← hot, ← Nat.card_zpowers]
      exact pow_card_eq_one'
    have hp : p ^ 3 = 1 := Prod.ext (by rw [Prod.pow_fst, Prod.fst_one]; exact h1 _)
      (by rw [Prod.pow_snd, Prod.snd_one]; exact h2 _)
    rw [← map_pow, hp, map_one]
  have hFz : ∀ y ∈ F, MulAut.conj z y = y := by
    rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
    rw [conj_apply_eq_iff]
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl z).zpow_right i).mul_right (hzt.zpow_right j)
  have hFR : F ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hnorm y (hFz y hy) r hr, fun hr => ?_⟩
    have hyinv : MulAut.conj z y⁻¹ = y⁻¹ := by rw [map_inv, hFz y hy]
    have h' := hnorm y⁻¹ hyinv _ hr
    have e : y⁻¹ * (y * r * y⁻¹) * y⁻¹⁻¹ = r := by group
    rwa [e] at h'
  have hFp : IsPGroup 3 F := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hF3 _ y.2)⟩
  obtain ⟨T, hTs, -, hFT⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_two (Q := ⊥) hFp h3 hFR bot_le IsPGroup.of_bot
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hT1 : T ≠ ⊥ := by
    obtain ⟨P, hP⟩ := Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hTs
    have hU1 : U ≠ ⊥ := fun h => hUnc (by rw [h]; infer_instance)
    have h2U : 2 ∣ Nat.card U := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hU1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
      rw [hn]
      exact dvd_pow_self 2 hn0
    have hP1 := P.ne_bot_of_dvd_card (h2U.trans (Subgroup.card_dvd_of_le hUR))
    rw [← hP]
    intro h
    exact hP1 ((Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).mp h)
  exact false_of_le_normalizer_of_odd hf hK hσ3 hF3 hF9 hTs.2.1 hT1 hFT

theorem not_pullDatum_threeB [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hσ3 : σ ^ 3 = 1)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ¬ PullDatum (MulAut.conj z) := by
  intro h
  have h3 : ¬ 3 ∣ 2 ^ f := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨hcomm, hord⟩ := KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ f) σ hK hσ h3 z hzS hz3 hz1
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    rw [hK]
    exact le_trans (by norm_num) (Nat.pow_le_pow_left h2 3)
  have hfixC : ∀ c, MulAut.conj z c = c →
      c ∈ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr ((conj_apply_eq_iff z c).mp hc).symm
  have hSfix : ∀ s ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, MulAut.conj z s = s := fun s hs =>
    (conj_apply_eq_iff z s).mpr (Subgroup.mem_centralizer_iff.mp hzS s hs).symm
  refine h.false_of_quasisimple _ hSfix (fun c hc s hs => ?_) (isQuasisimple_d4Short hσ3 hK4)
    (fun c hc hcS => ?_)
  · have hm := hcomm c (hfixC c hc) s (hfixC s (hSfix s hs))
    have e : c * s * c⁻¹ = c * s * c⁻¹ * s⁻¹ * s := by group
    rw [e]
    exact mul_mem hm hs
  · have hb := hord c (hfixC c hc) (Subgroup.mem_centralizer_iff.mpr fun s hs => (hcS s hs).symm)
    have he : Even ((2 ^ f) ^ 2) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
    have hodd : Odd ((2 ^ f) ^ 2 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity)) he odd_one
    exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hb)

end D4

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
