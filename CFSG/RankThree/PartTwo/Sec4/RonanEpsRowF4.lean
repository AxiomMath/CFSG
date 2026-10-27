module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieOrders
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofKFacts
public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSixRee
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem two_lt_ordTwistedF4 {q : ℕ} (hq : 8 ≤ q) : 2 < CFSG.Open.ordTwistedF4 q := by
  unfold CFSG.Open.ordTwistedF4
  have h4 : 8 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h12 : 8 ^ 12 ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  norm_num at h4 h12
  have hA : 0 < q ^ 4 - 1 := by omega
  have hB : 0 < q - 1 := by omega
  have hC : 0 < q ^ 6 + 1 := by omega
  have hD : 0 < q ^ 3 + 1 := by omega
  calc 2 < q ^ 12 := by omega
    _ ≤ q ^ 12 * (q ^ 6 + 1) := Nat.le_mul_of_pos_right _ hC
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) := Nat.le_mul_of_pos_right _ hA
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) := Nat.le_mul_of_pos_right _ hD
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) :=
      Nat.le_mul_of_pos_right _ hB

theorem exists_noncomm_of_simple_card {X : Type} [Group X] [IsSimpleGroup X]
    (h2 : 2 ∣ Nat.card X) (hlt : 2 < Nat.card X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  haveI : IsMulCommutative X := ⟨⟨fun a b => hcomm a b⟩⟩
  have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp ‹IsSimpleGroup X›
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

theorem exists_quasisimple_central_three {Y : Type} [Group Y] {N : Subgroup Y} {F : Type}
    [Field F] [Finite F] {f : ℕ} (φ : N ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hodd : Odd f) :
    IsQuasisimple N ∧ ∃ z ∈ N, (∀ n ∈ N, n * z = z * n) ∧ orderOf z = 3 := by
  obtain ⟨hq, x, hxZ, hx1, hx3⟩ := Res4Seven.statedSU_three_facts hF hf hodd
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq, (φ.symm x : Y), (φ.symm x).2,
    ?_, ?_⟩
  · intro n hn
    have h1 := Subgroup.mem_center_iff.mp hxZ (φ ⟨n, hn⟩)
    have h2 : (⟨n, hn⟩ : N) * φ.symm x = φ.symm x * ⟨n, hn⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h1
    exact congrArg Subtype.val h2
  · have hz3 : (φ.symm x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hz1 : φ.symm x ≠ 1 :=
      fun h => hx1 (by rw [← MulEquiv.apply_symm_apply φ x, h, map_one])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply orderOf_eq_prime
    · exact congrArg Subtype.val hz3
    · exact fun h => hz1 (Subtype.ext h)

section F4


theorem noCfgSEps_reeGamma {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    [Finite (ReeTag.F4.reeGamma K a)] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    NoCfgSEps (ReeTag.F4.reeGamma K a) := by
  intro A σ J hc
  have hσ3 : σ ^ 3 = 1 := hc.pow_three
  have hZ : ∀ s : ReeTag.F4.reeGamma K a, (∀ t, s * t = t * s) → s = 1 := by
    intro s hs
    refine CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.eq_one_of_conj_eq_one
      hK ?_
    ext t
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [hs t, mul_inv_cancel_right]
  have hZT : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    exact hZ s fun t => (Subgroup.mem_center_iff.mp hs t).symm
  obtain ⟨-, -, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  by_cases hin : IsInnerAut σ
  ·
    obtain ⟨y, rfl⟩ := hin
    have hy3 : y ^ 3 = 1 := by
      have h3' : MulAut.conj (y ^ 3) = 1 := by rw [map_pow]; exact hσ3
      exact conj_injective_of_center_eq_bot hZT (by rw [h3', map_one])
    have hy1 : y ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := Sec8.ReeF4Conj2Proof.kF83ReeCentThree_holds a K ha hK y hyo
    have hKN : J ≤ inSubgroup perfectResidual
        (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
      have h := hc.le_perfectResidual
      rwa [RowV.autFix_conj_eq_centralizer] at h
    have hNC : inSubgroup perfectResidual
        (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) ≤
          autFix (MulAut.conj y) := by
      rw [RowV.autFix_conj_eq_centralizer]
      exact Subgroup.map_subtype_le _
    obtain ⟨hNq, z, hzN, hz, hzo⟩ := exists_quasisimple_central_three φ hF (by omega) ⟨a, rfl⟩
    exact hc.false_of_le_quasisimple_central hKN hNC hNq hzN hz hzo
  ·
    set p := Ψ.symm σ with hp
    have hσp : σ = MulAut.conj p.left * ReeTag.F4.reeGammaFieldAut K a p.right := by
      rw [← hΨ]
      exact (Ψ.apply_symm_apply σ).symm
    have hF1 : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
      have h1 := hΨ 1 1
      rw [show (⟨1, 1⟩ : ReeTag.F4.reeGamma K a ⋊[ReeTag.F4.reeGammaFieldAutHom K a] (K ≃+* K)) = 1
        from rfl, map_one, map_one, one_mul] at h1
      exact h1.symm
    have hβ3 : p.right ^ 3 = 1 := by
      have h1 : p ^ 3 = 1 := by
        apply Ψ.injective
        rw [map_pow, hp, Ψ.apply_symm_apply, hσ3, map_one]
      have h2 := congrArg (SemidirectProduct.rightHom) h1
      rwa [map_pow, map_one] at h2
    have hβ1 : p.right ≠ 1 := by
      intro h1
      apply hin
      rw [hσp, h1, hF1, mul_one]
      exact ⟨p.left, rfl⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hβ : orderOf p.right = 3 := orderOf_eq_prime hβ3 hβ1
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three
      p.right hβ σ hσ3 ⟨p.left, hσp⟩
    obtain ⟨b, -, hkcard, himg⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.largeRee_fixed_data_of_odd hK Nat.prime_three
        (by norm_num) p.right hβ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP (fixSubfield p.right) ReeTag.F4.prime := by
      have := Fintype.ofFinite (fixSubfield p.right)
      exact charP_of_card_eq_prime_pow (f := 2 * b + 1)
        (by rw [← Nat.card_eq_fintype_card, hkcard]; rfl)
    set γ := ReeTag.F4.reeGammaFieldAut K a p.right with hγ
    have eγ : Sec4.autFix γ ≃* ReeTag.F4.reeGamma (fixSubfield p.right) b :=
      (((MulEquiv.subgroupCongr (show Sec4.autFix γ = γ.toMonoidHom.eqLocus (MonoidHom.id _)
          from rfl)).trans
        ((γ.toMonoidHom.eqLocus (MonoidHom.id _)).equivMapOfInjective _
          (Subgroup.subtype_injective _))).trans (MulEquiv.subgroupCongr himg)).trans
        ((ReeTag.F4.reeGamma (fixSubfield p.right) b).equivMapOfInjective _
          (baseChangeGL_injective (fixSubfield p.right).subtype)).symm
    have eσ : Sec4.autFix σ ≃* ReeTag.F4.reeGamma (fixSubfield p.right) b := by
      rw [hg]
      exact (autFixConjEquiv (MulAut.conj g) γ).trans eγ
    have hcardC : Nat.card (Sec4.autFix σ) = CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) :=
      Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b (fixSubfield p.right) hkcard eσ
    have hJC : Nat.card J ∣ Nat.card (Sec4.autFix σ) := Subgroup.card_dvd_of_le hc.le_autFix
    rcases Nat.eq_zero_or_pos b with rfl | hb
    ·
      have hdvd : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ 35942400 := by
        have h1 : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
        rw [hcardC] at hJC
        simpa [CFSG.Open.ordTwistedF4] using h1.trans hJC
      exact not_isTypeEpsCube_of_dvd (B := 3) (by norm_num) hdvd (by norm_num)
        (by decide +kernel) (by decide +kernel) (isTypeEpsCube_of_cfgSEps hc)
    ·
      haveI hCs : IsSimpleGroup (ReeTag.F4.reeGamma (fixSubfield p.right) b) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
      haveI hCs' : IsSimpleGroup (Sec4.autFix σ) := eσ.isSimpleGroup
      have h8 : 8 ≤ 2 ^ (2 * b + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ∣ Nat.card (Sec4.autFix σ) := by
        rw [hcardC]
        unfold CFSG.Open.ordTwistedF4
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _) _) _
      have h2' : 2 < Nat.card (Sec4.autFix σ) := by
        rw [hcardC]
        exact two_lt_ordTwistedF4 h8
      obtain ⟨hQ, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
        (exists_noncomm_of_simple_card h2 h2')
      have hcube := hc.isTypeEpsCube_of_le hc.le_autFix le_rfl hQ hZ
      exact not_isTypeEpsCube_of_card_f4_even (m := 2 * b + 1) (by omega)
        (by rw [hcardC]; simp only [CFSG.Open.ordTwistedF4, mul_assoc]) hcube

theorem noCfgSEps_of_reeGamma {S : Type} [Group S] [Finite S] {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (τ : S ≃* ReeTag.F4.reeGamma K a) : NoCfgSEps S := by
  haveI : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv S τ.toEquiv
  exact (noCfgSEps_reeGamma ha hK).of_mulEquiv τ

theorem rowSEpsOf_seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  intro m hm S _ _ hs hna ⟨e⟩
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hm e
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e'⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  exact noCfgSEps_of_reeGamma ha hK e'

end F4

end CFSG.RankThree.PartTwo.Sec4.RonanEps
