module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofField
import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofUniFix

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Item424Res3

theorem isFieldCent424_of_psu {X : Type} [Group X] {F : Type} [Field F] {m : ℕ}
    (hF : UnitaryFieldData 2 (3 * m) F) (hm : Even m) (e : X ≃* unitaryPSU hF 3) :
    IsFieldCent424 X := by
  have hm1 : 1 ≤ m := by have := hF.one_le; omega
  have h31 : 2 ^ (3 * m) % 3 = 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, show 3 * (k + k) = 2 * (3 * k) by ring, pow_mul, Nat.pow_mod]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hF.finite
  set K₀ := GaloisField 2 (2 * (3 * m))
  have hK₀ : UnitaryFieldData 2 (3 * m) K₀ :=
    ⟨Nat.prime_two, hF.one_le, GaloisField.card 2 _ (by omega)⟩
  let φ : F ≃+* K₀ :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 (2 * (3 * m)) (by omega) hF.card
  let E : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * m)) F)
      ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * m)) K₀) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 _)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hK₀
  exact Or.inr ⟨m, hm1, Or.inl ⟨h31, ⟨e.trans ((unitaryPSUEquiv hF (by norm_num)).trans
    (E.trans ((unitaryPSUEquiv hK₀ (by norm_num)).symm.trans ψ)))⟩⟩⟩

theorem orderOf_eq_three_of_conj_psu {p f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData p f F}
    {d : MulAut (unitaryPSU h 3)} {σ : F ≃+* F} (hφ1 : KFacts.psuField h σ ≠ 1)
    (h3 : (d * KFacts.psuField h σ * d⁻¹) ^ 3 = 1) : orderOf σ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [conj_pow, conj_eq_one_iff, ← map_pow] at h3
  have hσ3 : σ ^ 3 = 1 :=
    (KFacts.eq_one_of_psuConj_mul_psuField_eq_one (h := h) 1 (σ ^ 3)
      (by rw [map_one, one_mul, h3])).1
  refine orderOf_eq_prime hσ3 fun h1 => hφ1 ?_
  rw [h1, map_one]

end Item424Res3

open Item424Res3

theorem k424FieldCentUnitary : K424FieldCentUnitary := by
  intro G _ _ L K c p f F _ hF hq hind hc3 hK hT
  have := hF.finite
  rcases hind with ⟨e, hcN, hk⟩ | ⟨e, hcN, hk⟩
  ·
    obtain ⟨φ, hφ, hφ1, d, -, hα⟩ := hk
    obtain ⟨σ, rfl⟩ := hφ
    have hHas := (Item424Res2.hasType424_fixSub_of_mem hcN hc3 hK hT).of_mulEquiv
      (Sec11.KS11Lie2Proof.fixSubCongr e (Item426.thetaAut L hcN))
    have hα' : MulAut.congr e (Item426.thetaAut L hcN) = d * KFacts.psuField hF σ * d⁻¹ := hα
    rw [hα'] at hHas
    have hσ3 : orderOf σ = 3 := orderOf_eq_three_of_conj_psu hφ1 (by
      rw [← hα]
      exact KFacts.inducedAutHom_pow_eq_one L e hcN hc3)
    obtain ⟨hp, m, hfm, hm⟩ := hasType424_psuField_imp hσ3 (hasType424_fixSub_of_conj hHas)
    subst hp
    subst hfm
    exact isFieldCent424_of_psu hF hm e
  ·
    obtain ⟨φ, hφ, hφ1, d, hd, hα⟩ := hk
    obtain ⟨σ, rfl⟩ := hφ
    obtain ⟨H, rfl⟩ := hd
    have : Group.IsPerfect (unitarySU p f F 3) := KFacts.isPerfect_unitarySU_three hF hq
    set β := KFacts.inducedAutHom L e ⟨c, hcN⟩ with hβ
    have hγ : MulAut.congr (KFacts.suCenterEquiv hF hq) (KFacts.centerDescend _
        (KFacts.suConj hF H * KFacts.suField hF σ * (KFacts.suConj hF H)⁻¹)) =
        MulAut.congr (KFacts.suCenterEquiv hF hq) (KFacts.centerDescend _ β) := by
      rw [hα, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
        Sec4.congr_centerDescend_suConj hF hq, Sec4.congr_centerDescend_suField hF hq]
    have hγ' := (MulAut.congr (KFacts.suCenterEquiv hF hq)).injective hγ
    have hlift : β = KFacts.suConj hF H * KFacts.suField hF σ * (KFacts.suConj hF H)⁻¹ := by
      apply Sec4.mulAut_eq_of_inv_mul_mem_center
      intro g
      have h1 := congrArg (fun τ : MulAut (unitarySU p f F 3 ⧸ Subgroup.center _) =>
        τ (g : unitarySU p f F 3 ⧸ Subgroup.center _)) hγ'
      simp only [KFacts.centerDescend_mk] at h1
      exact QuotientGroup.eq.mp h1
    have hHas := (Item424Res2.hasType424_fixSub_of_mem hcN hc3 hK hT).of_mulEquiv
      (Sec11.KS11Lie2Proof.fixSubCongr e (Item426.thetaAut L hcN))
    have hβ' : MulAut.congr e (Item426.thetaAut L hcN) =
        KFacts.suConj hF H * KFacts.suField hF σ * (KFacts.suConj hF H)⁻¹ := hlift
    rw [hβ'] at hHas
    have hσ3 : orderOf σ = 3 := orderOf_eq_three_of_conj_psu hφ1 (by
      rw [← hα, ← map_pow, ← map_pow, KFacts.inducedAutHom_pow_eq_one L e hcN hc3, map_one,
        map_one])
    obtain ⟨hp, m, hfm, hm⟩ := hasType424_suField_imp hσ3 (hasType424_fixSub_of_conj hHas)
    subst hp
    subst hfm
    have h31 : 2 ^ (3 * m) % 3 = 1 := by
      obtain ⟨k, hk⟩ := hm
      rw [hk, show 3 * (k + k) = 2 * (3 * k) by ring, pow_mul, Nat.pow_mod]
      norm_num
    exact isFieldCent424_of_psu hF hm (e.trans (MulEquiv.ofBijective (unitaryProj hF 3)
      ⟨KFacts.unitaryProj_three_injective hF h31, unitaryProj_surjective hF 3⟩))

end CFSG.RankThree.PartTwo.Sec4
