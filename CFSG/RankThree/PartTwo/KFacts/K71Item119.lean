module

public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.KFacts.K72L3Fix
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.GorensteinWalter
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix

@[expose] def slCongrOfRingEquiv {S S' : Type} [Field S] [Field S'] (n : ℕ) (φ : S ≃+* S') :
    SpecialLinearGroup (Fin n) S ≃* SpecialLinearGroup (Fin n) S' where
  toFun := SpecialLinearGroup.map φ.toRingHom
  invFun := SpecialLinearGroup.map φ.symm.toRingHom
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

@[expose] def psl2CongrOfRingEquiv {S S' : Type} [Field S] [Field S'] (φ : S ≃+* S') :
    PSL2 S ≃* PSL2 S' :=
  QuotientGroup.congr _ _ (slCongrOfRingEquiv 2 φ) (Subgroup.map_center_eq _)

theorem nonempty_eqLocus_congr {X Y : Type*} [Group X] [Group Y] (ε : X ≃* Y) (α : MulAut X) :
    Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id X) ≃*
      (MulAut.congr ε α).toMonoidHom.eqLocus (MonoidHom.id Y)) :=
  nonempty_eqLocus_mulEquiv ε α
    ((MulAut.congr ε α).toMonoidHom.eqLocus (MonoidHom.id Y)).subtype Subtype.val_injective
    fun y => by
      rw [Subgroup.range_subtype]
      rfl

theorem nonempty_eqLocus_mulEquiv_projSL_two {X : Type} [Group X] {p m : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p (3 * m)))
    {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id X) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p m)) := by
  set F := GaloisField p (3 * m)
  set ε : X ≃* PSL2 F := e.trans (Sec4.projSLEquivPSL F) with hε
  have hβ3 : MulAut.congr ε α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut (MulAut.congr ε α) := fun h => hout ((isInnerAut_congr ε α).mp h)
  obtain ⟨σ, hσ3, ⟨ι⟩⟩ := exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  obtain ⟨κ⟩ := nonempty_eqLocus_congr ε α
  have hF : Nat.card F = (p ^ m) ^ 3 := by
    rw [GaloisField.card p (3 * m) (by omega), ← pow_mul, mul_comm]
  have hS : Nat.card (fixedField σ) = p ^ m := card_fixedField_of_orderOf_eq_three hσ3 hF
  let φ : fixedField σ ≃+* GaloisField p m :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField σ) p m (by omega) hS
  exact ⟨(κ.trans ι).trans ((psl2CongrOfRingEquiv φ).trans
    (Sec4.projSLEquivPSL (GaloisField p m)).symm)⟩

theorem nonempty_sl3_mulEquiv_projSL {F : Type} [Field F] [Finite F] (hF : Nat.card F % 3 = 2) :
    Nonempty (SpecialLinearGroup (Fin 3) F ≃* CFSG.Assembly.RankThreeEven.projSL 3 F) := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 F
  exact ⟨(MulEquiv.ofBijective (proj 3 F) ⟨proj_three_injective hF, proj_surjective 3 F⟩).trans
    φ.symm⟩

theorem isoLThreeMinusPi_eqLocus {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    Sec8.IsoLThreeMinusPi (α.toMonoidHom.eqLocus (MonoidHom.id X)) 2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  have hpow : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  ·
    have hq₀ : 2 ^ n % 3 = 1 := by rw [← pow_three_mod_three, ← hpow, hq]
    left
    refine ⟨hq₀, ?_⟩
    set K := GaloisField 2 (2 * (3 * n))
    have h : UnitaryFieldData 2 (3 * n) K :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    obtain ⟨σ, hσ, τ, hτ⟩ :=
      exists_congr_eq_psuField_of_mulEquiv_unitaryPSU h hq hq2 (e.trans φ.symm) hα3 hout
    obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
    have hf₀n : f₀ = n := by omega
    subst hf₀n
    have h₀ : UnitaryFieldData 2 f₀ (fixedField σ) := ⟨Nat.prime_two, hf₀, hcard⟩
    have hinj : Function.Injective
        ((unitaryProj h 3).comp (suIncl h h₀ (bar_coe_fixedField h hf h₀))) :=
      (unitaryProj_three_injective h hq).comp (suIncl_injective h h₀ _)
    obtain ⟨eC⟩ := nonempty_eqLocus_mulEquiv τ α _ hinj fun y => by
      rw [hτ]
      exact mem_range_unitaryProj_comp_suIncl_iff h hq hf h₀ y
    set K₀ := GaloisField 2 (2 * f₀)
    have h₀' : UnitaryFieldData 2 f₀ K₀ := ⟨Nat.prime_two, hf₀, GaloisField.card 2 _ (by omega)⟩
    let ψ : fixedField σ ≃+* K₀ :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField σ) 2 (2 * f₀) (by omega) hcard
    have hSU : (StatedSU 3 (2 ^ f₀) (fixedField σ)).map
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) ψ).toMonoidHom =
        StatedSU 3 (2 ^ f₀) K₀ :=
      CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU ψ 3 (2 ^ f₀)
    let ρ : unitarySU 2 f₀ (fixedField σ) 3 ≃* unitarySU 2 f₀ K₀ 3 :=
      ((StatedSU 3 (2 ^ f₀) (fixedField σ)).equivMapOfInjective _
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) ψ).injective).trans
        (MulEquiv.subgroupCongr hSU)
    obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h₀'
    have hbij : Function.Bijective (unitaryProj h₀' 3) :=
      ⟨unitaryProj_three_injective h₀' hq₀, unitaryProj_surjective h₀' 3⟩
    exact ⟨((eC.trans ρ).trans (MulEquiv.ofBijective _ hbij)).trans φ₀⟩
  ·
    have hq₀ : 2 ^ n % 3 = 2 := by rw [← pow_three_mod_three, ← hpow, hq]
    right
    refine ⟨hq₀, ?_⟩
    set K := GaloisField 2 (3 * n)
    have hK : Nat.card K % 3 = 2 := by rwa [GaloisField.card 2 (3 * n) (by omega)]
    obtain ⟨σ, hσ, τ, hτ⟩ := exists_congr_eq_fieldAut_of_mulEquiv_projSL hK e hα3 hout
    have hinj : Function.Injective
        ((proj 3 K).comp (SpecialLinearGroup.map (fixedField σ).subtype)) :=
      (proj_three_injective hK).comp (sl_map_subtype_injective σ)
    obtain ⟨eC⟩ := nonempty_eqLocus_mulEquiv τ α _ hinj fun y => by
      rw [hτ]
      exact mem_range_proj_comp_map_iff hK σ y
    have hcardK : Nat.card K = (2 ^ n) ^ 3 := by
      rw [GaloisField.card 2 (3 * n) (by omega), hpow]
    have hS : Nat.card (fixedField σ) = 2 ^ n := card_fixedField_of_orderOf_eq_three hσ hcardK
    let ψ : fixedField σ ≃+* GaloisField 2 n :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField σ) 2 n (by omega) hS
    have hK₀ : Nat.card (GaloisField 2 n) % 3 = 2 := by
      rwa [GaloisField.card 2 n (by omega)]
    obtain ⟨ν⟩ := nonempty_sl3_mulEquiv_projSL hK₀
    exact ⟨(eC.trans (slCongrOfRingEquiv 3 ψ)).trans ν⟩

end CFSG.RankThree.PartTwo.KFacts
