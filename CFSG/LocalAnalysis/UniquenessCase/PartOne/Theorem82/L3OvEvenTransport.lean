module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvDefs
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReducePSL
import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Reduction
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open scoped MatrixGroups
open Matrix

theorem l3OvAlt_map_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (Y K : Subgroup G) :
    L3OvAlt (Y.map e.toMonoidHom) (K.map e.toMonoidHom) ↔ L3OvAlt Y K := by
  constructor
  · rintro ⟨g', hg'Y, r, hr, hr5, hord, hrdvd, hcomm⟩
    obtain ⟨g, hgY, rfl⟩ := Subgroup.mem_map.mp hg'Y
    refine ⟨g, hgY, r, hr, hr5, ?_, ?_, ?_⟩
    · have hord' : orderOf (e g) = r := hord
      rwa [MulEquiv.orderOf_eq] at hord'
    · rwa [Subgroup.card_map_of_injective e.injective] at hrdvd
    · intro k hk
      have hk' : e k ∈ K.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hk
      have h := hcomm (e k) hk'
      rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv] at h
      obtain ⟨x, hxK, hx⟩ := Subgroup.mem_map.mp h
      have hx' : e.toMonoidHom x = e.toMonoidHom (g * k * g⁻¹ * k⁻¹) := by
        have hx'' : e.toMonoidHom x =
            e.toMonoidHom g * e.toMonoidHom k * (e.toMonoidHom g)⁻¹ *
              (e.toMonoidHom k)⁻¹ := hx
        simpa only [map_mul, map_inv] using hx''
      exact (e.injective hx') ▸ hxK
  · rintro ⟨g, hgY, r, hr, hr5, hord, hrdvd, hcomm⟩
    refine ⟨e g, Subgroup.mem_map_of_mem e.toMonoidHom hgY, r, hr, hr5, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]
      exact hord
    · rwa [Subgroup.card_map_of_injective e.injective]
    · intro k' hk'
      obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hk'
      change e.toMonoidHom g * e.toMonoidHom k * (e.toMonoidHom g)⁻¹ *
        (e.toMonoidHom k)⁻¹ ∈ CFSG.Open.pCoreOf 2 (Subgroup.map e.toMonoidHom K)
      rw [show e.toMonoidHom g * e.toMonoidHom k * (e.toMonoidHom g)⁻¹ *
          (e.toMonoidHom k)⁻¹ = e.toMonoidHom (g * k * g⁻¹ * k⁻¹) by
        simp only [map_mul, map_inv],
        CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
      exact Subgroup.mem_map_of_mem e.toMonoidHom (hcomm k hkK)

theorem exists_mulAut_eq_zNF {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) {u : SL(3, F)} (hu : orderOf u = 3) :
    ∃ c : MulAut SL(3, F), c u = zNF F := by
  have hnotdvd : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hF]
    intro hd
    obtain ⟨k, hk⟩ := hd
    have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
    have hmod : 2 ^ f % 3 = 2 := by
      obtain ⟨m, rfl⟩ := hf
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : 2 ^ f % 3 = 1 := by
      rw [show 2 ^ f = 3 * k + 1 by omega, Nat.add_mod, Nat.mul_mod]
      omega
    omega
  have hu3 : u ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    omega
  have hus : u ∉ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F := by
    rw [CFSG.AGLEmbedding.ToralReduce.scalars_eq_bot_of_not_dvd hnotdvd]
    exact fun h => hu1 (Subgroup.mem_bot.mp h)
  obtain ⟨htr, -⟩ := CFSG.AGLEmbedding.LinearThreeKit.trace_eq_zero_of_pow_three
    (CFSG.AGLEmbedding.LinearThreeKit.coe_pow_eq_one hu3) u.prop
    (CFSG.AGLEmbedding.LinearThreeKit.ne_smul_one_of_notMem_scalars hus)
  obtain ⟨x, hx0, hux⟩ :=
    CFSG.AGLEmbedding.LinearThreeKit.exists_mulVec_eq_smul_of_pow_three
      (CFSG.AGLEmbedding.LinearThreeKit.coe_pow_eq_one hu3) u.prop
      (CFSG.AGLEmbedding.LinearThreeKit.ne_smul_one_of_notMem_scalars hus) (one_pow 3)
  have hfl : CFSG.AGLEmbedding.LinearThreeKit.IsFixedLine 3 u x :=
    CFSG.AGLEmbedding.ToralReduce.isFixedLine_of_fixed (by decide)
      CFSG.AGLEmbedding.ToralReduce.three_ne_zero_of_charTwo hu3 hu1 hx0
      (by simpa using hux)
  obtain ⟨w, -, hli, huw2, -⟩ := hfl.exists_normalBasis
  have hUuw : (u : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      (-1 : F) • w + (-1 : F) • ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
    rw [huw2, htr]
    module
  let b : Fin 3 → Fin 3 → F := ![w, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ w, x]
  have hb : LinearIndependent F b := by
    have hli' := hli.comp (![1, 2, 0] : Fin 3 → Fin 3)
      (by decide : Function.Injective (![1, 2, 0] : Fin 3 → Fin 3))
    convert hli' using 1
    ext i
    fin_cases i <;> rfl
  let P : Matrix (Fin 3) (Fin 3) F := (Matrix.of b)ᵀ
  have hP : IsUnit P := by
    simpa [P] using CFSG.AGLEmbedding.LinearThreeKit.isUnit_transpose_of hb
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hUP : (u : Matrix (Fin 3) (Fin 3) F) * P =
      P * (zNF F : Matrix (Fin 3) (Fin 3) F) := by
    rw [CFSG.AGLEmbedding.LinearThreeKit.mul_transpose_of_iff]
    intro j
    fin_cases j <;> simp [b, P, zNF, hux, hUuw, Fin.sum_univ_three]
  let A : GL (Fin 3) F := (Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet.ne_zero)⁻¹
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A, ?_⟩
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
  have hA : (A : Matrix (Fin 3) (Fin 3) F) = P⁻¹ := by
    simp [A, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Units.val_inv_eq_inv_val]
  have hAinv : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = P := by
    simp [A, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Units.val_inv_eq_inv_val]
  rw [hA, hAinv]
  calc P⁻¹ * (u : Matrix (Fin 3) (Fin 3) F) * P
      = P⁻¹ * ((u : Matrix (Fin 3) (Fin 3) F) * P) := by rw [Matrix.mul_assoc]
    _ = P⁻¹ * (P * (zNF F : Matrix (Fin 3) (Fin 3) F)) := by rw [hUP]
    _ = (P⁻¹ * P) * (zNF F : Matrix (Fin 3) (Fin 3) F) := by rw [Matrix.mul_assoc]
    _ = (zNF F : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.nonsing_inv_mul _ hPdet, Matrix.one_mul]

theorem l3Overgroup_psl_two (hM : L3OvMatrix) {X : Type} [Group X] [Finite X] {f : ℕ}
    (hL : CFSG.Blueprint.LieModel X .PSL 3 2 f) (hf : 2 ^ f % 3 = 2) {Z Y K : Subgroup X}
    (hZ : Nat.card Z = 3) (hZY : Subgroup.normalizer (Z : Set X) ≤ Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set X)) (hKK : ⁅K, K⁆ = K) (hZK : Z ≤ K)
    (hQ : CFSG.Open.pCoreOf 2 K ≠ ⊥) : L3OvAlt Y K := by
  obtain ⟨F, hField, hFinite, hcard, ⟨eX⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  letI : Field F := hField
  letI : Finite F := hFinite
  have hnotdvd : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hcard]
    intro hd
    obtain ⟨k, hk⟩ := hd
    have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
    have h2 : 2 ^ f % 3 = 1 := by
      rw [show 2 ^ f = 3 * k + 1 by omega, Nat.add_mod, Nat.mul_mod]
      omega
    omega
  letI : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
  have hfold : Odd f := by
    rcases Nat.even_or_odd f with he | ho
    · exfalso
      have h4all : ∀ m : ℕ, 4 ^ m % 3 = 1 := by
        intro m
        induction m with
        | zero => norm_num
        | succ j ih => simp [pow_succ, Nat.mul_mod, ih]
      obtain ⟨m, hm⟩ := he
      rw [hm, show m + m = 2 * m by omega, pow_mul] at hf
      change 4 ^ m % 3 = 2 at hf
      rw [h4all m] at hf
      norm_num at hf
    · exact ho
  let eP : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F ≃* SL(3, F) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.AGLEmbedding.ToralReduce.scalars_eq_bot_of_not_dvd hnotdvd)).trans
      QuotientGroup.quotientBot
  let e0 : X ≃* SL(3, F) := eX.trans eP
  have h3dvd : 3 ∣ Nat.card Z := by rw [hZ]
  obtain ⟨uZ, huZorder⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 h3dvd
  have huZ1 : uZ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huZorder
    omega
  have horderX : orderOf (uZ : X) = 3 := (Subgroup.orderOf_coe uZ).trans huZorder
  have hZtop : Z = Subgroup.zpowers (uZ : X) := by
    have hle : Subgroup.zpowers (uZ : X) ≤ Z :=
      Subgroup.zpowers_le.mpr (uZ : Z).2
    have hcard' : Nat.card Z ≤ Nat.card (Subgroup.zpowers (uZ : X)) := by
      rw [Nat.card_zpowers, horderX, hZ]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard').symm
  obtain ⟨c, hc⟩ := exists_mulAut_eq_zNF hcard hfold
    (u := e0 (uZ : X)) (by rw [MulEquiv.orderOf_eq, horderX])
  let ψ : X ≃* SL(3, F) := e0.trans c
  have hψu : ψ (uZ : X) = zNF F := by
    rw [MulEquiv.trans_apply]
    exact hc
  have hmapZ : Z.map ψ.toMonoidHom = Subgroup.zpowers (zNF F) := by
    rw [hZtop, MonoidHom.map_zpowers]
    change Subgroup.zpowers (ψ (uZ : X)) = Subgroup.zpowers (zNF F)
    rw [hψu]
  have hNY : Subgroup.normalizer (Subgroup.zpowers (zNF F) : Set (SL(3, F))) ≤
      Y.map ψ.toMonoidHom := by
    rw [← hmapZ, ← Subgroup.map_equiv_normalizer_eq Z ψ]
    exact Subgroup.map_mono hZY
  have hYK' : Y.map ψ.toMonoidHom ≤
      Subgroup.normalizer ((K.map ψ.toMonoidHom : Subgroup SL(3, F)) :
        Set (SL(3, F))) := by
    rw [← Subgroup.map_equiv_normalizer_eq K ψ]
    exact Subgroup.map_mono hYK
  have hKK' : ⁅K.map ψ.toMonoidHom, K.map ψ.toMonoidHom⁆ = K.map ψ.toMonoidHom := by
    rw [← Subgroup.map_commutator K K ψ.toMonoidHom, hKK]
  have hZK' : zNF F ∈ K.map ψ.toMonoidHom := by
    have hmem : zNF F ∈ Z.map ψ.toMonoidHom :=
      hmapZ ▸ Subgroup.mem_zpowers (zNF F)
    exact Subgroup.map_mono hZK hmem
  have hQ' : CFSG.Open.pCoreOf 2 (K.map ψ.toMonoidHom) ≠ ⊥ := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    intro hbot
    exact hQ ((Subgroup.map_eq_bot_iff_of_injective (CFSG.Open.pCoreOf 2 K) ψ.injective).mp
      hbot)
  have hres := hM F f hcard hfold (Y.map ψ.toMonoidHom) (K.map ψ.toMonoidHom)
    hNY hYK' hKK' hZK' hQ'
  exact (l3OvAlt_map_iff ψ Y K).mp hres

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
