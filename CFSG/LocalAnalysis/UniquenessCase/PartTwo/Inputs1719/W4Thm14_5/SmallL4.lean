module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Module
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Klein
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.LieType.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Blueprint (LieModel)

theorem exists_sl4_mulEquiv_of_lieModel {X : Type} [Group X] {e : ℕ}
    (hS : LieModel X .PSL 4 2 e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 4) K) := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ := by
    rw [← LinearFlag.scalars_eq_center, eq_bot_iff]
    rintro A ⟨c, hc, hA⟩
    rw [Subgroup.mem_bot]
    have hc1 : (c : K) = 1 := by
      have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      have h : ((c : K) + 1) ^ 4 = 0 := by
        have hexp : ((c : K) + 1) ^ 4 = ((c : K) ^ 4 + 1) + 2 * (2 * (c : K) ^ 3 +
            3 * (c : K) ^ 2 + 2 * (c : K)) := by ring
        rw [hexp, h4, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
      exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.mp h)
    apply Subtype.ext
    change (A : Matrix (Fin 4) (Fin 4) K) = 1
    rw [hA, hc1, map_one]
  exact ⟨K, inferInstance, inferInstance, hK, ⟨φ.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot))⟩⟩

theorem k14_5SmallFor_l4 : K14_5SmallFor fun L _ e => LieModel L .PSL 4 2 e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have hne : n = e := nParam_eq_of_lieModel_psl4_parabolic hS hPL hpar hinf hN hn
  have he3 : 3 ≤ e := by omega
  obtain ⟨K, _, _, hK, ⟨ψ⟩⟩ := exists_sl4_mulEquiv_of_lieModel hS
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hKf : Fintype.card K = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := I) fun v => by
    rw [← pow_two]
    exact hI v
  let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W :=
    (subRep θ L).comp ψ.symm.toMonoidHom
  have hρ : ∀ (l : ↥L) (w : W), ρ (ψ l) w = binPsi θ (l : MulAut I) w := fun l w => by
    change subRep θ L (ψ.symm (ψ l)) w = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hirrL := subRep_isIrreducible θ le_rfl hirr
  have hirrρ : ρ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff] at hirrL ⊢
    refine ⟨hirrL.1, fun U hU => hirrL.2 U fun l u hu => ?_⟩
    have h := hU (ψ l) u hu
    rwa [hρ] at h
  have hsimpL : IsSimpleGroup ↥L := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hS
  let x₀ : Matrix.SpecialLinearGroup (Fin 4) K :=
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 1) (by decide) 1
  have hx₀2 : x₀ * x₀ = 1 := by
    apply Subtype.ext
    change Matrix.transvection (0 : Fin 4) 1 (1 : K) * Matrix.transvection 0 1 1 = 1
    rw [_root_.Matrix.transvection_mul_transvection_same (0 : Fin 4) 1 (by decide),
      CharTwo.add_self_eq_zero,
      _root_.Matrix.transvection_zero]
  have hx₀1 : x₀ ≠ 1 := by
    intro h
    have h01 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K) 0 1) h
    change Matrix.transvection (0 : Fin 4) 1 (1 : K) 0 1 =
      (1 : Matrix (Fin 4) (Fin 4) K) 0 1 at h01
    simp [Matrix.transvection] at h01
  have hevL : Even (Nat.card ↥L) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (ψ.symm x₀) = 2 := orderOf_eq_prime
      (by rw [pow_two, ← map_mul, hx₀2, map_one])
      (fun h => hx₀1 (by simpa using congrArg ψ h))
    exact even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard _)
  have hev : Even (Nat.card ↥X) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hevL).trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  have htc : ∃ x ∈ L, t * x ≠ x * t := by
    by_contra hcon
    push Not at hcon
    have h1 := eq_one_of_commute_of_isIrrOn hI hirr (by rw [pow_two]; exact htt) hcon
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hLodd : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N = ⊥ :=
    fun N hN hodd => eq_bot_of_odd_of_isSimpleGroup hevL N hN hodd
  obtain ⟨l, hl, k, hyL, hy1, hy2⟩ := exists_involution_pow_mul_conj hLodd (hXN htX) htt htc
  set y : MulAut I := (t * (l⁻¹ * t * l)) ^ k with hy
  have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  set t' : ↥X := ⟨t, htX⟩ with ht'def
  have hrkt : Module.finrank (ZMod 2) (LinearMap.range (subRep θ X t' - 1)) ≤ e + 1 := by
    have ht' : orderOf t' = 2 := by rw [ht'def, Subgroup.orderOf_mk]; exact ht2
    have h1 := finrank_quotient_fixSub_subRep θ X (zpowers t')
    rw [MonoidHom.map_zpowers, Excl147.fixSub_zpowers_eq_ker (subRep θ X) ht'] at h1
    have h2 := (LinearMap.ker (subRep θ X t' - 1)).finrank_quotient_add_finrank
    have h3 := LinearMap.finrank_range_add_finrank_ker (subRep θ X t' - 1)
    have h4 : rkIdx (fixV (zpowers (X.subtype t'))) = E3.mParam X := htm
    omega
  have hrky := finrank_range_pow_mul_conj_le (subRep θ X) t' ⟨l, hLX hl⟩ k
  have hyX : ((t' * ((⟨l, hLX hl⟩ : ↥X)⁻¹ * t' * ⟨l, hLX hl⟩)) ^ k : ↥X) =
      ⟨y, hLX hyL⟩ := Subtype.ext (by simp [hy, ht'def])
  rw [hyX] at hrky
  set g : Matrix.SpecialLinearGroup (Fin 4) K := ψ ⟨y, hyL⟩ with hg
  have hρg : ρ g = subRep θ X ⟨y, hLX hyL⟩ := by
    ext w
    rw [hg, hρ]
    rfl
  have hg2 : g * g = 1 := by
    rw [hg, ← map_mul, ← map_one ψ]
    exact congrArg ψ (Subtype.ext hy2)
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    have h' : (⟨y, hyL⟩ : ↥L) = 1 := ψ.injective (by rw [← hg, h, map_one])
    exact congrArg Subtype.val h'
  have hrk : Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) ≤ 2 * e + 2 := by
    rw [hρg]
    omega
  have hne' : ∃ g, ρ g ≠ 1 := by
    refine ⟨g, fun h => hg1 ?_⟩
    have h1 : subRep θ X ⟨y, hLX hyL⟩ = 1 := hρg ▸ h
    have h2 : (⟨y, hLX hyL⟩ : ↥X) = 1 := subRep_injective θ X (by rw [h1, map_one])
    have h3 : y = 1 := congrArg Subtype.val h2
    have h4 : (⟨y, hyL⟩ : ↥L) = 1 := Subtype.ext h3
    rw [hg, h4, map_one]
  obtain ⟨j, r, hj1, hj4, β, hβ⟩ := exists_extTwist_of_finrank_le he3 hKf ρ hirrρ hne' hg2 hg1 hrk
  have hβL : ∀ (l : ↥L) (w : W), β (binPsi θ (l : MulAut I) w) = extTwist 4 j r K (ψ l) *ᵥ β w :=
    fun l w => by rw [← hρ, hβ]
  have hSLn : IsSLn ↥L 4 e :=
    ⟨K, inferInstance, inferInstance, hK, ⟨ψ.trans (specialLinearGroupEquivStatedSL 4 K)⟩⟩
  refine Or.inl ⟨e, ?_, Or.inl hne⟩
  interval_cases j
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSLn,
      ⟨K, inferInstance, inferInstance, hK, realizes_natSL4_of_extTwist_one θ ψ r β hβL⟩⟩)))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨isOmegaPlus_six_of_mulEquiv hK ψ, by decide, K, inferInstance, inferInstance, hK,
        realizes_natOmegaPlus_of_extTwist_two θ ψ r β hβL⟩))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSLn,
      ⟨K, inferInstance, inferInstance, hK, realizes_natSL4_of_extTwist_three θ ψ r β hβL⟩⟩)))))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
