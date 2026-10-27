module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU5Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU5Module
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.Blueprint (LieModel)

theorem k14_5SmallFor_u5 : K14_5SmallFor fun L _ e => e = 2 ∧ IsU5 L 2 := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  obtain ⟨-, hS⟩ := hS
  classical
  exfalso
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn4 : n = 4 := nParam_eq_four_of_isU5_two hS hPL hN hn
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (show Nat.card K = 2 ^ 4 by rw [hK]; norm_num)
  let e₀ : SU (unitaryInvolution K 2 2) 5 ≃* ↥(StatedSU 5 (2 ^ 2) K) := suToStated hK 5
  let π : SU (unitaryInvolution K 2 2) 5 →* ↥L :=
    (φ.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp e₀.toMonoidHom
  have hπs : Function.Surjective π := φ.symm.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e₀.surjective)
  have hπ1 : ∀ g, π g = 1 ↔ (e₀ g : ↥(StatedSU 5 (2 ^ 2) K)) ∈
      (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K) := fun g => by
    change φ.symm (QuotientGroup.mk (e₀ g)) = 1 ↔ _
    rw [map_eq_one_iff φ.symm φ.symm.injective, QuotientGroup.eq_one_iff]
  have hπc : ∀ (c : Kˣ) (hc : GeneralLinearGroup.scalar (Fin 5) c ∈
      SU (unitaryInvolution K 2 2) 5), π ⟨_, hc⟩ = 1 := by
    intro c hc
    rw [hπ1, Subgroup.mem_subgroupOf]
    refine ⟨c, ?_⟩
    change GeneralLinearGroup.scalar (Fin 5) c =
      wittMat hK 5 * GeneralLinearGroup.scalar (Fin 5) c * (wittMat hK 5)⁻¹
    rw [(GeneralLinearGroup.scalar_commute (n := Fin 5) c (wittMat hK 5)).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := I) fun v => by
    rw [← pow_two]
    exact hI v
  let ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 2) 5) W := (subRep θ L).comp π
  have hirrL := subRep_isIrreducible θ le_rfl hirr
  have hirrρ : ρ.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff] at hirrL ⊢
    refine ⟨hirrL.1, fun U hU => hirrL.2 U fun l u hu => ?_⟩
    obtain ⟨g, rfl⟩ := hπs l
    exact hU g u hu
  have hsimpL : IsSimpleGroup ↥L :=
    uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) hS
  have hneρ : ∃ g, ρ g ≠ 1 := by
    obtain ⟨l, hl1⟩ := exists_ne (1 : ↥L)
    obtain ⟨g, rfl⟩ := hπs l
    exact ⟨g, fun h => hl1 (subRep_injective θ L (h.trans (map_one _).symm))⟩
  have hscalρ : ∀ (c : Kˣ) (hc : GeneralLinearGroup.scalar (Fin 5) c ∈
      SU (unitaryInvolution K 2 2) 5), ρ ⟨_, hc⟩ = 1 := fun c hc => by
    change subRep θ L (π ⟨_, hc⟩) = 1
    rw [hπc c hc, map_one]
  have hcardL : Nat.card ↥L = 53443952640000 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_four
      (CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide))
  have hevL : Even (Nat.card ↥L) := by
    rw [hcardL]
    decide
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
  have hrkt : Module.finrank (ZMod 2) (LinearMap.range (subRep θ X t' - 1)) ≤ 5 := by
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
  obtain ⟨x₀, hx₀⟩ := hπs ⟨y, hyL⟩
  have hx₀2 : π (x₀ * x₀) = 1 := by
    rw [map_mul, hx₀]
    exact Subtype.ext hy2
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp ((hπ1 _).mp hx₀2)
  have hc5 : c ^ 5 = 1 := by
    refine CFSG.GroupTheory.WeirSylow.pow_eq_one_of_scalar_mem_statedSL ?_
    rw [hc]
    exact CFSG.Open.StatedAPI.statedSU_le_statedSL 5 (2 ^ 2) K (e₀ (x₀ * x₀)).2
  set x := x₀ ^ 5 with hxdef
  have hx : x * x = 1 := by
    apply e₀.injective
    have h1 : x * x = (x₀ * x₀) ^ 5 := by
      rw [hxdef, ← pow_add, ← sq, ← pow_mul]
    rw [h1, map_pow, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc5, map_one]
    rfl
  have hπx : π x = ⟨y, hyL⟩ := by
    rw [hxdef, map_pow, hx₀]
    have hy2' : (⟨y, hyL⟩ : ↥L) ^ 2 = 1 := by
      rw [sq]
      exact Subtype.ext hy2
    rw [show (5 : ℕ) = 2 * 2 + 1 by rfl, pow_succ, pow_mul, hy2', one_pow, one_mul]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hy1
    have := congrArg Subtype.val (hπx.symm.trans (by rw [h1, map_one]) : (⟨y, hyL⟩ : ↥L) = 1)
    exact this
  have h11 := eleven_le_finrank_range_su54 hK ρ hirrρ hneρ hscalρ hx hx1
  have hρx : ρ x = subRep θ X ⟨y, hLX hyL⟩ := by
    ext w
    change subRep θ L (π x) w = _
    rw [hπx]
    rfl
  rw [hρx] at h11
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
