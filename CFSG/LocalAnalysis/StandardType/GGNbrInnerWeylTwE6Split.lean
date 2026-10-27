module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitEmbed
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameGen
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLargeF4
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

section Main

theorem sylowTorus_recipeR_split {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    SylowTorus (TwE6Delta.RecipeR K n) p 4 := by
  obtain ⟨σ, hσ, ⟨e⟩⟩ := exists_mulEquiv_recipeR_twistedE6RootGroup hn hK
  have hpq : ¬ p ∣ 2 ^ n := by
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hmod : ((2 ^ n : ℕ) : ZMod p) = 1 := by
    have h1 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ n - 1) p).2 hpn
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.cast_sub h2n, Nat.cast_one] at h1
    exact sub_eq_zero.mp h1
  have he : orderOf (((2 ^ n : ℕ)) : ZMod p) = 1 := by rw [hmod, orderOf_one]
  exact (ExcFrames.sylowTorus_twistedE6_one (ℓ := 2) (f := n) Nat.prime_two hn K hK σ hσ
    hp hp5 hpq he).of_mulEquiv e.symm

theorem ggSL2Center_eq_bot_of_charTwo {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (SL2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, hr2, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 2) (R := K)).mp hx
  have hr1 : r = 1 := by
    have h2 : r ^ 2 = 1 := by simpa using hr2
    have h : (r - 1) ^ 2 = 0 := by
      have h3 : (r - 1) ^ 2 = (2 : K) * (1 - r) := by linear_combination h2
      rw [h3, CharTwo.two_eq_zero, zero_mul]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hr, hr1]
  exact map_one (Matrix.scalar (Fin 2))

theorem ggSCNoLine_recipeR_split {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) (r : ℕ) :
    GGSCNoLine p r (TwE6Delta.RecipeR K n) := by
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, _, _, _, ι, hk, hι⟩ := exists_injective_f4_recipeR hn hK
  have hpk : p ∣ Nat.card k - 1 := by rw [hk]; exact hpn
  have := TwE6Delta.finite_recipeR (K := K) hK
  obtain ⟨s, m, hs, hm⟩ := exists_order_p_inverting_sl2_split hp hp2 hpk
  have hu : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h
    have h3 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hval : (-1 : ZMod p).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hn' : m * s * m⁻¹ = s ^ (-1 : ZMod p).val := by
    rw [hm, hval]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, ← hs]
    exact pow_orderOf_eq_one s
  have hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center (SL2 k)) := by
    rw [ggSL2Center_eq_bot_of_charTwo]
    exact disjoint_bot_right
  refine ggSCNoLine_of_sylowTorus_frameGen hp hp2 (-1) hu s m hs hn' hZ
    (sylowTorus_recipeR_split hn hK hp hp5 hpn) (fun i => ι.comp (TableBF4Two.rho k i))
    (fun i => hι.comp (TableBF4Two.rho_injective i))
    (fun i j hij A B => (TableBF4Two.commute_rho hij A B).map ι) (fun i => ?_) r
  obtain ⟨j, hji, g, hg⟩ := ExcPlusLargeF4.exists_conj_rho_F4 (K := k) i
  refine ⟨j, hji, ι g, 1, one_ne_zero, ?_⟩
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  simp only [MonoidHom.comp_apply, h1, pow_one]
  rw [← map_inv, ← map_mul, ← map_mul, hg]

theorem ggTorusNoLine_twE6Dvd_largePrime {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusNoLine p 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  exact ggTorusNoLine_of_scNoLine hp (TwE6Delta.center_recipeR_eq_bot hn hK)
    (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ hφ hφp)
    (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
    (ggSCNoLine_recipeR_split hn hK hp hp5 hpn 4)

end Main

end CFSG.StandardType

end
