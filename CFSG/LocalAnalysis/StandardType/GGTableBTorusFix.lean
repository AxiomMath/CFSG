module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ringAut_apply_eq_of_pow_fixes {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {σ : K ≃+* K}
    {c : ℕ} {ζ : K} (hζ1 : ζ ≠ 1) (hζ : ζ ^ p = 1) (hfix : (σ ^ p ^ c) ζ = ζ) {x : K}
    (hx : x ^ p = 1) : σ x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζord : orderOf ζ = p := orderOf_eq_prime hζ hζ1
  have hprim : IsPrimitiveRoot ζ p :=
    IsPrimitiveRoot.mk hζ fun l hl => by
      rw [← hζord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hl
  obtain ⟨k, -, hσζ⟩ :=
    IsPrimitiveRoot.eq_pow_of_pow_eq_one hprim (by rw [← map_pow σ.toRingHom, hζ, map_one])
  have hpow : ∀ m : ℕ, (σ ^ m) ζ = ζ ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', RingAut.mul_apply, ih]
      change σ.toRingHom (ζ ^ (k ^ m)) = ζ ^ (k ^ (m + 1))
      rw [map_pow σ.toRingHom, ← hσζ, ← pow_mul, ← pow_succ']
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · exfalso
      have h1 : σ.toRingHom ζ = σ.toRingHom 1 := by
        rw [← hσζ, hk0, pow_zero, map_one]
      exact hζ1 (σ.injective h1)
    · exact hk
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have hpow_pos : 1 ≤ k ^ (p ^ c) := one_le_pow₀ hk_pos
  have hfixζ : ζ ^ (k ^ (p ^ c)) = ζ := by rw [← hpow (p ^ c), hfix]
  have hdiv1 : p ∣ k ^ (p ^ c) - 1 := by
    have h2 : ζ ^ (k ^ (p ^ c) - 1) = 1 := by
      have h3 : ζ ^ (k ^ (p ^ c) - 1) * ζ = 1 * ζ := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hpow_pos, hfixζ]
      exact mul_right_cancel₀ hζ0 h3
    exact (hprim.pow_eq_one_iff_dvd _).mp h2
  have hfermat : (k : ZMod p) ^ (p ^ c) = (k : ZMod p) := by
    have h : ∀ n : ℕ, (k : ZMod p) ^ (p ^ n) = (k : ZMod p) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
    exact h c
  have hmod1 : k ^ (p ^ c) ≡ 1 [MOD p] := by
    have h : ((k ^ (p ^ c) - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (k ^ (p ^ c) - 1) p).mpr hdiv1
    rw [Nat.cast_sub hpow_pos, Nat.cast_one, sub_eq_zero] at h
    exact (ZMod.natCast_eq_natCast_iff (k ^ (p ^ c)) 1 p).mp (by simpa using h)
  have hmod2 : k ^ (p ^ c) ≡ k [MOD p] := by
    have h : ((k ^ (p ^ c) : ℕ) : ZMod p) = ((k : ℕ) : ZMod p) := by
      rw [Nat.cast_pow, hfermat]
    exact (ZMod.natCast_eq_natCast_iff (k ^ (p ^ c)) k p).mp h
  have hk1 : k ≡ 1 [MOD p] := (hmod1.symm.trans hmod2).symm
  have hσζ' : σ.toRingHom ζ = ζ := by
    have hζk : ζ ^ k = ζ ^ 1 := pow_eq_pow_of_modEq hk1 hζ
    rw [← hσζ, hζk, pow_one]
  obtain ⟨i, -, hi⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hprim hx
  rw [← hi]
  change σ.toRingHom (ζ ^ i) = ζ ^ i
  rw [map_pow σ.toRingHom, hσζ']

theorem entrywiseAdjointAut_apply_of_mem_torusPow
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) {σ : K ≃+* K} {c : ℕ}
    (hσ : (entrywiseAdjointAut τ σ) ^ p ^ c = 1) {v : adjointGroup τ K}
    (hv : v ∈ TableBExc.torusPow τ K p) : entrywiseAdjointAut τ σ v = v := by
  rw [TableBExc.mem_torusPow] at hv
  obtain ⟨hvH, hvp⟩ := hv
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvH
  have ha' : rootDiagUnitHom (τ := τ) (K := K) a = (v : ModGL τ K) := ha.symm
  have hvp' : (v : ModGL τ K) ^ p = 1 := by
    have h := congrArg (fun w : adjointGroup τ K => (w : ModGL τ K)) hvp
    simpa using h
  have hap : a ^ p = 1 := by
    apply rootDiagUnit_injective (τ := τ) (K := K)
    change rootDiagUnitHom (τ := τ) (K := K) (a ^ p) =
      rootDiagUnitHom (τ := τ) (K := K) (1 : Fin τ.rank → Kˣ)
    rw [map_pow, ha', hvp', map_one]
  have h4 : (fun i => Units.map ((σ ^ p ^ c).toRingHom).toMonoidHom (a i)) = a := by
    have h1 : entrywiseAdjointAut τ (σ ^ p ^ c) v = v := by
      rw [entrywiseAdjointAut_pow, hσ, MulAut.one_apply]
    have h2 := congrArg (fun w : adjointGroup τ K => (w : ModGL τ K)) h1
    rw [coe_entrywiseAdjointAut, ha] at h2
    have h3 : Units.map (entrywiseHom (σ ^ p ^ c).toRingHom) (rootDiagUnit τ a) =
        rootDiagUnit τ (fun i => Units.map ((σ ^ p ^ c).toRingHom).toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag (σ ^ p ^ c).toRingHom a)
    exact rootDiagUnit_injective (h3.symm.trans h2)
  have hafix : ∀ i, (σ ^ p ^ c) ((a i : Kˣ) : K) = ((a i : Kˣ) : K) := fun i =>
    congrArg Units.val (congrFun h4 i)
  have ha_ne_one : a ≠ 1 := by
    intro h
    apply hv1
    refine Subtype.ext ?_
    show (v : ModGL τ K) = 1
    rw [ha, h, rootDiagUnit_one]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha_ne_one
  have hi₀' : a i₀ ≠ 1 := by simpa using hi₀
  have hζ1 : ((a i₀ : Kˣ) : K) ≠ 1 := fun h => hi₀' (Units.ext h)
  have hζ : ((a i₀ : Kˣ) : K) ^ p = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) (congrFun hap i₀)
    simpa [Pi.pow_apply] using h
  have hx : ∀ i, ((a i : Kˣ) : K) ^ p = 1 := fun i => by
    have h := congrArg (fun u : Kˣ => (u : K)) (congrFun hap i)
    simpa [Pi.pow_apply] using h
  have hσa : ∀ i, σ ((a i : Kˣ) : K) = ((a i : Kˣ) : K) := fun i =>
    ringAut_apply_eq_of_pow_fixes hp hζ1 hζ (hafix i₀) (hx i)
  have haσ : (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) = a := by
    funext i
    exact Units.ext (hσa i)
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut]
  have h3 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) =
      rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
    Units.ext (entrywise_rootDiag σ.toRingHom a)
  rw [ha, h3, haσ]

end CFSG.StandardType
