module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251L
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Shape
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KOut
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R847O3

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec21 (sl2OrderThree coe_sl2OrderThree orderOf_sl2OrderThree
  eq_one_of_mem_center_sl2)

@[expose] def ThreeInvPair (X : Type) [Group X] : Type :=
  {xg : X × X // orderOf xg.1 = 3 ∧ xg.2 * xg.1 * xg.2⁻¹ = xg.1⁻¹}

instance (X : Type) [Group X] : MulAction (MulAut X) (ThreeInvPair X) where
  smul f xg := ⟨(f xg.1.1, f xg.1.2), (MulEquiv.orderOf_eq f _).trans xg.2.1, by
    simpa only [map_mul, map_inv] using congrArg f xg.2.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[expose] def LossPairAt (X : Type) [Group X] (p : ℕ) : Prop :=
  ∀ (P : Type) [Group P] [Finite P], (∀ x : P, x ^ p = 1) → (∀ x y : P, x * y = y * x) →
    ∀ φ : P →* MulAut X, ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ ∧
      ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x ∧ φ u g = g

theorem exists_invPair_index_le_of {X : Type} [Group X] [Finite X] {P : Type} [Group P]
    [Finite P] {p : ℕ} (hp : p.Prime) (hexp : ∀ x : P, x ^ p = 1)
    (hPab : ∀ x y : P, x * y = y * x) (φ : P →* MulAut X)
    (h3 : ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹)
    (hcyc : IsCyclic ↥(φ.range ⊓ (MulAut.conj : X →* MulAut X).range))
    (hquot : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ k : ℕ, x ^ k * y ∈ (MulAut.conj : X →* MulAut X).range)
    (hfix : ∀ z ∈ φ.range, z ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ ∧ z x = x ∧ z g = g) :
    ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ ∧
      ∃ Q : Subgroup P, Q.index ≤ p ∧ ∀ u ∈ Q, φ u x = x ∧ φ u g = g := by
  obtain ⟨x₀, g₀, hx₀, hg₀⟩ := h3
  haveI : Finite (ThreeInvPair X) := Subtype.finite
  haveI : Nonempty (ThreeInvPair X) := ⟨⟨(x₀, g₀), hx₀, hg₀⟩⟩
  obtain ⟨ω, hω⟩ := uc22p22y_exists_fixed_index_le (Ω := ThreeInvPair X) hp hexp hPab φ
    (MulAut.conj : X →* MulAut X).range hcyc hquot fun z hz hzi => by
      obtain ⟨x, g, hx, hg, hzx, hzg⟩ := hfix z hz hzi
      exact ⟨⟨(x, g), hx, hg⟩, Subtype.ext (Prod.ext hzx hzg)⟩
  refine ⟨ω.1.1, ω.1.2, ω.2.1, ω.2.2, (MulAction.stabilizer (MulAut X) ω).comap φ, hω,
    fun u hu => ?_⟩
  have h := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 hu)
  exact ⟨congrArg (fun w : ThreeInvPair X => w.1.1) h,
    congrArg (fun w : ThreeInvPair X => w.1.2) h⟩

theorem exists_invPair_fixed_psl2FieldAut (F : Type) [Field F] [CharP F 2] :
    ∃ c s : CFSG.GorensteinWalter.PSL2 F, orderOf c = 3 ∧ s * c * s⁻¹ = c⁻¹ ∧
      ∀ τ : F ≃+* F, CFSG.GorensteinWalter.psl2FieldAut F τ c = c ∧
        CFSG.GorensteinWalter.psl2FieldAut F τ s = s := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix.SpecialLinearGroup (Fin 2) F,
      (s₀ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] :=
    ⟨⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of]; linear_combination -h2⟩, rfl⟩
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (eq_one_of_mem_center_sl2 hx)
  have hfix : ∀ (τ : F ≃+* F) (x : Matrix.SpecialLinearGroup (Fin 2) F),
      (∀ i j, τ ((x : Matrix (Fin 2) (Fin 2) F) i j) = (x : Matrix (Fin 2) (Fin 2) F) i j) →
      CFSG.GorensteinWalter.psl2FieldAut F τ
          (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x) =
        QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x := by
    intro τ x hx
    rw [CFSG.GorensteinWalter.psl2FieldAut_apply, CFSG.GorensteinWalter.psl2RingEquiv_mk]
    congr 1
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hx i j
  have hcsc : sl2OrderThree * s₀ * sl2OrderThree = s₀ := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2OrderThree,
      hs₀, Matrix.mul_fin_two, Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2
  have hsc : s₀ * sl2OrderThree * s₀⁻¹ = (sl2OrderThree)⁻¹ := by
    calc s₀ * sl2OrderThree * s₀⁻¹ =
        (sl2OrderThree)⁻¹ * (sl2OrderThree * s₀ * sl2OrderThree) * s₀⁻¹ := by group
      _ = (sl2OrderThree)⁻¹ := by rw [hcsc]; group
  refine ⟨QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) sl2OrderThree,
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) s₀, ?_, ?_,
    fun τ => ⟨hfix τ _ fun i j => ?_, hfix τ _ fun i j => ?_⟩⟩
  · rw [orderOf_injective _ hinj, orderOf_sl2OrderThree]
  · simpa only [map_mul, map_inv] using
      congrArg (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) hsc
  · rw [coe_sl2OrderThree]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hs₀]
    fin_cases i <;> fin_cases j <;> simp

theorem exists_fixed_invPair {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (z : MulAut X) (hz : orderOf z = p)
    (hzi : z ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ ∧ z x = x ∧ z g = g := by
  obtain ⟨F, _, _, _, -, ⟨e⟩⟩ := P22y.exists_equiv_psl2 h
  have hz'i : ∀ g, MulAut.congr e z ≠ MulAut.conj g := by
    intro g hg
    apply hzi
    refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
    have h1 : e (z x) = g * e x * g⁻¹ := by
      have := congrArg (fun α : MulAut (CFSG.GorensteinWalter.PSL2 F) => α (e x)) hg
      simpa [MulAut.congr_apply, MulAut.conj_apply] using this
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, h1]
  obtain ⟨τ, β, -, hτ⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_fieldAut hp
    (hp.odd_of_ne_two hp2) ⟨by rw [MulEquiv.orderOf_eq, hz], hz'i⟩
  obtain ⟨c, s, hc, hsc, hfc⟩ := exists_invPair_fixed_psl2FieldAut F
  have hback : ∀ y, CFSG.GorensteinWalter.psl2FieldAut F τ y = y →
      z (e.symm (β y)) = e.symm (β y) := fun y hy => by
    have h1 : MulAut.congr e z (β y) = β y := by
      rw [hτ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h1
    exact e.injective (by rw [h1, MulEquiv.apply_symm_apply])
  refine ⟨e.symm (β c), e.symm (β s), by rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hc], ?_,
    hback c (hfc τ).1, hback s (hfc τ).2⟩
  simpa only [map_mul, map_inv] using congrArg (fun y => e.symm (β y)) hsc

theorem lossPairAt_of_isL2Ev {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : LossPairAt X p := by
  intro P _ _ hexp hPab φ
  haveI : Fact p.Prime := ⟨hp⟩
  have hrp : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hexp, map_one]
  have h3 : ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ := by
    obtain ⟨F, _, _, _, -, ⟨e⟩⟩ := P22y.exists_equiv_psl2 h
    obtain ⟨c, s, hc, hsc, -⟩ := exists_invPair_fixed_psl2FieldAut F
    exact ⟨e.symm c, e.symm s, by rw [MulEquiv.orderOf_eq, hc], by
      simpa only [map_mul, map_inv] using congrArg e.symm hsc⟩
  refine exists_invPair_index_le_of hp hexp hPab φ h3
    (P22y.isCyclic_range_inf_inner h hp hp2 hexp φ)
    (fun x hx y hy hxi => P22y.exists_pow_mul_mem_inner h hp (hrp x hx) (hrp y hy) hxi)
    fun z hz hzi => ?_
  have hz1 : z ≠ 1 := fun h1 => hzi (h1 ▸ Subgroup.one_mem _)
  exact exists_fixed_invPair h hp hp2 z (orderOf_eq_prime (hrp z hz) hz1) hzi

private theorem exists_invPair_of_perfect {X : Type} [Group X] [Finite X]
    (hperf : _root_.commutator X = ⊤) (h3 : 3 ∣ Nat.card X)
    (h3r : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) :
    ∃ x g : X, orderOf x = 3 ∧ g * x * g⁻¹ = x⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  obtain ⟨w, hwN, hwC⟩ := uc22ine229_exists_mem_normalizer_not_mem_centralizer hperf
    Nat.prime_three (by norm_num) h3r (X := zpowers x) (by rw [Nat.card_zpowers, hx])
  have hwx : w * x * w⁻¹ ∈ zpowers x := (mem_normalizer_iff.1 hwN x).1 (mem_zpowers x)
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hwx
  have hmod : x ^ (n % 3) = x ^ n := by
    have h := zpow_mod_orderOf x n
    rw [hx] at h
    exact_mod_cast h
  refine ⟨x, w, hx, ?_⟩
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> rw [h] at hmod
  · have h1 : w * x * w⁻¹ = 1 := by rw [← hn, ← hmod, zpow_zero]
    rw [conj_eq_one_iff] at h1
    rw [h1, orderOf_one] at hx
    omega
  · have h1 : w * x * w⁻¹ = x := by rw [← hn, ← hmod, zpow_one]
    refine absurd (mem_centralizer_iff.2 fun y hy => ?_) hwC
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 (show y ∈ zpowers x from hy)
    have hc : Commute w x := by
      calc w * x = w * x * w⁻¹ * w := by group
        _ = x * w := by rw [h1]
    exact (hc.zpow_right m).eq.symm
  · have h2 : x ^ 2 * x = 1 := by
      rw [← pow_succ]
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    rw [← hn, ← hmod, zpow_two, ← pow_two]
    exact eq_inv_of_mul_eq_one_left h2

theorem lossPairAt_of_thinShape {X : Type} [Group X] [Finite X] (hX : R8107Shape.ThinShape X)
    (hZ : center X = ⊥) (hperf : _root_.commutator X = ⊤) (h3 : 3 ∣ Nat.card X)
    (h3r : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcp : ∀ B : Subgroup X, IsPGroup p B → IsCyclic ↥B) : LossPairAt X p := by
  intro P _ _ hexp hPab φ
  rcases hX with ⟨n, h⟩ | hs
  · exact lossPairAt_of_isL2Ev (P22fin.isL2Ev_of_isL2 h).1 hp hp2 P hexp hPab φ
  have hinn : φ.range ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨u, rfl⟩
    exact KBridge.kOddOutInner_holds X (Or.inr hs) (φ u) (Odd.of_dvd_nat (hp.odd_of_ne_two hp2)
      (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hexp, map_one])))
  exact exists_invPair_index_le_of hp hexp hPab φ (exists_invPair_of_perfect hperf h3 h3r)
    (P2251L.isCyclic_range_inf_inner_of hZ hcp hexp φ) (fun _ hx _ _ hxi => absurd (hinn hx) hxi)
    fun _ hz hzi => absurd (hinn hz) hzi

end CFSG.LocalAnalysis.UniquenessCase.UC22.R847O3

end
