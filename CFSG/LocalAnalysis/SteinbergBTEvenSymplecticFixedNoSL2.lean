module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocleSuzuki
public import CFSG.LocalAnalysis.SteinbergBTAlternatingInvolutionFixedSupportSL2
public import CFSG.LocalAnalysis.SteinbergCDEvenClassicalOrderFour

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBT

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A} {K : Type} [Field K]

theorem exists_orderOf_eq_four_alternating_six :
    ∃ y : alternatingGroup (Fin 6), orderOf y = 4 := by
  obtain ⟨g, hg4, hg2, hgs⟩ := exists_even_orderOf_eq_four_fin_six
  refine ⟨⟨g, hgs⟩, SteinbergCD.orderOf_eq_four (Subtype.ext ?_) fun h => hg2 ?_⟩
  · rw [Subgroup.coe_pow, hg4, Subgroup.coe_one]
  · have := congrArg Subtype.val h
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

theorem sp_fixed_field_orderOf_four [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) {r e : ℕ} (hr : 2 ≤ r)
    (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e) (φ : W ≃* StatedProj (StatedSp r K))
    {ρ : A →* MulAut (StatedProj (StatedSp r K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) {g : StatedSp r K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hρa : ρ a = spInner r K g * fieldAut r K σ) : ∃ x : L, orderOf x = 4 := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hαα : ρ a * ρ a = 1 := by rw [← map_mul, ← sq, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, hk, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) he hK hαα g σ hρa hσ
  rw [← spInner_apply] at hh
  have he2 : 2 ≤ e := by
    obtain ⟨m, hm⟩ := heven
    omega
  obtain ⟨hNI, -, hι₀inj, ⟨act, -, Θ, hΘ⟩, -, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores hr he2 heven hK σ hσx
  set ι₀ := (spInner r K).comp (subfieldSpHom r (descentField σ)) with hι₀
  set N₀ := ι₀.range with hN₀
  have hNC : N₀ ≤ centralizer {fieldAut r K σ} := by
    rintro _ ⟨u, rfl⟩
    have hmem := (Θ ⟨u, 1⟩).2
    rw [hΘ, map_one, mul_one] at hmem
    exact (mem_inf.mp hmem).2
  have hIC : centralizer {fieldAut r K σ} ⊓ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) =
      N₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hNC hNI)
    obtain ⟨hxC, hxI⟩ := mem_inf.mp hx
    have hxE : x ∈ spSemilinearAutGroup r K ⊓ centralizer {fieldAut r K σ} :=
      mem_inf.mpr ⟨inner_le_spSemilinearAutGroup hxI, hxC⟩
    obtain ⟨⟨u, φ'⟩, hu⟩ := Θ.surjective ⟨x, hxE⟩
    have hx' : x = spInner r K (subfieldSpHom r (descentField σ) u) * fieldAut r K φ' := by
      rw [← hΘ]
      exact (congrArg Subtype.val hu).symm
    rw [← range_spInner] at hxI
    obtain ⟨s, hs⟩ := hxI
    have h1 : spInner r K s * fieldAut r K 1 =
        spInner r K (subfieldSpHom r (descentField σ) u) * fieldAut r K φ' := by
      rw [map_one, mul_one, hs, hx']
    obtain ⟨-, hφ'⟩ := spInner_mul_fieldAut_inj h1
    rw [hx', ← hφ', map_one, mul_one]
    exact ⟨u, rfl⟩
  set χ := spInner r K h with hχ
  have hW : W.map ρ = OuterAutomorphisms.inner (StatedProj (StatedSp r K)) :=
    map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hCW' : (W ⊓ centralizer {a}).map ρ = N₀.map (MulAut.conj χ).toMonoidHom := by
    rw [hCWimg, hh, ← map_conj_inner_inf_centralizer, inf_comm, hIC]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (N₀.map (MulAut.conj χ).toMonoidHom) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCW'] at this
  have hid : (MulAut.conj χ⁻¹).toMonoidHom.comp (MulAut.conj χ).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : Subgroup (MulAut (StatedProj (StatedSp r K))),
      L₀ = (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ ι₀.range := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [Subgroup.map_map _ (MulAut.conj χ⁻¹).toMonoidHom (MulAut.conj χ).toMonoidHom, hid,
      Subgroup.map_id, ← hL₀def] at this
  let eL : L ≃* L₀ := (L.equivMapOfInjective ρ hinj).trans
    (((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective).trans
      (MulEquiv.subgroupCongr hL₀def.symm))
  have hdim : Module.finrank (descentField σ) (Fin r ⊕ Fin r → descentField σ) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  rcases symplectic_component_dichotomy hι₀inj hL₀ hk (by omega : 1 ≤ r) (by omega)
      (pairedSympForm (descentField σ) r) pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate hdim
      CatalogueBSymplecticB.statedSpIsometryEquiv with
    ⟨-, -, -, -, ⟨eX⟩⟩ | ⟨-, -, hXc, -, -, ⟨eA⟩⟩
  · obtain ⟨y, hy, -⟩ := SteinbergCD.exists_orderOf_eq_four_statedSp (k := descentField σ)
      CharTwo.two_eq_zero hr
    exact ⟨(eL.trans eX).symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  · obtain ⟨y, hy⟩ := exists_orderOf_eq_four_alternating_six
    exact ⟨(eL.trans ((MulEquiv.subgroupCongr hXc).trans eA)).symm y,
      by rw [MulEquiv.orderOf_eq, hy]⟩

theorem not_three_dvd_suzuki_order (m : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
  have hq3 : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hq1' : (2 ^ (2 * m + 1) - 1) % 3 = 1 := by omega
  have hsq : (2 ^ (2 * m + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq3]
  have hsq1 : ((2 ^ (2 * m + 1)) ^ 2 + 1) % 3 = 2 := by omega
  have h1 : (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) % 3 = 1 := by
    rw [Nat.mul_mod, hsq, hq1']
  have h2 : (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) % 3 =
      2 := by
    rw [Nat.mul_mod, h1, hsq1]
  omega

theorem sp_fixed_suzuki_not_three_dvd [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) {m : ℕ} (hm : 1 ≤ m)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (φ : W ≃* StatedProj (StatedSp 2 K)) {ρ : A →* MulAut (StatedProj (StatedSp 2 K))}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) {s : StatedSp 2 K}
    (hρa : ρ a = spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) : ¬ 3 ∣ Nat.card L := by
  classical
  have ha2 : a ^ 2 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hαα : ρ a * ρ a = 1 := by rw [← map_mul, ← sq, ha2, map_one]
  rw [hρa] at hαα
  obtain ⟨χ, -, hχ⟩ := exists_inner_conj_eta hK hαα
  rw [← hρa] at hχ
  obtain ⟨ψ, -, hψinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  have hW : W.map ρ = OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) :=
    map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hCW' : (W ⊓ centralizer {a}).map ρ = ψ.range.map (MulAut.conj χ).toMonoidHom := by
    rw [hCWimg, hχ, ← map_conj_inner_inf_centralizer, ← hrange]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (ψ.range.map (MulAut.conj χ).toMonoidHom) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCW'] at this
  have hid : (MulAut.conj χ⁻¹).toMonoidHom.comp (MulAut.conj χ).toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : Subgroup (MulAut (StatedProj (StatedSp 2 K))),
      L₀ = (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ ψ.range := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [Subgroup.map_map _ (MulAut.conj χ⁻¹).toMonoidHom (MulAut.conj χ).toMonoidHom, hid,
      Subgroup.map_id, ← hL₀def] at this
  let eL : L ≃* L₀ := (L.equivMapOfInjective ρ hinj).trans
    (((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective).trans
      (MulEquiv.subgroupCongr hL₀def.symm))
  intro h3
  have hdvd : Nat.card L₀ ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hL₀.1
  rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, suzuki_order hK,
    ← Nat.card_congr eL.toEquiv] at hdvd
  exact not_three_dvd_suzuki_order m (h3.trans hdvd)

theorem sp_fixed_false [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) {r e : ℕ} (hr : 2 ≤ r)
    (he : 1 ≤ e) (hre : ¬ (r = 2 ∧ e = 1)) (hK : Nat.card K = 2 ^ e)
    (φ : W ≃* StatedProj (StatedSp r K)) {ρ : A →* MulAut (StatedProj (StatedSp r K))}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (hZ : center (StatedProj (StatedSp r K)) = ⊥) (h4 : ∀ x : L, orderOf x ≠ 4)
    (h3 : 3 ∣ Nat.card L) : False := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hnI : ρ a ∉ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) := fun h =>
    sp_socle_inner_false ha hLCW (by omega) he hK φ hinj hρW hZ h
  have hE : ρ a ∈ spSemilinearAutGroup r K → False := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hgσ
      exact hnI (hgσ ▸ spInner_mem_inner g)
    · obtain ⟨x, hx⟩ := sp_fixed_field_orderOf_four ha hLCW hr he hK φ hinj hρW hσ hgσ
      exact h4 x hx
  by_cases hr3 : 3 ≤ r
  · apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hr3).1]
    exact mem_top _
  · obtain rfl : r = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism he hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    have hρa2 : orderOf (ρ a) = 2 := (orderOf_injective ρ hinj a).trans ha
    rcases Nat.even_or_odd e with he' | ho
    · exact hE (heven he' _ hρa2)
    · obtain ⟨s, hs⟩ := hodd ho _ hρa2 hnI
      obtain ⟨m, rfl⟩ := ho
      have hm : 1 ≤ m := by omega
      rw [eq_exceptionalAut hγ] at hs
      exact sp_fixed_suzuki_not_three_dvd ha hLCW hm hK φ hinj hρW hs h3

end CFSG.LocalAnalysis.SteinbergBT
