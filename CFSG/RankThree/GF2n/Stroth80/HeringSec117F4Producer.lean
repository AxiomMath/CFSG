module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2Producer
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.LinearAlgebra.EigenOrbit

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 QuadraticMap Module

section Restrict

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {X : Type*} [Group X]

omit [FiniteDimensional K V] in
theorem apply_mem_commutatorSpace {H : Subgroup (V ≃ₗ[K] V)} {h : V ≃ₗ[K] V} (hh : h ∈ H)
    {u : V} (hu : u ∈ commutatorSpace H) : h u ∈ commutatorSpace H := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, hg, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨h * g * h⁻¹, H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh),
      h v, ?_⟩
    simp [map_sub]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

omit [FiniteDimensional K V] in
theorem exists_restrict_commutatorSpace (ρ : X →* (V ≃ₗ[K] V)) (F : Subgroup X) :
    ∃ ρU : ↥F →* (↥(commutatorSpace (F.map ρ)) ≃ₗ[K] ↥(commutatorSpace (F.map ρ))),
      ∀ g v, ((ρU g v : ↥(commutatorSpace (F.map ρ))) : V) = ρ g v := by
  set U := commutatorSpace (F.map ρ)
  have hmap : ∀ g : ↥F, U.map ((ρ g : V ≃ₗ[K] V) : V →ₗ[K] V) = U := by
    intro g
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact apply_mem_commutatorSpace (Subgroup.mem_map_of_mem ρ g.2) hu
    · intro u hu
      refine ⟨ρ g⁻¹ u, apply_mem_commutatorSpace (Subgroup.mem_map_of_mem ρ (F.inv_mem g.2)) hu,
        ?_⟩
      change ρ g (ρ g⁻¹ u) = u
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  refine ⟨{ toFun := fun g => LinearEquiv.ofSubmodules (ρ g) U U (hmap g)
            map_one' := ?_
            map_mul' := ?_ }, fun g v => rfl⟩
  · refine LinearEquiv.ext fun v => Subtype.ext ?_
    change ρ ((1 : ↥F) : X) v = v
    rw [OneMemClass.coe_one, map_one]
    rfl
  · intro g h
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    change ρ ((g * h : ↥F) : X) v = ρ g (ρ h v)
    rw [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply]

end Restrict


@[expose] def F4ExclStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ∀ c ∈ [f4Rep K [47, 44], f4Rep K [41, 45]],
    ∃ s t : ↥(adjointGroup .F4 K), IsConj s c ∧ IsConj t c ∧
      (s * t) ^ 4 ≠ 1 ∧ ¬ Odd (orderOf (s * t))

@[expose] def F4GenStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ∀ c ∈ [f4Rep K [47], f4Rep K [44]],
    ∃ d : Fin 5 → ↥(adjointGroup .F4 K), ∃ e : ↥(adjointGroup .F4 K),
      (∀ i, IsConj (d i) c) ∧ IsConj e c ∧ IsConj (e * d 4) c ∧ e * d 4 = d 4 * e ∧
      ∃ t ∈ Subgroup.closure (Set.range (Fin.cons e d)),
        ∃ n ∈ Subgroup.closure (Set.range (Fin.cons e d)),
          orderOf t = 13 ∧ n⁻¹ * t * n = t ^ 2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Qf : QuadraticForm K V} {X : Type} [Group X]
  {K' : Type} [Field K'] [Finite K'] [CharP K' 2]

omit
  [Finite K] [FiniteDimensional K V] in
theorem eq_one_of_odd_of_trivial_on {t : V ≃ₗ[K] V} {U : Submodule K V}
    (hU : ∀ v, t v - v ∈ U) (htU : ∀ u ∈ U, t u = u) (hodd : Odd (orderOf t)) : t = 1 := by
  have h2 : t * t = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have h := htU _ (hU v)
    rw [map_sub, sub_eq_iff_eq_add] at h
    rw [LinearEquiv.mul_apply, h]
    change _ = v
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : t v - v + t v = (2 : K) • t v - v := by rw [two_smul]; abel
    rw [this, h2, zero_smul, zero_sub]
    have hv : (2 : K) • v = 0 := by rw [h2, zero_smul]
    rw [two_smul] at hv
    exact neg_eq_of_add_eq_zero_right hv
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [_root_.sq, h2])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

theorem orderOf_two_zmod_thirteen : orderOf ((2 : ℕ) : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem false_of_f4 (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (ψ : X ≃* ↥(adjointGroup .F4 K')) {t₀ : X} (ht₀ : IsLongRootElement Qf (ρ t₀))
    (hF1 : F4ExclStatement) (hF2 : F4GenStatement) : False := by
  have h2 : orderOf (ψ t₀) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_two_of_isLongRootElement hnd ρ hρ ht₀
  have hinv : ψ t₀ * ψ t₀ = 1 := by rw [← _root_.sq, ← h2, pow_orderOf_eq_one]
  have hne : ψ t₀ ≠ 1 := fun h => by rw [h, orderOf_one] at h2; exact absurd h2 (by decide)
  have hsieg : ∀ z : ↥(adjointGroup .F4 K'), IsConj z (ψ t₀) →
      IsLongRootElement Qf (ρ (ψ.symm z)) := fun z hz =>
    isLongRootElement_of_isConj ρ hρQ ψ ht₀ (by simpa using hz)
  obtain ⟨y, hy, hyt⟩ := classesCover_AS (K := K') (ψ t₀) hinv hne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  have hexcl : ∀ c ∈ [f4Rep K' [47, 44], f4Rep K' [41, 45]], IsConj c (ψ t₀) → False := by
    intro c hc hct
    obtain ⟨s, t, hs, ht, h4, hodd⟩ := hF1 K' c hc
    set φ : ↥(adjointGroup .F4 K') →* (V ≃ₗ[K] V) := ρ.comp ψ.symm.toMonoidHom
    have hφ : Function.Injective φ := hρ.comp ψ.symm.injective
    have hs' : IsLongRootElement Qf (φ s) := hsieg s (hs.trans hct)
    have ht' : IsLongRootElement Qf (φ t) := hsieg t (ht.trans hct)
    rcases pow_four_eq_one_or_odd_orderOf_mul hnd hs' ht' with h | h
    · rw [← map_mul, ← map_pow] at h
      refine h4 (hφ ?_)
      rw [map_one]
      exact h
    · rw [← map_mul, orderOf_injective φ hφ] at h
      exact hodd h
  have hroot : ∀ c ∈ [f4Rep K' [47], f4Rep K' [44]], IsConj c (ψ t₀) → False := by
    intro c hc hyt
    obtain ⟨d, e, hd, he, hed, hcomm, t, ht, n, hn, hto, htn⟩ := hF2 K' c hc
    set F : Subgroup X := Subgroup.closure (Set.range (Fin.cons (ψ.symm e) (ψ.symm ∘ d)))
    have hFmap : F.map ρ = Subgroup.closure (Set.range (Fin.cons (ρ (ψ.symm e))
        (fun i => ρ (ψ.symm (d i))))) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      congr 2
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have htF : ψ.symm t ∈ F := by
      have := Subgroup.mem_map_of_mem ψ.symm.toMonoidHom ht
      rw [MonoidHom.map_closure, ← Set.range_comp] at this
      convert this using 3
      all_goals first
        | rfl
        | (ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp)
    have hnF : ψ.symm n ∈ F := by
      have := Subgroup.mem_map_of_mem ψ.symm.toMonoidHom hn
      rw [MonoidHom.map_closure, ← Set.range_comp] at this
      convert this using 3
      all_goals first
        | rfl
        | (ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp)
    have hdi : ∀ i, IsLongRootElement Qf (ρ (ψ.symm (d i))) := fun i =>
      hsieg _ ((hd i).trans hyt)
    have hU11 : finrank K ↥(commutatorSpace (F.map ρ)) ≤ 2 * 5 + 1 := by
      rw [hFmap]
      exact finrank_commutatorSpace_cons_le hnd (fun i => ρ (ψ.symm (d i))) hdi
        (hsieg _ (he.trans hyt)) (hdi 4) (Subgroup.subset_closure ⟨4, rfl⟩)
        (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm])
        (by rw [← map_mul, ← map_mul]; exact hsieg _ (hed.trans hyt))
    obtain ⟨ρU, hρU⟩ := exists_restrict_commutatorSpace ρ F
    have hto' : orderOf (⟨ψ.symm t, htF⟩ : ↥F) = 13 := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hto]
    have hρUt : ρU ⟨ψ.symm t, htF⟩ ≠ 1 := by
      intro h1
      have hmov : ∀ v, ρ (ψ.symm t) v - v ∈ commutatorSpace (F.map ρ) := fun v =>
        movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ htF) ⟨v, rfl⟩
      have htriv : ∀ u ∈ commutatorSpace (F.map ρ), ρ (ψ.symm t) u = u := by
        intro u hu
        have := congrArg (fun f => ((f ⟨u, hu⟩ : ↥(commutatorSpace (F.map ρ))) : V)) h1
        simpa [hρU] using this
      have hodd : Odd (orderOf (ρ (ψ.symm t))) := by
        rw [orderOf_injective ρ hρ, MulEquiv.orderOf_eq, hto]
        decide
      have h1' := eq_one_of_odd_of_trivial_on hmov htriv hodd
      have : ψ.symm t = 1 := hρ (h1'.trans (map_one ρ).symm)
      rw [MulEquiv.map_eq_one_iff] at this
      rw [this, orderOf_one] at hto
      exact absurd hto (by decide)
    have h12 := CFSG.LinearAlgebra.le_finrank_of_eigen_orbit ρU (t := ⟨ψ.symm t, htF⟩)
      (n := ⟨ψ.symm n, hnF⟩) (ℓ := 13) (k := 2) (m := 12) (by norm_num)
      (by
        have h13 : ((13 : ℕ) : K) = 1 := by
          have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
          have : ((13 : ℕ) : K) = 6 * 2 + 1 := by push_cast; ring
          rw [this, h2, mul_zero, zero_add]
        rw [h13]
        exact one_ne_zero)
      hto' (Subtype.ext (by simp [← map_inv, ← map_mul, htn])) orderOf_two_zmod_thirteen hρUt
    omega
  rcases hy with rfl | rfl | rfl | rfl
  · exact hroot _ (by simp) hyt
  · exact hroot _ (by simp) hyt
  · exact hexcl _ (by simp) hyt
  · exact hexcl _ (by simp) hyt

end CFSG.RankThree.GF2n.Stroth80
