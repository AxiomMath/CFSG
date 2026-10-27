module

public import CFSG.Timmesfeld.ARS.Sec5Lines
public import CFSG.Timmesfeld.ARS.Sec8Regular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace TwoCore

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

theorem eq_one_of_mem_of_mem {N : Subgroup G} (hN : N.Normal) (hN2 : IsPGroup 2 N)
    {T : Subgroup G} (hT : T ∈ R) {y : G} (hyT : y ∈ T) (hyN : y ∈ N) : y = 1 := by
  by_contra hy1
  obtain ⟨U, hU, hTU⟩ := hiso T hT
  obtain ⟨u, hu, hu1⟩ := hR.exists_ne_one hU
  have hTT' : Opposite T (conjSub T u) := opposite_conjSub_of_opposite hR hU hT hTU.symm hu hu1
  set y' := u * y * u⁻¹ with hy'def
  have hy'T : y' ∈ conjSub T u := conj_mem_conjSub u hyT
  have hy'N : y' ∈ N := hN.conj_mem y hyN u
  have hy'1 : y' ≠ 1 := fun e => hy1 (by
    have : u * y * u⁻¹ = 1 := e
    rwa [conj_eq_one_iff] at this)
  have hodd := hTT'.odd_orderOf_mul (hR.mul_self T hT) hyT hy1 hy'T hy'1
  obtain ⟨k, hk⟩ := hN2 ⟨y * y', N.mul_mem hyN hy'N⟩
  have hpow : (y * y') ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf (y * y') ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · rw [hj, pow_succ] at hodd
      exact absurd hodd (by simp)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have hyy : y' = y⁻¹ := eq_inv_of_mul_eq_one_right hj
  have hmem : y' ∈ T ⊓ conjSub T u := ⟨hyy ▸ T.inv_mem hyT, hy'T⟩
  rw [hTT'.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact hy'1 hmem

theorem eq_bot_of_rootClosure_eq_singleton (hnd : IsNondegenerate R)
    (hZ : Subgroup.center G = ⊥) (hcl : ∀ A ∈ R, rootClosure R A = {A}) {N : Subgroup G}
    (hN : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A := fun A hA B hB hΩ => by
    have := mem_rootClosure_of_omegaSet_eq hR hiso hA hB hΩ
    rwa [hcl A hA] at this
  by_contra hNb
  obtain ⟨X, hX, hXN⟩ : ∃ X ∈ R, ¬ Commuting X N := by
    by_contra! hall
    apply hNb
    have hC : (⊤ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
      rw [← hR.gen]
      exact iSup₂_le fun A hA => commuting_iff_le_centralizer.1 (hall A hA).symm
    rw [← le_bot_iff, ← hZ]
    intro n hn
    exact Subgroup.mem_center_iff.2 fun g =>
      (Subgroup.mem_centralizer_iff.1 (hC (Subgroup.mem_top g)) n hn).symm
  obtain ⟨x, hx, n, hn, hxn⟩ : ∃ x ∈ X, ∃ n ∈ N, ¬ Commute x n := by
    by_contra! hall
    exact hXN hall
  set z := ⁅x, n⁆ with hzdef
  have hz1 : z ≠ 1 := fun e => hxn (commutatorElement_eq_one_iff_mul_comm.1 e)
  have hzN : z ∈ N := by
    rw [hzdef, commutatorElement_def]
    exact N.mul_mem (hN.conj_mem n hn x) (N.inv_mem hn)
  have hzX : z = x * (n * x⁻¹ * n⁻¹) := by rw [hzdef, commutatorElement_def]; group
  by_cases hXn : conjSub X n = X
  ·
    apply hz1
    refine eq_one_of_mem_of_mem hR hiso hN hN2 hX ?_ hzN
    rw [hzX]
    exact X.mul_mem hx (hXn ▸ conj_mem_conjSub n (X.inv_mem hx))
  set Δ : Set (Subgroup G) := (fun m => conjSub X m) '' (N : Set G) with hΔ
  have hΔorb : ∀ g : G, conjSet Δ g = (fun m => conjSub (conjSub X g) m) '' (N : Set G) := by
    intro g
    ext C
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨g * m * g⁻¹, hN.conj_mem m hm g, ?_⟩
      change conjSub (conjSub X g) (g * m * g⁻¹) = conjSub (conjSub X m) g
      rw [← conjSub_mul, ← conjSub_mul, inv_mul_cancel_right]
    · rintro ⟨m, hm, rfl⟩
      refine ⟨conjSub X (g⁻¹ * m * g), ⟨g⁻¹ * m * g, by
        have := hN.conj_mem m hm g⁻¹
        rwa [inv_inv] at this, rfl⟩, ?_⟩
      change conjSub (conjSub X (g⁻¹ * m * g)) g = conjSub (conjSub X g) m
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
  have hΔwti : IsWeakTI R Δ := by
    refine ⟨?_, ⟨X, ⟨1, N.one_mem, conjSub_one X⟩, conjSub X n, ⟨n, hn, rfl⟩, Ne.symm hXn⟩,
      ?_, fun d _ => ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact hR.conjSub_mem hX m
    ·
      intro e
      obtain ⟨Y, hY, hXY⟩ := hiso X hX
      have hNX : IsPGroup 2 ↥(N ⊔ X) := IsPGroup.to_sup_of_normal_left hN2 (hR.isPGroup hX)
      have htop : N ⊔ X = ⊤ := by
        rw [eq_top_iff, ← hR.gen, ← e]
        refine iSup₂_le fun A hA => ?_
        obtain ⟨m, hm, rfl⟩ := hA
        rintro _ ⟨a, ha, rfl⟩
        change m * a * m⁻¹ ∈ N ⊔ X
        rw [show m * a * m⁻¹ = (m * (a * m⁻¹ * a⁻¹)) * a by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (N.mul_mem hm
          (hN.conj_mem m⁻¹ (N.inv_mem hm) a))) (Subgroup.mem_sup_right ha)
      have h2 : IsPGroup 2 ↥(X ⊔ Y) := (htop ▸ hNX).to_le le_top
      exact Sec3.not_opposite_of_isPGroup_sup hR hX hY h2 hXY
    ·
      by_cases hint : (Δ ∩ conjSet Δ d).Nonempty
      · right
        obtain ⟨C, ⟨m₁, hm₁, rfl⟩, hC⟩ := hint
        rw [hΔorb d] at hC
        obtain ⟨m₂, hm₂, hm₂e⟩ := hC
        refine Set.inter_eq_left.2 ?_
        rw [hΔorb d]
        rintro _ ⟨m, hm, rfl⟩
        refine ⟨m * m₁⁻¹ * m₂, N.mul_mem (N.mul_mem hm (N.inv_mem hm₁)) hm₂, ?_⟩
        change conjSub (conjSub X d) (m * m₁⁻¹ * m₂) = conjSub X m
        have hm₂e' : conjSub (conjSub X d) m₂ = conjSub X m₁ := hm₂e
        rw [conjSub_mul, hm₂e', ← conjSub_mul, inv_mul_cancel_right]
      · left
        exact Set.not_nonempty_iff_eq_empty.1 hint
  have hXΔ : X ∈ Δ := ⟨1, N.one_mem, conjSub_one X⟩
  have hzΔ : z ∈ gen Δ := by
    rw [hzX]
    exact Subgroup.mul_mem _ (le_gen hXΔ hx)
      (le_gen (⟨n, hn, rfl⟩ : conjSub X n ∈ Δ) (conj_mem_conjSub n (X.inv_mem hx)))
  obtain ⟨T, hT, -, hzT⟩ :=
    Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔwti subset_rfl hzΔ hz1
  exact hz1 (eq_one_of_mem_of_mem hR hiso hN hN2 (hΔwti.1 hT) hzT hzN)

end TwoCore

end CFSG.Timmesfeld.ARS
