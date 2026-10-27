module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreCases
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
import CFSG.Goldschmidt75.OddCore
import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
import CFSG.Timmesfeld.CorollaryBBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Fischer CFSG.Fischer Subgroup CFSG.Permutation.SymmetricCoxeter
open CFSG.Open (fusionOddCore)

namespace CoreStar

variable {Y : Type} [Group Y] {t : Y}

theorem pair_of_threeTransp [Finite Y] (hord : orderOf t = 2)
    (hncl : normalClosure ({t} : Set Y) = ⊤)
    (h3 : ∀ a b : Y, IsConj t a → IsConj t b → orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) :
    Pair Y {x | IsConj t x} := by
  refine ⟨inferInstance, ⟨t, rfl⟩, fun e he => ?_, fun e he f hf => h3 e f he hf, ?_⟩
  · obtain ⟨g, rfl⟩ := isConj_iff.mp he
    rw [← hord]
    exact (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm
  · have h := CFSG.Timmesfeld.CorB.normalClosure_eq t
    rw [hncl] at h
    exact h.symm

theorem isPGroup_two_center_of_fusionOddCore [Finite Y] (hO : fusionOddCore Y = ⊥) :
    IsPGroup 2 (center Y) := by
  intro z
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z : Y)).ne'
  have hy : (z : Y) ^ 2 ^ a ∈ center Y := pow_mem z.2 _
  have hord : orderOf ((z : Y) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
  have hnorm : (zpowers ((z : Y) ^ 2 ^ a)).Normal :=
    ⟨fun w hw g => by
      rw [Subgroup.mem_center_iff.mp (zpowers_le.mpr hy hw) g, mul_inv_cancel_right]
      exact hw⟩
  have hle : zpowers ((z : Y) ^ 2 ^ a) ≤ fusionOddCore Y := by
    refine CFSG.Goldschmidt75.le_oddCore hnorm ?_
    rw [Nat.card_zpowers, hord]
    exact hm
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow, hle, OneMemClass.coe_one])⟩

theorem exists_perm_two_of_mem_center (hP : Pair Y {x | IsConj t x}) (ht : t ∈ center Y) :
    ∃ e : Y ≃* Equiv.Perm (Fin 2), (e t).IsSwap := by
  have := Pair.finite hP
  have htop : zpowers t = ⊤ := by
    rw [eq_top_iff, ← Pair.closure_eq hP, closure_le]
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    rw [SetLike.mem_coe, Subgroup.mem_center_iff.mp ht g, mul_inv_cancel_right]
    exact mem_zpowers t
  have hcard : Nat.card Y = 2 := by
    rw [← Subgroup.card_top (G := Y), ← htop, Nat.card_zpowers,
      Pair.orderOf_eq_two hP (IsConj.refl t)]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : Y ≃* Equiv.Perm (Fin 2) := mulEquivOfPrimeCardEq hcard
    (by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl)
  have hne : e t ≠ 1 := fun h =>
    Pair.ne_one hP (IsConj.refl t) (e.injective (h.trans (map_one e).symm))
  have key : ∀ σ : Equiv.Perm (Fin 2), σ ≠ 1 → σ = Equiv.swap 0 1 := by decide
  exact ⟨e, 0, 1, by decide, key _ hne⟩

theorem exists_orderOf_mul_eq_three_of_not_mem_center (hP : Pair Y {x | IsConj t x})
    (ht : t ∉ center Y) {x : Y} (hx : IsConj t x) : ∃ c, IsConj t c ∧ orderOf (c * x) = 3 := by
  by_contra h
  push Not at h
  have hxZ : x ∈ center Y := (Pair.mem_center_iff hP).2 fun e he => by
    by_contra hne
    exact h e he (Pair.orderOf_mul_eq_three hP he hx hne)
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  apply ht
  have h1 := Subgroup.mem_center_iff.mp hxZ g
  have htx : t = x := by
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = g⁻¹ * (x * g) := by rw [hg, mul_assoc]
      _ = x := by rw [← h1]; group
  rw [htx]
  exact hxZ

private theorem mem_one_two_three_of_dvd {k j : ℕ} (hkj : k ∣ j)
    (hj : j ∈ ({1, 2, 3} : Set ℕ)) : k ∈ ({1, 2, 3} : Set ℕ) := by
  rcases hj with rfl | rfl | rfl
  · exact Or.inl (Nat.dvd_one.mp hkj)
  · rcases (Nat.dvd_prime Nat.prime_two).mp hkj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases (Nat.dvd_prime Nat.prime_three).mp hkj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

section Quotient

variable {Q : Subgroup Y} [Q.Normal]

private theorem exists_lift {a : Y ⧸ Q} (ha : IsConj (t : Y ⧸ Q) a) :
    ∃ d : Y, IsConj t d ∧ (d : Y ⧸ Q) = a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨g' * t * g'⁻¹, isConj_iff.mpr ⟨g', rfl⟩, by simp⟩

theorem pair_quotient (hP : Pair Y {x | IsConj t x}) (ht : t ∉ Q) :
    Pair (Y ⧸ Q) {x | IsConj (t : Y ⧸ Q) x} := by
  have := Pair.finite hP
  have hnot : ∀ {d : Y}, IsConj t d → d ∉ Q := fun {d} hd hdQ => by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hd
    apply ht
    have := ‹Q.Normal›.conj_mem _ hdQ g⁻¹
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  refine ⟨Finite.of_surjective _ QuotientGroup.mk_surjective, ⟨_, rfl⟩, fun e he => ?_,
    fun e he f hf => ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := exists_lift he
    refine orderOf_eq_prime ?_ fun h => hnot hd ((QuotientGroup.eq_one_iff d).mp h)
    rw [← QuotientGroup.mk_pow, sq, Pair.mul_self hP hd, QuotientGroup.mk_one]
  · obtain ⟨d, hd, rfl⟩ := exists_lift he
    obtain ⟨d', hd', rfl⟩ := exists_lift hf
    have hdvd : orderOf ((d : Y ⧸ Q) * d') ∣ orderOf (d * d') := by
      rw [← QuotientGroup.mk_mul]
      exact orderOf_map_dvd (QuotientGroup.mk' Q) (d * d')
    exact mem_one_two_three_of_dvd hdvd (Pair.orderOf_mul_mem hP hd hd')
  · rw [eq_top_iff, ← map_top_of_surjective _ (QuotientGroup.mk'_surjective Q),
      ← Pair.closure_eq hP, MonoidHom.map_closure]
    exact closure_mono (Set.image_subset_iff.mpr fun d hd =>
      (QuotientGroup.mk' Q).map_isConj hd)

theorem hasCoreStar_of_quotient (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q)
    (h : HasCoreStar (Y ⧸ Q) (t : Y ⧸ Q)) : HasCoreStar Y t := by
  obtain ⟨ē₁, ē₂, ē₃, k₁, k₂, k₃, o₁, o₂, o₃, c₁₂, c₁₃, c₂₃, n₁₂, n₁₃, n₂₃⟩ := h
  obtain ⟨e₁, h₁, rfl⟩ := exists_lift k₁
  obtain ⟨e₂, h₂, rfl⟩ := exists_lift k₂
  obtain ⟨e₃, h₃, rfl⟩ := exists_lift k₃
  have hord : ∀ {e : Y}, IsConj t e → orderOf ((t : Y ⧸ Q) * e) = 3 → orderOf (t * e) = 3 := by
    intro e he h3
    have hdvd : 3 ∣ orderOf (t * e) := by
      rw [← h3, ← QuotientGroup.mk_mul]
      exact orderOf_map_dvd (QuotientGroup.mk' Q) (t * e)
    rcases Pair.orderOf_mul_mem hP (IsConj.refl t) he with h | h | h <;> rw [h] at hdvd ⊢ <;>
      norm_num at hdvd
  have hcomm : ∀ {a b : Y}, IsConj t a → IsConj t b → (a : Y ⧸ Q) * b = b * a →
      a * b = b * a := fun ha hb h => commute_of_mk_commute hP hQ2 ha hb h
  exact ⟨e₁, e₂, e₃, h₁, h₂, h₃, hord h₁ o₁, hord h₂ o₂, hord h₃ o₃, hcomm h₁ h₂ c₁₂,
    hcomm h₁ h₃ c₁₃, hcomm h₂ h₃ c₂₃, fun h => n₁₂ (by rw [h]), fun h => n₁₃ (by rw [h]),
    fun h => n₂₃ (by rw [h])⟩

theorem eq_of_mk_eq_of_le_center (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q)
    (hQZ : Q ≤ center Y) (ht : t ∉ center Y) {x y : Y} (hx : IsConj t x) (hy : IsConj t y)
    (hxy : (x : Y ⧸ Q) = y) : x = y := by
  obtain ⟨c, hc, hcx⟩ := exists_orderOf_mul_eq_three_of_not_mem_center hP ht hx
  have hcy := orderOf_eq_three_of_mk_eq hP hQ2 hc hx hy hxy hcx
  have hz : x⁻¹ * y ∈ Q := QuotientGroup.eq.mp hxy
  have hzc : Commute (c * x) (x⁻¹ * y) := Subgroup.mem_center_iff.mp (hQZ hz) (c * x)
  have e2 : (c * x) ^ 3 = 1 := by rw [← hcx, pow_orderOf_eq_one]
  have h3 : (x⁻¹ * y) ^ 3 = 1 := by
    have e1 : (c * y) ^ 3 = 1 := by rw [← hcy, pow_orderOf_eq_one]
    rwa [show c * y = c * x * (x⁻¹ * y) by group, hzc.mul_pow, e2, one_mul] at e1
  obtain ⟨k, hk⟩ := hQ2 ⟨x⁻¹ * y, hz⟩
  have hk' : (x⁻¹ * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hdvd1 : orderOf (x⁻¹ * y) ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  have h1 : x⁻¹ * y = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  exact inv_mul_eq_one.mp h1

private theorem adjSwap_zero_ne {m j : ℕ} (hj0 : 0 < j) (hj : j < m) :
    adjSwap m 0 ≠ adjSwap m j := by
  intro h
  have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ ⟨0, by omega⟩) h
  simp only [adjSwap_of_lt hj, adjSwap_of_lt (show 0 < m by omega), Equiv.swap_apply_left] at this
  rw [Equiv.swap_apply_of_ne_of_ne (by simp only [ne_eq, Fin.mk.injEq]; omega)
    (by simp only [ne_eq, Fin.mk.injEq]; omega)] at this
  exact absurd (Fin.mk.inj_iff.mp this) (by omega)

theorem exists_perm_of_quotient (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q)
    (hQZ : Q ≤ center Y) (ht : t ∉ center Y) {n : ℕ} (θ : Y ⧸ Q ≃* Equiv.Perm (Fin n))
    (hθ : (θ (t : Y ⧸ Q)).IsSwap) : ∃ e : Y ≃* Equiv.Perm (Fin n), (e t).IsSwap := by
  classical
  have hinj : ∀ {x y : Y}, IsConj t x → IsConj t y → (x : Y ⧸ Q) = y → x = y :=
    fun hx hy h => eq_of_mk_eq_of_le_center hP hQ2 hQZ ht hx hy h
  obtain ⟨c, hc, hct⟩ := exists_orderOf_mul_eq_three_of_not_mem_center hP ht (IsConj.refl t)
  have hn : 3 ≤ n := by
    by_contra hn
    have hn' : n < 3 := by omega
    have hab : ∀ a b : Equiv.Perm (Fin n), a * b = b * a := by
      interval_cases n <;> decide
    apply mul_ne_mul_of_orderOf (Pair.mul_self hP hc) (Pair.mul_self hP (IsConj.refl t)) hct
    apply commute_of_mk_commute hP hQ2 hc (IsConj.refl t)
    apply θ.injective
    rw [map_mul, map_mul, hab]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨a, b, hab, hθt⟩ := hθ
  have hconj : ∀ σ : Equiv.Perm (Fin (m + 1)), σ.IsSwap → IsConj (t : Y ⧸ Q) (θ.symm σ) := by
    rintro σ ⟨p, q, hpq, rfl⟩
    have := (θ.symm.toMonoidHom).map_isConj (Equiv.Perm.isConj_swap hab hpq)
    rwa [← hθt, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
  have hex : ∀ i : ℕ, ∃ d : Y, IsConj t d ∧ (i < m → (d : Y ⧸ Q) = θ.symm (adjSwap m i)) := by
    intro i
    by_cases hi : i < m
    · obtain ⟨d, hd, hdq⟩ := exists_lift (hconj (adjSwap m i) (by
        rw [adjSwap_of_lt hi]; exact ⟨_, _, by simp [Fin.ext_iff], rfl⟩))
      exact ⟨d, hd, fun _ => hdq⟩
    · exact ⟨t, IsConj.refl t, fun h => absurd h hi⟩
  choose x hxD hxq using hex
  have hcox' := CFSG.CGT.PushingUpLit.BHSSym.isCoxeterA_symm_adjSwap θ
  have hcox : IsCoxeterA m x := by
    refine ⟨fun i _ => Pair.mul_self hP (hxD i), fun i hi => ?_, fun i j hij hj => ?_⟩
    · apply hinj (Pair.mul_mul_mem hP (hxD i) (hxD (i + 1)))
        (Pair.mul_mul_mem hP (hxD (i + 1)) (hxD i))
      simp only [QuotientGroup.mk_mul, hxq i (by omega), hxq (i + 1) hi]
      exact hcox'.braid i hi
    · apply commute_of_mk_commute hP hQ2 (hxD i) (hxD j)
      rw [hxq i (by omega), hxq j hj]
      exact hcox'.comm i j hij hj
  have hx01 : x 0 ≠ x 1 := fun h => adjSwap_zero_ne (m := m) (j := 1) (by omega) (by omega)
    (θ.symm.injective (by rw [← hxq 0 (by omega), ← hxq 1 (by omega), h]))
  have hx02 : 3 ≤ m → x 0 ≠ x 2 := fun hm h =>
    adjSwap_zero_ne (m := m) (j := 2) (by omega) (by omega)
      (θ.symm.injective (by rw [← hxq 0 (by omega), ← hxq 2 (by omega), h]))
  obtain ⟨e, he⟩ :=
    CFSG.CGT.PushingUpLit.BHSSym.exists_mulEquiv_closure (by omega : 2 ≤ m) hcox hx01 hx02
  set ψ : Equiv.Perm (Fin (m + 1)) →* Y :=
    (closure (x '' Set.Iio m)).subtype.comp e.toMonoidHom with hψ
  have hψi : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hψadj : ∀ i, i < m → ψ (adjSwap m i) = x i := fun i hi => he i hi
  have hψθ : (QuotientGroup.mk' Q).comp ψ = θ.symm.toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense (closure_adjSwap m) ?_
    rintro _ ⟨i, hi, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [hψadj i hi, hxq i hi]
  have hψq : ∀ σ, (ψ σ : Y ⧸ Q) = θ.symm σ := fun σ => DFunLike.congr_fun hψθ σ
  have key : ∀ d : Y, IsConj t d → ψ (θ (d : Y ⧸ Q)) = d := by
    intro d hd
    have hσ : IsConj (adjSwap m 0) (θ (d : Y ⧸ Q)) := by
      have h1 : IsConj (θ (t : Y ⧸ Q)) (θ (d : Y ⧸ Q)) :=
        θ.toMonoidHom.map_isConj ((QuotientGroup.mk' Q).map_isConj hd)
      refine IsConj.trans ?_ h1
      rw [hθt, adjSwap_of_lt (by omega)]
      exact Equiv.Perm.isConj_swap (by simp [Fin.ext_iff]) hab
    have hmem : IsConj t (ψ (θ (d : Y ⧸ Q))) := by
      have := ψ.map_isConj hσ
      rw [hψadj 0 (by omega)] at this
      exact (hxD 0).trans this
    exact hinj hmem hd (by rw [hψq, MulEquiv.symm_apply_apply])
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Pair.closure_eq hP, closure_le]
    intro d hd
    exact MonoidHom.mem_range.mpr ⟨_, key d hd⟩
  have hbij : Function.Bijective ψ := ⟨hψi, hsurj⟩
  refine ⟨(MulEquiv.ofBijective ψ hbij).symm, ?_⟩
  have hte : (MulEquiv.ofBijective ψ hbij).symm t = θ (t : Y ⧸ Q) := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, key t (IsConj.refl t)]
  rw [hte, hθt]
  exact ⟨a, b, hab, rfl⟩

end Quotient

end CoreStar

@[expose] def OddTranspCoreSimpleInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (t : Y), Pair Y {x | IsConj t x} →
    Subgroup.center Y = ⊥ → (∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) →
    fusionOddCore Y = ⊥ →
    (∃ n : ℕ, ∃ e : Y ≃* Equiv.Perm (Fin n), (e t).IsSwap) ∨ CoreStar.HasCoreStar Y t

theorem oddTranspCoreThreeTranspInput_of_simple (hSF : OddTranspCoreSimpleInput) :
    OddTranspCoreThreeTranspInput := by
  suffices H : ∀ (N : ℕ) (Y : Type) [Group Y] [Finite Y] (t : Y), Nat.card Y = N →
      Pair Y {x | IsConj t x} → fusionOddCore Y = ⊥ →
      (∃ n : ℕ, ∃ e : Y ≃* Equiv.Perm (Fin n), (e t).IsSwap) ∨ CoreStar.HasCoreStar Y t by
    intro Y _ _ t hord hncl h3 hO
    exact H _ Y t rfl (CoreStar.pair_of_threeTransp hord hncl h3) hO
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro Y _ _ t hN hP hO
  by_cases htZ : t ∈ center Y
  · exact Or.inl ⟨2, CoreStar.exists_perm_two_of_mem_center hP htZ⟩
  by_cases hQ : ∃ Q : Subgroup Y, Q.Normal ∧ IsPGroup 2 Q ∧ ¬ Q ≤ center Y
  · obtain ⟨Q, hQn, hQ2, hQZ⟩ := hQ
    rcases CoreStar.perm_four_or_hasCoreStar hP hQ2 hQZ with h | h
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  push Not at hQ
  have hZ2 := CoreStar.isPGroup_two_center_of_fusionOddCore hO
  by_cases hZ : center Y = ⊥
  · exact hSF Y t hP hZ (fun Q hQn hQ2 => le_bot_iff.mp (hZ ▸ hQ Q hQn hQ2)) hO
  have : Finite (Y ⧸ center Y) := Finite.of_surjective _ QuotientGroup.mk_surjective
  have hlt : Nat.card (Y ⧸ center Y) < N := by
    rw [← hN, Subgroup.card_eq_card_quotient_mul_card_subgroup (center Y)]
    exact lt_mul_of_one_lt_right Nat.card_pos ((Subgroup.one_lt_card_iff_ne_bot _).mpr hZ)
  have hO' : fusionOddCore (Y ⧸ center Y) = ⊥ :=
    CFSG.QuasiDihedralFusion.oddCore_quotient_eq_bot_of_le_center hO (center Y) le_rfl hZ2
  rcases ih _ hlt (Y ⧸ center Y) (t : Y ⧸ center Y) rfl (CoreStar.pair_quotient hP htZ) hO' with
    ⟨n, θ, hθ⟩ | h
  · exact Or.inl ⟨n, CoreStar.exists_perm_of_quotient hP hZ2 le_rfl htZ θ hθ⟩
  · exact Or.inr (CoreStar.hasCoreStar_of_quotient hP hZ2 h)

end CFSG.LocalAnalysis.WeakClosure81
