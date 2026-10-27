module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeFixedCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LinearAlgebra.BinaryReflectionNormalizer
public import Mathlib.FieldTheory.Finiteness

public noncomputable section

namespace CFSG.Quasithin.SteinbergBQ

open Module

section FixedPoints

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem two_pow_finrank_modEq_one [Finite V] {p : ℕ} [Fact p.Prime]
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (hP : IsPGroup p P)
    (U : Submodule (ZMod 2) V) (hU : ∀ x ∈ P, ∀ u ∈ U, (x : V →ₗ[ZMod 2] V) u ∈ U)
    (hfix : ∀ u ∈ U, (∀ x ∈ P, (x : V →ₗ[ZMod 2] V) u = u) → u = 0) :
    2 ^ finrank (ZMod 2) U ≡ 1 [MOD p] := by
  let : MulAction P U :=
    { smul := fun x u => ⟨((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u,
        hU x x.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun x y u => Subtype.ext rfl }
  have h := hP.card_modEq_card_fixedPoints U
  have hfp : MulAction.fixedPoints P U = {0} := by
    ext u
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hu
      exact Subtype.ext (hfix u u.2 fun x hx => congrArg Subtype.val (hu ⟨x, hx⟩))
    · rintro rfl x
      exact Subtype.ext (map_zero _)
  have h1 : Nat.card (MulAction.fixedPoints P U) = 1 := by
    rw [hfp]
    exact Nat.card_unique
  have h2 : Nat.card U = 2 ^ finrank (ZMod 2) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h1, h2] at h
  exact h

end FixedPoints

section Commutator

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))

@[expose] def commSpan : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ x ∈ Q, ∃ v : V, w = (x : V →ₗ[ZMod 2] V) v - v}

theorem sub_mem_commSpan {x : LinearMap.GeneralLinearGroup (ZMod 2) V} (hx : x ∈ Q) (v : V) :
    (x : V →ₗ[ZMod 2] V) v - v ∈ commSpan Q :=
  Submodule.subset_span ⟨x, hx, v, rfl⟩

theorem map_mem_commSpan {y : LinearMap.GeneralLinearGroup (ZMod 2) V} (hy : y ∈ Q) {w : V}
    (hw : w ∈ commSpan Q) : (y : V →ₗ[ZMod 2] V) w ∈ commSpan Q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have e : (y : V →ₗ[ZMod 2] V) ((x : V →ₗ[ZMod 2] V) v - v) =
        (((y * x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v - v) -
          ((y : V →ₗ[ZMod 2] V) v - v) := by
      rw [map_sub, Units.val_mul, Module.End.mul_apply]
      abel
    rw [e]
    exact Submodule.sub_mem _ (sub_mem_commSpan Q (Q.mul_mem hy hx) v) (sub_mem_commSpan Q hy v)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

@[expose] def resEnd : Q →* Module.End (ZMod 2) (commSpan Q) where
  toFun x := ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V).restrict
    fun _ hw => map_mem_commSpan Q x.2 hw
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

@[expose] def resComm : Q →* LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q) :=
  (resEnd Q).toHomUnits

theorem resComm_apply (x : Q) (w : commSpan Q) :
    (((resComm Q x : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)) :
      commSpan Q →ₗ[ZMod 2] commSpan Q) w : V) =
      ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w := rfl

theorem mul_eq_inv_mul_of_inverts {t x : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (h : t⁻¹ * x⁻¹ * t = x⁻¹⁻¹) : t * x = x⁻¹ * t := by
  rw [inv_inv] at h
  calc t * x = t * (t⁻¹ * x⁻¹ * t) := by rw [h]
    _ = x⁻¹ * t := by group

theorem t_map_mem_commSpan {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) {w : V} (hw : w ∈ commSpan Q) :
    (t : V →ₗ[ZMod 2] V) w ∈ commSpan Q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have htx := mul_eq_inv_mul_of_inverts (htQ x⁻¹ (Q.inv_mem hx))
    have e : (t : V →ₗ[ZMod 2] V) ((x : V →ₗ[ZMod 2] V) v - v) =
        ((x⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((t : V →ₗ[ZMod 2] V) v) - (t : V →ₗ[ZMod 2] V) v := by
      rw [map_sub, ← Module.End.mul_apply, ← Units.val_mul, htx, Units.val_mul,
        Module.End.mul_apply]
    rw [e]
    exact sub_mem_commSpan Q (Q.inv_mem hx) _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem toAddSubgroup_commSpan :
    (commSpan Q).toAddSubgroup = CFSG.LocalAnalysis.ComponentInitial.coprimeCommutator Q V := by
  refine le_antisymm (fun w (hw : w ∈ commSpan Q) => ?_) ((AddSubgroup.closure_le _).2 ?_)
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, v, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨x, hx, v, rfl⟩
    | zero => exact AddSubgroup.zero_mem _
    | add a b _ _ ha hb => exact AddSubgroup.add_mem _ ha hb
    | smul c a _ ha =>
      obtain rfl | rfl : c = 0 ∨ c = 1 := by revert c; decide
      · rw [zero_smul]
        exact AddSubgroup.zero_mem _
      · rw [one_smul]
        exact ha
  · rintro _ ⟨a, ha, v, rfl⟩
    exact Submodule.subset_span ⟨a, ha, v, rfl⟩

end Commutator

section Decomposition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))

theorem finite_generalLinearGroup [FiniteDimensional (ZMod 2) V] :
    Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  infer_instance

theorem isPGroup_of_isElementaryAbelian {p : ℕ} [IsElementaryAbelian p Q] : IsPGroup p Q :=
  fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian
      (x : LinearMap.GeneralLinearGroup (ZMod 2) V) x.2)⟩

theorem commSpan_decomposition [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) [IsElementaryAbelian p Q] :
    (∀ w ∈ commSpan Q, (∀ x ∈ Q, (x : V →ₗ[ZMod 2] V) w = w) → w = 0) ∧
      ∀ v : V, ∃ w ∈ commSpan Q, ∃ c : V, (∀ x ∈ Q, (x : V →ₗ[ZMod 2] V) c = c) ∧
        w + c = v := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := finite_generalLinearGroup (V := V)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElementaryAbelian Q (p := p))
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card V) := by
    rw [hk, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out Nat.prime_two).2 hp2)
  have hdec :=
    (CFSG.LocalAnalysis.ComponentInitial.abelian_coprime_fixed_commutator_decomposition Q hcop).1
  rw [← toAddSubgroup_commSpan] at hdec
  refine ⟨fun w hw hfix => ?_, fun v => ?_⟩
  · have hmem : w ∈ (commSpan Q).toAddSubgroup ⊓
        CFSG.LocalAnalysis.ComponentInitial.coprimeFixed Q V := ⟨hw, fun a ha => hfix a ha⟩
    rw [hdec.inf_eq_bot] at hmem
    exact hmem
  · have hv : v ∈ (commSpan Q).toAddSubgroup ⊔
        CFSG.LocalAnalysis.ComponentInitial.coprimeFixed Q V := by
      rw [hdec.sup_eq_top]
      exact AddSubgroup.mem_top v
    obtain ⟨w, hw, c, hc, hwc⟩ := AddSubgroup.mem_sup.1 hv
    exact ⟨w, hw, c, fun x hx => hc x hx, hwc⟩

theorem resComm_injective [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [IsElementaryAbelian p Q] : Function.Injective (resComm Q) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hW : ∀ w ∈ commSpan Q,
      ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w := fun w hw => by
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q) =>
      (((g : commSpan Q →ₗ[ZMod 2] commSpan Q) ⟨w, hw⟩ : commSpan Q) : V)) hx
    exact this
  obtain ⟨-, hdec⟩ := commSpan_decomposition Q hp2
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨w, hw, c, hc, rfl⟩ := hdec v
  rw [map_add, hW w hw, hc x x.2]
  rfl

theorem sum_apply_eq_zero [Fintype Q] {w : V} (hw : w ∈ commSpan Q) :
    ∑ x : Q, ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    simp only [map_sub, Finset.sum_sub_distrib, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.mulRight ⟨y, hy⟩) _ _ fun x => rfl
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Finset.sum_congr rfl fun x _ => map_add _ a b, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul c a _ ha =>
    rw [Finset.sum_congr rfl fun x _ => map_smul _ c a, ← Finset.smul_sum, ha, smul_zero]

theorem exists_half_sign {G : Type*} [Group G] [Finite G] [DecidableEq G]
    (hinv : ∀ x : G, x⁻¹ = x → x = 1) :
    ∃ ε : G → ZMod 2, ∀ x, ε x + ε x⁻¹ = if x = 1 then 0 else 1 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  refine ⟨fun x => if (e x : ℕ) < e x⁻¹ then 1 else 0, fun x => ?_⟩
  simp only [inv_inv]
  by_cases hx : x = 1
  · subst hx
    simp
  · have hne : (e x : ℕ) ≠ e x⁻¹ := fun h => hx (hinv x (e.injective (Fin.ext h)).symm)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hx, h, not_lt.2 h.le]
    · simp [hx, h, not_lt.2 h.le]

theorem exists_t_sub_eq [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [IsElementaryAbelian p Q] {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) {w : V} (hw : w ∈ commSpan Q)
    (htw : (t : V →ₗ[ZMod 2] V) w = w) :
    ∃ u ∈ commSpan Q, (t : V →ₗ[ZMod 2] V) u - u = w := by
  classical
  have := finite_generalLinearGroup (V := V)
  have : Fintype Q := Fintype.ofFinite Q
  have hinv : ∀ x : Q, x⁻¹ = x → x = 1 := by
    intro x hx
    have h2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hx]
      exact inv_mul_cancel x
    have hp : x ^ p = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian
      (x : LinearMap.GeneralLinearGroup (ZMod 2) V) x.2)
    have := pow_gcd_eq_one.2 ⟨h2, hp⟩
    rwa [Nat.Coprime.gcd_eq_one ((Nat.coprime_primes Nat.prime_two Fact.out).2 hp2.symm),
      pow_one] at this
  obtain ⟨ε, hε⟩ := exists_half_sign hinv
  set φ : Q → V := fun x => ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w
    with hφ
  refine ⟨∑ x : Q, ε x • φ x,
    Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (map_mem_commSpan Q x.2 hw), ?_⟩
  have h1 : ∀ x : Q, (t : V →ₗ[ZMod 2] V) (ε x • φ x) = ε x • φ x⁻¹ := by
    intro x
    have htx := mul_eq_inv_mul_of_inverts (htQ _ (Q.inv_mem x.2))
    rw [map_smul, hφ]
    simp only
    rw [← Module.End.mul_apply, ← Units.val_mul, htx, Units.val_mul, Module.End.mul_apply, htw]
    rfl
  have htu : (t : V →ₗ[ZMod 2] V) (∑ x : Q, ε x • φ x) = ∑ x : Q, ε x⁻¹ • φ x := by
    rw [map_sum, Finset.sum_congr rfl fun x _ => h1 x]
    exact Fintype.sum_equiv (Equiv.inv Q) _ _ fun x => by simp
  have h2 : ∀ x : Q, ε x⁻¹ • φ x - ε x • φ x = φ x - if x = 1 then w else 0 := by
    intro x
    have hsub : ε x⁻¹ - ε x = ε x + ε x⁻¹ := by
      rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]
    rw [← sub_smul, hsub, hε]
    by_cases hx : x = 1
    · subst hx
      simp [hφ]
    · simp [hx]
  have h3 : ∑ x : Q, (if x = 1 then w else 0) = w := by simp
  rw [htu, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_sub_distrib,
    sum_apply_eq_zero Q hw, h3, zero_sub]
  exact neg_eq_of_add_eq_zero_left (CFSG.LinearAlgebra.zmod2_vec_add_self w)

theorem finrank_commSpan_eq_two_mul [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) [IsElementaryAbelian p Q] {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht : t ^ 2 = 1) (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) :
    finrank (ZMod 2) (commSpan Q) =
      2 * finrank (ZMod 2) ((commSpan Q).map ((t : V →ₗ[ZMod 2] V) - 1)) := by
  set W := commSpan Q with hWdef
  set T : Module.End (ZMod 2) V := (t : V →ₗ[ZMod 2] V) - 1 with hT
  have hTW : ∀ w ∈ W, T w ∈ W := fun w hw => by
    rw [hT, LinearMap.sub_apply, Module.End.one_apply]
    exact W.sub_mem (t_map_mem_commSpan Q htQ hw) hw
  let TW : Module.End (ZMod 2) W := T.restrict hTW
  have htt : ∀ v, (t : V →ₗ[ZMod 2] V) ((t : V →ₗ[ZMod 2] V) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← Units.val_mul, ← pow_two, ht, Units.val_one,
      Module.End.one_apply]
  have hTT : ∀ v, T (T v) = 0 := fun v => by
    rw [hT, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, htt]
    have e : v - (t : V →ₗ[ZMod 2] V) v - ((t : V →ₗ[ZMod 2] V) v - v) =
        (v + v) - ((t : V →ₗ[ZMod 2] V) v + (t : V →ₗ[ZMod 2] V) v) := by abel
    rw [e, CFSG.LinearAlgebra.zmod2_vec_add_self, CFSG.LinearAlgebra.zmod2_vec_add_self, sub_self]
  have hker : LinearMap.ker TW = LinearMap.range TW := by
    refine le_antisymm (fun w hw => ?_) ?_
    · have h0 : T w = 0 := congrArg Subtype.val hw
      have htw : (t : V →ₗ[ZMod 2] V) w = w := by
        rw [hT, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
        exact h0
      obtain ⟨u, hu, hut⟩ := exists_t_sub_eq Q hp2 htQ w.2 htw
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      change T u = w
      rw [hT, LinearMap.sub_apply, Module.End.one_apply]
      exact hut
    · rintro _ ⟨w, rfl⟩
      exact Subtype.ext (hTT w)
  have h := LinearMap.finrank_range_add_finrank_ker TW
  rw [hker] at h
  have hmap : (LinearMap.range TW).map W.subtype = W.map T := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨T w, hTW w hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
  have h2 := Submodule.finrank_map_subtype_eq W (LinearMap.range TW)
  rw [hmap] at h2
  omega

end Decomposition

section FiveSupport

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

theorem eq_bot_or_eq_top_of_five (hU : finrank (ZMod 2) U = 4)
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) (hP : IsPGroup 5 P)
    (hfix : ∀ u : U, (∀ x ∈ P, (x : U →ₗ[ZMod 2] U) u = u) → u = 0)
    (U₀ : Submodule (ZMod 2) U) (hU₀ : ∀ x ∈ P, ∀ u ∈ U₀, (x : U →ₗ[ZMod 2] U) u ∈ U₀) :
    U₀ = ⊥ ∨ U₀ = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have h := two_pow_finrank_modEq_one P hP U₀ hU₀ fun u _ hu => hfix u hu
  have hle : finrank (ZMod 2) U₀ ≤ 4 := hU ▸ Submodule.finrank_le U₀
  by_cases h0 : U₀ = ⊥
  · exact Or.inl h0
  · right
    have hpos : finrank (ZMod 2) U₀ ≠ 0 := fun h' => h0 (Submodule.finrank_eq_zero.1 h')
    have h4 : finrank (ZMod 2) U₀ = 4 := by
      set d := finrank (ZMod 2) U₀ with hd
      interval_cases d <;> first | rfl | exact absurd rfl hpos | exact absurd h (by decide)
    exact Submodule.eq_top_of_finrank_eq (h4.trans hU.symm)

theorem fixed_eq_zero_of_ne_one (hU : finrank (ZMod 2) U = 4)
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) (hP : IsPGroup 5 P)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hfix : ∀ u : U, (∀ x ∈ P, (x : U →ₗ[ZMod 2] U) u = u) → u = 0)
    {X : LinearMap.GeneralLinearGroup (ZMod 2) U} (hX : X ∈ P) (hX1 : X ≠ 1) :
    ∀ u : U, (X : U →ₗ[ZMod 2] U) u = u → u = 0 := by
  have hmem : ∀ u, u ∈ LinearMap.ker ((X : U →ₗ[ZMod 2] U) - 1) ↔
      (X : U →ₗ[ZMod 2] U) u = u := fun u => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hK := eq_bot_or_eq_top_of_five hU P hP hfix (LinearMap.ker ((X : U →ₗ[ZMod 2] U) - 1))
    (by
      intro y hy u hu
      rw [hmem] at hu ⊢
      rw [← Module.End.mul_apply, ← Units.val_mul, hcomm X hX y hy, Units.val_mul,
        Module.End.mul_apply, hu])
  rcases hK with hK | hK
  · intro u hu
    have h := (hmem u).2 hu
    rw [hK] at h
    exact (Submodule.mem_bot _).1 h
  · exfalso
    apply hX1
    refine Units.ext (LinearMap.ext fun u => ?_)
    exact (hmem u).1 (hK ▸ Submodule.mem_top)

omit [FiniteDimensional (ZMod 2) U] in
theorem pow_apply_mem {X : LinearMap.GeneralLinearGroup (ZMod 2) U} {U₀ : Submodule (ZMod 2) U}
    (hX : ∀ u ∈ U₀, (X : U →ₗ[ZMod 2] U) u ∈ U₀) (n : ℕ) :
    ∀ u ∈ U₀, ((X ^ n : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) u ∈ U₀ := by
  induction n with
  | zero =>
    intro u hu
    simpa using hu
  | succ n ih =>
    intro u hu
    rw [pow_succ, Units.val_mul, Module.End.mul_apply]
    exact ih _ (hX u hu)

omit [FiniteDimensional (ZMod 2) U] in
theorem zpow_apply_mem {X : LinearMap.GeneralLinearGroup (ZMod 2) U} {U₀ : Submodule (ZMod 2) U}
    (hX : ∀ u ∈ U₀, (X : U →ₗ[ZMod 2] U) u ∈ U₀)
    (hXinv : ∀ u ∈ U₀, ((X⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) u ∈ U₀) :
    ∀ y ∈ Subgroup.zpowers X, ∀ u ∈ U₀, (y : U →ₗ[ZMod 2] U) u ∈ U₀ := by
  rintro _ ⟨k, rfl⟩
  induction k using Int.induction_on with
  | zero =>
    intro u hu
    simpa using hu
  | succ k ih =>
    intro u hu
    simp only [zpow_add_one, Units.val_mul, Module.End.mul_apply] at ih ⊢
    exact ih _ (hX u hu)
  | pred k ih =>
    intro u hu
    simp only [zpow_sub_one, Units.val_mul, Module.End.mul_apply] at ih ⊢
    exact ih _ (hXinv u hu)

theorem eq_bot_or_eq_top_of_ne_one (hU : finrank (ZMod 2) U = 4)
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) (hP : IsPGroup 5 P)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hfix : ∀ u : U, (∀ x ∈ P, (x : U →ₗ[ZMod 2] U) u = u) → u = 0)
    {X : LinearMap.GeneralLinearGroup (ZMod 2) U} (hX : X ∈ P) (hX1 : X ≠ 1)
    (U₀ : Submodule (ZMod 2) U) (hU₀ : ∀ u ∈ U₀, (X : U →ₗ[ZMod 2] U) u ∈ U₀) :
    U₀ = ⊥ ∨ U₀ = ⊤ := by
  obtain ⟨n, hn⟩ := hP ⟨X, hX⟩
  have hXn : X ^ (5 ^ n) = 1 := congrArg Subtype.val hn
  have hXinv : X⁻¹ = X ^ (5 ^ n - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), hXn]
  refine eq_bot_or_eq_top_of_five hU (Subgroup.zpowers X) (hP.to_le (Subgroup.zpowers_le.2 hX))
    (fun u hu => fixed_eq_zero_of_ne_one hU P hP hcomm hfix hX hX1 u
      (hu X (Subgroup.mem_zpowers X))) U₀ ?_
  exact zpow_apply_mem hU₀ fun u hu => hXinv ▸ pow_apply_mem hU₀ _ u hu

end FiveSupport

section Field

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
variable {X : Module.End (ZMod 2) U}

omit [FiniteDimensional (ZMod 2) U] in
theorem adjoin_le_centralizer_singleton :
    Algebra.adjoin (ZMod 2) {X} ≤ Subalgebra.centralizer (ZMod 2) {X} :=
  Algebra.adjoin_le (Set.singleton_subset_iff.2 ((Subalgebra.mem_centralizer_iff _).2
    fun g hg => by rw [Set.mem_singleton_iff.1 hg]))

omit [FiniteDimensional (ZMod 2) U] in
theorem mul_comm_of_mem_adjoin {e : Module.End (ZMod 2) U}
    (he : e ∈ Algebra.adjoin (ZMod 2) {X}) : X * e = e * X :=
  (Subalgebra.mem_centralizer_iff _).1 (adjoin_le_centralizer_singleton he) X rfl

omit [FiniteDimensional (ZMod 2) U] in
theorem mul_comm_of_mem_adjoin_of_mem {e f : Module.End (ZMod 2) U}
    (he : e ∈ Algebra.adjoin (ZMod 2) {X}) (hf : f ∈ Algebra.adjoin (ZMod 2) {X}) :
    e * f = f * e := by
  have hle : Algebra.adjoin (ZMod 2) {X} ≤ Subalgebra.centralizer (ZMod 2) {e} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 ((Subalgebra.mem_centralizer_iff _).2
      fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]
        exact (mul_comm_of_mem_adjoin he).symm))
  exact (Subalgebra.mem_centralizer_iff _).1 (hle hf) e rfl

variable (hirr : ∀ U₀ : Submodule (ZMod 2) U, (∀ u ∈ U₀, X u ∈ U₀) → U₀ = ⊥ ∨ U₀ = ⊤)
include hirr

omit [FiniteDimensional (ZMod 2) U] in
theorem injective_of_mem_adjoin {e : Module.End (ZMod 2) U}
    (he : e ∈ Algebra.adjoin (ZMod 2) {X}) (he0 : e ≠ 0) : Function.Injective e := by
  have hK := hirr (LinearMap.ker e) fun u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← Module.End.mul_apply, ← mul_comm_of_mem_adjoin he, Module.End.mul_apply, hu, map_zero]
  rcases hK with hK | hK
  · exact LinearMap.ker_eq_bot.1 hK
  · exact (he0 (LinearMap.ext fun u => (hK ▸ Submodule.mem_top : u ∈ LinearMap.ker e))).elim

theorem exists_mul_eq_one_of_mem_adjoin {e : Module.End (ZMod 2) U}
    (he : e ∈ Algebra.adjoin (ZMod 2) {X}) (he0 : e ≠ 0) :
    ∃ f ∈ Algebra.adjoin (ZMod 2) {X}, e * f = 1 := by
  have : Finite (Module.End (ZMod 2) U) := Module.finite_of_finite (ZMod 2)
  have hinj : Function.Injective fun f : Algebra.adjoin (ZMod 2) {X} =>
      (⟨e, he⟩ : Algebra.adjoin (ZMod 2) {X}) * f := by
    intro f f' hff'
    have h := congrArg Subtype.val hff'
    refine Subtype.ext (LinearMap.ext fun u => injective_of_mem_adjoin hirr he he0 ?_)
    exact LinearMap.congr_fun h u
  obtain ⟨f, hf⟩ := (Finite.injective_iff_surjective.1 hinj) 1
  exact ⟨f, f.2, congrArg Subtype.val hf⟩

theorem isField_adjoin [Nontrivial U] : IsField (Algebra.adjoin (ZMod 2) {X}) where
  exists_pair_ne := ⟨0, 1, fun h => by
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    exact hu (LinearMap.congr_fun (congrArg Subtype.val h) u).symm⟩
  mul_comm a b := Subtype.ext (mul_comm_of_mem_adjoin_of_mem a.2 b.2)
  mul_inv_cancel {a} ha := by
    obtain ⟨f, hf, hef⟩ :=
      exists_mul_eq_one_of_mem_adjoin hirr a.2 fun h => ha (Subtype.ext h)
    exact ⟨⟨f, hf⟩, Subtype.ext hef⟩

omit [FiniteDimensional (ZMod 2) U] in
theorem exists_mem_adjoin_apply_eq {u₀ : U} (hu₀ : u₀ ≠ 0) (u : U) :
    ∃ e ∈ Algebra.adjoin (ZMod 2) {X}, e u₀ = u := by
  let Im : Submodule (ZMod 2) U :=
    (Subalgebra.toSubmodule (Algebra.adjoin (ZMod 2) {X})).map (LinearMap.applyₗ u₀)
  have hmem : ∀ v, v ∈ Im ↔ ∃ e ∈ Algebra.adjoin (ZMod 2) {X}, e u₀ = v := fun v => by
    simp [Im]
  have hIm := hirr Im fun v hv => by
    obtain ⟨e, he, rfl⟩ := (hmem v).1 hv
    exact (hmem _).2 ⟨X * e, (Algebra.adjoin (ZMod 2) {X}).mul_mem
      (Algebra.self_mem_adjoin_singleton _ X) he, rfl⟩
  rcases hIm with hIm | hIm
  · exfalso
    have h1 : u₀ ∈ Im := (hmem u₀).2 ⟨1, (Algebra.adjoin (ZMod 2) {X}).one_mem, rfl⟩
    rw [hIm] at h1
    exact hu₀ ((Submodule.mem_bot _).1 h1)
  · exact (hmem u).1 (hIm ▸ Submodule.mem_top)

omit [FiniteDimensional (ZMod 2) U] in
theorem card_adjoin [Nontrivial U] : Nat.card (Algebra.adjoin (ZMod 2) {X}) = Nat.card U := by
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : U)
  refine Nat.card_congr (Equiv.ofBijective
    (fun e : Algebra.adjoin (ZMod 2) {X} => (e : Module.End (ZMod 2) U) u₀)
    ⟨fun e e' h => ?_, fun u => ?_⟩)
  · by_contra hne
    have hsub : (e : Module.End (ZMod 2) U) - e' ≠ 0 := fun h0 =>
      hne (Subtype.ext (sub_eq_zero.1 h0))
    have hinj := injective_of_mem_adjoin hirr
      ((Algebra.adjoin (ZMod 2) {X}).sub_mem e.2 e'.2) hsub
    apply hu₀
    apply hinj
    rw [LinearMap.sub_apply, map_zero]
    exact sub_eq_zero.2 h
  · obtain ⟨e, he, heu⟩ := exists_mem_adjoin_apply_eq hirr hu₀ u
    exact ⟨⟨e, he⟩, heu⟩

omit [FiniteDimensional (ZMod 2) U] in
theorem mem_adjoin_of_commute [Nontrivial U] {g : Module.End (ZMod 2) U} (hg : g * X = X * g) :
    g ∈ Algebra.adjoin (ZMod 2) {X} := by
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : U)
  obtain ⟨e, he, heu⟩ := exists_mem_adjoin_apply_eq hirr hu₀ (g u₀)
  have hc : (g - e) * X = X * (g - e) := by
    rw [sub_mul, mul_sub, hg, ← mul_comm_of_mem_adjoin he]
  have hK := hirr (LinearMap.ker (g - e)) fun u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hu, map_zero]
  rcases hK with hK | hK
  · exfalso
    have h1 : u₀ ∈ LinearMap.ker (g - e) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, heu, sub_self]
    rw [hK] at h1
    exact hu₀ ((Submodule.mem_bot _).1 h1)
  · have h0 : g - e = 0 :=
      LinearMap.ext fun u => (hK ▸ Submodule.mem_top : u ∈ LinearMap.ker (g - e))
    rw [sub_eq_zero.1 h0]
    exact he

end Field

section Core

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

theorem five_support_core (hU : finrank (ZMod 2) U = 4)
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) (hP : IsPGroup 5 P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hfix : ∀ u : U, (∀ x ∈ P, (x : U →ₗ[ZMod 2] U) u = u) → u = 0) :
    Nat.card P = 5 ∧
      (∀ U₀ : Submodule (ZMod 2) U, (∀ x ∈ P, ∀ u ∈ U₀, (x : U →ₗ[ZMod 2] U) u ∈ U₀) →
        U₀ = ⊥ ∨ U₀ = ⊤) ∧
      (∀ x ∈ P, x ≠ 1 →
        IsField (Algebra.adjoin (ZMod 2) {(x : Module.End (ZMod 2) U)}) ∧
        Nat.card (Algebra.adjoin (ZMod 2) {(x : Module.End (ZMod 2) U)}) = 16 ∧
        ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) U,
          g ∈ Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) U)) ↔
            (g : Module.End (ZMod 2) U) ∈
              Algebra.adjoin (ZMod 2) {(x : Module.End (ZMod 2) U)}) ∧
      (∀ g ∈ Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) U)),
        ∀ h ∈ Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) U)),
          g * h = h * g) ∧
      Nat.card (Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) U))) = 15 ∧
      ∃! H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U),
        H ≤ Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) U)) ∧
          Nat.card H = 5 := by
  classical
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := finite_generalLinearGroup (V := U)
  have : Finite (Module.End (ZMod 2) U) := Module.finite_of_finite (ZMod 2)
  set C := Subgroup.centralizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) U)) with hC
  have hirrx : ∀ x ∈ P, x ≠ 1 → ∀ U₀ : Submodule (ZMod 2) U,
      (∀ u ∈ U₀, (x : U →ₗ[ZMod 2] U) u ∈ U₀) → U₀ = ⊥ ∨ U₀ = ⊤ :=
    fun x hx hx1 U₀ hU₀ => eq_bot_or_eq_top_of_ne_one hU P hP hcomm hfix hx hx1 U₀ hU₀
  have hmemC : ∀ x ∈ P, x ≠ 1 → ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) U,
      g ∈ C ↔ (g : Module.End (ZMod 2) U) ∈
        Algebra.adjoin (ZMod 2) {(x : Module.End (ZMod 2) U)} := by
    intro x hx hx1 g
    rw [hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg
      exact mem_adjoin_of_commute (hirrx x hx hx1)
        (by rw [← Units.val_mul, ← hg x hx, Units.val_mul])
    · intro hg y hy
      have hyE := mem_adjoin_of_commute (hirrx x hx hx1)
        (show (y : Module.End (ZMod 2) U) * x = x * y by
          rw [← Units.val_mul, ← Units.val_mul, hcomm y hy x hx])
      exact Units.ext (mul_comm_of_mem_adjoin_of_mem hyE hg)
  have hcard16 : Nat.card U = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hU]
    norm_num
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  set E := Algebra.adjoin (ZMod 2) {(x : Module.End (ZMod 2) U)} with hE
  have hirr := hirrx x hx hx1'
  have hCcomm : ∀ g ∈ C, ∀ h ∈ C, g * h = h * g := fun g hg h hh =>
    Units.ext (mul_comm_of_mem_adjoin_of_mem ((hmemC x hx hx1' g).1 hg) ((hmemC x hx hx1' h).1 hh))
  have hne0 : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) U, (g : Module.End (ZMod 2) U) ≠ 0 :=
    fun g h0 => by
      have h1 : ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) U) : Module.End (ZMod 2) U) =
          0 := by rw [Units.val_mul, h0, mul_zero]
      rw [inv_mul_cancel, Units.val_one] at h1
      exact one_ne_zero h1
  have hCcard : Nat.card C = 15 := by
    have : Fintype E := Fintype.ofFinite E
    let f : C → {e : E // e ≠ 0} := fun g =>
      ⟨⟨(g : LinearMap.GeneralLinearGroup (ZMod 2) U), (hmemC x hx hx1' g).1 g.2⟩,
        fun h => hne0 g (congrArg Subtype.val h)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun g g' h => Subtype.ext (Units.ext (congrArg
        (fun e : {e : E // e ≠ 0} => ((e.1 : E) : Module.End (ZMod 2) U)) h)), ?_⟩
      rintro ⟨⟨e, he⟩, he0⟩
      have he0' : e ≠ 0 := fun h => he0 (Subtype.ext h)
      obtain ⟨f', hf', hef⟩ := exists_mul_eq_one_of_mem_adjoin hirr he he0'
      have hfe : f' * e = 1 := by rw [mul_comm_of_mem_adjoin_of_mem hf' he, hef]
      let u : LinearMap.GeneralLinearGroup (ZMod 2) U := ⟨e, f', hef, hfe⟩
      exact ⟨⟨u, (hmemC x hx hx1' u).2 he⟩, rfl⟩
    have h2 : Nat.card {e : E // e ≠ 0} = Nat.card E - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq]
    rw [Nat.card_congr (Equiv.ofBijective f hf), h2, hE, card_adjoin hirr, hcard16]
  let R : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U) :=
    { carrier := {g | g ∈ C ∧ g ^ 5 = 1}
      mul_mem' := fun {a b} ha hb => ⟨C.mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hCcomm a ha.1 b hb.1) 5, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨C.one_mem, one_pow 5⟩
      inv_mem' := fun {a} ha => ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hRC : R ≤ C := fun g hg => hg.1
  have hle5 : ∀ H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U), H ≤ C → IsPGroup 5 H →
      ∃ k ≤ 1, Nat.card H = 5 ^ k := by
    intro H hHC hHp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hHp
    have hdvd : 5 ^ k ∣ 15 := hk ▸ hCcard ▸ Subgroup.card_dvd_of_le hHC
    refine ⟨k, ?_, hk⟩
    by_contra hk2
    have h25 : 5 ^ 2 ∣ 15 := (pow_dvd_pow 5 (by omega)).trans hdvd
    norm_num at h25
  have hRp : IsPGroup 5 R := fun r => ⟨1, Subtype.ext (by simpa using r.2.2)⟩
  have hRcard : Nat.card R ≤ 5 := by
    obtain ⟨k, hk1, hk⟩ := hle5 R hRC hRp
    rw [hk]
    exact (Nat.pow_le_pow_right (by norm_num) hk1).trans (by norm_num)
  have heqR : ∀ H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U), H ≤ C →
      Nat.card H = 5 → H = R := by
    intro H hHC hH5
    have hHR : H ≤ R := fun h hh => ⟨hHC hh, by
      have := congrArg Subtype.val (pow_card_eq_one' (G := H) (x := ⟨h, hh⟩))
      rwa [hH5] at this⟩
    exact Subgroup.eq_of_le_of_card_ge hHR (hRcard.trans hH5.ge)
  have hPC : P ≤ C := fun a ha => Subgroup.mem_centralizer_iff.2 fun h hh => hcomm h hh a ha
  have hPcard : Nat.card P = 5 := by
    obtain ⟨k, hk1, hk⟩ := hle5 P hPC hP
    interval_cases k
    · exact absurd (Subgroup.eq_bot_of_card_eq P (by rw [hk, pow_zero])) hP1
    · rw [hk, pow_one]
  refine ⟨hPcard, fun U₀ hU₀ => eq_bot_or_eq_top_of_five hU P hP hfix U₀ hU₀,
    fun y hy hy1 => ?_, hCcomm, hCcard,
    ⟨P, ⟨hPC, hPcard⟩, fun H hH => (heqR H hH.1 hH.2).trans (heqR P hPC hPcard).symm⟩⟩
  have hirry := hirrx y hy hy1
  refine ⟨isField_adjoin hirry, ?_, hmemC y hy hy1⟩
  rw [card_adjoin hirry, hcard16]

end Core

theorem small_inverted_odd_binary_module_forces_cyclic_five_support {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {p : ℕ}
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    [IsElementaryAbelian p Q] (hQ : Q ≠ ⊥) (t : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (ht : t ^ 2 = 1) (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) :
    (∀ w ∈ commSpan Q, (t : V →ₗ[ZMod 2] V) w ∈ commSpan Q) ∧
      Function.Injective (resComm Q) ∧
      finrank (ZMod 2) (commSpan Q) =
        2 * finrank (ZMod 2) ((commSpan Q).map ((t : V →ₗ[ZMod 2] V) - 1)) ∧
      4 ≤ finrank (ZMod 2) (commSpan Q) ∧
      (finrank (ZMod 2) (commSpan Q) ≤ 4 →
        p = 5 ∧ Nat.card Q = 5 ∧ finrank (ZMod 2) (commSpan Q) = 4 ∧
        (∀ U : Submodule (ZMod 2) (commSpan Q),
          (∀ x : Q, ∀ u ∈ U, ((resComm Q x : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)) :
            commSpan Q →ₗ[ZMod 2] commSpan Q) u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
        (∀ x : Q, x ≠ 1 →
          IsField (Algebra.adjoin (ZMod 2)
            {((resComm Q x : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)) :
              Module.End (ZMod 2) (commSpan Q))}) ∧
          Nat.card (Algebra.adjoin (ZMod 2)
            {((resComm Q x : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)) :
              Module.End (ZMod 2) (commSpan Q))}) = 16 ∧
          ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q),
            g ∈ Subgroup.centralizer
                ((resComm Q).range : Set (LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q))) ↔
              (g : Module.End (ZMod 2) (commSpan Q)) ∈ Algebra.adjoin (ZMod 2)
                {((resComm Q x : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)) :
                  Module.End (ZMod 2) (commSpan Q))}) ∧
        (∀ g ∈ Subgroup.centralizer
            ((resComm Q).range : Set (LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q))),
          ∀ h ∈ Subgroup.centralizer
            ((resComm Q).range : Set (LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q))),
            g * h = h * g) ∧
        Nat.card (Subgroup.centralizer
          ((resComm Q).range : Set (LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)))) = 15 ∧
        ∃! H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)),
          H ≤ Subgroup.centralizer
            ((resComm Q).range : Set (LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q))) ∧
            Nat.card H = 5) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := finite_generalLinearGroup (V := V)
  obtain ⟨hfixW, -⟩ := commSpan_decomposition Q hp2
  have hinj := resComm_injective Q hp2
  have hdim := finrank_commSpan_eq_two_mul Q hp2 ht htQ
  have hQp := isPGroup_of_isElementaryAbelian Q (p := p)
  have hmod := two_pow_finrank_modEq_one Q hQp (commSpan Q)
    (fun x hx u hu => map_mem_commSpan Q hx hu) hfixW
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
  have hW0 : finrank (ZMod 2) (commSpan Q) ≠ 0 := by
    intro h0
    have hbot : commSpan Q = ⊥ := Submodule.finrank_eq_zero.1 h0
    apply hy1
    apply hinj
    rw [map_one]
    refine Units.ext (LinearMap.ext fun w => Subtype.ext ?_)
    have hw : (w : V) = 0 := by
      have h1 : (w : V) ∈ (⊥ : Submodule (ZMod 2) V) := hbot ▸ w.2
      exact (Submodule.mem_bot _).1 h1
    simp [resComm_apply, hw]
  have h4 : 4 ≤ finrank (ZMod 2) (commSpan Q) := by
    rcases (by omega : finrank (ZMod 2) (commSpan Q) = 2 ∨ 4 ≤ finrank (ZMod 2) (commSpan Q))
      with h2 | h4
    · exfalso
      rw [h2] at hmod
      have h' : 4 % p = 1 % p := hmod
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
      omega
    · exact h4
  refine ⟨fun w hw => t_map_mem_commSpan Q htQ hw, hinj, hdim, h4, fun hle => ?_⟩
  have hn4 : finrank (ZMod 2) (commSpan Q) = 4 := le_antisymm hle h4
  have hp5' : p = 5 := by
    rw [hn4] at hmod
    have hdvd : p ∣ 15 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
    have hle15 : p ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p <;> first | rfl | (exfalso; revert hdvd; decide) |
      (exfalso; exact absurd hp.out (by decide))
  subst hp5'
  have hQcomm : ∀ a b : Q, a * b = b * a := fun a b =>
    (inferInstance : IsMulCommutative Q).is_comm.comm a b
  have hPp : IsPGroup 5 (resComm Q).range := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨k, hk⟩ := hQp x
    exact ⟨k, Subtype.ext (show (resComm Q x) ^ (5 ^ k) = 1 by rw [← map_pow, hk, map_one])⟩
  have hP1 : (resComm Q).range ≠ ⊥ := Subgroup.ne_bot_iff_exists_ne_one.2
    ⟨⟨resComm Q y, y, rfl⟩, fun h => hy1 (hinj (by rw [map_one]; exact congrArg Subtype.val h))⟩
  have hPcomm : ∀ a ∈ (resComm Q).range, ∀ b ∈ (resComm Q).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hQcomm]
  have hPfix : ∀ u : commSpan Q, (∀ z ∈ (resComm Q).range,
      ((z : LinearMap.GeneralLinearGroup (ZMod 2) (commSpan Q)) :
        commSpan Q →ₗ[ZMod 2] commSpan Q) u = u) → u = 0 := by
    intro u hu
    refine Subtype.ext (hfixW u u.2 fun x hx => ?_)
    exact congrArg Subtype.val (hu _ ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨hcard, hirr, hfield, hcomm, hCcard, huniq⟩ :=
    five_support_core hn4 (resComm Q).range hPp hP1 hPcomm hPfix
  refine ⟨rfl, ?_, hn4, fun U hU => hirr U ?_, fun x hx => hfield _ ⟨x, rfl⟩ ?_, hcomm, hCcard,
    huniq⟩
  · rw [← hcard]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  · rintro _ ⟨x, rfl⟩ u hu
    exact hU x u hu
  · intro h
    apply hx
    apply hinj
    rw [h, map_one]

end CFSG.Quasithin.SteinbergBQ
