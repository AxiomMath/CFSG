module

public import CFSG.Quasithin.Vol2.KGFact12617LieW
public import CFSG.LieType.BorelTits.SpecialLinear
public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Module
open scoped Matrix

section Counting

variable {K V H : Type*} [Field K] [AddCommGroup V] [Module K V] [Group H]

theorem card_modEq_card_inf_fix [Finite V] (ρ : H →* Module.End K V) {p : ℕ} [Fact p.Prime]
    (G : Subgroup H) (hG : IsPGroup p ↥G) (W : Submodule K V)
    (hW : ∀ g ∈ G, ∀ v ∈ W, ρ g v ∈ W) :
    Nat.card ↥W ≡ Nat.card ↥(W ⊓ fixFlag ρ G 1) [MOD p] := by
  classical
  let act : MulAction ↥G ↥W :=
    { smul := fun g w => ⟨ρ g w, hW g g.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ρ ((1 : ↥G) : H) w = w
        simp)
      mul_smul := fun g h w => Subtype.ext (by
        show ρ ((g * h : ↥G) : H) w = ρ g (ρ h w)
        simp) }
  have hsmul : ∀ (g : ↥G) (w : ↥W), ((g • w : ↥W) : V) = ρ g w := fun _ _ => rfl
  have hmod := hG.card_modEq_card_fixedPoints ↥W
  have heq : Nat.card (MulAction.fixedPoints ↥G ↥W) = Nat.card ↥(W ⊓ fixFlag ρ G 1) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.1.2, ?_⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun g => Subtype.ext ?_⟩
        left_inv := fun w => rfl
        right_inv := fun v => rfl }
    · refine (mem_fixFlag_succ ρ (k := 0)).2 fun g hg => ?_
      have h := congrArg Subtype.val (w.2 ⟨g, hg⟩)
      rw [hsmul] at h
      rw [h, sub_self, fixFlag_zero]
      exact Submodule.zero_mem _
    · rw [hsmul]
      have h := (mem_fixFlag_succ ρ (k := 0)).1 v.2.2 g g.2
      rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h
      exact h
  rwa [heq] at hmod

end Counting

section SL5

variable {F : Type} [Field F]

local notation "SLF" => StatedSL 5 F
local notation "ρ" => natRep (StatedSL 5 F)

theorem card_eq_two_pow (hF : Nat.card F = 2) (W : Submodule F (Fin 5 → F)) :
    Nat.card ↥W = 2 ^ finrank F ↥W := by
  rw [Module.natCard_eq_pow_finrank (K := F), hF]

theorem finrank_v5 : finrank F (Fin 5 → F) = 5 := by
  rw [finrank_fintype_fun_eq_card]
  rfl

theorem finrank_le_five (W : Submodule F (Fin 5 → F)) : finrank F ↥W ≤ 5 :=
  (Submodule.finrank_le W).trans finrank_v5.le

theorem pow_mod_five_cases {k j : ℕ} (hk : k ≤ 5) (hj : j ≤ 1) (h : 2 ^ k ≡ 2 ^ j [MOD 5]) :
    (j = 0 ∧ (k = 0 ∨ k = 4)) ∨ (j = 1 ∧ (k = 1 ∨ k = 5)) := by
  unfold Nat.ModEq at h
  interval_cases k <;> interval_cases j <;> simp_all

theorem zpowers_stable {x : ↥SLF} (hx : orderOf x = 5) {W : Submodule F (Fin 5 → F)}
    (hW : ∀ v ∈ W, ρ x v ∈ W) : ∀ g ∈ Subgroup.zpowers x, ∀ v ∈ W, ρ g v ∈ W := by
  have hpow : ∀ n : ℕ, ∀ v ∈ W, ρ (x ^ n) v ∈ W := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact ih _ (hW v hv)
  intro g hg v hv
  have hfin : IsOfFinOrder x := orderOf_pos_iff.1 (by rw [hx]; norm_num)
  obtain ⟨n, rfl⟩ := hfin.mem_powers_iff_mem_zpowers.2 hg
  exact hpow n v hv

theorem mem_fix_zpowers_iff {x : ↥SLF} {v : Fin 5 → F} :
    v ∈ fixFlag ρ (Subgroup.zpowers x) 1 ↔ ρ x v = v := by
  constructor
  · intro hv
    have h := (mem_fixFlag_succ ρ (k := 0)).1 hv x (Subgroup.mem_zpowers x)
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  · intro hv
    refine (mem_fixFlag_succ ρ (k := 0)).2 fun g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hk : ρ (x ^ k) v = v := by
      have h1 : ∀ n : ℕ, ρ (x ^ n) v = v := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hv, ih]
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast, h1]
      · rw [zpow_neg, zpow_natCast]
        conv_lhs => rw [← h1 n]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hk, sub_self, fixFlag_zero]
    exact Submodule.zero_mem _

theorem finrank_fix_orderOf_five [Finite F] (hF : Nat.card F = 2) {x : ↥SLF}
    (hx : orderOf x = 5) : finrank F ↥(fixFlag ρ (Subgroup.zpowers x) 1) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hG : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  have h := card_modEq_card_inf_fix ρ _ hG ⊤ (fun _ _ _ _ => Submodule.mem_top)
  rw [top_inf_eq, card_eq_two_pow hF, card_eq_two_pow hF, finrank_top, finrank_v5] at h
  have hk := finrank_le_five (fixFlag ρ (Subgroup.zpowers x) 1)
  have hne : finrank F ↥(fixFlag ρ (Subgroup.zpowers x) 1) ≠ 5 := by
    intro h5
    have htop := Submodule.eq_top_of_finrank_eq (h5.trans finrank_v5.symm)
    have hx1 : x = 1 := by
      apply natRep_injective (StatedSL 5 F)
      rw [map_one]
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ fixFlag ρ (Subgroup.zpowers x) 1 := htop ▸ Submodule.mem_top
      rw [mem_fix_zpowers_iff] at hv
      rw [hv, Module.End.one_apply]
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  unfold Nat.ModEq at h
  interval_cases hd : finrank F ↥(fixFlag ρ (Subgroup.zpowers x) 1) <;> simp_all

theorem stable_cases [Finite F] (hF : Nat.card F = 2) {x : ↥SLF} (hx : orderOf x = 5)
    {W : Submodule F (Fin 5 → F)} (hW : ∀ v ∈ W, ρ x v ∈ W) :
    (W ⊓ fixFlag ρ (Subgroup.zpowers x) 1 = ⊥ ∧ (finrank F W = 0 ∨ finrank F W = 4)) ∨
      (fixFlag ρ (Subgroup.zpowers x) 1 ≤ W ∧ (finrank F W = 1 ∨ finrank F W = 5)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hG : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  have hC1 := finrank_fix_orderOf_five hF hx
  have h := card_modEq_card_inf_fix ρ _ hG W (zpowers_stable hx hW)
  rw [card_eq_two_pow hF, card_eq_two_pow hF] at h
  have hle : finrank F ↥(W ⊓ fixFlag ρ (Subgroup.zpowers x) 1) ≤ 1 :=
    (Submodule.finrank_mono inf_le_right).trans hC1.le
  rcases pow_mod_five_cases (finrank_le_five W) hle h with ⟨hj, hk⟩ | ⟨hj, hk⟩
  · exact Or.inl ⟨Submodule.finrank_eq_zero.1 hj, hk⟩
  · refine Or.inr ⟨?_, hk⟩
    have heq : W ⊓ fixFlag ρ (Subgroup.zpowers x) 1 = fixFlag ρ (Subgroup.zpowers x) 1 :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hC1, hj])
    rw [← heq]
    exact inf_le_left

theorem eq_of_finrank_eq_one [Finite F] (hF : Nat.card F = 2) {C : Submodule F (Fin 5 → F)}
    (hC : finrank F ↥C = 1) {v w : Fin 5 → F} (hv : v ∈ C) (hw : w ∈ C) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) : v = w := by
  classical
  by_contra hvw
  have hcard : Nat.card ↥C = 2 := by rw [card_eq_two_pow hF, hC, pow_one]
  have := Fintype.ofFinite ↥C
  have h3 : (({⟨0, C.zero_mem⟩, ⟨v, hv⟩, ⟨w, hw⟩} : Finset ↥C)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hvw (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hv0 (congrArg Subtype.val h).symm,
        fun h => hw0 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_univ ({⟨0, C.zero_mem⟩, ⟨v, hv⟩, ⟨w, hw⟩} : Finset ↥C)
  rw [h3, ← Nat.card_eq_fintype_card, hcard] at this
  omega

theorem eq_one_of_commute_orderOf_five [Finite F] (hF : Nat.card F = 2) {x t : ↥SLF}
    (hx : orderOf x = 5) (ht : t ^ 2 = 1) (hc : x * t = t * x) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← hF, Nat.card_eq_fintype_card])
  set f : Module.End F (Fin 5 → F) := ρ t - 1 with hf
  have hxt : ∀ v, ρ x (ρ t v) = ρ t (ρ x v) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
  have hDx : ∀ v ∈ LinearMap.ker f, ρ x v ∈ LinearMap.ker f := by
    intro v hv
    rw [LinearMap.mem_ker, hf, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    rw [← hxt, hv]
  have hC1 := finrank_fix_orderOf_five hF hx
  have hCD : fixFlag ρ (Subgroup.zpowers x) 1 ≤ LinearMap.ker f := by
    intro v hv
    rw [LinearMap.mem_ker, hf, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    have htv : ρ t v ∈ fixFlag ρ (Subgroup.zpowers x) 1 := by
      rw [mem_fix_zpowers_iff] at hv ⊢
      rw [hxt, hv]
    have htv0 : ρ t v ≠ 0 := by
      intro h0
      apply hv0
      have := congrArg (ρ t) h0
      rwa [map_zero, ← Module.End.mul_apply, ← map_mul, ← sq, ht, map_one,
        Module.End.one_apply] at this
    exact eq_of_finrank_eq_one hF hC1 htv hv htv0 hv0
  have h2 : ∀ w : Fin 5 → F, w + w = 0 := fun w => by
    ext i
    exact CharTwo.add_self_eq_zero _
  have hff : ∀ v, f (f v) = 0 := by
    intro v
    simp only [hf, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← Module.End.mul_apply (ρ t) (ρ t), ← map_mul, ← sq, ht, map_one, Module.End.one_apply]
    calc v - ρ t v - (ρ t v - v) = (v + v) - (ρ t v + ρ t v) := by abel
      _ = 0 := by rw [h2, h2, sub_self]
  have hrk : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact hff v
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [finrank_v5] at hrn
  have hmono := Submodule.finrank_mono hrk
  rcases stable_cases hF hx hDx with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [inf_eq_right.2 hCD] at h1
    rw [h1, finrank_bot] at hC1
    exact absurd hC1 (by norm_num)
  · have h5 : finrank F ↥(LinearMap.ker f) = 5 := by omega
    have htop := Submodule.eq_top_of_finrank_eq (h5.trans finrank_v5.symm)
    apply natRep_injective (StatedSL 5 F)
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hf, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [hv, Module.End.one_apply]

theorem finrank_fix_cases [Finite F] (hF : Nat.card F = 2) {x : ↥SLF} (hx : orderOf x = 5)
    {U : Subgroup ↥SLF} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U)
    (hxU : x ∈ Subgroup.normalizer (U : Set ↥SLF)) :
    finrank F ↥(fixFlag ρ U 1) = 1 ∨ finrank F ↥(fixFlag ρ U 1) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← hF, Nat.card_eq_fintype_card])
  have hst : ∀ v ∈ fixFlag ρ U 1, ρ x v ∈ fixFlag ρ U 1 := fun v hv =>
    ((normalizer_le_flagStab_fixFlag ρ U) hxU 1 v hv).1
  have hne : fixFlag ρ U 1 ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ 2 U hU2
    intro hbot
    have hvU : v ∈ fixFlag ρ U 1 := by
      refine (mem_fixFlag_succ ρ (k := 0)).2 fun g hg => ?_
      rw [hv g hg, sub_self, fixFlag_zero]
      exact Submodule.zero_mem _
    rw [hbot, Submodule.mem_bot] at hvU
    exact hv0 hvU
  have htop : fixFlag ρ U 1 ≠ ⊤ := by
    intro htop
    apply hU
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    apply natRep_injective (StatedSL 5 F)
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ fixFlag ρ U 1 := htop ▸ Submodule.mem_top
    have h := (mem_fixFlag_succ ρ (k := 0)).1 hv u hu
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h
    rw [h, Module.End.one_apply]
  have h0 : finrank F ↥(fixFlag ρ U 1) ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.1 h)
  have h5 : finrank F ↥(fixFlag ρ U 1) ≠ 5 := fun h =>
    htop (Submodule.eq_top_of_finrank_eq (h.trans finrank_v5.symm))
  rcases stable_cases hF hx hst with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> omega

theorem det_eq_one_of_mem {g : GL (Fin 5) F} (hg : g ∈ StatedSL 5 F) :
    (g : Matrix (Fin 5) (Fin 5) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

@[expose] def invTr (g : GL (Fin 5) F) : GL (Fin 5) F :=
  ⟨((g⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ, (g : Matrix (Fin 5) (Fin 5) F)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem coe_invTr (g : GL (Fin 5) F) :
    ((invTr g : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      ((g⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ := rfl

theorem invTr_mem {g : GL (Fin 5) F} (hg : g ∈ StatedSL 5 F) : invTr g ∈ StatedSL 5 F := by
  refine Subgroup.subset_closure ?_
  show (((g⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ).det = 1
  rw [Matrix.det_transpose, Matrix.coe_units_inv, Matrix.det_nonsing_inv, det_eq_one_of_mem hg,
    Ring.inverse_one]

theorem invTr_invTr (g : GL (Fin 5) F) : invTr (invTr g) = g := by
  ext i j
  simp [invTr]

theorem invTr_mul (g h : GL (Fin 5) F) : invTr (g * h) = invTr g * invTr h := by
  ext : 1
  simp only [coe_invTr, mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

@[expose] def theta : MulAut ↥SLF where
  toFun g := ⟨invTr g, invTr_mem g.2⟩
  invFun g := ⟨invTr g, invTr_mem g.2⟩
  left_inv _ := Subtype.ext (invTr_invTr _)
  right_inv _ := Subtype.ext (invTr_invTr _)
  map_mul' _ _ := Subtype.ext (invTr_mul _ _)

theorem rep_theta_apply (g : ↥SLF) (v : Fin 5 → F) :
    ρ (theta g) v = (((g⁻¹ : ↥SLF) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ v := by
  rw [natRep_apply]
  rfl

@[expose] def dotForm : ReflForm F (Fin 5 → F) where
  σ := RingEquiv.refl F
  β u v := u ⬝ᵥ v
  add_left u u' v := add_dotProduct u u' v
  smul_left c u v := by simp [smul_dotProduct]
  add_right u v v' := dotProduct_add u v v'
  smul_right c u v := by simp [dotProduct_smul]
  refl u v h := by rwa [dotProduct_comm]
  nondeg u h := by
    ext i
    have h1 := h (Pi.single i 1)
    simpa using h1

@[expose] def commSp (U : Subgroup ↥SLF) : Submodule F (Fin 5 → F) :=
  Submodule.span F {w | ∃ u ∈ U, ∃ v, w = ρ u v - v}

theorem dot_rep (g : ↥SLF) (v w : Fin 5 → F) :
    ρ g v ⬝ᵥ w = v ⬝ᵥ ((((g : ↥SLF) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ w) := by
  rw [natRep_apply, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm,
    ← Matrix.mulVec_transpose]

theorem fix_theta_eq_perp (U : Subgroup ↥SLF) :
    fixFlag ρ (U.map theta.toMonoidHom) 1 = dotForm.perp (commSp U) := by
  ext v
  constructor
  · intro hv w hw
    show w ⬝ᵥ v = 0
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu, y, rfl⟩ := hw
      have h := (mem_fixFlag_succ ρ (k := 0)).1 hv (theta u⁻¹) ⟨u⁻¹, U.inv_mem hu, rfl⟩
      rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero, rep_theta_apply, inv_inv] at h
      rw [sub_dotProduct, dot_rep, h, sub_self]
    | zero => exact zero_dotProduct v
    | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]
  · intro hv
    refine (mem_fixFlag_succ ρ (k := 0)).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero]
    show ρ (theta u) v = v
    rw [rep_theta_apply]
    ext i
    have h := hv (ρ u⁻¹ (Pi.single i 1) - Pi.single i 1)
      (Submodule.subset_span ⟨u⁻¹, U.inv_mem hu, Pi.single i 1, rfl⟩)
    change (ρ u⁻¹ (Pi.single i 1) - Pi.single i 1) ⬝ᵥ v = 0 at h
    rw [sub_dotProduct, dot_rep, sub_eq_zero] at h
    simpa using h

theorem finrank_fix_theta (U : Subgroup ↥SLF) :
    finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1) + finrank F ↥(commSp U) = 5 := by
  rw [fix_theta_eq_perp, dotForm.finrank_perp, finrank_v5]

theorem commSp_stable {U : Subgroup ↥SLF} {g : ↥SLF} (hg : g ∈ Subgroup.normalizer (U : Set ↥SLF)) :
    ∀ w ∈ commSp U, ρ g w ∈ commSp U := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, hu, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg u).mp hu,
      ρ g v, ?_⟩
    have hgg : ∀ y, ρ g⁻¹ (ρ g y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h : ρ (g * u * g⁻¹) (ρ g v) = ρ g (ρ u v) := by
      simp only [map_mul, Module.End.mul_apply, hgg]
    rw [map_sub, h]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem card_le_two_of_finrank_four [Finite F] (hF : Nat.card F = 2) {U : Subgroup ↥SLF}
    (h1 : finrank F ↥(fixFlag ρ U 1) = 4)
    (h2 : finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1) = 4) : Nat.card ↥U ≤ 2 := by
  classical
  have hc := finrank_fix_theta U
  rw [h2] at hc
  have hc1 : finrank F ↥(commSp U) = 1 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ fixFlag ρ U 1 := by
    by_contra h
    push Not at h
    have htop : fixFlag ρ U 1 = ⊤ := eq_top_iff.2 fun v _ => h v
    have := congrArg (fun W : Submodule F (Fin 5 → F) => finrank F ↥W) htop
    simp only [h1, finrank_top, finrank_v5] at this
    omega
  have hsup : fixFlag ρ U 1 ⊔ F ∙ v₀ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hlt : fixFlag ρ U 1 < fixFlag ρ U 1 ⊔ F ∙ v₀ := lt_of_le_of_ne le_sup_left fun h =>
      hv₀ (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    have h4 := finrank_le_five (fixFlag ρ U 1 ⊔ F ∙ v₀)
    rw [finrank_v5]
    omega
  have hfixU : ∀ u ∈ U, ∀ w ∈ fixFlag ρ U 1, ρ u w = w := by
    intro u hu w hw
    have h := (mem_fixFlag_succ ρ (k := 0)).1 hw u hu
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  let f : ↥U → ↥(commSp U) := fun u =>
    ⟨ρ u v₀ - v₀, Submodule.subset_span ⟨u, u.2, v₀, rfl⟩⟩
  have hf : Function.Injective f := by
    intro u u' huu'
    have h0 : ρ u v₀ = ρ u' v₀ := by
      have := congrArg Subtype.val huu'
      simpa [f] using this
    apply Subtype.ext
    apply natRep_injective (StatedSL 5 F)
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ fixFlag ρ U 1 ⊔ F ∙ v₀ := hsup ▸ Submodule.mem_top
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_add, map_add, map_smul, map_smul, hfixU u u.2 w hw, hfixU u' u'.2 w hw, h0]
  have hcard := Nat.card_le_card_of_injective f hf
  rwa [card_eq_two_pow hF, hc1, pow_one] at hcard

theorem false_of_finrank_one [Finite F] (hF : Nat.card F = 2) {x : ↥SLF} (hx : orderOf x = 5)
    {U : Subgroup ↥SLF} (hU2 : IsPGroup 2 ↥U) (hxU : x ∈ Subgroup.normalizer (U : Set ↥SLF))
    (h1 : finrank F ↥(fixFlag ρ U 1) = 1)
    (h2 : finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1) = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← hF, Nat.card_eq_fintype_card])
  have hc := finrank_fix_theta U
  rw [h2] at hc
  have hc4 : finrank F ↥(commSp U) = 4 := by omega
  have hCx : ∀ v ∈ commSp U, ρ x v ∈ commSp U := commSp_stable hxU
  have hdisj : commSp U ⊓ fixFlag ρ (Subgroup.zpowers x) 1 = ⊥ := by
    rcases stable_cases hF hx hCx with ⟨h, -⟩ | ⟨-, h | h⟩
    · exact h
    · omega
    · omega
  have hUx : ∀ v ∈ fixFlag ρ U 1, ρ x v ∈ fixFlag ρ U 1 := fun v hv =>
    ((normalizer_le_flagStab_fixFlag ρ U) hxU 1 v hv).1
  have hxle : fixFlag ρ (Subgroup.zpowers x) 1 ≤ fixFlag ρ U 1 := by
    rcases stable_cases hF hx hUx with ⟨-, h | h⟩ | ⟨h, -⟩
    · omega
    · omega
    · exact h
  have hbot : (⊥ : Submodule F (Fin 5 → F)) < commSp U := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [h, finrank_bot] at hc4
    omega
  obtain ⟨w, hw, hw0, hwfix⟩ := exists_mem_notMem_forall_sub_mem ρ 2 U hU2 hbot
    (fun g _ v hv => by rw [(Submodule.mem_bot F).1 hv, map_zero]; exact Submodule.zero_mem _)
    (fun g hg => commSp_stable (Subgroup.le_normalizer hg))
  have hwU : w ∈ fixFlag ρ U 1 := (mem_fixFlag_succ ρ (k := 0)).2 fun g hg => hwfix g hg
  have hwx : w ∈ fixFlag ρ (Subgroup.zpowers x) 1 := by
    have heq : fixFlag ρ (Subgroup.zpowers x) 1 = fixFlag ρ U 1 :=
      Submodule.eq_of_le_of_finrank_le hxle (by rw [h1, finrank_fix_orderOf_five hF hx])
    rw [heq]
    exact hwU
  have : w ∈ commSp U ⊓ fixFlag ρ (Subgroup.zpowers x) 1 := ⟨hw, hwx⟩
  rw [hdisj] at this
  exact hw0 this

theorem orderOf_theta {g : ↥SLF} (hg : orderOf g = 5) : orderOf (theta g) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : g ^ 5 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, h5, map_one]
  · intro h
    have h1 : g = 1 := theta.injective (h.trans (map_one theta).symm)
    rw [h1, orderOf_one] at hg
    norm_num at hg

theorem finrank_fix_cases_theta [Finite F] (hF : Nat.card F = 2) {x : ↥SLF} (hx : orderOf x = 5)
    {U : Subgroup ↥SLF} (hU2 : IsPGroup 2 ↥U) (hxU : x ∈ Subgroup.normalizer (U : Set ↥SLF))
    (hU4 : 4 ≤ Nat.card ↥U) :
    (finrank F ↥(fixFlag ρ U 1) = 1 ∧
        finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1) = 4) ∨
      (finrank F ↥(fixFlag ρ U 1) = 4 ∧
        finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1) = 1) := by
  have hU : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    omega
  have hθU : U.map theta.toMonoidHom ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff_of_injective _ theta.injective] at h
    exact hU h
  have hθx : theta x ∈ Subgroup.normalizer ((U.map theta.toMonoidHom : Subgroup ↥SLF) :
      Set ↥SLF) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨x, hxU, rfl⟩
  rcases finrank_fix_cases hF hx hU hU2 hxU with h1 | h1 <;>
    rcases finrank_fix_cases hF (orderOf_theta hx) hθU (hU2.map _) hθx with h2 | h2
  · exact absurd (false_of_finrank_one hF hx hU2 hxU h1 h2) id
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · have := card_le_two_of_finrank_four hF h1 h2
    omega

end SL5

end CFSG.Quasithin.H13.KG12617L52
