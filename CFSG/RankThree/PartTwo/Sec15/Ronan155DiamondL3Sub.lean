module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LieType.CentralExt.CoprimeLift
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K : Type*} [Field K]

@[expose] def LiftInv (H : Subgroup (projectiveSL 3 K)) (W : Submodule K (Fin 3 → K)) : Prop :=
  ∀ g : SpecialLinearGroup (Fin 3) K, proj 3 K g ∈ H → ∀ w ∈ W,
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W

@[expose] def uRad (W : Submodule K (Fin 3 → K)) : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | (∀ v, ((g : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ v ∈ W) ∧
    ∀ w ∈ W, ((g : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ w = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    have key : ∀ v, (((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ v =
        ((g : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ v) +
          ((h : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ v := by
      intro v
      rw [SpecialLinearGroup.coe_mul, sub_mulVec, sub_mulVec, sub_mulVec]
      simp only [one_mulVec]
      rw [← mulVec_mulVec]
      abel
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [key]
      exact W.add_mem (hg1 _) (hh1 v)
    · rw [key]
      have hhw : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
        have := hh2 w hw
        rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
      rw [hhw, hg2 w hw, hh2 w hw, add_zero]
  one_mem' := by
    refine ⟨fun v => ?_, fun w _ => ?_⟩ <;>
      simp only [SpecialLinearGroup.coe_one, sub_self, zero_mulVec, W.zero_mem]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ∀ x, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
      intro x
      rw [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one,
        one_mulVec]
    have hfix : ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
      intro w hw
      have := hg2 w hw
      rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
    have hfix' : ∀ w ∈ W, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
        w := by
      intro w hw
      conv_lhs => rw [← hfix w hw]
      exact hinv w
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · set u := ((g : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ v with hu
      have hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v + u := by
        rw [hu, sub_mulVec, one_mulVec]
        abel
      have h1 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v - u := by
        have h2 := hinv v
        rw [hgv, mulVec_add, hfix' u (hg1 v)] at h2
        exact eq_sub_of_add_eq h2
      rw [sub_mulVec, one_mulVec, h1, sub_sub_cancel_left]
      exact W.neg_mem (hg1 v)
    · rw [sub_mulVec, one_mulVec, hfix' w hw, sub_self]

theorem sq_eq_one_of_mem_uRad [CharP K 2] {W : Submodule K (Fin 3 → K)}
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ uRad W) : g ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ((g : Matrix (Fin 3) (Fin 3) K) - 1) ^ 2 = (g : Matrix (Fin 3) (Fin 3) K) ^ 2 - 1 := by
    have h := sub_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) K) 2 1
      (Commute.one_right (g : Matrix (Fin 3) (Fin 3) K))
    simpa using h
  have hzero : ((g : Matrix (Fin 3) (Fin 3) K) - 1) ^ 2 = 0 := by
    ext i j
    have h := hg.2 _ (hg.1 (Pi.single j 1))
    rw [mulVec_mulVec, mulVec_single_one, ← sq] at h
    simpa using congrFun h i
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one]
  rw [hzero] at hsq
  exact (sub_eq_zero.mp hsq.symm)

theorem isPGroup_uRad [CharP K 2] (W : Submodule K (Fin 3 → K)) : IsPGroup 2 (uRad W) :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (sq_eq_one_of_mem_uRad g.2)⟩

theorem conj_mem_uRad {W : Submodule K (Fin 3 → K)} {g h : SpecialLinearGroup (Fin 3) K}
    (hgW : ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W)
    (hgW' : ∀ w ∈ W, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W)
    (hh : h ∈ uRad W) : g * h * g⁻¹ ∈ uRad W := by
  have key : ∀ v, (((g * h * g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ
      v = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (((h : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) := by
    intro v
    have hgg : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
      rw [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one,
        one_mulVec]
    rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, mulVec_sub, hgg, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [key]
    exact hgW _ (hh.1 _)
  · rw [key, hh.2 _ (hgW' w hw), mulVec_zero]

theorem sq_eq_zero_of_isNilpotent {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {φ : Module.End K V} (h : IsNilpotent φ) (hd : Module.finrank K V ≤ 2) : φ ^ 2 = 0 := by
  have hc := h.charpoly_eq_X_pow_finrank
  have hCH := LinearMap.aeval_self_charpoly φ
  rw [hc, map_pow, Polynomial.aeval_X] at hCH
  rw [← Nat.sub_add_cancel hd, pow_add, hCH, mul_zero]

theorem pow_two_mem_uRad [CharP K 2] {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    {g : SpecialLinearGroup (Fin 3) K} {a : ℕ} (hg : g ^ 2 ^ a = 1)
    (hgW : ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) : g ^ 2 ∈ uRad W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) - 1 with hN
  have hNa : N ^ 2 ^ a = 0 := by
    rw [hN, sub_pow_char_pow_of_commute 2 a (Commute.one_right _), one_pow,
      ← SpecialLinearGroup.coe_pow, hg, SpecialLinearGroup.coe_one, sub_self]
  have hN2 : ((g ^ 2 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1 = N * N := by
    have h := sub_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) K) 2 1
      (Commute.one_right (g : Matrix (Fin 3) (Fin 3) K))
    rw [pow_one, one_pow] at h
    rw [SpecialLinearGroup.coe_pow, ← h, sq]
  set f : Module.End K (Fin 3 → K) := Matrix.toLin' N with hf
  have hfv : ∀ v, f v = N *ᵥ v := fun v => Matrix.toLin'_apply N v
  have hfW : ∀ w ∈ W, f w ∈ W := by
    intro w hw
    rw [hfv, hN, sub_mulVec, one_mulVec]
    exact W.sub_mem (hgW w hw) hw
  have hfpow : ∀ (k : ℕ) (v : Fin 3 → K), (f ^ k) v = N ^ k *ᵥ v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, hfv, mulVec_mulVec, ← pow_succ]
  have hWle : Module.finrank K W ≤ 2 := by
    have := Submodule.finrank_lt hW1
    rw [Module.finrank_fin_fun] at this
    omega
  set fW : Module.End K W := f.restrict hfW with hfWdef
  have hfWpow : ∀ (k : ℕ) (w : W), (((fW ^ k) w : W) : Fin 3 → K) = (f ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, hfWdef,
        LinearMap.restrict_coe_apply]
  have hfWnil : IsNilpotent fW := by
    refine ⟨2 ^ a, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [hfWpow, hfpow, hNa, zero_mulVec]
    rfl
  have hfW2 := sq_eq_zero_of_isNilpotent hfWnil hWle
  have hfQle : W ≤ W.comap f := fun w hw => hfW w hw
  set fQ : Module.End K ((Fin 3 → K) ⧸ W) := W.mapQ W f hfQle with hfQdef
  have hQle : Module.finrank K ((Fin 3 → K) ⧸ W) ≤ 2 := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fin_fun] at h1
    have h2 : 0 < Module.finrank K W :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hW0)
    omega
  have hfQpow : ∀ (k : ℕ) (v : Fin 3 → K),
      (fQ ^ k) (Submodule.Quotient.mk v) = Submodule.Quotient.mk ((f ^ k) v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hfQdef, Submodule.mapQ_apply, ← hfQdef, ih, pow_succ,
        Module.End.mul_apply]
  have hfQnil : IsNilpotent fQ := by
    refine ⟨2 ^ a, LinearMap.ext fun x => ?_⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
    rw [hfQpow, hfpow, hNa, zero_mulVec]
    rfl
  have hfQ2 := sq_eq_zero_of_isNilpotent hfQnil hQle
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [hN2, ← mulVec_mulVec, ← hfv, ← hfv]
    have h := congrArg (fun φ : Module.End K ((Fin 3 → K) ⧸ W) => φ (Submodule.Quotient.mk v)) hfQ2
    simp only [sq, Module.End.mul_apply, hfQdef, Submodule.mapQ_apply, LinearMap.zero_apply] at h
    exact (Submodule.Quotient.mk_eq_zero W).mp h
  · rw [hN2, ← mulVec_mulVec, ← hfv, ← hfv]
    have h := congrArg (fun φ : Module.End K W => ((φ ⟨w, hw⟩ : W) : Fin 3 → K)) hfW2
    simpa only [sq, Module.End.mul_apply, hfWdef, LinearMap.restrict_coe_apply,
      LinearMap.zero_apply, Submodule.coe_zero] using h

theorem not_two_dvd_card_ker_proj [Finite K] : ¬ 2 ∣ Nat.card (proj 3 K).ker := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxs : (x : SpecialLinearGroup (Fin 3) K) ∈ scalars 3 K :=
    proj_eq_one_iff.mp (MonoidHom.mem_ker.mp x.2)
  obtain ⟨c, hc, hxc⟩ := mem_scalars.mp hxs
  have hx3' : (x : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_pow, hxc, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one,
      map_one, SpecialLinearGroup.coe_one]
  have hx3 : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hx3']; rfl)
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rw [hx] at h3
  norm_num at h3

theorem exists_lift_isPElement [Finite K] {x : projectiveSL 3 K} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    ∃ g : SpecialLinearGroup (Fin 3) K, proj 3 K g = x ∧ ∃ n : ℕ, g ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∃ n : ℕ, orderOf x = 2 ^ n :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx) |>.imp fun _ h => h.2
  obtain ⟨hpg, n, hn⟩ := CFSG.LieType.CentralExt.pLift_spec (proj_surjective 3 K)
    not_two_dvd_card_ker_proj hord
  exact ⟨_, hpg, n, hn ▸ pow_orderOf_eq_one _⟩

@[expose] def fixedSub (S : Subgroup (SpecialLinearGroup (Fin 3) K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
  add_mem' := by
    intro u v hu hv s hs
    rw [mulVec_add, hu s hs, hv s hs]
  zero_mem' := by
    intro s _
    rw [mulVec_zero]
  smul_mem' := by
    intro c v hv s hs
    rw [mulVec_smul, hv s hs]

theorem fixedSub_ne_bot [Finite K] [CharP K 2] {S : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hS : IsPGroup 2 S) : fixedSub S ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction S (Fin 3 → K) :=
    MulAction.compHom (Fin 3 → K) (SpecialLinearGroup.toLin'.comp S.subtype)
  have hsmul : ∀ (s : S) (v : Fin 3 → K), s • v = (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
    intro s v
    change SpecialLinearGroup.toLin' (s : SpecialLinearGroup (Fin 3) K) v = _
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  have hmod := hS.card_modEq_card_fixedPoints (Fin 3 → K)
  have hK2 : 2 ∣ Nat.card K := by
    haveI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mod_eq_zero (FiniteField.even_card_of_char_two (ringChar.eq K 2))
  have hV : 2 ∣ Nat.card (Fin 3 → K) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    exact dvd_pow hK2 (by norm_num)
  have hF : 2 ∣ Nat.card (MulAction.fixedPoints S (Fin 3 → K)) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hV)))
  have h0 : (0 : Fin 3 → K) ∈ MulAction.fixedPoints S (Fin 3 → K) := fun s =>
    (hsmul s 0).trans (mulVec_zero _)
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ MulAction.fixedPoints S (Fin 3 → K), v ≠ 0 := by
    by_contra hne
    push Not at hne
    have hsub : Subsingleton (MulAction.fixedPoints S (Fin 3 → K)) :=
      ⟨fun a b => Subtype.ext ((hne a a.2).trans (hne b b.2).symm)⟩
    haveI : Nonempty (MulAction.fixedPoints S (Fin 3 → K)) := ⟨⟨0, h0⟩⟩
    have h1 : Nat.card (MulAction.fixedPoints S (Fin 3 → K)) = 1 := Nat.card_unique
    rw [h1] at hF
    norm_num at hF
  rw [Submodule.ne_bot_iff]
  refine ⟨v, fun s hs => ?_, hv0⟩
  exact (hsmul ⟨s, hs⟩ v).symm.trans (hv ⟨s, hs⟩)

theorem eq_one_of_forall_mulVec_eq {M : Matrix (Fin 3) (Fin 3) K} (h : ∀ v, M *ᵥ v = v) :
    M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one, Matrix.col_apply] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

theorem exists_liftInv_of_isPGroup [Finite K] [CharP K 2] {H U : Subgroup (projectiveSL 3 K)}
    (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hHU : H ≤ Subgroup.normalizer (U : Set (projectiveSL 3 K))) :
    ∃ W : Submodule K (Fin 3 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftInv H W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : (proj 3 K).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj, scalars_eq_center]
  set S := CFSG.LieType.CentralExt.liftSubgroup 2 (proj 3 K) U with hSdef
  have hS2 : IsPGroup 2 S := CFSG.LieType.CentralExt.liftSubgroup_isPGroup hcen hU2
  have hmem : ∀ e : SpecialLinearGroup (Fin 3) K,
      e ∈ S ↔ proj 3 K e ∈ U ∧ ∃ n : ℕ, orderOf e = 2 ^ n := fun e =>
    CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hU2
  refine ⟨fixedSub S, fixedSub_ne_bot hS2, ?_, ?_⟩
  · obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have hord : ∃ n : ℕ, orderOf (u : projectiveSL 3 K) = 2 ^ n :=
      CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_mem hU2 u
    obtain ⟨hpu, -⟩ := CFSG.LieType.CentralExt.pLift_spec (proj_surjective 3 K)
      not_two_dvd_card_ker_proj hord
    have hmemS := CFSG.LieType.CentralExt.pLift_mem_liftSubgroup (proj_surjective 3 K) hcen
      not_two_dvd_card_ker_proj hU2 u.2
    intro htop
    apply hu1
    apply Subtype.ext
    rw [← hpu]
    have hfix : ∀ v, ((CFSG.LieType.CentralExt.pLift 2 (proj 3 K) (u : projectiveSL 3 K) :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := fun v =>
      (htop ▸ Submodule.mem_top : v ∈ fixedSub S) _ hmemS
    have h1 : CFSG.LieType.CentralExt.pLift 2 (proj 3 K) (u : projectiveSL 3 K) = 1 :=
      Subtype.ext (eq_one_of_forall_mulVec_eq hfix)
    rw [h1, map_one]
    rfl
  · intro g hg w hw s hs
    have hconj : g⁻¹ * s * g ∈ S := by
      rw [hmem]
      obtain ⟨hsU, n, hn⟩ := (hmem s).mp hs
      refine ⟨?_, n, ?_⟩
      · have hgN : (proj 3 K g)⁻¹ ∈ Subgroup.normalizer (U : Set (projectiveSL 3 K)) :=
          inv_mem (hHU hg)
        have := (Subgroup.mem_normalizer_iff.mp hgN (proj 3 K s)).mp hsU
        rwa [inv_inv, ← map_inv, ← map_mul, ← map_mul] at this
      · have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulEquiv.injective _) s
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
        rw [h, hn]
    have h1 := hw _ hconj
    have h2 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((g⁻¹ * s * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        (s : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_mul,
        ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [← h2, h1]

@[expose] def HasOrderFourMod {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ N : Subgroup G, N ≤ H ∧
    (∀ D : Subgroup G, D ≤ H → H ≤ Subgroup.normalizer (D : Set G) → IsPGroup 2 D → D ≤ N) ∧
    ∃ y ∈ H, (∃ k : ℕ, y ^ 2 ^ k = 1) ∧ y ^ 2 ∉ N

theorem false_of_liftInv [Finite K] [CharP K 2] {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hW : LiftInv H W) : False := by
  obtain ⟨N, -, hDN, y, hyH, ⟨k, hyk⟩, hy2⟩ := hH
  set D := (uRad W).map (proj 3 K) ⊓ H with hD
  have hD2 : IsPGroup 2 D := ((isPGroup_uRad W).map (proj 3 K)).to_le inf_le_left
  have hconjD : ∀ x ∈ H, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    obtain ⟨⟨h, hh, rfl⟩, hdH⟩ := hd
    obtain ⟨g, rfl⟩ := proj_surjective 3 K x
    have hx' : proj 3 K g⁻¹ ∈ H := by
      rw [map_inv]
      exact H.inv_mem hx
    refine ⟨⟨g * h * g⁻¹, conj_mem_uRad (hW g hx) (hW g⁻¹ hx') hh,
      by rw [map_mul, map_mul, map_inv]⟩, H.mul_mem (H.mul_mem hx hdH) (H.inv_mem hx)⟩
  have hHD : H ≤ Subgroup.normalizer (D : Set (projectiveSL 3 K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨hconjD x hx d, fun h => ?_⟩
    have := hconjD x⁻¹ (H.inv_mem hx) _ h
    have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
    rwa [e] at this
  have hDle := hDN D inf_le_right hHD hD2
  obtain ⟨g, rfl, n, hgn⟩ := exists_lift_isPElement hyk
  have hg2 := pow_two_mem_uRad hW0 hW1 hgn (hW g hyH)
  exact hy2 (hDle ⟨⟨g ^ 2, hg2, map_pow _ _ _⟩, pow_mem hyH 2⟩)

theorem eq_bot_of_isPGroup_of_le_normalizer [Finite K] [CharP K 2]
    {H : Subgroup (projectiveSL 3 K)} (hH : HasOrderFourMod H) {U : Subgroup (projectiveSL 3 K)}
    (hU2 : IsPGroup 2 U) (hHU : H ≤ Subgroup.normalizer (U : Set (projectiveSL 3 K))) : U = ⊥ := by
  by_contra hU1
  obtain ⟨W, hW0, hW1, hW⟩ := exists_liftInv_of_isPGroup hU2 hU1 hHU
  exact false_of_liftInv hH hW0 hW1 hW

theorem liftInv_eq_bot_or_eq_top [Finite K] [CharP K 2] {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) {W : Submodule K (Fin 3 → K)} (hW : LiftInv H W) :
    W = ⊥ ∨ W = ⊤ := by
  by_contra h
  push Not at h
  exact false_of_liftInv hH h.1 h.2 hW

end CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3
