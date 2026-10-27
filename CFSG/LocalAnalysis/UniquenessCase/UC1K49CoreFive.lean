module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs
public import CFSG.GroupTheory.HyperplaneDecomposition
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem pow_two_modEq_five_of_le_three {d e : ℕ} (hle : e ≤ d) (hd : d ≤ 3)
    (h : 2 ^ d ≡ 2 ^ e [MOD 5]) : d = e := by
  have key : ∀ d < 4, ∀ e < 4, e ≤ d → 2 ^ d % 5 = 2 ^ e % 5 → d = e := by decide
  exact key d (by omega) e (by omega) hle h

private theorem natCard_eq_two_pow_finrank (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rwa [Nat.card_zmod] at h

private theorem card_modEq_fixedSubmodule_of_pow_five {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (T : V →ₗ[ZMod 2] V) (hT : T ^ 5 = 1) :
    Nat.card V ≡ Nat.card (LinearMap.ker (T - 1)) [MOD 5] := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let g : Function.End V := fun v => T v
  have hg : g ^ 5 ^ 1 = 1 := by
    rw [pow_one]
    funext v
    change T^[5] v = v
    rw [← Module.End.pow_apply T 5 v, hT, Module.End.one_apply]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := V) (f := g) (p := 5) (n := 1) hg
  have hFmem : ∀ v : V, v ∈ LinearMap.ker (T - 1) ↔ T v = v := by
    intro v
    simp [LinearMap.mem_ker, sub_eq_zero]
  have hfixed : Fintype.card (Function.fixedPoints g) =
      Fintype.card (LinearMap.ker (T - 1)) := by
    apply Fintype.card_congr
    exact
      { toFun := fun v => ⟨v.1, (hFmem v.1).mpr v.2⟩
        invFun := fun v => ⟨v.1, (hFmem v.1).mp v.2⟩
        left_inv := fun v => Subtype.ext rfl
        right_inv := fun v => Subtype.ext rfl }
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [hfixed] at hmod
  exact hmod

theorem four_le_finrank_of_pow_five {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V →ₗ[ZMod 2] V) (hT : T ^ 5 = 1) (hT1 : T ≠ 1) :
    4 ≤ Module.finrank (ZMod 2) V := by
  classical
  by_contra hcon
  push Not at hcon
  have hd : Module.finrank (ZMod 2) V ≤ 3 := by omega
  have hmod := card_modEq_fixedSubmodule_of_pow_five T hT
  rw [natCard_eq_two_pow_finrank V,
    natCard_eq_two_pow_finrank ↥(LinearMap.ker (T - 1))] at hmod
  have hle : Module.finrank (ZMod 2) ↥(LinearMap.ker (T - 1)) ≤
      Module.finrank (ZMod 2) V := Submodule.finrank_le _
  have heq : Module.finrank (ZMod 2) ↥(LinearMap.ker (T - 1)) =
      Module.finrank (ZMod 2) V :=
    (pow_two_modEq_five_of_le_three (d := Module.finrank (ZMod 2) V)
      (e := Module.finrank (ZMod 2) ↥(LinearMap.ker (T - 1))) hle hd hmod).symm
  have hFtop : LinearMap.ker (T - 1) = ⊤ := Submodule.eq_top_of_finrank_eq heq
  apply hT1
  ext v
  have hv : v ∈ LinearMap.ker (T - 1) := by rw [hFtop]; exact Submodule.mem_top
  simpa [LinearMap.mem_ker, sub_eq_zero] using hv

theorem isProj_subgroupAverage_invariants {B V : Type} [Group B] [Finite B] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) B V) (H : Subgroup B)
    (hH : (Nat.card H : ZMod 2) ≠ 0) :
    LinearMap.IsProj (Representation.invariants (ρ.comp H.subtype))
      (CFSG.SolvableHall.subgroupAverage ρ H) :=
  ⟨CFSG.SolvableHall.subgroupAverage_mem_invariants ρ H,
   fun _ hv => CFSG.SolvableHall.subgroupAverage_eq_self ρ (by norm_num) hH hv⟩

theorem normal_subgroupOf_of_commutator_le {N M : Subgroup G} (hMN : M ≤ N)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ M) : (M.subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hMN]
  intro m n hm hn
  rw [show n * m * n⁻¹ = ⁅n, m⁆ * m by rw [commutatorElement_def]; group]
  exact M.mul_mem (hcomm n hn m (hMN hm)) hm

theorem isElementaryAbelian_quotient49 {N M : Subgroup G} (hMN : M ≤ N)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ M) (hsq : ∀ x ∈ N, x ^ 2 ∈ M)
    [(M.subgroupOf N).Normal] :
    CFSG.IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) where
  is_comm := ⟨fun x y => by
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc : (((a * b)⁻¹ * (b * a) : N) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [hc]
    exact hcomm _ (inv_mem b.2) _ (inv_mem a.2)⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hsq _ a.2

private theorem exists_hyperplane_operator_fixing_not_of_span {B V : Type} [Group B] [Finite B]
    [Nontrivial B] [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) B V)
    (hinj : Function.Injective ρ)
    (hspan : ⨆ D : {D : Subgroup B // D ≤ ⊤ ∧ D.relIndex ⊤ = 5},
      Representation.invariants (ρ.comp D.1.subtype) = ⊤) :
    ∃ D : {D : Subgroup B // D ≤ ⊤ ∧ D.relIndex ⊤ = 5},
      ∃ b : B, ∃ v ∈ Representation.invariants (ρ.comp D.1.subtype), ρ b v ≠ v := by
  by_contra hcon
  push Not at hcon
  have hle : (⨆ D : {D : Subgroup B // D ≤ ⊤ ∧ D.relIndex ⊤ = 5},
      Representation.invariants (ρ.comp D.1.subtype)) ≤
      Representation.invariants (ρ.comp (⊤ : Subgroup B).subtype) := by
    refine iSup_le fun D => ?_
    intro w hw
    rw [CFSG.SolvableHall.mem_invariants_comp_subtype]
    intro c _
    exact hcon D c w hw
  have htop : Representation.invariants (ρ.comp (⊤ : Subgroup B).subtype) = ⊤ :=
    le_antisymm le_top (hspan ▸ hle)
  have hrho1 : ρ = 1 := by
    ext c w
    have hw : w ∈ Representation.invariants (ρ.comp (⊤ : Subgroup B).subtype) := by
      rw [htop]; exact Submodule.mem_top
    exact (CFSG.SolvableHall.mem_invariants_comp_subtype.mp hw) c (Subgroup.mem_top c)
  obtain ⟨b0, hb0⟩ := exists_ne (1 : B)
  exact hb0 (hinj (by simp [hrho1]))

private theorem exists_hyperplane_operator_fixing_not (k : ℕ)
    {B V : Type} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) B V) (hpow : ∀ b : B, b ^ 5 = 1)
    (hcomm : ∀ a b : B, a * b = b * a) (hcard : Nat.card B = 5 ^ (k + 1))
    (hinj : Function.Injective ρ) :
    ∃ D : {D : Subgroup B // D ≤ ⊤ ∧ D.relIndex ⊤ = 5},
      ∃ b : B, ∃ v ∈ Representation.invariants (ρ.comp D.1.subtype), ρ b v ≠ v := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hAtop : CFSG.Open.IsElemAbelian 5 (⊤ : Subgroup B) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm (a : B) (b : B))⟩⟩, fun x _ => hpow (x : B)⟩
  have hBnt : Nontrivial B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact lt_of_lt_of_le (by norm_num) (Nat.le_self_pow (Nat.succ_ne_zero k) 5)
  have hA1 : (⊤ : Subgroup B) ≠ ⊥ := by
    intro hbot
    have h1 : ∀ b : B, b = 1 := fun b =>
      (Subgroup.eq_bot_iff_forall (⊤ : Subgroup B)).mp hbot b (Subgroup.mem_top b)
    have hsub : Subsingleton B := ⟨fun a b => by rw [h1 a, h1 b]⟩
    have hle : Nat.card B ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    rw [hcard] at hle
    have hlt : 1 < 5 ^ (k + 1) :=
      lt_of_lt_of_le (by norm_num) (Nat.le_self_pow (Nat.succ_ne_zero k) 5)
    omega
  have hspan : ⨆ D : {D : Subgroup B // D ≤ ⊤ ∧ D.relIndex ⊤ = 5},
      Representation.invariants (ρ.comp D.1.subtype) = ⊤ :=
    CFSG.SolvableHall.iSup_invariants_hyperplanes_eq_top ρ (by norm_num) (by norm_num)
      (by norm_num) hAtop hA1
  haveI : Nontrivial B := hBnt
  exact exists_hyperplane_operator_fixing_not_of_span ρ hinj hspan

private theorem card_of_relIndex_five (k : ℕ) {B : Type} [Group B] [Finite B] {D : Subgroup B}
    (hcard : Nat.card B = 5 ^ (k + 1)) (hidx : D.relIndex ⊤ = 5) :
    Nat.card ↥D = 5 ^ k ∧ (Nat.card ↥D : ZMod 2) ≠ 0 := by
  have hDidx : D.index = 5 := by
    rw [← Subgroup.relIndex_top_right]
    exact hidx
  have hDcard : Nat.card ↥D = 5 ^ k := by
    have h := Subgroup.card_mul_index D
    rw [hDidx, hcard] at h
    have h2 : Nat.card ↥D * 5 = 5 ^ k * 5 := by
      rw [h, pow_succ]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 5) h2
  refine ⟨hDcard, ?_⟩
  have h5nz : ((5 : ℕ) : ZMod 2) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff_even] at h
    norm_num at h
  rw [hDcard, Nat.cast_pow]
  exact pow_ne_zero k h5nz

private theorem four_le_finrank_invariants {B V : Type} [Group B] [Finite B] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) B V) (D : Subgroup B) (b : B)
    (hcomm : ∀ a b : B, a * b = b * a) (hpow : ∀ b : B, b ^ 5 = 1)
    (hbv : ∃ v ∈ Representation.invariants (ρ.comp D.subtype), ρ b v ≠ v) :
    4 ≤ Module.finrank (ZMod 2) (Representation.invariants (ρ.comp D.subtype)) := by
  have hWinv : ∀ w ∈ Representation.invariants (ρ.comp D.subtype),
      ρ b w ∈ Representation.invariants (ρ.comp D.subtype) := by
    intro w hw
    rw [CFSG.SolvableHall.mem_invariants_comp_subtype] at hw ⊢
    intro d hd
    have hbw : ρ d (ρ b w) = ρ b (ρ d w) := by
      rw [← Module.End.mul_apply, ← map_mul, hcomm d b, map_mul, Module.End.mul_apply]
    rw [hbw, hw d hd]
  let T : ↥(Representation.invariants (ρ.comp D.subtype)) →ₗ[ZMod 2]
      ↥(Representation.invariants (ρ.comp D.subtype)) := (ρ b).restrict hWinv
  have hb5 : (ρ b) ^ 5 = 1 := by rw [← map_pow, hpow b, map_one]
  have hTiter : ∀ n : ℕ, ∀ w : ↥(Representation.invariants (ρ.comp D.subtype)),
      (((⇑T)^[n] w : ↥(Representation.invariants (ρ.comp D.subtype))) : V) =
        (⇑(ρ b))^[n] (w : V) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ihh =>
        intro w
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change (ρ b) ((((⇑T)^[n] w : ↥(Representation.invariants (ρ.comp D.subtype))) : V)) =
          (ρ b) (((⇑(ρ b))^[n]) ((w : ↥(Representation.invariants (ρ.comp D.subtype))) : V))
        rw [ihh w]
  refine four_le_finrank_of_pow_five T ?_ ?_
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [Module.End.pow_apply, hTiter 5 w, ← Module.End.pow_apply, hb5]
    simp
  · intro hT1
    obtain ⟨v, hv, hbv⟩ := hbv
    apply hbv
    have h1 : (T ⟨v, hv⟩ : ↥(Representation.invariants (ρ.comp D.subtype))) =
        ⟨v, hv⟩ := by rw [hT1]; rfl
    have h2 : (T ⟨v, hv⟩ : V) = ρ b v := rfl
    rw [← h2]
    exact congrArg Subtype.val h1

private theorem kernelRep_exists {B V : Type} [Group B] [Finite B] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) B V) (D : Subgroup B) :
    ∃ ρK : Representation (ZMod 2) ↥D
        ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D)),
      ∀ (c : ↥D) (u : ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D))),
        (ρK c u : V) = ρ (c : B) u := by
  have hKinv : ∀ c : ↥D, LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D) ≤
      (LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D)).comap (ρ (c : B)) := by
    intro c w hw
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    change CFSG.SolvableHall.subgroupAverage ρ D (ρ (c : B) w) = 0
    rw [CFSG.SolvableHall.subgroupAverage_rho_of_mem_normalizer ρ D
      (Subgroup.le_normalizer c.2) w]
    rw [show CFSG.SolvableHall.subgroupAverage ρ D w = 0 from LinearMap.mem_ker.mp hw,
      map_zero]
  refine ⟨{ toFun := fun c => (ρ (c : B)).restrict (hKinv c)
            map_one' := by
              ext x
              simp
            map_mul' := by
              intro a c
              ext x
              simp [map_mul, Module.End.mul_apply] }, ?_⟩
  intro c u
  rfl

private theorem injective_kernelRep {B V : Type} [Group B] [Finite B] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) B V) (D : Subgroup B)
    (hcompl : IsCompl (Representation.invariants (ρ.comp D.subtype))
      (LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D)))
    (hinj : Function.Injective ρ)
    (ρK : Representation (ZMod 2) ↥D
      ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D)))
    (hρK : ∀ (c : ↥D) (u : ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D))),
      (ρK c u : V) = ρ (c : B) u) :
    Function.Injective ρK := by
  have hkerK : ∀ c : ↥D, ρK c = 1 → c = 1 := by
    intro c hc
    have hfixK : ∀ u : ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D)),
        ρK c u = u := by intro u; rw [hc]; rfl
    have hfixW : ∀ w ∈ Representation.invariants (ρ.comp D.subtype), ρ (c : B) w = w := by
      intro w hw
      exact (CFSG.SolvableHall.mem_invariants_comp_subtype.mp hw) (c : B) c.2
    have hcomp : ρ (c : B) = 1 := by
      ext w
      have hw : w ∈ Representation.invariants (ρ.comp D.subtype) ⊔
          LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D) := by
        rw [hcompl.sup_eq_top]
        exact Submodule.mem_top
      rw [Submodule.mem_sup] at hw
      obtain ⟨a, ha, d, hd, rfl⟩ := hw
      rw [map_add, hfixW a ha]
      congr 1
      have h1 : (ρK c ⟨d, hd⟩ : V) = d := congrArg Subtype.val (hfixK ⟨d, hd⟩)
      rw [hρK c ⟨d, hd⟩] at h1
      exact h1
    apply Subtype.ext
    exact hinj (by simp [hcomp])
  intro a c hac
  have h1 : ρK a * ρK c⁻¹ = 1 := by rw [hac, ← map_mul, mul_inv_cancel, map_one]
  have h2 : ρK (a * c⁻¹) = 1 := by rw [map_mul]; exact h1
  exact mul_inv_eq_one.mp (hkerK (a * c⁻¹) h2)

private theorem five_finrank_bound_succ (k : ℕ)
    (ih : ∀ {B V : Type} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) B V), (∀ b : B, b ^ 5 = 1) →
      (∀ a b : B, a * b = b * a) → Nat.card B = 5 ^ k →
      Function.Injective ρ → 4 * k ≤ Module.finrank (ZMod 2) V)
    {B V : Type} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) B V) (hpow : ∀ b : B, b ^ 5 = 1)
    (hcomm : ∀ a b : B, a * b = b * a) (hcard : Nat.card B = 5 ^ (k + 1))
    (hinj : Function.Injective ρ) :
    4 * (k + 1) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨D, b, v, hv, hbv⟩ :=
    exists_hyperplane_operator_fixing_not k ρ hpow hcomm hcard hinj
  obtain ⟨hDcard, hoddD⟩ := card_of_relIndex_five k hcard D.2.2
  have hcomplD := (isProj_subgroupAverage_invariants ρ D.1 hoddD).isCompl
  have hWdim : 4 ≤ Module.finrank (ZMod 2)
      (Representation.invariants (ρ.comp D.1.subtype)) :=
    four_le_finrank_invariants ρ D.1 b hcomm hpow ⟨v, hv, hbv⟩
  obtain ⟨ρK, hρK⟩ := kernelRep_exists ρ D.1
  have hinjK := injective_kernelRep ρ D.1 hcomplD hinj ρK hρK
  have hpowH : ∀ x : ↥(D.1), x ^ 5 = 1 := by
    intro x
    apply Subtype.ext
    simpa using hpow (x.1 : B)
  have hcommH : ∀ a c : ↥(D.1), a * c = c * a := by
    intro a c
    apply Subtype.ext
    simpa using hcomm (a.1 : B) (c.1 : B)
  have hIH : 4 * k ≤ Module.finrank (ZMod 2)
      ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D.1)) :=
    ih (B := ↥(D.1)) (V := ↥(LinearMap.ker (CFSG.SolvableHall.subgroupAverage ρ D.1)))
      ρK hpowH hcommH hDcard hinjK
  have hVdim := Submodule.finrank_add_eq_of_isCompl hcomplD
  omega

theorem five_finrank_bound : ∀ (k : ℕ), ∀ {B V : Type} [Group B] [Finite B] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) B V),
    (∀ b : B, b ^ 5 = 1) → (∀ a b : B, a * b = b * a) →
    Nat.card B = 5 ^ k → Function.Injective ρ → 4 * k ≤ Module.finrank (ZMod 2) V := by
  intro k
  induction k with
  | zero => intro B V _ _ _ _ _ ρ hpow hcomm hcard hinj; simp
  | succ k ih =>
    intro B V _ _ _ _ _ ρ hpow hcomm hcard hinj
    exact five_finrank_bound_succ k ih ρ hpow hcomm hcard hinj

theorem fiveRankBound : FiveRankBound := by
  intro G _ _ N M B k hMN hcomm hsq hBel hBcard hBN hBM hfaith
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hMnorm : (M.subgroupOf N).Normal := normal_subgroupOf_of_commutator_le hMN hcomm
  haveI := hMnorm
  haveI hEel : CFSG.IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) :=
    isElementaryAbelian_quotient49 hMN hcomm hsq
  let rep : Representation (ZMod 2) ↥B (Additive (N ⧸ M.subgroupOf N)) :=
    (Units.coeHom (Additive (N ⧸ M.subgroupOf N) →ₗ[ZMod 2] Additive (N ⧸ M.subgroupOf N))).comp
      (chiefRep (N := B) (W₁ := N) (W₂ := M) (p := 2) hBN hBM)
  have hrepinj : Function.Injective rep := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hb2 : chiefRep (N := B) (W₁ := N) (W₂ := M) (p := 2) hBN hBM b = 1 :=
      Units.val_injective (by simpa [rep] using hb)
    rw [chiefRep_eq_one_iff] at hb2
    exact Subtype.ext (hfaith (b : G) b.2 hb2)
  have hpowB : ∀ b : ↥B, b ^ 5 = 1 := fun b => by
    apply Subtype.ext
    exact hBel.2 (b : G) b.2
  have hcommB : ∀ a b : ↥B, a * b = b * a := fun a b => hBel.1.is_comm.comm a b
  have hbound := five_finrank_bound k rep hpowB hcommB hBcard hrepinj
  haveI : Module.Finite (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) := Module.Finite.of_finite
  have hVfin : Nat.card (Additive (N ⧸ M.subgroupOf N)) =
      2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (N ⧸ M.subgroupOf N))
    rwa [Nat.card_zmod] at this
  have hcardV : Nat.card (Additive (N ⧸ M.subgroupOf N)) = M.relIndex N := rfl
  calc 2 ^ (4 * k) ≤ 2 ^ Module.finrank (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
        Nat.pow_le_pow_right (by norm_num) hbound
    _ = Nat.card (Additive (N ⧸ M.subgroupOf N)) := hVfin.symm
    _ = M.relIndex N := hcardV

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
