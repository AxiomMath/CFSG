module

public import CFSG.Quasithin.H13.NQCoreWholeModuleTools
public import CFSG.Quasithin.SteinbergCDOddResidualModule

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module CFSG.Quasithin
open CFSG.Quasithin.SteinbergBQ (commSpan)
open scoped IsMulCommutative commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isPGroup_map_conjGL {X V : Subgroup Q} [V.Normal] [IsMulCommutative ↥V]
    [Module (ZMod 2) (Additive ↥V)] {p : ℕ} (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hq : (CFSG.pCore 2 ↥X).map X.subtype ≤ centralizer (V : Set Q)) :
    IsPGroup p (X.map (conjGL V)) := by
  rintro ⟨γ, x, hx, rfl⟩
  obtain ⟨k, hk⟩ := hP (⟨x, hx⟩ : X)
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (⟨x, hx⟩ : X) ^ p ^ k ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  have h2 : x ^ p ^ k ∈ centralizer (V : Set Q) := hq ⟨_, h1, rfl⟩
  rw [← ker_conjGL] at h2
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← map_pow]
  exact h2

theorem whole_module_core {X : Subgroup Q} [X.Normal] (T : Sylow 2 Q)
    (hXT : X ⊔ (T : Subgroup Q) = ⊤) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hshape : (IsMulCommutative (X ⧸ CFSG.pCore 2 X) ∧ Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2) ∨
      (¬ IsMulCommutative (X ⧸ CFSG.pCore 2 X) ∧ Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 3))
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hWc : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ M : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ t ∈ (T : Subgroup Q), ∀ x : X,
        ((x : X ⧸ CFSG.pCore 2 X) : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ∈ M →
          (((MulAut.conjNormal t x : X) : X ⧸ CFSG.pCore 2 X) :
            (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ∈ M) → M = ⊥ ∨ M = ⊤)
    {V : Subgroup Q} (hVdef : V = ⁅primeReducedAggregate Q 2, X⁆) (hV : V ≠ ⊥) :
    primeReducedAggregate Q 2 = BlueprintB2.centerTorsion 2 (CFSG.pCore 2 Q) ∧
    ((X ⊓ centralizer (V : Set Q)).subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤
      frattini (X ⧸ CFSG.pCore 2 X) ∧
    (∀ v ∈ V, v ^ 2 = 1) ∧
    (T : Subgroup Q) ⊓ centralizer (V : Set Q) = CFSG.pCore 2 Q ∧
    ∃ _ : V.Normal, ∃ _ : IsMulCommutative ↥V, ∀ [Module (ZMod 2) (Additive ↥V)],
      Group.IsSolvable ↥(conjGL V).range ∧ CFSG.pCore 2 ↥(conjGL V).range = ⊥ ∧
      ¬ 3 ∣ Nat.card (conjGL V).range ∧
      ∃ _ : ((X.map (conjGL V)).subgroupOf (conjGL V).range).Normal,
      IsPGroup 2 (↥(conjGL V).range ⧸ (X.map (conjGL V)).subgroupOf (conjGL V).range) ∧
      ((IsElementaryAbelian p ↥(X.map (conjGL V)) ∧ Nat.card (X.map (conjGL V)) = p ^ 2) ∨
        ((∃ x y : ↥(X.map (conjGL V)), x * y ≠ y * x) ∧ Nat.card (X.map (conjGL V)) = p ^ 3 ∧
          ∀ x : ↥(X.map (conjGL V)), x ^ p = 1)) ∧
      commSpan (X.map (conjGL V)) = ⊤ ∧
      (IsElementaryAbelian p ↥(X.map (conjGL V)) →
        ∀ P' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
          P' ≤ X.map (conjGL V) →
          (∀ g ∈ (T : Subgroup Q).map (conjGL V), ∀ x ∈ P', g * x * g⁻¹ ∈ P') →
          P' = ⊥ ∨ P' = X.map (conjGL V)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  subst hVdef
  obtain ⟨hUZ, ⟨-, -, -, hVel⟩, -, hVX, hqB, -, -, -, -, hTC, -, ⟨hCn, hO2C⟩, -, hBΦ, hBn,
    hρall, ⟨eBq, heBq⟩, μ, hμ, α, β, hα, hβ, hμαβ⟩ :=
    SteinbergCD.irreducible_odd_residual_full_central_core_module_exact_kernel T hXT hp hp2 hP
      hirr rfl rfl rfl rfl rfl rfl rfl hV
  set V := ⁅primeReducedAggregate Q 2, X⁆ with hVd
  obtain ⟨hUn, -, -⟩ := primeReducedAggregate_normal_elementaryAbelian (E := Q) 2
  have hVn : V.Normal := Subgroup.commutator_normal _ _
  have hVc : IsMulCommutative ↥V := hVel.toIsMulCommutative
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have := hVel
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  refine ⟨hUZ, hBΦ, hV2, hTC, hVn, hVc, ?_⟩
  intro _
  have : Finite (Additive ↥V) := inferInstanceAs (Finite ↥V)
  have : FiniteDimensional (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) :=
    SteinbergBQ.finite_generalLinearGroup
  set ρ : Q →* MulAut ↥V := MulAut.conjNormal with hρ
  obtain ⟨hρsolv, -, -, -, ⟨eρ, heρ⟩⟩ := hρall ρ fun g v => rfl
  have hconj : conjGL V = (mulAutToGL V).comp ρ := rfl
  have hΓ : (conjGL V).range = ρ.range.map (mulAutToGL V) := by
    rw [hconj, MonoidHom.range_comp]
  have hPV : X.map (conjGL V) = (X.map ρ).map (mulAutToGL V) := by
    rw [hconj, ← Subgroup.map_map]
  have hsolv : Group.IsSolvable ↥(conjGL V).range := by
    rw [hΓ]
    exact Group.isSolvable_of_surjective (f := (ρ.range.equivMapOfInjective (mulAutToGL V)
      (mulAutToGL_injective V)).toMonoidHom) (MulEquiv.surjective _)
  have hO2 : CFSG.pCore 2 ↥(conjGL V).range = ⊥ := by
    have e : (Q ⧸ centralizer (V : Set Q)) ≃* ↥(conjGL V).range :=
      (QuotientGroup.quotientMulEquivOfEq (ker_conjGL V)).symm.trans
        (QuotientGroup.quotientKerEquivRange (conjGL V))
    rw [← CFSG.pCore_map_iso 2 e, hO2C, Subgroup.map_bot]
  have hqC : (CFSG.pCore 2 ↥X).map X.subtype ≤ centralizer (V : Set Q) :=
    hqB.trans inf_le_right
  have hPVp : IsPGroup p (X.map (conjGL V)) := isPGroup_map_conjGL hP hqC
  obtain ⟨hPn, hΓP⟩ := isPGroup_quotient_map_conjGL V T.isPGroup' hXT
  have h3 : ¬ 3 ∣ Nat.card (conjGL V).range := by
    have hcard := Subgroup.card_mul_index ((X.map (conjGL V)).subgroupOf (conjGL V).range)
    have hsub : Nat.card ((X.map (conjGL V)).subgroupOf (conjGL V).range) =
        Nat.card (X.map (conjGL V)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (map_le_range _ _)).toEquiv
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hPVp
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hΓP
    rw [hsub, ha, Subgroup.index_eq_card, hb] at hcard
    rw [← hcard]
    intro h3
    rcases (Nat.prime_three.dvd_mul).mp h3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  have ePV : (X ⧸ (X ⊓ centralizer (V : Set Q)).subgroupOf X) ≃* ↥(X.map (conjGL V)) := by
    rw [hPV]
    exact eρ.trans ((X.map ρ).equivMapOfInjective (mulAutToGL V) (mulAutToGL_injective V))
  have eP : ↥(X.map (conjGL V)) ≃* ((X ⧸ CFSG.pCore 2 X) ⧸
      ((X ⊓ centralizer (V : Set Q)).subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    ePV.symm.trans eBq
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hP⟩
  have hshapeV : (IsElementaryAbelian p ↥(X.map (conjGL V)) ∧
        Nat.card (X.map (conjGL V)) = p ^ 2) ∨
      ((∃ x y : ↥(X.map (conjGL V)), x * y ≠ y * x) ∧ Nat.card (X.map (conjGL V)) = p ^ 3 ∧
        ∀ x : ↥(X.map (conjGL V)), x ^ p = 1) := by
    rcases hshape with ⟨hab, hcard⟩ | ⟨hnab, hcard⟩
    · have hel : IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X) :=
        { toIsMulCommutative := hab, exponent_dvd_p := hexp ▸ dvd_rfl }
      have hΦ : frattini (X ⧸ CFSG.pCore 2 X) = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := p)
      have hK0 : ((X ⊓ centralizer (V : Set Q)).subgroupOf X).map
          (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊥ := le_bot_iff.mp (hΦ ▸ hBΦ)
      have e' : ↥(X.map (conjGL V)) ≃* (X ⧸ CFSG.pCore 2 X) :=
        eP.trans ((QuotientGroup.quotientMulEquivOfEq hK0).trans QuotientGroup.quotientBot)
      exact Or.inl ⟨isElementaryAbelian_of_mulEquiv' e'.symm hel,
        by rw [Nat.card_congr e'.toEquiv, hcard]⟩
    · have hΦcard : Nat.card (frattini (X ⧸ CFSG.pCore 2 X)) = p := by
        have h1 := Subgroup.card_mul_index (frattini (X ⧸ CFSG.pCore 2 X))
        rw [Subgroup.index_eq_card, hWc, hcard] at h1
        have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
        exact Nat.eq_of_mul_eq_mul_right hp2pos (by rw [h1]; ring)
      have hKdvd : Nat.card (((X ⊓ centralizer (V : Set Q)).subgroupOf X).map
          (QuotientGroup.mk' (CFSG.pCore 2 X))) ∣ p := hΦcard ▸ Subgroup.card_dvd_of_le hBΦ
      rcases (Nat.dvd_prime hp).mp hKdvd with hK1 | hKp
      · have hK0 := Subgroup.card_eq_one.mp hK1
        have e' : ↥(X.map (conjGL V)) ≃* (X ⧸ CFSG.pCore 2 X) :=
          eP.trans ((QuotientGroup.quotientMulEquivOfEq hK0).trans QuotientGroup.quotientBot)
        refine Or.inr ⟨?_, by rw [Nat.card_congr e'.toEquiv, hcard], fun x => ?_⟩
        · by_contra hc
          push Not at hc
          exact hnab ⟨⟨fun a b => e'.symm.injective (by rw [map_mul, map_mul]; exact hc _ _)⟩⟩
        · apply e'.injective
          rw [map_pow, map_one, ← hexp]
          exact Monoid.pow_exponent_eq_one _
      · have hKΦ : ((X ⊓ centralizer (V : Set Q)).subgroupOf X).map
            (QuotientGroup.mk' (CFSG.pCore 2 X)) = frattini (X ⧸ CFSG.pCore 2 X) :=
          Subgroup.eq_of_le_of_card_ge hBΦ (by rw [hΦcard, hKp])
        have e' : ↥(X.map (conjGL V)) ≃*
            ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
          eP.trans (QuotientGroup.quotientMulEquivOfEq hKΦ)
        exact Or.inl ⟨isElementaryAbelian_of_mulEquiv' e'.symm
          (isElementaryAbelian_quotient_frattini (p := p)),
          by rw [Nat.card_congr e'.toEquiv, hWc]⟩
  refine ⟨hsolv, hO2, h3, hPn, hΓP, hshapeV, commSpan_map_conjGL_eq_top V hVX, ?_⟩
  intro hel P' hP'P hinv
  set θ : ↥X →* ↥(X.map (conjGL V)) := (conjGL V).subgroupMap X with hθ
  have hθs : Function.Surjective θ := MonoidHom.subgroupMap_surjective _ _
  set K := ((X ⊓ centralizer (V : Set Q)).subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X))
    with hKdef
  have hΦK : frattini (X ⧸ CFSG.pCore 2 X) ≤ K := by
    have : Fact (IsPGroup p ((X ⧸ CFSG.pCore 2 X) ⧸ K)) :=
      ⟨hP.to_quotient K⟩
    have : IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ K) :=
      isElementaryAbelian_of_mulEquiv' eP hel
    have h1 := SteinbergCD.map_frattini_eq_of_ker_le_frattini (QuotientGroup.mk'_surjective K)
      (by rw [QuotientGroup.ker_mk']; exact hBΦ)
    rw [frattini_eq_bot_of_isElementaryAbelian (R := (X ⧸ CFSG.pCore 2 X) ⧸ K) (p := p)] at h1
    intro z hz
    have h2 : QuotientGroup.mk' K z = 1 := (Subgroup.mem_bot).mp (h1 ▸ mem_map_of_mem _ hz)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hθΦ : ∀ x : ↥X, ((x : X ⧸ CFSG.pCore 2 X) ∈ frattini (X ⧸ CFSG.pCore 2 X)) → θ x = 1 := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hΦK hx
    have hbx' : b⁻¹ * x ∈ CFSG.pCore 2 ↥X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [QuotientGroup.mk'_apply] at hbx
      rw [hbx, inv_mul_cancel]
    have hxB : (x : Q) ∈ X ⊓ centralizer (V : Set Q) := by
      have h1 : ((b⁻¹ * x : ↥X) : Q) ∈ X ⊓ centralizer (V : Set Q) := hqB ⟨_, hbx', rfl⟩
      have h2 : (x : Q) = (b : Q) * ((b⁻¹ * x : ↥X) : Q) := by simp
      rw [h2]
      exact mul_mem hb h1
    apply Subtype.ext
    have h3 : (x : Q) ∈ (conjGL V).ker := by rw [ker_conjGL]; exact (mem_inf.mp hxB).2
    exact h3
  set N : Subgroup ↥X := (P'.subgroupOf (X.map (conjGL V))).comap θ with hNdef
  have hNmem : ∀ x : ↥X, x ∈ N ↔ ((θ x : ↥(X.map (conjGL V))) :
      LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) ∈ P' := fun x => Iff.rfl
  set Mw := (N.map (QuotientGroup.mk' (CFSG.pCore 2 X))).map
    (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))) with hMw
  have hM : ∀ x : ↥X, ((x : X ⧸ CFSG.pCore 2 X) :
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ∈ Mw ↔ x ∈ N := by
    intro x
    constructor
    · rintro ⟨_, ⟨n, hn, rfl⟩, hnx⟩
      have h1 : ((n⁻¹ * x : ↥X) : X ⧸ CFSG.pCore 2 X) ∈ frattini (X ⧸ CFSG.pCore 2 X) := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        simp only [QuotientGroup.mk'_apply] at hnx
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnx, inv_mul_cancel]
      have h2 := hθΦ _ h1
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      rw [hNmem, ← h2]
      exact hn
    · intro hx
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rcases hirr Mw (fun t ht x hx => by
      rw [hM] at hx ⊢
      rw [hNmem] at hx ⊢
      have h1 : ((θ (MulAut.conjNormal t x) : ↥(X.map (conjGL V))) :
            LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) =
          conjGL V t * ((θ x : ↥(X.map (conjGL V))) :
            LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) * (conjGL V t)⁻¹ := by
        simp only [hθ, MonoidHom.subgroupMap_apply_coe, MulAut.conjNormal_apply, map_mul, map_inv]
      rw [h1]
      exact hinv _ ⟨t, ht, rfl⟩ _ hx) with hMb | hMt
  · left
    rw [eq_bot_iff]
    intro γ hγ
    obtain ⟨x, hx⟩ := hθs ⟨γ, hP'P hγ⟩
    have hxN : x ∈ N := by rw [hNmem, hx]; exact hγ
    have h1 := (hM x).mpr hxN
    rw [hMb, mem_bot, QuotientGroup.eq_one_iff] at h1
    have h2 := hθΦ x h1
    rw [hx] at h2
    exact (mem_bot).mpr (congrArg Subtype.val h2)
  · right
    refine le_antisymm hP'P fun γ hγ => ?_
    obtain ⟨x, hx⟩ := hθs ⟨γ, hγ⟩
    have h1 : x ∈ N := (hM x).mp (hMt ▸ mem_top _)
    rw [hNmem, hx] at h1
    exact h1

end CFSG.Quasithin.H13.NQCore
