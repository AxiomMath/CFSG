module

public import CFSG.RankThree.Classical2.CentralLiftCommutator
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.Classical2

open scoped commutatorElement
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev orthDerived (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

abbrev ProjOrthDerived (Q : QuadraticForm K V) : Type _ :=
  orthDerived Q ⧸ (scalars K V).subgroupOf (orthDerived Q)

section Reflections

variable {Q : QuadraticForm K V}

theorem reflect_apply_self {v : V} (hv : Q v ≠ 0) : reflect Q v v = -v := by
  rw [reflect_apply hv, polar_self_eq_two_mul, mul_div_cancel_right₀ _ hv]
  module

theorem reflect_apply_smul_self {v : V} (hv : Q v ≠ 0) (c : K) :
    reflect Q v (c • v) = -(c • v) := by
  rw [map_smul, reflect_apply_self hv, smul_neg]

theorem reflect_sub_apply (h2 : (2 : K) ≠ 0) {u v : V} (hu : Q u = 1) (hv : Q v = 1)
    (huv : polar Q u v = 0) :
    reflect Q (u - v) u = v ∧ reflect Q (u - v) v = u := by
  have hvu : polar Q v u = 0 := by rw [polar_comm, huv]
  have hQ : Q (u - v) = 2 := by
    have h := QuadraticMap.map_add Q u (-v)
    rw [QuadraticMap.map_neg, polar_neg_right, huv, neg_zero, add_zero, hu, hv] at h
    rw [sub_eq_add_neg, h]
    norm_num
  have hQ0 : Q (u - v) ≠ 0 := by rw [hQ]; exact h2
  have hpu : polar Q (u - v) u = 2 := by
    rw [polar_sub_left, polar_self_eq_two_mul, hu, hvu]
    ring
  have hpv : polar Q (u - v) v = -2 := by
    rw [polar_sub_left, polar_self_eq_two_mul, hv, huv]
    ring
  refine ⟨?_, ?_⟩
  · rw [reflect_apply hQ0, hpu, hQ, div_self h2, one_smul]
    abel
  · rw [reflect_apply hQ0, hpv, hQ, neg_div, div_self h2, neg_smul, one_smul, sub_neg_eq_add]
    abel

theorem commutatorElement_eichler {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {e u : V} (hge : g e = e)
    (hu : polar Q e u = 0) : ⁅g, eichler Q e u⁆ = eichler Q e (g u - u) := by
  have hgu : polar Q e (g u) = 0 := by rw [← hge, polar_map_of_mem hg, hu]
  have hnu : polar Q e (-u) = 0 := by rw [polar_neg_right, hu, neg_zero]
  rw [commutatorElement_def, eichler_conj hg, hge, eichler_inv hu, eichler_mul hgu hnu,
    sub_eq_add_neg]

theorem reflect_hyperbolic {e h : V} (he : Q e = 0) (hh : Q h = 0) (heh : polar Q e h = 1)
    {c : K} (hc : c ≠ 0) :
    reflect Q (e - c • h) e = c • h ∧ reflect Q (e - c • h) h = c⁻¹ • e ∧
      ∀ w, polar Q e w = 0 → polar Q h w = 0 → reflect Q (e - c • h) w = w := by
  have hhe : polar Q h e = 1 := by rw [polar_comm, heh]
  have hQ : Q (e - c • h) = -c := by
    have h1 := QuadraticMap.map_add Q e (-(c • h))
    rw [QuadraticMap.map_neg, QuadraticMap.map_smul, hh, he, polar_neg_right,
      polar_smul_right_eq, heh] at h1
    rw [sub_eq_add_neg, h1]
    simp
  have hQ0 : Q (e - c • h) ≠ 0 := by rw [hQ]; exact neg_ne_zero.mpr hc
  refine ⟨?_, ?_, fun w hw1 hw2 => ?_⟩
  · rw [reflect_apply hQ0, hQ, polar_sub_left, polar_self_eq_zero he, polar_smul_left_eq, hhe,
      mul_one, zero_sub, div_self (neg_ne_zero.mpr hc), one_smul]
    abel
  · rw [reflect_apply hQ0, hQ, polar_sub_left, polar_smul_left_eq, polar_self_eq_zero hh,
      mul_zero, sub_zero, heh, smul_sub, smul_smul]
    field_simp
    module
  · refine reflect_apply_of_polar_eq_zero ?_
    rw [polar_sub_left, polar_smul_left_eq, hw1, hw2, mul_zero, sub_zero]

theorem exists_mem_orthDerived_apply_eq_sq_smul {e h : V} (he : Q e = 0) (hh : Q h = 0)
    (heh : polar Q e h = 1) {a : K} (ha : a ≠ 0) :
    ∃ g ∈ orthDerived Q, g e = a ^ 2 • e ∧
      ∀ w, polar Q e w = 0 → polar Q h w = 0 → g w = w := by
  obtain ⟨s1e, s1h, s1w⟩ := reflect_hyperbolic he hh heh (c := 1) one_ne_zero
  obtain ⟨sae, sah, saw⟩ := reflect_hyperbolic he hh heh ha
  rw [one_smul] at s1e s1h s1w
  rw [inv_one, one_smul] at s1h
  set s := reflect Q (e - h)
  set r := reflect Q (e - a • h)
  have hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q := reflect_mem_orthogonalGroup Q _
  have hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q := reflect_mem_orthogonalGroup Q _
  have hss : ∀ x, s (s x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, reflect_mul_self]
    rfl
  have hcomm : ∀ x, ⁅s * r, s⁆ x = s (r (s (r x))) := fun x => by
    rw [commutatorElement_def, mul_inv_rev, reflect_inv, reflect_inv]
    simp only [LinearEquiv.mul_apply]
    rw [hss]
  refine ⟨⁅s * r, s⁆, Subgroup.commutator_mem_commutator (mul_mem hs hr) hs, ?_,
    fun w hw1 hw2 => ?_⟩
  · rw [hcomm, sae, map_smul, s1h, map_smul, sae, smul_smul, map_smul, s1h, ← pow_two]
  · rw [hcomm, saw w hw1 hw2, s1w w hw1 hw2, saw w hw1 hw2, s1w w hw1 hw2]

theorem exists_mem_orthDerived_double_sign (h2 : (2 : K) ≠ 0) {u v : V} (hu : Q u = 1)
    (hv : Q v = 1) (huv : polar Q u v = 0) :
    ∃ g ∈ orthDerived Q, g u = -u ∧ g v = -v ∧
      ∀ x, polar Q u x = 0 → polar Q v x = 0 → g x = x := by
  have hu0 : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hv0 : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  obtain ⟨hsu, hsv⟩ := reflect_sub_apply h2 hu hv huv
  set a := reflect Q u
  set b := reflect Q (u - v)
  have ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := reflect_mem_orthogonalGroup Q _
  have hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := reflect_mem_orthogonalGroup Q _
  have hvu : polar Q v u = 0 := by rw [polar_comm, huv]
  have hav : a v = v := reflect_apply_of_polar_eq_zero huv
  have hau : a u = -u := reflect_apply_self hu0
  refine ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator ha hb, ?_, ?_, fun x hx1 hx2 => ?_⟩
  · rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, reflect_inv, reflect_inv]
    change a (b (a (b u))) = -u
    rw [hsu, hav, hsv, hau]
  · rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, reflect_inv, reflect_inv]
    change a (b (a (b v))) = -v
    rw [hsv, hau, map_neg, hsu, map_neg, hav]
  · have hbx : b x = x := by
      refine reflect_apply_of_polar_eq_zero ?_
      rw [polar_sub_left, hx1, hx2, sub_zero]
    have hax : a x = x := reflect_apply_of_polar_eq_zero hx1
    rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, reflect_inv, reflect_inv]
    change a (b (a (b x))) = x
    rw [hbx, hax, hbx, hax]

end Reflections

theorem exists_double_sign_indices {d : ℕ} (hd : 4 ≤ d) {i j : Fin d} (hij : i ≠ j) :
    ∃ r s : Fin d, (r : ℕ) + 1 < d ∧ (s : ℕ) + 1 < d ∧ (r = i ∨ r = j) ∧ s ≠ i ∧ s ≠ j := by
  have hr : ∃ r : Fin d, (r : ℕ) + 1 < d ∧ (r = i ∨ r = j) := by
    by_cases hi : (i : ℕ) + 1 < d
    · exact ⟨i, hi, Or.inl rfl⟩
    · refine ⟨j, ?_, Or.inr rfl⟩
      have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      have := i.isLt
      have := j.isLt
      omega
  obtain ⟨r, hr1, hr2⟩ := hr
  by_cases h0 : (⟨0, by omega⟩ : Fin d) ≠ i ∧ (⟨0, by omega⟩ : Fin d) ≠ j
  · exact ⟨r, _, hr1, by simp; omega, hr2, h0.1, h0.2⟩
  by_cases h1 : (⟨1, by omega⟩ : Fin d) ≠ i ∧ (⟨1, by omega⟩ : Fin d) ≠ j
  · exact ⟨r, _, hr1, by simp; omega, hr2, h1.1, h1.2⟩
  refine ⟨r, ⟨2, by omega⟩, hr1, by simp; omega, hr2, ?_, ?_⟩ <;> intro h <;>
    simp only [ne_eq, Fin.ext_iff, not_and_or, not_not] at h0 h1 h <;> omega

universe u

theorem orthogonal_isotropic_line_unipotent_core {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) [FiniteDimensional K V] (Q : QuadraticForm K V)
    {e h : V} {D : Submodule K V} (he : Q e = 0) (hh : Q h = 0) (heh : polar Q e h = 1)
    (hDe : ∀ w ∈ D, polar Q e w = 0) (hDh : ∀ w ∈ D, polar Q h w = 0)
    (hDreg : (LinearMap.BilinForm.restrict (polarBilin Q) D).Nondegenerate)
    {d : ℕ} (hd : Module.finrank K D = d) (hd4 : 4 ≤ d) :
    ∃ U₀ : Subgroup (V ≃ₗ[K] V),
      (U₀ : Set (V ≃ₗ[K] V)) =
        {g : V ≃ₗ[K] V | ∃ w ∈ D, (g : V →ₗ[K] V) = orthElementaryMap Q e w} ∧
      U₀ ≤ orthDerived Q ∧
      Set.InjOn (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
        (U₀.subgroupOf (orthDerived Q)) ∧
      CFSG.Assembly.IsElemAbelian p ((U₀.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) ∧
      Nat.card ((U₀.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) = p ^ (f * d) ∧
      ∀ (Y : Type u) [Group Y] (φ : Y →* ProjOrthDerived Q), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y →
        ∀ x ∈ ((U₀.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).comap φ,
          ∀ y ∈ ((U₀.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).comap φ,
            x * y = y * x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h9 : p ^ f ≠ 9 := by
    intro h9
    have h1 : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact dvd_pow_self p (by omega)
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h1)
    omega
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at heh
    exact zero_ne_one heh
  have hDreg' : (polarBilin (Q.comp D.subtype)).Nondegenerate := by
    have : polarBilin (Q.comp D.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) D := by
      ext x y
      rfl
    rw [this]
    exact hDreg
  obtain ⟨vb, hvorth, hvnorm, hvlast⟩ := CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq
    (K := K) (V := D) hKodd hd (by omega) (Q.comp D.subtype) hDreg' one_ne_zero
  set v : Fin d → V := fun i => (vb i : V) with hvdef
  have hvD : ∀ i, v i ∈ D := fun i => (vb i).2
  have hvo : ∀ i j, i ≠ j → polar Q (v i) (v j) = 0 := hvorth
  have hv1 : ∀ i : Fin d, (i : ℕ) + 1 < d → Q (v i) = 1 := hvnorm
  have hv0 : ∀ i, Q (v i) ≠ 0 := by
    intro i
    by_cases hi : (i : ℕ) + 1 < d
    · rw [hv1 i hi]
      exact one_ne_zero
    · have : i = ⟨d - 1, by omega⟩ := Fin.ext (by have := i.isLt; simp only; omega)
      rw [this]
      exact hvlast
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  set Ω := orthDerived Q with hΩdef
  have hΩO : Ω ≤ O := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  set Zs := (scalars K V).subgroupOf Ω with hZsdef
  set ρ := QuotientGroup.mk' Zs with hρdef
  let θ : Multiplicative D →* (V ≃ₗ[K] V) :=
    { toFun := fun a => eichler Q e ((Multiplicative.toAdd a : D) : V)
      map_one' := by
        change eichler Q e ((0 : D) : V) = 1
        rw [ZeroMemClass.coe_zero, eichler_zero_right]
      map_mul' := fun a b => by
        change eichler Q e (((Multiplicative.toAdd a + Multiplicative.toAdd b : D)) : V) = _
        rw [Submodule.coe_add]
        exact (eichler_mul (hDe _ (Multiplicative.toAdd a).2)
          (hDe _ (Multiplicative.toAdd b).2)).symm }
  have hθ : ∀ w : D, θ (Multiplicative.ofAdd w) = eichler Q e (w : V) := fun w => rfl
  have hsingle : ∀ (i : Fin d) (c : K), eichler Q e (c • v i) ∈ Ω := by
    intro i c
    have hsO : reflect Q (v i) ∈ O := reflect_mem_orthogonalGroup Q _
    have hse : reflect Q (v i) e = e :=
      reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact hDe _ (hvD i))
    have hu : polar Q e (-(c / 2) • v i) = 0 := by
      rw [polar_smul_right_eq, hDe _ (hvD i), mul_zero]
    have hcomm := commutatorElement_eichler hsO hse hu
    have hcv : reflect Q (v i) (-(c / 2) • v i) - -(c / 2) • v i = c • v i := by
      rw [map_smul, reflect_apply_self (hv0 i)]
      have : c / 2 + c / 2 = c := by field_simp; ring
      calc -(c / 2) • -v i - -(c / 2) • v i = (c / 2 + c / 2) • v i := by module
        _ = c • v i := by rw [this]
    rw [hcv] at hcomm
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator hsO (eichler_mem_orthogonalGroup Q _ _)
  have hθΩ : ∀ a : Multiplicative D, θ a ∈ Ω := by
    intro a
    obtain ⟨w, rfl⟩ : ∃ w : D, Multiplicative.ofAdd w = a := ⟨Multiplicative.toAdd a, rfl⟩
    rw [← vb.sum_repr w, ofAdd_sum]
    refine (Ω.comap θ).prod_mem fun i _ => ?_
    rw [Subgroup.mem_comap, hθ, Submodule.coe_smul]
    exact hsingle i _
  let θΩ : Multiplicative D →* Ω := θ.codRestrict Ω hθΩ
  let θT : Multiplicative D →* ProjOrthDerived Q := ρ.comp θΩ
  have hrange : θ.range.subgroupOf Ω = θΩ.range := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  have hU : (θ.range.subgroupOf Ω).map ρ = θT.range := by
    rw [hrange, MonoidHom.map_range]
  have hθTinj : Function.Injective θT := by
    refine (injective_iff_map_eq_one θT).mpr fun a ha => ?_
    have hmem : θΩ a ∈ Zs := (QuotientGroup.eq_one_iff (θΩ a)).mp ha
    rw [hZsdef, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := mem_scalars.mp hmem
    obtain ⟨w, rfl⟩ : ∃ w : D, Multiplicative.ofAdd w = a := ⟨Multiplicative.toAdd a, rfl⟩
    have hc' : ∀ x, eichler Q e (w : V) x = c • x := hc
    have hce : c • e = e := by rw [← hc' e, eichler_apply_self]
    have hc1 : c = 1 := by
      have h1 : (c - 1) • e = 0 := by rw [sub_smul, hce, one_smul, sub_self]
      rcases smul_eq_zero.mp h1 with h1 | h1
      · exact sub_eq_zero.mp h1
      · exact absurd h1 he0
    have hwh := hc' h
    rw [hc1, one_smul, eichler_apply he (hDe _ w.2), polar_comm Q h e, heh, one_smul,
      hDh _ w.2, zero_add, mul_one, add_sub_assoc, add_eq_left, sub_eq_zero] at hwh
    have hQw : Q w = 0 := by
      have h1 := hDh _ w.2
      rw [hwh, polar_smul_right_eq, polar_comm, heh, mul_one] at h1
      exact h1
    rw [hQw, zero_smul] at hwh
    have hw0 : w = 0 := Subtype.ext hwh
    rw [hw0]
    rfl
  have hpow : ∀ a : Multiplicative D, a ^ p = 1 := by
    intro a
    change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = 1
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]
    rfl
  refine ⟨θ.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨((Multiplicative.toAdd a : D) : V), (Multiplicative.toAdd a).2,
        LinearMap.ext fun x => eichler_apply he (hDe _ (Multiplicative.toAdd a).2) x⟩
    · rintro ⟨w, hw, hg⟩
      refine ⟨Multiplicative.ofAdd ⟨w, hw⟩, LinearEquiv.ext fun x => ?_⟩
      rw [hθ, eichler_apply he (hDe w hw)]
      exact (LinearMap.congr_fun hg x).symm
  · rintro _ ⟨a, rfl⟩
    exact hθΩ a
  · intro x hx y hy hxy
    rw [hrange] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [hθTinj (show θT a = θT b from hxy)]
  · rw [hU]
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, rfl⟩⟩ := y
      change θT a * θT b = θT b * θT a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hpow, map_one]
  · rw [hU, ← Nat.card_congr (MonoidHom.ofInjective hθTinj).toEquiv, Nat.card_congr
      Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := K), hK, hd, ← pow_mul]
  ·
    intro Y _ φ hφ hker x hx y hy
    rw [hU] at hx hy
    refine mul_comm_of_liftComm_eq_one hφ hker (U := θT.range) ?_ hx hy
    set β : D → D → Y := fun a b =>
      liftComm φ hφ (θT (Multiplicative.ofAdd a)) (θT (Multiplicative.ofAdd b)) with hβdef
    have hcomm : ∀ a b : D, Commute (θT (Multiplicative.ofAdd a)) (θT (Multiplicative.ofAdd b)) :=
      fun a b => (Commute.all _ _).map θT
    have hβc : ∀ a b, β a b ∈ Subgroup.center Y := fun a b =>
      liftComm_mem_center hφ hker (hcomm a b)
    have hβadd₁ : ∀ a a' b, β (a + a') b = β a b * β a' b := fun a a' b => by
      simp only [hβdef, ofAdd_add, map_mul]
      exact liftComm_mul_left hφ hker (hcomm _ _)
    have hβadd₂ : ∀ a b b', β a (b + b') = β a b * β a b' := fun a b b' => by
      simp only [hβdef, ofAdd_add, map_mul]
      exact liftComm_mul_right hφ hker (hcomm _ _)
    have hβneg₁ : ∀ a b, β (-a) b = (β a b)⁻¹ := fun a b => by
      simp only [hβdef, ofAdd_neg, map_inv]
      exact liftComm_inv_left hφ hker (hcomm _ _)
    have hβneg₂ : ∀ a b, β a (-b) = (β a b)⁻¹ := fun a b => by
      simp only [hβdef, ofAdd_neg, map_inv]
      rw [liftComm_swap, liftComm_inv_left hφ hker (hcomm _ _).symm, inv_inv, liftComm_swap]
    have hβconj : ∀ g ∈ Ω, ∀ (c : K) (a a' b b' : D), g e = c • e →
        (a' : V) = c • g a → (b' : V) = c • g b → β a' b' = β a b := by
      intro g hg c a a' b b' hge ha' hb'
      have hconj : ∀ (u u' : D), (u' : V) = c • g u →
          ρ ⟨g, hg⟩ * θT (Multiplicative.ofAdd u) * (ρ ⟨g, hg⟩)⁻¹ =
            θT (Multiplicative.ofAdd u') := by
        intro u u' hu'
        change ρ ⟨g, hg⟩ * ρ (θΩ _) * (ρ ⟨g, hg⟩)⁻¹ = ρ (θΩ _)
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        change g * θ (Multiplicative.ofAdd u) * g⁻¹ = θ (Multiplicative.ofAdd u')
        rw [hθ, hθ, eichler_conj (hΩO hg), hge, eichler_smul_left, hu']
      have h := liftComm_conj hφ hker (hcomm a b) (ρ ⟨g, hg⟩)
      rw [hconj a a' ha', hconj b b' hb'] at h
      exact h
    have hsq : ∀ (a : K), a ≠ 0 → ∀ u u' : D, β (a ^ 2 • u) (a ^ 2 • u') = β u u' := by
      intro a ha u u'
      obtain ⟨g, hg, hge, hgw⟩ := exists_mem_orthDerived_apply_eq_sq_smul he hh heh ha
      exact hβconj g hg (a ^ 2) u _ u' _ hge
        (by rw [hgw _ (hDe _ u.2) (hDh _ u.2)]; rfl)
        (by rw [hgw _ (hDe _ u'.2) (hDh _ u'.2)]; rfl)
    have hline : ∀ (i : Fin d) (x y : K), β (x • vb i) (y • vb i) = 1 := by
      intro i
      let : CommGroup (Subgroup.center Y) :=
        { (inferInstance : Group (Subgroup.center Y)) with
          mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
      let b : K → K → Additive (Subgroup.center Y) := fun x y =>
        Additive.ofMul ⟨β (x • vb i) (y • vb i), hβc _ _⟩
      have hb0 := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero (W := Additive
        (Subgroup.center Y)) hp2 hK b
        (fun x x' y => by
          change Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _
          rw [← ofMul_mul]
          congr 1
          apply Subtype.ext
          rw [Subgroup.coe_mul, add_smul]
          exact hβadd₁ _ _ _)
        (fun x y y' => by
          change Additive.ofMul _ = Additive.ofMul _ + Additive.ofMul _
          rw [← ofMul_mul]
          congr 1
          apply Subtype.ext
          rw [Subgroup.coe_mul, add_smul]
          exact hβadd₂ _ _ _)
        (fun x => by
          change Additive.ofMul _ = 0
          rw [← ofMul_one]
          congr 1
          exact Subtype.ext (liftComm_self hφ _))
        (fun a ha x y => by
          change Additive.ofMul _ = Additive.ofMul _
          congr 1
          apply Subtype.ext
          change β ((a ^ 2 * x) • vb i) ((a ^ 2 * y) • vb i) = β (x • vb i) (y • vb i)
          rw [mul_smul, mul_smul]
          exact hsq a ha _ _)
        h9
      intro x y
      have := congrArg (fun z => ((Additive.toMul z : Subgroup.center Y) : Y)) (hb0 x y)
      simpa [b] using this
    have hcross : ∀ (i j : Fin d), i ≠ j → ∀ x y : K, β (x • vb i) (y • vb j) ^ 2 = 1 := by
      intro i j hij x y
      obtain ⟨r, s, hr, hs, hrij, hsi, hsj⟩ := exists_double_sign_indices hd4 hij
      have hrs : r ≠ s := by
        rintro rfl
        rcases hrij with rfl | rfl
        · exact hsi rfl
        · exact hsj rfl
      obtain ⟨ε, hεΩ, hεr, hεs, hεx⟩ :=
        exists_mem_orthDerived_double_sign h2 (hv1 r hr) (hv1 s hs) (hvo r s hrs)
      have hεe : ε e = e := hεx e (by rw [polar_comm]; exact hDe _ (hvD r))
        (by rw [polar_comm]; exact hDe _ (hvD s))
      have hεk : ∀ k, k ≠ r → k ≠ s → ε (v k) = v k := fun k hkr hks =>
        hεx (v k) (hvo r k (Ne.symm hkr)) (hvo s k (Ne.symm hks))
      have hsq1 : ∀ z : Y, z = z⁻¹ → z ^ 2 = 1 := fun z hz => by
        rw [pow_two]
        nth_rewrite 2 [hz]
        exact mul_inv_cancel z
      apply hsq1
      rcases hrij with rfl | rfl
      ·
        have h := hβconj ε hεΩ 1 (x • vb r) (-(x • vb r)) (y • vb j) (y • vb j) (by rw [one_smul,
          hεe]) (by rw [one_smul, Submodule.coe_neg, Submodule.coe_smul, map_smul, hεr,
            smul_neg]) (by rw [one_smul, Submodule.coe_smul, map_smul, hεk j hij.symm hsj.symm])
        rw [hβneg₁] at h
        exact h.symm
      ·
        have h := hβconj ε hεΩ 1 (x • vb i) (x • vb i) (y • vb r) (-(y • vb r)) (by rw [one_smul,
          hεe]) (by rw [one_smul, Submodule.coe_smul, map_smul, hεk i hij hsi.symm])
          (by rw [one_smul, Submodule.coe_neg, Submodule.coe_smul, map_smul, hεr, smul_neg])
        rw [hβneg₂] at h
        exact h.symm
    have hβ : ∀ (i j : Fin d) (x y : K), β (x • vb i) (y • vb j) = 1 := by
      have : NeZero (2 : K) := ⟨h2⟩
      intro i j x y
      rcases eq_or_ne i j with rfl | hij
      · exact hline i x y
      · have hx : x • vb i = (x / 2) • vb i + (x / 2) • vb i := by
          rw [← add_smul, add_halves]
        rw [hx, hβadd₁, ← pow_two]
        exact hcross i j hij _ _
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine liftComm_eq_one_of_closure hφ hker θT
      (S := {w | ∃ (i : Fin d) (c : K), w = c • vb i}) ?_ ?_ a b
    · refine eq_top_iff.mpr fun w _ => ?_
      rw [← vb.sum_repr w]
      exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ⟨i, _, rfl⟩
    · rintro _ ⟨i, x, rfl⟩ _ ⟨j, y, rfl⟩
      exact hβ i j x y

theorem orthogonal_isotropic_line_unipotent_central_preimage_abelian {p f : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) [FiniteDimensional K V]
    (Q : QuadraticForm K V) (_hB : (polarBilin Q).Nondegenerate) {e h : V}
    {D R : Submodule K V} (he : Q e = 0) (hh : Q h = 0) (heh : polar Q e h = 1)
    (hDe : ∀ w ∈ D, polar Q e w = 0) (hDh : ∀ w ∈ D, polar Q h w = 0)
    (_hRe : ∀ x ∈ R, polar Q e x = 0) (_hRh : ∀ x ∈ R, polar Q h x = 0)
    (_hDR : ∀ w ∈ D, ∀ x ∈ R, polar Q w x = 0) (_hV : Submodule.span K {e, h} ⊔ D ⊔ R = ⊤)
    (hDreg : (LinearMap.BilinForm.restrict (polarBilin Q) D).Nondegenerate)
    (_hRreg : (LinearMap.BilinForm.restrict (polarBilin Q) R).Nondegenerate)
    {d : ℕ} (hd : Module.finrank K D = d) (hd4 : 4 ≤ d) :
    ∃ U₀ : Subgroup (V ≃ₗ[K] V),
      (U₀ : Set (V ≃ₗ[K] V)) =
        {g : V ≃ₗ[K] V | ∃ w ∈ D, (g : V →ₗ[K] V) = orthElementaryMap Q e w} ∧
      U₀ ≤ orthDerived Q ∧
      Set.InjOn (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
        (U₀.subgroupOf (orthDerived Q)) ∧
      CFSG.Assembly.IsElemAbelian p ((U₀.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) ∧
      Nat.card ((U₀.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) = p ^ (f * d) ∧
      ∀ (Y : Type u) [Group Y] (φ : Y →* ProjOrthDerived Q), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y →
        ∀ x ∈ ((U₀.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).comap φ,
          ∀ y ∈ ((U₀.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).comap φ,
            x * y = y * x :=
  orthogonal_isotropic_line_unipotent_core hp hp3 hf hK Q he hh heh hDe hDh hDreg hd hd4

end CFSG.RankThree.Classical2
