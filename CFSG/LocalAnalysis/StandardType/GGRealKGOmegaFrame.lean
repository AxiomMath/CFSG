module

public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RealKGOmega

open Module QuadraticMap Multiplicative SpCoord CFSG.RankThree.OrthogonalInvolutions
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen
open CFSG.RankThree.Classical2 (orthDerived)

section Involution

variable {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem mul_self_eq_one_of_finrank_commSpace_le_one (hQ : (polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[F] V} (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h1 : finrank F (commSpace x) ≤ 1) : x * x = 1 := by
  rcases Nat.lt_or_ge (finrank F (commSpace x)) 1 with h0 | h0
  · have hbot : commSpace x = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hx1 : ∀ y, x y = y := fun y => by
      have h := sub_mem_commSpace x y
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at h
      exact h
    refine LinearEquiv.ext fun y => ?_
    rw [LinearEquiv.mul_apply, hx1, hx1]
    rfl
  · have hone : finrank F (commSpace x) = 1 := by omega
    obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp hone
    have hd : ∀ y, ∃ d : F, x y = y + d • (w : V) := by
      intro y
      obtain ⟨d, hd⟩ := hw ⟨x y - y, sub_mem_commSpace x y⟩
      refine ⟨d, ?_⟩
      have h := congrArg Subtype.val hd
      rw [Submodule.coe_smul] at h
      rw [h]
      exact (add_sub_cancel y (x y)).symm
    have hw0' : (w : V) ≠ 0 := fun h => hw0 (Subtype.ext h)
    obtain ⟨c, hc⟩ := hd w
    have hpw : polar Q (w : V) w = 0 := by
      rw [QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]
    obtain ⟨y, hy⟩ : ∃ y, polar Q y (w : V) ≠ 0 := by
      by_contra! h
      exact hw0' (hQ.1 w fun z => by rw [polarBilin_apply_apply, polar_comm]; exact h z)
    obtain ⟨d, hdy⟩ := hd y
    have hinv := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx y w
    rw [hdy, hc] at hinv
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hpw,
      smul_eq_mul, mul_zero, add_zero] at hinv
    have hc0 : c = 0 := by
      have h2 : c * polar Q y (w : V) = 0 := by linear_combination hinv
      exact (mul_eq_zero.mp h2).resolve_right hy
    rw [hc0, zero_smul, add_zero] at hc
    refine LinearEquiv.ext fun z => ?_
    obtain ⟨d', hd'⟩ := hd z
    rw [LinearEquiv.mul_apply, hd', map_add, map_smul, hc, hd', add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rfl

end Involution

section Frame

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}

theorem frame_coe_pow_eq_one (hF : IsPlaneFrame Q p U e E) (j : Fin k) :
    ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p = 1 := by
  have h := congrArg Subtype.val (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
  simpa using h

theorem not_eigen (hF : IsPlaneFrame Q p U e E) (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1)
    {j : Fin k} {y : V} (hy : y ∈ U j) (hy0 : y ≠ 0) (μ : F)
    (hμ : ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) y = μ • y) : False := by
  have hpow : ∀ n : ℕ, (((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ n) y = μ ^ n • y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hμ, smul_smul, pow_succ]
  have hp1 : μ ^ p = 1 := by
    have h := hpow p
    rw [frame_coe_pow_eq_one hF j] at h
    change y = μ ^ p • y at h
    have h2 : (μ ^ p - 1) • y = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hy0)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hp1
    exact zero_ne_one hp1
  have hq : μ ^ (Nat.card F - 1) = 1 := by
    haveI := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one μ hμ0
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hp1) with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    subst h1
    rw [one_smul] at hμ
    exact hy0 (hF.eq_zero_of_apply_eq j y hy hμ)
  · exact hpq (h1 ▸ orderOf_dvd_of_pow_eq_one hq)

theorem frame_apply_sub_mem (hF : IsPlaneFrame Q p U e E) (j : Fin k) (v : V) :
    ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) v - v ∈ U j := by
  have hv : v ∈ U j ⊔ polarPerp Q (U j) := by
    rw [(isCompl_polarPerp (hF.nondeg j)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hF.apply_of_perp j b hb, add_sub_add_right_eq_sub]
  exact sub_mem (hF.maps_to j a ha) ha

theorem frame_exists_apply_sub_eq (hF : IsPlaneFrame Q p U e E) (j : Fin k) {x : V}
    (hx : x ∈ U j) : ∃ x₀ ∈ U j, ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) x₀ - x₀ = x := by
  let φ : U j →ₗ[F] U j :=
    (((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap - LinearMap.id).restrict
      fun z _ => frame_apply_sub_mem hF j z
  have hφ : ∀ z, (φ z : V) = ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) z - z := fun z => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h := congrArg Subtype.val hz
    rw [hφ, Submodule.coe_zero, sub_eq_zero] at h
    exact Subtype.ext (hF.eq_zero_of_apply_eq j z z.2 h)
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  exact ⟨z, z.2, by rw [← hφ, hz]⟩

theorem mem_span_pair (hF : IsPlaneFrame Q p U e E) (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1)
    {j : Fin k} {y : V} (hy : y ∈ U j) (hy0 : y ≠ 0) {x : V} (hx : x ∈ U j) :
    x ∈ Submodule.span F (Set.range ![y, ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) y]) := by
  set ey := ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) y
  have hli : LinearIndependent F ![y, ey] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hy0, rfl⟩
    · exfalso
      refine not_eigen hF hp hpq hy hy0 (-(t⁻¹ * s)) ?_
      have h1 : t • ey = -(s • y) := eq_neg_of_add_eq_zero_right hst
      calc ey = t⁻¹ • (t • ey) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = -(t⁻¹ * s) • y := by rw [h1, smul_neg, smul_smul, neg_smul]
  have hle : Submodule.span F (Set.range ![y, ey]) ≤ U j := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact hy
    · exact hF.maps_to j y hy
  have hfr : finrank F (Submodule.span F (Set.range ![y, ey])) = finrank F (U j) := by
    rw [finrank_span_eq_card hli, Fintype.card_fin, hF.finrank_eq j]
  rw [Submodule.eq_of_le_of_finrank_eq hle hfr]
  exact hx

theorem eq_one_of_mul_self_of_commute (hF : IsPlaneFrame Q p U e E) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (htop : (⨆ j, U j) = ⊤) {t : V ≃ₗ[F] V} (ht : t * t = 1)
    (hc : ∀ j, t * ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) * t) : t = 1 := by
  refine hF.toIsPlaneSystem.eq_one_of_apply_eq (fun j x hx => ?_) (fun x hx => ?_)
  · have hce : ∀ z, t (((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) z) =
        ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) (t z) := fun z => by
      have h := LinearEquiv.congr_fun (hc j) z
      simpa using h
    have htU : ∀ z ∈ U j, t z ∈ U j := by
      intro z hz
      obtain ⟨z₀, -, rfl⟩ := frame_exists_apply_sub_eq hF j hz
      rw [map_sub, hce]
      exact frame_apply_sub_mem hF j _
    have htt : ∀ z, t (t z) = z := fun z => by
      have h := LinearEquiv.congr_fun ht z
      simpa using h
    set y := t x - x with hydef
    have hyU : y ∈ U j := sub_mem (htU x hx) hx
    have hty : t y = y := by
      have h2 : (2 : F) • y = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
      rw [two_smul] at h2
      rw [hydef, map_sub, htt, ← neg_sub]
      exact neg_eq_of_add_eq_zero_left h2
    by_contra hne
    have hy0 : y ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have htey : t (((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) y) =
        ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) y := by rw [hce, hty]
    have hfix : Submodule.span F (Set.range ![y, ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) y]) ≤
        LinearMap.ker ((t : V →ₗ[F] V) - LinearMap.id) := by
      rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · simp [LinearMap.mem_ker, hty]
      · simp [LinearMap.mem_ker, htey]
    have hxk := hfix (mem_span_pair hF hp hpq hyU hy0 hx)
    rw [LinearMap.mem_ker] at hxk
    exact hne (sub_eq_zero.mp hxk)
  · have hbot : polarPerp Q (⨆ j, U j) = ⊥ := by
      have h := hF.toIsPlaneSystem.isCompl_iSup
      rw [htop] at h ⊢
      exact top_disjoint.mp h.disjoint
    rw [hbot, Submodule.mem_bot] at hx
    rw [hx, map_zero]

theorem reflection_mul_comm (hF : IsPlaneFrame Q p U e E) {a b : Fin k} (hab : b ≠ a) {v : V}
    (hv : v ∈ U a) [Invertible (Q v)] :
    TauCeti.QuadraticMap.reflection Q v * ((e b : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      ((e b : ↥(orthDerived Q)) : V ≃ₗ[F] V) * TauCeti.QuadraticMap.reflection Q v := by
  have hev : ((e b : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = v :=
    hF.apply_of_perp b v (mem_polarPerp_iff.2 fun y hy => hF.perp b a hab y hy v hv)
  have hO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (e b).2
  refine LinearEquiv.ext fun x => ?_
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO v x
  rw [hev] at h1
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, TauCeti.QuadraticMap.reflection_apply,
    TauCeti.QuadraticMap.reflection_apply, map_sub, map_smul, hev, h1]

theorem reflection_conj_self (hQ : (polarBilin Q).Nondegenerate) (hF : IsPlaneFrame Q p U e E)
    {a : Fin k} {v : V} (hv : v ∈ U a) [Invertible (Q v)] :
    TauCeti.QuadraticMap.reflection Q v * ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
      TauCeti.QuadraticMap.reflection Q v = ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V)⁻¹ := by
  set ρ := TauCeti.QuadraticMap.reflection Q v with hρ
  set ea := ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V) with hea
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have heΩ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (e a).2
  obtain ⟨heO, heven⟩ := mem_omegaGroup.mp heΩ
  have hle : commSpace (ρ * ea) ≤ U a := by
    intro z hz
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hz
    have h1 : ρ (ea y) - ea y ∈ U a := by
      rw [hρ, TauCeti.QuadraticMap.reflection_apply, sub_sub_cancel_left]
      exact neg_mem (Submodule.smul_mem _ _ hv)
    have h2 : ea y - y ∈ U a := frame_apply_sub_mem hF a y
    have h3 : (ρ * ea) y - y = (ρ (ea y) - ea y) + (ea y - y) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [h3]
    exact add_mem h1 h2
  have hdim2 : finrank F (commSpace (ρ * ea)) ≤ 2 := by
    have h := Submodule.finrank_mono hle
    rwa [hF.finrank_eq a] at h
  have hpar := natCast_finrank_commSpace_mul hQ hρO heO
  rw [finrank_commSpace_reflection hQ v, (ZMod.natCast_eq_zero_iff_even).mpr heven, add_zero,
    Nat.cast_one] at hpar
  have hodd : ¬ Even (finrank F (commSpace (ρ * ea))) := by
    rw [← ZMod.natCast_eq_zero_iff_even, hpar]
    exact one_ne_zero
  have hle1 : finrank F (commSpace (ρ * ea)) ≤ 1 := by
    rcases Nat.lt_or_ge (finrank F (commSpace (ρ * ea))) 2 with h | h
    · omega
    · exact absurd (show Even 2 from even_two) (by
        rwa [show finrank F (commSpace (ρ * ea)) = 2 by omega] at hodd)
  have hinv := mul_self_eq_one_of_finrank_commSpace_le_one hQ (mul_mem hρO heO) hle1
  have hρρ : ρ * ρ = 1 := mul_self_eq_one_of_finrank_commSpace_le_one hQ hρO
    (by rw [finrank_commSpace_reflection hQ v])
  have h4 : ρ * ea * ρ * ea = 1 := by
    calc ρ * ea * ρ * ea = ρ * ea * (ρ * ea) := by rw [mul_assoc (ρ * ea)]
      _ = 1 := hinv
  exact eq_inv_of_mul_eq_one_left h4

theorem reflection_conj_tau (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hF : IsPlaneFrame Q p U e E) {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (ofAdd 1)) = e c) {a : Fin k} {v : V} (hv : v ∈ U a)
    [Invertible (Q v)] (f : Fin k → Multiplicative (ZMod p)) :
    TauCeti.QuadraticMap.reflection Q v * ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
      (TauCeti.QuadraticMap.reflection Q v)⁻¹ =
      ((τ (sgnAut a f) : ↥(orthDerived Q)) : V ≃ₗ[F] V) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hρO : TauCeti.QuadraticMap.reflection Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have hρρ : TauCeti.QuadraticMap.reflection Q v * TauCeti.QuadraticMap.reflection Q v = 1 :=
    mul_self_eq_one_of_finrank_commSpace_le_one hQ hρO
      (by rw [finrank_commSpace_reflection hQ v])
  have hρinv : (TauCeti.QuadraticMap.reflection Q v)⁻¹ = TauCeti.QuadraticMap.reflection Q v :=
    inv_eq_of_mul_eq_one_right hρρ
  refine conj_eq_of_mulSingle ((orthDerived Q).subtype.comp τ) _ (sgnAut a) (fun d => ?_) f
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [hρinv]
  by_cases hda : d = a
  · subst hda
    rw [sgnAut_mulSingle_self, map_inv, hτ d, Subgroup.coe_inv]
    exact reflection_conj_self hQ hF hv
  · rw [sgnAut_mulSingle_of_ne hda, hτ d, reflection_mul_comm hF hda hv, mul_assoc, hρρ,
      mul_one]

private theorem coe_conj {g : ↥(orthDerived Q)} {x y : ↥(orthDerived Q)} (h : g * x * g⁻¹ = y) :
    (g : V ≃ₗ[F] V) * (x : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹ = (y : V ≃ₗ[F] V) := by
  rw [← h]
  rfl

theorem not_induces_sgnAut (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (hF : IsPlaneFrame Q p U e E) (htop : (⨆ j, U j) = ⊤)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (ofAdd 1)) = e c) {a : Fin k} {v : V} (hv : v ∈ U a)
    (hQv : Q v ≠ 0) (g : ↥(orthDerived Q)) (hg : ∀ f, g * τ f * g⁻¹ = τ (sgnAut a f)) :
    False := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Invertible (Q v) := invertibleOfNonzero hQv
  set ρ := TauCeti.QuadraticMap.reflection Q v with hρ
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have hρρ : ρ * ρ = 1 := mul_self_eq_one_of_finrank_commSpace_le_one hQ hρO
    (by rw [finrank_commSpace_reflection hQ v])
  have hgΩ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ g.2
  obtain ⟨hgO, hgeven⟩ := mem_omegaGroup.mp hgΩ
  set h : V ≃ₗ[F] V := (g : V ≃ₗ[F] V) * ρ with hh
  have hge : ∀ j, (g : V ≃ₗ[F] V) * ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
      (g : V ≃ₗ[F] V)⁻¹ = ((τ (sgnAut a (Pi.mulSingle j (ofAdd 1))) : ↥(orthDerived Q)) :
        V ≃ₗ[F] V) := fun j => by
    rw [← hτ j]
    exact coe_conj (hg _)
  have hc : ∀ j, h * ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) * h := by
    intro j
    by_cases hja : j = a
    · subst hja
      have h1 := hge j
      rw [sgnAut_mulSingle_self, map_inv, hτ j, Subgroup.coe_inv] at h1
      have h2 : ρ * ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
          ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V)⁻¹ * ρ := by
        rw [← reflection_conj_self hQ hF hv, mul_assoc _ ρ ρ, hρρ, mul_one]
      have h3 : (g : V ≃ₗ[F] V) * ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V)⁻¹ =
          ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
        have h4 := congrArg Inv.inv h1
        rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc] at h4
        exact mul_inv_eq_iff_eq_mul.mp h4
      rw [hh, mul_assoc, h2, ← mul_assoc, h3, mul_assoc]
    · have h1 := hge j
      rw [sgnAut_mulSingle_of_ne hja, hτ j] at h1
      have h3 : (g : V ≃ₗ[F] V) * ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
          ((e j : ↥(orthDerived Q)) : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
        exact mul_inv_eq_iff_eq_mul.mp h1
      rw [hh, mul_assoc, reflection_mul_comm hF hja hv, ← mul_assoc, h3, mul_assoc]
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hgO hρO
  have hpar := natCast_finrank_commSpace_mul hQ hgO hρO
  rw [finrank_commSpace_reflection hQ v, (ZMod.natCast_eq_zero_iff_even).mpr hgeven, zero_add,
    Nat.cast_one] at hpar
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun x : V ≃ₗ[F] V => (x : V → V))
    fun x y hxy => LinearEquiv.ext (congrFun hxy)
  set H : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := ⟨h, hO⟩ with hH
  have hD : dicksonHom Q hQ H = ofAdd (1 : ZMod 2) := by
    rw [dicksonHom_apply]
    exact congrArg ofAdd hpar
  have hn := pow_orderOf_eq_one H
  have hDn : (ofAdd (1 : ZMod 2)) ^ orderOf H = 1 := by
    rw [← hD, ← map_pow, hn, map_one]
  rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_one, ZMod.natCast_eq_zero_iff_even] at hDn
  obtain ⟨m, hm⟩ := hDn
  have hpos := orderOf_pos H
  have hm0 : m ≠ 0 := by omega
  have hmlt : m < orderOf H := by omega
  have hne := pow_ne_one_of_lt_orderOf hm0 hmlt
  have htt : (H ^ m) * (H ^ m) = 1 := by rw [← pow_add, ← hm, hn]
  have hcoe : ((H ^ m : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) : V ≃ₗ[F] V) = h ^ m := by
    rw [SubgroupClass.coe_pow]
  have ht1 := eq_one_of_mul_self_of_commute hF hp hpq htop (t := h ^ m)
    (by rw [← hcoe, ← Subgroup.coe_mul, htt]; rfl)
    (fun j => ((Commute.pow_left (hc j) m)).eq)
  exact hne (Subtype.ext (by rw [hcoe, ht1]; rfl))

theorem isSignedPerm_of_normalizer (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0) {u : Fin k → V} {c t : F}
    (hF : IsCoherentFrame Q p U e E u c t) (hk : 0 < k)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    {τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q)} (hτinj : Function.Injective τ)
    (hτE : τ.range = E) (hτ : ∀ c, τ (Pi.mulSingle c (ofAdd 1)) = e c) {g : ↥(orthDerived Q)}
    {w : MulAut (Fin k → Multiplicative (ZMod p))} (hgw : ∀ f, g * τ f * g⁻¹ = τ (w f)) :
    IsSignedPerm ⇑w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hE := hF.isElemAbelian
  set A := E.map (orthDerived Q).subtype with hAdef
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE hx hy]
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, hsc ⟨g, hg⟩ (fun x hx => Subtype.ext (hgc _ ⟨x, hx, rfl⟩))
      (Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)), rfl⟩
  have hne : ∃ b ∈ A, b ≠ 1 := by
    refine ⟨((e ⟨0, hk⟩ : ↥(orthDerived Q)) : V ≃ₗ[F] V), ⟨e ⟨0, hk⟩, hF.toIsPlaneFrame.mem ⟨0, hk⟩, rfl⟩, ?_⟩
    intro h1
    have h2 := hF.orderOf_eq ⟨0, hk⟩
    rw [show e ⟨0, hk⟩ = 1 from Subtype.ext h1, orderOf_one] at h2
    exact hp.one_lt.ne h2
  obtain ⟨r, τ', hτ'inj, hτ'A, -, -, hnorm, -⟩ :=
    OrthTorus.exists_torus hp2 (Or.inr hpq) hQ hT hAΩ hApow hAcomm hmax hne
  set τG : (Fin k → Multiplicative (ZMod p)) →* (V ≃ₗ[F] V) := (orthDerived Q).subtype.comp τ
    with hτG
  have hτGinj : Function.Injective τG :=
    (Subgroup.subtype_injective _).comp hτinj
  have hτGA : τG.range = A := by
    rw [hτG, MonoidHom.range_comp, hτE]
  have hrk : r = k := by
    haveI : Fintype (Fin r → Multiplicative (ZMod p)) := Fintype.ofFinite _
    have h1 : Nat.card (Fin r → Multiplicative (ZMod p)) = Nat.card A := by
      rw [← hτ'A]
      exact Nat.card_congr (MonoidHom.ofInjective hτ'inj).toEquiv
    have h2 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card A := by
      rw [← hτGA]
      exact Nat.card_congr (MonoidHom.ofInjective hτGinj).toEquiv
    rw [← h2, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r),
      Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin, Fintype.card_fin] at h1
    have hlt : 2 ≤ Nat.card (Multiplicative (ZMod p)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      exact hp.two_le
    exact Nat.pow_right_injective hlt h1
  subst hrk
  have h'' : ∀ (g : V ≃ₗ[F] V) (u : MulAut (Fin r → Multiplicative (ZMod p))),
      (∀ f, g * τ' f * g⁻¹ = τ' (u f)) → IsSignedPerm ⇑u := by
    intro g u hgu
    obtain ⟨π, ε, hε, hπ⟩ := hnorm g fun a ha => by
      rw [← hτ'A] at ha ⊢
      obtain ⟨f, rfl⟩ := ha
      exact ⟨u f, (hgu f).symm⟩
    exact ⟨π, ε, hε, fun f i => hπ f (u f) (hgu f) i⟩
  have hs : ∀ i : Fin r, ∃ g : V ≃ₗ[F] V, ∀ f, g * τG f * g⁻¹ = τG (sgnAut i f) := by
    intro i
    letI : Invertible (Q (u i)) := invertibleOfNonzero (by rw [hF.quad_eq i]; exact hF.c_ne_zero)
    exact ⟨TauCeti.QuadraticMap.reflection Q (u i), fun f =>
      reflection_conj_tau hQ hp hF.toIsPlaneFrame hτ (hF.mem i) f⟩
  have hswap : ∀ i j : Fin r, i < j → ∃ g : V ≃ₗ[F] V,
      ∀ f, g * τG f * g⁻¹ = τG (permAut (Equiv.swap i j) f) := by
    intro i j hij
    refine ⟨frameSwap Q e u c t i j, fun f => ?_⟩
    refine conj_eq_of_mulSingle τG _ (permAut (Equiv.swap i j)) (fun l => ?_) f
    simp only [hτG, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [inv_eq_of_mul_eq_one_left (frameSwap_mul_self hF hij.ne)]
    by_cases hli : l = i
    · rw [hli, permAut_mulSingle, Equiv.swap_apply_left, hτ j, hτ i]
      exact frameSwap_conj_left hF hij.ne
    · by_cases hlj : l = j
      · rw [hlj, permAut_mulSingle, Equiv.swap_apply_right, hτ i, hτ j]
        exact frameSwap_conj_right hF hij.ne
      · rw [permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hli hlj, hτ l]
        exact frameSwap_conj_of_ne hF hij.ne hli hlj
  have ht : ∀ a b : Fin r, a ≠ b →
      ∃ g : V ≃ₗ[F] V, ∀ f, g * τG f * g⁻¹ = τG (permAut (Equiv.swap a b) f) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact hswap a b h
    · rw [Equiv.swap_comm]
      exact hswap b a h
  refine RealKGModelRoot.isSignedPerm_of_coords hp hτGinj hτ'inj (hτ'A.trans hτGA.symm) h'' hs ht
    (g := (g : V ≃ₗ[F] V)) fun f => ?_
  exact coe_conj (hgw f)

end Frame

end RealKGOmega

end CFSG.StandardType

end
