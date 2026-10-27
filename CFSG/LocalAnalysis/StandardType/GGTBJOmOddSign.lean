module

public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth TypeBDatum TypeDDatum
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private theorem tbjO_toAdd_piMul_mulSingle (j k : Fin r)
    (c : Multiplicative (ZMod p)) :
    (toAdd (piMul r p (Pi.mulSingle j c))) k = if k = j then toAdd c else 0 := by
  rw [piMul_apply, toAdd_ofAdd]
  by_cases h : k = j
  · subst h
    simp [Pi.mulSingle_apply]
  · simp [Pi.mulSingle_apply, h, toAdd_one]

private noncomputable def tbjO_gen (Δ : TBJOmData Q p A r) (j : Fin r) :
    V ≃ₗ[K] V :=
  Δ.F.ι (piMul r p (Pi.mulSingle j (ofAdd 1)))

private theorem tbjO_gen_mem (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q) (j : Fin r) :
    tbjO_gen Δ j ∈ orthDerived Q :=
  hA (Δ.F.mem (piMul r p (Pi.mulSingle j (ofAdd 1))))

private theorem tbjO_gen_apply_eq_self_iff [Fact p.Prime] (Δ : TBJOmData Q p A r) (j : Fin r)
    (v : V) :
    tbjO_gen Δ j v = v ↔ ∀ u ∈ Δ.F.U j, polar Q u v = 0 := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  change Δ.F.ι (piMul r p (Pi.mulSingle j (ofAdd 1))) v = v ↔ _
  rw [Δ.F.fix]
  constructor
  · intro h u hu
    refine h j ?_ u hu
    rw [tbjO_toAdd_piMul_mulSingle]
    simp
  · intro h k hk u hu
    by_cases hkj : k = j
    · subst hkj
      exact h u hu
    · have h0 : (toAdd (piMul r p (Pi.mulSingle j (ofAdd 1)))) k = 0 := by
        rw [tbjO_toAdd_piMul_mulSingle]
        simp [hkj]
      exact (hk h0).elim

private theorem tbjO_gen_apply_of_mem_orthogonal [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (j : Fin r) {v : V}
    (hv : v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j)) :
    tbjO_gen Δ j v = v :=
  (tbjO_gen_apply_eq_self_iff Δ j v).mpr fun u hu => by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) u hu
    simpa [polarBilin_apply_apply] using h

private theorem tbjO_isCompl_orthogonal (Δ : TBJOmData Q p A r) (j : Fin r) :
    IsCompl (Δ.F.U j) (LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j)) := by
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  have hnd : (LinearMap.BilinForm.restrict (polarBilin Q) (Δ.F.U j)).Nondegenerate := by
    constructor
    · intro x hx
      refine Subtype.ext ?_
      refine Δ.F.nondeg j ↑x x.2 ?_
      intro v hv
      have h := hx ⟨v, hv⟩
      simpa [polarBilin_apply_apply, polar_comm] using h
    · intro y hy
      refine Subtype.ext ?_
      refine Δ.F.nondeg j ↑y y.2 ?_
      intro v hv
      have h := hy ⟨v, hv⟩
      simpa [polarBilin_apply_apply, polar_comm] using h
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd

private theorem tbjO_gen_apply_sub_mem [Fact p.Prime] (Δ : TBJOmData Q p A r) (j : Fin r) (x : V) :
    tbjO_gen Δ j x - x ∈ Δ.F.U j := by
  have hx : x ∈ Δ.F.U j ⊔
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j) := by
    rw [(tbjO_isCompl_orthogonal Δ j).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp hx
  have hwfix : tbjO_gen Δ j w = w := tbjO_gen_apply_of_mem_orthogonal Δ j hw
  rw [← huv, map_add, hwfix, add_sub_add_right_eq_sub]
  exact sub_mem (Δ.F.mapsTo (piMul r p (Pi.mulSingle j (ofAdd 1))) j u hu) hu

private theorem tbjO_exists_quad_ne_zero (Δ : TBJOmData Q p A r) (a : Fin r) :
    ∃ v ∈ Δ.F.U a, Q v ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Δ.F.ne_bot a)
  refine hu0 (Δ.F.nondeg a u hu fun w hw => ?_)
  have h1 : Q (u + w) = 0 := h (u + w) (Submodule.add_mem (Δ.F.U a) hu hw)
  have h2 : Q u = 0 := h u hu
  have h3 : Q w = 0 := h w hw
  rw [QuadraticMap.map_add Q u w, h2, h3, zero_add, zero_add] at h1
  rw [polar_comm Q w u]
  exact h1

private theorem tbjO_iSup_U_eq_top (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) :
    (⨆ j, Δ.F.U j) = ⊤ := by
  classical
  let W : Submodule K V := ⨆ j, Δ.F.U j
  have hWperp : LinearMap.BilinForm.orthogonal (polarBilin Q) W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvfix : ∀ a ∈ A, a v = v := by
      intro a ha
      obtain ⟨s, hs⟩ := Δ.F.exists_eq ha
      rw [← hs, Δ.F.fix]
      intro j _ u hu
      have huW : u ∈ W := Submodule.mem_iSup_of_mem j hu
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) u huW
      simpa [polarBilin_apply_apply] using h
    have hv0 : v = 0 := hnf v hvfix
    simpa [hv0] using Submodule.zero_mem (⊥ : Submodule K V)
  have horth := LinearMap.BilinForm.orthogonal_orthogonal hQ
    (QuadraticMap.isSymm_polarBilin Q).isRefl W
  rw [hWperp] at horth
  simpa using horth.symm

private theorem tbjO_reflection_mul_comm_of_apply_eq
    (hQ : (polarBilin Q).Nondegenerate) {v : V} [Invertible (Q v)] {e : V ≃ₗ[K] V}
    (heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hev : e v = v) :
    TauCeti.QuadraticMap.reflection Q v * e =
      e * TauCeti.QuadraticMap.reflection Q v := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    TauCeti.QuadraticMap.reflection_apply, TauCeti.QuadraticMap.reflection_apply,
    map_sub, map_smul, hev]
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup heO v x
  rw [hev] at h1
  rw [h1]

private theorem tbjO_reflection_mul_gen_of_ne [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q p A r)
    (hA : A ≤ orthDerived Q) {a j : Fin r} (hja : j ≠ a) {v : V} (hv : v ∈ Δ.F.U a)
    [Invertible (Q v)] :
    TauCeti.QuadraticMap.reflection Q v * tbjO_gen Δ j =
      tbjO_gen Δ j * TauCeti.QuadraticMap.reflection Q v := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  refine tbjO_reflection_mul_comm_of_apply_eq hQ
    (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (tbjO_gen_mem Δ hA j)) ?_
  rw [tbjO_gen_apply_eq_self_iff]
  intro u hu
  exact Δ.F.orth j a hja u hu v hv

private theorem tbjO_reflection_conj_gen_self [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {a : Fin r} {v : V} (hv : v ∈ Δ.F.U a) [Invertible (Q v)] :
    TauCeti.QuadraticMap.reflection Q v * tbjO_gen Δ a *
      TauCeti.QuadraticMap.reflection Q v = (tbjO_gen Δ a)⁻¹ := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  set ρ := TauCeti.QuadraticMap.reflection Q v with hρ
  set ea := tbjO_gen Δ a with hea
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have heΩ : ea ∈ orthDerived Q := tbjO_gen_mem Δ hA a
  have heO : ea ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup heΩ
  have heven := (mem_omegaGroup.mp (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ heΩ)).2
  have hle : commSpace (ρ * ea) ≤ Δ.F.U a := by
    intro z hz
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hz
    have h1 : ρ (ea y) - ea y ∈ Δ.F.U a := by
      rw [hρ, TauCeti.QuadraticMap.reflection_apply, sub_sub_cancel_left]
      exact neg_mem (Submodule.smul_mem _ _ hv)
    have h2 : ea y - y ∈ Δ.F.U a := tbjO_gen_apply_sub_mem Δ a y
    have h3 : (ρ * ea) y - y = (ρ (ea y) - ea y) + (ea y - y) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [h3]
    exact add_mem h1 h2
  have hdim2 : finrank K (commSpace (ρ * ea)) ≤ 2 := by
    have h := Submodule.finrank_mono hle
    rwa [Δ.finrank_piece a] at h
  have hpar := natCast_finrank_commSpace_mul hQ hρO heO
  rw [finrank_commSpace_reflection hQ v,
    (ZMod.natCast_eq_zero_iff_even).mpr heven, add_zero, Nat.cast_one] at hpar
  have hodd : ¬ Even (finrank K (commSpace (ρ * ea))) := by
    rw [← ZMod.natCast_eq_zero_iff_even, hpar]
    exact one_ne_zero
  have hle1 : finrank K (commSpace (ρ * ea)) ≤ 1 := by
    rcases Nat.lt_or_ge (finrank K (commSpace (ρ * ea))) 2 with h | h
    · omega
    · exact absurd (show Even 2 from even_two) (by
        rwa [show finrank K (commSpace (ρ * ea)) = 2 by omega] at hodd)
  have hinv := RealKGOmega.mul_self_eq_one_of_finrank_commSpace_le_one hQ
    (mul_mem hρO heO) hle1
  have hρρ : ρ * ρ = 1 := RealKGOmega.mul_self_eq_one_of_finrank_commSpace_le_one hQ hρO
    (by rw [finrank_commSpace_reflection hQ v])
  have h4 : ρ * ea * ρ * ea = 1 := by
    calc ρ * ea * ρ * ea = ρ * ea * (ρ * ea) := by rw [mul_assoc (ρ * ea)]
      _ = 1 := hinv
  exact eq_inv_of_mul_eq_one_left h4

private theorem tbjO_reflection_conj_tau [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {a : Fin r} {v : V} (hv : v ∈ Δ.F.U a) [Invertible (Q v)]
    (f : Fin r → Multiplicative (ZMod p)) :
    TauCeti.QuadraticMap.reflection Q v * Δ.τ f *
      (TauCeti.QuadraticMap.reflection Q v)⁻¹ = Δ.τ (sgnAut a f) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  have hρO : TauCeti.QuadraticMap.reflection Q v ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have hρρ : TauCeti.QuadraticMap.reflection Q v *
      TauCeti.QuadraticMap.reflection Q v = 1 :=
    RealKGOmega.mul_self_eq_one_of_finrank_commSpace_le_one hQ hρO
      (by rw [finrank_commSpace_reflection hQ v])
  have hρinv : (TauCeti.QuadraticMap.reflection Q v)⁻¹ =
      TauCeti.QuadraticMap.reflection Q v :=
    inv_eq_of_mul_eq_one_right hρρ
  refine CFSG.StandardType.OmNsRootGen.conj_eq_of_mulSingle Δ.τ (TauCeti.QuadraticMap.reflection Q v) (sgnAut a)
    (fun d => ?_) f
  by_cases hda : d = a
  · subst hda
    rw [sgnAut_mulSingle_self, map_inv, hρinv, Δ.τ_eq]
    simpa [tbjO_gen] using tbjO_reflection_conj_gen_self hQ Δ hA hv
  · rw [sgnAut_mulSingle_of_ne hda, hρinv, Δ.τ_eq]
    change TauCeti.QuadraticMap.reflection Q v * tbjO_gen Δ d *
      TauCeti.QuadraticMap.reflection Q v = tbjO_gen Δ d
    rw [tbjO_reflection_mul_gen_of_ne hQ Δ hA hda hv, mul_assoc, hρρ, mul_one]

private theorem tbjO_sgnAut_apply_self (a : Fin r)
    (f : Fin r → Multiplicative (ZMod p)) : sgnAut a (sgnAut a f) = f := by
  have h := congrArg (fun u : MulAut (Fin r → Multiplicative (ZMod p)) => u f)
    (sgnAut_sq a)
  simpa [pow_two] using h

private theorem tbjO_pow_conj_eq (u x : V ≃ₗ[K] V) (h : u * x * u⁻¹ = x) (n : ℕ) :
    u ^ n * x * (u ^ n)⁻¹ = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_inv_rev]
    calc (u ^ n * u) * x * (u⁻¹ * (u ^ n)⁻¹)
        = u ^ n * (u * x * u⁻¹) * (u ^ n)⁻¹ := by group
      _ = u ^ n * x * (u ^ n)⁻¹ := by rw [h]
      _ = x := ih

private theorem tbjO_centralizer_reflection [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {a : Fin r} (g : ↥(orthDerived Q))
    (hg : ∀ f, g * Δ.τΩ hA f * g⁻¹ = Δ.τΩ hA (sgnAut a f))
    {v : V} (hv : v ∈ Δ.F.U a) [Invertible (Q v)] :
    ∀ f, ((g : V ≃ₗ[K] V) * TauCeti.QuadraticMap.reflection Q v) * Δ.τ f *
      ((g : V ≃ₗ[K] V) * TauCeti.QuadraticMap.reflection Q v)⁻¹ = Δ.τ f := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  have hge : ∀ f, (g : V ≃ₗ[K] V) * Δ.τ f * (g : V ≃ₗ[K] V)⁻¹ =
      Δ.τ (sgnAut a f) := by
    intro f
    have h := congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[K] V)) (hg f)
    simpa [TBJOmData.τΩ] using h
  intro f
  calc ((g : V ≃ₗ[K] V) * TauCeti.QuadraticMap.reflection Q v) * Δ.τ f *
        ((g : V ≃ₗ[K] V) * TauCeti.QuadraticMap.reflection Q v)⁻¹
      = (g : V ≃ₗ[K] V) * (TauCeti.QuadraticMap.reflection Q v * Δ.τ f *
          (TauCeti.QuadraticMap.reflection Q v)⁻¹) * (g : V ≃ₗ[K] V)⁻¹ := by group
    _ = (g : V ≃ₗ[K] V) * Δ.τ (sgnAut a f) * (g : V ≃ₗ[K] V)⁻¹ := by
          rw [tbjO_reflection_conj_tau hQ Δ hA hv f]
    _ = Δ.τ f := by
          rw [hge (sgnAut a f), tbjO_sgnAut_apply_self a f]

private theorem tbjO_exists_involution_power [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) {h : V ≃ₗ[K] V}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hpar : (finrank K (commSpace h) : ZMod 2) = 1) :
    ∃ (m : ℕ) (t : V ≃ₗ[K] V), 0 < m ∧ t = h ^ m ∧ t * t = 1 ∧ t ≠ 1 ∧
      t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun x : V ≃ₗ[K] V => (x : V → V))
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
  have hcoe : ((H ^ m : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) : V ≃ₗ[K] V) = h ^ m := by
    rw [SubgroupClass.coe_pow]
  refine ⟨m, h ^ m, Nat.pos_of_ne_zero hm0, rfl, ?_, ?_, ?_⟩
  · have := congrArg (fun x : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =>
      (x : V ≃ₗ[K] V)) htt
    simpa [hcoe] using this
  · intro h1
    apply hne
    apply Subtype.ext
    rw [hcoe, h1]
    rfl
  · have := (H ^ m).2
    simpa [hcoe] using this

private theorem tbjO_exists_fixed_involution [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {a : Fin r} (g : ↥(orthDerived Q))
    (hg : ∀ f, g * Δ.τΩ hA f * g⁻¹ = Δ.τΩ hA (sgnAut a f)) :
    ∃ t : V ≃ₗ[K] V, t * t = 1 ∧ t ≠ 1 ∧
      (∀ f, t * Δ.τ f * t⁻¹ = Δ.τ f) ∧
      t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  classical
  obtain ⟨v, hvU, hQv⟩ := tbjO_exists_quad_ne_zero Δ a
  letI : Invertible (Q v) := invertibleOfNonzero hQv
  set ρ := TauCeti.QuadraticMap.reflection Q v with hρ
  have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have hgΩ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ g.2
  obtain ⟨hgO, hgeven⟩ := mem_omegaGroup.mp hgΩ
  set h : V ≃ₗ[K] V := (g : V ≃ₗ[K] V) * ρ with hh
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hgO hρO
  have hcen : ∀ f, h * Δ.τ f * h⁻¹ = Δ.τ f := by
    intro f
    have h1 := tbjO_centralizer_reflection hQ Δ hA g hg hvU f
    simpa [h, hh, hρ] using h1
  have hpar := natCast_finrank_commSpace_mul hQ hgO hρO
  rw [finrank_commSpace_reflection hQ v,
    (ZMod.natCast_eq_zero_iff_even).mpr hgeven, zero_add, Nat.cast_one] at hpar
  obtain ⟨m, t, hm0, ht, htt, htne, htO⟩ :=
    tbjO_exists_involution_power (p := p) hQ hO (by simpa [h] using hpar)
  refine ⟨t, htt, htne, ?_, htO⟩
  intro f
  rw [ht]
  exact tbjO_pow_conj_eq h (Δ.τ f) (hcen f) m

private theorem tbjO_scalar_eq_zero {M : Type} [AddCommGroup M] [Module K M]
    {lam : K} (hlam : lam ≠ lam⁻¹) {v : M} (hv : v ≠ 0) {a : K}
    (h : (a * lam) • v = (a * lam⁻¹) • v) : a = 0 := by
  have hdiff : ((a * lam) - (a * lam⁻¹)) • v = 0 := by
    rw [sub_smul, h, sub_self]
  have hcoef : a * (lam - lam⁻¹) = 0 := by
    simpa [mul_sub] using (smul_eq_zero.mp hdiff).resolve_right hv
  rcases mul_eq_zero.mp hcoef with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hlam

private theorem tbjO_endomorphism_eq_one (Δ : TBJOmData Q p A r)
    {tj : Δ.D →ₗ[K] Δ.D} (hsq : ∀ d, tj (tj d) = d)
    (hc : ∀ d, tj (Δ.c d) = Δ.c (tj d)) : tj = 1 := by
  classical
  by_contra hne
  have hNne : tj - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hN2 : ∀ d, (tj - 1) ((tj - 1) d) = 0 := by
    intro d
    have h1 : tj (tj d) = d := hsq d
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [map_sub, h1]
    have h2 : d - tj d - (tj d - d) = (d - tj d) + (d - tj d) := by abel
    rw [h2]
    calc (d - tj d) + (d - tj d) = (2 : K) • (d - tj d) := (two_smul K _).symm
      _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have hle : LinearMap.range (tj - 1) ≤ LinearMap.ker (tj - 1) := by
    rintro z ⟨d, rfl⟩
    exact hN2 d
  have hdim := LinearMap.finrank_range_add_finrank_ker (tj - 1)
  rw [Δ.finrank_D] at hdim
  have hrank_le : finrank K (LinearMap.range (tj - 1)) ≤
      finrank K (LinearMap.ker (tj - 1)) := Submodule.finrank_mono hle
  have hrange_ne : LinearMap.range (tj - 1) ≠ ⊥ := fun hbot =>
    hNne (LinearMap.range_eq_bot.mp hbot)
  have hrank_pos : 0 < finrank K (LinearMap.range (tj - 1)) := by
    have : Nontrivial (LinearMap.range (tj - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr hrange_ne
    exact Module.finrank_pos
  have hkerdim : finrank K (LinearMap.ker (tj - 1)) = 1 := by omega
  obtain ⟨v, hv0, hvspan⟩ := finrank_eq_one_iff'.mp hkerdim
  have hv0' : (v : Δ.D) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hvker : (tj - 1) (v : Δ.D) = 0 := LinearMap.mem_ker.mp v.2
  have htjv : tj (v : Δ.D) = (v : Δ.D) := by
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hvker
    exact hvker
  have hcvker : Δ.c (v : Δ.D) ∈ LinearMap.ker (tj - 1) := by
    rw [LinearMap.mem_ker]
    have h : (tj - 1) (Δ.c (v : Δ.D)) = Δ.c ((tj - 1) (v : Δ.D)) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hc (v : Δ.D)]
    rw [h, hvker, map_zero]
  obtain ⟨lam, hlam⟩ := hvspan ⟨Δ.c (v : Δ.D), hcvker⟩
  have hcv : Δ.c (v : Δ.D) = lam • (v : Δ.D) := (congrArg Subtype.val hlam).symm
  have hlamne : lam ≠ 1 := fun h1 =>
    hv0' (Δ.c_fix (v : Δ.D) (by rw [hcv, h1, one_smul]))
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hv0'
    apply Δ.c.injective
    rw [hcv, h0, zero_smul, map_zero]
  obtain ⟨T, hT⟩ := Δ.c_twist
  have hT' : T * Δ.c = Δ.c⁻¹ * T := by
    calc T * Δ.c = (T * Δ.c * T⁻¹) * T := by group
      _ = Δ.c⁻¹ * T := by rw [hT]
  have h1 : T (Δ.c (v : Δ.D)) = Δ.c⁻¹ (T (v : Δ.D)) := by
    have := congrArg (fun f : Δ.D ≃ₗ[K] Δ.D => f (v : Δ.D)) hT'
    simpa [LinearEquiv.mul_apply] using this
  have h1' : lam • T (v : Δ.D) = Δ.c⁻¹ (T (v : Δ.D)) := by
    rw [← h1, hcv, map_smul]
  have hcTv : Δ.c (T (v : Δ.D)) = lam⁻¹ • T (v : Δ.D) := by
    have h2 : Δ.c (lam • T (v : Δ.D)) = T (v : Δ.D) := by
      rw [h1']
      exact Δ.c.apply_symm_apply (T (v : Δ.D))
    rw [map_smul] at h2
    calc Δ.c (T (v : Δ.D)) = lam⁻¹ • (lam • Δ.c (T (v : Δ.D))) := by
          rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      _ = lam⁻¹ • T (v : Δ.D) := by rw [h2]
  have hlamlam : lam ≠ lam⁻¹ := by
    intro he
    apply hlamne
    have h2 : lam * lam = 1 := by
      nth_rewrite 2 [he]
      exact mul_inv_cancel₀ hlam0
    have h3 : (lam - 1) * (lam - 1) = 0 := by
      calc (lam - 1) * (lam - 1) = lam * lam - (lam + lam) + 1 := by ring
        _ = lam * lam - 0 + 1 := by rw [CharTwo.add_self_eq_zero]
        _ = 1 + 1 := by rw [h2]; ring
        _ = 0 := CharTwo.add_self_eq_zero 1
    rcases mul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact sub_eq_zero.mp h
  have hTv0 : T (v : Δ.D) ≠ 0 := by
    intro h0
    exact hv0' (T.injective (by rw [h0, map_zero]))
  have hNTv_mem : (tj - 1) (T (v : Δ.D)) ∈ LinearMap.ker (tj - 1) :=
    hle (LinearMap.mem_range_self (tj - 1) (T (v : Δ.D)))
  obtain ⟨μ, hμ⟩ := hvspan ⟨(tj - 1) (T (v : Δ.D)), hNTv_mem⟩
  have hμ' : (tj - 1) (T (v : Δ.D)) = μ • (v : Δ.D) :=
    (congrArg Subtype.val hμ).symm
  have hcN : Δ.c ((tj - 1) (T (v : Δ.D))) = lam⁻¹ • ((tj - 1) (T (v : Δ.D))) := by
    calc Δ.c ((tj - 1) (T (v : Δ.D)))
        = Δ.c (tj (T (v : Δ.D))) - Δ.c (T (v : Δ.D)) := by
          rw [LinearMap.sub_apply, Module.End.one_apply, map_sub]
      _ = tj (Δ.c (T (v : Δ.D))) - Δ.c (T (v : Δ.D)) := by rw [hc (T (v : Δ.D))]
      _ = tj (lam⁻¹ • T (v : Δ.D)) - lam⁻¹ • T (v : Δ.D) := by rw [hcTv]
      _ = lam⁻¹ • tj (T (v : Δ.D)) - lam⁻¹ • T (v : Δ.D) := by rw [map_smul]
      _ = lam⁻¹ • (tj (T (v : Δ.D)) - T (v : Δ.D)) := by rw [smul_sub]
  have hμeq : (μ * lam) • (v : Δ.D) = (μ * lam⁻¹) • (v : Δ.D) := by
    have h1 : Δ.c (μ • (v : Δ.D)) = lam⁻¹ • (μ • (v : Δ.D)) := by
      rw [← hμ']
      exact hcN
    rw [map_smul, hcv, smul_smul, smul_smul] at h1
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1
  have hμ0 : μ = 0 := tbjO_scalar_eq_zero hlamlam hv0' hμeq
  have hNTv : (tj - 1) (T (v : Δ.D)) = 0 := by
    rw [hμ', hμ0, zero_smul]
  have hTv_mem : T (v : Δ.D) ∈ LinearMap.ker (tj - 1) := by
    rw [LinearMap.mem_ker]
    exact hNTv
  obtain ⟨ν, hν⟩ := hvspan ⟨T (v : Δ.D), hTv_mem⟩
  have hν' : T (v : Δ.D) = ν • (v : Δ.D) := (congrArg Subtype.val hν).symm
  have hνeq : (ν * lam) • (v : Δ.D) = (ν * lam⁻¹) • (v : Δ.D) := by
    have h1 : Δ.c (T (v : Δ.D)) = Δ.c (ν • (v : Δ.D)) := by rw [hν']
    rw [hcTv, map_smul, hcv, hν', smul_smul, smul_smul] at h1
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1.symm
  have hν0 : ν = 0 := tbjO_scalar_eq_zero hlamlam hv0' hνeq
  exact hTv0 (by rw [hν', hν0, zero_smul])

private theorem tbjO_mapsTo_orthogonal_of_commute [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (j : Fin r) {u : V ≃ₗ[K] V} (hcomm : u * tbjO_gen Δ j = tbjO_gen Δ j * u)
    {y : V} (hy : y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j)) :
    u y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  have hyfix : tbjO_gen Δ j y = y := tbjO_gen_apply_of_mem_orthogonal Δ j hy
  have hfix : tbjO_gen Δ j (u y) = u y := by
    calc tbjO_gen Δ j (u y) = (tbjO_gen Δ j * u) y := rfl
      _ = (u * tbjO_gen Δ j) y := by rw [← hcomm]
      _ = u (tbjO_gen Δ j y) := rfl
      _ = u y := by rw [hyfix]
  exact (tbjO_gen_apply_eq_self_iff Δ j (u y)).mp hfix

private theorem tbjO_mapsTo_piece [Fact p.Prime]
    (hQ : (polarBilin Q).Nondegenerate) (Δ : TBJOmData Q p A r) {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ j, t * tbjO_gen Δ j = tbjO_gen Δ j * t)
    (j : Fin r) {x : V} (hx : x ∈ Δ.F.U j) : t x ∈ Δ.F.U j := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
  have htinvO : t⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem htO
  have htinvcomm : ∀ j, t⁻¹ * tbjO_gen Δ j = tbjO_gen Δ j * t⁻¹ := by
    intro j
    exact (Commute.inv_left (hcomm j)).eq
  have hfixinv : ∀ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j),
      t⁻¹ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j) := fun y hy =>
    tbjO_mapsTo_orthogonal_of_commute Δ j (htinvcomm j) hy
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ
    (QuadraticMap.isSymm_polarBilin Q).isRefl (Δ.F.U j)]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htO (t⁻¹ y) x
  have h1' : polar Q y (t x) = polar Q (t⁻¹ y) x := by simpa using h1
  change polar Q y (t x) = 0
  rw [h1']
  simpa [polarBilin_apply_apply, polar_comm] using
    (LinearMap.BilinForm.mem_orthogonal_iff.mp (hfixinv y hy)) x hx

private theorem tbjO_eq_self_on_piece [Fact p.Prime] (Δ : TBJOmData Q p A r) (j : Fin r)
    {t : V ≃ₗ[K] V} (htt : t * t = 1)
    (hcomm : t * tbjO_gen Δ j = tbjO_gen Δ j * t)
    (hpres : ∀ x ∈ Δ.F.U j, t x ∈ Δ.F.U j) :
    ∀ x ∈ Δ.F.U j, t x = x := by
  classical
  let θj : Δ.D →ₗ[K] Δ.F.U j :=
    (Δ.θ j).codRestrict (Δ.F.U j) (fun d => by
      rw [← Δ.θ_range j]
      exact LinearMap.mem_range_self _ d)
  have hθj_inj : Function.Injective θj := by
    intro d d' h
    exact Δ.θ_inj j (Subtype.ext_iff.mp h)
  have hθj_surj : Function.Surjective θj := by
    intro u
    obtain ⟨d, hd⟩ := LinearMap.mem_range.mp (by
      rw [Δ.θ_range j]
      exact u.2)
    exact ⟨d, Subtype.ext hd⟩
  let θe : Δ.D ≃ₗ[K] Δ.F.U j := LinearEquiv.ofBijective θj ⟨hθj_inj, hθj_surj⟩
  let tU : Δ.F.U j →ₗ[K] Δ.F.U j :=
    (t : V →ₗ[K] V).restrict (fun x hx => hpres x hx)
  let tj : Δ.D →ₗ[K] Δ.D :=
    θe.symm.toLinearMap.comp (tU.comp θe.toLinearMap)
  have htj_apply : ∀ d, (θe (tj d) : V) = t (θe d : V) := by
    intro d
    simp [tj, tU]
  have htt' : ∀ y, t (t y) = y := by
    intro y
    have := congrArg (fun u : V ≃ₗ[K] V => u y) htt
    simpa [LinearEquiv.mul_apply] using this
  have htj_sq : ∀ d, tj (tj d) = d := by
    intro d
    apply θe.injective
    apply Subtype.ext
    rw [htj_apply (tj d), htj_apply d, htt']
  have hθc : ∀ d, (θe (Δ.c d) : V) = tbjO_gen Δ j (θe d : V) := by
    intro d
    haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    have hval : ((toAdd (piMul r p (Pi.mulSingle j (ofAdd 1)))) j).val = 1 := by
      rw [tbjO_toAdd_piMul_mulSingle, if_pos rfl, toAdd_ofAdd, ZMod.val_one p]
    have hpow : (Δ.c ^ ((toAdd (piMul r p (Pi.mulSingle j (ofAdd 1)))) j).val) = Δ.c := by
      rw [hval, pow_one]
    have h := Δ.θ_act (piMul r p (Pi.mulSingle j (ofAdd 1))) j d
    rw [hpow] at h
    change (θj (Δ.c d) : V) = Δ.F.ι (piMul r p (Pi.mulSingle j (ofAdd 1))) (θj d : V)
    simpa [θj] using h.symm
  have htj_comm : ∀ d, tj (Δ.c d) = Δ.c (tj d) := by
    intro d
    apply θe.injective
    apply Subtype.ext
    rw [htj_apply (Δ.c d), hθc d, hθc (tj d), htj_apply d]
    have h := congrArg (fun u : V ≃ₗ[K] V => u (θe d : V)) hcomm
    simpa [LinearEquiv.mul_apply] using h
  have htj1 : tj = 1 := tbjO_endomorphism_eq_one Δ htj_sq htj_comm
  intro x hx
  obtain ⟨d, hd⟩ := hθj_surj ⟨x, hx⟩
  have hxeq : x = (θe d : V) := (congrArg Subtype.val hd).symm
  rw [hxeq]
  have h2 : (θe (tj d) : V) = t (θe d : V) := htj_apply d
  rw [congrArg (fun u : Δ.D →ₗ[K] Δ.D => u d) htj1] at h2
  exact h2.symm

theorem TBJOmData.not_induces_sgnAut_of_noFixed [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (a : Fin r) (g : ↥(orthDerived Q))
    (hg : ∀ f, g * Δ.τΩ hA f * g⁻¹ = Δ.τΩ hA (sgnAut a f)) : False := by
  classical
  obtain ⟨t, htt, htne, htconj, htO⟩ := tbjO_exists_fixed_involution hQ Δ hA g hg
  have hcomm : ∀ j, t * tbjO_gen Δ j = tbjO_gen Δ j * t := by
    intro j
    have h := htconj (Pi.mulSingle j (ofAdd 1))
    rw [Δ.τ_eq] at h
    have := congrArg (fun x : V ≃ₗ[K] V => x * t) h
    simpa [tbjO_gen, mul_assoc] using this
  have hpres : ∀ j, ∀ x ∈ Δ.F.U j, t x ∈ Δ.F.U j := fun j x hx =>
    tbjO_mapsTo_piece hQ Δ htO hcomm j hx
  have hfix : ∀ j, ∀ x ∈ Δ.F.U j, t x = x := fun j =>
    tbjO_eq_self_on_piece Δ j htt (hcomm j) (hpres j)
  have htop := tbjO_iSup_U_eq_top Δ hQ hnf
  have hle : (⨆ j, Δ.F.U j) ≤ fixedSpace t :=
    iSup_le fun j x hx => mem_fixedSpace.mpr (hfix j x hx)
  have hfixall : fixedSpace t = ⊤ := top_unique (by rwa [htop] at hle)
  have ht1 : t = 1 := by
    refine LinearEquiv.ext fun x => ?_
    have hx : x ∈ fixedSpace t := by rw [hfixall]; exact Submodule.mem_top
    exact mem_fixedSpace.mp hx
  exact htne ht1

end OrthTorus

end CFSG.StandardType

end
