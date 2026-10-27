module
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1AllPairs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport
public import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
public import CFSG.LocalAnalysis.StandardType.GGTBJOmOddSign
public import CFSG.LocalAnalysis.StandardType.GGEvenSignedNormalizer
public import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
public import CFSG.LocalAnalysis.StandardType.GGTBJOmDTwo
public import CFSG.RankThree.PartOne.S11d.OrthModels

public section
namespace CFSG.StandardType

theorem nontrivial_action_of_automizer_reflection
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (r : MulAut ↥Bs) (hr : r ∈ ggAutomizer X Bs) (hrefl : GGIsReflection p r)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨g, hgX, _hgN, hg⟩ := mem_ggAutomizer_iff.mp hr
  have hr1 : r = 1 := by
    ext b
    rw [hg]
    have hb := congrArg Subtype.val (DFunLike.congr_fun (h b) ⟨g, hgX⟩)
    rw [ggGamma_coe] at hb
    change (b : G) * g * (b : G)⁻¹ = g at hb
    have hbg : (b : G) * g = g * (b : G) := (mul_inv_eq_iff_eq_mul).mp hb
    change g * (b : G) * g⁻¹ = (b : G)
    rw [← hbg]
    group
  exact hrefl.ne_one (Fact.out : p.Prime) hr1

namespace OrthTorus
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan Multiplicative

theorem TBJOmData.polarBilin_nondegenerate_of_noFixed
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
    (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) :
    (QuadraticMap.polarBilin Q).Nondegenerate := by
  have hs : (QuadraticMap.polarBilin Q).SeparatingRight := by
    intro v hv
    apply hfix v
    intro a ha
    obtain ⟨s, rfl⟩ := Δ.F.exists_eq ha
    refine (Δ.F.fix s v).mpr fun j _ u _ => ?_
    exact hv u
  refine ⟨?_, hs⟩
  intro v hv
  exact hs v (fun u => by
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hv u)

theorem TBJOmData.finrank_eq_two_mul_of_noFixed
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
    (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) :
    Module.finrank K V = 2 * r := by
  have h := Δ.finrank_fixedSpace hfix (1 : Fin r → Multiplicative (ZMod p))
  rw [Δ.τ.map_one] at h
  have hW : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
      (1 : V ≃ₗ[K] V) = ⊤ := by
    ext v
    rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace]
    change v = v ↔ True
    exact iff_true_intro rfl
  rw [hW] at h
  simpa using h

@[expose] def OrthWeakFrame.toCore
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthWeakFrame p Bs X) : OrthFrameCore p Bs X where
  F := Φ.F
  V := Φ.V
  Q := Φ.Q
  A := Φ.A
  r := Φ.r
  Δ := Φ.Δ
  ψ := Φ.ψ
  β := Φ.β
  hA := Φ.hA
  hr := Φ.hr
  hpq := Φ.hpq
  hfix := Φ.hfix
  hinj := Φ.hinj
  hrange := Φ.hrange
  hβA := Φ.hβA
  hβsurj := Φ.hβsurj
  hcompat := Φ.hcompat
  swapReal := Φ.swapReal
  dinvReal := Φ.dinvReal

theorem OrthFrameCore.aut_eq_iff_torus_action
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (w v : ↥(orthDerived Φ.Q))
    (r s : MulAut ↥Bs) (u t : MulAut (Fin Φ.r → Multiplicative (ZMod p)))
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hs : ∀ b : ↥Bs, ((s b : ↥Bs) : G) = Φ.ψ v * b * (Φ.ψ v)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (u f))
    (hv : ∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (t f)) :
    r = s ↔ u = t := by
  let k : ↥(orthDerived Φ.Q) := v⁻¹ * w
  have hkψ : Φ.ψ k = (Φ.ψ v)⁻¹ * Φ.ψ w := by simp [k]
  constructor
  · intro hrs
    apply MulEquiv.ext
    intro f
    have hτA : Φ.Δ.τ f ∈ Φ.A := by
      exact le_of_eq Φ.Δ.τ_range (MonoidHom.mem_range.mpr ⟨f, rfl⟩)
    obtain ⟨b, hβ⟩ := Φ.hβsurj (Φ.Δ.τ f) hτA
    have hcG : Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹ = Φ.ψ v * (b : G) * (Φ.ψ v)⁻¹ := by
      rw [← hr b, ← hs b, hrs]
    have hkG : Φ.ψ k * (b : G) * (Φ.ψ k)⁻¹ = (b : G) := by
      rw [hkψ]
      calc ((Φ.ψ v)⁻¹ * Φ.ψ w) * (b : G) * ((Φ.ψ v)⁻¹ * Φ.ψ w)⁻¹ =
          (Φ.ψ v)⁻¹ * (Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹) * Φ.ψ v := by group
        _ = (b : G) := by rw [hcG]; group
    have hkβ := (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat k b).mp hkG
    have hkτ : (k : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        (k : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ f := by
      have hkval := congrArg Subtype.val hkβ
      change (k : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) * (k : Φ.V ≃ₗ[Φ.F] Φ.V) at hkval
      rw [hβ] at hkval
      rw [hkval]
      group
    apply Φ.Δ.τ_inj
    calc Φ.Δ.τ (u f) = (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ := (hw f).symm
      _ = (v : Φ.V ≃ₗ[Φ.F] Φ.V) * ((k : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
          (k : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹) * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ := by
        simp only [k, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      _ = (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ := by rw [hkτ]
      _ = Φ.Δ.τ (t f) := hv f
  · intro hut
    apply MulEquiv.ext
    intro b
    have hβA := Φ.hβA b
    rw [← Φ.Δ.τ_range] at hβA
    obtain ⟨f, hf⟩ := hβA
    have hkτ : (k : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        (k : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ f := by
      calc (k : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (k : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
          (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ * ((w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
            (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹) * (v : Φ.V ≃ₗ[Φ.F] Φ.V) := by
            simp only [k, Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ * Φ.Δ.τ (t f) * (v : Φ.V ≃ₗ[Φ.F] Φ.V) := by rw [hw f, hut]
        _ = Φ.Δ.τ f := by rw [← hv f]; group
    have hkβ : k * Φ.β b = Φ.β b * k := by
      apply Subtype.ext
      change (k : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) * (k : Φ.V ≃ₗ[Φ.F] Φ.V)
      rw [← hf]
      exact (mul_inv_eq_iff_eq_mul).mp hkτ
    have hkG := (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat k b).mpr hkβ
    rw [hkψ] at hkG
    apply Subtype.ext
    rw [hr b, hs b]
    calc Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹ =
        Φ.ψ v * (((Φ.ψ v)⁻¹ * Φ.ψ w) * (b : G) * ((Φ.ψ v)⁻¹ * Φ.ψ w)⁻¹) * (Φ.ψ v)⁻¹ := by group
      _ = Φ.ψ v * (b : G) * (Φ.ψ v)⁻¹ := by rw [hkG]
theorem OrthFrameCore.aut_commute_iff_torus_action
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (w v : ↥(orthDerived Φ.Q))
    (r s : MulAut ↥Bs) (u t : MulAut (Fin Φ.r → Multiplicative (ZMod p)))
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hs : ∀ b : ↥Bs, ((s b : ↥Bs) : G) = Φ.ψ v * b * (Φ.ψ v)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (u f))
    (hv : ∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (t f)) :
    r * s = s * r ↔ u * t = t * u := by
  have hprodG : ∀ (w v : ↥(orthDerived Φ.Q)) (r s : MulAut ↥Bs),
      (∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) →
      (∀ b : ↥Bs, ((s b : ↥Bs) : G) = Φ.ψ v * b * (Φ.ψ v)⁻¹) →
      ∀ b : ↥Bs, (((r * s) b : ↥Bs) : G) = Φ.ψ (w * v) * b * (Φ.ψ (w * v))⁻¹ := by
    intro w v r s hr hs b
    change ((r (s b) : ↥Bs) : G) = _
    rw [hr, hs, map_mul]
    group
  have hprodT : ∀ (w v : ↥(orthDerived Φ.Q))
      (u t : MulAut (Fin Φ.r → Multiplicative (ZMod p))),
      (∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (u f)) →
      (∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (t f)) →
      ∀ f, ((w * v : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        ((w * v : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ ((u * t) f) := by
    intro w v u t hw hv f
    change ((w : Φ.V ≃ₗ[Φ.F] Φ.V) * (v : Φ.V ≃ₗ[Φ.F] Φ.V)) * Φ.Δ.τ f *
      ((w : Φ.V ≃ₗ[Φ.F] Φ.V) * (v : Φ.V ≃ₗ[Φ.F] Φ.V))⁻¹ = Φ.Δ.τ (u (t f))
    calc _ = (w : Φ.V ≃ₗ[Φ.F] Φ.V) * ((v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹) * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ := by group
      _ = Φ.Δ.τ (u (t f)) := by rw [hv, hw]
  exact Φ.aut_eq_iff_torus_action (w * v) (v * w) (r * s) (s * r) (u * t) (t * u)
    (hprodG w v r s hr hs) (hprodG v w s r hs hr)
    (hprodT w v u t hw hv) (hprodT v w t u hv hw)
theorem OrthFrameCore.rankOne_eq_map_of_signed_action
    {p : ℕ} {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (w : ↥(orthDerived Φ.Q))
    (r : MulAut ↥Bs) (x : OmPlusIdx Φ.r)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p x f)) :
    ggRankOneIn X Bs r =
      ((if x.2 then Φ.Δ.rankOnePos x.1.1.1 x.1.1.2 else Φ.Δ.rankOne x.1.1.1 x.1.1.2).subgroupOf
        (orthDerived Φ.Q)).map Φ.ψ := by
  have := Φ.finite_linearEquiv
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  cases s
  · have h := ggRankOneIn_eq_map_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj hr
      (fun t => Φ.Δ.mem_reflFixed_iff hw t)
    rw [Φ.hrange] at h
    exact h
  · have hw' : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (NbrOrth.dinv a b (SpCoord.permAut (Equiv.swap a b) f)) := by
      intro f
      simpa only [omPlusRefl, Bool.cond_true, MulAut.mul_apply, SpCoord.sgnAut_apply,
        NbrOrth.dinv, Function.update_apply, if_neg (ne_of_lt hab).symm] using hw f
    have h := ggRankOneIn_eq_map_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj hr
      (fun t => Φ.Δ.mem_reflFixedPos_iff (ne_of_lt hab) hw' t)
    rw [Φ.hrange] at h
    exact h
theorem OrthFrameCore.beta_mem_fixedTorus_of_hyperplane
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (w : ↥(orthDerived Φ.Q))
    (r : MulAut ↥Bs) (x : OmPlusIdx Φ.r)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p x f))
    (b : ↥Bs) (hb : (b : G) ∈ ggHyperplane Bs r) :
    (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) ∈
      (if x.2 then Φ.Δ.reflFixedPos x.1.1.1 x.1.1.2
        else Φ.Δ.reflFixed x.1.1.1 x.1.1.2) := by
  obtain ⟨b', hb', hc⟩ :=
    (mem_ggHyperplane_iff_comm Φ.ψ Φ.β Φ.hinj Φ.hcompat hr (b : G)).mp hb
  have hbb : b' = b := Subtype.ext hb'
  subst b'
  have hc' := congrArg Subtype.val hc
  rcases x with ⟨⟨⟨a, c⟩, hac⟩, s⟩
  cases s
  · exact (Φ.Δ.mem_reflFixed_iff hw _).mpr ⟨Φ.hβA b, hc'⟩
  · have hw' : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (NbrOrth.dinv a c (SpCoord.permAut (Equiv.swap a c) f)) := by
      intro f
      simpa only [omPlusRefl, Bool.cond_true, MulAut.mul_apply, SpCoord.sgnAut_apply,
        NbrOrth.dinv, Function.update_apply, if_neg (ne_of_lt hac).symm] using hw f
    exact (Φ.Δ.mem_reflFixedPos_iff (ne_of_lt hac) hw' _).mpr ⟨Φ.hβA b, hc'⟩

theorem OrthFrameCore.exists_unitaryPair_of_signed_actions
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (hp2 : p ≠ 2)
    (w v : ↥(orthDerived Φ.Q)) (r s : MulAut ↥Bs) (x y : OmPlusIdx Φ.r)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hs : ∀ b : ↥Bs, ((s b : ↥Bs) : G) = Φ.ψ v * b * (Φ.ψ v)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p x f))
    (hv : ∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p y f))
    (hcomm : r * s ≠ s * r) :
    ∃ W : Subgroup G,
      W ≤ X ⊓ Subgroup.centralizer ((ggHyperplane Bs r ⊓ ggHyperplane Bs s : Subgroup G) :
        Set G) ∧
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ),
        Nat.card F = (2 ^ f) ^ 2 →
        Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
        UnitaryBlockStandardPair F 2 f W (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  let U : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
    if x.2 then Φ.Δ.rankOnePos x.1.1.1 x.1.1.2 else Φ.Δ.rankOne x.1.1.1 x.1.1.2
  let V : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
    if y.2 then Φ.Δ.rankOnePos y.1.1.1 y.1.1.2 else Φ.Δ.rankOne y.1.1.1 y.1.1.2
  have hUeq : ggRankOneIn X Bs r = (U.subgroupOf (orthDerived Φ.Q)).map Φ.ψ :=
    Φ.rankOne_eq_map_of_signed_action w r x hr hw
  have hVeq : ggRankOneIn X Bs s = (V.subgroupOf (orthDerived Φ.Q)).map Φ.ψ :=
    Φ.rankOne_eq_map_of_signed_action v s y hs hv
  have hcomm' := Φ.aut_commute_iff_torus_action w v r s
    (omPlusRefl p x) (omPlusRefl p y) hr hs hw hv
  let : Fintype Φ.F := Fintype.ofFinite Φ.F
  obtain ⟨n, _, hn⟩ := FiniteField.card Φ.F 2
  have hn' : Nat.card Φ.F = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  obtain ⟨W, hW, hpair⟩ := Φ.Δ.pair_signed_rankOne_forall_fields hp2 Φ.hA
    (by have := Φ.hr; omega) Φ.hpq Φ.hfix (n : ℕ) hn' x y (fun h => hcomm (hcomm'.mpr h))
  refine ⟨(W.subgroupOf (orthDerived Φ.Q)).map Φ.ψ, ?_, ?_⟩
  · apply le_inf
    · rintro _ ⟨a, _ha, rfl⟩
      exact le_of_eq Φ.hrange (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
    · rintro _ ⟨a, ha, rfl⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro b hb
      obtain ⟨b', hb', _⟩ :=
        (mem_ggHyperplane_iff_comm Φ.ψ Φ.β Φ.hinj Φ.hcompat hr b).mp hb.1
      have hb₀ : (b' : G) ∈ ggHyperplane Bs r := hb'.symm ▸ hb.1
      have hb₁ : (b' : G) ∈ ggHyperplane Bs s := hb'.symm ▸ hb.2
      have hβ₀ := Φ.beta_mem_fixedTorus_of_hyperplane w r x hr hw b' hb₀
      have hβ₁ := Φ.beta_mem_fixedTorus_of_hyperplane v s y hs hv b' hb₁
      have hc := (Subgroup.mem_centralizer_iff.mp (hW ha).2)
        (Φ.β b' : Φ.V ≃ₗ[Φ.F] Φ.V) ⟨hβ₀, hβ₁⟩
      have hc' : Φ.β b' * a = a * Φ.β b' := Subtype.ext hc
      have heq : Φ.β b' * a * (Φ.β b')⁻¹ = a := by rw [hc']; group
      have hcompat := Φ.hcompat b' a
      rw [heq] at hcompat
      rw [← hb']
      exact (mul_inv_eq_iff_eq_mul).mp hcompat.symm
  · intro F _ _ _ f hF horder
    have hUΩ : U ≤ orthDerived Φ.Q := by
      dsimp only [U]
      cases x.2
      · exact Φ.Δ.rankOne_le _ _
      · exact Φ.Δ.rankOnePos_le _ _
    have hcardU : Nat.card ↥U = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [hUeq, Subgroup.card_map_of_injective Φ.hinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUΩ).toEquiv] at horder
      exact horder
    have hpair' := hpair F f hF hcardU
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hrestrict := unitaryBlockStandardPair_restrict hpair' (orthDerived Φ.Q)
      (hW.trans inf_le_left)
    have hmap := CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hrestrict Φ.ψ Φ.hinj
    rwa [← hUeq, ← hVeq] at hmap

theorem OrthFrameCore.pair_of_signed_actions
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (hp2 : p ≠ 2)
    (w v : ↥(orthDerived Φ.Q)) (r s : MulAut ↥Bs) (x y : OmPlusIdx Φ.r)
    (hrs : r ≠ s)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hs : ∀ b : ↥Bs, ((s b : ↥Bs) : G) = Φ.ψ v * b * (Φ.ψ v)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p x f))
    (hv : ∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p y f)) :
    GGPairConcl Bs X r s := by
  let U : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
    if x.2 then Φ.Δ.rankOnePos x.1.1.1 x.1.1.2 else Φ.Δ.rankOne x.1.1.1 x.1.1.2
  let V : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
    if y.2 then Φ.Δ.rankOnePos y.1.1.1 y.1.1.2 else Φ.Δ.rankOne y.1.1.1 y.1.1.2
  have hUeq : ggRankOneIn X Bs r = (U.subgroupOf (orthDerived Φ.Q)).map Φ.ψ :=
    Φ.rankOne_eq_map_of_signed_action w r x hr hw
  have hVeq : ggRankOneIn X Bs s = (V.subgroupOf (orthDerived Φ.Q)).map Φ.ψ :=
    Φ.rankOne_eq_map_of_signed_action v s y hs hv
  have hxy : x ≠ y := by
    intro h
    apply hrs
    exact (Φ.aut_eq_iff_torus_action w v r s (omPlusRefl p x) (omPlusRefl p y) hr hs hw hv).mpr
      (congrArg (omPlusRefl p) h)
  have hcomm := Φ.aut_commute_iff_torus_action w v r s
    (omPlusRefl p x) (omPlusRefl p y) hr hs hw hv
  constructor
  · intro hc a ha b hb
    have hmodel := Φ.Δ.commute_signed_rankOne_of_refl_commute hp2 Φ.hA Φ.hfix x y hxy
      (hcomm.mp hc)
    rw [hUeq] at ha
    rw [hVeq] at hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hab : a' * b' = b' * a' := Subtype.ext (hmodel a' ha' b' hb')
    simpa only [map_mul] using congrArg Φ.ψ hab
  · intro hc F _ _ _ f hF horder
    obtain ⟨W, _, hpair⟩ :=
      Φ.exists_unitaryPair_of_signed_actions hp2 w v r s x y hr hs hw hv hc
    exact ⟨W, hpair F f hF horder⟩
theorem OrthFrameCore.beta_equivariant_of_inner
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (hZ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥)
    (w : ↥(orthDerived Φ.Q)) (r : MulAut ↥Bs)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) :
    ∀ b : ↥Bs, Φ.β (r b) = w * Φ.β b * w⁻¹ := by
  have hconj_inj : Function.Injective (MulAut.conj : ↥(orthDerived Φ.Q) →* MulAut ↥(orthDerived Φ.Q)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro z hz
    have hz' : MulAut.conj z = 1 := hz
    have hzc : z ∈ Subgroup.center ↥(orthDerived Φ.Q) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      have h := DFunLike.congr_fun hz' y
      change z * y * z⁻¹ = y at h
      exact ((mul_inv_eq_iff_eq_mul).mp h).symm
    rwa [hZ] at hzc
  intro b
  apply hconj_inj
  apply MulEquiv.ext
  intro y
  apply Φ.hinj
  change Φ.ψ (Φ.β (r b) * y * (Φ.β (r b))⁻¹) =
    Φ.ψ ((w * Φ.β b * w⁻¹) * y * (w * Φ.β b * w⁻¹)⁻¹)
  calc _ = ((r b : ↥Bs) : G) * Φ.ψ y * ((r b : ↥Bs) : G)⁻¹ := Φ.hcompat (r b) y
    _ = Φ.ψ w * ((b : G) * Φ.ψ (w⁻¹ * y * w) * (b : G)⁻¹) * (Φ.ψ w)⁻¹ := by
      rw [hr b]
      simp only [map_mul, map_inv]
      group
    _ = Φ.ψ (w * (Φ.β b * (w⁻¹ * y * w) * (Φ.β b)⁻¹) * w⁻¹) := by
      rw [← Φ.hcompat b]
      simp only [map_mul, map_inv]
    _ = Φ.ψ ((w * Φ.β b * w⁻¹) * y * (w * Φ.β b * w⁻¹)⁻¹) := by
      exact congrArg Φ.ψ (by group)

theorem OrthFrameCore.isReflection_of_original_action
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (w : ↥(orthDerived Φ.Q))
    (r : MulAut ↥Bs) (u : MulAut (Fin Φ.r → Multiplicative (ZMod p)))
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (u f))
    (hrefl : GGIsReflection p r) : u ^ 2 = 1 ∧
      Nat.card {f : Fin Φ.r → Multiplicative (ZMod p) // u f = f} * p =
        Nat.card (Fin Φ.r → Multiplicative (ZMod p)) := by
  have := Φ.finite_linearEquiv
  let β' : ↥Bs →* (Φ.V ≃ₗ[Φ.F] Φ.V) := (orthDerived Φ.Q).subtype.comp Φ.β
  let C : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) := Subgroup.centralizer ({(w : Φ.V ≃ₗ[Φ.F] Φ.V)} : Set _)
  let S : Subgroup ↥Bs := C.comap β'
  let H : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) := C ⊓ Φ.A
  let T : Subgroup (Fin Φ.r → Multiplicative (ZMod p)) :=
    (u.toMonoidHom / MonoidHom.id _).ker
  have hfix : ∀ b : ↥Bs, r b = b ↔ b ∈ S := by
    intro b
    change r b = b ↔ (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ C
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat w b).mp (by rw [← hr b, h])
      exact (congrArg Subtype.val h').symm
    · intro h
      apply Subtype.ext
      rw [hr]
      apply (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat w b).mpr
      exact Subtype.ext h.symm
  have hfixCard : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥S :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  have hSidx : S.index = p := by
    have h := hrefl.2
    rw [hfixCard] at h
    exact mul_left_cancel₀ (Nat.card_pos (α := ↥S)).ne' (by rw [Subgroup.card_mul_index S, h])
  have hβrange : β'.range = Φ.A := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩; exact Φ.hβA b
    · intro ha; obtain ⟨b, hb⟩ := Φ.hβsurj a ha; exact ⟨b, hb⟩
  have hidx : C.relIndex Φ.A = p := by
    have h := Subgroup.index_comap C β'
    rw [hβrange] at h
    exact h.symm.trans hSidx
  have hcardH : Nat.card ↥H * p = Nat.card ↥Φ.A := by
    simpa only [H, hidx, mul_comm] using Subgroup.relIndex_mul_card C Φ.A
  have hT : ∀ f, f ∈ T ↔ u f = f := by
    intro f
    change u f / f = 1 ↔ _
    exact div_eq_one
  have hH : ∀ f, Φ.Δ.τ f ∈ H ↔ u f = f := by
    intro f
    have hA : Φ.Δ.τ f ∈ Φ.A := le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩
    change Φ.Δ.τ f ∈ C ∧ Φ.Δ.τ f ∈ Φ.A ↔ _
    rw [and_iff_left hA, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      apply Φ.Δ.τ_inj
      rw [← hw, hc.symm]
      group
    · intro hf
      have h := hw f
      rw [hf] at h
      exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  have heq : Nat.card ↥T = Nat.card ↥H := by
    let θ : ↥T →* ↥H := (Φ.Δ.τ.comp T.subtype).codRestrict H (fun f => (hH f).mpr ((hT f).mp f.2))
    refine Nat.card_congr (MulEquiv.ofBijective θ ?_).toEquiv
    constructor
    · intro f g h; exact Subtype.ext (Φ.Δ.τ_inj (congrArg Subtype.val h))
    · intro a
      have ha := a.2.2
      rw [← Φ.Δ.τ_range] at ha
      obtain ⟨f, hf⟩ := ha
      have hfT : f ∈ T := (hT f).mpr ((hH f).mp (hf.symm ▸ a.2))
      exact ⟨⟨f, hfT⟩, Subtype.ext hf⟩
  have hcardT : Nat.card {f : Fin Φ.r → Multiplicative (ZMod p) // u f = f} * p =
      Nat.card (Fin Φ.r → Multiplicative (ZMod p)) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => (hT f).symm)), heq, hcardH]
    exact Nat.card_congr (MulEquiv.ofBijective (Φ.Δ.τ.codRestrict Φ.A (fun f => le_of_eq Φ.Δ.τ_range ⟨f,rfl⟩))
      ⟨fun f g h => Φ.Δ.τ_inj (congrArg Subtype.val h), fun a => by
        have ha : (a : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.Δ.τ.range :=
          le_of_eq Φ.Δ.τ_range.symm a.2
        obtain ⟨f,hf⟩ := ha
        exact ⟨f,Subtype.ext hf⟩⟩).toEquiv.symm
  have hr2 : ∀ b : ↥Bs, (((r * r) b : ↥Bs) : G) = Φ.ψ (w * w) * b * (Φ.ψ (w * w))⁻¹ := by
    intro b
    change ((r (r b) : ↥Bs) : G) = _
    rw [hr, hr, map_mul]
    group
  have hw2 : ∀ f, ((w * w : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
      ((w * w : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ ((u * u) f) := by
    intro f
    have h := hw (u f)
    rw [← hw f] at h
    simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, MulAut.mul_apply] using h
  have hu2 := (Φ.aut_eq_iff_torus_action (w*w) 1 (r*r) 1 (u*u) 1 hr2
    (by intro b; simp) hw2 (by intro f; simp)).mp (by simpa only [pow_two] using hrefl.1)
  change u ^ 2 = 1 ∧ Nat.card {f : Fin Φ.r → Multiplicative (ZMod p) // u f = f} * p = _
  exact ⟨by simpa only [pow_two] using hu2, hcardT⟩
theorem OrthFrameCore.exists_torus_action_of_inner
    {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (hZ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥)
    (w : ↥(orthDerived Φ.Q)) (r : MulAut ↥Bs)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) :
    ∃ u : MulAut (Fin Φ.r → Multiplicative (ZMod p)),
      ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (u f) := by
  classical
  have := Φ.finite_linearEquiv
  have hAconj : ∀ a ∈ Φ.A, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * a *
      (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ ∈ Φ.A := by
    intro a ha
    obtain ⟨b, hb⟩ := Φ.hβsurj a ha
    have heq := congrArg Subtype.val (Φ.beta_equivariant_of_inner hZ w r hr b)
    change (Φ.β (r b) : Φ.V ≃ₗ[Φ.F] Φ.V) =
      (w : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) *
        (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ at heq
    rw [hb] at heq
    rw [← heq]
    exact Φ.hβA (r b)
  let θ : (Fin Φ.r → Multiplicative (ZMod p)) ≃* ↥Φ.A :=
    MulEquiv.ofBijective (Φ.Δ.τ.codRestrict Φ.A (fun f => Φ.Δ.τ_range.le ⟨f, rfl⟩))
      ⟨fun f g h => Φ.Δ.τ_inj (congrArg Subtype.val h), fun a => by
        have ha : (a : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.Δ.τ.range := Φ.Δ.τ_range.symm.le a.2
        obtain ⟨f, hf⟩ := ha
        exact ⟨f, Subtype.ext hf⟩⟩
  let c : ↥Φ.A →* ↥Φ.A :=
    ((MulAut.conj (w : Φ.V ≃ₗ[Φ.F] Φ.V)).toMonoidHom.comp Φ.A.subtype).codRestrict
      Φ.A (fun a => hAconj a a.2)
  have hc : Function.Injective c := by
    intro a b h
    apply Subtype.ext
    apply (MulAut.conj (w : Φ.V ≃ₗ[Φ.F] Φ.V)).injective
    exact congrArg Subtype.val h
  let e : MulAut ↥Φ.A := MulEquiv.ofBijective c ⟨hc, Finite.surjective_of_injective hc⟩
  let u : MulAut (Fin Φ.r → Multiplicative (ZMod p)) := θ.trans (e.trans θ.symm)
  refine ⟨u, fun f => ?_⟩
  have h : θ (u f) = c (θ f) := by
    simp only [u, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have h' := congrArg Subtype.val h
  exact h'.symm

theorem OrthFrameCore.exists_signed_action_of_inner
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Φ.Q).Nondegenerate)
    (hZ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥)
    (w : ↥(orthDerived Φ.Q)) (r : MulAut ↥Bs)
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (hrefl : GGIsReflection p r) :
    ∃ x : OmPlusIdx Φ.r, ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
      (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (omPlusRefl p x f) := by
  classical
  obtain ⟨u, hu⟩ := Φ.exists_torus_action_of_inner hZ w r hr
  have huΩ : ∀ f, w * Φ.Δ.τΩ Φ.hA f * w⁻¹ = Φ.Δ.τΩ Φ.hA (u f) := by
    intro f
    exact Subtype.ext (hu f)
  have hs := tbjA_isSignedPerm_of_induced Φ.Δ Φ.hA (J := ⊤) ⟨w, Subgroup.mem_top _, huΩ⟩
  have href := CFSG.StandardType.OrthExcEven.isRefl_of_fixed_card u
    (Φ.isReflection_of_original_action w r u hr hu hrefl)
  rcases CFSG.StandardType.OrthExcEven.shape_of_refl (Fact.out : p.Prime) hp2 hs href with
    ⟨a, ha⟩ | ⟨a, b, hab, t, ht, hut⟩
  · exfalso
    apply Φ.Δ.not_induces_sgnAut_of_noFixed hp2 hQ Φ.hA Φ.hfix a w
    simpa only [ha] using huΩ
  · have hswap : (SpCoord.sgnAut a * SpCoord.sgnAut b *
        SpCoord.permAut (Equiv.swap a b) : MulAut (Fin Φ.r → Multiplicative (ZMod p))) =
        SpCoord.sgnAut b * SpCoord.sgnAut a * SpCoord.permAut (Equiv.swap b a) := by
      rw [CFSG.StandardType.OrthExcEven.sgnAut_mul_sgnAut_diag hab,
        CFSG.StandardType.OrthExcEven.sgnAut_mul_sgnAut_diag hab.symm, Equiv.swap_comm]
      congr 2
      funext i
      simp only [or_comm]
    rcases lt_or_gt_of_ne hab with hab | hba
    · rcases ht with rfl | rfl
      · refine ⟨⟨⟨⟨a, b⟩, hab⟩, false⟩, ?_⟩
        simpa only [hut, CFSG.StandardType.OrthExcEven.reflAut_one,
          CFSG.StandardType.OrthExcEven.transp, omPlusRefl_false] using hu
      · refine ⟨⟨⟨⟨a, b⟩, hab⟩, true⟩, ?_⟩
        simpa only [hut, CFSG.StandardType.OrthExcEven.reflAut_neg_one (ne_of_lt hab),
          CFSG.StandardType.OrthExcEven.sgnTransp, omPlusRefl_true] using hu
    · rcases ht with rfl | rfl
      · refine ⟨⟨⟨⟨b, a⟩, hba⟩, false⟩, ?_⟩
        simpa only [hut, CFSG.StandardType.OrthExcEven.reflAut_one,
          CFSG.StandardType.OrthExcEven.transp, omPlusRefl_false, Equiv.swap_comm] using hu
      · refine ⟨⟨⟨⟨b, a⟩, hba⟩, true⟩, ?_⟩
        simpa only [hut, CFSG.StandardType.OrthExcEven.reflAut_neg_one hab,
          CFSG.StandardType.OrthExcEven.sgnTransp, omPlusRefl_true, hswap] using hu

theorem OrthFrameCore.pair_of_reflections
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (hp2 : p ≠ 2)
    (r s : MulAut ↥Bs) (hr : r ∈ ggAutomizer X Bs) (hs : s ∈ ggAutomizer X Bs)
    (hrefl : GGIsReflection p r) (hsrefl : GGIsReflection p s) (hrs : r ≠ s) :
    GGPairConcl Bs X r s := by
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨g, hgX, _hgN, hgr⟩ := mem_ggAutomizer_iff.mp hr
  obtain ⟨h, hhX, _hhN, hhs⟩ := mem_ggAutomizer_iff.mp hs
  have hg : g ∈ Φ.ψ.range := by rwa [Φ.hrange]
  have hh : h ∈ Φ.ψ.range := by rwa [Φ.hrange]
  obtain ⟨w, hw⟩ := hg
  obtain ⟨v, hv⟩ := hh
  have hwr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹ := by
    intro b
    rw [hw]
    exact hgr b
  have hvs : ∀ b : ↥Bs, ((s b : ↥Bs) : G) = Φ.ψ v * b * (Φ.ψ v)⁻¹ := by
    intro b
    rw [hv]
    exact hhs b
  obtain ⟨x, hx⟩ := Φ.exists_signed_action_of_inner hp2 hQ hZ w r hwr hrefl
  obtain ⟨y, hy⟩ := Φ.exists_signed_action_of_inner hp2 hQ hZ v s hvs hsrefl
  exact Φ.pair_of_signed_actions hp2 w v r s x y hrs hwr hvs hx hy

end OrthTorus
end CFSG.StandardType
end
