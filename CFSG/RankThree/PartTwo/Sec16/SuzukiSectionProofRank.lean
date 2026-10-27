module

public import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
import CFSG.RankThree.PartTwo.Sec16.Item16Tail23
import CFSG.RankThree.Coprime.InvolutionFixedRankBound

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Subgroup CFSG.RankThree.PartTwo.Sec3
open scoped commutatorElement IsMulCommutative

section LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem three_le_finrank_of_cyclic (h2 : (2 : K) ≠ 0) {σ₁ σ₂ τ : Module.End K V}
    (h11 : σ₁ * σ₁ = 1) (h22 : σ₂ * σ₂ = 1) (h12 : σ₁ * σ₂ = σ₂ * σ₁)
    (hτ₁ : σ₁ * τ = τ * σ₂) (hτ₂ : σ₂ * τ = τ * (σ₁ * σ₂)) (hτ : Function.Injective τ)
    (hσ₁ : σ₁ ≠ 1) : 3 ≤ Module.finrank K V := by
  have app : ∀ (f g h : Module.End K V), f * g = h → ∀ v, f (g v) = h v := fun f g h e v => by
    rw [← e, Module.End.mul_apply]
  have e11 : ∀ v, σ₁ (σ₁ v) = v := fun v => by rw [app _ _ _ h11, Module.End.one_apply]
  have e22 : ∀ v, σ₂ (σ₂ v) = v := fun v => by rw [app _ _ _ h22, Module.End.one_apply]
  have e12 : ∀ v, σ₁ (σ₂ v) = σ₂ (σ₁ v) := fun v => by rw [app _ _ _ h12, Module.End.mul_apply]
  have eτ₁ : ∀ v, σ₁ (τ v) = τ (σ₂ v) := fun v => by rw [app _ _ _ hτ₁, Module.End.mul_apply]
  have eτ₂ : ∀ v, σ₂ (τ v) = τ (σ₁ (σ₂ v)) := fun v => by
    rw [app _ _ _ hτ₂, Module.End.mul_apply, Module.End.mul_apply]
  have hneg : ∀ (f : Module.End K V) (v : V), f v = v → f v = -v → v = 0 := fun f v h1 h2' => by
    have hv : v = -v := h1.symm.trans h2'
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hv]
      exact add_neg_cancel v
    exact (smul_eq_zero.mp h2v).resolve_left h2
  set W₁ := σ₁.eigenspace 1 ⊓ σ₂.eigenspace (-1) with hW₁
  set W₂ := σ₁.eigenspace (-1) ⊓ σ₂.eigenspace 1 with hW₂
  set W₃ := σ₁.eigenspace (-1) ⊓ σ₂.eigenspace (-1) with hW₃
  have mem : ∀ (s t : K) (v : V), v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t ↔
      σ₁ v = s • v ∧ σ₂ v = t • v := fun s t v => by
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  have mem₁ : ∀ v, v ∈ W₁ ↔ σ₁ v = v ∧ σ₂ v = -v := fun v => by
    rw [hW₁, mem, one_smul, neg_one_smul]
  have mem₂ : ∀ v, v ∈ W₂ ↔ σ₁ v = -v ∧ σ₂ v = v := fun v => by
    rw [hW₂, mem, one_smul, neg_one_smul]
  have mem₃ : ∀ v, v ∈ W₃ ↔ σ₁ v = -v ∧ σ₂ v = -v := fun v => by
    rw [hW₃, mem, neg_one_smul]
  have hτ13 : ∀ v ∈ W₁, τ v ∈ W₃ := fun v hv => by
    rw [mem₁] at hv
    rw [mem₃]
    exact ⟨by rw [eτ₁, hv.2, map_neg], by rw [eτ₂, hv.2, map_neg, hv.1, map_neg]⟩
  have hτ32 : ∀ v ∈ W₃, τ v ∈ W₂ := fun v hv => by
    rw [mem₃] at hv
    rw [mem₂]
    exact ⟨by rw [eτ₁, hv.2, map_neg], by rw [eτ₂, hv.2, map_neg, hv.1, neg_neg]⟩
  have hτ21 : ∀ v ∈ W₂, τ v ∈ W₁ := fun v hv => by
    rw [mem₂] at hv
    rw [mem₁]
    exact ⟨by rw [eτ₁, hv.2], by rw [eτ₂, hv.2, hv.1, map_neg]⟩
  have hle : ∀ {W W' : Submodule K V}, (∀ v ∈ W, τ v ∈ W') →
      Module.finrank K W ≤ Module.finrank K W' := fun {W W'} h =>
    LinearMap.finrank_le_finrank_of_injective (f := τ.restrict h)
      (fun x y hxy => Subtype.ext (hτ (congrArg Subtype.val hxy)))
  have hk13 := hle hτ13
  have hk32 := hle hτ32
  have hk21 := hle hτ21
  have hinf₂₃ : W₂ ⊓ W₃ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hneg σ₂ v ((mem₂ v).mp hv.1).2 ((mem₃ v).mp hv.2).2
  have hinf₁ : W₁ ⊓ (W₂ ⊔ W₃) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hsup : W₂ ⊔ W₃ ≤ σ₁.eigenspace (-1) := sup_le inf_le_left inf_le_left
    have h3 := hsup hv.2
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at h3
    exact hneg σ₁ v ((mem₁ v).mp hv.1).1 h3
  have hsum : Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) =
      Module.finrank K W₁ + (Module.finrank K W₂ + Module.finrank K W₃) := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq W₁ (W₂ ⊔ W₃)
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq W₂ W₃
    rw [hinf₁, finrank_bot, add_zero] at e1
    rw [hinf₂₃, finrank_bot, add_zero] at e2
    rw [e1, e2]
  have hVle : Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) ≤ Module.finrank K V := Submodule.finrank_le _
  obtain ⟨v, hv⟩ : ∃ v, σ₁ v ≠ v := by
    by_contra h
    push Not at h
    exact hσ₁ (LinearMap.ext fun v => by rw [h v, Module.End.one_apply])
  set u := v - σ₁ v with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hσu : σ₁ u = -u := by rw [hu, map_sub, e11, neg_sub]
  have hup : u + σ₂ u ∈ W₂ := by
    rw [mem₂]
    refine ⟨?_, ?_⟩
    · rw [map_add, e12, hσu, map_neg, neg_add]
    · rw [map_add, e22, add_comm]
  have hum : u - σ₂ u ∈ W₃ := by
    rw [mem₃]
    refine ⟨?_, ?_⟩
    · rw [map_sub, e12, hσu, map_neg]
      abel
    · rw [map_sub, e22, neg_sub]
  have hk1 : 1 ≤ Module.finrank K W₂ ∨ 1 ≤ Module.finrank K W₃ := by
    by_contra hcon
    push Not at hcon
    have h2' : Module.finrank K W₂ = 0 := by omega
    have h3' : Module.finrank K W₃ = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h2' h3'
    have a1 : u + σ₂ u = 0 := by
      have := hup
      rw [h2'] at this
      exact (Submodule.mem_bot K).mp this
    have a2 : u - σ₂ u = 0 := by
      have := hum
      rw [h3'] at this
      exact (Submodule.mem_bot K).mp this
    have h2u : (2 : K) • u = 0 := by
      rw [two_smul]
      calc u + u = (u + σ₂ u) + (u - σ₂ u) := by abel
        _ = 0 := by rw [a1, a2, add_zero]
    exact hu0 ((smul_eq_zero.mp h2u).resolve_left h2)
  omega

end LinearAlgebra

section Groups

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_of_le {p : ℕ} (hp : 1 < p) {D P : Subgroup G} (hDP : D ≤ P)
    (H : Subgroup D) : CFSG.pRank p H ≤ CFSG.Open.pRank p P := by
  let f : H →* G := D.subtype.comp H.subtype
  have hf : Function.Injective f := fun a b hab => Subtype.ext (Subtype.ext hab)
  have hmap : (⊤ : Subgroup H).map f ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact hDP (y : D).2
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact (CFSG.SectionRank.pRank_le_map hp f hf ⊤).trans (CFSG.SectionRank.pRank_mono hp hmap)

theorem false_of_kleinFour_cyclic {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {D P : Subgroup G}
    (hD : IsPGroup p D) (hDP : D ≤ P) (hPrank : CFSG.Open.pRank p P ≤ 2)
    (hDexp : ∀ d ∈ D, d ^ p = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    {u c : G} (huD : u ∈ normalizer (D : Set G)) (hcD : c ∈ normalizer (D : Set G))
    (hu2 : u * u = 1) (huC : u ∉ centralizer (D : Set G))
    (hv2 : (c⁻¹ * u * c) * (c⁻¹ * u * c) = 1) (huv : u * (c⁻¹ * u * c) = c⁻¹ * u * c * u)
    (hcv : c⁻¹ * (c⁻¹ * u * c) * c = u * (c⁻¹ * u * c)) : False := by
  classical
  have hp' : p.Prime := hp.out
  have hexp : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hclass : commutator D ≤ Subgroup.center D := commutator_le_center_of_forall hDcl
  obtain ⟨hchar, hVcomm, -, hVelem, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hD
  have : Finite (Additive (D ⧸ frattini D)) := inferInstanceAs (Finite (D ⧸ frattini D))
  have : FiniteDimensional (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  let E : MulAut (D ⧸ frattini D) →* Module.End (ZMod p) (Additive (D ⧸ frattini D)) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hE : ∀ (σ : MulAut (D ⧸ frattini D)) (q : D ⧸ frattini D),
      E σ (Additive.ofMul q) = Additive.ofMul (σ q) := fun _ _ => rfl
  let q := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D)
  let ψ : normalizer (D : Set G) →* Module.End (ZMod p) (Additive (D ⧸ frattini D)) :=
    E.comp (q.comp D.normalizerMonoidHom)
  have hψmul : ∀ x y : normalizer (D : Set G), ψ x * ψ y = ψ (x * y) := fun x y =>
    (map_mul ψ x y).symm
  have hvD : c⁻¹ * u * c ∈ normalizer (D : Set G) :=
    mul_mem (mul_mem (inv_mem hcD) huD) hcD
  set nu : normalizer (D : Set G) := ⟨u, huD⟩ with hnu
  set nv : normalizer (D : Set G) := ⟨c⁻¹ * u * c, hvD⟩ with hnv
  set nc : normalizer (D : Set G) := ⟨c, hcD⟩ with hnc
  have h11 : ψ nu * ψ nu = 1 := by
    rw [hψmul, show nu * nu = 1 from Subtype.ext hu2, map_one]
  have h22 : ψ nv * ψ nv = 1 := by
    rw [hψmul, show nv * nv = 1 from Subtype.ext hv2, map_one]
  have h12 : ψ nu * ψ nv = ψ nv * ψ nu := by
    rw [hψmul, hψmul, show nu * nv = nv * nu from Subtype.ext huv]
  have hτ₁ : ψ nu * ψ nc = ψ nc * ψ nv := by
    rw [hψmul, hψmul]
    congr 1
    apply Subtype.ext
    change u * c = c * (c⁻¹ * u * c)
    group
  have hτ₂ : ψ nv * ψ nc = ψ nc * (ψ nu * ψ nv) := by
    rw [hψmul, hψmul, hψmul]
    congr 1
    apply Subtype.ext
    change c⁻¹ * u * c * c = c * (u * (c⁻¹ * u * c))
    rw [← hcv]
    group
  have hτ : Function.Injective (ψ nc) := by
    intro x y hxy
    have h1 : Additive.toMul (ψ nc x) = Additive.toMul (ψ nc y) := congrArg _ hxy
    change (q (D.normalizerMonoidHom nc)) (Additive.toMul x) =
      (q (D.normalizerMonoidHom nc)) (Additive.toMul y) at h1
    exact (q (D.normalizerMonoidHom nc)).injective h1
  have hσ₁ : ψ nu ≠ 1 := by
    intro h1
    have hne : D.normalizerMonoidHom nu ≠ 1 := by
      intro h
      apply huC
      rw [mem_centralizer_iff]
      intro d hd
      have h' := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : G)) h
      simp only [MulAut.one_apply] at h'
      rw [normalizerMonoidHom_apply_apply_coe] at h'
      change u * d * u⁻¹ = d at h'
      calc d * u = u * d * u⁻¹ * u := by rw [h']
        _ = u * d := by group
    have hord : orderOf (D.normalizerMonoidHom nu) = 2 :=
      orderOf_eq_prime (by
        rw [← map_pow, pow_two, show nu * nu = 1 from Subtype.ext hu2, map_one]) hne
    apply hne
    refine CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial 2
      _ hord (not_two_dvd_card_of_odd hp2 hD) ?_
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (D ⧸ frattini D)) =>
      Additive.toMul (f (Additive.ofMul (x : D ⧸ frattini D)))) h1
    simp only [Module.End.one_apply, toMul_ofMul] at h
    change (q (D.normalizerMonoidHom nu)) (x : D ⧸ frattini D) = (x : D ⧸ frattini D) at h
    rw [show (x : D ⧸ frattini D) = QuotientGroup.mk' (frattini D) x from rfl,
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply] at h
    exact h
  have hdim : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 2 := by
    have h := finrank_eigenspace_le_two_of_pRank_le_two hp2 hD hexp hclass
      (σ := 1) (one_pow 2) ((pRank_le_of_le hp'.one_lt hDP _).trans hPrank) 1
      (fun _ => rfl)
    have htop : (1 : Module.End (ZMod p) (Additive (D ⧸ frattini D))).eigenspace 1 = ⊤ := by
      ext v
      simp
    rw [htop, finrank_top] at h
    exact h
  have h3 := three_le_finrank_of_cyclic (two_ne_zero_zmod hp' hp2) h11 h22 h12 hτ₁ hτ₂ hτ hσ₁
  omega

theorem card_le_eight_of_faithful {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {D : Type*}
    [Group D] [Finite D] (hD : IsPGroup p D) (hexp : ∀ x : D, x ^ p = 1)
    (hclass : commutator D ≤ Subgroup.center D) {A : Type*} [CommGroup A] [Finite A]
    (hA2 : ∀ a : A, a ^ 2 = 1) (ρ : A →* MulAut D) (hρ : Function.Injective ρ)
    (hfix : ∀ a : A, a ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ a)) ≤ 2) : Nat.card A ≤ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2g : IsPGroup 2 A := fun a => ⟨1, by rw [pow_one]; exact hA2 a⟩
  obtain ⟨n, hn⟩ := hA2g.exists_card_eq
  have hn3 : n ≤ 3 := by
    let _ : MulDistribMulAction A D := MulDistribMulAction.compHom D ρ
    have : FaithfulSMul A D := ⟨fun {a b} h => hρ (MulEquiv.ext h)⟩
    let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule fun x => by
      change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
      rw [hA2]
    have hlcs : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
      change ⁅⁅(⊤ : Subgroup D), ⊤⁆, ⊤⁆ = ⊥
      rw [commutator_eq_bot_iff_le_centralizer, coe_top, centralizer_univ]
      exact hclass
    have h := (CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound
      (hp.out.odd_of_ne_two hp2) hD (Monoid.exponent_dvd_of_forall_pow_eq_one hexp) hlcs n 2 hn
      (fun a ha => by
        have heq : CFSG.fixedPointSubgroup (zpowers a) D = fixedSubgroupOf (ρ a) := by
          ext x
          rw [mem_fixedSubgroupOf]
          constructor
          · intro h
            exact h ⟨a, mem_zpowers a⟩
          · intro h
            rintro ⟨b, hb⟩
            obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
            change (ρ (a ^ k)) x = x
            rw [map_zpow]
            exact zpow_apply_eq_self_of_apply_eq_self h k
        rw [heq]
        exact hfix a ha)).1
    omega
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 8 := by norm_num

theorem card_le_eight_of_faithful_subgroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {D P U : Subgroup G} (hD : IsPGroup p D) (hDP : D ≤ P) (hDexp : ∀ d ∈ D, d ^ p = 1)
    (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hUD : U ≤ normalizer (D : Set G)) (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hfaith : U ⊓ centralizer (D : Set G) = ⊥)
    (hfix : ∀ u ∈ U, u ≠ 1 → CFSG.Open.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2) :
    Nat.card U ≤ 8 := by
  classical
  have hexp : ∀ x : D, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  let _ : CommGroup U :=
    { (inferInstance : Group U) with mul_comm := fun a b => hU.1.is_comm.comm a b }
  set ρ := conjAction D U hUD with hρdef
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu' : (u : G) ∈ U ⊓ centralizer (D : Set G) := ⟨u.2, mem_ker_conjAction.mp hu⟩
    rw [hfaith, Subgroup.mem_bot] at hu'
    rw [Subgroup.mem_bot]
    exact Subtype.ext hu'
  have hA2 : ∀ a : U, a ^ 2 = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_pow, hU.2 a a.2, Subgroup.coe_one])
  refine card_le_eight_of_faithful hp2 hD hexp (commutator_le_center_of_forall hDcl) hA2 ρ hρ ?_
  intro a ha
  have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  exact (pRank_fixedSubgroupOf_le hp.out.one_lt hDP a).trans (hfix a a.2 ha')

theorem card_modEq_one_of_invariant {W Y : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) (hYW : Y ≤ W)
    (hcY : c ∈ normalizer (Y : Set G)) (hWc : W ⊓ centralizer ({c} : Set G) = ⊥) :
    Nat.card Y ≡ 1 [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Γ := zpowers c with hΓ
  have hΓ3 : IsPGroup 3 Γ := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hc3, one_zpow, Subgroup.coe_one]⟩
  have hΓY : Γ ≤ normalizer (Y : Set G) := zpowers_le.mpr hcY
  let φ : Γ →* MulAut Y := Y.normalizerMonoidHom.comp (inclusion hΓY)
  let _ : MulAction Γ Y := MulAction.compHom Y φ
  have h := hΓ3.card_modEq_card_fixedPoints Y
  have hfp : Nat.card (MulAction.fixedPoints Γ Y) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => map_one (φ g)⟩, fun ⟨y, hy⟩ => Subtype.ext ?_⟩
    have h1 : (φ ⟨c, mem_zpowers c⟩) y = y := hy ⟨c, mem_zpowers c⟩
    have h2 : c * (y : G) * c⁻¹ = y := by
      have := congrArg Subtype.val h1
      rwa [MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe] at this
    have hyW : (y : G) ∈ W ⊓ centralizer ({c} : Set G) := by
      refine ⟨hYW y.2, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (y : G) * c = c * (y : G) * c⁻¹ * c := by rw [h2]
        _ = c * y := by group
    rw [hWc, mem_bot] at hyW
    exact Subtype.ext hyW
  rw [hfp] at h
  exact h

theorem card_eq_of_invariant {W Y : Subgroup G} {c : G} (hW16 : Nat.card W = 16) (hc3 : c ^ 3 = 1)
    (hYW : Y ≤ W) (hcY : c ∈ normalizer (Y : Set G))
    (hWc : W ⊓ centralizer ({c} : Set G) = ⊥) :
    Nat.card Y = 1 ∨ Nat.card Y = 4 ∨ Nat.card Y = 16 := by
  have hmod := card_modEq_one_of_invariant hc3 hYW hcY hWc
  have hdvd : Nat.card Y ∣ 16 := hW16 ▸ Subgroup.card_dvd_of_le hYW
  have hle : Nat.card Y ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases h : Nat.card Y <;> simp_all

omit [Finite G] in
theorem mul_conj_mul_conj_eq_one {W : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hcW : c ∈ normalizer (W : Set G)) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hWc : W ⊓ centralizer ({c} : Set G) = ⊥) {w : G} (hw : w ∈ W) :
    w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) = 1 := by
  have hc' : c⁻¹ ∈ normalizer (W : Set G) := inv_mem hcW
  have hconj : ∀ x ∈ W, c⁻¹ * x * c ∈ W := fun x hx => by
    have := (mem_normalizer_iff.mp hc' x).mp hx
    simpa using this
  have hw1 := hconj w hw
  have hw2 := hconj _ hw1
  have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
  have e3 : c⁻¹ * (c⁻¹ * (c⁻¹ * w * c) * c) * c = w := by
    calc c⁻¹ * (c⁻¹ * (c⁻¹ * w * c) * c) * c = (c * c * c)⁻¹ * w * (c * c * c) := by group
      _ = w := by rw [hc3']; group
  have hcn : c⁻¹ * (w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c)) * c =
      w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) := by
    calc c⁻¹ * (w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c)) * c
        = (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) *
          (c⁻¹ * (c⁻¹ * (c⁻¹ * w * c) * c) * c) := by group
      _ = (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) * w := by rw [e3]
      _ = w * ((c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c)) :=
          hWab _ (mul_mem hw1 hw2) w hw
      _ = w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) := (mul_assoc _ _ _).symm
  have hnC : w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) ∈ W ⊓ centralizer ({c} : Set G) := by
    refine ⟨mul_mem (mul_mem hw hw1) hw2, mem_centralizer_singleton_iff.mpr ?_⟩
    set n := w * (c⁻¹ * w * c) * (c⁻¹ * (c⁻¹ * w * c) * c) with hn
    calc n * c = c * (c⁻¹ * n * c) := by group
      _ = c * n := by rw [hcn]
  rw [hWc, mem_bot] at hnC
  exact hnC

theorem commutator_eq_bot_of_isPGroup {X W R : Subgroup G} {c : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hR : IsPGroup p R) (hRX : R ≤ X) (hWR : W ≤ normalizer (R : Set G))
    (hcR : c ∈ normalizer (R : Set G)) (hW : CFSG.Assembly.IsElemAbelian 2 W)
    (hW16 : Nat.card W = 16) (hcW : c ∈ normalizer (W : Set G)) (hc3 : c ^ 3 = 1)
    (hWc : W ⊓ centralizer ({c} : Set G) = ⊥)
    (hrank : ∀ t ∈ W, t ≠ 1 →
      CFSG.Open.pRank p (X ⊓ centralizer ({t} : Set G) : Subgroup G) ≤ 2) :
    ⁅R, W⁆ = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 4) (by rw [hW16]; norm_num)
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hWsq : ∀ x ∈ W, x * x = 1 := fun x hx => by rw [← pow_two]; exact hW.2 x hx
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW16
    norm_num at hW16
  set K₀ := W ⊓ centralizer (R : Set G) with hK₀
  have hcK₀ : c ∈ normalizer (K₀ : Set G) :=
    mem_normalizer_inf hcW (mem_normalizer_centralizer hcR)
  rcases card_eq_of_invariant hW16 hc3 inf_le_left hcK₀ hWc with h1 | h4 | h16
  ·
    exfalso
    have hfaith : W ⊓ centralizer (R : Set G) = ⊥ := Subgroup.card_eq_one.mp h1
    obtain ⟨D, hDR, hND, hDexp, hDcl, hDfaith⟩ :=
      exists_critical_subgroup hp2 hR hW2 hWR hfaith hW1
    have h8 := card_le_eight_of_faithful_subgroup hp2 (hR.to_le hDR) (hDR.trans hRX) hDexp hDcl
      (hWR.trans hND) hW hDfaith hrank
    omega
  ·
    exfalso
    have h4' : Nat.card K₀ = 4 := h4
    obtain ⟨t, htK, ht1⟩ : ∃ t ∈ K₀, t ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : K₀ = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx)
      rw [hbot, card_bot] at h4'
      norm_num at h4'
    obtain ⟨u, huW, huK⟩ : ∃ u ∈ W, u ∉ K₀ := by
      by_contra h
      push Not at h
      have hle := Subgroup.card_le_of_le (show W ≤ K₀ from fun x hx => h x hx)
      omega
    have hc' : c⁻¹ ∈ normalizer (W : Set G) := inv_mem hcW
    set v := c⁻¹ * u * c with hv
    have hvW : v ∈ W := by
      have := (mem_normalizer_iff.mp hc' u).mp huW
      simpa [hv] using this
    have huv : u * v = v * u := hWab u huW v hvW
    have hu2 : u * u = 1 := hWsq u huW
    have hv2 : v * v = 1 := hWsq v hvW
    have hcv : c⁻¹ * v * c = u * v := by
      have h := mul_conj_mul_conj_eq_one hc3 hcW hWab hWc huW
      have h' : c⁻¹ * v * c = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h', mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hu2, huv]
    have hu1 : u ≠ 1 := fun h => huK (h ▸ K₀.one_mem)
    have hv1 : v ≠ 1 := fun h => hu1 (by
      calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
        _ = 1 := by rw [← hv, h]; group)
    have huv' : u ≠ v := by
      intro h
      have huC : u ∈ W ⊓ centralizer ({c} : Set G) := by
        refine ⟨huW, mem_centralizer_singleton_iff.mpr ?_⟩
        calc u * c = c * (c⁻¹ * u * c) := by group
          _ = c * u := by rw [← hv, ← h]
      rw [hWc, mem_bot] at huC
      exact hu1 huC
    set U := closure ({u, v} : Set G) with hU
    have hU4 : IsKleinFour U :=
      Proof1623.isKleinFour_closure_pair hu2 hv2 hu1 hv1 huv' (show Commute u v from huv)
    have hUcard : Nat.card U = 4 := IsKleinFour.card_four
    have hUW : U ≤ W := by
      rw [hU, closure_le]
      rintro g (rfl | rfl)
      · exact huW
      · exact hvW
    have hcU : c ∈ normalizer (U : Set G) := by
      have hle : U.map (MulAut.conj c⁻¹).toMonoidHom ≤ U := by
        rw [hU, MonoidHom.map_closure, closure_le]
        rintro _ ⟨g, hg, rfl⟩
        have hg' : g = u ∨ g = v := by simpa using hg
        rcases hg' with hgu | hgv
        · rw [hgu]
          change c⁻¹ * u * c⁻¹⁻¹ ∈ closure ({u, v} : Set G)
          rw [inv_inv, ← hv]
          exact subset_closure (by simp)
        · rw [hgv]
          change c⁻¹ * v * c⁻¹⁻¹ ∈ closure ({u, v} : Set G)
          rw [inv_inv, hcv]
          exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      have hc'U : c⁻¹ ∈ normalizer (U : Set G) :=
        mem_normalizer_fintype fun w hw => hle ⟨w, hw, rfl⟩
      simpa using inv_mem hc'U
    have hUfaith : U ⊓ centralizer (R : Set G) = ⊥ := by
      have hY := card_eq_of_invariant hW16 hc3 (inf_le_left.trans hUW : U ⊓ K₀ ≤ W)
        (mem_normalizer_inf hcU hcK₀) hWc
      have hYU : Nat.card (U ⊓ K₀ : Subgroup G) ≤ 4 := hUcard ▸ Subgroup.card_le_of_le inf_le_left
      have hY1 : U ⊓ K₀ = ⊥ := by
        rcases hY with h | h | h
        · exact Subgroup.card_eq_one.mp h
        · exfalso
          have heq : U ⊓ K₀ = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hUcard])
          have huU : u ∈ U := subset_closure (by simp)
          rw [← heq] at huU
          exact huK huU.2
        · omega
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ U ⊓ K₀ := ⟨hx.1, hUW hx.1, hx.2⟩
      rwa [hY1] at hx'
    have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
    have hUbot : U ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hUcard
      norm_num at hUcard
    obtain ⟨D, hDR, hND, hDexp, hDcl, hDfaith⟩ :=
      exists_critical_subgroup hp2 hR hU2 (hUW.trans hWR) hUfaith hUbot
    have htR : t ∈ centralizer (R : Set G) := htK.2
    have hDP : D ≤ X ⊓ centralizer ({t} : Set G) := by
      intro d hd
      refine ⟨hRX (hDR hd), mem_centralizer_singleton_iff.mpr ?_⟩
      exact mem_centralizer_iff.mp htR d (hDR hd)
    have huC : u ∉ centralizer (D : Set G) := by
      intro h
      have hu' : u ∈ U ⊓ centralizer (D : Set G) := ⟨subset_closure (by simp), h⟩
      rw [hDfaith, mem_bot] at hu'
      exact hu1 hu'
    exact false_of_kleinFour_cyclic hp2 (hR.to_le hDR) hDP (hrank t htK.1 ht1) hDexp hDcl
      (hND (hWR huW)) (hND hcR) hu2 huC hv2 huv hcv
  ·
    have hK₀W : K₀ = W := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hW16])
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [← hK₀W]
    exact inf_le_right

end Groups

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
