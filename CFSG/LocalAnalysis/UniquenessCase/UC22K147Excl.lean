module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace
public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds
import CFSG.LargeExtraspecial.A2ModSqueeze
import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147

open CFSG.Open Subgroup Module
open CFSG.RankThree.FFModules
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

structure Facts (H : Type) [Group H] (ℓ : ℕ) : Prop where
  simple : IsSimpleGroup H
  exists_involution : ∃ s : H, orderOf s = 2
  inverts : ∀ s : H, orderOf s = 2 → ∃ x : H, orderOf x = ℓ ∧ s * x * s⁻¹ = x⁻¹
  inner : ∀ α : MulAut H, α ^ 2 = 1 → ∃ s : H, ∀ y : H, α y = s * y * s⁻¹

theorem inv_ne_of_orderOf {H : Type} [Group H] {x : H} {ℓ : ℕ} (hx : orderOf x = ℓ) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) : x⁻¹ ≠ x := by
  intro h
  have h2 : x ^ 2 = 1 := by
    rw [pow_two]
    calc x * x = x⁻¹ * x := by rw [h]
      _ = 1 := inv_mul_cancel x
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hx] at this
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)

theorem mul_self_and_ne_one {H : Type} [Group H] {s : H} (hs : orderOf s = 2) : s * s = 1 ∧ s ≠ 1 := by
  refine ⟨by rw [← pow_two, ← hs, pow_orderOf_eq_one], fun h => ?_⟩
  rw [h, orderOf_one] at hs
  exact absurd hs (by norm_num)

namespace Facts

variable {H H' : Type} [Group H] [Group H'] {ℓ : ℕ}

theorem of_mulEquiv (e : H ≃* H') (h : Facts H ℓ) : Facts H' ℓ where
  simple := by
    haveI := h.simple
    exact e.symm.isSimpleGroup
  exists_involution := by
    obtain ⟨s, hs⟩ := h.exists_involution
    exact ⟨e s, by rw [MulEquiv.orderOf_eq]; exact hs⟩
  inverts s hs := by
    obtain ⟨x, hx, hsx⟩ := h.inverts (e.symm s) (by rw [MulEquiv.orderOf_eq]; exact hs)
    refine ⟨e x, by rw [MulEquiv.orderOf_eq]; exact hx, ?_⟩
    have := congrArg e hsx
    rwa [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply] at this
  inner α hα := by
    let β : MulAut H := (e.trans α).trans e.symm
    have hβ : ∀ y, β y = e.symm (α (e y)) := fun y => rfl
    have hα2 : ∀ z, α (α z) = z := fun z => by
      have := congrArg (fun γ : MulAut H' => γ z) hα
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using this
    have hβ2 : β ^ 2 = 1 := by
      refine MulEquiv.ext fun y => ?_
      rw [pow_two, MulAut.mul_apply, hβ, hβ, MulEquiv.apply_symm_apply, hα2, MulEquiv.symm_apply_apply,
        MulAut.one_apply]
    obtain ⟨s, hs⟩ := h.inner β hβ2
    refine ⟨e s, fun y => ?_⟩
    have := congrArg e (hs (e.symm y))
    rwa [hβ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this

theorem exists_noncomm (h : Facts H ℓ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ∃ s x : H, orderOf s = 2 ∧ orderOf x = ℓ ∧ s * x * s⁻¹ = x⁻¹ ∧ s * x ≠ x * s := by
  obtain ⟨s, hs⟩ := h.exists_involution
  obtain ⟨x, hx, hsx⟩ := h.inverts s hs
  refine ⟨s, x, hs, hx, hsx, fun hc => inv_ne_of_orderOf hx hℓ hℓ2 ?_⟩
  rw [← hsx, hc, mul_inv_cancel_right]

theorem center_eq_bot (h : Facts H ℓ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : center H = ⊥ := by
  haveI := h.simple
  obtain ⟨s, x, -, -, -, hc⟩ := h.exists_noncomm hℓ hℓ2
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H)).resolve_right fun htop => hc ?_
  have hs : s ∈ center H := by rw [htop]; exact mem_top s
  exact (mem_center_iff.1 hs x).symm

theorem exists_involution_of_aut (h : Facts H ℓ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {α : MulAut H}
    (hα : α ^ 2 = 1) (hα1 : α ≠ 1) : ∃ s : H, orderOf s = 2 ∧ ∀ y, α y = s * y * s⁻¹ := by
  obtain ⟨s, hs⟩ := h.inner α hα
  refine ⟨s, ?_, hs⟩
  have hss : s * s ∈ center H := by
    rw [mem_center_iff]
    intro g
    have h1 : α (α g) = g := by
      have := congrArg (fun γ : MulAut H => γ g) hα
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using this
    rw [hs, hs] at h1
    calc g * (s * s) = s * (s * g * s⁻¹) * s⁻¹ * (s * s) := by rw [h1]
      _ = s * s * g := by group
  rw [h.center_eq_bot hℓ hℓ2, mem_bot] at hss
  refine orderOf_eq_prime (by rw [pow_two]; exact hss) fun hs1 => hα1 ?_
  refine MulEquiv.ext fun y => ?_
  rw [hs, hs1, one_mul, inv_one, mul_one, MulAut.one_apply]

end Facts

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem fixSub_zpowers_eq_ker (ρ : Representation (ZMod 2) G V) {t : G} (ht : orderOf t = 2) :
    fixSub ρ (zpowers t) = LinearMap.ker (ρ t - 1) := by
  ext v
  simp only [mem_fixSub, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  refine ⟨fun h => h t (mem_zpowers t), fun h a ha => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero, map_one, Module.End.one_apply]
  · rw [h1, zpow_one]
    exact h

theorem finrank_quotient_fixSub_eq (ρ : Representation (ZMod 2) G V) {t : G} (ht : orderOf t = 2) :
    finrank (ZMod 2) (V ⧸ fixSub ρ (zpowers t)) = finrank (ZMod 2) (commSpace ρ (zpowers t)) := by
  have hfin : IsOfFinOrder t := orderOf_pos_iff.1 (by rw [ht]; norm_num)
  rw [fixSub_zpowers_eq_ker ρ ht,
    CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.commSpace_zpowers_eq_range ρ t hfin]
  exact (LinearMap.quotKerEquivRange (ρ t - 1)).finrank_eq

theorem le_mGV [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) {k : ℕ}
    (hev : ∃ t : G, orderOf t = 2)
    (h : ∀ t : G, orderOf t = 2 → k ≤ finrank (ZMod 2) (V ⧸ fixSub ρ (zpowers t))) :
    k ≤ F05.mGV ρ := by
  obtain ⟨t₀, ht₀⟩ := hev
  have heven : Even (Nat.card G) := by
    have := orderOf_dvd_natCard t₀
    rw [ht₀] at this
    exact even_iff_two_dvd.2 this
  unfold F05.mGV
  rw [if_pos heven]
  refine le_csInf ⟨_, t₀, ht₀, rfl⟩ fun m hm => ?_
  obtain ⟨t, ht, rfl⟩ := hm
  exact h t ht

theorem orderOf_two_le_of_inverts [Finite G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ) {t : G} (ht : orderOf t = 2)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {e : G} (he : orderOf e = ℓ) (hinv : t * e * t⁻¹ = e⁻¹) :
    orderOf (2 : ZMod ℓ) ≤ 2 * finrank (ZMod 2) (commSpace ρ (zpowers t)) := by
  have hab : IsElemAbelian ℓ (zpowers e) := ⟨inferInstance, fun x hx =>
    orderOf_dvd_iff_pow_eq_one.1 (he ▸ orderOf_dvd_of_mem_zpowers hx)⟩
  have hcard : Nat.card (zpowers e) = ℓ ^ 1 := by rw [Nat.card_zpowers, he, pow_one]
  have hX : ∀ x ∈ zpowers e, t * x * t⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h := map_zpow (MulAut.conj t) e k
    simp only [MulAut.conj_apply] at h
    rw [h, hinv, inv_zpow]
  have h73 := (finrank_commutator_eq_two_mul_and_involution_rank_bound ρ hρ t ht hℓ hℓ2 one_pos
    (zpowers e) hab hcard hX).2
  have hd : orderOf (2 : ZMod ℓ) ≤ eOfPrime ℓ := by
    rw [← CFSG.LocalAnalysis.RankThreeUC.WeakClosure.dOfPrime_eq_orderOf hℓ hℓ2]
    unfold eOfPrime
    split_ifs <;> omega
  calc orderOf (2 : ZMod ℓ) ≤ eOfPrime ℓ := hd
    _ ≤ max 1 (minHyperplaneOrbit ℓ (zpowers e)) * eOfPrime ℓ :=
      Nat.le_mul_of_pos_left _ (lt_of_lt_of_le one_pos (le_max_left _ _))
    _ ≤ _ := h73

theorem orderOf_two_le_finrank_of_stable [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {x : G} (hx : orderOf x = ℓ) (W : Submodule (ZMod 2) V)
    (hW : ∀ w ∈ W, ρ x w ∈ W) (hW' : ∀ w ∈ W, ρ x⁻¹ w ∈ W) (hne : ∃ w ∈ W, ρ x w ≠ w) :
    orderOf (2 : ZMod ℓ) ≤ finrank (ZMod 2) W := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let f : W →ₗ[ZMod 2] W := (ρ x).restrict hW
  let f' : W →ₗ[ZMod 2] W := (ρ x⁻¹).restrict hW'
  have hff' : f.comp f' = LinearMap.id := LinearMap.ext fun w => Subtype.ext (ρ.self_inv_apply x w)
  have hf'f : f'.comp f = LinearMap.id := LinearMap.ext fun w => Subtype.ext (ρ.inv_self_apply x w)
  let g : W ≃ₗ[ZMod 2] W := LinearEquiv.ofLinear f f' hff' hf'f
  have hgw : ∀ w : W, ((g w : W) : V) = ρ x w := fun w => rfl
  have hpow : ∀ k : ℕ, ∀ w : W, (((g ^ k) w : W) : V) = ρ (x ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, LinearEquiv.mul_apply, ih, hgw, pow_succ, map_mul, Module.End.mul_apply]
  have hg : g ^ ℓ = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [hpow, ← hx, pow_orderOf_eq_one, map_one]
    rfl
  have hg1 : g ≠ 1 := by
    intro h1
    obtain ⟨w, hw, hxw⟩ := hne
    apply hxw
    have := congrArg (fun φ : W ≃ₗ[ZMod 2] W => ((φ ⟨w, hw⟩ : W) : V)) h1
    simpa [hgw] using this
  exact (CFSG.LargeExtraspecial.A2Mod.orderOf_two_le_finrank_commSpace hℓ2 hg hg1).trans
    (Submodule.finrank_le _)

@[expose] def ptStab (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {c | ∀ w ∈ W, ρ c w = w}
  mul_mem' {a b} ha hb w hw := by rw [map_mul, Module.End.mul_apply, hb w hw, ha w hw]
  one_mem' w _ := by rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha w hw := by
    conv_lhs => rw [← ha w hw]
    exact ρ.inv_self_apply a w

theorem orderOf_two_le_of_facts [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {L : Subgroup G} (hL : IsComponentOf L ⊤)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hF : Facts L ℓ) {t : G} (ht : orderOf t = 2) :
    orderOf (2 : ZMod ℓ) ≤ 2 * finrank (ZMod 2) (commSpace ρ (zpowers t)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := hF.simple
  have htt : t * t = 1 := (mul_self_and_ne_one ht).1
  obtain ⟨s₀, x₀, hs₀, hx₀, hsx₀, hnc⟩ := hF.exists_noncomm hℓ hℓ2
  have hx₀G : orderOf (x₀ : G) = ℓ := by rw [Subgroup.orderOf_coe, hx₀]
  have key : ∀ g x : G, orderOf x = ℓ → (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ = x⁻¹ →
      orderOf (2 : ZMod ℓ) ≤ 2 * finrank (ZMod 2) (commSpace ρ (zpowers t)) := by
    intro g x hx hinv
    refine orderOf_two_le_of_inverts ρ hρ ht hℓ hℓ2 (e := g * x * g⁻¹) ?_ ?_
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
    · calc t * (g * x * g⁻¹) * t⁻¹ = g * ((g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹) * g⁻¹ := by group
        _ = (g * x * g⁻¹)⁻¹ := by rw [hinv]; group
  by_cases hA : ∃ g : G, ∃ y ∈ L, (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹ ∉ L
  ·
    obtain ⟨g, y, hy, hyL⟩ := hA
    have huu : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt]; group
    obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * t * g := ⟨_, rfl⟩
    rw [← hu] at hyL huu
    obtain ⟨L₂, hL₂def⟩ : ∃ L₂ : Subgroup G, L₂ = L.map (MulAut.conj u).toMonoidHom := ⟨_, rfl⟩
    have hL₂ : IsComponentOf L₂ ⊤ := by
      rw [hL₂def]
      exact (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj u) L).2 hL
    have hmem₂ : ∀ z ∈ L, u * z * u⁻¹ ∈ L₂ := fun z hz => by rw [hL₂def]; exact ⟨z, hz, rfl⟩
    have hne : L ≠ L₂ := by
      intro h
      apply hyL
      rw [h]
      exact hmem₂ y hy
    have hcomm : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a := by
      intro a ha b hb
      have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L₂ hL hL₂ hne
      exact (mem_centralizer_iff.1 ((commutator_eq_bot_iff_le_centralizer.1 h) ha) b hb).symm
    obtain ⟨y₂, hy₂⟩ : ∃ y₂ : G, y₂ = u * x₀ * u⁻¹ := ⟨_, rfl⟩
    have hy₂L : y₂ ∈ L₂ := by rw [hy₂]; exact hmem₂ x₀ x₀.2
    have hxy : (x₀ : G) * y₂⁻¹ = y₂⁻¹ * x₀ := hcomm _ x₀.2 _ (inv_mem hy₂L)
    have hx₀ℓ : (x₀ : G) ^ ℓ = 1 := by rw [← hx₀G]; exact pow_orderOf_eq_one _
    have hy₂ℓ : y₂ ^ ℓ = 1 := by rw [hy₂, conj_pow, hx₀ℓ, mul_one, mul_inv_cancel]
    have hpow : ((x₀ : G) * y₂⁻¹) ^ ℓ = 1 := by
      rw [Commute.mul_pow hxy, inv_pow, hx₀ℓ, hy₂ℓ, inv_one, one_mul]
    have hne1 : (x₀ : G) * y₂⁻¹ ≠ 1 := by
      intro h1
      have hxy₂ : (x₀ : G) = y₂ := mul_inv_eq_one.1 h1
      have hx₀L₂ : (x₀ : G) ∈ L₂ := by rw [hxy₂]; exact hy₂L
      exact hnc (Subtype.ext (hcomm _ s₀.2 _ hx₀L₂))
    have hinv : u * ((x₀ : G) * y₂⁻¹) * u⁻¹ = ((x₀ : G) * y₂⁻¹)⁻¹ := by
      rw [hy₂]
      calc u * ((x₀ : G) * (u * x₀ * u⁻¹)⁻¹) * u⁻¹
          = (u * x₀ * u⁻¹) * ((u * u) * (x₀ : G)⁻¹ * (u * u)⁻¹) := by group
        _ = ((x₀ : G) * (u * x₀ * u⁻¹)⁻¹)⁻¹ := by rw [huu]; group
    exact key g _ (orderOf_eq_prime hpow hne1) (by rw [← hu]; exact hinv)
  push Not at hA
  by_cases hB : ∃ g : G, ∃ y ∈ L, (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹ ≠ y
  ·
    obtain ⟨g, y, hy, hyne⟩ := hB
    have huu : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt]; group
    have hmem : ∀ z : L, (g⁻¹ * t * g) * (z : G) * (g⁻¹ * t * g)⁻¹ ∈ L := fun z => hA g z z.2
    obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * t * g := ⟨_, rfl⟩
    rw [← hu] at hyne huu hmem
    have hinvol : ∀ z : G, u * (u * z * u⁻¹) * u⁻¹ = z := fun z => by
      calc u * (u * z * u⁻¹) * u⁻¹ = (u * u) * z * (u * u)⁻¹ := by group
        _ = z := by rw [huu]; group
    let α : MulAut L :=
      { toFun := fun z => ⟨u * z * u⁻¹, hmem z⟩
        invFun := fun z => ⟨u * z * u⁻¹, hmem z⟩
        left_inv := fun z => Subtype.ext (hinvol z)
        right_inv := fun z => Subtype.ext (hinvol z)
        map_mul' := fun a b => Subtype.ext (by
          change u * ((a : G) * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹)
          group) }
    have hαapp : ∀ z : L, ((α z : L) : G) = u * z * u⁻¹ := fun z => rfl
    have hα2 : α ^ 2 = 1 := by
      refine MulEquiv.ext fun z => Subtype.ext ?_
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hαapp, hαapp]
      exact hinvol z
    have hα1 : α ≠ 1 := by
      intro h1
      apply hyne
      have := congrArg (fun β : MulAut L => ((β ⟨y, hy⟩ : L) : G)) h1
      simpa only [hαapp, MulAut.one_apply] using this
    obtain ⟨s, hs, hsα⟩ := hF.exists_involution_of_aut hℓ hℓ2 hα2 hα1
    obtain ⟨x, hx, hsx⟩ := hF.inverts s hs
    refine key g x (by rw [Subgroup.orderOf_coe, hx]) ?_
    have h1 : ((α x : L) : G) = ((s * x * s⁻¹ : L) : G) := congrArg Subtype.val (hsα x)
    rw [hαapp, hsx] at h1
    rw [← hu, h1, Subgroup.coe_inv]
  push Not at hB
  have hct : ∀ g : G, ∀ y ∈ L, t * (g * y * g⁻¹) = g * y * g⁻¹ * t := by
    intro g y hy
    calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹) * g⁻¹ * t := by group
      _ = g * y * g⁻¹ * t := by rw [hB g y hy]
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) V, W = LinearMap.range (ρ t - 1) := ⟨_, rfl⟩
  have hWmem : ∀ v : V, ρ t v - v ∈ W := fun v => by rw [hW]; exact ⟨v, by simp⟩
  have hWinv : ∀ c : G, t * c = c * t → ∀ w ∈ W, ρ c w ∈ W := by
    intro c hc w hw
    rw [hW] at hw ⊢
    obtain ⟨v, rfl⟩ := hw
    refine ⟨ρ c v, ?_⟩
    have h1 : ρ t (ρ c v) = ρ c (ρ t v) := by
      rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    simp [h1]
  have hclaim : ∃ g : G, ∃ z ∈ L, orderOf z = ℓ ∧ ∃ w ∈ W, ρ (g * z * g⁻¹) w ≠ w := by
    by_contra hcon
    push Not at hcon
    have hfix : ∀ g : G, ∀ y ∈ L, ∀ w ∈ W, ρ (g * y * g⁻¹) w = w := by
      intro g
      let K : Subgroup L := (ptStab ρ W).comap ((MulAut.conj g).toMonoidHom.comp L.subtype)
      have hmemK : ∀ y : L, y ∈ K ↔ ∀ w ∈ W, ρ (g * y * g⁻¹) w = w := fun y => Iff.rfl
      haveI hKn : K.Normal := ⟨fun a ha b => (hmemK _).2 fun w hw => by
        have h1 : g * ((b * a * b⁻¹ : L) : G) * g⁻¹ =
            (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        have hb' : ρ (g * b * g⁻¹)⁻¹ w ∈ W := by
          refine hWinv _ ?_ w hw
          have := hct g _ (inv_mem b.2)
          rw [show (g * (b : G) * g⁻¹)⁻¹ = g * (b : G)⁻¹ * g⁻¹ by group]
          exact this
        rw [h1, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hmemK a).1 ha _ hb',
          ρ.self_inv_apply]⟩
      have hx₀K : x₀ ∈ K := (hmemK x₀).2 (hcon g x₀ x₀.2 hx₀G)
      have hKtop : K = ⊤ := by
        refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_left fun hbot => ?_
        rw [hbot, mem_bot] at hx₀K
        rw [hx₀K, orderOf_one] at hx₀
        exact hℓ.one_lt.ne hx₀
      intro y hy w hw
      have hyK : (⟨y, hy⟩ : L) ∈ K := by rw [hKtop]; exact mem_top _
      exact (hmemK _).1 hyK w hw
    have hcent : ∀ g : G, ∀ y ∈ L, ∀ v : V,
        ρ t (ρ (g * y * g⁻¹) v - v) = ρ (g * y * g⁻¹) v - v := by
      intro g y hy v
      have h1 : ρ t (ρ (g * y * g⁻¹) v) = ρ (g * y * g⁻¹) (ρ t v) := by
        rw [← Module.End.mul_apply, ← map_mul, hct g y hy, map_mul, Module.End.mul_apply]
      have h2 := hfix g y hy _ (hWmem v)
      rw [map_sub, sub_eq_iff_eq_add] at h2
      rw [map_sub, h1, h2]
      abel
    let U : Submodule (ZMod 2) V :=
      Submodule.span (ZMod 2) {w | ∃ g : G, ∃ y ∈ L, ∃ v : V, w = ρ (g * y * g⁻¹) v - v}
    have hUinv : ∀ h : G, U ≤ U.comap (ρ h) := fun h => Submodule.span_le.2 (by
      rintro _ ⟨g, y, hy, v, rfl⟩
      have h1 : ρ h (ρ (g * y * g⁻¹) v) = ρ (h * g * y * (h * g)⁻¹) (ρ h v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
          show h * (g * y * g⁻¹) = h * g * y * (h * g)⁻¹ * h by group]
      show ρ h (ρ (g * y * g⁻¹) v - v) ∈ U
      rw [map_sub, h1]
      exact Submodule.subset_span ⟨h * g, y, hy, ρ h v, rfl⟩)
    have hU0 : U ≠ ⊥ := by
      have hx₀1 : (x₀ : G) ≠ 1 := fun h => by
        rw [h, orderOf_one] at hx₀G
        exact hℓ.one_lt.ne hx₀G
      obtain ⟨v, hv⟩ : ∃ v : V, ρ x₀ v ≠ v := by
        by_contra hcon'
        push Not at hcon'
        apply hx₀1
        apply hρ
        rw [map_one]
        exact LinearMap.ext fun v => (hcon' v).trans (Module.End.one_apply v).symm
      intro hU
      have hmemU : ρ (1 * (x₀ : G) * 1⁻¹) v - v ∈ U := Submodule.subset_span ⟨1, x₀, x₀.2, v, rfl⟩
      rw [hU, Submodule.mem_bot, sub_eq_zero, one_mul, inv_one, mul_one] at hmemU
      exact hv hmemU
    have hUtop : U = ⊤ := by
      haveI := hirr
      let S : Subrepresentation ρ := ⟨U, fun h _ hw => hUinv h hw⟩
      rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
      · exact absurd (congrArg Subrepresentation.toSubmodule h) hU0
      · exact congrArg Subrepresentation.toSubmodule h
    have hUker : U ≤ LinearMap.ker (ρ t - 1) := Submodule.span_le.2 (by
      rintro _ ⟨g, y, hy, v, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hcent g y hy v)
    have ht1 : t = 1 := by
      apply hρ
      rw [map_one]
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ LinearMap.ker (ρ t - 1) := hUker (by rw [hUtop]; exact Submodule.mem_top)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      exact hv
    exact (mul_self_and_ne_one ht).2 ht1
  obtain ⟨g, z, hz, hzℓ, w, hw, hzw⟩ := hclaim
  have hxt : t * (g * z * g⁻¹) = (g * z * g⁻¹) * t := hct g z hz
  have hxt' : t * (g * z * g⁻¹)⁻¹ = (g * z * g⁻¹)⁻¹ * t := by
    calc t * (g * z * g⁻¹)⁻¹ = (g * z * g⁻¹)⁻¹ * ((g * z * g⁻¹) * t) * (g * z * g⁻¹)⁻¹ := by group
      _ = (g * z * g⁻¹)⁻¹ * (t * (g * z * g⁻¹)) * (g * z * g⁻¹)⁻¹ := by rw [hxt]
      _ = (g * z * g⁻¹)⁻¹ * t := by group
  have hxℓ : orderOf (g * z * g⁻¹) = ℓ := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hzℓ]
  have hbound := orderOf_two_le_finrank_of_stable ρ hℓ hℓ2 hxℓ W (hWinv _ hxt) (hWinv _ hxt')
    ⟨w, hw, hzw⟩
  have hWc : W = commSpace ρ (zpowers t) := by
    rw [hW, CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.commSpace_zpowers_eq_range ρ t
      (orderOf_pos_iff.1 (by rw [ht]; norm_num))]
  rw [← hWc]
  omega

theorem lt_mGV_of_facts [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {L : Subgroup G} (hL : IsComponentOf L ⊤)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hF : Facts L ℓ) {n : ℕ}
    (hn : 2 * n + 4 ≤ orderOf (2 : ZMod ℓ)) : n + 1 < F05.mGV ρ := by
  obtain ⟨s, hs⟩ := hF.exists_involution
  have h := le_mGV ρ (k := n + 2) ⟨s, by rw [Subgroup.orderOf_coe, hs]⟩ fun t ht => by
    have := orderOf_two_le_of_facts ρ hρ hirr hL hℓ hℓ2 hF ht
    rw [finrank_quotient_fixSub_eq ρ ht]
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147
