module

public import CFSG.Quasithin.Background.SmithB45M22HatSmall

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Quasithin CFSG.Quasithin.HatM22 Module
open CFSG.CharacterTheory.SteinbergBY (FieldFour)

theorem le_center_or_eq_top_of_isQuasisimple {K : Type*} [Group K] (h : CFSG.IsQuasisimple K)
    (N : Subgroup K) [N.Normal] : N ≤ center K ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  haveI hNm : (N.map (QuotientGroup.mk' (center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center K))) with h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (center K) x ∈ (⊥ : Subgroup (K ⧸ center K)) := h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hNZ : N ⊔ center K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center K)) N
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator K ≤ N := by
      have e : commutator K = ⁅N ⊔ center K, N ⊔ center K⁆ := by rw [hNZ]; rfl
      rw [e, Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left N N
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

theorem isHat_of_mulEquiv {X Y S : Type} [Group X] [Group Y] [Group S] (e : X ≃* Y)
    (h : IsHat X S) : IsHat Y S := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv e.symm hq, ?_, ⟨?_⟩⟩
  · have h1 : Nat.card ((center X).map (e : X →* Y)) = Nat.card (center X) :=
      Subgroup.card_map_of_injective e.injective
    rw [Subgroup.map_center_eq e] at h1
    rw [h1, hc]
  · exact (QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e)).symm.trans f

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] noncomputable def toMulAutHom (U : Type) [AddCommGroup U] [Module (ZMod 2) U] :
    (U ≃ₗ[ZMod 2] U) →* MulAut (Multiplicative U) where
  toFun e := e.toAddEquiv.toMultiplicative
  map_one' := by
    ext x
    rfl
  map_mul' e f := by
    ext x
    rfl

theorem toMulAutHom_apply (e : U ≃ₗ[ZMod 2] U) (x : U) :
    toMulAutHom U e (Multiplicative.ofAdd x) = Multiplicative.ofAdd (e x) := rfl

theorem toMulAutHom_injective : Function.Injective (toMulAutHom U) := by
  intro e f h
  ext x
  have := DFunLike.congr_fun h (Multiplicative.ofAdd x)
  exact congrArg Multiplicative.toAdd this

theorem map_eq_of_inv {L : Subgroup (U ≃ₗ[ZMod 2] U)} {W : Submodule (ZMod 2) U}
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) {g : U ≃ₗ[ZMod 2] U} (hg : g ∈ L) :
    W.map (g : U →ₗ[ZMod 2] U) = W := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hW g hg w hw
  · refine ⟨g.symm w, hW g⁻¹ (L.inv_mem hg) w hw, ?_⟩
    simp

@[expose] noncomputable def restrictHom (L : Subgroup (U ≃ₗ[ZMod 2] U)) (W : Submodule (ZMod 2) U)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) : ↥L →* (↥W ≃ₗ[ZMod 2] ↥W) where
  toFun g := LinearEquiv.ofSubmodules (g : U ≃ₗ[ZMod 2] U) W W (map_eq_of_inv hW g.2)
  map_one' := by
    ext w
    rfl
  map_mul' g h := by
    ext w
    rfl

theorem realizes_of_irr (hHat : HatM22SmallModules) [Finite U] (L : Subgroup (U ≃ₗ[ZMod 2] U))
    (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) [Nontrivial U]
    (hirr : ∀ W : Submodule (ZMod 2) U, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcard : Nat.card U < 2 ^ 30) :
    (FFModel.nat hatM22Γ₀).Realizes (L.map (toMulAutHom U)) ⊤ ⊥ := by
  refine hHat (Multiplicative U) (fun v => ?_) (L.map (toMulAutHom U))
    (isHat_of_mulEquiv (L.equivMapOfInjective _ toMulAutHom_injective) hL) ⟨bot_lt_top, ?_⟩
    (by rwa [Nat.card_congr Multiplicative.toAdd])
  · rw [pow_two]
    change Multiplicative.ofAdd (Multiplicative.toAdd v + Multiplicative.toAdd v) = 1
    rw [ZModModule.add_self]
    rfl
  · intro J hJ _ _
    let W : Submodule (ZMod 2) U := AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' J)
    have hmem : ∀ w : U, w ∈ W ↔ Multiplicative.ofAdd w ∈ J := fun w => Iff.rfl
    have hWinv : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W := by
      intro g hg w hw
      rw [hmem] at hw ⊢
      have := hJ ⟨toMulAutHom U g, ⟨g, hg, rfl⟩⟩ _ hw
      exact this
    rcases hirr W hWinv with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have : Multiplicative.toAdd x ∈ W := (hmem _).mpr hx
      rw [h, Submodule.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact this
    · right
      rw [eq_top_iff]
      intro x _
      have : Multiplicative.toAdd x ∈ W := by rw [h]; trivial
      exact (hmem _).mp this

theorem card_eq_of_realizes {L : Subgroup (MulAut (Multiplicative U))}
    (h : (FFModel.nat hatM22Γ₀).Realizes L ⊤ ⊥) : Nat.card U = 2 ^ 12 := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  have h1 := Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
  have h2 : Nat.card ↥(⊤ : Subgroup (Multiplicative U)) = Nat.card U :=
    (Nat.card_congr Subgroup.topEquiv.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  have h3 : Nat.card (↥(FFModel.nat hatM22Γ₀).sec ⧸
      ((FFModel.nat hatM22Γ₀).ker.subgroupOf (FFModel.nat hatM22Γ₀).sec)) = 2 ^ 12 := by
    change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 6 → FieldFour))) ⧸
      ((⊥ : Subgroup (Multiplicative (Fin 6 → FieldFour))).subgroupOf ⊤)) = 2 ^ 12
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fin, CFSG.CharacterTheory.SteinbergBY.FieldFour.natCard_eq]
    norm_num
  rw [← h2, h1, h3]

@[expose] noncomputable def kerTrace (θ : U ≃ₗ[ZMod 2] U) : Submodule (ZMod 2) U :=
  LinearMap.ker ((1 : U →ₗ[ZMod 2] U) + (θ : U →ₗ[ZMod 2] U) +
    (θ : U →ₗ[ZMod 2] U) ∘ₗ (θ : U →ₗ[ZMod 2] U))

theorem mem_kerTrace {θ : U ≃ₗ[ZMod 2] U} {v : U} : v ∈ kerTrace θ ↔ v + θ v + θ (θ v) = 0 :=
  Iff.rfl

theorem apply_mem_kerTrace {θ g : U ≃ₗ[ZMod 2] U} (hc : g * θ = θ * g) {v : U}
    (hv : v ∈ kerTrace θ) : g v ∈ kerTrace θ := by
  rw [mem_kerTrace] at hv ⊢
  have h1 : ∀ x, g (θ x) = θ (g x) := fun x => LinearEquiv.congr_fun hc x
  rw [← h1, ← h1, ← map_add, ← map_add, hv, map_zero]

theorem eq_zero_of_mem_kerTrace {θ : U ≃ₗ[ZMod 2] U} {v : U} (hv : v ∈ kerTrace θ)
    (hfix : θ v = v) : v = 0 := by
  rw [mem_kerTrace, hfix, hfix, ZModModule.add_self, zero_add] at hv
  exact hv

theorem kerTrace_ne_bot {θ : U ≃ₗ[ZMod 2] U} (h3 : θ ^ 3 = 1) (h1 : θ ≠ 1) : kerTrace θ ≠ ⊥ := by
  obtain ⟨u, hu⟩ : ∃ u, θ u ≠ u := by
    by_contra h
    push Not at h
    exact h1 (LinearEquiv.ext h)
  have h3' : ∀ x, θ (θ (θ x)) = x := fun x => by
    have := LinearEquiv.congr_fun h3 x
    simpa [pow_three, LinearEquiv.mul_apply] using this
  intro hbot
  have hmem : u + θ u ∈ kerTrace θ := by
    rw [mem_kerTrace, map_add, map_add, h3']
    have hx : ∀ x : U, x + x = 0 := fun x => ZModModule.add_self x
    calc u + θ u + (θ u + θ (θ u)) + (θ (θ u) + u)
        = (u + u) + (θ u + θ u) + (θ (θ u) + θ (θ u)) := by abel
      _ = 0 := by rw [hx u, hx (θ u), hx (θ (θ u)), add_zero, add_zero]
  rw [hbot, Submodule.mem_bot] at hmem
  apply hu
  have := congrArg (· + θ u) hmem
  simp only [zero_add] at this
  rw [add_assoc, ZModModule.add_self, add_zero] at this
  exact this.symm

variable [Finite U]

theorem exists_minimal_inv (L : Subgroup (U ≃ₗ[ZMod 2] U)) {W : Submodule (ZMod 2) U}
    (hW0 : W ≠ ⊥) (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) :
    ∃ W' : Submodule (ZMod 2) U, W' ≤ W ∧ W' ≠ ⊥ ∧ (∀ g ∈ L, ∀ w ∈ W', g w ∈ W') ∧
      ∀ J : Submodule (ZMod 2) U, J ≤ W' → J ≠ ⊥ → (∀ g ∈ L, ∀ w ∈ J, g w ∈ J) → J = W' := by
  classical
  set S : Set (Submodule (ZMod 2) U) :=
    {J | J ≤ W ∧ J ≠ ⊥ ∧ ∀ g ∈ L, ∀ w ∈ J, g w ∈ J} with hS
  have hne : S.Nonempty := ⟨W, le_rfl, hW0, hW⟩
  obtain ⟨W', ⟨hW'W, hW'0, hW'inv⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hne
  refine ⟨W', hW'W, hW'0, hW'inv, fun J hJ hJ0 hJinv => ?_⟩
  by_contra hne'
  exact hmin J ⟨hJ.trans hW'W, hJ0, hJinv⟩ (lt_of_le_of_ne hJ hne')

theorem eq_top_of_fixedPointFree (hHat : HatM22SmallModules) (hU : finrank (ZMod 2) U = 12)
    (L : Subgroup (U ≃ₗ[ZMod 2] U)) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {W : Submodule (ZMod 2) U} (hW0 : W ≠ ⊥) (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W)
    (hfpf : ∀ θ ∈ center ↥L, θ ≠ 1 → ∀ w ∈ W, ((θ : ↥L) : U ≃ₗ[ZMod 2] U) w = w → w = 0) :
    W = ⊤ := by
  obtain ⟨W', hW'W, hW'0, hW'inv, hmin⟩ := exists_minimal_inv L hW0 hW
  set f := restrictHom L W' hW'inv with hf
  have hW'nz : ∃ w ∈ W', w ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hW'0
  have htriv : ∀ θ : ↥L, θ ∈ f.ker → θ ∈ center ↥L → θ = 1 := by
    intro θ hθK hθZ
    by_contra hθ1
    obtain ⟨w, hw, hw0⟩ := hW'nz
    apply hw0
    refine hfpf θ hθZ hθ1 w (hW'W hw) ?_
    have := LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hθK) ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro θ hθ
    have hθK : θ ∈ f.ker := hθ
    rcases le_center_or_eq_top_of_isQuasisimple hL.1 f.ker with hc | htop
    · exact htriv θ hθK (hc hθK)
    · exfalso
      have hcard : Nat.card (center ↥L) = 3 := hL.2.1
      obtain ⟨θ', hθ'Z, hθ'1⟩ : ∃ θ' ∈ center ↥L, θ' ≠ 1 := by
        by_contra h
        push Not at h
        have : center ↥L = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
        rw [this, Subgroup.card_bot] at hcard
        omega
      exact hθ'1 (htriv θ' (htop ▸ Subgroup.mem_top θ') hθ'Z)
  have hmapinj := Submodule.map_injective_of_injective (f := W'.subtype) W'.injective_subtype
  have hirr : ∀ J : Submodule (ZMod 2) ↥W', (∀ g ∈ f.range, ∀ w ∈ J, g w ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hJinv : ∀ g ∈ L, ∀ w ∈ J.map W'.subtype, g w ∈ J.map W'.subtype := by
      rintro g hg _ ⟨w, hw, rfl⟩
      exact ⟨f ⟨g, hg⟩ w, hJ _ ⟨⟨g, hg⟩, rfl⟩ w hw, rfl⟩
    by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · right
      have hJ0' : J.map W'.subtype ≠ ⊥ := by
        intro h
        apply hJ0
        apply hmapinj
        rw [h, Submodule.map_bot]
      have heq := hmin (J.map W'.subtype) (Submodule.map_subtype_le W' J) hJ0' hJinv
      apply hmapinj
      rw [heq, Submodule.map_subtype_top]
  have hHatW : IsHat ↥f.range (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv (MonoidHom.ofInjective hinj) hL
  haveI : Nontrivial ↥W' := Submodule.nontrivial_iff_ne_bot.mpr hW'0
  haveI : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hcardU : Nat.card U = 2 ^ 12 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hU]
  have hcardW : Nat.card ↥W' < 2 ^ 30 := by
    calc Nat.card ↥W' ≤ Nat.card U := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 2 ^ 12 := hcardU
      _ < 2 ^ 30 := by norm_num
  have hc := card_eq_of_realizes (realizes_of_irr hHat f.range hHatW hirr hcardW)
  have hW'top : W' = ⊤ := by
    have h1 : (W'.toAddSubgroup) = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      rw [hcardU]
      exact hc
    exact Submodule.toAddSubgroup_injective (h1.trans Submodule.top_toAddSubgroup.symm)
  exact top_le_iff.mp (hW'top ▸ hW'W)

theorem center_fixedPointFree (hHat : HatM22SmallModules) (hU : finrank (ZMod 2) U = 12)
    (L : Subgroup (U ≃ₗ[ZMod 2] U)) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {θ : ↥L} (hθZ : θ ∈ center ↥L) (hθ1 : θ ≠ 1) (v : U)
    (hv : ((θ : ↥L) : U ≃ₗ[ZMod 2] U) v = v) : v = 0 := by
  have hcard : Nat.card (center ↥L) = 3 := hL.2.1
  haveI : Finite (U ≃ₗ[ZMod 2] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod 2] U => (e : U → U)) DFunLike.coe_injective
  have hθ3 : θ ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨θ, hθZ⟩)
    rw [hcard] at h
    exact congrArg Subtype.val h
  have hθ3' : ((θ : ↥L) : U ≃ₗ[ZMod 2] U) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hθ3, Subgroup.coe_one]
  have hθ1' : ((θ : ↥L) : U ≃ₗ[ZMod 2] U) ≠ 1 := fun h => hθ1 (Subtype.ext h)
  have hZ : ∀ η ∈ center ↥L, η = 1 ∨ η = θ ∨ η = θ ^ 2 := by
    intro η hη
    have hcyc : ∀ η ∈ center ↥L, η ∈ zpowers θ := by
      intro η hη
      have hle : zpowers θ ≤ center ↥L := (zpowers_le).mpr hθZ
      have hord : orderOf θ = 3 := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact orderOf_eq_prime hθ3 hθ1
      have hceq : (zpowers θ).subgroupOf (center ↥L) = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hord,
          hcard]
      have : (⟨η, hη⟩ : ↥(center ↥L)) ∈ (zpowers θ).subgroupOf (center ↥L) := hceq ▸ trivial
      exact this
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hcyc η hη)
    have hord : orderOf θ = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hθ3 hθ1
    have : θ ^ k = θ ^ (k % 3) := by
      rw [← zpow_mod_orderOf, hord]
      rfl
    rw [this]
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    interval_cases (k % 3)
    · left; simp
    · right; left; simp
    · right; right; simp
  set W := kerTrace ((θ : ↥L) : U ≃ₗ[ZMod 2] U) with hW
  have hWinv : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    refine apply_mem_kerTrace ?_ hw
    have := Subgroup.mem_center_iff.mp hθZ ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hfpf : ∀ η ∈ center ↥L, η ≠ 1 → ∀ w ∈ W, ((η : ↥L) : U ≃ₗ[ZMod 2] U) w = w → w = 0 := by
    intro η hη hη1 w hw hfix
    rcases hZ η hη with rfl | rfl | rfl
    · exact absurd rfl hη1
    · exact eq_zero_of_mem_kerTrace hw hfix
    ·
      refine eq_zero_of_mem_kerTrace hw ?_
      have h2 : ((θ : ↥L) : U ≃ₗ[ZMod 2] U) (((θ : ↥L) : U ≃ₗ[ZMod 2] U) w) = w := by
        have := hfix
        simpa [pow_two, LinearEquiv.mul_apply] using this
      have h3 := LinearEquiv.congr_fun hθ3' w
      simp only [pow_three, LinearEquiv.mul_apply] at h3
      change ((θ : ↥L) : U ≃ₗ[ZMod 2] U) (((θ : ↥L) : U ≃ₗ[ZMod 2] U)
        (((θ : ↥L) : U ≃ₗ[ZMod 2] U) w)) = w at h3
      rw [h2] at h3
      exact h3
  have htop := eq_top_of_fixedPointFree hHat hU L hL (kerTrace_ne_bot hθ3' hθ1') hWinv hfpf
  have hvW : v ∈ W := by
    rw [hW, htop]
    exact Submodule.mem_top
  exact eq_zero_of_mem_kerTrace hvW hv

theorem eq_top_of_inv (hHat : HatM22SmallModules) (hU : finrank (ZMod 2) U = 12)
    (L : Subgroup (U ≃ₗ[ZMod 2] U)) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {W : Submodule (ZMod 2) U} (hW0 : W ≠ ⊥) (hW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) : W = ⊤ :=
  eq_top_of_fixedPointFree hHat hU L hL hW0 hW fun _ hθZ hθ1 w _ hfix =>
    center_fixedPointFree hHat hU L hL hθZ hθ1 w hfix

theorem exists_hatM22_realization (hHat : HatM22SmallModules) (hU : finrank (ZMod 2) U = 12)
    (L : Subgroup (U ≃ₗ[ZMod 2] U)) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    ∃ ψ : U ≃+ (Fin 6 → FieldFour),
      (∀ g ∈ L, ∃ γ ∈ hatM22Γ₀, ∀ v : U, ψ (g v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour).mulVec
          (ψ v)) ∧
      (∀ γ ∈ hatM22Γ₀, ∃ g ∈ L, ∀ v : U, ψ (g v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour).mulVec
          (ψ v)) := by
  haveI : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hcardU : Nat.card U = 2 ^ 12 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hU]
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hU]; norm_num)
  have hirr : ∀ W : Submodule (ZMod 2) U, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (eq_top_of_inv hHat hU L hL h0 hW)
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ :=
    realizes_of_irr hHat L hL hirr (by rw [hcardU]; norm_num)
  set q : ↥(⊤ : Subgroup (Multiplicative (Fin 6 → FieldFour))) ⧸
      ((⊥ : Subgroup (Multiplicative (Fin 6 → FieldFour))).subgroupOf ⊤) ≃*
        Multiplicative (Fin 6 → FieldFour) :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf ⊤)).trans
      ((QuotientGroup.quotientBot).trans Subgroup.topEquiv) with hq
  have hqmk : ∀ m : ↥(⊤ : Subgroup (Multiplicative (Fin 6 → FieldFour))),
      q (QuotientGroup.mk m) = (m : Multiplicative (Fin 6 → FieldFour)) := fun _ => rfl
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let b0 : Multiplicative U →* Multiplicative (Fin 6 → FieldFour) :=
    q.toMonoidHom.comp (β.comp (Subgroup.topEquiv.symm.toMonoidHom))
  have hb0 : Function.Bijective b0 :=
    ⟨q.injective.comp (hβinj.comp Subgroup.topEquiv.symm.injective),
      q.surjective.comp (hβs.comp Subgroup.topEquiv.symm.surjective)⟩
  set be := MulEquiv.ofBijective b0 hb0 with hbe
  have hint : ∀ (γ : (FFModel.nat hatM22Γ₀).Gam) (x : Multiplicative U),
      be (((π γ : ↥(L.map (toMulAutHom U))) : MulAut (Multiplicative U)) x) =
        (FFModel.nat hatM22Γ₀).act γ (be x) := by
    intro γ x
    have hu : β ⟨x, Subgroup.mem_top x⟩ = QuotientGroup.mk ⟨be x, Subgroup.mem_top _⟩ := by
      apply q.injective
      rfl
    have := hβe γ ⟨x, Subgroup.mem_top x⟩ ⟨be x, Subgroup.mem_top _⟩ (Subgroup.mem_top _)
      (Subgroup.mem_top _) hu
    change q (β ⟨_, Subgroup.mem_top _⟩) = _
    rw [this]
    rfl
  let ψ : U ≃+ (Fin 6 → FieldFour) := AddEquiv.toMultiplicative.symm be
  let toGam : ↥hatM22Γ₀ → (FFModel.nat hatM22Γ₀).Gam := id
  have hψ : ∀ (γ : ↥hatM22Γ₀) (g : U ≃ₗ[ZMod 2] U),
      toMulAutHom U g = ((π (toGam γ) : ↥(L.map (toMulAutHom U))) : MulAut (Multiplicative U)) →
        ∀ v : U, ψ (g v) =
          ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour).mulVec
            (ψ v) := by
    intro γ g hg v
    have h1 : Multiplicative.ofAdd (g v) =
        ((π (toGam γ) : ↥(L.map (toMulAutHom U))) : MulAut (Multiplicative U))
          (Multiplicative.ofAdd v) := by
      rw [← hg, toMulAutHom_apply]
    change Multiplicative.toAdd (be (Multiplicative.ofAdd (g v))) = _
    rw [h1, hint]
    rfl
  refine ⟨ψ, fun g hg => ?_, fun γ hγ => ?_⟩
  · obtain ⟨γ, hγ⟩ := hπs ⟨toMulAutHom U g, ⟨g, hg, rfl⟩⟩
    let γ' : ↥hatM22Γ₀ := γ
    exact ⟨γ'.1, γ'.2, hψ γ' g (congrArg Subtype.val hγ).symm⟩
  · obtain ⟨g, hg, hgγ⟩ := (π (toGam ⟨γ, hγ⟩)).2
    exact ⟨g, hg, hψ ⟨γ, hγ⟩ g hgγ⟩

end CFSG.Quasithin.H13.AS91
