module

public import CFSG.Milestones.ASVolI.B4Ext.IVb
public import CFSG.Milestones.ASVolI.B4Ext.Parab

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section PreWCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

theorem burnsideB49x_mem_preW {Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)}
    {g : MulAut V} :
    g ∈ burnsideB49x_preW hV U G hG Q ↔ ∃ h : g ∈ G, burnsideB49_iota hV U G hG ⟨g, h⟩ ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hQ⟩
    exact ⟨⟨g, h⟩, hQ, rfl⟩

theorem burnsideB49x_iota_mem_of_mem_preW
    {Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)} {g : MulAut V}
    (hg : g ∈ burnsideB49x_preW hV U G hG Q) :
    burnsideB49_iota hV U G hG ⟨g, burnsideB49x_preW_le hV U G hG Q hg⟩ ∈ Q := by
  obtain ⟨y, hy, rfl⟩ := hg
  exact hy

theorem burnsideB49x_preW_mono
    {Q Q' : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)} (h : Q ≤ Q') :
    burnsideB49x_preW hV U G hG Q ≤ burnsideB49x_preW hV U G hG Q' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem burnsideB49x_preW_inf (Q Q' : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    burnsideB49x_preW hV U G hG (Q ⊓ Q') =
      burnsideB49x_preW hV U G hG Q ⊓ burnsideB49x_preW hV U G hG Q' := by
  unfold burnsideB49x_preW
  rw [Subgroup.comap_inf, Subgroup.map_inf_eq _ _ _ (Subgroup.subtype_injective G)]

theorem burnsideB49x_preW_bot (hinj : Function.Injective (burnsideB49_iota hV U G hG)) :
    burnsideB49x_preW hV U G hG ⊥ = ⊥ := by
  unfold burnsideB49x_preW
  rw [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).2 hinj, Subgroup.map_bot]

theorem burnsideB49x_preW_sup (hsurj : Function.Surjective (burnsideB49_iota hV U G hG))
    (Q Q' : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    burnsideB49x_preW hV U G hG (Q ⊔ Q') =
      burnsideB49x_preW hV U G hG Q ⊔ burnsideB49x_preW hV U G hG Q' := by
  unfold burnsideB49x_preW
  rw [← Subgroup.comap_sup_eq (burnsideB49_iota hV U G hG) Q Q' hsurj, Subgroup.map_sup]

@[expose] noncomputable def burnsideB49x_preWHom
    (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    ↥(burnsideB49x_preW hV U G hG Q) →* ↥Q :=
  ((burnsideB49_iota hV U G hG).comp
    (Subgroup.inclusion (burnsideB49x_preW_le hV U G hG Q))).codRestrict Q
    (fun x => burnsideB49x_iota_mem_of_mem_preW hV U G hG x.2)

theorem burnsideB49x_preWHom_apply
    (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U))
    (x : ↥(burnsideB49x_preW hV U G hG Q)) :
    ((burnsideB49x_preWHom hV U G hG Q x : ↥Q) : burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) =
      burnsideB49_iota hV U G hG ⟨x.1, burnsideB49x_preW_le hV U G hG Q x.2⟩ := rfl

theorem burnsideB49x_preWHom_bijective (hbij : Function.Bijective (burnsideB49_iota hV U G hG))
    (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    Function.Bijective (burnsideB49x_preWHom hV U G hG Q) := by
  refine ⟨fun x y hxy => ?_, fun q => ?_⟩
  · have h1 : burnsideB49_iota hV U G hG ⟨x.1, burnsideB49x_preW_le hV U G hG Q x.2⟩ =
        burnsideB49_iota hV U G hG ⟨y.1, burnsideB49x_preW_le hV U G hG Q y.2⟩ := by
      rw [← burnsideB49x_preWHom_apply, ← burnsideB49x_preWHom_apply, hxy]
    have h2 := hbij.1 h1
    exact Subtype.ext (congrArg (fun z : ↥G => (z : MulAut V)) h2)
  · obtain ⟨y, hy⟩ := hbij.2 q
    have hmem : (y : MulAut V) ∈ burnsideB49x_preW hV U G hG Q := by
      refine (burnsideB49x_mem_preW hV U G hG).2 ⟨y.2, ?_⟩
      rw [hy]
      exact q.2
    refine ⟨⟨y, hmem⟩, Subtype.ext ?_⟩
    rw [burnsideB49x_preWHom_apply]
    exact hy

theorem burnsideB49x_pCoreOf_preW (hbij : Function.Bijective (burnsideB49_iota hV U G hG))
    (Q : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)) :
    CFSG.Open.pCoreOf 2 (burnsideB49x_preW hV U G hG Q) =
      burnsideB49x_preW hV U G hG (CFSG.Open.pCoreOf 2 Q) := by
  set e := MulEquiv.ofBijective (burnsideB49x_preWHom hV U G hG Q)
    (burnsideB49x_preWHom_bijective hV U G hG hbij Q) with he
  have hmap : (CFSG.pCore 2 ↥(burnsideB49x_preW hV U G hG Q)).map e.toMonoidHom =
      CFSG.pCore 2 ↥Q := CFSG.pCore_map_iso 2 e
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine (burnsideB49x_mem_preW hV U G hG).2 ⟨burnsideB49x_preW_le hV U G hG Q x.2, ?_⟩
    have hex : e x ∈ CFSG.pCore 2 ↥Q := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    exact Subgroup.mem_map.2 ⟨e x, hex, burnsideB49x_preWHom_apply hV U G hG Q x⟩
  · intro hg
    obtain ⟨hgG, y, hy, hyeq⟩ := (burnsideB49x_mem_preW hV U G hG).1 hg
    have hyeq' : (y : burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) =
        burnsideB49_iota hV U G hG ⟨g, hgG⟩ := hyeq
    have hgP : g ∈ burnsideB49x_preW hV U G hG Q := by
      refine (burnsideB49x_mem_preW hV U G hG).2 ⟨hgG, ?_⟩
      rw [← hyeq']
      exact y.2
    refine ⟨⟨g, hgP⟩, ?_, rfl⟩
    have hey : e ⟨g, hgP⟩ = y := by
      apply Subtype.ext
      rw [hyeq']
      exact burnsideB49x_preWHom_apply hV U G hG Q ⟨g, hgP⟩
    have hy' : y ∈ CFSG.pCore 2 ↥Q := hy
    rw [← hmap, Subgroup.mem_map_equiv, ← hey, MulEquiv.symm_apply_apply] at hy'
    exact hy'

end PreWCore

section PsiBij

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49x_psi_bijective (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (φ : V ⧸ U ≃* DualGrp ↥U) : Function.Bijective (burnsideB49x_psi hV U φ) := by
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  haveI : Finite (Dual (ZMod 2) (burnsideB49_W hV U)) := Module.finite_of_finite (ZMod 2)
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = n := burnsideB49_finrank_W hV hK hreal hquot
  have hcardU : Nat.card ↥U = Nat.card (Dual (ZMod 2) (burnsideB49_W hV U)) := by
    rw [burnsideB49_card_U hreal, hK, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Subspace.dual_finrank_eq, hn]
  exact (Nat.bijective_iff_injective_and_card _).2 ⟨burnsideB49x_psi_injective hV U φ, hcardU⟩

end PsiBij

section StabCorr

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (φ : V ⧸ U ≃* DualGrp ↥U)

include hV hG in
theorem burnsideB49x_mem_stabSub_iff
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    (u₀ : ↥U) (g : ↥G) :
    (g : MulAut V) ∈ stabSub (Subgroup.zpowers (u₀ : V)) ↔
      burnsideB49_iota hV U G hG g ∈ burnsideB49_stab (burnsideB49x_psi hV U φ u₀) := by
  rw [mem_stabSub, burnsideB49_mem_stab]
  have key : (g : MulAut V) u₀ = u₀ ↔ ∀ x, burnsideB49x_psi hV U φ u₀
      (burnsideB49_iota hV U G hG g x) = burnsideB49x_psi hV U φ u₀ x := by
    constructor
    · intro h x
      have h1 := burnsideB49x_psi_equiv hV U G hG φ hφ g u₀ (burnsideB49_iota hV U G hG g x)
      rw [LinearEquiv.symm_apply_apply] at h1
      have h2 : (⟨(g : MulAut V) u₀, hG g g.2 u₀ u₀.2⟩ : ↥U) = u₀ := Subtype.ext h
      rw [h2] at h1
      exact h1
    · intro h
      have hψ : burnsideB49x_psi hV U φ ⟨(g : MulAut V) u₀, hG g g.2 u₀ u₀.2⟩ =
          burnsideB49x_psi hV U φ u₀ := by
        ext w
        rw [burnsideB49x_psi_equiv hV U G hG φ hφ g u₀ w]
        have := h ((burnsideB49_iota hV U G hG g).symm w)
        rw [LinearEquiv.apply_symm_apply] at this
        exact this.symm
      exact congrArg (fun z : ↥U => (z : V)) (burnsideB49x_psi_injective hV U φ hψ)
  rw [← key]
  constructor
  · intro h
    have hmem : (g : MulAut V) u₀ ∈ Subgroup.zpowers (u₀ : V) := (h u₀).2 (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk2 : (u₀ : V) ^ k = (u₀ : V) ^ (k % 2) := by
      have := zpow_eq_zpow_emod' (x := (u₀ : V)) k (n := 2) (hV u₀)
      simpa only [Nat.cast_ofNat] using this
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk2, h0, zpow_zero] at hk
      have hu : (u₀ : V) = 1 := by
        have h' : (g : MulAut V) u₀ = (g : MulAut V) 1 := by rw [← hk, map_one]
        exact (g : MulAut V).injective h'
      rw [hu, map_one]
    · rw [hk2, h1, zpow_one] at hk
      exact hk.symm
  · intro h v
    constructor
    · intro hv
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
      have hv' : v = (u₀ : V) ^ k := by
        apply (g : MulAut V).injective
        rw [map_zpow, h, hk]
      rw [hv']
      exact Subgroup.zpow_mem_zpowers _ _
    · intro hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [map_zpow, h]
      exact Subgroup.zpow_mem_zpowers _ _

include hV hG in
theorem burnsideB49x_stabSub_eq_preW
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    (u₀ : ↥U) :
    G ⊓ stabSub (Subgroup.zpowers (u₀ : V)) =
      burnsideB49x_preW hV U G hG (burnsideB49_stab (burnsideB49x_psi hV U φ u₀)) := by
  ext g
  rw [Subgroup.mem_inf, burnsideB49x_mem_preW]
  constructor
  · rintro ⟨hg, hs⟩
    exact ⟨hg, (burnsideB49x_mem_stabSub_iff hV U G hG φ hφ u₀ ⟨g, hg⟩).1 hs⟩
  · rintro ⟨hg, hs⟩
    exact ⟨hg, (burnsideB49x_mem_stabSub_iff hV U G hG φ hφ u₀ ⟨g, hg⟩).2 hs⟩

include hV hG in
theorem burnsideB49x_isLevi (hbij : Function.Bijective (burnsideB49_iota hV U G hG))
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    (u₀ : ↥U) {w₀ : burnsideB49_W hV U} (hw₀ : burnsideB49x_psi hV U φ u₀ w₀ = 1) :
    CFSG.ASVolI.ChB.IsLeviComplement (G ⊓ stabSub (Subgroup.zpowers (u₀ : V)))
      (burnsideB49x_preW hV U G hG (burnsideB49_K (burnsideB49x_psi hV U φ u₀) w₀)) := by
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  rw [burnsideB49x_stabSub_eq_preW hV U G hG φ hφ u₀]
  have hcore : CFSG.Open.pCoreOf 2 (burnsideB49x_preW hV U G hG
      (burnsideB49_stab (burnsideB49x_psi hV U φ u₀))) =
      burnsideB49x_preW hV U G hG (burnsideB49x_par_R (burnsideB49x_psi hV U φ u₀)) := by
    rw [burnsideB49x_pCoreOf_preW hV U G hG hbij]
    congr 1
    exact burnsideB49x_par_pCore_eq _
  unfold CFSG.ASVolI.ChB.IsLeviComplement
  rw [hcore]
  refine ⟨burnsideB49x_preW_mono hV U G hG (burnsideB49_K_le_stab _ w₀), ?_, ?_⟩
  · rw [← burnsideB49x_preW_inf, burnsideB49x_par_K_inf_R hw₀,
      burnsideB49x_preW_bot hV U G hG hbij.1]
  · rw [← burnsideB49x_preW_sup hV U G hG hbij.2, burnsideB49x_par_K_sup_R hw₀]

end StabCorr

section Rad

variable {V : Type} [CommGroup V]

@[expose] def burnsideB49x_radSub (U Y : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | (∀ u ∈ U, g u * u⁻¹ ∈ Y) ∧ ∀ y ∈ Y, g y = y}
  one_mem' := ⟨fun u _ => by rw [MulAut.one_apply, mul_inv_cancel]; exact Y.one_mem,
    fun y _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun u hu => ?_, fun y hy => ?_⟩
    · have e : (a * b) u * u⁻¹ = a (b u * u⁻¹) * (a u * u⁻¹) := by
        rw [MulAut.mul_apply, map_mul, map_inv]
        group
      rw [e, ha' _ (hb u hu)]
      exact Y.mul_mem (hb u hu) (ha u hu)
    · rw [MulAut.mul_apply, hb' y hy, ha' y hy]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have hinvY : ∀ y ∈ Y, a⁻¹ y = y := fun y hy => by
      conv_lhs => rw [← ha' y hy]
      exact MulAut.inv_apply_self V a y
    refine ⟨fun u hu => ?_, hinvY⟩
    have h1 := hinvY _ (ha u hu)
    rw [map_mul, map_inv, MulAut.inv_apply_self] at h1
    have h2 : a⁻¹ u * u⁻¹ = (a u * u⁻¹)⁻¹ := by
      rw [← h1]
      group
    rw [h2]
    exact Y.inv_mem (ha u hu)

theorem burnsideB49x_mem_radSub {U Y : Subgroup V} {g : MulAut V} :
    g ∈ burnsideB49x_radSub U Y ↔ (∀ u ∈ U, g u * u⁻¹ ∈ Y) ∧ ∀ y ∈ Y, g y = y := Iff.rfl

end Rad

section FiveClass

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {K : Type} [Field K]
  [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL 5 K) →* ↥G}

include hV in
theorem burnsideB49x_five_levi (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hlt : ¬ burnsideB49x_wfix (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A) ≤
      burnsideB49x_wcomm (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) :
    ∃ P M : Subgroup (MulAut V), CFSG.ASVolI.ChB.IsSubspaceStab G U 1 P ∧
      CFSG.ASVolI.ChB.IsLeviComplement P M ∧ A ≤ M := by
  set hG := burnsideB49_hG hreal with hGdef
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  have hbij := burnsideB49_iota_bijective hV hK hreal hquot
  set Â := burnsideB49x_hatW hV U G hG A with hÂ
  obtain ⟨w₀, hw₀C, hw₀Z⟩ := SetLike.not_le_iff_exists.1 hlt
  obtain ⟨f, hf0, hfZ⟩ := Submodule.exists_le_ker_of_notMem hw₀Z
  have hf1 : f w₀ = 1 := by
    have key : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact key _ hf0
  obtain ⟨φ, hφ⟩ := hdual
  obtain ⟨u₀, hu₀⟩ := (burnsideB49x_psi_bijective hV hK hreal hquot φ).2 f
  have hu₀1 : (u₀ : V) ≠ 1 := by
    intro h
    apply hf0
    have h1 : u₀ = 1 := Subtype.ext h
    rw [← hu₀, h1, burnsideB49x_psi_apply, map_one, toAdd_one]
  refine ⟨G ⊓ stabSub (Subgroup.zpowers (u₀ : V)),
    burnsideB49x_preW hV U G hG (burnsideB49_K f w₀),
    ⟨Subgroup.zpowers (u₀ : V), (Subgroup.zpowers_le).2 u₀.2, ?_, rfl⟩, ?_, ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime (hV u₀) hu₀1, pow_one]
  · have h := burnsideB49x_isLevi hV U G hG φ hbij hφ u₀ (w₀ := w₀) (by rw [hu₀]; exact hf1)
    rw [hu₀] at h
    exact h
  · intro a ha
    refine (burnsideB49x_mem_preW hV U G hG).2 ⟨hAG ha, fun x => ?_, ?_⟩
    · have hmem := burnsideB49x_sub_mem_wcomm (E := Â)
        (Subgroup.mem_map_of_mem (burnsideB49_iota hV U G hG)
          (show (⟨a, hAG ha⟩ : ↥G) ∈ A.subgroupOf G from ha)) x
      have h0 := hfZ hmem
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
      exact h0
    · exact hw₀C _ (Subgroup.mem_map_of_mem (burnsideB49_iota hV U G hG)
        (show (⟨a, hAG ha⟩ : ↥G) ∈ A.subgroupOf G from ha))

include hV in
theorem burnsideB49x_five_rad
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hq : burnsideB49x_wcomm (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A) ≤
      burnsideB49x_wfix (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) :
    A ≤ CFSG.Open.pCoreOf 2 (G ⊓ stabSub (fixV A ⊓ U)) := by
  set hG := burnsideB49_hG hreal with hGdef
  obtain ⟨φ, hφ⟩ := hdual
  set Y := fixV A ⊓ U with hY
  set P := G ⊓ stabSub Y with hP
  set N := P ⊓ burnsideB49x_radSub U Y with hN
  have hNP : N ≤ P := inf_le_left
  have hAN : A ≤ N := by
    intro a ha
    have hfixY : ∀ y ∈ Y, a y = y := fun y hy => (Subgroup.mem_inf.1 hy).1 a ha
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hAG ha, mem_stabSub.2 fun v => ⟨fun hv => ?_,
      fun hv => ?_⟩⟩, burnsideB49x_mem_radSub.2 ⟨fun u hu => ?_, hfixY⟩⟩
    · have h1 : a⁻¹ (a v) = a v := (Subgroup.mem_inf.1 hv).1 a⁻¹ (A.inv_mem ha)
      rw [MulAut.inv_apply_self] at h1
      rw [h1]
      exact hv
    · rw [hfixY v hv]
      exact hv
    · exact Subgroup.mem_inf.2 ⟨fun a' ha' =>
        burnsideB49x_quadU hV U G hG φ hφ hAG hq a ha a' ha' u hu,
        U.mul_mem (hG a (hAG ha) u hu) (U.inv_mem hu)⟩
  have hnorm : (N.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNP]
    intro h k hh hk
    obtain ⟨hhP, hhR⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hhU, hhY⟩ := burnsideB49x_mem_radSub.1 hhR
    obtain ⟨hkG, hkS⟩ := Subgroup.mem_inf.1 hk
    have hkS' := mem_stabSub.1 hkS
    refine Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hk hhP) (P.inv_mem hk),
      burnsideB49x_mem_radSub.2 ⟨fun u hu => ?_, fun y hy => ?_⟩⟩
    · have hu' : k⁻¹ u ∈ U := hG k⁻¹ (G.inv_mem hkG) u hu
      have h1 := (hkS' (h (k⁻¹ u) * (k⁻¹ u)⁻¹)).2 (hhU _ hu')
      rw [map_mul, map_inv, MulAut.apply_inv_self] at h1
      rw [MulAut.mul_apply, MulAut.mul_apply]
      exact h1
    · have hy' : k⁻¹ y ∈ Y := (hkS' (k⁻¹ y)).1 (by rw [MulAut.apply_inv_self]; exact hy)
      rw [MulAut.mul_apply, MulAut.mul_apply, hhY _ hy', MulAut.apply_inv_self]
  have hp : IsPGroup 2 (N.subgroupOf P) := by
    intro x
    refine ⟨1, ?_⟩
    have hxN : ((x : ↥P) : MulAut V) ∈ N := x.2
    obtain ⟨hxP, hxR⟩ := Subgroup.mem_inf.1 hxN
    obtain ⟨hxU, hxY⟩ := burnsideB49x_mem_radSub.1 hxR
    set g : MulAut V := ((x : ↥P) : MulAut V) with hgdef
    have hgG : g ∈ G := (Subgroup.mem_inf.1 hxP).1
    have hsq : (⟨g ^ 2, G.pow_mem hgG 2⟩ : ↥G) = 1 := by
      apply burnsideB49_faithfulU hreal
      intro u hu
      have hy := hxU u hu
      have hgy := hxY _ hy
      rw [map_mul, map_inv] at hgy
      show (g ^ 2) u = u
      rw [pow_two, MulAut.mul_apply]
      have h3 : g (g u) = g u * u⁻¹ * g u := by
        rw [← hgy]
        group
      rw [h3]
      have h2 := hV (g u * u⁻¹)
      rw [pow_two] at h2
      calc g u * u⁻¹ * g u = (g u * u⁻¹) * (g u * u⁻¹) * u := by group
        _ = u := by rw [h2, one_mul]
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact congrArg (fun z : ↥G => (z : MulAut V)) hsq
  have hle : N.subgroupOf P ≤ CFSG.pCore 2 ↥P := le_sSup ⟨hnorm, hp⟩
  intro a ha
  exact ⟨⟨a, hNP (hAN ha)⟩, hle (show (⟨a, hNP (hAN ha)⟩ : ↥P) ∈ N.subgroupOf P from hAN ha), rfl⟩

include hV in
theorem burnsideB49x_five_class (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 5 K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {T : Subgroup (MulAut V)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender T A) :
    (CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 16 ∧ ∃ P M : Subgroup (MulAut V),
        (CFSG.ASVolI.ChB.IsSubspaceStab G U 1 P ∨ CFSG.ASVolI.ChB.IsSubspaceStab G U 4 P) ∧
          CFSG.ASVolI.ChB.IsLeviComplement P M ∧ A ≤ M) ∨
      (CFSG.Open.IsElemAbelian 2 A ∧ (Nat.card A = 32 ∨ Nat.card A = 64) ∧
        ∃ P : Subgroup (MulAut V),
          (CFSG.ASVolI.ChB.IsSubspaceStab G U 2 P ∨ CFSG.ASVolI.ChB.IsSubspaceStab G U 3 P) ∧
            A ≤ CFSG.Open.pCoreOf 2 P) := by
  set hG := burnsideB49_hG hreal with hGdef
  have hAG' := burnsideB49x_offender_mono hT.1 hA
  have hAG : A ≤ G := hAG'.1
  have hel : IsElemAbelian2 A := hA.2.2.1
  obtain ⟨hquad, hcases, hlow, hup⟩ := burnsideB49x_five_quad hV hK hreal hdual hAG hel hAG'.2.1
    (burnsideB49x_offender_card hAG')
  have hEA : CFSG.Open.IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hel.1 a a.2 b b.2)⟩⟩, fun x hx => hel.2 x hx⟩
  have hBr : Nat.card A = 2 ^ rk A := B1.card_elemAbelian hel
  have hcardY := burnsideB49x_card_fixU_dual hV hK hreal hdual hAG
  have hrad := burnsideB49x_five_rad hV hreal hdual hAG hquad
  set c := finrank (ZMod 2) (burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A)) with hcdef
  set b := finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)) with hbdef
  have hrange : 2 ^ 5 ≤ Nat.card A → Nat.card A ≤ 2 ^ 6 →
      Nat.card A = 32 ∨ Nat.card A = 64 := by
    intro h1 h2
    rw [hBr] at h1 h2 ⊢
    have h1' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    have h2' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    rcases Nat.eq_or_lt_of_le h1' with h | h
    · left
      rw [← h]
      norm_num
    · right
      rw [show rk ↥A = 6 by omega]
      norm_num
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    left
    have h16 : Nat.card A = 16 := by
      rw [h1, h2] at hlow hup
      norm_num at hlow hup
      omega
    have hlt : ¬ burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A) ≤
        burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A) := by
      intro hle
      have := Submodule.finrank_mono hle
      omega
    obtain ⟨P, M, hP, hM, hAM⟩ := burnsideB49x_five_levi hV hK hreal hdual hAG hlt
    exact ⟨hEA, h16, P, M, Or.inl hP, hM, hAM⟩
  ·
    right
    refine ⟨hEA, ?_, G ⊓ stabSub (fixV A ⊓ U), Or.inl ⟨fixV A ⊓ U, inf_le_right, ?_, rfl⟩, hrad⟩
    · rw [h1, h2] at hlow hup
      exact hrange hlow hup
    · rw [hcardY, h2]
  ·
    right
    refine ⟨hEA, ?_, G ⊓ stabSub (fixV A ⊓ U), Or.inr ⟨fixV A ⊓ U, inf_le_right, ?_, rfl⟩, hrad⟩
    · rw [h1, h2] at hlow hup
      exact hrange hlow hup
    · rw [hcardY, h2]

end FiveClass

end CFSG.ASVolI
