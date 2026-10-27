module

public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Monster.Code CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

section L8213D

variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}

theorem card_V_of_cocode24_82 (h : MathieuCocode24 H ⊤ ⊥) : Nat.card V = 2 ^ 11 := by
  obtain ⟨e, -⟩ := cocode24_std h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp [W11, Fintype.card_multiplicative]

theorem card_of_rep_82 {W Γ : Type*} [CommGroup W] [Group Γ]
    {ρ : Γ →* MulAut W} (hρ : Function.Injective ρ) {e : V ≃* W}
    (he : H.map (congrHom e) = ρ.range) : Nat.card ↥H = Nat.card Γ := by
  rw [← Subgroup.card_map_of_injective (congrHom_injective e), he]
  exact Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv.symm

theorem normalizer_of_rep_82 {W : Type*} [CommGroup W]
    {R : Subgroup (MulAut W)} {e : V ≃* W} (he : H.map (congrHom e) = R)
    (hR : Subgroup.normalizer (R : Set (MulAut W)) = R) :
    Subgroup.normalizer (H : Set (MulAut V)) = H := by
  apply le_antisymm _ Subgroup.le_normalizer
  intro φ hφ
  have h1 : congrHom e φ ∈ Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut W)) :
      Set (MulAut W)) := Subgroup.le_normalizer_map (congrHom e) ⟨φ, hφ, rfl⟩
  rw [he, hR, ← he] at h1
  obtain ⟨ψ, hψ, hψφ⟩ := h1
  rwa [← congrHom_injective e hψφ]

theorem card_of_cocode24_82
    (h : MathieuCocode24 H ⊤ ⊥) : Nat.card ↥H = 244823040 := by
  obtain ⟨e, he⟩ := cocode24_std h
  rw [card_of_rep_82 (rho11_injective AutPerm le_rfl) he, card_AutPerm]

theorem normalizer_of_cocode24_82
    (h : MathieuCocode24 H ⊤ ⊥) : Subgroup.normalizer (H : Set (MulAut V)) = H := by
  obtain ⟨e, he⟩ := cocode24_std h
  exact normalizer_of_rep_82 he normalizer_rho11_autPerm

theorem coe_autPermEquivM24'_symm_82
    (g : ↥NativeSporadic.M24) :
    ((autPermEquivM24'.symm g : ↥AutPerm) : Equiv.Perm (Fin 24)) =
      bridgeQ⁻¹ * (g : Equiv.Perm (Fin 24)) * bridgeQ := by
  change bridgeQ⁻¹ * (g : Equiv.Perm (Fin 24)) * bridgeQ⁻¹⁻¹ = _
  rw [inv_inv]

@[expose] noncomputable def bridgeE82 : ↥(G6.coreMod 24) ≃* ↥(G6.coreMod 24) where
  toFun m := ⟨G6.permAct 24 bridgeQ (m : G6.PermMod 24), G6.permAct_mem_coreMod bridgeQ m.2⟩
  invFun m := ⟨G6.permAct 24 bridgeQ⁻¹ (m : G6.PermMod 24), G6.permAct_mem_coreMod bridgeQ⁻¹ m.2⟩
  left_inv m := by
    apply Subtype.ext
    change G6.permAct 24 bridgeQ⁻¹ (G6.permAct 24 bridgeQ (m : G6.PermMod 24)) = m
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  right_inv m := by
    apply Subtype.ext
    change G6.permAct 24 bridgeQ (G6.permAct 24 bridgeQ⁻¹ (m : G6.PermMod 24)) = m
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  map_mul' a b := Subtype.ext (map_mul (G6.permAct 24 bridgeQ) (a : G6.PermMod 24) b)

theorem coe_bridgeE82 (m : ↥(G6.coreMod 24)) :
    ((bridgeE82 m : ↥(G6.coreMod 24)) : G6.PermMod 24) =
      G6.permAct 24 bridgeQ (m : G6.PermMod 24) := rfl

theorem map_bridgeE82 (hC : golayC ≤ G6.coreMod 24) :
    (golayC.subgroupOf (G6.coreMod 24)).map (bridgeE82 : ↥(G6.coreMod 24) →* _) =
      nativeGolayC.subgroupOf (G6.coreMod 24) := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hx⟩, hxC, hxy⟩
    have hxC' : x ∈ golayC := hxC
    have h1 : G6.permAct 24 bridgeQ x = y := congrArg Subtype.val hxy
    exact ⟨x, hxC', h1⟩
  · rintro ⟨x, hxC, hxy⟩
    refine ⟨⟨x, hC hxC⟩, hxC, ?_⟩
    exact Subtype.ext hxy

@[expose] noncomputable def bridgeQuot82 (hC : golayC ≤ G6.coreMod 24) :
    ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24) ≃*
      ↥(G6.coreMod 24) ⧸ nativeGolayC.subgroupOf (G6.coreMod 24) :=
  QuotientGroup.congr _ _ bridgeE82 (map_bridgeE82 hC)

theorem bridgeQuot82_mk (hC : golayC ≤ G6.coreMod 24) (m : ↥(G6.coreMod 24)) :
    bridgeQuot82 hC (m : ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24)) =
      ((bridgeE82 m : ↥(G6.coreMod 24)) :
        ↥(G6.coreMod 24) ⧸ nativeGolayC.subgroupOf (G6.coreMod 24)) := rfl

theorem nativeCocode24_of_data_82 (π : ↥NativeSporadic.M24 →* ↥H) (hπ : Function.Surjective π)
    (β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸ nativeGolayC.subgroupOf (G6.coreMod 24))
    (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(⊤ : Subgroup V), β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V))
    (hC : nativeGolayC ≤ G6.coreMod 24)
    (hβ : ∀ (γ : ↥NativeSporadic.M24) (u : ↥(⊤ : Subgroup V)) (m : ↥(G6.coreMod 24))
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ (⊤ : Subgroup V))
      (hm : G6.permAct 24 (γ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24) ∈ G6.coreMod 24),
      β u = (m : ↥(G6.coreMod 24) ⧸ nativeGolayC.subgroupOf (G6.coreMod 24)) →
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          ((⟨G6.permAct 24 (γ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24), hm⟩ :
            ↥(G6.coreMod 24)) : ↥(G6.coreMod 24) ⧸ nativeGolayC.subgroupOf (G6.coreMod 24))) :
    NativeCocode24 H ⊤ ⊥ :=
  ⟨π, hπ, bot_le, hC, fun _ _ _ => trivial, fun _ _ hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one], fun _ _ hm => G6.permAct_mem_coreMod _ hm,
    fun γ _ hm => nativeGolayC_invariant γ.2 hm, β, hβs, hβk, hβ⟩

theorem nativeCocode24_of_82 (h : MathieuCocode24 H ⊤ ⊥) :
    NativeCocode24 H ⊤ ⊥ := by
  obtain ⟨π, hπs, -, hks, -, -, -, -, β, hβs, hβk, hβ⟩ := h
  have hC : golayC ≤ G6.coreMod 24 := hks
  let π₀ : ↥AutPerm →* ↥H := π
  have hπ₀ : Function.Surjective π₀ := hπs
  let β₀ : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24) := β
  have hβs₀ : Function.Surjective β₀ := hβs
  have hβk₀ : ∀ u : ↥(⊤ : Subgroup V), β₀ u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := hβk
  have hβ₀ : ∀ (σ : ↥AutPerm) (u : ↥(⊤ : Subgroup V)) (m : ↥(G6.coreMod 24))
      (hu : ((π₀ σ : ↥H) : MulAut V) (u : V) ∈ (⊤ : Subgroup V))
      (hm : G6.permAct 24 (σ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24) ∈ G6.coreMod 24),
      β₀ u = (m : ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24)) →
        β₀ ⟨((π₀ σ : ↥H) : MulAut V) (u : V), hu⟩ =
          ((⟨G6.permAct 24 (σ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24), hm⟩ :
            ↥(G6.coreMod 24)) : ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24)) := hβ
  set Φ := bridgeQuot82 hC with hΦdef
  have hnC : nativeGolayC ≤ G6.coreMod 24 := by
    rintro _ ⟨x, hx, rfl⟩
    exact G6.permAct_mem_coreMod bridgeQ (hC hx)
  refine nativeCocode24_of_data_82 (π₀.comp autPermEquivM24'.symm.toMonoidHom) ?_
    (Φ.toMonoidHom.comp β₀) ?_ ?_ hnC ?_
  · intro x
    obtain ⟨σ, rfl⟩ := hπ₀ x
    refine ⟨autPermEquivM24' σ, ?_⟩
    change π₀ (autPermEquivM24'.symm (autPermEquivM24' σ)) = π₀ σ
    rw [MulEquiv.symm_apply_apply]
  · intro y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    obtain ⟨u, rfl⟩ := hβs₀ x
    exact ⟨u, rfl⟩
  · intro u
    rw [← hβk₀ u]
    change Φ (β₀ u) = 1 ↔ β₀ u = 1
    rw [MulEquiv.map_eq_one_iff]
  · intro γ u m hu hm hum
    set σ := autPermEquivM24'.symm γ with hσ
    have hσγ : ((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) =
        bridgeQ⁻¹ * (γ : Equiv.Perm (Fin 24)) * bridgeQ :=
      coe_autPermEquivM24'_symm_82 γ
    set m₀ : ↥(G6.coreMod 24) := bridgeE82.symm m with hm₀
    have hum₀ : β₀ u = (m₀ : ↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24)) := by
      apply Φ.injective
      have h2 : Φ (β₀ u) = (m : ↥(G6.coreMod 24) ⧸ nativeGolayC.subgroupOf (G6.coreMod 24)) :=
        hum
      rw [h2, hΦdef, bridgeQuot82_mk, hm₀, MulEquiv.apply_symm_apply]
    have hm₀' : G6.permAct 24 (σ : Equiv.Perm (Fin 24)) (m₀ : G6.PermMod 24) ∈ G6.coreMod 24 :=
      G6.permAct_mem_coreMod _ m₀.2
    have h1 := hβ₀ σ u m₀ hu hm₀' hum₀
    change Φ (β₀ ⟨((π₀ σ : ↥H) : MulAut V) (u : V), hu⟩) = _
    rw [h1, hΦdef, bridgeQuot82_mk]
    congr 1
    apply Subtype.ext
    rw [coe_bridgeE82]
    change G6.permAct 24 bridgeQ (G6.permAct 24 (σ : Equiv.Perm (Fin 24))
      (G6.permAct 24 bridgeQ⁻¹ (m : G6.PermMod 24))) =
        G6.permAct 24 (γ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24)
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hσγ]
    congr 2
    group

end L8213D

end CFSG.Quasithin.H13
