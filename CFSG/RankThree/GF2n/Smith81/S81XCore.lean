module

public import CFSG.RankThree.GF2n.Smith81.S81BPos3
public import CFSG.RankThree.GF2n.Smith81.S81BConj
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas
public import CFSG.RankThree.GF2n.Smith81.S81BPos2
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.EGeom

section Model

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def SpecialAt (β : V →ₗ[K] V →ₗ[K] K) (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V))
    (g : V ≃ₗ[K] V) : Prop :=
  β p₀ (g p₀) = 0 ∧ g p₀ ∉ Wsp (Submodule.span K {p₀}) U₀

structure Fe2Geom (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V))
    (β : V →ₗ[K] V →ₗ[K] K) (n : ℕ) : Prop where
  geom : MinuscGeom Γ p₀ U₀ n
  β_inv : ∀ g ∈ Γ, ∀ v w : V, β (g v) (g w) = β v w
  β_skew : ∀ v w : V, β v w = - β w v
  U_card : Nat.card K ^ (n - 1) ≤ Nat.card U₀
  U_norm : ∀ h ∈ Γ, (∃ c : K, c ≠ 0 ∧ h p₀ = c • p₀) → conjSub h U₀ = U₀
  lemmaS : ∀ g ∈ Γ, SpecialAt β p₀ U₀ g → ∃ h₁ ∈ Γ, ∃ h₂ ∈ Γ,
    h₁ p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ ∧ h₂ p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ ∧
    g⁻¹ (h₁ p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ ∧ g⁻¹ (h₂ p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ ∧
    SpecialAt β p₀ U₀ (h₁⁻¹ * h₂)

variable {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}
  {β : V →ₗ[K] V →ₗ[K] K} {n : ℕ}

theorem Fe2Geom.mem_W0_iff (hG : Fe2Geom Γ p₀ U₀ β n) {s : V ≃ₗ[K] V} (hs : s ∈ Γ) {c : K}
    (hc : c ≠ 0) (hsp : s p₀ = c • p₀) (x : V) :
    s x ∈ Wsp (Submodule.span K {p₀}) U₀ ↔ x ∈ Wsp (Submodule.span K {p₀}) U₀ := by
  have hU : conjSub s U₀ = U₀ := hG.U_norm s hs ⟨c, hc, hsp⟩
  have hL : (Submodule.span K {p₀}).map (s : V →ₗ[K] V) = Submodule.span K {p₀} := by
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hsp]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _
  have hW := Wsp_map s (Submodule.span K {p₀}) U₀
  rw [hL, hU] at hW
  have h2 : s x ∈ (Wsp (Submodule.span K {p₀}) U₀).map (s : V →ₗ[K] V) ↔
      x ∈ Wsp (Submodule.span K {p₀}) U₀ := by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [← hW] at h2
  exact h2

theorem Fe2Geom.beta_inv_smul (hG : Fe2Geom Γ p₀ U₀ β n) {s : V ≃ₗ[K] V} (hs : s ∈ Γ) {c : K}
    (hsp : s p₀ = c • p₀) (x : V) : β p₀ (s⁻¹ x) = c * β p₀ x := by
  have hx : s (s⁻¹ x) = x := by
    rw [LinearEquiv.coe_inv]
    exact s.apply_symm_apply x
  have h := hG.β_inv s hs p₀ (s⁻¹ x)
  rw [hsp, hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact h.symm

theorem Fe2Geom.special_mul_iff (hG : Fe2Geom Γ p₀ U₀ β n) {s₁ s₂ Q : V ≃ₗ[K] V} (h₁ : s₁ ∈ Γ)
    (h₂ : s₂ ∈ Γ) {c₁ c₂ : K} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (e₁ : s₁ p₀ = c₁ • p₀)
    (e₂ : s₂ p₀ = c₂ • p₀) :
    SpecialAt β p₀ U₀ (s₁⁻¹ * Q * s₂) ↔ SpecialAt β p₀ U₀ Q := by
  have hP : (s₁⁻¹ * Q * s₂) p₀ = c₂ • s₁⁻¹ (Q p₀) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e₂, map_smul, map_smul]
  have hβP : β p₀ (c₂ • s₁⁻¹ (Q p₀)) = c₂ * (c₁ * β p₀ (Q p₀)) := by
    rw [map_smul, smul_eq_mul, hG.beta_inv_smul h₁ e₁]
  have hWP : c₂ • s₁⁻¹ (Q p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ ↔
      Q p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ := by
    refine (Submodule.smul_mem_iff _ hc₂).trans ?_
    have h := hG.mem_W0_iff h₁ hc₁ e₁ (s₁⁻¹ (Q p₀))
    have hx : s₁ (s₁⁻¹ (Q p₀)) = Q p₀ := by
      rw [LinearEquiv.coe_inv]
      exact s₁.apply_symm_apply _
    rw [hx] at h
    exact h.symm
  have hz : c₂ * (c₁ * β p₀ (Q p₀)) = 0 ↔ β p₀ (Q p₀) = 0 := by
    rw [mul_eq_zero, mul_eq_zero]
    constructor
    · rintro (h | h | h)
      · exact absurd h hc₂
      · exact absurd h hc₁
      · exact h
    · intro h
      exact Or.inr (Or.inr h)
  unfold SpecialAt
  rw [hP, hβP, hWP, hz]

theorem Fe2Geom.special_rel_point (hG : Fe2Geom Γ p₀ U₀ β n) {g₁ g₂ g₁' g₂' : V ≃ₗ[K] V}
    (h₁ : g₁ ∈ Γ) (h₂ : g₂ ∈ Γ) (h₁' : g₁' ∈ Γ) (h₂' : g₂' ∈ Γ) {c₁ c₂ : K} (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (e₁ : g₁' p₀ = c₁ • g₁ p₀) (e₂ : g₂' p₀ = c₂ • g₂ p₀) :
    SpecialAt β p₀ U₀ (g₁'⁻¹ * g₂') ↔ SpecialAt β p₀ U₀ (g₁⁻¹ * g₂) := by
  have hs₁ : g₁⁻¹ * g₁' ∈ Γ := Γ.mul_mem (Γ.inv_mem h₁) h₁'
  have hs₂ : g₂⁻¹ * g₂' ∈ Γ := Γ.mul_mem (Γ.inv_mem h₂) h₂'
  have hs₁p : (g₁⁻¹ * g₁') p₀ = c₁ • p₀ := by
    rw [LinearEquiv.mul_apply, e₁, map_smul, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hs₂p : (g₂⁻¹ * g₂') p₀ = c₂ • p₀ := by
    rw [LinearEquiv.mul_apply, e₂, map_smul, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hid : g₁'⁻¹ * g₂' = (g₁⁻¹ * g₁')⁻¹ * (g₁⁻¹ * g₂) * (g₂⁻¹ * g₂') := by group
  rw [hid]
  exact hG.special_mul_iff hs₁ hs₂ hc₁ hc₂ hs₁p hs₂p

end Model

end CFSG.RankThree.GF2n.Smith81.EGeom

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom

section FrameA

variable {G : Type} [Group G] [Finite G] {M Q A B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q A K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)} {β : V →ₗ[K] V →ₗ[K] K} {n : ℕ}

theorem fe2_common_collinear (hg : GlobalModelData M Q A γ M₀)
    (d : EUniData M Q A B M₀ ψ φ Γ p₀ U₀) (hG : Fe2Geom Γ p₀ U₀ β n) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f))
    (hcard : ∀ C : Subgroup G, Ctx M Q A C → Nat.card ↥(Q ⊓ QB C) = Nat.card A ^ (n + 1))
    (hBc : Ctx M Q A B) {Z X : Subgroup G} (hZc : Ctx M Q A Z) (hXc : Ctx M Q A X)
    (hpos : EPosM Z X) :
    ∃ D₁ D₂ : Subgroup G, Ctx M Q A D₁ ∧ Ctx M Q A D₂ ∧ D₁ ≤ QB Z ∧ D₂ ≤ QB Z ∧
      D₁ ≤ QB X ∧ D₂ ≤ QB X ∧ EPosM D₁ D₂ := by
  have hK : Nat.card K = Nat.card A := hg.card
  obtain ⟨gZ, hgZ⟩ := d.exists_isPt hZc
  obtain ⟨gX, hgX⟩ := d.exists_isPt hXc
  have hspec : SpecialAt β p₀ U₀ (gZ⁻¹ * gX) := by
    have h := (d.pos_classes hg hZc hXc hgZ hgX (hcard Z hZc) hG.geom.W_le hK hG.geom.p₀_ne
      hG.geom.U₀_fix hG.β_inv hG.β_skew hlam hform).2.2.1
    rw [h] at hpos
    exact hpos
  obtain ⟨h₁, hh₁, h₂, hh₂, hW₁, hW₂, hX₁, hX₂, hsp⟩ :=
    hG.lemmaS (gZ⁻¹ * gX) (Γ.mul_mem (Γ.inv_mem hgZ.1) hgX.1) hspec
  obtain ⟨D₁, hD₁, gD₁, hgD₁, c₁, hc₁, e₁⟩ := d.exists_ctx_with_class hBc hG.geom.p₀_ne hgZ hh₁
  obtain ⟨D₂, hD₂, gD₂, hgD₂, c₂, hc₂, e₂⟩ := d.exists_ctx_with_class hBc hG.geom.p₀_ne hgZ hh₂
  have hZmem : ∀ {D : Subgroup G} {gD h : V ≃ₗ[K] V} {c : K},
      Ctx M Q A D → d.IsPt D gD → gZ⁻¹ (gD p₀) = c • h p₀ →
      h p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ → D ≤ QB Z := by
    intro D gD h c hD hgD e hW
    refine ((d.le_QB_iff hZc hD hgZ hgD (hcard Z hZc) hG.geom.W_le hK hG.geom.p₀_ne
      hG.geom.U₀_fix)).mpr ?_
    rw [e]
    exact Submodule.smul_mem _ _ hW
  have hXmem : ∀ {D : Subgroup G} {gD h : V ≃ₗ[K] V} {c : K},
      Ctx M Q A D → d.IsPt D gD → gZ⁻¹ (gD p₀) = c • h p₀ →
      (gZ⁻¹ * gX)⁻¹ (h p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ → D ≤ QB X := by
    intro D gD h c hD hgD e hW
    refine ((d.le_QB_iff hXc hD hgX hgD (hcard X hXc) hG.geom.W_le hK hG.geom.p₀_ne
      hG.geom.U₀_fix)).mpr ?_
    have e2 : gX⁻¹ (gD p₀) = (gZ⁻¹ * gX)⁻¹ (c • h p₀) := by
      have e3 : gD p₀ = gZ (gZ⁻¹ (gD p₀)) := by
        rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
      have e4 : gD p₀ = gZ (c • h p₀) := e3.trans (congrArg gZ e)
      rw [mul_inv_rev, inv_inv, LinearEquiv.mul_apply, e4]
    rw [e2, map_smul]
    exact Submodule.smul_mem _ _ hW
  have hD₁Z := hZmem hD₁ hgD₁ e₁ hW₁
  have hD₂Z := hZmem hD₂ hgD₂ e₂ hW₂
  have hD₁X := hXmem hD₁ hgD₁ e₁ hX₁
  have hD₂X := hXmem hD₂ hgD₂ e₂ hX₂
  have hrel : ∀ {gD h : V ≃ₗ[K] V} {c : K}, gZ⁻¹ (gD p₀) = c • h p₀ →
      gD p₀ = c • (gZ * h) p₀ := by
    intro gD h c e
    have e3 : gD p₀ = gZ (gZ⁻¹ (gD p₀)) := by
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    rw [e3, e, map_smul, LinearEquiv.mul_apply]
  have hspD : SpecialAt β p₀ U₀ (gD₁⁻¹ * gD₂) := by
    refine (hG.special_rel_point (Γ.mul_mem hgZ.1 hh₁) (Γ.mul_mem hgZ.1 hh₂) hgD₁.1 hgD₂.1
      hc₁ hc₂ (hrel e₁) (hrel e₂)).mpr ?_
    rw [show (gZ * h₁)⁻¹ * (gZ * h₂) = h₁⁻¹ * h₂ by group]
    exact hsp
  have hpos' : EPosM D₁ D₂ := by
    have h := (d.pos_classes hg hD₁ hD₂ hgD₁ hgD₂ (hcard D₁ hD₁) hG.geom.W_le hK
      hG.geom.p₀_ne hG.geom.U₀_fix hG.β_inv hG.β_skew hlam hform).2.2.1
    rw [h]
    exact hspD
  exact ⟨D₁, D₂, hD₁, hD₂, hD₁Z, hD₂Z, hD₁X, hD₂X, hpos'⟩

end FrameA

section FrameZ

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)} {β : V →ₗ[K] V →ₗ[K] K} {n : ℕ}

theorem fe2_le_and_map_eq_of_radical {α β : Type} [Group α] [Finite α] [Group β]
    {L Q T : Subgroup α} {R : Subgroup β} (f : L →* β) (hf : ∀ s : L, f s = 1 ↔ (s : α) ∈ Q)
    (hQL : Q ≤ L) (hQT : Q ≤ T) (hsurj : ∀ u ∈ R, ∃ t : L, (t : α) ∈ T ∧ f t = u)
    (hcard : Nat.card ↥T ≤ Nat.card Q * Nat.card ↥R) :
    T ≤ L ∧ (T.subgroupOf L).map f = R := by
  have hQS : Q ≤ T ⊓ L := le_inf hQT hQL
  have hA := card_eq_card_mul_card_map_of_ker f hf hQL hQS inf_le_right
  have hRle : R ≤ ((T ⊓ L).subgroupOf L).map f := by
    intro u hu
    obtain ⟨t, htT, htf⟩ := hsurj u hu
    exact Subgroup.mem_map.mpr
      ⟨t, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨htT, t.2⟩), htf⟩
  haveI := finite_map_aux f ((T ⊓ L).subgroupOf L)
  have hle1 : Nat.card ↥T ≤ Nat.card ↥(T ⊓ L) := by
    rw [hA]
    exact hcard.trans (Nat.mul_le_mul le_rfl (Subgroup.card_le_of_le hRle))
  have hTL : T ⊓ L = T := Subgroup.eq_of_le_of_card_ge inf_le_left hle1
  have hTL' : T ≤ L := by
    rw [← hTL]
    exact inf_le_right
  rw [hTL] at hA hRle
  haveI := finite_map_aux f (T.subgroupOf L)
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hcardM : Nat.card ↥((T.subgroupOf L).map f) ≤ Nat.card ↥R := by
    refine Nat.le_of_mul_le_mul_left ?_ hQpos
    rw [← hA]
    exact hcard
  have hRM : R = (T.subgroupOf L).map f := Subgroup.eq_of_le_of_card_ge hRle hcardM
  exact ⟨hTL', hRM.symm⟩

theorem fe2_LB_le_Lgen_and_map_eq (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (hLM : LB M Q B ≤ M)
    {X : Subgroup G} {g : V ≃ₗ[K] V} (hX : d.IsPt X g) {m : ℕ}
    (hc : Nat.card ↥(LB M Q X) = Nat.card Q * Nat.card Z ^ (m - 1))
    (hU : Nat.card K ^ (m - 1) ≤ Nat.card U₀) (hK : Nat.card K = Nat.card Z) :
    LB M Q X ≤ Lgen M (LB M Q B) ∧
      ((LB M Q X).subgroupOf (Lgen M (LB M Q B))).map φ = conjSub g U₀ := by
  have hLM' : Lgen M (LB M Q B) ≤ M := CFSG.RankThree.GF2n.Stroth80.Lgen_le hLM
  have hQLB : Q ≤ LB M Q B := (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M))
  have hQL : Q ≤ Lgen M (LB M Q B) :=
    hQLB.trans (CFSG.RankThree.GF2n.Stroth80.le_Lgen_self M (LB M Q B))
  have hQX : Q ≤ LB M Q X := (le_sup_left : Q ≤ Q ⊔ (QB X ⊓ M))
  have hlift : ∀ u ∈ conjSub g U₀, ∃ t : Lgen M (LB M Q B), (t : G) ∈ LB M Q X ∧ φ t = u := by
    intro u hu
    obtain ⟨-, -, hrad⟩ := hX
    obtain ⟨t, htQB, htφ⟩ := hrad u hu
    refine ⟨t, ?_, htφ⟩
    have htM : (t : G) ∈ M := hLM' t.2
    exact (le_sup_right : QB X ⊓ M ≤ Q ⊔ (QB X ⊓ M)) (Subgroup.mem_inf.mpr ⟨htQB, htM⟩)
  have hRcard : Nat.card Z ^ (m - 1) ≤ Nat.card ↥(conjSub g U₀) := by
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom :=
      fun a b h => (MulAut.conj g).injective h
    unfold conjSub
    rw [Subgroup.card_map_of_injective hinj, ← hK]
    exact hU
  refine fe2_le_and_map_eq_of_radical φ d.ker hQL hQX hlift ?_
  rw [hc]
  exact Nat.mul_le_mul le_rfl hRcard

theorem fe2_radical_core (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (hG : Fe2Geom Γ p₀ U₀ β n) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f)) (hLM : LB M Q B ≤ M)
    (h35 : ∀ D : Subgroup G, Ctx M Q Z D →
      Nat.card ↥(LB M Q D) = Nat.card Q * Nat.card Z ^ (n - 1) ∧
        Nat.card ↥(Q ⊓ QB D) = Nat.card Z ^ (n + 1))
    {X : Subgroup G} {t : G} (hs : Sit M Q Z X t) {D₁ D₂ : Subgroup G} (hD₁ : Ctx M Q Z D₁)
    (hD₂ : Ctx M Q Z D₂) (hD₁X : D₁ ≤ QB X) (hD₂X : D₂ ≤ QB X) (hpos : EPosM D₁ D₂) :
    ∃ htL : t ∈ Lgen M (LB M Q B), ∃ g₁ g₂ : V ≃ₗ[K] V, g₁ ∈ Γ ∧ g₂ ∈ Γ ∧
      SpecialAt β p₀ U₀ (g₁⁻¹ * g₂) ∧ φ ⟨t, htL⟩ ∈ conjSub g₁ U₀ ⊓ conjSub g₂ U₀ ∧
        φ ⟨t, htL⟩ ≠ 1 := by
  have H : StrothHyp M Q Z := hs.hyp
  have hXz : IsZConjugate Z X := hs.conj
  have hK : Nat.card K = Nat.card Z := hg.card
  have htLB : ∀ D : Subgroup G, Ctx M Q Z D → D ≤ QB X → t ∈ LB M Q D := fun D hD hDX =>
    (le_sup_right : QB D ⊓ M ≤ Q ⊔ (QB D ⊓ M)) (Subgroup.mem_inf.mpr
      ⟨(IsZConjugate.le_QB_iff H hD.conj hXz).mpr hDX hs.mem, hs.memM⟩)
  obtain ⟨g₁, hg₁⟩ := d.exists_isPt hD₁
  obtain ⟨g₂, hg₂⟩ := d.exists_isPt hD₂
  obtain ⟨hL₁, hm₁⟩ := fe2_LB_le_Lgen_and_map_eq d hLM hg₁ (h35 D₁ hD₁).1 hG.U_card hK
  obtain ⟨-, hm₂⟩ := fe2_LB_le_Lgen_and_map_eq d hLM hg₂ (h35 D₂ hD₂).1 hG.U_card hK
  have htL : t ∈ Lgen M (LB M Q B) := hL₁ (htLB D₁ hD₁ hD₁X)
  have hφ₁ : φ ⟨t, htL⟩ ∈ conjSub g₁ U₀ := by
    rw [← hm₁]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr (htLB D₁ hD₁ hD₁X))
  have hφ₂ : φ ⟨t, htL⟩ ∈ conjSub g₂ U₀ := by
    rw [← hm₂]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr (htLB D₂ hD₂ hD₂X))
  have hne : φ ⟨t, htL⟩ ≠ 1 := fun h => hs.notQ ((d.ker ⟨t, htL⟩).mp h)
  have hspec : SpecialAt β p₀ U₀ (g₁⁻¹ * g₂) := by
    have h := (d.pos_classes hg hD₁ hD₂ hg₁ hg₂ (h35 D₁ hD₁).2 hG.geom.W_le hK hG.geom.p₀_ne
      hG.geom.U₀_fix hG.β_inv hG.β_skew hlam hform).2.2.1
    rw [h] at hpos
    exact hpos
  exact ⟨htL, g₁, g₂, hg₁.1, hg₂.1, hspec, Subgroup.mem_inf.mpr ⟨hφ₁, hφ₂⟩, hne⟩

end FrameZ

section Main

private theorem fe2_exists_conj_of_isZConjugate {G : Type} [Group G] {Z A X : Subgroup G}
    (hA : IsZConjugate Z A) (hX : IsZConjugate Z X) : ∃ g : G, X = conjSubgroup g A := by
  obtain ⟨y, rfl⟩ := hA
  obtain ⟨g₀, rfl⟩ := hX
  refine ⟨g₀ * y⁻¹, ?_⟩
  rw [← conjSubgroup_mul, inv_mul_cancel_right]

theorem Fe2_inter_conj {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)} {β : V →ₗ[K] V →ₗ[K] K}
    {R : (V ≃ₗ[K] V) → Prop} (hRconj : ∀ g ∈ Γ, ∀ u, R u → R (g * u * g⁻¹))
    (hT : ∀ g ∈ Γ, SpecialAt β p₀ U₀ g → ∀ u ∈ U₀ ⊓ conjSub g U₀, u ≠ 1 → R u)
    {g₁ g₂ : V ≃ₗ[K] V} (hg₁ : g₁ ∈ Γ) (hg₂ : g₂ ∈ Γ) (hs : SpecialAt β p₀ U₀ (g₁⁻¹ * g₂))
    {u : V ≃ₗ[K] V} (hu : u ∈ conjSub g₁ U₀ ⊓ conjSub g₂ U₀) (hu1 : u ≠ 1) : R u := by
  obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨u₀, hu₀U, hu₀eq⟩ := mem_conjSub.mp hu₁
  obtain ⟨u₂, hu₂U, hu₂eq⟩ := mem_conjSub.mp hu₂
  have key : g₁⁻¹ * g₂ * u₂ * (g₁⁻¹ * g₂)⁻¹ = u₀ := by
    calc g₁⁻¹ * g₂ * u₂ * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * u₂ * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * u * g₁ := by rw [hu₂eq]
      _ = u₀ := by rw [← hu₀eq]; group
  have hu₀1 : u₀ ≠ 1 := by
    rintro rfl
    apply hu1
    rw [← hu₀eq, mul_one, mul_inv_cancel]
  have hgmem : g₁⁻¹ * g₂ ∈ Γ := Γ.mul_mem (Γ.inv_mem hg₁) hg₂
  have hR := hT _ hgmem hs u₀ (Subgroup.mem_inf.mpr ⟨hu₀U, mem_conjSub.mpr ⟨u₂, hu₂U, key⟩⟩) hu₀1
  have h := hRconj g₁ hg₁ u₀ hR
  rwa [hu₀eq] at h

variable {G : Type} [Group G] [Finite G]

@[expose] def Fe2Frame (n : ℕ) (M Q A B : Subgroup G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q A K γ),
    GlobalModelData M Q A γ M₀ ∧
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (ψ : M₀.E ≃ₗ[K] V)
      (φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)) (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V)
      (U₀ : Subgroup (V ≃ₗ[K] V)) (β : V →ₗ[K] V →ₗ[K] K),
      EUniData M Q A B M₀ ψ φ Γ p₀ U₀ ∧ Fe2Geom Γ p₀ U₀ β n ∧
      ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f)

theorem fe2_generic
    (Case : Subgroup G → Subgroup G → Subgroup G → Subgroup G → Prop) (n : ℕ) (hn : 2 < n)
    (hCaseConj : ∀ {M Q Z B : Subgroup G} (y : G), Case M Q Z B →
      Case (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B))
    (hWidth : ∀ M Q Z B : Subgroup G, Case M Q Z B → Width Q Z n)
    (hTacit : ∀ M Q Z B : Subgroup G, SmithECfg M Q Z B → Case M Q Z B →
      ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B')
    (h34 : Stroth34Statement)
    (h28 : ∀ M Q Z B : Subgroup G, SmithECfg M Q Z B → Case M Q Z B →
      ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X)
    (hFrame : ∀ M Q A B : Subgroup G, SmithECfg M Q A B → Case M Q A B → Fe2Frame n M Q A B)
    {M Q Z B : Subgroup G} (hc : SmithECfg M Q Z B) (hcase : Case M Q Z B)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hg : GlobalModelData M Q Z γ M₀)
    {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
    {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
    {U₀ : Subgroup (V ≃ₗ[K] V)} {β : V →ₗ[K] V →ₗ[K] K}
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (hG : Fe2Geom Γ p₀ U₀ β n) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f))
    {R : (V ≃ₗ[K] V) → Prop} (hRconj : ∀ g ∈ Γ, ∀ u, R u → R (g * u * g⁻¹))
    (hT : ∀ g ∈ Γ, SpecialAt β p₀ U₀ g → ∀ u ∈ U₀ ⊓ conjSub g U₀, u ≠ 1 → R u)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {t : G} (hzt : IsConj z t) (htM : t ∈ M) (htQ : t ∉ Q) :
    ∃ htL : t ∈ Lgen M (LB M Q B), φ ⟨t, htL⟩ ≠ 1 ∧ R (φ ⟨t, htL⟩) := by
  have H : StrothHyp M Q Z := hc.ctx.hyp
  obtain ⟨X, hs⟩ : ∃ X : Subgroup G, Sit M Q Z X t := exists_sit_of_isConj H hz hzt htM htQ
  have hXz : IsZConjugate Z X := hs.conj
  have hZz : IsZConjugate Z Z := IsZConjugate.self Z
  have h12 := smith_1_12 hs
  obtain ⟨A, hAc, hAQ, hAZ, hAX, hAXne, -⟩ := smith29_of_exists hs (h28 M Q Z B hc hcase X t hs)
  obtain ⟨y, hAy, hQBA, -⟩ := hAc.QB_eq H
  have hcA : SmithECfg (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hc.conj y
  have hcaseA : Case (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hCaseConj y hcase
  have hHA := hcA.ctx.hyp
  have hXQ : X ≤ QB A := (hAc.le_QB_iff H hXz).mpr hAX
  have hZQA : Z ≤ QB A := (hAc.le_QB_iff H hZz).mpr (by rw [H.QB_Z]; exact hAQ)
  have hXc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A X :=
    ⟨hHA, fe2_exists_conj_of_isZConjugate hAc hXz, by rw [← hQBA]; exact hXQ, hAXne.symm⟩
  have hZc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A Z :=
    ⟨hHA, fe2_exists_conj_of_isZConjugate hAc hZz, by rw [← hQBA]; exact hZQA, hAZ.symm⟩
  have hBc := hcA.ctx
  obtain ⟨KA, _, _, γA, M₀A, hgA, VA, _, _, ψA, φA, ΓA, p₀A, U₀A, βA, dA, hGA, lamA, hlamA,
    hformA⟩ := hFrame _ _ _ _ hcA hcaseA
  have hwA : Width (conjSubgroup y Q) A n := hWidth _ _ _ _ hcaseA
  have hTacA := hTacit _ _ _ _ hcA hcaseA
  have hcardA : ∀ C : Subgroup G, Ctx (conjSubgroup y M) (conjSubgroup y Q) A C →
      Nat.card ↥(conjSubgroup y Q ⊓ QB C) = Nat.card A ^ (n + 1) := fun C hC =>
    (stroth_3_5 h34 hC hwA hn (hTacA C hC).1 (hTacA C hC).2).2.2.2
  have hXN : X ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    H.Z_normal.2 (Subgroup.mem_inf.mp (h12.1 hx)).1
  have hXnQ : ¬ X ≤ QB Z := fun h => hs.notQ (by rw [H.QB_Z] at h; exact h hs.mem)
  obtain ⟨D₁, D₂, hD₁, hD₂, hD₁Z, hD₂Z, hD₁X, hD₂X, hpos⟩ :=
    fe2_common_collinear hgA dA hGA hlamA hformA hcardA hBc hZc hXc ⟨hXN, hXnQ⟩
  have hbot := Z_inf_QB_eq_bot hs h12
  have hq4 : 4 ≤ Nat.card Z := H.q4
  have hCtx : ∀ {D : Subgroup G}, Ctx (conjSubgroup y M) (conjSubgroup y Q) A D → D ≤ QB Z →
      D ≤ QB X → Ctx M Q Z D := by
    intro D hD hDZ hDX
    refine ⟨H, ?_, by rw [H.QB_Z] at hDZ; exact hDZ, ?_⟩
    · obtain ⟨g, hg⟩ := hD.conj
      exact ⟨g * y, by rw [hg, hAy, conjSubgroup_mul]⟩
    · intro hDZeq
      have hZX : Z ≤ QB X := hDZeq ▸ hDX
      have : Z ≤ Z ⊓ QB X := le_inf le_rfl hZX
      rw [hbot] at this
      have h1 : Nat.card Z = 1 := Subgroup.card_eq_one.mpr (le_bot_iff.mp this)
      omega
  have hD₁' : Ctx M Q Z D₁ := hCtx hD₁ hD₁Z hD₁X
  have hD₂' : Ctx M Q Z D₂ := hCtx hD₂ hD₂Z hD₂X
  have hwZ : Width Q Z n := hWidth M Q Z B hcase
  have hTacZ := hTacit M Q Z B hc hcase
  have h35 : ∀ D : Subgroup G, Ctx M Q Z D →
      Nat.card ↥(LB M Q D) = Nat.card Q * Nat.card Z ^ (n - 1) ∧
        Nat.card ↥(Q ⊓ QB D) = Nat.card Z ^ (n + 1) := fun D hD =>
    let h := stroth_3_5 h34 hD hwZ hn (hTacZ D hD).1 (hTacZ D hD).2
    ⟨h.2.2.1, h.2.2.2⟩
  obtain ⟨htL, g₁, g₂, hg₁, hg₂, hspec, hmem, hne⟩ :=
    fe2_radical_core hg d hG hlam hform hc.ctx.LB_le_M h35 hs hD₁' hD₂' hD₁X hD₂X hpos
  exact ⟨htL, hne, Fe2_inter_conj hRconj hT hg₁ hg₂ hspec hmem hne⟩

end Main

end CFSG.RankThree.GF2n.Smith81
