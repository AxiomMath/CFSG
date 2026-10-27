module

public import CFSG.RankThree.GF2n.Smith81.S81LModel
public import CFSG.RankThree.GF2n.Smith81.S81NMain
public import CFSG.RankThree.GF2n.Smith81.S81BPos3
public import CFSG.RankThree.GF2n.Smith81.S81JSpecial
public import CFSG.RankThree.GF2n.Smith81.S81BPos2
public import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

section HT

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem EGeom.EUniData.LB_le_Lgen_and_map_eq (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀)
    (hLM : LB M Q B ≤ M) {X : Subgroup G} {g : V ≃ₗ[K] V} (hX : d.IsPt X g) {n : ℕ}
    (hc : Nat.card ↥(LB M Q X) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hU : Nat.card U₀ = Nat.card K ^ (n - 1)) (hK : Nat.card K = Nat.card Z) :
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
  have hRcard : Nat.card ↥(conjSub g U₀) = Nat.card Z ^ (n - 1) := by
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom :=
      fun a b h => (MulAut.conj g).injective h
    unfold conjSub
    rw [Subgroup.card_map_of_injective hinj, hU, hK]
  refine le_and_map_eq_of_radical φ d.ker hQL hQX hlift ?_
  rw [hRcard]
  exact hc

end HT

section Pos

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ψ : M₀.E ≃ₗ[K] Cube K} {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}

theorem EGeom.EUniData.epos_M_iff_special (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * beta K (ψ e) (ψ f)) {B' C' : Subgroup G}
    (hB' : Ctx M Q Z B') (hC' : Ctx M Q Z C') {gB gC : Cube K ≃ₗ[K] Cube K} (hgB : d.IsPt B' gB)
    (hgC : d.IsPt C' gC) (hcard : Nat.card ↥(Q ⊓ QB B') = Nat.card Z ^ (10 + 1)) :
    EPosM B' C' ↔ Special K (gB⁻¹ * gC) := by
  have h := (d.pos_classes hg hB' hC' hgB hgC hcard a5MinuscGeom.W_le hg.card
    a5MinuscGeom.p₀_ne a5MinuscGeom.U₀_fix a5MinuscRank.β_inv a5MinuscRank.β_skew hlam hform).2.2.1
  rw [h]
  rfl

end Pos

section FrameA

variable {G : Type} [Group G]

private theorem s81j_exists_conj_of_isZConjugate {Z A X : Subgroup G} (hA : IsZConjugate Z A)
    (hX : IsZConjugate Z X) : ∃ g : G, X = conjSubgroup g A := by
  obtain ⟨y, rfl⟩ := hA
  obtain ⟨g₀, rfl⟩ := hX
  refine ⟨g₀ * y⁻¹, ?_⟩
  rw [← conjSubgroup_mul, inv_mul_cancel_right]

theorem e3l_special_pair_le_inf [Finite G]
    (hFE1 : Smith24E3LUniformStatement) (hTacit : ETacitE3LStatement)
    (h34 : Stroth34Statement) {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G))
    (hc : SmithECfg M Q Z B) (h3L : InCaseE3L M Q Z B) {X A : Subgroup G} {t : G}
    (hs : Sit M Q Z X t) (hAc : IsZConjugate Z A) (hAQ : A ≤ Q) (hAZ : A ≠ Z)
    (hAX : A ≤ QB X) (hAXne : A ≠ X) :
    ∃ D₁ D₂ : Subgroup G, Ctx M Q Z D₁ ∧ Ctx M Q Z D₂ ∧ D₁ ≤ QB X ∧ D₂ ≤ QB X ∧
      EPosM D₁ D₂ := by
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have hXz : IsZConjugate Z X := hs.conj
  have hZz : IsZConjugate Z Z := IsZConjugate.self Z
  have h12 := smith_1_12 hs
  obtain ⟨y, hAy, hQBA, -⟩ := hAc.QB_eq H
  have hcA : SmithECfg (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact hc.conj y
  have h3LA : InCaseE3L (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := by
    rw [hAy]
    exact h3L.conj y
  have hHA := hcA.ctx.hyp
  have hXQ : X ≤ QB A := (hAc.le_QB_iff H hXz).mpr hAX
  have hZQA : Z ≤ QB A := (hAc.le_QB_iff H hZz).mpr (by rw [H.QB_Z]; exact hAQ)
  have hXc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A X :=
    ⟨hHA, s81j_exists_conj_of_isZConjugate hAc hXz, by rw [← hQBA]; exact hXQ, hAXne.symm⟩
  have hZc : Ctx (conjSubgroup y M) (conjSubgroup y Q) A Z :=
    ⟨hHA, s81j_exists_conj_of_isZConjugate hAc hZz, by rw [← hQBA]; exact hZQA, hAZ.symm⟩
  have hBc := hcA.ctx
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hHA
  obtain ⟨ψ, φ, d⟩ := hFE1 G (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) IH
    hcA.toRemCfg h3LA K γ M₀ hg
  obtain ⟨lam, hlam, hform⟩ := smith24E3LFormStatement_holds G (conjSubgroup y M)
    (conjSubgroup y Q) A (conjSubgroup y B) IH hcA.toRemCfg h3LA K γ M₀ hg ψ φ d
  have hw : Width (conjSubgroup y Q) A 10 := by
    obtain ⟨t', -, h⟩ := h3LA
    exact h.1
  have hTacA := hTacit G (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) IH hcA h3LA
  have hcardA : ∀ C : Subgroup G, Ctx (conjSubgroup y M) (conjSubgroup y Q) A C →
      Nat.card ↥(conjSubgroup y Q ⊓ QB C) = Nat.card A ^ (10 + 1) := fun C hC =>
    (stroth_3_5 h34 hC hw (by norm_num) (hTacA C hC).1 (hTacA C hC).2).2.2.2
  obtain ⟨gZ, hgZ⟩ := d.exists_isPt hZc
  obtain ⟨gX, hgX⟩ := d.exists_isPt hXc
  have hXN : X ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    H.Z_normal.2 (Subgroup.mem_inf.mp (h12.1 hx)).1
  have hXnQ : ¬ X ≤ QB Z := fun h => hs.notQ (by rw [H.QB_Z] at h; exact h hs.mem)
  have hspec : Special K (gZ⁻¹ * gX) :=
    (d.epos_M_iff_special hg hlam hform hZc hXc hgZ hgX (hcardA Z hZc)).mp ⟨hXN, hXnQ⟩
  obtain ⟨h₁, hh₁, h₂, hh₂, hW₁, hW₂, hX₁, hX₂, hsp⟩ :=
    a5_special_common_collinear ((Gam K).mul_mem (Subgroup.inv_mem _ hgZ.1) hgX.1) hspec
  obtain ⟨D₁, hD₁, gD₁, hgD₁, c₁, hc₁, e₁⟩ :=
    d.exists_ctx_with_class hBc a5MinuscGeom.p₀_ne hgZ hh₁
  obtain ⟨D₂, hD₂, gD₂, hgD₂, c₂, hc₂, e₂⟩ :=
    d.exists_ctx_with_class hBc a5MinuscGeom.p₀_ne hgZ hh₂
  have hK : Nat.card K = Nat.card A := hg.card
  have hZmem : ∀ {D : Subgroup G} {gD h : Cube K ≃ₗ[K] Cube K} {c : K},
      Ctx (conjSubgroup y M) (conjSubgroup y Q) A D → d.IsPt D gD →
      gZ⁻¹ (gD (p0 K)) = c • h (p0 K) → h (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) →
      D ≤ QB Z := by
    intro D gD h c hD hgD e hW
    refine ((d.le_QB_iff hZc hD hgZ hgD (hcardA Z hZc) a5MinuscGeom.W_le hK
      a5MinuscGeom.p₀_ne a5MinuscGeom.U₀_fix)).mpr ?_
    rw [e]
    exact Submodule.smul_mem _ _ hW
  have hXmem : ∀ {D : Subgroup G} {gD h : Cube K ≃ₗ[K] Cube K} {c : K},
      Ctx (conjSubgroup y M) (conjSubgroup y Q) A D → d.IsPt D gD →
      gZ⁻¹ (gD (p0 K)) = c • h (p0 K) →
      (gZ⁻¹ * gX)⁻¹ (h (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) → D ≤ QB X := by
    intro D gD h c hD hgD e hW
    refine ((d.le_QB_iff hXc hD hgX hgD (hcardA X hXc) a5MinuscGeom.W_le hK
      a5MinuscGeom.p₀_ne a5MinuscGeom.U₀_fix)).mpr ?_
    have e2 : gX⁻¹ (gD (p0 K)) = (gZ⁻¹ * gX)⁻¹ (c • h (p0 K)) := by
      have e3 : gD (p0 K) = gZ (gZ⁻¹ (gD (p0 K))) := by
        rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
      have e4 : gD (p0 K) = gZ (c • h (p0 K)) := e3.trans (congrArg gZ e)
      rw [mul_inv_rev, inv_inv, LinearEquiv.mul_apply, e4]
    rw [e2, map_smul]
    exact Submodule.smul_mem _ _ hW
  have hD₁Z := hZmem hD₁ hgD₁ e₁ hW₁
  have hD₂Z := hZmem hD₂ hgD₂ e₂ hW₂
  have hD₁X := hXmem hD₁ hgD₁ e₁ hX₁
  have hD₂X := hXmem hD₂ hgD₂ e₂ hX₂
  have hrel : ∀ {gD h : Cube K ≃ₗ[K] Cube K} {c : K}, gZ⁻¹ (gD (p0 K)) = c • h (p0 K) →
      gD (p0 K) = c • (gZ * h) (p0 K) := by
    intro gD h c e
    have e3 : gD (p0 K) = gZ (gZ⁻¹ (gD (p0 K))) := by
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    rw [e3, e, map_smul, LinearEquiv.mul_apply]
  have hspD : Special K (gD₁⁻¹ * gD₂) := by
    refine (special_rel_point ((Gam K).mul_mem hgZ.1 hh₁) ((Gam K).mul_mem hgZ.1 hh₂) hgD₁.1
      hgD₂.1 hc₁ hc₂ (hrel e₁) (hrel e₂)).mpr ?_
    rw [show (gZ * h₁)⁻¹ * (gZ * h₂) = h₁⁻¹ * h₂ by group]
    exact hsp
  have hpos : EPosM D₁ D₂ :=
    (d.epos_M_iff_special hg hlam hform hD₁ hD₂ hgD₁ hgD₂ (hcardA D₁ hD₁)).mpr hspD
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
  exact ⟨D₁, D₂, hCtx hD₁ hD₁Z hD₁X, hCtx hD₂ hD₂Z hD₂X, hD₁X, hD₂X, hpos⟩

end FrameA

section Main

variable {G : Type} [Group G]

theorem e3lRootElt_of_inputs
    (hFE1 : Smith24E3LUniformStatement) (h34 : Stroth34Statement) : E3LRootEltStatement := by
  intro G _ _ M Q Z B IH hR hc K _ _ γ M₀ hg ψ φ d z hz hz1 t hzt htM htQ
  have hSE : SmithECfg M Q Z B := by
    obtain ⟨t', hD, h⟩ := hc
    exact ⟨hR.toCfg, t', hD, Or.inl ⟨h.1, h.2.1, Or.inr h.2.2⟩⟩
  have hTacit := eTacitE3L_of_uniform hFE1
  have H : StrothHyp M Q Z := hSE.ctx.hyp
  have hXex : ∃ X : Subgroup G, Sit M Q Z X t := exists_sit_of_isConj H hz hzt htM htQ
  obtain ⟨X, hs⟩ := hXex
  have hQX : Q ⊓ QB X ≠ ⊥ :=
    smith28aE3L_of_normQuot (normQuotE3L_of_uniform hFE1) (elemBoundE3L_of_uniform hFE1)
      G M Q Z B IH hSE hc X t hs
  obtain ⟨A, hAc, hAQ, hAZ, hAX, hAXne, -⟩ := smith29_of_exists hs
    (e3l28Cond_of_uniform hFE1 G M Q Z B IH hSE hc X t hs hQX)
  obtain ⟨D₁, D₂, hD₁, hD₂, hD₁X, hD₂X, hpos⟩ :=
    e3l_special_pair_le_inf hFE1 hTacit h34 IH hSE hc hs hAc hAQ hAZ hAX hAXne
  have hw : Width Q Z 10 := by
    obtain ⟨t', -, h⟩ := hc
    exact h.1
  have hLM : LB M Q B ≤ M := hSE.ctx.LB_le_M
  obtain ⟨lam, hlam, hform⟩ := smith24E3LFormStatement_holds G M Q Z B IH hR hc K γ M₀ hg ψ φ d
  have hTacI := hTacit G M Q Z B IH hSE hc
  have h35 : ∀ D : Subgroup G, Ctx M Q Z D →
      Nat.card ↥(LB M Q D) = Nat.card Q * Nat.card Z ^ (10 - 1) ∧
        Nat.card ↥(Q ⊓ QB D) = Nat.card Z ^ (10 + 1) := fun D hD =>
    let h := stroth_3_5 h34 hD hw (by norm_num) (hTacI D hD).1 (hTacI D hD).2
    ⟨h.2.2.1, h.2.2.2⟩
  have hXz : IsZConjugate Z X := hs.conj
  have htLB : ∀ D : Subgroup G, Ctx M Q Z D → D ≤ QB X → t ∈ LB M Q D := fun D hD hDX =>
    (le_sup_right : QB D ⊓ M ≤ Q ⊔ (QB D ⊓ M)) (Subgroup.mem_inf.mpr
      ⟨(IsZConjugate.le_QB_iff H hD.conj hXz).mpr hDX hs.mem, htM⟩)
  obtain ⟨g₁, hg₁⟩ := d.exists_isPt hD₁
  obtain ⟨g₂, hg₂⟩ := d.exists_isPt hD₂
  have hU : Nat.card (U0 K) = Nat.card K ^ (10 - 1) := a5MinuscRank.U_card
  obtain ⟨hL₁, hm₁⟩ := d.LB_le_Lgen_and_map_eq hLM hg₁ (h35 D₁ hD₁).1 hU hg.card
  obtain ⟨-, hm₂⟩ := d.LB_le_Lgen_and_map_eq hLM hg₂ (h35 D₂ hD₂).1 hU hg.card
  have htL : t ∈ Lgen M (LB M Q B) := hL₁ (htLB D₁ hD₁ hD₁X)
  have hφ₁ : φ ⟨t, htL⟩ ∈ conjSub g₁ (U0 K) := by
    rw [← hm₁]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr (htLB D₁ hD₁ hD₁X))
  have hφ₂ : φ ⟨t, htL⟩ ∈ conjSub g₂ (U0 K) := by
    rw [← hm₂]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr (htLB D₂ hD₂ hD₂X))
  have hne : φ ⟨t, htL⟩ ≠ 1 := fun h => htQ ((d.ker ⟨t, htL⟩).mp h)
  have hspec : Special K (g₁⁻¹ * g₂) :=
    (d.epos_M_iff_special hg hlam hform hD₁ hD₂ hg₁ hg₂ (h35 D₁ hD₁).2).mp hpos
  obtain ⟨τ, hτ, hφτ⟩ := a5_inter_special_transvec' hg₁.1 hg₂.1 hspec ⟨hφ₁, hφ₂⟩ hne
  exact ⟨⟨t, htL⟩, by simp, τ, hτ, hφτ⟩

end Main

end CFSG.RankThree.GF2n.Smith81
