module

public import CFSG.RankThree.GF2n.Tim79a34C8Base
public import CFSG.RankThree.GF2n.Tim79a34GammaSteps
public import CFSG.RankThree.GF2n.Tim79a34SpOrder

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open scoped commutatorElement Matrix

structure ResCfg {G : Type} [Group G] [Finite G] (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1)
    (T : Subgroup ↥(StatedSp n (GaloisField 2 1))) : Prop where
  hyp : TwoEndHyp M V Q P H
  nat : NatCfg V H hyp.setup.mc.toMinCex.V_le_H Φ ψ
  ne : a ≠ 0
  trans : CaseM.IsTransGroup a T
  tv : T.map Φ.toMonoidHom = Vy V H
  point : c8W ψ a ∈ V
  perp : ∀ v, c8W ψ v ∈ P ↔ spForm a v = 0
  rbar : Rbar V H P = (spRad a).map Φ.toMonoidHom
  xh : xOf V H = H
  cent : Subgroup.centralizer ({c8W ψ a} : Set G) = M
  hPc : Subgroup.centralizer (P : Set G) = V

theorem exists_resCfg {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    ∃ (n : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
      (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
      (a : Fin n ⊕ Fin n → GaloisField 2 1)
      (T : Subgroup ↥(StatedSp n (GaloisField 2 1))), 3 ≤ n ∧ ResCfg M V Q P H Φ ψ a T := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h12 : Lemma12Statement := lemma12Statement_holds
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ
  obtain ⟨n, Φ, ψ, -, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  have hNat : NatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨n', hn'3, ⟨e⟩⟩ := hn
  have hnn : n = n' := by
    let e2 : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hZ)
    exact statedSp_gf2_rank_eq (Φ.trans (e2.trans e.symm))
  obtain ⟨hiff, hRbar, hxOf, -⟩ := h11a G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV
  obtain ⟨-, -, hPcent⟩ := h11b G M V Q P H hH hZ hcP
  have hcentM := (h12 G M V Q P H hH hZ Φ ψ hNat a T ha hT hTV).1
  exact ⟨n, Φ, ψ, a, T, by omega, ⟨hH, hNat, ha, hT, hTV, hpoint a T ha hT hTV, hiff, hRbar,
    hxOf, hcentM, hPcent⟩⟩

theorem exists_spRad_of_mem_P {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : ResCfg M V Q P H Φ ψ a T) {u : G} (hu : u ∈ P) :
    ∃ g ∈ spRad a, (∀ v, u * c8W ψ v * u⁻¹ = c8W ψ (SpExtras.mat n (GaloisField 2 1) g *ᵥ v)) ∧
      (g ∈ T → ∃ y ∈ V, ∃ s ∈ P ⊓ wOf V H, u = y * s) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have huX : u ∈ xOf V H := by
    rw [cfg.xh]
    exact hc.PleH hu
  have hxb : xToXbar hVH ⟨u, huX⟩ ∈ Rbar V H P := by
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨u, huX⟩, hu, rfl⟩
  rw [cfg.rbar] at hxb
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hxb
  have hg' : Φ.symm (xToXbar hVH ⟨u, huX⟩) = g := by
    rw [← hgx]
    exact Φ.symm_apply_apply g
  refine ⟨g, hg, fun v => ?_, fun hgT => ?_⟩
  · have key := cfg.nat.equiv ⟨u, huX⟩ v
    rw [hg'] at key
    exact key.symm
  · have hmem : xToXbar hVH ⟨u, huX⟩ ∈ Vy V H := by
      rw [← cfg.tv, ← hgx]
      exact Subgroup.mem_map_of_mem _ hgT
    obtain ⟨y', hy'V, hy'⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hmem)
    rw [coe_xToXbar] at hy'
    have h1 : piBar V H (y'⁻¹ * Subgroup.inclusion (xOf_le_H hVH) ⟨u, huX⟩) = 1 := by
      rw [map_mul, map_inv, hy', inv_mul_cancel]
    have h2 := (piBar_eq_one_iff _).mp h1
    refine ⟨(y' : G), hy'V, (y' : G)⁻¹ * u, ?_, by group⟩
    exact Subgroup.mem_inf.mpr ⟨P.mul_mem (P.inv_mem (hc.V_le_P hy'V)) hu, h2⟩

theorem eq_zero_or_one_gf2 (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · refine Or.inr (tw_eq_one_of_card_two ?_ h)
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]

theorem mem_T_of_param {n : ℕ} {a : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 1))} (hT : CaseM.IsTransGroup a T)
    {g : ↥(StatedSp n (GaloisField 2 1))} {w : Fin n ⊕ Fin n → GaloisField 2 1}
    {c e : GaloisField 2 1} (hw : w = e • a)
    (hmat : ∀ x, SpExtras.mat n (GaloisField 2 1) g *ᵥ x =
      x + spForm a x • w + spForm w x • a + (c * spForm a x) • a) : g ∈ T := by
  refine (hT.1 g).2 ⟨c, ?_⟩
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [hmat x, spTrans_mulVec, hw, spForm_smul_left']
  linear_combination (norm := module) vec_add_self ((e * spForm a x) • a)

theorem sp_classify_Y {n : ℕ} {a : Fin n ⊕ Fin n → GaloisField 2 1} (ha : a ≠ 0)
    (Y : Set (Fin n ⊕ Fin n → GaloisField 2 1))
    (hadd : ∀ x ∈ Y, ∀ y ∈ Y, x + y ∈ Y)
    (hperp : ∀ v ∈ Y, spForm a v = 0)
    (hmove : ∀ v ∈ Y, ∀ x, spForm a x = 0 → v + spForm x v • x ∈ Y) :
    (∀ v ∈ Y, v = 0 ∨ v = a) ∨ (∀ z, spForm a z = 0 → z ∈ Y) := by
  by_cases h : ∀ v ∈ Y, v = 0 ∨ v = a
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨v, hvY, hv0, hva⟩ := h
    have hva' : ∀ c : GaloisField 2 1, v ≠ c • a := by
      intro c hc
      rcases eq_zero_or_one_gf2 c with rfl | rfl
      · exact hv0 (by rw [hc, zero_smul])
      · exact hva (by rw [hc, one_smul])
    obtain ⟨u, hau, hvu⟩ := exists_dual ha (hperp v hvY) hva'
    have huv : spForm u v = 1 := (spForm_comm_charTwo v u).trans hvu
    have key : ∀ z, spForm a z = 0 → spForm z v = 1 → z ∈ Y := by
      intro z hz hzv
      have h1 := hmove v hvY z hz
      rw [hzv, one_smul] at h1
      have h2 : v + z + v = z := by rw [add_comm v z, add_assoc, vec_add_self, add_zero]
      rw [← h2]
      exact hadd _ h1 _ hvY
    have hu : u ∈ Y := key u hau huv
    intro z hz
    rcases eq_zero_or_one_gf2 (spForm z v) with h0 | h1
    · have hzu : z + u ∈ Y := key (z + u) (by rw [spForm_add_right, hz, hau, add_zero])
        (by rw [spForm_add_left, h0, huv, zero_add])
      have h2 : z + u + u = z := by rw [add_assoc, vec_add_self, add_zero]
      rw [← h2]
      exact hadd _ hzu _ hu
    · exact key z hz h1

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G} {n : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 1}
  {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

theorem wOf_le_inf_residual (cfg : ResCfg M V Q P H Φ ψ a T) (hX : xOf V H ≤ pResidual 2 G) :
    wOf V H ≤ M ⊓ pResidual 2 G := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  refine le_inf ?_ ((wOf_le_xOf V H).trans hX)
  have h := nm_wOf_le_normalizer hc (g := 1) H.one_mem
  rw [conjSubgroup_one, hc.normalizer_eq] at h
  exact h

theorem exists_lift_spTrans_residual (cfg : ResCfg M V Q P H Φ ψ a T) (hX : xOf V H ≤ pResidual 2 G)
    {x : Fin n ⊕ Fin n → GaloisField 2 1} (hx : spForm a x = 0) :
    ∃ m ∈ M ⊓ pResidual 2 G,
      ∀ v, m * c8W ψ v * m⁻¹ = c8W ψ (v + spForm x v • x) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨t, ht⟩ := exists_mat_eq_spTrans x (1 : GaloisField 2 1)
  obtain ⟨xx, hxx⟩ := xToXbar_surjective hVH (Φ t)
  have hsymm : Φ.symm (xToXbar hVH xx) = t := by
    rw [hxx]
    exact Φ.symm_apply_apply t
  have key : ∀ v, (xx : G) * c8W ψ v * (xx : G)⁻¹ = c8W ψ (v + spForm x v • x) := by
    intro v
    have h := cfg.nat.equiv xx v
    rw [hsymm, ht, spTrans_mulVec, one_mul] at h
    exact h.symm
  refine ⟨(xx : G), Subgroup.mem_inf.mpr ⟨?_, hX xx.2⟩, key⟩
  rw [← cfg.cent, Subgroup.mem_centralizer_singleton_iff]
  have h := key a
  rw [spForm_eq_zero_comm hx, zero_smul, add_zero] at h
  calc (xx : G) * c8W ψ a = ((xx : G) * c8W ψ a * (xx : G)⁻¹) * (xx : G) := by group
    _ = c8W ψ a * (xx : G) := by rw [h]

theorem classify_abelian (cfg : ResCfg M V Q P H Φ ψ a T) (hX : xOf V H ≤ pResidual 2 G)
    {A : Subgroup G} (hVA : V ≤ A) (hAP : A ≤ P)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAn : ∀ m ∈ M ⊓ pResidual 2 G, ∀ x ∈ A, m * x * m⁻¹ ∈ A) :
    A = V ∨ A = V ⊔ (P ⊓ wOf V H) := by
  have hWM := wOf_le_inf_residual cfg hX
  have hcls := sp_classify_Y cfg.ne {v | c8W ψ v ∈ A}
    (fun x hx y hy => by
      show c8W ψ (x + y) ∈ A
      rw [c8W_add]
      exact A.mul_mem hx hy)
    (fun v hv => (cfg.perp v).mp (hAP hv))
    (fun v hv x hx => by
      obtain ⟨m, hm, hmx⟩ := exists_lift_spTrans_residual cfg hX hx
      show c8W ψ (v + spForm x v • x) ∈ A
      rw [← hmx v]
      exact hAn m hm _ hv)
  rcases hcls with hY | hY
  · left
    refine le_antisymm (fun x hx => ?_) hVA
    obtain ⟨g, hg, hgx, hgT⟩ := exists_spRad_of_mem_P cfg (hAP hx)
    obtain ⟨w, hw, c, hmat⟩ := exists_spRad_param cfg.ne hg
    obtain ⟨b, hb⟩ := exists_spForm_eq_one cfg.ne
    have hmM : c8W ψ b ∈ M ⊓ pResidual 2 G := hWM (c8W_mem ψ b)
    have hx' := A.mul_mem hx (hAn _ hmM x⁻¹ (A.inv_mem hx))
    have e1 : x * (c8W ψ b * x⁻¹ * (c8W ψ b)⁻¹) =
        c8W ψ (w + (spForm w b + c) • a) := by
      have h2 : x * (c8W ψ b * x⁻¹ * (c8W ψ b)⁻¹) = (x * c8W ψ b * x⁻¹) * (c8W ψ b)⁻¹ := by
        group
      rw [h2, hgx b, c8W_inv, ← c8W_add, hmat b, hb]
      congr 1
      linear_combination (norm := module) vec_add_self b
    rw [e1] at hx'
    have hwe : ∃ e' : GaloisField 2 1, w = e' • a := by
      rcases hY _ hx' with h | h
      · exact ⟨-(spForm w b + c), by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h⟩
      · exact ⟨1 - (spForm w b + c), by rw [sub_smul, one_smul]; exact eq_sub_of_add_eq h⟩
    obtain ⟨e', hwe'⟩ := hwe
    obtain ⟨y, hyV, s, hs, rfl⟩ := hgT (mem_T_of_param cfg.trans hwe' hmat)
    have hsA : s ∈ A := by
      have := A.mul_mem (A.inv_mem (hVA hyV)) hx
      simpa using this
    obtain ⟨v₀, hv₀⟩ := c8W_surj ψ (Subgroup.mem_inf.mp hs).2
    have hv₀Y : v₀ ∈ {v | c8W ψ v ∈ A} := by
      show c8W ψ v₀ ∈ A
      rw [hv₀]
      exact hsA
    refine V.mul_mem hyV ?_
    rcases hY v₀ hv₀Y with h | h
    · rw [← hv₀, h, c8W_zero]
      exact V.one_mem
    · rw [← hv₀, h]
      exact cfg.point
  · right
    have hPW : P ⊓ wOf V H ≤ A := by
      intro s hs
      obtain ⟨v₀, hv₀⟩ := c8W_surj ψ (Subgroup.mem_inf.mp hs).2
      have hperp : spForm a v₀ = 0 :=
        (cfg.perp v₀).mp (by rw [hv₀]; exact (Subgroup.mem_inf.mp hs).1)
      have h := hY v₀ hperp
      show s ∈ A
      rw [← hv₀]
      exact h
    refine le_antisymm (fun x hx => ?_) (sup_le hVA hPW)
    obtain ⟨g, hg, hgx, hgT⟩ := exists_spRad_of_mem_P cfg (hAP hx)
    obtain ⟨w, hw, c, hmat⟩ := exists_spRad_param cfg.ne hg
    have hcomm : ∀ z, spForm a z = 0 → spForm w z = 0 := by
      intro z hz
      have hzA : c8W ψ z ∈ A := hY z hz
      have h2 : x * c8W ψ z * x⁻¹ = c8W ψ z := by
        rw [hAab x hx _ hzA]
        group
      rw [hgx z, hmat z] at h2
      simp only [hz, zero_smul, add_zero, mul_zero] at h2
      have h3 := c8W_inj ψ h2
      have h4 : spForm w z • a = 0 := by
        have h5 := congrArg (fun y => y - z) h3
        simpa using h5
      rcases smul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h cfg.ne
    have hwa : ∃ e : GaloisField 2 1, w = e • a := by
      by_contra hne
      push Not at hne
      obtain ⟨u, hau, hwu⟩ := exists_dual cfg.ne hw hne
      have h := hcomm u hau
      rw [hwu] at h
      exact one_ne_zero h
    obtain ⟨e, hwe⟩ := hwa
    obtain ⟨y, hyV, s, hs, rfl⟩ := hgT (mem_T_of_param cfg.trans hwe hmat)
    exact Subgroup.mul_mem_sup hyV hs

end CFSG.RankThree.GF2n.Tim79a
