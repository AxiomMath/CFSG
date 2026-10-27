module

public import CFSG.Quasithin.Background.SmithB42U33Gen
public import CFSG.Quasithin.Background.SmithB42HatA6Dim
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.Quasithin.Background.SmithB42Alt7Ctx
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.Quasithin.B42U33

open CFSG.Open CFSG.Quasithin H13 H13.Orbit JonesParshall CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.HatA6 (le_of_b4Hyp le_normalizer_of_b4Hyp inf_centralizer_le_of_b4Hyp
  fixV_eq_bot_of_b4Hyp card_le_pow_of_le_closure index_le_of_offender)

theorem nonempty_equiv_g2Derived
    {X : Type} [Group X] (hX : B42TypeU33 X) : Nonempty (X ≃* ↥(g2Derived (ZMod 2))) := by
  obtain ⟨hZ, -, K, _, _, hK, ⟨e⟩⟩ := hX
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 3 (2 * 1))
  have hc : Fintype.card K = Fintype.card (GaloisField 3 (2 * 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Timmesfeld.Final.GF9.card]
  obtain ⟨u⟩ := lred3_equiv_g2derived_psu33 (K := ZMod 2) (by rw [Nat.card_zmod])
  let e0 : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨e0.symm.trans (e.trans ((CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 3 (3 ^ 1)).trans
      (u.trans (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)).symm)))⟩

theorem card_of_b42TypeU33 {X : Type} [Group X] (hX : B42TypeU33 X) : Nat.card X = 6048 := by
  obtain ⟨hZ, -, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have hbot := CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hK9
  let e2 : Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 3 K) ≃*
      Assembly.LowTwoRank.StatedSU 3 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let e0 : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rw [Nat.card_congr ((e0.symm.trans e).trans e2).toEquiv,
    CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hK9]

theorem conjNormal_bijective :
    Function.Bijective
      (MulAut.conjNormal : ↥(quasithinG2 (ZMod 2)) →* MulAut ↥(g2Derived (ZMod 2))) := by
  have : Finite (MulAut ↥(g2Derived (ZMod 2))) := Finite.of_injective _ DFunLike.coe_injective
  have hinj : Function.Injective
      (MulAut.conjNormal : ↥(quasithinG2 (ZMod 2)) →* MulAut ↥(g2Derived (ZMod 2))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply g2QAct_injective
    rw [map_one]
    apply schur_Q
    rintro _ ⟨d, hd, rfl⟩
    have h1 : g * d * g⁻¹ = d := by
      have := congrArg (fun f : MulAut ↥(g2Derived (ZMod 2)) =>
        ((f ⟨d, hd⟩ : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2)))) hg
      simpa [MulAut.conjNormal_apply] using this
    rw [← map_mul, ← map_mul]
    congr 1
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [h1]
  exact hinj.bijective_of_nat_card_le (le_of_eq (by rw [card_mulAut_g2Derived, card_g2Two]))

section Emb

variable {X Y : Type*} [Group X] [Group Y] {D : Subgroup Y} [D.Normal]
  (hD : Function.Bijective (MulAut.conjNormal : Y →* MulAut ↥D)) {N : Subgroup X} [N.Normal]
  (θ : ↥N ≃* ↥D)

@[expose] noncomputable def embG : X →* Y :=
  (MulEquiv.ofBijective _ hD).symm.toMonoidHom.comp
    ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)

theorem conjNormal_embG (x : X) :
    MulAut.conjNormal (embG hD θ x) = MulAut.congr θ (MulAut.conjNormal x) :=
  (MulEquiv.ofBijective _ hD).apply_symm_apply _

theorem conjNormal_embG_apply (x : X) (n : ↥N) :
    MulAut.conjNormal (embG hD θ x) (θ n) = θ (MulAut.conjNormal x n) := by
  rw [conjNormal_embG]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem embG_coe (n : ↥N) : embG hD θ (n : X) = θ n := by
  apply hD.1
  refine MulEquiv.ext fun δ => Subtype.ext ?_
  obtain ⟨m, rfl⟩ := θ.surjective δ
  rw [conjNormal_embG_apply, MulAut.conjNormal_apply]
  have e1 : MulAut.conjNormal (n : X) m = n * m * n⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [e1, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem embG_eq_one {x : X} (hx : embG hD θ x = 1) : ∀ n ∈ N, x * n * x⁻¹ = n := by
  intro n hn
  have h1 : ((MulAut.conjNormal (embG hD θ x) (θ ⟨n, hn⟩) : ↥D) : Y) = θ ⟨n, hn⟩ := by
    rw [MulAut.conjNormal_apply, hx, one_mul, inv_one, mul_one]
  rw [conjNormal_embG_apply] at h1
  have h2 := congrArg Subtype.val (θ.injective (Subtype.ext h1))
  simpa [MulAut.conjNormal_apply] using h2

end Emb

section B4

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem exists_embedding
    (hHyp : B4Hyp G L) (hP : B42TypeU33 ↥L) :
    ∃ ψ : ↥G →* ↥(quasithinG2 (ZMod 2)), Function.Injective ψ ∧
      (∀ g : ↥G, (g : MulAut V) ∈ L → ψ g ∈ g2Derived (ZMod 2)) ∧
      ∀ δ ∈ g2Derived (ZMod 2), ∃ g : ↥G, (g : MulAut V) ∈ L ∧ ψ g = δ := by
  have hLG := le_of_b4Hyp hHyp
  have hGN := le_normalizer_of_b4Hyp hHyp
  have hCL := inf_centralizer_le_of_b4Hyp hHyp
  have hL'n : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).2 hGN
  obtain ⟨θ⟩ := nonempty_equiv_g2Derived hP
  let θ' : ↥(L.subgroupOf G) ≃* ↥(g2Derived (ZMod 2)) :=
    (Subgroup.subgroupOfEquivOfLe hLG).trans θ
  refine ⟨embG conjNormal_bijective θ', ?_, fun g hg => ?_, fun δ hδ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hc := embG_eq_one conjNormal_bijective θ' hg
    have hcomm : ∀ x ∈ L, x * (g : MulAut V) = (g : MulAut V) * x := by
      intro x hx
      have h1 := congrArg Subtype.val (hc ⟨x, hLG hx⟩ hx)
      change (g : MulAut V) * x * (g : MulAut V)⁻¹ = x at h1
      calc x * (g : MulAut V) = (g : MulAut V) * x * (g : MulAut V)⁻¹ * g := by rw [h1]
        _ = (g : MulAut V) * x := by group
    have hgL : (g : MulAut V) ∈ L :=
      hCL ⟨g.2, Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx⟩
    have hgZ : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2)
    rw [hP.1, Subgroup.mem_bot] at hgZ
    have h1 : (g : MulAut V) = 1 := congrArg (fun y : ↥L => (y : MulAut V)) hgZ
    exact Subtype.ext h1
  · have := embG_coe conjNormal_bijective θ' ⟨g, hg⟩
    rw [this]
    exact (θ' _).2
  · refine ⟨θ'.symm ⟨δ, hδ⟩, (θ'.symm ⟨δ, hδ⟩).2, ?_⟩
    rw [embG_coe conjNormal_bijective, MulEquiv.apply_symm_apply]

theorem short_generation
    (hHyp : B4Hyp G L) (hP : B42TypeU33 ↥L) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ L) ∧
        L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) := by
  have hLG := le_of_b4Hyp hHyp
  obtain ⟨ψ, hψ, hψL, hψD⟩ := exists_embedding hHyp hP
  set A' : Subgroup ↥G := A.subgroupOf G with hA'
  set B : Subgroup ↥(quasithinG2 (ZMod 2)) := A'.map ψ with hBdef
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have h1 : ψ ⟨a, hAG ha⟩ ∈ B := ⟨⟨a, hAG ha⟩, ha, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ψ] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (hψ h1)
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAe.1 _ ha _ hb)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, ← map_one ψ]
    congr 1
    exact Subtype.ext (hAe.2 _ ha)
  obtain ⟨r, m, hr, hr1, hr3, hmr, d, hd, hle⟩ := shortGen hB1 hBc hB2
  choose l hlL hld using fun i => hψD (d i) (hd i)
  refine ⟨r, m, ?_, hr1, hr3, hmr, fun i => (l i : MulAut V), hlL, ?_⟩
  · rw [← hr, hBdef, Subgroup.card_map_of_injective hψ]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv).symm
  ·
    have hmap : ∀ i, B.map (MulAut.conj (d i)).toMonoidHom =
        (A'.map (MulAut.conj (l i)).toMonoidHom).map ψ := by
      intro i
      rw [hBdef, Subgroup.map_map, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun a => ?_
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_mul, map_inv, ← hld i]
    intro y hy
    have hy' := hle (hψL ⟨y, hLG hy⟩ hy)
    simp only [hmap, Subgroup.coe_map] at hy'
    rw [← Set.image_iUnion, ← MonoidHom.map_closure] at hy'
    · obtain ⟨z, hz, hzy⟩ := hy'
      have hzy' : z = ⟨y, hLG hy⟩ := hψ hzy
      have h1 := Subgroup.mem_map_of_mem G.subtype hz
      rw [MonoidHom.map_closure, hzy'] at h1
      refine Subgroup.closure_mono ?_ h1
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨a, ha, rfl⟩ := hi
      exact Set.mem_iUnion.2 ⟨i, ⟨(a : MulAut V), ha, rfl⟩⟩

theorem card_mulAut_eq (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ} (hk : Nat.card V = 2 ^ k) :
    Nat.card (MulAut V) = ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hV _
  have hfin : Module.finrank (ZMod 2) (Additive V) = k := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive V) = 2 ^ k := hk
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans h2)
  let b : Module.Basis (Fin k) (ZMod 2) (Additive V) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hfin
  let eLin : MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun φ =>
        { AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive φ : Additive V →+ Additive V) with
          invFun := fun x => Additive.ofMul (φ.symm (Additive.toMul x))
          left_inv := fun x => by simp
          right_inv := fun x => by simp }
      invFun := fun e => MulEquiv.toAdditive.symm e.toAddEquiv
      left_inv := fun φ => by ext; rfl
      right_inv := fun e => by ext; rfl
      map_mul' := fun φ ψ => by ext; rfl }
  let eGL : GL (Fin k) (ZMod 2) ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V))
  rw [Nat.card_congr eLin.toEquiv, ← Nat.card_congr eGL.toEquiv, Matrix.card_GL_field,
    ZMod.card]

theorem six_le_of_card_dvd (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ} (hk : Nat.card V = 2 ^ k)
    (L : Subgroup (MulAut V)) (hL : Nat.card L = 6048) : 6 ≤ k := by
  have h := Subgroup.card_subgroup_dvd_card L
  rw [hL, card_mulAut_eq hV hk] at h
  by_contra hlt
  push Not at hlt
  interval_cases k <;> simp [Fin.prod_univ_succ] at h

theorem card_V
    (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hP : B42TypeU33 ↥L)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : Nat.card V = 2 ^ 6 := by
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle⟩ := short_generation hHyp hP hA.1 hA.2.1 hA.2.2.1
  have h1 := card_le_pow_of_le_closure (fixV_eq_bot_of_b4Hyp hHyp) l hle
  have hup : Nat.card V ≤ 2 ^ 6 := by
    refine h1.trans ((Nat.pow_le_pow_left (index_le_of_offender hA) m).trans ?_)
    rw [hr, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hmr)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card V = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hV)
  have hk6 : k ≤ 6 := by
    rw [hk] at hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hup
  have h6 := six_le_of_card_dvd hV hk L (card_of_b42TypeU33 hP)
  rw [hk, show k = 6 by omega]

end B4

end CFSG.Quasithin.B42U33
