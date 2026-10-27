module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelC
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBAux2
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBAux5
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordAAux2
import CFSG.Quasithin.EmptyFaithful.S146zMListCl
import CFSG.Assembly.GL83StatedBridge
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_spLift
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) :
    ∃ (m : ℕ) (φ : StatedSp m (GaloisField 2 1) →* G),
      4 ≤ m ∧ Function.Injective φ ∧ φ.range = K := by
  obtain ⟨labJ, labK, hJ2, -, -, hHasK, -, htagJ, hnJ, htagK, hnK, hrank⟩ := hrow
  have hperf : commutator ↥K = ⊤ := by
    have hID : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
    unfold GGInnerDiagOn LargeEvenMarking LargeEvenMarkingLegacy at hID
    exact hID.1
  have hfour : 4 ≤ labK.rank := by
    have h5 := hdRo7CLCoordAux_rank_ge_five hJ2 hnJ htagJ hrank
    omega
  have h1n : 1 ≤ labK.n := by omega
  have hmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSp labK.rank 2 1 := by
    have h := hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htagK (by omega) h1n hHasK
    rwa [hnK] at h
  obtain ⟨φ, hinj, hrange⟩ := ggSpLiftInput_holds G K labK.rank 1 hfour hperf hmodel
  exact ⟨labK.rank, φ, hfour, hinj, hrange⟩

private theorem hdRo7CKCoordAux_three_dvd_quotient {X : Type} [Group X] [Finite X]
    (tag : LargeEvenLieTag) (r n : ℕ)
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨tag, r, n⟩
      (fun R _ _ _ => Nonempty (X ≃* R)))
    (htag : tag = .B ∨ tag = .C) (hn : n = 1) (hr : 1 ≤ r) :
    3 ∣ Nat.card X := by
  rcases htag with hB | hC
  · subst hB
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSymplectic] at h
    obtain ⟨K, hf, hfin, hK, ⟨e⟩⟩ := h
    have e' : X ≃* LargeEvenProj (LargeEvenSpGroup K r) := by simpa using e
    rw [Nat.card_congr e'.toEquiv]
    rw [largeEvenProj_eq_statedProj, largeEvenSpGroup_eq_statedSp]
    exact CFSG.Quasithin.three_dvd_card_psp hr
  · subst hC
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSymplectic] at h
    obtain ⟨K, hf, hfin, hK, ⟨e⟩⟩ := h
    have e' : X ≃* LargeEvenProj (LargeEvenSpGroup K r) := by simpa using e
    rw [Nat.card_congr e'.toEquiv]
    rw [largeEvenProj_eq_statedProj, largeEvenSpGroup_eq_statedSp]
    exact CFSG.Quasithin.three_dvd_card_psp hr

theorem hdRo7CKCoordAux_x_decomp
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K)
    (n : ℕ) (hy : y ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hp3 : p = 3)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (hmodel : C2CoordModel p Bs K n τ) (hx : x ∈ Bs) :
    ∃ (c : ℕ) (z : G), z ∈ Bs ⊓ K ∧ x = y ^ c * z := by
  obtain ⟨R, hRgrp, I, θ, hBsN, -, -, -, -, hI, hBs3⟩ :=
    hdRo7CKCoordAux_torus_data hRig hH hrow
  letI : Group R := hRgrp
  have hZK : Subgroup.center ↥K = ⊥ := hdRo7CKCoordAux_center_K_eq_bot hH hrow
  have hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹ :=
    hdRo7CKCoordAux_hinner p B Bs x L D J y K hH R I θ hI hZK hBsN hBs3
  let Φ := hdRo7CKCoordAux_split_equiv p B Bs x L D J y K hH hZK hBsN hinner
  obtain ⟨⟨⟨t, ht⟩, ⟨c', hc'⟩⟩, htc⟩ := Φ.surjective ⟨x, hx⟩
  have hx_eq : t * c' = x := by
    have h := congrArg Subtype.val htc
    rw [hdRo7CKCoordAux_split_equiv_apply] at h
    exact h
  have hcy : c' ∈ Subgroup.zpowers y :=
    hdRo7CKCoordAux_centralizer_K_le_zpowers_y n hy τ hp3 h0 hmodel hc'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcy
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hyp : y ^ p = 1 := hdRo7CKCoordAux_y_pow_eq_one hH
  let c : ℕ := (k % (p : ℤ)).toNat
  have hc_cast : (c : ℤ) = k % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k hpz)
  have hkc : y ^ c = c' := by
    rw [← hk]
    calc y ^ c = y ^ ((c : ℤ)) := (zpow_natCast y c).symm
      _ = y ^ (k % (p : ℤ)) := by rw [hc_cast]
      _ = y ^ k := (zpow_eq_zpow_emod k (by rw [zpow_natCast]; exact hyp)).symm
  have hcomm : Commute t y :=
    show t * y = y * t from IsElemAbelian.comm hH.1.tableB_facts.2.1 ht.1 hy
  refine ⟨c, t, ht, ?_⟩
  rw [← hx_eq, ← hkc]
  exact (hcomm.pow_right c).eq

theorem hdRo7CKCoordAux_component_K_z (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) (z : G) (hz : z ∈ Bs ⊓ K) (c : ℕ)
    (hxz : x = y ^ c * z) :
    CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨labJ, labK, hΛJ, -, hJlab, -, hp3, hBCJ, hnJ, -, -, hrankKJ⟩ := hrow
  have hrJ : 1 ≤ labJ.rank := by
    have h2 : 2 ≤ labJ.rank := by
      unfold LargeEvenInLambda2 at hΛJ
      rcases hBCJ with hB | hC
      · rw [hB] at hΛJ; exact hΛJ.2.1
      · rw [hC] at hΛJ; exact hΛJ.2.1
    omega
  have h3Q : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    hdRo7CKCoordAux_three_dvd_quotient labJ.tag labJ.rank labJ.n hJlab hBCJ hnJ hrJ
  have h3J : 3 ∣ Nat.card ↥J :=
    h3Q.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  have hpJ : p ∣ Nat.card J := by rw [hp3]; exact h3J
  have hnbr := hH.2.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnbr
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := hH.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hJx : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnbr hJK
  have hyK : ∀ t : G, t ∈ K → t * y = y * t := by
    intro t htK
    have h := (hnbr.1.2.2.2.1 htK : t ∈ Subgroup.centralizer ({y} : Set G))
    rwa [Subgroup.mem_centralizer_singleton_iff] at h
  have hcent : K ⊓ Subgroup.centralizer ({x} : Set G) =
      K ⊓ Subgroup.centralizer ({z} : Set G) := by
    apply le_antisymm
    · rintro t ⟨htK, htC⟩
      refine ⟨htK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have htC' : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.mp htC
      have hcomm : t * (y ^ c)⁻¹ = (y ^ c)⁻¹ * t :=
        ((show Commute t y from hyK t htK).pow_right c).inv_right.eq
      have hz_eq : z = (y ^ c)⁻¹ * x := by rw [hxz]; group
      calc t * z = t * ((y ^ c)⁻¹ * x) := by rw [hz_eq]
        _ = (t * (y ^ c)⁻¹) * x := by rw [mul_assoc]
        _ = ((y ^ c)⁻¹ * t) * x := by rw [hcomm]
        _ = (y ^ c)⁻¹ * (t * x) := by rw [mul_assoc]
        _ = (y ^ c)⁻¹ * (x * t) := by rw [htC']
        _ = ((y ^ c)⁻¹ * x) * t := by rw [mul_assoc]
        _ = z * t := by rw [hz_eq]
    · rintro t ⟨htK, htC⟩
      refine ⟨htK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have htC' : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp htC
      have hcomm : t * (y ^ c) = (y ^ c) * t :=
        (show Commute t y from hyK t htK).pow_right c |>.eq
      calc t * x = t * (y ^ c * z) := by rw [hxz]
        _ = (t * (y ^ c)) * z := by rw [mul_assoc]
        _ = ((y ^ c) * t) * z := by rw [hcomm]
        _ = (y ^ c) * (t * z) := by rw [mul_assoc]
        _ = (y ^ c) * (z * t) := by rw [htC']
        _ = ((y ^ c) * z) * t := by rw [mul_assoc]
        _ = x * t := by rw [hxz]
  rw [hcent] at hJx
  exact hJx

theorem hdRo7CKCoordAux_support_of_statedSp
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J K) (n : ℕ) (hy : y ∈ Bs)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (hp3 : p = 3) (hn : 5 ≤ n)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (hmodel : C2CoordModel p Bs K n τ)
    (hmem : ∀ f : Fin (n + 1) → Multiplicative (ZMod p), ((τ f : ↥Bs) : G) ∈ K ↔ f 0 = 1)
    (m : ℕ) (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K)
    (z : G) (hz : z ∈ Bs ⊓ K)
    (hJz : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({z} : Set G))) :
    ∃ i j : Fin (n + 1), i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧
      ∀ l : Fin (n + 1), l ≠ 0 →
        (Multiplicative.toAdd (τ.symm ⟨z, hz.1⟩ l) ≠ 0 ↔ l = i ∨ l = j) := by
  have hzK : z ∈ φ.range := by rw [hrange]; exact hz.2
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hzK
  have htE : t ∈ (Bs ⊓ K).comap φ := by
    rw [Subgroup.mem_comap]; rw [ht]; exact hz
  have hEab : IsElemAbelian 3 ((Bs ⊓ K).comap φ) :=
    hdRo7CKCoordAux_E_elemAbelian hH hp3 φ hinj
  have hEsc : ∀ Z : StatedSp m (GaloisField 2 1),
      (∀ Y ∈ (Bs ⊓ K).comap φ, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ (Bs ⊓ K).comap φ :=
    hdRo7CKCoordAux_E_selfCentralizing hH hRig hrow hp3 n hy τ h0 hmodel φ hinj hrange
  obtain ⟨L, hLf, hAlg, hMF, ζ, hdim, hζ, F, hFs, c, hc⟩ :=
    hdRo7CKCoordAux_frame_of_K (m := m) φ hEab hEsc t htE
  haveI : Module.Finite (GaloisField 2 1) L := hMF
  obtain ⟨labJ, labK, hΛJ, hΛK, hJlab, hKlab, hrowBC, hrankK, hrankJ⟩ :=
    hdRo7CKCoordAux_rank_K_eq_m hH hrow φ hinj hrange
  have hnJ : labJ.n = 1 := hrowBC.2.2.1
  have htagJ : labJ.tag = .B ∨ labJ.tag = .C := hrowBC.2.1
  have hrankKJ : labK.rank = labJ.rank + 2 := hrowBC.2.2.2.2.2
  have hm5 : 5 ≤ m := by
    have h5 := hdRo7CLCoordAux_rank_ge_five hΛJ hnJ htagJ hrankKJ
    omega
  have hJ' := hdRo7CKCoordAux_component_comap φ hinj hrange t z ht hJz
  have hlab_eq : (⟨labJ.tag, m - 2, 1⟩ : LargeEvenLabel) = labJ := by
    cases labJ with
    | mk tag rank n => simp_all
  have hlabel : GGHasLabel ⟨labJ.tag, m - 2, 1⟩
      (↥(J.comap φ) ⧸ Subgroup.center ↥(J.comap φ)) := by
    rw [hdRo7CKCoordAux_label_comap φ hinj hrange (hJz.1.trans inf_le_left)]
    rw [hlab_eq]
    exact hJlab
  rw [← hc] at hJ'
  have hsupp_c := hdRo7CKCoordAux_supp_frame (hRig := hRig) (ζ := ζ) hζ hdim (m := m) hm5
    F c (J.comap φ) hJ' htagJ hlabel
  exact hdRo7CKCoordAux_coord_transfer_core hRig n hy hz τ hp3 hn h0 hmodel hmem φ hinj hrange
    F c t hc ht rfl hsupp_c

theorem hdRo7CKCoordAux_support_transfer {G : Type} [Group G] {p : ℕ}
    {Bs : Subgroup G} {x y z : G} (n : ℕ)
    (hy : y ∈ Bs) (hx : x ∈ Bs) (hz : z ∈ Bs)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (c : ℕ) (hxz : x = y ^ c * z) :
    ∀ l : Fin (n + 1), l ≠ 0 →
      (Multiplicative.toAdd (τ.symm ⟨x, hx⟩ l) ≠ 0 ↔
        Multiplicative.toAdd (τ.symm ⟨z, hz⟩ l) ≠ 0) := by
  have hsym : τ.symm ⟨y, hy⟩ =
      Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) 0
        (Multiplicative.ofAdd (1 : ZMod p)) := by
    have h := congrArg τ.symm h0
    simpa using h.symm
  have hx_eq : (⟨x, hx⟩ : ↥Bs) = ⟨y, hy⟩ ^ c * ⟨z, hz⟩ := Subtype.ext (by simpa using hxz)
  have hcoord : τ.symm ⟨x, hx⟩ = (τ.symm ⟨y, hy⟩) ^ c * τ.symm ⟨z, hz⟩ := by
    have h := congrArg τ.symm hx_eq
    simpa only [map_mul, map_pow] using h
  intro l hl
  have hsingle : (τ.symm ⟨y, hy⟩) l = 1 := by
    rw [hsym, Pi.mulSingle_apply, if_neg hl]
  have key : Multiplicative.toAdd (τ.symm ⟨x, hx⟩ l) =
      Multiplicative.toAdd (τ.symm ⟨z, hz⟩ l) := by
    have h1 : τ.symm ⟨x, hx⟩ l = ((τ.symm ⟨y, hy⟩) l) ^ c * (τ.symm ⟨z, hz⟩ l) :=
      congrFun hcoord l
    rw [h1, hsingle, one_pow, one_mul]
  rw [key]

end CFSG.StandardType.HdRo7C

end
