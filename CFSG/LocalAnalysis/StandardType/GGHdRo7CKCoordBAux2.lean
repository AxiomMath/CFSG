module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBCore
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordAAux2
public import CFSG.LocalAnalysis.StandardType.GGTPNI1BCComm
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_E_elemAbelian {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ) :
    IsElemAbelian 3 ((Bs ⊓ K).comap φ) := by
  have hBs_ab : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hcomap : IsElemAbelian p (Bs.comap φ) := IsElemAbelian.comap hBs_ab hinj
  have hle : (Bs ⊓ K).comap φ ≤ Bs.comap φ := by
    intro g hg
    rw [Subgroup.mem_comap] at hg ⊢
    exact hg.1
  have hsub : IsElemAbelian p ((Bs ⊓ K).comap φ) := IsElemAbelian.mono hcomap hle
  rw [hp3] at hsub
  exact hsub

private lemma hdRo7CKCoordAux_ofAdd_pow {p : ℕ} (a : ZMod p) (n : ℕ) :
    (Multiplicative.ofAdd a) ^ n = Multiplicative.ofAdd ((n : ZMod p) * a) := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih]; simp [add_mul]

theorem hdRo7CKCoordAux_centralizer_K_le_zpowers_y {G : Type} [Group G]
    {p : ℕ} {Bs K : Subgroup G} {y : G}
    (n : ℕ) (hy : y ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hp3 : p = 3)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (hmodel : C2CoordModel p Bs K n τ) :
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
  subst hp3
  intro b hb
  obtain ⟨hbB, hbC⟩ := hb
  let Stab : Subgroup (MulAut ↥Bs) :=
    { carrier := {a | a ⟨b, hbB⟩ = ⟨b, hbB⟩}
      one_mem' := rfl
      mul_mem' := by
        rintro x y hx hy
        show (x * y) ⟨b, hbB⟩ = ⟨b, hbB⟩
        rw [MulAut.mul_apply, hy, hx]
      inv_mem' := by
        rintro x hx
        show x⁻¹ ⟨b, hbB⟩ = ⟨b, hbB⟩
        have h := congrArg (fun z => x⁻¹ z) hx
        simpa using h.symm }
  have hgen : ggInduced K Bs ⊆ ↑Stab := by
    rintro a ⟨g, hgK, -, hgact⟩
    show a ⟨b, hbB⟩ = ⟨b, hbB⟩
    apply Subtype.ext
    rw [hgact ⟨b, hbB⟩]
    show g * b * g⁻¹ = b
    have hcomm : g * b = b * g := Subgroup.mem_centralizer_iff.mp hbC g hgK
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : ∀ a ∈ ggAutomizer K Bs, a ⟨b, hbB⟩ = ⟨b, hbB⟩ := by
    intro a ha
    exact (Subgroup.closure_le Stab).mpr hgen ha
  let f : Fin (n + 1) → Multiplicative (ZMod 3) := τ.symm ⟨b, hbB⟩
  have hbf : τ f = ⟨b, hbB⟩ := MulEquiv.apply_symm_apply τ ⟨b, hbB⟩
  have hfl : ∀ l : Fin (n + 1), l ≠ 0 → f l = 1 := by
    intro l hl
    let a : MulAut ↥Bs := (τ.symm.trans (SpCoord.sgnAut l)).trans τ
    have ha_apply : ∀ g : Fin (n + 1) → Multiplicative (ZMod 3),
        a (τ g) = τ (SpCoord.sgnAut l g) := by
      intro g
      change τ (SpCoord.sgnAut l (τ.symm (τ g))) = τ (SpCoord.sgnAut l g)
      rw [MulEquiv.symm_apply_apply]
    have ha_mem : a ∈ ggAutomizer K Bs := by
      rw [hmodel a]
      refine ⟨Equiv.refl _, (fun i => if i = l then -1 else 1), rfl, ?_, ?_, ?_⟩
      · show (if (0 : Fin (n + 1)) = l then -1 else 1) = 1
        rw [if_neg (Ne.symm hl)]
      · intro i
        by_cases hi : i = l
        · right; simp [hi]
        · left; simp [hi]
      · intro g i
        change Multiplicative.toAdd (τ.symm (a (τ g)) i) =
          (if i = l then -1 else 1) * Multiplicative.toAdd (g i)
        rw [ha_apply g, MulEquiv.symm_apply_apply, SpCoord.sgnAut_apply]
        by_cases hi : i = l
        · subst hi
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hi, if_neg hi, one_mul]
    have hfixed : a (τ f) = τ f := by
      have h := hfix a ha_mem
      rwa [← hbf] at h
    have h1 : τ (SpCoord.sgnAut l f) = τ f := by
      rw [← ha_apply f]; exact hfixed
    have hsgnf : SpCoord.sgnAut l f = f := τ.injective h1
    have hcoord := congrFun hsgnf l
    rw [SpCoord.sgnAut_apply, Function.update_self] at hcoord
    have hneg : -(Multiplicative.toAdd (f l)) = Multiplicative.toAdd (f l) := by
      have := congrArg Multiplicative.toAdd hcoord
      simpa using this
    have hzero : Multiplicative.toAdd (f l) = 0 := by
      have h : ∀ a : ZMod 3, -a = a → a = 0 := by decide
      exact h _ hneg
    exact Multiplicative.toAdd.injective (by simpa using hzero)
  have hf : f = Pi.mulSingle (M := fun _ => Multiplicative (ZMod 3)) 0 (f 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi; rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_apply, if_neg hi]; exact hfl i hi
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨((Multiplicative.toAdd (f 0)).val : ℤ), ?_⟩
  rw [zpow_natCast]
  have hthis : (⟨y, hy⟩ : ↥Bs) ^ (Multiplicative.toAdd (f 0)).val = ⟨b, hbB⟩ := by
    rw [← hbf, hf, show (⟨y, hy⟩ : ↥Bs) =
      τ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod 3)) 0
        (Multiplicative.ofAdd (1 : ZMod 3))) from h0.symm]
    rw [← map_pow]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same,
        hdRo7CKCoordAux_ofAdd_pow, mul_one, ZMod.natCast_zmod_val]
      exact Multiplicative.ofAdd.apply_symm_apply (f 0)
    · simp [Pi.pow_apply, Pi.mulSingle_apply, hi]
  simpa using (Subgroup.coe_pow Bs ⟨y, hy⟩ _).symm.trans (congrArg Subtype.val hthis)

theorem hdRo7CKCoordAux_E_selfCentralizing
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowCorank2C p J K) (hp3 : p = 3)
    (n : ℕ) (hy : y ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (h0 : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩)
    (hmodel : C2CoordModel p Bs K n τ)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K) :
    ∀ Z : StatedSp m (GaloisField 2 1),
      (∀ Y ∈ (Bs ⊓ K).comap φ, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ (Bs ⊓ K).comap φ := by
  obtain ⟨R, hRgrp, I, θ, hBsN, -, -, -, -, hI, hBs3⟩ :=
    hdRo7CKCoordAux_torus_data hRig hH hrow
  letI : Group R := hRgrp
  have hZK : Subgroup.center ↥K = ⊥ := hdRo7CKCoordAux_center_K_eq_bot hH hrow
  have hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹ :=
    hdRo7CKCoordAux_hinner p B Bs x L D J y K hH R I θ hI hZK hBsN hBs3
  let Φ := hdRo7CKCoordAux_split_equiv p B Bs x L D J y K hH hZK hBsN hinner
  have hCyle : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y :=
    hdRo7CKCoordAux_centralizer_K_le_zpowers_y n hy τ hp3 h0 hmodel
  have hnbr := hH.2.2.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnbr.1.2.2.2.1
  intro Z hZcomm hZ3
  rw [Subgroup.mem_comap]
  have hZKmem : φ Z ∈ K := by
    rw [← hrange]; exact ⟨Z, rfl⟩
  have hZBs : φ Z ∈ Bs := by
    refine hH.1.2.1.2.2.2 (φ Z) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨⟨⟨t, ht⟩, ⟨c, hc⟩⟩, htc⟩ := Φ.surjective ⟨b, hb⟩
      have hbc : t * c = b := by
        have h := congrArg Subtype.val htc
        rw [hdRo7CKCoordAux_split_equiv_apply] at h
        exact h
      obtain ⟨t', ht'⟩ := MonoidHom.mem_range.mp (show t ∈ φ.range by rw [hrange]; exact ht.2)
      have ht'E : t' ∈ (Bs ⊓ K).comap φ := by
        rw [Subgroup.mem_comap, ht']; exact ht
      have hZt' : Commute Z t' := show Z * t' = t' * Z from hZcomm t' ht'E
      have hcomm_t : Commute (φ Z) t := by rw [← ht']; exact hZt'.map φ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hCyle hc)
      have hZy : Commute (φ Z) y := by
        have h := hKy hZKmem
        rwa [Subgroup.mem_centralizer_singleton_iff] at h
      have hcomm_c : Commute (φ Z) c := by
        show φ Z * c = c * φ Z
        rw [← hk]
        exact (hZy.zpow_right k).eq
      rw [← hbc]
      calc (t * c) * φ Z = t * (c * φ Z) := by rw [mul_assoc]
        _ = t * (φ Z * c) := by rw [hcomm_c.eq.symm]
        _ = (t * φ Z) * c := by rw [mul_assoc]
        _ = (φ Z * t) * c := by rw [hcomm_t.eq.symm]
        _ = φ Z * (t * c) := by rw [mul_assoc]
    · rw [hp3, ← map_pow, hZ3, map_one]
  exact ⟨hZBs, hZKmem⟩

theorem hdRo7CKCoordAux_frame_of_K {G : Type} [Group G]
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G)
    {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (hEab : IsElemAbelian 3 E)
    (hEsc : ∀ Z : StatedSp m (GaloisField 2 1),
      (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E)
    (t : StatedSp m (GaloisField 2 1)) (ht : t ∈ E) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (GaloisField 2 1) L)
      (_ : Module.Finite (GaloisField 2 1) L) (ζ : L)
      (_ : Module.finrank (GaloisField 2 1) L = 2) (_ : IsPrimitiveRoot ζ 3)
      (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E),
      F.s = m ∧ ∃ c : Fin F.s → ZMod 3, F.tor c = t := by
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨L, hLf, hAlg, hMF, ζ, hdim, hζ, ⟨F⟩⟩ :=
    A6InsideSp.exists_frame_two (K := GaloisField 2 1) (n := m) hK hEab hEsc
  haveI : Module.Finite (GaloisField 2 1) L := hMF
  obtain ⟨c, hc⟩ := F.mem_tor t ht
  exact ⟨L, hLf, hAlg, hMF, ζ, hdim, hζ, F, A6InsideSp.s_eq F hdim, c, hc⟩

theorem hdRo7CKCoordAux_supp_frame (hRig : GGLabelRigidInput)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L] [Module.Finite (GaloisField 2 1) L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (hdim : Module.finrank (GaloisField 2 1) L = 2)
    {m : ℕ} (hm : 5 ≤ m) {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (J' : Subgroup (StatedSp m (GaloisField 2 1)))
    (hJ' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({F.tor c} : Set (StatedSp m (GaloisField 2 1)))))
    {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C)
    (hlabel : GGHasLabel ⟨tag, m - 2, 1⟩ (↥J' ⧸ Subgroup.center ↥J')) :
    (F.suppSet c).card = 2 :=
  hdRo7CKCoordAux_supp_frame_core hRig hζ hdim hm F c J' hJ' htag hlabel

theorem hdRo7CKCoordAux_component_comap {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G)
    (hinj : Function.Injective φ) (hrange : φ.range = K)
    (t : StatedSp m (GaloisField 2 1)) (z : G) (htz : φ t = z)
    (hJ : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({z} : Set G))) :
    CFSG.Assembly.IsComponentOf (J.comap φ)
      (Subgroup.centralizer ({t} : Set (StatedSp m (GaloisField 2 1)))) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hKcomap : K.comap φ = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    rw [Subgroup.mem_comap, ← hrange]
    exact ⟨x, rfl⟩
  have hcen : (Subgroup.centralizer ({z} : Set G)).comap φ =
      Subgroup.centralizer ({t} : Set (StatedSp m (GaloisField 2 1))) := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply hinj
      rw [map_mul, map_mul, htz]
      exact h
    · intro h
      rw [← htz, ← map_mul, ← map_mul, h]
  have hcomap_eq : (K ⊓ Subgroup.centralizer ({z} : Set G)).comap φ =
      Subgroup.centralizer ({t} : Set (StatedSp m (GaloisField 2 1))) := by
    rw [Subgroup.comap_inf, hKcomap, hcen, top_inf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcomap_eq]; exact Subgroup.comap_mono hJ.1
  · rw [← hcomap_eq]; exact hJ.2.1.comap φ
  · have hmap : (J.comap φ).map φ = J :=
      Subgroup.map_comap_eq_self (by rw [hrange]; exact hJK)
    let e : ↥(J.comap φ) ≃* ↥J :=
      (Subgroup.equivMapOfInjective (J.comap φ) φ hinj).trans (MulEquiv.subgroupCongr hmap)
    exact Assembly.IsQuasisimple.of_mulEquiv e hJ.2.2

theorem hdRo7CKCoordAux_label_comap {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G)
    (hinj : Function.Injective φ) (hrange : φ.range = K) (hJK : J ≤ K) (lab : LargeEvenLabel) :
    GGHasLabel lab (↥(J.comap φ) ⧸ Subgroup.center ↥(J.comap φ)) ↔
      GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
  have hle : J ≤ φ.range := by rw [hrange]; exact hJK
  have hmap : (J.comap φ).map φ = J := Subgroup.map_comap_eq_self hle
  let e : ↥(J.comap φ) ≃* ↥J :=
    (Subgroup.equivMapOfInjective (J.comap φ) φ hinj).trans (MulEquiv.subgroupCongr hmap)
  have hc : (Subgroup.center ↥(J.comap φ)).map (e : ↥(J.comap φ) →* ↥J) =
      Subgroup.center ↥J := Subgroup.map_center_eq e
  let e' : (↥(J.comap φ) ⧸ Subgroup.center ↥(J.comap φ)) ≃*
      (↥J ⧸ Subgroup.center ↥J) := QuotientGroup.congr _ _ e hc
  exact ⟨fun h => ggHasLabel_of_mulEquiv e' h, fun h => ggHasLabel_of_mulEquiv e'.symm h⟩

private theorem hdRo7CKCoordAux_card_statedSp_congr {K K' : Type} [Field K] [Finite K]
    [Field K'] [Finite K'] (h : Nat.card K = Nat.card K') (r : ℕ) :
    Nat.card (StatedSp r K) = Nat.card (StatedSp r K') := by
  induction r with
  | zero =>
    haveI : Subsingleton (StatedSp 0 K) := inferInstance
    haveI : Nonempty (StatedSp 0 K) := ⟨1⟩
    haveI : Subsingleton (StatedSp 0 K') := inferInstance
    haveI : Nonempty (StatedSp 0 K') := ⟨1⟩
    rw [Nat.card_unique, Nat.card_unique]
  | succ r ih => rw [tpbcB_card_statedSp_succ K r, tpbcB_card_statedSp_succ K' r, ih, h]

theorem hdRo7CKCoordAux_rank_K_eq_m
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K) :
    ∃ labJ labK : LargeEvenLabel,
      LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labK ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) ∧
      ggRowCorank2C p labJ labK ∧ labK.rank = m ∧ labJ.rank = m - 2 := by
  have hZK : Subgroup.center ↥K = ⊥ := hdRo7CKCoordAux_center_K_eq_bot hH hrow
  obtain ⟨labJ, labK, hΛJ, hΛK, hJlab, hKlab, hp3, htagJ, hnJ, htagK, hnK, hrankKJ⟩ := hrow
  have h1n : 1 ≤ labK.n := by omega
  have h4 : 4 ≤ labK.rank := by
    have h5 : 5 ≤ labK.rank := hdRo7CLCoordAux_rank_ge_five hΛJ hnJ htagJ (by
      have := hrankKJ; omega)
    omega
  have hmodelK : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSp labK.rank 2 1 := by
    have h := hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htagK (by omega) h1n hKlab
    rwa [hnK] at h
  obtain ⟨K', hK'f, hK'fin, hK'card, ⟨e'⟩⟩ := hmodelK.2
  letI : Field K' := hK'f
  letI : Finite K' := hK'fin
  haveI : CharP K' 2 := charP_two_of_card hK'card
  have hcardKZ : Nat.card (↥K ⧸ Subgroup.center ↥K) = Nat.card ↥K := by
    rw [hZK]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥K)).toEquiv
  have hcardKSp : Nat.card ↥K = Nat.card (StatedSp m (GaloisField 2 1)) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcardZ : Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (StatedProj (StatedSp labK.rank K')) := Nat.card_congr e'.toEquiv
  have hproj : Nat.card (StatedProj (StatedSp labK.rank K')) =
      Nat.card (StatedSp labK.rank K') := by
    rw [StatedProj, CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := StatedSp labK.rank K')).toEquiv
  have hK'2 : Nat.card K' = 2 := by rw [hK'card]; norm_num
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]; norm_num
  have hcard_field : Nat.card (StatedSp labK.rank K') =
      Nat.card (StatedSp labK.rank (GaloisField 2 1)) :=
    hdRo7CKCoordAux_card_statedSp_congr (by rw [hK'2, hF2]) labK.rank
  have hEq : Nat.card (StatedSp m (GaloisField 2 1)) =
      Nat.card (StatedSp labK.rank (GaloisField 2 1)) := by
    rw [← hcardKSp, ← hcardKZ, hcardZ, hproj, hcard_field]
  have hrank : labK.rank = m :=
    ((tpbcB_card_statedSp_strictMono (GaloisField 2 1)).injective hEq).symm
  exact ⟨labJ, labK, hΛJ, hΛK, hJlab, hKlab,
    ⟨hp3, htagJ, hnJ, htagK, hnK, hrankKJ⟩, hrank, by omega⟩

end CFSG.StandardType.HdRo7C

end
