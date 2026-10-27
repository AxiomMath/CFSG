module

public import CFSG.LocalAnalysis.WeakClosure81.W16QSetup
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIc
public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

structure DichCfg (M V₀ V U S H : Subgroup G) {X : Type} [Group X]
    (φ : ↥(conjClosure V H) →* X) : Prop where
  cfg : Cfg1616 M V₀ V U S H
  bar : SevenK.IsBarMap (conjClosure V H) (iSub16 V H) φ
  shape : Shape166 X (SevenK.barSub (conjClosure V H) φ V) (E3.mQuot V (iSub16 V H))
  o2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥

private theorem w16q_odd_card_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = pPrimeCore 2 X := by
    unfold fusionOddCore pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))

private theorem w16q_odd_sq_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) :
    Odd ((2 ^ n) ^ 2 - 1) := by
  have hpos : 0 < 2 ^ n := by positivity
  have h3 : 2 ≤ (2 ^ n) ^ 2 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ (2 ^ n) ^ 2 := by
        rw [sq]
        exact Nat.le_mul_of_pos_left _ hpos
  have h4 : Even ((2 ^ n) ^ 2) := by
    rw [← pow_mul]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨k, hk⟩ := h4
  exact ⟨k - 1, by omega⟩

private theorem w16q_nonempty_psl_equiv_of_isPSL {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n X) : Nonempty (X ≃* PSL(2, GaloisField 2 n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [CFSG.Quasithin.IsPSL, CFSG.Open.StatedClassicalModel] at h
  obtain ⟨hadm, K, _hField, _hFinite, hcard, ⟨e⟩⟩ := h
  have hn : 0 < n := by have := hadm.2.1; omega
  exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 n hn hcard)⟩

private theorem w16q_mQuot_inf_centralizer_le_mSub {V V₀ : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀V : V₀ ≤ V) {w : G}
    (hcomm : ∀ v ∈ V, w * v * w⁻¹ * v⁻¹ ∈ V₀) :
    E3.mQuot V (V ⊓ Subgroup.centralizer ({w} : Set G)) ≤ mSub V₀ := by
  let f : V →* G :=
    { toFun := fun a => w * (a : G) * w⁻¹ * (a : G)⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        let ca : G := w * (a : G) * w⁻¹ * (a : G)⁻¹
        let cb : G := w * (b : G) * w⁻¹ * (b : G)⁻¹
        have haV : ca ∈ V := hV₀V (hcomm a a.2)
        have hbV : cb ∈ V := hV₀V (hcomm b b.2)
        have haw : w * (a : G) * w⁻¹ = ca * (a : G) := by
          change w * (a : G) * w⁻¹ = (w * (a : G) * w⁻¹ * (a : G)⁻¹) * (a : G)
          group
        have hbw : w * (b : G) * w⁻¹ = cb * (b : G) := by
          change w * (b : G) * w⁻¹ = (w * (b : G) * w⁻¹ * (b : G)⁻¹) * (b : G)
          group
        have hacb : (a : G) * cb = cb * (a : G) := B2F.isElemAbelian_comm hV a.2 hbV
        have hconj : (a : G) * cb * (a : G)⁻¹ = cb := by rw [hacb]; group
        show w * ((a * b : V) : G) * w⁻¹ * ((a * b : V) : G)⁻¹ = ca * cb
        rw [Subgroup.coe_mul]
        calc w * ((a : G) * (b : G)) * w⁻¹ * ((a : G) * (b : G))⁻¹
            = (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹) * (b : G)⁻¹ * (a : G)⁻¹ := by
              group
          _ = (ca * (a : G)) * (cb * (b : G)) * (b : G)⁻¹ * (a : G)⁻¹ := by rw [haw, hbw]
          _ = ca * ((a : G) * cb * (a : G)⁻¹) := by group
          _ = ca * cb := by rw [hconj] }
  have hker : f.ker = (V ⊓ Subgroup.centralizer ({w} : Set G)).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, fun y hy => ?_⟩
      have hyw : y = w := Set.mem_singleton_iff.mp hy
      have h1 : w * (x : G) * w⁻¹ = (x : G) := mul_inv_eq_one.1 h
      calc y * (x : G) = w * (x : G) := by rw [hyw]
        _ = (w * (x : G) * w⁻¹) * w := by group
        _ = (x : G) * w := by rw [h1]
        _ = (x : G) * y := by rw [hyw]
    · rintro ⟨-, hc⟩
      have hwx : w * (x : G) = (x : G) * w := hc w (Set.mem_singleton w)
      show w * (x : G) * w⁻¹ * (x : G)⁻¹ = 1
      rw [hwx]
      group
  have hrel : (V ⊓ Subgroup.centralizer ({w} : Set G)).relIndex V = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hrange : f.range ≤ V₀ := by
    rintro z ⟨a, rfl⟩
    exact hcomm a a.2
  have hdvd : Nat.card f.range ∣ Nat.card V₀ := Subgroup.card_dvd_of_le hrange
  calc E3.mQuot V (V ⊓ Subgroup.centralizer ({w} : Set G))
      = padicValNat 2 ((V ⊓ Subgroup.centralizer ({w} : Set G)).relIndex V) := rfl
    _ = padicValNat 2 (Nat.card f.range) := by rw [hrel]
    _ ≤ padicValNat 2 (Nat.card V₀) := padicValNat_two_le_of_dvd (Nat.card_pos.ne') hdvd
    _ = mSub V₀ := rfl

private theorem w16q_relIndex_sup_eq_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

private theorem w16q_card_sup_mul_card_inf {X : Type} [Group X] {A N : Subgroup X}
    (hAN : A ≤ Subgroup.normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

private theorem w16q_barSub_conjClosure_le_normalClosure {K A : Subgroup G} (hAK : A ≤ K)
    {X : Type} [Group X] (φ : ↥K →* X) :
    SevenK.barSub K φ (CFSG.Quasithin.conjClosure A K) ≤
      Subgroup.normalClosure ((SevenK.barSub K φ A : Subgroup X) : Set X) := by
  let N : Subgroup X := Subgroup.normalClosure ((SevenK.barSub K φ A : Subgroup X) : Set X)
  have hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hNle : SevenK.barSub K φ A ≤ N := Subgroup.le_normalClosure
  have hL : CFSG.Quasithin.conjClosure A K ≤ (N.comap φ).map K.subtype := by
    refine CFSG.Quasithin.conjClosure_le fun h hh a ha => ?_
    let hK : ↥K := ⟨h, hh⟩
    let aK : ↥K := ⟨a, hAK ha⟩
    have hφa : φ aK ∈ N := hNle (SevenK.mem_barSub.mpr ⟨aK, ha, rfl⟩)
    have hconj : φ hK * φ aK * (φ hK)⁻¹ ∈ N := hNnorm.conj_mem (φ aK) hφa (φ hK)
    refine Subgroup.mem_map.mpr ⟨hK * aK * hK⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hconj
  calc SevenK.barSub K φ (CFSG.Quasithin.conjClosure A K)
      = ((CFSG.Quasithin.conjClosure A K).subgroupOf K).map φ := rfl
    _ ≤ (((N.comap φ).map K.subtype).subgroupOf K).map φ :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono K hL)
    _ = (N.comap φ).map φ := by
        rw [← Subgroup.comap_subtype ((N.comap φ).map K.subtype) K,
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    _ ≤ N := Subgroup.map_comap_le φ N

theorem Cfg1616.mQuot_le_mSub {M V₀ V U S H : Subgroup G} (c : Cfg1616 M V₀ V U S H) :
    E3.mQuot V (iSub16 V H) ≤ mSub V₀ := by
  obtain ⟨g, hgK, hgM⟩ := Set.not_subset.1 c.not_conjClosure_le
  have hgH : g ∈ H := c.conjClosure_le_H hgK
  have hgC : g ∈ centralizer (U : Set G) := c.conjClosure_le_centralizer hgK
  have hV0_le_I : V₀ ≤ iSub16 V H := le_sup_right.trans c.le_iSub16
  have hW_le_I : conjSubgroup V₀ g ≤ iSub16 V H := by
    calc conjSubgroup V₀ g ≤ conjSubgroup (iSub16 V H) g := conjSubgroup_mono hV0_le_I g
      _ = iSub16 V H :=
        conjSubgroup_eq_iff_mem_normalizer.mpr
          (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hgH)
  have hWne : conjSubgroup V₀ g ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(conjSubgroup V₀ g) = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card ↥V₀ = 1 := by
      rwa [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h1
    exact c.cex.hyp.ne_bot (Subgroup.card_eq_one.mp h2)
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hWne
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwS : (w : G) ∈ S := (c.iSub16_le_tSub16 (hW_le_I w.2)).1
  have hC : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V :=
    hW_le_I.trans (c.iSub16_le_tSub16.trans (inf_le_left.trans c.cex.S_le_cTilde))
  have hcen : V ⊓ Subgroup.centralizer ({(w : G)} : Set G) = U ⊔ V₀ :=
    Cex16.inf_centralizer_eq c.one c.five c.fifteen c.std c.cex hgC hgM hC w.2 hw1'
  have hcomm : ∀ v ∈ V, (w : G) * v * (w : G)⁻¹ * v⁻¹ ∈ V₀ :=
    fun v hv => c.cex.comm_mem_V₀ hwS hv
  have hstep : E3.mQuot V (V ⊓ Subgroup.centralizer ({(w : G)} : Set G)) ≤ mSub V₀ :=
    w16q_mQuot_inf_centralizer_le_mSub c.cex.hyp.h6.elemAbelian c.cex.hyp.h6.le hcomm
  have hmq : E3.mQuot V (iSub16 V H) = E3.mQuot V (V ⊓ iSub16 V H) := by
    unfold E3.mQuot
    rw [← Subgroup.inf_relIndex_right (H := iSub16 V H) (K := V), inf_comm (iSub16 V H) V]
  calc E3.mQuot V (iSub16 V H)
      = E3.mQuot V (V ⊓ iSub16 V H) := hmq
    _ = E3.mQuot V (U ⊔ V₀) := by
        rw [Cex16.inf_iSub16_eq c.one c.five c.std c.cex c.min.fam16 c.not_le]
    _ = E3.mQuot V (V ⊓ Subgroup.centralizer ({(w : G)} : Set G)) := by rw [← hcen]
    _ ≤ mSub V₀ := hstep

theorem card_le_of_isPGroup_psl {X : Type} [Group X] [Finite X] {n : ℕ} (hn : n ≠ 0)
    (h : CFSG.Quasithin.IsPSL 2 2 n X) :
    ∀ P : Subgroup X, IsPGroup 2 P → Nat.card P ≤ 2 ^ n := by
  intro P hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  obtain ⟨e⟩ := w16q_nonempty_psl_equiv_of_isPSL h
  let e' : X ≃* SL(2, GaloisField 2 n) :=
    e.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 n))
  let P' : Subgroup SL(2, GaloisField 2 n) := P.map e'.toMonoidHom
  have hP' : IsPGroup 2 P' := hP.map e'.toMonoidHom
  have hcard : Nat.card P' = Nat.card P := Subgroup.card_map_of_injective e'.injective
  rw [← hcard]
  have hdvd : Nat.card P' ∣ Nat.card SL(2, GaloisField 2 n) :=
    Subgroup.card_subgroup_dvd_card P'
  rw [CFSG.CGT.Timmesfeld75.card_sl2, GaloisField.card 2 n hn] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP'
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ n) ^ 2 - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (w16q_odd_sq_two_pow_sub_one hn1))
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem card_le_of_isPGroup_oddCore {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (hY : Nat.card Y = 2) (hX : Y ⊔ fusionOddCore X = ⊤) :
    ∀ P : Subgroup X, IsPGroup 2 P → Nat.card P ≤ 2 := by
  intro P hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (fusionOddCore X)) := w16q_odd_card_fusionOddCore X
  have hcop : Nat.Coprime 2 (Nat.card (fusionOddCore X)) := Nat.coprime_two_left.mpr hOodd
  have hinf : Y ⊓ fusionOddCore X = ⊥ := by
    refine Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop ?_ ?_)
    · rw [← hY]; exact Subgroup.card_dvd_of_le inf_le_left
    · exact Subgroup.card_dvd_of_le inf_le_right
  have hcardX : Nat.card X = 2 * Nat.card (fusionOddCore X) := by
    have hAN : Y ≤ Subgroup.normalizer (fusionOddCore X : Set X) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have h := w16q_card_sup_mul_card_inf hAN
    rw [hX, Subgroup.card_top, hinf, Subgroup.card_bot, mul_one, hY] at h
    exact h
  have hdvd : Nat.card P ∣ Nat.card X := Subgroup.card_subgroup_dvd_card P
  rw [hcardX] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  rw [hk] at hdvd ⊢
  have hcop' : Nat.Coprime (2 ^ k) (Nat.card (fusionOddCore X)) := Nat.Coprime.pow_left k hcop
  exact Nat.le_of_dvd (by norm_num) (hcop'.dvd_of_dvd_mul_right hdvd)

theorem eq_one_of_forall_normalizes_of_card_two {X : Type} [Group X] {Y : Subgroup X}
    (hY : Nat.card Y = 2) (hgen : Subgroup.normalClosure (Y : Set X) = ⊤) (α : MulAut X)
    (hα : ∀ y ∈ Y, α y = y)
    (hN : ∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) : α = 1 := by
  have hfix : ∀ x : X, ∀ z ∈ conjSubgroup Y x, α z = z := by
    intro x z hz
    have hcard : Nat.card ↥(conjSubgroup Y x) = 2 := by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hY]
    have hzmap : α z ∈ conjSubgroup Y x := by
      have : α z ∈ (conjSubgroup Y x).map α.toMonoidHom := ⟨z, hz, rfl⟩
      rwa [hN x] at this
    have huniq : ∀ u ∈ conjSubgroup Y x, ∀ v ∈ conjSubgroup Y x, u ≠ 1 → v ≠ 1 → u = v := by
      intro u hu v hv hu1 hv1
      obtain ⟨w, _hw, hwu⟩ := (Nat.card_eq_two_iff' (1 : ↥(conjSubgroup Y x))).1 hcard
      have hune : (⟨u, hu⟩ : ↥(conjSubgroup Y x)) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
      have hvne : (⟨v, hv⟩ : ↥(conjSubgroup Y x)) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
      exact congrArg Subtype.val ((hwu _ hune).trans (hwu _ hvne).symm)
    by_cases hz1 : z = 1
    · rw [hz1, map_one]
    · have hmap1 : α z ≠ 1 := fun h => hz1 (α.injective (by rw [h, map_one]))
      exact (huniq z hz (α z) hzmap hz1 hmap1).symm
  have hconj : ∀ z ∈ Group.conjugatesOfSet (Y : Set X), α z = z := by
    intro z hz
    obtain ⟨a, ha, hconjax⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨c, hc⟩ := isConj_iff.1 hconjax
    rw [← hc]
    exact hfix c⁻¹ (c * a * c⁻¹)
      (mem_conjSubgroup_iff.2 (by
        have hca : c⁻¹ * (c * a * c⁻¹) * (c⁻¹)⁻¹ = a := by group
        rw [hca]; exact ha))
  refine MulEquiv.ext fun z => ?_
  have hz : z ∈ Subgroup.closure (Group.conjugatesOfSet (Y : Set X)) := by
    have : z ∈ Subgroup.normalClosure (Y : Set X) := by rw [hgen]; trivial
    rwa [Subgroup.normalClosure] at this
  exact Subgroup.closure_induction (p := fun z _ => α z = z)
    (fun a ha => hconj a ha) (map_one α)
    (fun a b _ _ iha ihb => by rw [map_mul, iha, ihb])
    (fun a _ iha => by rw [map_inv, iha]) hz

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem isElemAbelian_barSub (d : DichCfg M V₀ V U S H φ) :
    IsElemAbelian 2 (SevenK.barSub (conjClosure V H) φ V) := by
  have hsub : IsElemAbelian 2 (V.subgroupOf (conjClosure V H)) :=
    d.cfg.cex.hyp.h6.elemAbelian.subgroupOf (conjClosure V H)
  have hmap : IsElemAbelian 2 ((V.subgroupOf (conjClosure V H)).map φ) := hsub.map φ
  simpa [SevenK.barSub] using hmap

theorem qSub16_inf_le (d : DichCfg M V₀ V U S H φ) :
    qSub16 V₀ V S H ⊓ conjClosure V H ≤ iSub16 V H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := qSub16 V₀ V S H
  let K : Subgroup G := conjClosure V H
  have hN_le_K : Q ⊓ K ≤ K := inf_le_right
  have hNnorm : ((Q ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_K]
    exact (le_inf (d.cfg.conjClosure_le_H.trans d.cfg.le_normalizer_qSub16)
      (le_normalizer (H := K))).trans
        (inf_normalizer_le_normalizer_inf (H := Q) (K := K))
  have hN2 : IsPGroup 2 ↥((Q ⊓ K).subgroupOf K) := by
    have h2 : IsPGroup 2 ↥(Q ⊓ K) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
        (inf_le_left.trans d.cfg.qSub16_le_pCoreOf)
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hN_le_K).symm
  have hbot : ((Q ⊓ K).subgroupOf K).map φ = ⊥ :=
    d.o2 _ (hNnorm.map φ d.bar.surjective) (hN2.map φ)
  intro x hx
  have hxmem : (⟨x, hx.2⟩ : ↥K) ∈ (Q ⊓ K).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr ⟨hx.1, hx.2⟩
  have hxphi : φ ⟨x, hx.2⟩ = 1 := by
    have hmem : φ ⟨x, hx.2⟩ ∈ ((Q ⊓ K).subgroupOf K).map φ :=
      Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hxmem, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  exact (d.bar.ker_iff ⟨x, hx.2⟩).1 hxphi

theorem comm_mem_qSub16 (d : DichCfg M V₀ V U S H φ) {x k : G} (hx : x ∈ qSub16 V₀ V S H)
    (hk : k ∈ conjClosure V H) : k * x * k⁻¹ * x⁻¹ ∈ iSub16 V H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ_le_H : qSub16 V₀ V S H ≤ H :=
    d.cfg.qSub16_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hxH : x ∈ H := hQ_le_H hx
  have hkxQ : k * x * k⁻¹ ∈ qSub16 V₀ V S H :=
    (Subgroup.mem_normalizer_iff.mp (d.cfg.le_normalizer_qSub16 (d.cfg.conjClosure_le_H hk))
      x).1 hx
  have hxK : x * k⁻¹ * x⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H hxH) k⁻¹).1
      ((conjClosure V H).inv_mem hk)
  have hcommQ : k * x * k⁻¹ * x⁻¹ ∈ qSub16 V₀ V S H :=
    (qSub16 V₀ V S H).mul_mem hkxQ ((qSub16 V₀ V S H).inv_mem hx)
  have hcommK : k * x * k⁻¹ * x⁻¹ ∈ conjClosure V H := by
    simpa only [mul_assoc] using (conjClosure V H).mul_mem hk hxK
  exact d.qSub16_inf_le ⟨hcommQ, hcommK⟩

theorem mem_of_map_mem (d : DichCfg M V₀ V U S H φ) {A : Subgroup G} (hIA : iSub16 V H ≤ A)
    {k : ↥(conjClosure V H)}
    (hk : φ k ∈ (A.subgroupOf (conjClosure V H)).map φ) : (k : G) ∈ A := by
  obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.1 hk
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hker : φ (a⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hak, inv_mul_cancel]
  have hmem : ((a⁻¹ * k : ↥(conjClosure V H)) : G) ∈ iSub16 V H :=
    (d.bar.ker_iff (a⁻¹ * k)).1 hker
  have hk_eq : (k : G) = (a : G) * ((a⁻¹ * k : ↥(conjClosure V H)) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hk_eq]
  exact A.mul_mem haA (hIA hmem)

theorem mem_sup_of_map_mem_barSub (d : DichCfg M V₀ V U S H φ) {k : ↥(conjClosure V H)}
    (hk : φ k ∈ SevenK.barSub (conjClosure V H) φ V) : (k : G) ∈ V ⊔ iSub16 V H := by
  obtain ⟨a, haV, hak⟩ := SevenK.mem_barSub.mp hk
  refine d.mem_of_map_mem (A := V ⊔ iSub16 V H) le_sup_right ?_
  exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left haV), hak⟩

theorem qSub16_le_tSub16_of_inf_le (d : DichCfg M V₀ V U S H φ)
    (hTK : S ⊓ conjClosure V H ≤ tSub16 V₀ S) : qSub16 V₀ V S H ≤ tSub16 V₀ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylH : IsSylowIn 2 S H := Cex16.isSylowIn_of_fam d.cfg.one d.cfg.std d.cfg.cex
    d.cfg.min.fam16
  have hKH : conjClosure V H ≤ H := d.cfg.conjClosure_le_H
  have hKN : ((conjClosure V H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    exact le_normalizer_conjClosure V H
  have hSylK : IsSylowIn 2 (S ⊓ conjClosure V H) (conjClosure V H) :=
    hSylH.inf_normal hKH hKN
  have hTeq : tSub16 V₀ S ⊓ conjClosure V H = S ⊓ conjClosure V H :=
    le_antisymm (inf_le_inf inf_le_left le_rfl) (le_inf hTK inf_le_right)
  have hSylTK : IsSylowIn 2 (tSub16 V₀ S ⊓ conjClosure V H) (conjClosure V H) := by
    rw [hTeq]; exact hSylK
  have hT2 : IsPGroup 2 (tSub16 V₀ S) := hSylH.isPGroup.to_le inf_le_left
  have hTN : tSub16 V₀ S ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    (inf_le_left.trans d.cfg.min.fam16.1).trans (le_normalizer_conjClosure V H)
  have hrel : (tSub16 V₀ S).relIndex (conjClosure V H ⊔ tSub16 V₀ S) =
      (tSub16 V₀ S ⊓ conjClosure V H).relIndex (conjClosure V H) :=
    (w16q_relIndex_sup_eq_of_le_normalizer hTN).trans
      (Subgroup.inf_relIndex_right (H := tSub16 V₀ S) (K := conjClosure V H)).symm
  have hodd : ¬ 2 ∣ (tSub16 V₀ S).relIndex (conjClosure V H ⊔ tSub16 V₀ S) := by
    rw [hrel]
    exact hSylTK.not_dvd_relIndex
  have hSylKT : IsSylowIn 2 (tSub16 V₀ S) (conjClosure V H ⊔ tSub16 V₀ S) :=
    ⟨le_sup_right, hT2, hodd⟩
  exact pCoreOf_le_of_isSylowIn hSylKT

theorem qSub16_le_tSub16_of_le (d : DichCfg M V₀ V U S H φ)
    (hTK : S ⊓ conjClosure V H ≤ V ⊔ iSub16 V H) : qSub16 V₀ V S H ≤ tSub16 V₀ S :=
  d.qSub16_le_tSub16_of_inf_le (hTK.trans (sup_le d.cfg.V_le_tSub16 d.cfg.iSub16_le_tSub16))

theorem inf_le_sup_of_card_le (d : DichCfg M V₀ V U S H φ)
    (hX : ∀ P : Subgroup X, IsPGroup 2 P →
      Nat.card P ≤ Nat.card (SevenK.barSub (conjClosure V H) φ V)) :
    S ⊓ conjClosure V H ≤ V ⊔ iSub16 V H := by
  haveI : Finite X := Finite.of_surjective φ d.bar.surjective
  intro x hx
  let P : Subgroup X :=
    ((S ⊓ conjClosure V H).subgroupOf (conjClosure V H)).map φ
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 ↥(S ⊓ conjClosure V H) :=
      d.cfg.cex.sylow.isPGroup.to_le inf_le_left
    have h2 : IsPGroup 2 ↥((S ⊓ conjClosure V H).subgroupOf (conjClosure V H)) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    exact h2.map φ
  have hY_le_P : SevenK.barSub (conjClosure V H) φ V ≤ P := by
    have hVSK : V ≤ S ⊓ conjClosure V H := le_inf d.cfg.cex.V_le_S (le_conjClosure V H)
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono (conjClosure V H) hVSK)
  have hPeq : P = SevenK.barSub (conjClosure V H) φ V :=
    (Subgroup.eq_of_le_of_card_ge hY_le_P (hX P hP2)).symm
  have hxphi : φ ⟨x, hx.2⟩ ∈ SevenK.barSub (conjClosure V H) φ V := by
    rw [← hPeq]
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hx, rfl⟩
  exact d.mem_sup_of_map_mem_barSub hxphi

theorem normalClosure_eq_top (d : DichCfg M V₀ V U S H φ) :
    Subgroup.normalClosure ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ := by
  let K : Subgroup G := conjClosure V H
  let N : Subgroup X :=
    Subgroup.normalClosure ((SevenK.barSub K φ V : Subgroup X) : Set X)
  have hgen : conjClosure V K = K :=
    IsMinFam16.conjClosure_conjClosure_eq d.cfg.one d.cfg.std d.cfg.cex d.cfg.min d.cfg.not_le
  have hVK : V ≤ K := le_conjClosure V H
  have hle : SevenK.barSub K φ K ≤ N := by
    have h := w16q_barSub_conjClosure_le_normalClosure (K := K) (A := V) hVK φ
    rwa [hgen] at h
  have hbarK : SevenK.barSub K φ K = ⊤ := by
    change (K.subgroupOf K).map φ = ⊤
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective φ d.bar.surjective
  rw [hbarK] at hle
  exact top_le_iff.mp hle

theorem exists_psl (d : DichCfg M V₀ V U S H φ)
    (h : CFSG.Quasithin.IsPSL 2 2 (E3.mQuot V (iSub16 V H)) X) :
    ∃ ψ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H))),
      Function.Surjective ψ ∧ ψ.ker = (iSub16 V H).subgroupOf (conjClosure V H) := by
  obtain ⟨e⟩ := w16q_nonempty_psl_equiv_of_isPSL h
  refine ⟨e.toMonoidHom.comp φ, e.surjective.comp d.bar.surjective, ?_⟩
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  change e (φ k) = 1 ↔ (k : G) ∈ iSub16 V H
  rw [e.map_eq_one_iff, d.bar.ker_iff k]

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
