module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDFiveModelA
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w16q_conj_inl {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {G : Subgroup (LGL 2 V)} (x : VG G) (w : V) :
    x * SemidirectProduct.inl (Multiplicative.ofAdd w) * x⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd (projG G x w)) := by
  obtain ⟨v, g, rfl⟩ := exists_eq_inl_mul_inr x
  have hproj : projG G (SemidirectProduct.inl (Multiplicative.ofAdd v) *
      SemidirectProduct.inr g) = (g : LGL 2 V) := by simp
  rw [hproj]
  calc (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g) *
        SemidirectProduct.inl (Multiplicative.ofAdd w) *
        (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g)⁻¹
      = SemidirectProduct.inl (Multiplicative.ofAdd v) *
        (SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd w) *
          (SemidirectProduct.inr g)⁻¹) *
        (SemidirectProduct.inl (Multiplicative.ofAdd v))⁻¹ := by group
    _ = SemidirectProduct.inl (Multiplicative.ofAdd v) *
        SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V) w)) *
        (SemidirectProduct.inl (Multiplicative.ofAdd v))⁻¹ := by
          rw [inr_mul_inl_mul_inr_inv]
    _ = SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V) w)) := by
          have hcomm : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) *
              (SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V) w)) : VG G) =
              (SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V) w)) : VG G) *
              (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) := by
            have h := congrArg (SemidirectProduct.inl : Multiplicative V → VG G)
              (mul_comm (Multiplicative.ofAdd v)
                (Multiplicative.ofAdd ((g : LGL 2 V) w)))
            simpa only [map_mul] using h
          rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem w16q_zpowers_eq_center_of_card_prime {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {z : X} (hz : z ∈ Subgroup.center X) (hz1 : z ≠ 1)
    (hcard : Nat.card (Subgroup.center X) = p) :
    Subgroup.zpowers z = Subgroup.center X := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  have hdvd : orderOf z ∣ p := hcard ▸ Subgroup.orderOf_dvd_natCard _ hz
  have hne : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf z = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne
  rw [hcard, Nat.card_zpowers, hord]

section Certified


theorem w16q_center_le_oddCoreCenter {X : Type} [Group X] [Finite X] {Y : Subgroup X} {p : ℕ}
    (h : Heis2p X Y p) : Subgroup.center X ≤ oddCoreCenter X := by
  intro x hx
  obtain ⟨v, hvY, o, hoO, hvo⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := Y) (t := fusionOddCore X)).mp
      (by rw [h.sup_eq]; exact Subgroup.mem_top x)
  by_cases hxO : x ∈ fusionOddCore X
  · refine Subgroup.mem_map.mpr ⟨⟨x, hxO⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx (m : X))
  · exfalso
    haveI hExt : CFSG.IsExtraspecial p ↥(fusionOddCore X) := h.ext
    have hvO : v ∉ fusionOddCore X := fun hv =>
      hxO (hvo ▸ (fusionOddCore X).mul_mem hv hoO)
    have hv1 : v ≠ 1 := fun h1 => hvO (h1 ▸ (fusionOddCore X).one_mem)
    have hcenter : ∀ n (hn : n ∈ fusionOddCore X),
        (⟨n, hn⟩ : ↥(fusionOddCore X)) ∈ Subgroup.center ↥(fusionOddCore X) := by
      intro n hn
      haveI hQea : IsElementaryAbelian p
          (↥(fusionOddCore X) ⧸ Subgroup.center ↥(fusionOddCore X)) :=
        CFSG.IsExtraspecial.quotient_elementary_abelian p ↥(fusionOddCore X)
      let nO : ↥(fusionOddCore X) := ⟨n, hn⟩
      let oO : ↥(fusionOddCore X) := ⟨o, hoO⟩
      let Q := ↥(fusionOddCore X) ⧸ Subgroup.center ↥(fusionOddCore X)
      have hstep1 : v * (o * n * o⁻¹) * v⁻¹ = n := by
        have hxn : (v * o) * n = n * (v * o) := by
          have h1 := Subgroup.mem_center_iff.mp hx n
          rw [← hvo] at h1
          exact h1.symm
        calc v * (o * n * o⁻¹) * v⁻¹ = ((v * o) * n) * (v * o)⁻¹ := by group
          _ = (n * (v * o)) * (v * o)⁻¹ := by rw [hxn]
          _ = n := by group
      have hcommut : ⁅oO, nO⁆ ∈ Subgroup.center ↥(fusionOddCore X) := by
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' (Subgroup.center ↥(fusionOddCore X))) ⁅oO, nO⁆ = 1
        have hmap := map_commutatorElement
          (f := QuotientGroup.mk' (Subgroup.center ↥(fusionOddCore X))) (g₁ := oO) (g₂ := nO)
        rw [hmap]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (show (oO : Q) * (nO : Q) = (nO : Q) * (oO : Q) from mul_comm' _ _)
      have hmO : n * (o * n * o⁻¹) ∈ fusionOddCore X :=
        (fusionOddCore X).mul_mem hn
          ((fusionOddCore X).mul_mem ((fusionOddCore X).mul_mem hoO hn)
            ((fusionOddCore X).inv_mem hoO))
      have hnm : (⟨n * (o * n * o⁻¹), hmO⟩ : ↥(fusionOddCore X)) ∈
          Subgroup.center ↥(fusionOddCore X) := by
        have hmemb : n * (o * n * o⁻¹) ∈ oddCoreCenter X := by
          have h1 := (h.inv_center hvY hv1).1 (o * n * o⁻¹)
            ((fusionOddCore X).mul_mem ((fusionOddCore X).mul_mem hoO hn)
              ((fusionOddCore X).inv_mem hoO))
          rwa [hstep1] at h1
        obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hmemb
        have hEq : (⟨n * (o * n * o⁻¹), hmO⟩ : ↥(fusionOddCore X)) = c :=
          Subtype.ext hceq.symm
        rw [hEq]; exact hc
      have hsq : nO ^ 2 ∈ Subgroup.center ↥(fusionOddCore X) := by
        have hcO : (oO * nO * oO⁻¹) = ⁅oO, nO⁆ * nO := by
          rw [commutatorElement_def]; group
        have h1 : nO * (⁅oO, nO⁆ * nO) ∈ Subgroup.center ↥(fusionOddCore X) := by
          have h2 : nO * (oO * nO * oO⁻¹) ∈ Subgroup.center ↥(fusionOddCore X) := by
            have h3 := hnm
            rw [show (⟨n * (o * n * o⁻¹), hmO⟩ : ↥(fusionOddCore X)) =
                nO * (oO * nO * oO⁻¹) from by
              apply Subtype.ext
              simp only [nO, oO, Subgroup.coe_mul, Subgroup.coe_inv]] at h3
            exact h3
          rwa [hcO] at h2
        have h2 : ⁅oO, nO⁆⁻¹ * (nO * (⁅oO, nO⁆ * nO)) ∈
            Subgroup.center ↥(fusionOddCore X) :=
          (Subgroup.center ↥(fusionOddCore X)).mul_mem
            ((Subgroup.center ↥(fusionOddCore X)).inv_mem hcommut) h1
        have h3 : ⁅oO, nO⁆⁻¹ * (nO * (⁅oO, nO⁆ * nO)) = nO ^ 2 := by
          have hcomm := Subgroup.mem_center_iff.mp hcommut nO
          have hc' : ⁅oO, nO⁆⁻¹ * nO * ⁅oO, nO⁆ = nO := by
            calc ⁅oO, nO⁆⁻¹ * nO * ⁅oO, nO⁆ =
                ⁅oO, nO⁆⁻¹ * (nO * ⁅oO, nO⁆) := by group
              _ = ⁅oO, nO⁆⁻¹ * (⁅oO, nO⁆ * nO) := by rw [hcomm]
              _ = nO := by group
          calc ⁅oO, nO⁆⁻¹ * (nO * (⁅oO, nO⁆ * nO))
              = (⁅oO, nO⁆⁻¹ * nO * ⁅oO, nO⁆) * nO := by group
            _ = nO * nO := by rw [hc']
            _ = nO ^ 2 := by rw [pow_two]
        rwa [h3] at h2
      have hq2 : ((nO : Q)) ^ 2 = 1 := by
        have hcoe : (nO : Q) = (QuotientGroup.mk'
            (Subgroup.center ↥(fusionOddCore X))) nO := rfl
        rw [hcoe, ← map_pow, QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr hsq
      have hqp : ((nO : Q)) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p
            (↥(fusionOddCore X) ⧸ Subgroup.center ↥(fusionOddCore X))) (nO : Q)
      have hpodd : Odd p := h.prime.odd_of_ne_two h.ne_two
      have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
      have hdvd : orderOf ((nO : Q)) ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hq2)
          (orderOf_dvd_iff_pow_eq_one.mpr hqp)
      rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
      have hq1 : (nO : Q) = 1 := orderOf_eq_one_iff.mp hdvd
      rw [← QuotientGroup.eq_one_iff]
      exact hq1
    have hcenter_top : Subgroup.center ↥(fusionOddCore X) = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨n, hn⟩ -
      exact hcenter n hn
    have hcard : Nat.card ↥(Subgroup.center ↥(fusionOddCore X)) =
        Nat.card ↥(fusionOddCore X) := by rw [hcenter_top, Subgroup.card_top]
    have hp_eq : p = p ^ 3 := by
      have h1 : Nat.card ↥(Subgroup.center ↥(fusionOddCore X)) = p :=
        CFSG.IsExtraspecial.center_order_p p ↥(fusionOddCore X)
      exact h1.symm.trans (hcard.trans h.card_O)
    have hp2sq : 1 < p ^ 2 := by nlinarith [h.prime.two_le]
    have hmul : p * 1 < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hp2sq h.prime.pos
    rw [mul_one] at hmul
    have hpow : p * p ^ 2 = p ^ 3 := by ring
    rw [hpow] at hmul
    omega

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem w16q_fixedPointFree [Finite X] (d : DichCfg M V₀ V U S H φ)
    (D : ModDataE H (iSub16 V H)) {p : ℕ}
    (h : Heis2p X (SevenK.barSub (conjClosure V H) φ V) p)
    (hfaith : conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ iSub16 V H)
    {k : ℕ}
    (hk : Nat.card ↥(iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) = 2 ^ (p * k))
    (hcomm : ⁅iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)),
        centerMod (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))
          (iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
            (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))⁆ =
        iSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) :
    ∀ z : ↥(conjClosure V H), φ z ∈ oddCoreCenter X → φ z ≠ 1 →
      conjClosure V₀ H ⊓ centralizer ({(z : G)} : Set G) = ⊥ := by
  intro z hzZ hz1
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hExt : CFSG.IsExtraspecial p ↥(fusionOddCore X) := h.ext
  let K : Subgroup G := conjClosure V H
  let G' : Subgroup (LGL 2 D.W) := D.img H
  let A0 : Subgroup (LGL 2 D.W) := D.img V
  let VA : Subgroup (LGL 2 D.W) → Submodule (ZMod 2) D.W := D.conjImgSpace V₀ V
  let V' : Subgroup (VG G') := UAOf G' VA A0
  let E' : Subgroup (VG G') := vHat G'
  let K' : Subgroup (VG G') := kSub V' ⊤ E'
  let I' : Subgroup (VG G') := iSub V' ⊤ E'
  have hHyp : SevenK.Hyp716 V' ⊤ E' :=
    IsMinFam16.hyp716_UAOf_img d.cfg.one d.cfg.five d.cfg.std d.cfg.cex d.cfg.min d.cfg.not_le D
  haveI hI'norm : I'.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (H := I') (K := ⊤) le_top).mp
        hHyp.jnormal))
  obtain ⟨ψ, hψbar, hψproj⟩ :=
    IsMinFam16.exists_isBarMap_kSub_UAOf_img d.cfg.one d.cfg.five d.cfg.std d.cfg.cex
      d.cfg.min d.cfg.not_le D
  obtain ⟨θ, hθ⟩ := w16q_exists_theta d D hfaith
  let rz : ↥(D.img K) := θ (φ z)
  have hφz_center : φ z ∈ Subgroup.center X := w16q_oddCoreCenter_le_center h hzZ
  have hmapcenter : (Subgroup.center X).map θ.toMonoidHom = Subgroup.center ↥(D.img K) :=
    Subgroup.map_center_eq θ
  have hrz_center : rz ∈ Subgroup.center ↥(D.img K) := by
    rw [← hmapcenter]
    exact Subgroup.mem_map.mpr ⟨φ z, hφz_center, rfl⟩
  have hrz_ne : rz ≠ 1 := by
    intro h1
    apply hz1
    apply θ.injective
    rw [show θ (φ z) = rz from rfl, h1, map_one]
  have hcenterX : Subgroup.center X = oddCoreCenter X :=
    le_antisymm (w16q_center_le_oddCoreCenter h) (w16q_oddCoreCenter_le_center h)
  have hcardOX : Nat.card (oddCoreCenter X) = p := by
    rw [oddCoreCenter]
    rw [Subgroup.card_map_of_injective (fusionOddCore X).subtype_injective]
    exact CFSG.IsExtraspecial.center_order_p p ↥(fusionOddCore X)
  have hcardZ : Nat.card (Subgroup.center X) = p := by rw [hcenterX]; exact hcardOX
  have hcardZ' : Nat.card (Subgroup.center ↥(D.img K)) = p := by
    rw [← hmapcenter, Subgroup.card_map_of_injective θ.injective, hcardZ]
  have hZeq : Subgroup.zpowers rz = Subgroup.center ↥(D.img K) :=
    w16q_zpowers_eq_center_of_card_prime h.prime hrz_center hrz_ne hcardZ'
  obtain ⟨k', hk'⟩ := hψbar.surjective rz
  have hk'mem : (k' : VG G') ∈ centerMod K' I' := by
    rw [mem_centerMod_iff]
    refine ⟨k'.2, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr hI'norm]; exact Subgroup.mem_top _
    intro m hm
    have hmem : ⁅(k' : VG G'), m⁆ ∈ K' := by
      rw [commutatorElement_def]
      exact K'.mul_mem (K'.mul_mem (K'.mul_mem k'.2 hm) (K'.inv_mem k'.2)) (K'.inv_mem hm)
    have hcoe : ((⁅(⟨(k' : VG G'), k'.2⟩ : ↥K'), ⟨m, hm⟩⁆ : ↥K') : VG G') =
        ⁅(k' : VG G'), m⁆ :=
      map_commutatorElement (f := Subgroup.subtype K')
        (g₁ := (⟨(k' : VG G'), k'.2⟩ : ↥K')) (g₂ := ⟨m, hm⟩)
    rw [← hcoe]
    exact (hψbar.ker_iff ⁅(⟨(k' : VG G'), k'.2⟩ : ↥K'), ⟨m, hm⟩⁆).mp (by
      rw [map_commutatorElement, hk']
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hrz_center (ψ ⟨m, hm⟩)).symm)
  have hI'eqw : I' = wHat G' (D.sp (conjClosure V₀ H)) := w16q_iSub_UAOf_eq d D
  have hI'ab : IsMulCommutative ↥I' := by
    rw [hI'eqw]
    exact (isElemAbelian_wHat (G := G') (D.sp (conjClosure V₀ H))).1
  have hcenterMod_le : centerMod K' I' ≤ Subgroup.zpowers (k' : VG G') ⊔ I' := by
    intro m hm
    obtain ⟨hmK, -, hmcomm⟩ := mem_centerMod_iff.mp hm
    let mK : ↥K' := ⟨m, hmK⟩
    have hcentral : ψ mK ∈ Subgroup.center ↥(D.img K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨kk, rfl⟩ := hψbar.surjective g
      have hmem : ⁅m, (kk : VG G')⁆ ∈ I' := hmcomm (kk : VG G') kk.2
      have hcoe : ((⁅mK, kk⁆ : ↥K') : VG G') = ⁅m, (kk : VG G')⁆ :=
        map_commutatorElement (f := Subgroup.subtype K') (g₁ := mK) (g₂ := kk)
      have h1 : ψ ⁅mK, kk⁆ = 1 := (hψbar.ker_iff ⁅mK, kk⁆).mpr (by rw [hcoe]; exact hmem)
      rw [map_commutatorElement] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hzp : ψ mK ∈ Subgroup.zpowers rz := by rw [hZeq]; exact hcentral
    rw [Subgroup.mem_zpowers_iff] at hzp
    obtain ⟨n, hn⟩ := hzp
    have hmemI : m * ((k' : VG G') ^ n)⁻¹ ∈ I' := by
      have hcoe2 : ((mK * (k' ^ n)⁻¹ : ↥K') : VG G') = m * ((k' : VG G') ^ n)⁻¹ := rfl
      rw [← hcoe2]
      exact (hψbar.ker_iff (mK * (k' ^ n)⁻¹)).mp (by
        rw [map_mul, map_inv, map_zpow, hk']
        rw [← hn, mul_inv_cancel])
    rw [sup_comm]
    convert Subgroup.mul_mem_sup (S := I')
      (T := Subgroup.zpowers (k' : VG G')) hmemI
      (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩) using 1
    group
  have hI'eq : ⁅I', Subgroup.zpowers (k' : VG G')⁆ = I' := by
    apply le_antisymm
    · calc ⁅I', Subgroup.zpowers (k' : VG G')⁆ ≤ ⁅I', centerMod K' I'⁆ :=
            Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hk'mem)
        _ = I' := hcomm
    · calc I' = ⁅I', centerMod K' I'⁆ := hcomm.symm
        _ ≤ ⁅I', Subgroup.zpowers (k' : VG G') ⊔ I'⁆ :=
            Subgroup.commutator_mono le_rfl hcenterMod_le
        _ = ⁅I', Subgroup.zpowers (k' : VG G')⁆ ⊔ ⁅I', I'⁆ :=
            Subgroup.commutator_sup_left I' (Subgroup.zpowers (k' : VG G')) I'
        _ = ⁅I', Subgroup.zpowers (k' : VG G')⁆ ⊔ ⊥ := by
            rw [Subgroup.commutator_self_eq_bot_iff.mpr hI'ab]
        _ = ⁅I', Subgroup.zpowers (k' : VG G')⁆ := by rw [sup_bot_eq]
  have hDQ : Subgroup.zpowers (k' : VG G') ≤ Subgroup.normalizer (I' : Set (VG G')) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hI'norm]
    exact le_top
  have hfp' : ∀ y ∈ I', (k' : VG G') * y = y * (k' : VG G') → y = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.fixedPointFree_of_commutator_eq_uc6
      (x := (k' : VG G')) (D := Subgroup.zpowers (k' : VG G')) (Q := I') rfl hI'ab hDQ
      (by rw [Subgroup.commutator_comm]; exact hI'eq)
  rw [Subgroup.eq_bot_iff_forall]
  intro e he
  obtain ⟨heI₀, heC⟩ := Subgroup.mem_inf.mp he
  have hez : (z : G) * e * (z : G)⁻¹ = e := by
    have hze : (z : G) * e = e * (z : G) :=
      Subgroup.mem_centralizer_iff.mp heC (z : G) (by simp)
    rw [hze]; group
  have hV0I : V₀ ≤ iSub16 V H := le_sup_right.trans d.cfg.le_iSub16
  have hHnormI : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hI0I : conjClosure V₀ H ≤ iSub16 V H :=
    conjClosure_le fun h hh y hy =>
      (Subgroup.mem_normalizer_iff.mp (hHnormI hh) y).1 (hV0I hy)
  have heI : e ∈ iSub16 V H := hI0I heI₀
  have hw : D.ι e ∈ D.sp (conjClosure V₀ H) := D.mem_sp.mpr ⟨e, ⟨heI₀, heI⟩, rfl⟩
  have hi_mem : SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) ∈ I' := by
    rw [hI'eqw]
    exact mem_wHat.mpr ⟨D.ι e, hw, rfl⟩
  have hproj_eq : projG G' (k' : VG G') =
      D.ρ (Subgroup.inclusion d.cfg.conjClosure_le_H z) := by
    rw [← hψproj k']
    show ((ψ k' : ↥(D.img K)) : LGL 2 D.W) =
      D.ρ (Subgroup.inclusion d.cfg.conjClosure_le_H z)
    rw [hk']
    exact congrArg Subtype.val (hθ z)
  have hrzw : projG G' (k' : VG G') (D.ι e) = D.ι e := by
    rw [hproj_eq]
    have h1 := D.ρ_ι (Subgroup.inclusion d.cfg.conjClosure_le_H z) e heI
    have hcoe : ((Subgroup.inclusion d.cfg.conjClosure_le_H z : ↥H) : G) = z :=
      Subgroup.coe_inclusion _ _
    rw [hcoe, hez] at h1
    exact h1
  have hconj_i : (k' : VG G') * SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) *
      (k' : VG G')⁻¹ = SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) := by
    rw [w16q_conj_inl]
    rw [hrzw]
  have hcomm_i : (k' : VG G') * SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) =
      SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) * (k' : VG G') := by
    calc (k' : VG G') * SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) =
        ((k' : VG G') * SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) *
          (k' : VG G')⁻¹) * (k' : VG G') := by group
      _ = SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) * (k' : VG G') := by
          rw [hconj_i]
  have hi1 := hfp' _ hi_mem hcomm_i
  have hw0 : D.ι e = 0 := by
    have h2 : Multiplicative.ofAdd (D.ι e) = 1 := by
      have h3 : (SemidirectProduct.inl (Multiplicative.ofAdd (D.ι e)) : VG G') =
          (SemidirectProduct.inl (1 : Multiplicative D.W) : VG G') := by simpa using hi1
      exact SemidirectProduct.inl_injective h3
    exact ofAdd_eq_one.mp h2
  exact D.ι_eq_zero e heI hw0

end DichCfg

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
