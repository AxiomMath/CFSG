module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSU
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSp
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic
public import CFSG.LieType.HighestRoot.CentIsogenyE6E7

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.RCKSmall (RCKSmallTag RCKSmallLabel RCKSmallEmpty)

private theorem rckGH_eq_one_of_mem_center_of_two_pow {K : Type} [Group K]
    (hZ : Odd (Nat.card (Subgroup.center K))) {c : K} (hc : c ∈ Subgroup.center K)
    {m : ℕ} (hm : c ^ 2 ^ m = 1) : c = 1 := by
  have hdvd2 : orderOf c ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.2 hm
  have hdvdZ : orderOf c ∣ Nat.card (Subgroup.center K) := Subgroup.orderOf_dvd_natCard _ hc
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) (2 ^ m) :=
    hZ.coprime_two_right.pow_right m
  have hdvd1 : orderOf c ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hdvdZ hdvd2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

private theorem rckGH_orderOf_eq_two_pow_of_isPGroup {X : Type} [Group X] {H : Subgroup X}
    (hH : IsPGroup 2 H) (x : ↥H) : ∃ k, orderOf (x : X) = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hH) x
  exact ⟨k, by rw [Subgroup.orderOf_coe x]; exact hk⟩

private theorem rckGH_pCoreOf_le {X : Type} [Group X] (p : ℕ) (H : Subgroup X) :
    pCoreOf p H ≤ H := by
  unfold pCoreOf
  exact Subgroup.map_subtype_le _

private theorem rckGH_isPGroup_pCoreOf {X : Type} [Group X] (p : ℕ) (H : Subgroup X) :
    IsPGroup p (pCoreOf p H) := by
  unfold pCoreOf
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

private theorem rckGH_pCoreOf_le_normalizer {X : Type} [Group X] (p : ℕ) (H : Subgroup X) :
    H ≤ Subgroup.normalizer (pCoreOf p H : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc y hy
  unfold pCoreOf at hy ⊢
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨w, hw, rfl⟩ := hy
  exact Subgroup.mem_map.mpr
    ⟨⟨c, hc⟩ * w * ⟨c, hc⟩⁻¹, (inferInstance : (pCore p ↥H).Normal).conj_mem w hw ⟨c, hc⟩,
      by simp⟩

private theorem rckGH_rootPairVia_map {M : LieUniversal} {X : Type} [Group X]
    {J : Subgroup X} {R Rm : Subgroup ↥J} {β : Fin M.D.rank → ℤ}
    (h : GGRootPairVia M (⊤ : Subgroup ↥J) R Rm β) :
    GGRootPairVia M J (R.map J.subtype) (Rm.map J.subtype) β := by
  unfold GGRootPairVia at h ⊢
  obtain ⟨φ, hφrange, hφker, u, hR, hRm⟩ := h
  refine ⟨J.subtype.comp φ, ?_, ?_, u, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hφrange, Subgroup.map_top, Subgroup.range_subtype]
  · exact (MonoidHom.ker_comp_of_injective φ J.subtype Subtype.val_injective).trans_le hφker
  · rw [hR]
    simp only [ggRootSub, Subgroup.map_map, MonoidHom.comp_assoc]
  · rw [hRm]
    simp only [ggRootSub, Subgroup.map_map, MonoidHom.comp_assoc]

theorem rck_K2_self {X : Type} [Group X] [Finite X] {J V : Subgroup X} {r : X}
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) (hrV : r ∈ V) (hVJ : V ≤ J)
    (hV : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hK1 : ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
      Y ≤ Subgroup.centralizer {r} →
      (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
      ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
        v * y * v⁻¹ * y⁻¹ = r ^ k * z) :
    pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := J ⊓ Subgroup.centralizer ({r} : Set X) with hHdef
  set Y : Subgroup X := pCoreOf 2 H with hYdef
  have hYleH : Y ≤ H := rckGH_pCoreOf_le 2 H
  have hYJ : Y ≤ J := hYleH.trans inf_le_left
  have hYC : Y ≤ Subgroup.centralizer ({r} : Set X) := hYleH.trans inf_le_right
  have hVH : V ≤ H := by
    refine le_inf hVJ ?_
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext_iff.mp (hV.1.is_comm.comm ⟨v, hv⟩ ⟨r, hrV⟩))
  have hNY : H ≤ Subgroup.normalizer (Y : Set X) := rckGH_pCoreOf_le_normalizer 2 H
  rw [Subgroup.le_normalizer_iff]
  intro y hy v hv
  obtain ⟨k, z, hzC, heq⟩ := hK1 Y (rckGH_isPGroup_pCoreOf 2 H)
    (hYJ.trans Subgroup.le_normalizer) hYC
    (fun c hcJ hcr => hNY (Subgroup.mem_inf.mpr
      ⟨hcJ, Subgroup.mem_centralizer_singleton_iff.mpr hcr⟩)) v hv y hy
  set c : X := r ^ k * z with hcdef
  have hvH : v ∈ H := hVH hv
  have hconj : v * y * v⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hNY hvH) y).mp hy
  have hcY : c ∈ Y := by
    rw [← heq]
    exact Y.mul_mem hconj (Y.inv_mem hy)
  have hcYJ : c ∈ J := hYJ hcY
  have hrkJ : r ^ k ∈ J := J.zpow_mem (hVJ hrV) k
  have hzJ : z ∈ J := by
    have hzc : z = (r ^ k)⁻¹ * c := by rw [hcdef]; group
    rw [hzc]
    exact J.mul_mem (J.inv_mem hrkJ) hcYJ
  have hzcenter : (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hzC (g : X) g.2
  obtain ⟨m, hm⟩ := rckGH_orderOf_eq_two_pow_of_isPGroup (rckGH_isPGroup_pCoreOf 2 H) ⟨c, hcY⟩
  have hcn : c ^ 2 ^ (max m 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hm]; exact pow_dvd_pow 2 (le_max_left m 1))
  have hrkn : (r ^ k) ^ 2 ^ (max m 1) = 1 := by
    have h2 : (r ^ k) ^ 2 = 1 := hV.2 (r ^ k) (V.zpow_mem hrV k)
    have hdvd : orderOf (r ^ k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    exact orderOf_dvd_iff_pow_eq_one.mp
      (hdvd.trans (dvd_pow_self 2 (by omega)))
  have hcz : Commute (r ^ k) z := hzC (r ^ k) hrkJ
  have hzc : z = (r ^ k)⁻¹ * c := by rw [hcdef]; group
  have hczc : Commute (r ^ k) c := by
    rw [hcdef]
    exact (Commute.refl (r ^ k)).mul_right hcz
  have hzn : z ^ 2 ^ (max m 1) = 1 := by
    rw [hzc, (hczc.inv_left).mul_pow, inv_pow, hrkn, inv_one, hcn, mul_one]
  have hz1 : z = 1 := by
    have hzn' : (⟨z, hzJ⟩ : ↥J) ^ 2 ^ (max m 1) = 1 := by
      apply Subtype.ext
      simpa using hzn
    exact congrArg Subtype.val
      (rckGH_eq_one_of_mem_center_of_two_pow hZ hzcenter hzn')
  have hyv : y * v * y⁻¹ = (r ^ k)⁻¹ * v := by
    have h1 : y * v * y⁻¹ = c⁻¹ * v := by
      rw [← heq]
      group
    rw [h1, hcdef, hz1, mul_one]
  rw [hyv]
  exact V.mul_mem (V.inv_mem (V.zpow_mem hrV k)) hv

private theorem rckGH_false_of_mem_roots_trivialUniversal (L : LieUniversal) (hL : L = trivialUniversal)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) : False := by
  subst hL
  rcases hβ with ⟨w, i, -⟩ | ⟨w, i, -, -⟩ <;> exact i.elim0

private theorem rckGH_GGLongRoot_mem_roots {U : Type} [Group U] {D : UniversalRootDatum U}
    {γ : Fin D.rank → ℤ} (h : GGLongRoot D γ) : γ ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private theorem rckGH_isPGroup_E8
    (K : Type) [Field K] [CharP K 2]
    {γ : Fin (CFSG.LieType.Steinberg.Adjoint.e8Datum K).rank → ℤ}
    (hγ : γ ∈ (CFSG.LieType.Steinberg.Adjoint.e8Datum K).roots) :
    IsPGroup 2 ((CFSG.LieType.Steinberg.Adjoint.e8Datum K).rootGroup γ) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  obtain ⟨c, hc⟩ :=
    (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
      (CFSG.LieType.Steinberg.Adjoint.mem_adjDatum_roots.1 hγ)
      (g : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 K))).1 g.2
  simp only [SubmonoidClass.coe_pow, Subgroup.coe_one]
  rw [← hc, pow_two, ← CFSG.LieType.Steinberg.Adjoint.xPar_add, CharTwo.add_self_eq_zero,
    CFSG.LieType.Steinberg.Adjoint.xPar_zero]

theorem rckGH_ggU_ggRootSub_isPGroup
    (t : StatedLieTag) (m g : ℕ) (ht : GGPosTag t)
    (hg : 1 ≤ g) :
    ∀ (β : Fin (ggU t m g).D.rank → ℤ), β ∈ (ggU t m g).D.roots →
      ∀ u : (ggU t m g).K,
        IsPGroup 2 (ggRootSub (ggU t m g).D (MonoidHom.id (ggU t m g).K) β u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (GaloisField 2 g) 2 := inferInstance
  unfold GGPosTag at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    cases m with
    | zero =>
      intro β hβ u
      exact (rckGH_false_of_mem_roots_trivialUniversal _ rfl hβ).elim
    | succ m' =>
      intro β hβ u
      exact CFSG.StandardType.LieKnownR2.PSL.rootGroup_isPGroup_PSL hβ u rfl
  ·
    intro β hβ u
    exact CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSU hβ u rfl
  ·
    intro β hβ u
    exact CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSp hβ u rfl
  ·
    by_cases hm : 3 ≤ m
    · have e : ggU .POmegaPlus m g =
          ⟨↥(spinGroup (Spin.quadPlus m (GaloisField 2 g))),
            Spin.plusDatum m (GaloisField 2 g) hm⟩ := by
        simp only [ggU, lieUniversal, dif_pos hm]
      rw [e]
      intro β hβ u
      have hpar := CFSG.LieType.Steinberg.SpinPlus.isParametrization
        (K := GaloisField 2 g) hm
      have hβ' : β ∈ (CFSG.LieType.Steinberg.SpinPlus.Φ m (GaloisField 2 g) hm).roots := by
        change β ∈ (Spin.plusDatum m (GaloisField 2 g) hm).roots
        exact hβ
      have h : IsPGroup 2 ((Spin.plusDatum m (GaloisField 2 g) hm).rootGroup β) :=
        CFSG.LieType.Steinberg.isPGroup_of_isParametrization hpar hβ'
      exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)
    · have e : ggU .POmegaPlus m g = trivialUniversal := by
        simp only [ggU, lieUniversal, dif_neg hm]
      intro β hβ u
      exact (rckGH_false_of_mem_roots_trivialUniversal _ e hβ).elim
  ·
    intro β hβ u
    have h : IsPGroup 2
        ((Spin.Twisted.minusDatum m (CFSG.LieType.Universal.minusCoeffs_irr 2 g)).rootGroup β) :=
      CFSG.LieType.Steinberg.isPGroup_minusRootGroup
        (CFSG.LieType.Universal.minusCoeffs_irr 2 g) hβ
    exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)
  ·
    intro β hβ u
    exact CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_F4 hβ u rfl
  ·
    intro β hβ u
    have h : IsPGroup 2 ((CFSG.LieType.Steinberg.Minuscule.e6Datum (GaloisField 2 g)).rootGroup β) :=
      CFSG.LieType.HighestRoot.isPGroup_minRootGroup
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid (GaloisField 2 g) β
    exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)
  ·
    intro β hβ u
    have h : IsPGroup 2 ((CFSG.LieType.Steinberg.Minuscule.e7Datum (GaloisField 2 g)).rootGroup β) :=
      CFSG.LieType.HighestRoot.isPGroup_minRootGroup
        CFSG.LieType.Steinberg.Minuscule.e7Data_valid (GaloisField 2 g) β
    exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)
  ·
    intro β hβ u
    have h : IsPGroup 2 ((CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 g)).rootGroup β) :=
      rckGH_isPGroup_E8 (GaloisField 2 g) hβ
    exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)
  ·
    intro β hβ u
    exact CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_twistedE6 hβ u rfl

theorem rckGH_triD4_rootGroup_isPGroup
    (F : Type) [Field F] [Finite F] (σ : F →+* F)
    (g : ℕ) (htri : TriField F σ g) {β : Fin (triD4Universal F σ).D.rank → ℤ}
    (hβ : β ∈ (triD4Universal F σ).D.roots) :
    IsPGroup 2 ((triD4Universal F σ).D.rootGroup β) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ (3 * g) := by
    rw [← Nat.card_eq_fintype_card, htri.2.1, ← pow_mul, mul_comm g 3]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3 * g) hcard
  have hσ := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ) (q := 2 ^ g)
    htri.2.1 htri.2.2
  exact CFSG.LieType.HighestRoot.isPGroup_twistedD4_rootGroup σ hσ
    (CFSG.LieType.Steinberg.TwistedD4.isRoot_of_mem_twistedDatum_roots σ hβ)

theorem rck_rootPosJ_isPGroup
    {X : Type} [Group X] {J R Rm : Subgroup X} (h : GGRootPosJ J R Rm) : IsPGroup 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold GGRootPosJ at h
  rcases h with ⟨t', m, g, β, ht, hg, hlong, hpair⟩ |
    ⟨F, hF, hFin, σ, g, β, htri, hlong, hpair⟩
  · unfold GGRootPairVia at hpair
    obtain ⟨φ, -, -, u, hR, -⟩ := hpair
    have hP := rckGH_ggU_ggRootSub_isPGroup t' m g ht hg β
      (rckGH_GGLongRoot_mem_roots hlong) u
    have hmap : ggRootSub (ggU t' m g).D φ β u =
        (ggRootSub (ggU t' m g).D (MonoidHom.id (ggU t' m g).K) β u).map φ := by
      simp only [ggRootSub]
      rw [Subgroup.map_id]
    rw [hR, hmap]
    exact hP.map φ
  · unfold GGRootPairVia at hpair
    obtain ⟨φ, -, -, u, hR, -⟩ := hpair
    letI : Field F := hF
    letI : Finite F := hFin
    have hP := rckGH_triD4_rootGroup_isPGroup F σ g htri
      (rckGH_GGLongRoot_mem_roots hlong)
    rw [hR]
    exact (hP.map (MulAut.conj u).toMonoidHom).map φ

theorem rck_rootPosJ_subtype
    {X : Type} [Group X] {J : Subgroup X} {R Rm : Subgroup ↥J}
    (h : GGRootPosJ (⊤ : Subgroup ↥J) R Rm) :
    GGRootPosJ J (R.map J.subtype) (Rm.map J.subtype) := by
  unfold GGRootPosJ at h ⊢
  rcases h with ⟨t', m, g, β, htag, hg, hlong, hpair⟩ |
    ⟨F, hF, hFin, σ, g, β, htri, hlong, hpair⟩
  · exact Or.inl ⟨t', m, g, β, htag, hg, hlong, rckGH_rootPairVia_map hpair⟩
  · exact Or.inr ⟨F, hF, hFin, σ, g, β, htri, hlong, rckGH_rootPairVia_map hpair⟩

theorem rck_V_le_R_of_image {X : Type} [Group X] [Finite X] {J V : Subgroup X}
    {R : Subgroup ↥J} (hZ : Odd (Nat.card (Subgroup.center ↥J))) (hR : IsPGroup 2 R)
    (hV : IsPGroup 2 V) (hVJ : V ≤ J)
    (himg : (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) ≤
      R.map (QuotientGroup.mk' (Subgroup.center ↥J))) :
    V ≤ R.map J.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVsub : IsPGroup 2 (V.subgroupOf J) :=
    IsPGroup.comap_of_injective hV J.subtype Subtype.val_injective
  have hle : V.subgroupOf J ≤ R := by
    intro x hx
    have hmem : QuotientGroup.mk' (Subgroup.center ↥J) x ∈
        R.map (QuotientGroup.mk' (Subgroup.center ↥J)) :=
      himg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    rw [Subgroup.mem_map] at hmem
    obtain ⟨r, hrR, hrx⟩ := hmem
    obtain ⟨a, ha⟩ := rckGH_orderOf_eq_two_pow_of_isPGroup hVsub ⟨x, hx⟩
    obtain ⟨b, hb⟩ := rckGH_orderOf_eq_two_pow_of_isPGroup hR ⟨r, hrR⟩
    set w : ↥J := x * r⁻¹ with hwdef
    have hwcenter : w ∈ Subgroup.center ↥J := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥J)]
      show QuotientGroup.mk' (Subgroup.center ↥J) w = 1
      rw [hwdef, map_mul, map_inv, ← hrx, mul_inv_cancel]
    have hxpow : x ^ 2 ^ max a b = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact pow_dvd_pow 2 (le_max_left a b))
    have hrpow : r ^ 2 ^ max a b = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hb]; exact pow_dvd_pow 2 (le_max_right a b))
    have hwr : w * r = x := by rw [hwdef, mul_assoc, inv_mul_cancel, mul_one]
    have hcomm : Commute w r := (Subgroup.mem_center_iff.mp hwcenter r).symm
    have hwpow : w ^ 2 ^ max a b = 1 := by
      have h := hcomm.mul_pow (2 ^ max a b)
      rw [hwr, hxpow, hrpow, mul_one] at h
      exact h.symm
    have hw1 : w = 1 := rckGH_eq_one_of_mem_center_of_two_pow hZ hwcenter hwpow
    have hxr : x = r := by
      rw [hwdef] at hw1
      exact mul_inv_eq_one.mp hw1
    rw [hxr]
    exact hrR
  intro x hx
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hVJ hx⟩,
      hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem rck_r_mem_R {X : Type} [Group X] [Finite X] {J : Subgroup X} {R : Subgroup ↥J} {r : ↥J}
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) (hR : IsPGroup 2 R) (hr : r ^ 2 = 1)
    (himg : QuotientGroup.mk' (Subgroup.center ↥J) r ∈
      R.map (QuotientGroup.mk' (Subgroup.center ↥J))) :
    r ∈ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.mem_map] at himg
  obtain ⟨s, hsR, hsr⟩ := himg
  set w : ↥J := r * s⁻¹ with hwdef
  have hwcenter : w ∈ Subgroup.center ↥J := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥J)]
    show QuotientGroup.mk' (Subgroup.center ↥J) w = 1
    rw [hwdef, map_mul, map_inv, hsr, mul_inv_cancel]
  obtain ⟨b, hb⟩ := rckGH_orderOf_eq_two_pow_of_isPGroup hR ⟨s, hsR⟩
  have hrs : r = w * s := by rw [hwdef, mul_assoc, inv_mul_cancel, mul_one]
  have hcomm : Commute r s := by
    rw [hrs]
    exact Commute.mul_left (Subgroup.mem_center_iff.mp hwcenter s).symm (Commute.refl s)
  have hrpow : r ^ 2 ^ (b + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr hr).trans (dvd_pow_self 2 (Nat.succ_ne_zero b)))
  have hs1 : s ^ 2 ^ b = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hb])
  have hspow : s ^ 2 ^ (b + 1) = 1 := by
    rw [pow_succ, pow_mul, hs1, one_pow]
  have hwpow : w ^ 2 ^ (b + 1) = 1 := by
    rw [hwdef, (hcomm.inv_right).mul_pow, hrpow, inv_pow, hspow, inv_one, mul_one]
  have hw1 : w = 1 := rckGH_eq_one_of_mem_center_of_two_pow hZ hwcenter hwpow
  have hrs_eq : r = s := by
    rw [hwdef] at hw1
    exact mul_inv_eq_one.mp hw1
  rw [hrs_eq]
  exact hsR

end CFSG.StandardType.RCKC1




