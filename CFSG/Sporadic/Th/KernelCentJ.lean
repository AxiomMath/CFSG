
module

public import CFSG.Sporadic.Th.KernelCentJBase

public import CFSG.Sporadic.Th.KernelCent
public import CFSG.Sporadic.Th.KernelOrder
public import CFSG.Certificates.Kernel.ThCent.WitSound
public import CFSG.Certificates.Kernel.Th.Spec.FwdExt
public import CFSG.Certificates.Kernel.Th.SoundnessGen
import CFSG.Certificates.Kernel.Th.Spec.Dce
import CFSG.Certificates.Kernel.Th.Spec.DceHsw

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec.DceStr
  CFSG.KC.Th.Spec.Dce CFSG.KC.Th.Gen CFSG.KC.Th.Spec TauCeti Pointwise


local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))


theorem K_eq : K = Subgroup.closure (gen '' {g | g < 7}) := by
  unfold K
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

set_option maxHeartbeats 1000000 in
theorem class_P [Finite P] (hP : Nat.card P = thOrder) (hK : Nat.card K ≤ 634023936)
    (D : DceStructData) (hD : dceStructChk D = true)
    {SV PI QI CJ R H1 : ℕ → ℕ} {B : ℕ} {w FL CS CM : List ℕ} {o r i1 j1 Hi N1 m1 : ℕ}
    (hsh : sharedOK D.ThB_LT B D.ThA_CB CJ D.ThB_om = true) (hNB : D.ThB_NB = 1)
    (hNO : D.ThB_NO ≤ 2048 * 9) (hnT : D.ThB_nT ≤ 2048 * 18)
    (hsv : ∀ i < 9, svChunk SV PI D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NO i = true)
    (hpt : ∀ i < 9, ptChunk SV QI D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NO i = true)
    (hmisc : classMisc D.ThB_LT D.ThA_CB D.ThB_HB D.ThB_GB D.ThB_OB SV D.ThB_osh D.ThB_owd
      D.ThB_om D.ThB_NO w FL CS CM o r i1 j1 Hi N1 m1 = true)
    (hdiff : ∀ i < 9, diffChunk SV R H1 D.ThB_NO B (psOf (wordM D.ThB_LT w) (o - 1))
      (FL.map (DceS.mat D.ThA_CB)) i1 i = true)
    (hsel : ∀ i < 9, selChunk R D.ThB_NO CS i = true)
    (hcomm : ∀ i < 18, commChunk D.ThB_HB D.ThB_TB
      (mul24 (mul24 (gmN D.ThB_HB D.ThB_GB j1) (wordM D.ThB_LT w)) Hi) D.ThB_nT CM i = true)
    (n : Fin 11 → ℕ) (hn : ∀ D' : Fin 11, D' ≠ 0 → ((Finset.range (mD D')).filter fun j =>
      ordRank o r (DceS.mat (tabB D (cosetOrder D')) j) = true).card ≤ n D') :
    ∃ ht : wval gen w ∈ K, wval gen w ^ o = 1 ∧ (wval gen w = 1 → r = 0) ∧
      Nat.card (Subgroup.centralizer ({(⟨wval gen w, ht⟩ : K)} : Set K)) ≤ N1 * m1 ∧
      (∀ g ∈ K, ∀ w' : List ℕ, (∀ c ∈ w', c < 14) →
        g * wval gen w * g⁻¹ = wval gen w' → ordRank o r (wordM D.ThB_LT w') = true) ∧
      Nat.card {p : Om // (wval gen w : P) • p = p} ≤ ∑ D', fixB (N1 * m1) n D' := by
  obtain ⟨h1, h2, h3⟩ := hsw_th
  have hrel := hsw_rel_of_pres _ h1 h2 h3
  have hgen := presGen_closure _ h1
  have hG : Nat.card P = 90745943887872000 := hP
  have key := class_bound gen hrel hgen D hD hG hsh hNB hNO hnT hsv hpt hmisc hdiff hsel hcomm
  rw [← K_eq] at key
  obtain ⟨ht, hpow, h1', hc, hinv, v, hv0, hcov, hstab, hcnt⟩ := key
  refine ⟨ht, hpow, h1', hc, hinv, ?_⟩
  refine card_fix_le_of hP hv0 hcov (fun D' => ?_) hK ⟨wval gen w, ht⟩ hc n fun D' hD0 => ?_
  · by_cases hD0 : D' = 0
    · subst hD0
      have : (1 : ℕ) ≤ Nat.card (stabK (v 0)) := Nat.card_pos
      exact this
    · exact (hstab D' hD0).ge
  · exact (hcnt D' hD0).trans (hn D' hD0)

theorem card_centralizer_conj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun g => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  constructor
  · intro hg
    rw [show c * g * c⁻¹ * (c * x * c⁻¹) = c * (g * x) * c⁻¹ by group, hg]
    group
  · intro hg
    have : c * (g * x) * c⁻¹ = c * (x * g) * c⁻¹ := by
      rw [show c * (g * x) * c⁻¹ = c * g * c⁻¹ * (c * x * c⁻¹) by group, hg]
      group
    simpa using this

theorem card_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g => ?_)).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

theorem card_centralizer_le_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hfac : (Nat.card G).factorization p = 1) {y z : G} (hy : orderOf y = p)
    (hz : orderOf z = p) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) ≤ Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  let Sz : Sylow p G := Sylow.ofCard (Subgroup.zpowers z) (by rw [Nat.card_zpowers, hz, hfac, pow_one])
  let Sy : Sylow p G := Sylow.ofCard (Subgroup.zpowers y) (by rw [Nat.card_zpowers, hy, hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sy Sz
  have hzm : z ∈ ((g • Sy : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact Subgroup.mem_zpowers z
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzm
  obtain ⟨u, hum, hu⟩ := hzm
  rw [Sylow.coe_ofCard] at hum
  have hu' : g * u * g⁻¹ = z := by
    rw [← hu, MulAut.smul_def, MulAut.conj_apply]
  have hzu : IsConj z u := (isConj_iff.mpr ⟨g, hu'⟩).symm
  have hou : orderOf u = p := by
    have e := MulEquiv.orderOf_eq (MulAut.conj g) u
    rw [MulAut.conj_apply, hu', hz] at e
    exact e.symm
  have heq : Subgroup.zpowers u = Subgroup.zpowers y := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hum) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hou, hy]
  have hym : y ∈ Subgroup.zpowers u := by
    rw [heq]
    exact Subgroup.mem_zpowers y
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hym
  have hle : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← hm]
    have hcu : Commute c u := hc
    exact (hcu.zpow_right m).eq
  calc Nat.card (Subgroup.centralizer ({z} : Set G))
      = Nat.card (Subgroup.centralizer ({u} : Set G)) := card_centralizer_conj hzu
    _ ≤ Nat.card (Subgroup.centralizer ({y} : Set G)) := Subgroup.card_le_of_le hle

theorem card_centralizer_mul_le_of_conj [Finite P] (hKc : Nat.card K = 634023936) {r : ℕ}
    (t : Fin r → K) (c : Fin r → ℕ) (hc : ∀ i, Nat.card (Subgroup.centralizer ({t i} : Set K)) ≤ c i)
    (hsd : ∀ i j, i ≠ j → ¬IsConj (t i) (t j)) (i0 : Fin r) {F : ℕ}
    (hfix : Nat.card {p : Om // (t i0 : P) • p = p} ≤ F) {H : Type*} [Group H] (ψ : P →* H)
    (hψ : Function.Bijective ψ) (z : H) (hz : ∀ i, IsConj z (ψ (t i))) :
    Nat.card (Subgroup.centralizer ({z} : Set H)) * ∑ i, 634023936 / c i ≤ F * 634023936 := by
  let e : P ≃* H := MulEquiv.ofBijective ψ hψ
  have hs : ∀ i, IsConj (t i0 : P) (t i : P) := by
    intro i
    have h1 : IsConj (ψ (t i0)) (ψ (t i)) := (hz i0).symm.trans (hz i)
    obtain ⟨g, hg⟩ := isConj_iff.1 h1
    refine isConj_iff.2 ⟨e.symm g, e.injective ?_⟩
    change ψ (e.symm g * ↑(t i0) * (e.symm g)⁻¹) = ψ ↑(t i)
    rw [map_mul, map_mul, map_inv]
    have he : ψ (e.symm g) = g := e.apply_symm_apply g
    rw [he]
    exact hg
  have h1 := card_centralizer_mul_le hKc (t i0 : P) t c hs hsd hc
  have e1 : Nat.card (Subgroup.centralizer ({z} : Set H)) =
      Nat.card (Subgroup.centralizer ({(t i0 : P)} : Set P)) := by
    rw [card_centralizer_conj (hz i0)]
    exact card_centralizer_equiv e _
  rw [e1]
  exact h1.trans (Nat.mul_le_mul_right _ hfix)

variable (h : KernelFacts)
include h


theorem psi_of_fwd (Df : FwdData) (hf : fwdChk Df = true)
    (hLA : Blueprint.NativeSporadic.ThSeed1 = String.ofList Df.ThSeed_LA)
    (hLB : Blueprint.NativeSporadic.ThSeed2 = String.ofList Df.ThSeed_LB) :
    ∃ ψ : P →* J, Function.Bijective ψ ∧
      (∀ g < 8, 𝕄 (ψ (presGen SporadicName.Th.presentation g)) =
          pkMat (Df.ThS_RBf (BigS.regAt Df.ThS_GRf g)) ∧
        𝕄 ((ψ (presGen SporadicName.Th.presentation g))⁻¹ : J) =
          pkMat (Df.ThS_RBf (BigS.regAt Df.ThS_IRf g))) ∧
      𝕄 a = pkMat (Df.ThS_RBf 1) ∧ 𝕄 b = pkMat (Df.ThS_RBf 2) ∧ 𝕄 (b⁻¹ : J) = pkMat Df.ThS_Bi ∧
      BigS.constsOK Df.ThS_c Df.ThS_rm Df.ThS_tm0 Df.ThS_tm1 Df.ThS_tm2 Df.ThS_tm3 Df.ThS_tm4
        Df.ThS_tm5 Df.ThS_tm6 Df.ThS_tm7 Df.ThS_up Df.ThS_dg Df.ThS_ONE = true := by
  have := h.finite
  obtain ⟨h1, h2, h3⟩ := hsw_th
  have ha : 𝕄 a = Blueprint.NativeSporadic.decode 2 248 1 (String.ofList Df.ThSeed_LA) := by
    rw [← hLA]
    rfl
  have hb : 𝕄 b = Blueprint.NativeSporadic.decode 2 248 1 (String.ofList Df.ThSeed_LB) := by
    rw [← hLB]
    rfl
  obtain ⟨ψ, hx, hra, hrb, hA, hB, hBi, hk⟩ :=
    CFSG.KC.Th.Spec.FwdExt.fwd_ext _ h1 h2 h3 Df hf a b ha hb
  have hs : Function.Surjective ψ := MonoidHom.range_eq_top.1 (range_eq_top hra hrb)
  refine ⟨ψ, hs.bijective_of_nat_card_le ?_, hx, hA, hB, hBi, hk⟩
  rw [card_P_eq h, card_J_eq h]

end CFSG.Sporadic.Th.Kernel

end
