module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Spin
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Cent
public import CFSG.ClassicalGroups.Orthogonal.EichlerNonsingularTwo
import CFSG.ClassicalGroups.Orthogonal.EichlerBlockInvolution
import CFSG.ClassicalGroups.Orthogonal.EichlerBlockTwoSubgroup
import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap

private theorem omegaSixBlockVia_orthPointVia {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (GaloisField 2 1) (ι → GaloisField 2 1)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (Spin.spinAction Q))
    (hrange : (Spin.spinAction Q).range =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hcenter : Subgroup.center (spinGroup Q) = ⊥)
    {X : Type} [Group X] [Finite X] {K J V : Subgroup X} {r : X}
    (hBlock : OmegaSixBlockVia Q K J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hCent : Cent96At J r)
    (hOdd : Odd (Nat.card (Subgroup.center ↥J))) :
    OrthPointVia Q K V r := by
  obtain ⟨φ, W, E, H, hφrange, hφker, hBlockOn, hHmap, hperp, hW⟩ := hBlock
  obtain ⟨hrV, hVJ, hElem, hVcard, hrne, hVconj⟩ := hFour
  have hF : ∀ a : GaloisField 2 1, a = 0 ∨ a = 1 := rck1416_gf2_eq_zero_or_one
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
    isMulCommutative_iff_of_setLike.mp hElem.1
  have hsqV : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    simpa [pow_two] using hElem.2 x hx
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hφker.trans (le_of_eq hcenter))
  have hψinj : Function.Injective (Spin.spinAction Q) := hinj
  have hrJ : r ∈ J := hVJ hrV
  have hrJ' : r ∈ H.map φ := by rwa [hHmap]
  obtain ⟨r₀, hr₀H, hr₀r⟩ := Subgroup.mem_map.mp hrJ'
  have hr₀V : r₀ ∈ V.comap φ := by
    rw [Subgroup.mem_comap, hr₀r]
    exact hrV
  have hr₀sq : r₀ * r₀ = 1 := by
    exact hφinj (by rw [map_mul, hr₀r, map_one]; exact hsqV r hrV)
  have hr₀ne : r₀ ≠ 1 := by
    intro h
    apply hrne
    rw [← hr₀r, h, map_one]
  have hgE : Spin.spinAction Q r₀ ∈ elementaryGroup Q := by
    have hmem : Spin.spinAction Q r₀ ∈ (Spin.spinAction Q).range := ⟨r₀, rfl⟩
    rwa [hrange] at hmem
  have hg2 : Spin.spinAction Q r₀ * Spin.spinAction Q r₀ = 1 := by
    rw [← map_mul, hr₀sq, map_one]
  have hg1 : Spin.spinAction Q r₀ ≠ 1 := by
    intro h
    exact hr₀ne (hψinj (by rw [h, map_one]))
  have hgW : ∀ w ∈ W, Spin.spinAction Q r₀ w ∈ W :=
    ((hBlockOn.2 r₀).mp hr₀H).1
  have hgE' : ∀ e ∈ E, Spin.spinAction Q r₀ e = e :=
    ((hBlockOn.2 r₀).mp hr₀H).2
  obtain ⟨z, y, hzW, hyW, hz0, hz, hzy, hyz, hgeq⟩ :=
    exists_eq_eichler_of_mul_self_block hF hQ hBlockOn.1 hW hgE hg2 hg1 hgW hgE'
  have hgO : Spin.spinAction Q r₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hgE
  have hcommφ : ∀ t : spinGroup Q,
      Spin.spinAction Q t * eichler Q z y = eichler Q z y * Spin.spinAction Q t →
      φ t * r = r * φ t := by
    intro t ht
    have htr : t * r₀ = r₀ * t :=
      hψinj (by rw [map_mul, map_mul, hgeq]; exact ht)
    rw [← hr₀r, ← map_mul, ← map_mul, htr]
  rcases hF (Q y) with hQy | hQy
  ·
    obtain ⟨𝒯, h𝒯elem, h𝒯block, h𝒯comm, h𝒯card⟩ :=
      exists_card_eq_sixtyFour_commute_eichler hF hQ hBlockOn.1 hperp hW
        hzW hyW hz0 hz hQy hzy hyz
    let T : Subgroup X := (𝒯.comap (Spin.spinAction Q)).map φ
    have h𝒯range : 𝒯 ≤ (Spin.spinAction Q).range := by
      rw [hrange]
      exact h𝒯elem
    have hTJ : T ≤ J := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
      have htH : t ∈ H := (hBlockOn.2 t).mpr (h𝒯block (Spin.spinAction Q t) ht)
      have hxJ : φ t ∈ H.map φ := Subgroup.mem_map_of_mem φ htH
      rwa [hHmap] at hxJ
    have hTr : ∀ t ∈ T, t * r = r * t := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
      exact hcommφ t (h𝒯comm (Spin.spinAction Q t) ht)
    have hTcard : Nat.card T = 64 := by
      have h1 : Nat.card ((𝒯.comap (Spin.spinAction Q)).map (Spin.spinAction Q)) =
          Nat.card (𝒯.comap (Spin.spinAction Q)) :=
        Subgroup.card_map_of_injective (f := Spin.spinAction Q) hψinj
      rw [Subgroup.map_comap_eq_self h𝒯range] at h1
      rw [Subgroup.card_map_of_injective (f := φ) hφinj]
      exact h1.symm.trans h𝒯card
    exact (rck_cent96At_false_of_le hOdd hCent hTJ hTr hTcard).elim
  ·
    have hEW : ∀ a ∈ W, polar Q z a = 0 →
        (∀ w ∈ W, eichler Q z a w ∈ W) ∧ ∀ e ∈ E, eichler Q z a e = e := by
      intro a ha hpa
      constructor
      · intro w hw
        rw [eichler_apply hz hpa]
        exact W.sub_mem (W.add_mem hw (W.smul_mem _ ha)) (W.smul_mem _ hzW)
      · intro e he
        rw [eichler_apply hz hpa, polar_comm Q e z, hperp z hzW e he,
          polar_comm Q e a, hperp a ha e he]
        simp
    let Y₀ : Subgroup (spinGroup Q) :=
      { carrier := {t | ∃ a ∈ W, polar Q z a = 0 ∧
          Spin.spinAction Q t = eichler Q z a}
        one_mem' := ⟨0, W.zero_mem, by rw [polar_zero_right],
          by rw [map_one, eichler_zero_right]⟩
        mul_mem' := by
          rintro t₁ t₂ ⟨a₁, ha₁, hp₁, ht₁⟩ ⟨a₂, ha₂, hp₂, ht₂⟩
          refine ⟨a₁ + a₂, W.add_mem ha₁ ha₂, ?_, ?_⟩
          · rw [polar_add_right, hp₁, hp₂, add_zero]
          · rw [map_mul, ht₁, ht₂, eichler_mul hp₁ hp₂]
        inv_mem' := by
          rintro t ⟨a, ha, hp, ht⟩
          refine ⟨-a, W.neg_mem ha, ?_, ?_⟩
          · rw [polar_neg_right, hp, neg_zero]
          · rw [map_inv, ht, eichler_inv hp] }
    have hY₀H : Y₀ ≤ H := by
      rintro t ⟨a, ha, hpa, ht⟩
      rw [hBlockOn.2 t]
      simpa only [ht] using hEW a ha hpa
    let Y : Subgroup X := Y₀.map φ
    have hYle : Y ≤ J ⊓ Subgroup.centralizer ({r} : Set X) := by
      intro y hy
      obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hmem : φ t ∈ J := hHmap ▸ Subgroup.mem_map_of_mem φ (hY₀H ht)
        rwa [← hty]
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hty]
        refine hcommφ t ?_
        obtain ⟨a, ha, hpa, hta⟩ := ht
        rw [hta]
        exact rootGroup_commute (eichler_mem_rootGroup hpa) (eichler_mem_rootGroup hzy)
    have hYp : IsPGroup 2 Y := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro y
      refine ⟨1, ?_⟩
      have hy2 : y * y = 1 := by
        apply Subtype.ext
        change (y : X) * (y : X) = 1
        obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp y.2
        obtain ⟨a, ha, hpa, hta⟩ := ht
        have haa : a + a = 0 := by
          have h2 : (2 : GaloisField 2 1) = 0 := CharP.cast_eq_zero (GaloisField 2 1) 2
          calc a + a = (2 : GaloisField 2 1) • a := (two_smul (GaloisField 2 1) a).symm
            _ = 0 := by rw [h2, zero_smul]
        have hsq : eichler Q z a * eichler Q z a = 1 := by
          rw [eichler_mul hpa hpa, haa, eichler_zero_right]
        have htt : t * t = 1 :=
          hψinj (by rw [map_mul, hta, hsq, map_one])
        rw [← hty, ← map_mul, htt, map_one]
      have hy2' : y ^ 2 = 1 := by
        rwa [pow_two]
      simpa using hy2'
    have hYnorm : ∀ h ∈ J ⊓ Subgroup.centralizer ({r} : Set X),
        ∀ q ∈ Y, h * q * h⁻¹ ∈ Y := by
      intro h hh q hq
      have hhJ : h ∈ J := (Subgroup.mem_inf.mp hh).1
      have hhr : h ∈ Subgroup.centralizer ({r} : Set X) := (Subgroup.mem_inf.mp hh).2
      have hhJ' : h ∈ H.map φ := by rwa [hHmap]
      obtain ⟨s, hsH, hsh⟩ := Subgroup.mem_map.mp hhJ'
      have hsr : s * r₀ = r₀ * s :=
        hφinj (by
          rw [map_mul, map_mul, hsh, hr₀r]
          exact Subgroup.mem_centralizer_singleton_iff.mp hhr)
      have hψscomm : Spin.spinAction Q s * eichler Q z y =
          eichler Q z y * Spin.spinAction Q s := by
        rw [← hgeq, ← map_mul, ← map_mul, hsr]
      have hsgO : Spin.spinAction Q s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => Spin.map_spinAction Q s w
      have hsz : Spin.spinAction Q s z = z :=
        (fix_of_commute_eichler hF hQ hz0 hz hzy hQy hsgO hψscomm).1
      obtain ⟨t, htY₀, htq⟩ := Subgroup.mem_map.mp hq
      obtain ⟨a, ha, hpa, hta⟩ := htY₀
      have hsa : Spin.spinAction Q s a ∈ W := ((hBlockOn.2 s).mp hsH).1 a ha
      have hspa : polar Q z (Spin.spinAction Q s a) = 0 := by
        have hmap := polar_map_of_mem hsgO z a
        rwa [hsz, hpa] at hmap
      have hconj : Spin.spinAction Q (s * t * s⁻¹) =
          eichler Q z (Spin.spinAction Q s a) := by
        rw [show Spin.spinAction Q (s * t * s⁻¹) =
          Spin.spinAction Q s * Spin.spinAction Q t * (Spin.spinAction Q s)⁻¹ by
            simp only [map_mul, map_inv]]
        rw [hta, eichler_conj (u := z) (w := a) hsgO, hsz]
      have hst : s * t * s⁻¹ ∈ Y₀ := ⟨Spin.spinAction Q s a, hsa, hspa, hconj⟩
      have hq' : h * q * h⁻¹ = φ (s * t * s⁻¹) := by
        rw [← htq, ← hsh]
        simp only [map_mul, map_inv]
      rw [hq']
      exact Subgroup.mem_map_of_mem φ hst
    have hYpCore : Y ≤ pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)) :=
      le_pCoreOf_of_normalized 2 hYle hYp hYnorm
    have hVrange : V ≤ φ.range := hVJ.trans (hHmap ▸ Subgroup.map_le_range φ H)
    have hV0map : (V.comap φ).map φ = V := Subgroup.map_comap_eq_self hVrange
    have hleRoot : (V.comap φ).map (Spin.spinAction Q) ≤ rootGroup Q z := by
      rintro g ⟨v, hv, rfl⟩
      have hvV : φ v ∈ V := hv
      have hvJ : φ v ∈ J := hVJ hvV
      have hv' : φ v ∈ H.map φ := by rwa [hHmap]
      obtain ⟨s, hsH, hsv⟩ := Subgroup.mem_map.mp hv'
      have hsv' : s = v := hφinj hsv
      have hvH : v ∈ H := hsv' ▸ hsH
      have hgOv : Spin.spinAction Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => Spin.map_spinAction Q v w
      have hgEv : Spin.spinAction Q v ∈ elementaryGroup Q := by
        have hmem : Spin.spinAction Q v ∈ (Spin.spinAction Q).range := ⟨v, rfl⟩
        rwa [hrange] at hmem
      have hvr : v * r₀ = r₀ * v :=
        hφinj (by rw [map_mul, map_mul, hr₀r]; exact hcommV (φ v) hvV r hrV)
      have hcv : Spin.spinAction Q v * eichler Q z y =
          eichler Q z y * Spin.spinAction Q v := by
        rw [← hgeq, ← map_mul, ← map_mul, hvr]
      have hgz : Spin.spinAction Q v z = z :=
        (fix_of_commute_eichler hF hQ hz0 hz hzy hQy hgOv hcv).1
      have hspanW : ∀ a ∈ W, polar Q z a = 0 →
          Spin.spinAction Q v a - a ∈ Submodule.span (GaloisField 2 1) {z, y} := by
        intro a ha hpa
        obtain ⟨t, ht⟩ : ∃ t : spinGroup Q, Spin.spinAction Q t = eichler Q z a := by
          have hmem : eichler Q z a ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q z a
          have hmem' : eichler Q z a ∈ (Spin.spinAction Q).range := by rwa [hrange]
          exact MonoidHom.mem_range.mp hmem'
        have htY₀ : t ∈ Y₀ := ⟨a, ha, hpa, ht⟩
        have htY : φ t ∈ Y := Subgroup.mem_map_of_mem φ htY₀
        have htcore : φ t ∈ pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)) :=
          hYpCore htY
        have hmem := hCore (φ v) hvV (φ t) htcore
        have hu : φ (v * t * v⁻¹ * t⁻¹) ∈ Subgroup.zpowers r := by
          simpa only [map_mul, map_inv] using hmem
        have hzpow : ∀ u : X, u ∈ Subgroup.zpowers r → u = 1 ∨ u = r := by
          intro u hu'
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu'
          have hr2 : r ^ (2 : ℕ) = 1 := by
            simpa [pow_two] using hsqV r hrV
          rw [zpow_eq_zpow_emod' k (n := 2) hr2] at hk
          rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
          · left
            rw [← hk]
            change r ^ (k % 2) = 1
            rw [hk0]
            simp
          · right
            rw [← hk]
            change r ^ (k % 2) = r
            rw [hk1]
            simp
        have hstep : Spin.spinAction Q (v * t * v⁻¹ * t⁻¹) = 1 ∨
            Spin.spinAction Q (v * t * v⁻¹ * t⁻¹) = eichler Q z y := by
          rcases hzpow _ hu with h1 | h1
          · left
            have h1' : v * t * v⁻¹ * t⁻¹ = 1 :=
              hφinj (by rw [h1, map_one])
            rw [h1', map_one]
          · right
            have h1' : v * t * v⁻¹ * t⁻¹ = r₀ :=
              hφinj (by rw [h1, hr₀r])
            rw [h1', hgeq]
        have hga : polar Q z (Spin.spinAction Q v a) = 0 := by
          have hmap := polar_map_of_mem hgOv z a
          rwa [hgz, hpa] at hmap
        have hna : polar Q z (-a) = 0 := by rw [polar_neg_right, hpa, neg_zero]
        have hcalc : Spin.spinAction Q (v * t * v⁻¹ * t⁻¹) =
            eichler Q z (Spin.spinAction Q v a - a) := by
          have h1 : Spin.spinAction Q (v * t * v⁻¹ * t⁻¹) =
              Spin.spinAction Q v * Spin.spinAction Q t * (Spin.spinAction Q v)⁻¹ *
                (Spin.spinAction Q t)⁻¹ := by
            simp only [map_mul, map_inv]
          rw [h1, ht, eichler_conj (u := z) (w := a) hgOv, hgz, eichler_inv hpa]
          rw [eichler_mul hga hna]
          congr 2
          abel
        have hpol : polar Q z (Spin.spinAction Q v a - a) = 0 := by
          rw [polar_sub_right, hga, hpa, sub_zero]
        rcases hstep with hstep1 | hstepx
        · have hEq : eichler Q z (Spin.spinAction Q v a - a) = eichler Q z 0 := by
            rw [← hcalc, hstep1, eichler_zero_right]
          have hmem := (eichler_eq_eichler_iff_sub_mem hQ hz0 hz hpol
            (polar_zero_right Q z)).mp hEq
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
          rw [sub_zero] at hc
          exact Submodule.mem_span_pair.mpr ⟨c, 0, by rw [zero_smul, add_zero]; exact hc⟩
        · have hEq : eichler Q z (Spin.spinAction Q v a - a) = eichler Q z y := by
            rw [← hcalc, hstepx]
          have hmem := (eichler_eq_eichler_iff_sub_mem hQ hz0 hz hpol hzy).mp hEq
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
          have hb : Spin.spinAction Q v a - a = c • z + y := by
            rw [hc]
            abel
          exact Submodule.mem_span_pair.mpr ⟨c, 1, by rw [one_smul]; exact hb.symm⟩
      have hspan : ∀ w, polar Q z w = 0 →
          Spin.spinAction Q v w - w ∈ Submodule.span (GaloisField 2 1) {z, y} := by
        intro w hw
        have hw' : w ∈ W ⊔ E := by
          rw [hBlockOn.1.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨a, ha, e, he, hwe⟩ := Submodule.mem_sup.mp hw'
        rw [← hwe]
        have hpa : polar Q z a = 0 := by
          have h0 := hw
          rw [← hwe, polar_add_right, hperp z hzW e he, add_zero] at h0
          exact h0
        have hve : Spin.spinAction Q v e = e := ((hBlockOn.2 v).mp hvH).2 e he
        have hdecomp : Spin.spinAction Q v (a + e) - (a + e) =
            Spin.spinAction Q v a - a := by
          rw [map_add, hve]
          abel
        rw [hdecomp]
        exact hspanW a ha hpa
      exact mem_rootGroup_of_mem_elementaryGroup hQ hz0 hz hzy hQy hgEv hgz hspan
    exact ⟨φ, r₀, V.comap φ, z, y, hφrange, hφker, hr₀r, hr₀V, hV0map,
      hz0, hz, hzy, hQy, hgeq, hleRoot⟩

theorem rckIIpOmegaSixBridge : RCKIIpOmegaSixBridge := by
  intro X _ _ K J V r hOddJ _ hFour hCore hCent hEmbed
  rcases hEmbed with ⟨n, hBlock⟩ | ⟨n, hBlock⟩
  · obtain ⟨φ, W, E, H, hφrange, hφker, hBlockOn, hHmap, hperp, hW⟩ := hBlock
    have hcard : Fintype.card (Fin n ⊕ Fin n) = n + n := by simp
    have hle : 6 ≤ n + n := by
      calc 6 = Module.finrank (GaloisField 2 1) W := hW.symm
        _ ≤ Module.finrank (GaloisField 2 1)
            (Fin n ⊕ Fin n → GaloisField 2 1) := Submodule.finrank_le W
        _ = Fintype.card (Fin n ⊕ Fin n) :=
          Module.finrank_fintype_fun_eq_card (GaloisField 2 1)
        _ = n + n := hcard
    have hn : 3 ≤ n := by omega
    obtain ⟨hQ, hinj, hrange, hcenter, -⟩ := rck1416_quadPlus_facts hn
    exact Or.inl ⟨n, hn, omegaSixBlockVia_orthPointVia hQ hinj hrange hcenter
      ⟨φ, W, E, H, hφrange, hφker, hBlockOn, hHmap, hperp, hW⟩
      hFour hCore hCent hOddJ⟩
  · obtain ⟨φ, W, E, H, hφrange, hφker, hBlockOn, hHmap, hperp, hW⟩ := hBlock
    have hcard : Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) =
        (n - 1) + (n - 1) + 2 := by
      simp
      omega
    have hle : 6 ≤ (n - 1) + (n - 1) + 2 := by
      calc 6 = Module.finrank (GaloisField 2 1) W := hW.symm
        _ ≤ Module.finrank (GaloisField 2 1)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1) :=
              Submodule.finrank_le W
        _ = Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :=
              Module.finrank_fintype_fun_eq_card (GaloisField 2 1)
        _ = (n - 1) + (n - 1) + 2 := hcard
    have hn : 3 ≤ n := by
      by_contra h
      have h2 : n ≤ 2 := by omega
      interval_cases n <;> norm_num at hle
    obtain ⟨hQ, hinj, hrange, hcenter, -⟩ := rck1416_quadMinus_facts hn
    exact Or.inr ⟨n, hn, omegaSixBlockVia_orthPointVia hQ hinj hrange hcenter
      ⟨φ, W, E, H, hφrange, hφker, hBlockOn, hHmap, hperp, hW⟩
      hFour hCore hCent hOddJ⟩

end CFSG.StandardType.RCKC1
