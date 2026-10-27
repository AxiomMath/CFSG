module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymA
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymMatching
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymNorm
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymSwaps
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymGen
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymBarGen
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem exists_equiv_isSwap {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 6 ≤ m)
    (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) {t : Y} (ht : t * t = 1)
    (hD : IsOddTranspClass {y : Y | IsConj t y}) :
    ∃ e' : Y ⧸ fusionOddCore Y ≃* Perm (Fin m), (symPi e' t).IsSwap :=
  w85g_exists_equiv_isSwap hm e ht hD

theorem map_centralizer_eq {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    (Subgroup.centralizer ({t} : Set Y)).map (symPi e) =
      Subgroup.centralizer ({symPi e t} : Set (Perm (Fin m))) := by
  have hker : (symPi e).ker = fusionOddCore Y := by
    rw [symPi]
    ext z
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [← map_mul, ← map_mul]
    exact congrArg (symPi e) (hx t (Set.mem_singleton t))
  · intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy
    obtain ⟨x, hxπ⟩ := w85g_symPi_surjective e y
    have hxπ' : symPi e x = y := hxπ
    have hxt : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      rw [show (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, h.mul_self]
      simp
    have h1 : x * t * x⁻¹ * t⁻¹ ∈ fusionOddCore Y := by
      have h2 : symPi e (x * t * x⁻¹ * t⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hxπ']
        rw [← hy (symPi e t) (by simp)]
        group
      rwa [← MonoidHom.mem_ker, hker] at h2
    have hcO : t * (x * t * x⁻¹) ∈ fusionOddCore Y := by
      have h2 : t * (x * t * x⁻¹) = t * (x * t * x⁻¹ * t⁻¹) * t⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right h.mul_self]
        rw [show t * (x * t * x⁻¹ * t) * t = t * (x * t * x⁻¹) * (t * t) by group,
          h.mul_self, mul_one]
      rw [h2]
      exact (fusionOddCore_normal Y).conj_mem _ h1 t
    obtain ⟨o, hoO, hoo⟩ := w85g_exists_conj_mem_fusionOddCore h.mul_self hxt hcO
    refine Subgroup.mem_map.mpr ⟨o⁻¹ * x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      have h3 : (o⁻¹ * x) * t = t * (o⁻¹ * x) := by
        have h4 : o⁻¹ * (x * t * x⁻¹) * o = t := by
          rw [← hoo]; group
        calc (o⁻¹ * x) * t = o⁻¹ * (x * t * x⁻¹) * (o * o⁻¹) * x := by group
          _ = (o⁻¹ * (x * t * x⁻¹) * o) * (o⁻¹ * x) := by group
          _ = t * (o⁻¹ * x) := by rw [h4]
      exact h3.symm
    · simp only [map_mul, map_inv, MonoidHom.mem_ker.mp (by rw [hker]; exact hoO), inv_one,
        one_mul]
      exact hxπ'

theorem symmetric_generation {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    Subgroup.closure ((Subgroup.centralizer ({t} : Set Y) : Set Y) ∪
      (Subgroup.setNormalizer (symT t (P : Subgroup Y)) : Set Y)) = ⊤ := by
  let C : Subgroup Y := Subgroup.centralizer ({t} : Set Y)
  let N : Subgroup Y := Subgroup.setNormalizer (symT t (P : Subgroup Y))
  let R : Subgroup Y := Subgroup.closure ((C : Set Y) ∪ (N : Set Y))
  have hπsurj : Function.Surjective (symPi e) := w85g_symPi_surjective e
  have hker : (symPi e).ker = fusionOddCore Y := by
    rw [symPi]
    ext z
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  let P' : Sylow 2 (Perm (Fin m)) := P.mapSurjective hπsurj
  have hτP : symPi e t ∈ (P' : Subgroup (Perm (Fin m))) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem (symPi e) h.mem
  have h5 : 5 ≤ m := le_trans (by norm_num : 5 ≤ 6) h.six_le
  have hcl := closure_centralizer_sup_normalizer_swaps h5 P' h.swap hτP
  have hmatch := symT_matching h
  have hset : symPi e '' symT t (P : Subgroup Y) =
      {σ : Perm (Fin m) | σ.IsSwap ∧ σ ∈ (P' : Subgroup (Perm (Fin m)))} := by
    ext σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hmatch.2.2.1 x hx, by
        rw [Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem (symPi e) hx.2⟩
    · rintro ⟨hσ, hσP⟩
      obtain ⟨a, b, hab, rfl⟩ := hσ
      rw [Sylow.coe_mapSurjective] at hσP
      exact hmatch.2.2.2 a b hab hσP
  have hmapR : R.map (symPi e) = ⊤ := by
    show (Subgroup.closure ((C : Set Y) ∪ (N : Set Y))).map (symPi e) = ⊤
    rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map,
      map_centralizer_eq h, map_setNormalizer_eq h, hset]
    exact hcl
  have hOle : fusionOddCore Y ≤ R := fusionOddCore_le_closure h
  have htop : R = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : symPi e y ∈ R.map (symPi e) := by rw [hmapR]; exact Subgroup.mem_top _
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp hy
    have hyr : y * r⁻¹ ∈ fusionOddCore Y := by
      have hmem : y * r⁻¹ ∈ (symPi e).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hry, mul_inv_cancel]
      rwa [hker] at hmem
    have hy' : y = (y * r⁻¹) * r := by group
    rw [hy']
    exact R.mul_mem (hOle hyr) hr
  simpa [R, C, N] using htop

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

theorem isSymGp_of_kBarOddQuotShape (d : ShapeData V H T φ) {m : ℕ}
    (h : KBarOddQuotShape V H T (fun X _ => IsSymGp X m)) :
    IsSymGp (X ⧸ fusionOddCore X) m := by
  haveI : Finite X := d.finite
  obtain ⟨Y, hYgrp, φ', hφ', hsym'⟩ := h
  letI := hYgrp
  haveI : Finite Y := Finite.of_surjective φ' hφ'.surjective
  obtain ⟨Y₀, hY₀grp, φ₀, ψ, hφ₀, hψsurj, _hψcomp, hψker⟩ :=
    exists_central_quotient d.hyp83 d.eq_sup d.bar
  letI := hY₀grp
  haveI : Finite Y₀ := Finite.of_surjective φ₀ hφ₀.surjective
  have hoddψ : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat d.odd_card_center (Subgroup.card_dvd_of_le hψker)
  have hker' : φ'.ker = (Subgroup.centralizer (eSub V H T : Set G)).subgroupOf (kGenIn V H) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ'.ker_iff k
  have hker₀ : φ₀.ker = (Subgroup.centralizer (eSub V H T : Set G)).subgroupOf (kGenIn V H) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ₀.ker_iff k
  have he : Y ≃* Y₀ :=
    (QuotientGroup.quotientKerEquivOfSurjective (φ := φ') hφ'.surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hker'.trans hker₀.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective (φ := φ₀) hφ₀.surjective))
  have hsymY₀ : IsSymGp (Y₀ ⧸ fusionOddCore Y₀) m :=
    w85g_isSymGp_quot_fusionOddCore_of_mulEquiv he hsym'
  exact w85g_isSymGp_quot_fusionOddCore_of_surjective ψ hψsurj hoddψ hsymY₀

theorem exists_symSetting (d : ShapeData V H T φ)
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2) {m : ℕ} (hm : 6 ≤ m)
    (h : IsSymGp (X ⧸ fusionOddCore X) m) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ' : ↥(kGenIn V H) →* Y)
      (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) (t : Y) (P : Sylow 2 Y),
      TailSetup V H T φ' ∧ SymSetting e t P ∧
        barSub (kGenIn V H) φ' V = Subgroup.zpowers t ∧
        (P : Subgroup Y) = barSub (kGenIn V H) φ' T := by
  haveI : Finite X := d.finite
  obtain ⟨Y, hYgrp, φ', ψ, hφ', hψsurj, hψcomp, hψker⟩ :=
    exists_central_quotient d.hyp83 d.eq_sup d.bar
  letI := hYgrp
  have hYfin : Finite Y := Finite.of_surjective φ' hφ'.surjective
  haveI := hYfin
  have hoddψ : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat d.odd_card_center (Subgroup.card_dvd_of_le hψker)
  obtain ⟨t, ht2, ht1, hSmap, hoddclass⟩ :=
    barSituation_map_two d.situation hS2 ψ hψsurj hoddψ
  have hφ'eq : φ' = ψ.comp φ := by
    ext k
    exact (hψcomp k).symm
  have hSV : barSub (kGenIn V H) φ' V = (barSub (kGenIn V H) φ V).map ψ := by
    rw [hφ'eq]
    show (V.subgroupOf (kGenIn V H)).map (ψ.comp φ) =
      ((V.subgroupOf (kGenIn V H)).map φ).map ψ
    rw [Subgroup.map_map]
  have ht : barSub (kGenIn V H) φ' V = Subgroup.zpowers t := by rw [hSV, hSmap]
  let s : TailSetup V H T φ' := ⟨d.hyp83, d.eq_sup, hφ'⟩
  obtain ⟨P, hP⟩ := exists_sylow_barSub_T s
  have htV : t ∈ barSub (kGenIn V H) φ' V := by rw [ht]; exact Subgroup.mem_zpowers t
  have hVleT : barSub (kGenIn V H) φ' V ≤ barSub (kGenIn V H) φ' T :=
    Subgroup.map_mono (fun x hx => d.hyp83.le_T hx)
  have htP : t ∈ (P : Subgroup Y) := by rw [hP]; exact hVleT htV
  have hcentral : ∀ y ∈ (P : Subgroup Y), t * y = y * t := by
    intro y hy
    rw [hP] at hy
    obtain ⟨k, hkT, hkφ⟩ := mem_barSub.mp hy
    obtain ⟨v, hvV, hvφ⟩ := mem_barSub.mp htV
    have hy_eq : y = φ' k := hkφ.symm
    have ht_eq : t = φ' v := hvφ.symm
    have hconj : φ' (k * v * k⁻¹) = y * t * y⁻¹ := by
      rw [hy_eq, ht_eq, map_mul, map_mul, map_inv]
    have hmemV : (k * v * k⁻¹) ∈ V.subgroupOf (kGenIn V H) := by
      change ((k : G) * (v : G) * (k : G)⁻¹) ∈ V
      exact (Subgroup.mem_normalizer_iff.mp (d.hyp83.T_le_normalizer hkT) (v : G)).mp hvV
    have hmem : φ' (k * v * k⁻¹) ∈ barSub (kGenIn V H) φ' V :=
      Subgroup.mem_map_of_mem φ' hmemV
    rw [ht] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hne : φ' (k * v * k⁻¹) ≠ 1 := by
      rw [hconj]
      intro h1
      have ht1' : t = 1 := by
        have h := congrArg (fun z => y⁻¹ * z * y) h1
        have hkey : y⁻¹ * (y * t * y⁻¹) * y = t := by group
        rw [hkey] at h
        simpa using h
      exact ht1 ht1'
    have ht2z : t ^ (2 : ℤ) = 1 := by simpa [pow_two] using ht2
    have hpow : ∀ n : ℤ, t ^ n = 1 ∨ t ^ n = t := by
      intro n
      rcases n.even_or_odd with ⟨m, hm⟩ | ⟨m, hm⟩
      · left
        rw [hm]
        rw [show m + m = 2 * m by ring, zpow_mul t 2 m, ht2z, one_zpow]
      · right
        rw [hm]
        rw [zpow_add t (2 * m) 1, zpow_mul t 2 m, ht2z,
          one_zpow, zpow_one, one_mul]
    have hconj_t : y * t * y⁻¹ = t := by
      rcases hpow n with h | h
      · exact absurd (hn.symm.trans h) hne
      · rw [← hconj]
        exact hn.symm.trans h
    have : y * t = t * y := by
      have := congrArg (fun z => z * y) hconj_t
      simpa [mul_assoc] using this
    exact this.symm
  obtain ⟨e₀⟩ := h
  obtain ⟨π, hπs, _hπψ, hπodd, hπmax, _⟩ := gap5X_exists_pi ψ hψsurj hoddψ e₀
  have hπker : π.ker = fusionOddCore Y := le_antisymm
    (CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hπodd)
    (hπmax (fusionOddCore Y) (fusionOddCore_normal Y)
      (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y))
  let e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπs)
  obtain ⟨e', he'⟩ := exists_equiv_isSwap hm e ht2 hoddclass
  exact ⟨Y, hYgrp, hYfin, φ', e', t, P, s,
    ⟨hm, ht2, he', hoddclass, htP, hcentral⟩, ht, hP⟩

theorem threeFirst_symmetric (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hTwo : W3Lem85TwoKT G) :
    ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
      IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
      (∃ m : ℕ, 3 < m ∧ KBarOddQuotShape V H T (fun X _ => IsSymGp X m)) →
      ¬ KBarCenterShape V H T (fun X _ => IsSpGp X 4 1) →
        H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
  intro V H T hV hH hH0 hT hKT hshape hnot
  obtain ⟨m, hm, hshape'⟩ := hshape
  obtain ⟨X, hXgrp, hXfin, φ, d, _halt⟩ := exists_shapeData h711 hV hH hH0 hT hKT
  letI := hXgrp
  haveI := hXfin
  have hsym : IsSymGp (X ⧸ fusionOddCore X) m := isSymGp_of_kBarOddQuotShape d hshape'
  have hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2 :=
    card_barSub_eq_two_of_symGp h711 d hm hsym
  have hm45 : ¬ (m = 4 ∨ m = 5) := fun h45 =>
    false_of_symGp_four_five d.situation hS2 (d.central hS2) hsym h45
  have hm6 : 6 ≤ m := by omega
  obtain ⟨Y, hYgrp, hYfin, φ', e, t, P, hTail, hSym, ht, hP⟩ :=
    exists_symSetting d hS2 hm6 hsym
  letI := hYgrp
  haveI := hYfin
  have hgen : Subgroup.closure ((Subgroup.centralizer ({t} : Set Y) : Set Y) ∪
      (Subgroup.setNormalizer (symT t (P : Subgroup Y)) : Set Y)) = ⊤ :=
    symmetric_generation hSym
  rcases hTwo V H T hV hH hH0 hT hKT with hfirst | ⟨m', n', hm', hSp | hPSU⟩
  · exact threeFirst_of_bar_generation hTail hfirst ht hP hgen
  · exfalso
    have hSpX : IsSpGp (X ⧸ Subgroup.center X) m' n' := by
      obtain ⟨Z, _, hZ, ⟨eZ⟩⟩ :=
        nonempty_mulEquiv_of_kBarCenterShape d.hyp83 d.eq_sup hSp d.bar
      obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨eY⟩⟩ := hZ
      exact ⟨k, hk, F, hFld, hFin, hFcard, ⟨eZ.trans eY⟩⟩
    have h4 : IsSpGp (X ⧸ Subgroup.center X) 4 1 :=
      isSpGp_four_one_of_isSymGp_of_spPSU (Y := X) (by omega) d.odd_card_center hsym hm'
        (Or.inl hSpX)
    exact hnot (d.kBarCenterShape h4)
  · exfalso
    have hPSUX : IsPSUGp (X ⧸ Subgroup.center X) m' n' := by
      obtain ⟨Z, _, hZ, ⟨eZ⟩⟩ :=
        nonempty_mulEquiv_of_kBarCenterShape d.hyp83 d.eq_sup hPSU d.bar
      exact CFSG.Blueprint.LieModel.of_mulEquiv eZ.symm hZ
    have h4 : IsSpGp (X ⧸ Subgroup.center X) 4 1 :=
      isSpGp_four_one_of_isSymGp_of_spPSU (Y := X) (by omega) d.odd_card_center hsym hm'
        (Or.inr hPSUX)
    exact hnot (d.kBarCenterShape h4)

end CFSG.LocalAnalysis.WeakClosure81

end
