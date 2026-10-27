module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Line
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.TheoremTwo
public import CFSG.OddTranspositions.PartFour.LineSpan
public import CFSG.OddTranspositions.PartFour.LineVmem
import CFSG.OddTranspositions.SevenLocalSecondConverse
public import CFSG.OddTranspositions.PartFour.LineStabilizer

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}



namespace MainHyp

variable {hC : HypothesisC D}

private theorem mem_blockLine_of_mem_Dalpha_of_mem_Dalpha (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha)
    (hcon : ∀ γ, γ ∈ Dalpha D hC.alpha → γ ∈ Dalpha D β →
      γ ∈ blockLine D hC.alpha β)
    {β₁ : Set G} (hβ₁ : β₁ ∈ Dalpha D hC.alpha) {γ : Set G}
    (hγ : γ ∈ Dalpha D hC.alpha) (hγβ₁ : γ ∈ Dalpha D β₁) :
    γ ∈ blockLine D hC.alpha β₁ := by
  obtain ⟨g, hgN, hgβ⟩ := hC.normalizer_transitive β hβ β₁ hβ₁
  have hgα : cimg g hC.alpha = hC.alpha := cimg_eq_self_of_mem_normalizer hgN
  have hgα' : cimg g⁻¹ hC.alpha = hC.alpha := by
    rw [← hgα, cimg_inv_cimg g hC.alpha]
    exact hgα.symm
  have hβeq : cimg g⁻¹ β₁ = β := by
    rw [← hgβ]
    change cimg g⁻¹ (cimg g β) = β
    rw [cimg_inv_cimg g β]
  have hg' : (fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' hC.alpha = hC.alpha := by
    simpa only [cimg] using hgα'
  have hβeq' : (fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' β₁ = β := by
    simpa only [cimg] using hβeq
  have hγ'α : cimg g⁻¹ γ ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hγ g⁻¹
    rw [hg'] at h
    exact h
  have hγ'β : cimg g⁻¹ γ ∈ Dalpha D β := by
    have h := Dalpha.conj hC.setup.normal hγβ₁ g⁻¹
    rw [hβeq'] at h
    exact h
  have hmem := hcon (cimg g⁻¹ γ) hγ'α hγ'β
  have h := (cimg_mem_blockLine_iff hC.setup.normal g hC.alpha β (cimg g⁻¹ γ)).mpr hmem
  change cimg g (cimg g⁻¹ γ) ∈ blockLine D (cimg g hC.alpha) (cimg g β) at h
  rw [cimg_cimg_inv g γ, hgα] at h
  change γ ∈ blockLine D hC.alpha ((fun x => g * x * g⁻¹) '' β) at h
  rw [hgβ] at h
  exact h

private theorem orderOf_dvd_two_pow_of_sq_mem_pCore {z : Halpha D hC.alpha}
    (hz : z * z ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    ∃ k : ℕ, orderOf z ∣ 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha)).exists_orderOf_eq_pow
    (⟨z * z, hz⟩ : CFSG.pCore 2 (Halpha D hC.alpha))
  refine ⟨k + 1, ?_⟩
  have hzz : orderOf (z * z) = 2 ^ k := by
    have h := hk
    rw [← Subgroup.orderOf_coe (⟨z * z, hz⟩ : CFSG.pCore 2 (Halpha D hC.alpha))] at h
    exact h
  have hpow : z ^ (2 ^ (k + 1)) = 1 := by
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, pow_mul]
    rw [show z ^ 2 = z * z from pow_two z, ← hzz, pow_orderOf_eq_one]
  exact orderOf_dvd_of_pow_eq_one hpow

private theorem sq_mem_pCore_of_mem_DalphaStar_triangle (h : MainHyp hC) {βx : Set G}
    (hβx : βx ∈ Dalpha D hC.alpha) {x y t : G} (hxβx : x ∈ βx)
    (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha)
    (ht : t ∈ DalphaStar D hC.alpha) (htri : IsTriangle D x y t)
    {r : Halpha D hC.alpha} (hr : r ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    {x' : G} (hx'βx : x' ∈ βx) (ht_eq : t = (r : G) * x' * (r : G)⁻¹) :
    (⟨x, Subgroup.subset_closure hx⟩ * ⟨t, Subgroup.subset_closure ht⟩ *
      ⟨y, Subgroup.subset_closure hy⟩) * (⟨x, Subgroup.subset_closure hx⟩ *
      ⟨t, Subgroup.subset_closure ht⟩ * ⟨y, Subgroup.subset_closure hy⟩) ∈
      CFSG.pCore 2 (Halpha D hC.alpha) := by
  have hxD : x ∈ D := DalphaStar_subset hC.isBlock_alpha hx
  have htD : t ∈ D := DalphaStar_subset hC.isBlock_alpha ht
  have hyD : y ∈ D := DalphaStar_subset hC.isBlock_alpha hy
  set xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  set tH : Halpha D hC.alpha := ⟨t, Subgroup.subset_closure ht⟩
  set yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  set xH' : Halpha D hC.alpha := ⟨x', Subgroup.subset_closure (subset_DalphaStar hβx hx'βx)⟩
  have hx2 : xH * xH = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hxD)
  have ht2 : tH * tH = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one htD)
  have hy2 : yH * yH = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hyD)
  have hxtsq : (xH * tH) ^ 2 = 1 :=
    (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hx2 ht2).mp
      (Subtype.ext htri.2.2.2.2.1.eq)
  have htH_eq : tH = r * xH' * r⁻¹ := Subtype.ext ht_eq
  have ht_mk : QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) tH =
      QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) xH' := by
    rw [htH_eq, map_mul, map_mul, map_inv, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff r).mpr hr, inv_one, mul_one, one_mul]
  have hxx'_sq_mk :
      QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) ((xH * xH') ^ 2) = 1 := by
    have h : QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) (xH * xH') =
        QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) (xH * tH) := by
      rw [map_mul, map_mul, ht_mk]
    rw [pow_two, map_mul, h, ← map_mul, ← pow_two, hxtsq, map_one]
  have hcommxx' : Commute (x : G) x' :=
    commute_of_mul_sq_mem_pCore hC hxD (hβx.2.1 hx'βx)
      ((QuotientGroup.eq_one_iff _).mp hxx'_sq_mk)
  have hxH'_eq : xH' = xH := by
    by_contra hne
    exact h.not_commute_of_mem_block hβx hxβx hx'βx (fun h => hne (Subtype.ext h.symm)) hcommxx'
  have hz : QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) (xH * tH * yH) =
      QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) yH := by
    rw [map_mul, map_mul, ht_mk, hxH'_eq, ← map_mul, hx2, map_one, one_mul]
  refine (QuotientGroup.eq_one_iff _).mp ?_
  rw [← QuotientGroup.mk'_apply, map_mul, hz, ← map_mul, hy2, map_one]

private theorem orderOf_mul_eq_four_of_dvd_two_pow {x y t : G} (hD : IsOddTransp D)
    (hN : IsNormalSet D) (htri : IsTriangle D x y t) {k : ℕ}
    (hdvd : orderOf (x * t * y) ∣ 2 ^ k) :
    orderOf (x * t * y) = 4 := by
  rcases IsTriangle.orderOf_cases hD hN htri with hfirst | hfour | hthird
  · exfalso
    obtain ⟨hodd, hgt⟩ := hfirst
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hone : orderOf (x * t * y) = 1 := by
      refine Nat.Coprime.eq_one_of_dvd ((Odd.coprime_two_right hodd).pow_right m) ?_
      rw [hm]
    omega
  · exact hfour
  · exfalso
    obtain ⟨n, hn, hn1, hord⟩ := hthird
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hdvdn : n ∣ 2 ^ m := ⟨2, by rw [← hm, hord]; ring⟩
    have hn1' : n = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Odd.coprime_two_right hn).pow_right m) hdvdn
    omega

private theorem orderOf_mul_eq_four_of_mem_DalphaStar (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha)
    (hcon : ∀ γ, γ ∈ Dalpha D hC.alpha → γ ∈ Dalpha D β →
      γ ∈ blockLine D hC.alpha β)
    {x y t : G} (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha)
    (ht : t ∈ DalphaStar D hC.alpha) (htri : IsTriangle D x y t) :
    orderOf (x * t * y) = 4 := by
  have hxt : Commute x t := htri.2.2.2.2.1
  have hxne : x ≠ t := htri.2.2.2.1
  obtain ⟨βx, hβx, hxβx⟩ := hx
  obtain ⟨βt, hβt, htβt⟩ := ht
  have hxstar : x ∈ DalphaStar D hC.alpha := ⟨βx, hβx, hxβx⟩
  have htstar : t ∈ DalphaStar D hC.alpha := ⟨βt, hβt, htβt⟩
  have hβne : βx ≠ βt := by
    intro heq
    exact h.not_commute_of_mem_block hβt (heq ▸ hxβx) htβt hxne hxt
  have hβtDβx : βt ∈ Dalpha D βx := by
    rcases mem_perp_iff.mp (mem_perp_of_commute hC hβx.1 hβt.1 hxβx htβt hxt) with h | h
    · exact h
    · exact absurd h.symm hβne
  have hβtline : βt ∈ blockLine D hC.alpha βx :=
    mem_blockLine_of_mem_Dalpha_of_mem_Dalpha h hβ hcon hβx hβt hβtDβx
  have hβtmem : βt ∈ insert hC.alpha ((fun q => cimg q βx) ''
      ((CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G)) := by
    rw [← h.blockLine_eq hβx]
    exact hβtline
  obtain ⟨r, hr, hrβ⟩ : ∃ r ∈ CFSG.pCore 2 (Halpha D hC.alpha),
      cimg (r : G) βx = βt := by
    rcases Set.mem_insert_iff.mp hβtmem with heq | hmem
    · exact absurd heq hβt.2.2.1
    · obtain ⟨g, hgmem, hgimg⟩ := hmem
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hgmem
      exact ⟨r, hr, hgimg⟩
  have ht_in : t ∈ cimg (r : G) βx := by rw [hrβ]; exact htβt
  obtain ⟨x', hx'βx, hx'eq⟩ := ht_in
  have ht_eq : t = (r : G) * x' * (r : G)⁻¹ := hx'eq.symm
  have hzsq := sq_mem_pCore_of_mem_DalphaStar_triangle h hβx hxβx hxstar hy htstar
    htri hr hx'βx ht_eq
  obtain ⟨k, hdvd⟩ := orderOf_dvd_two_pow_of_sq_mem_pCore hzsq
  have hdvdG : orderOf (x * t * y) ∣ 2 ^ k := by
    rw [show x * t * y = ((⟨x, Subgroup.subset_closure hxstar⟩ *
      ⟨t, Subgroup.subset_closure htstar⟩ * ⟨y, Subgroup.subset_closure hy⟩ :
        Halpha D hC.alpha) : G) from rfl, Subgroup.orderOf_coe]
    exact hdvd
  exact orderOf_mul_eq_four_of_dvd_two_pow hC.setup.oddT hC.setup.normal htri hdvdG

theorem exists_mem_Dalpha_not_mem_blockLine (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ γ ∈ Dalpha D hC.alpha, γ ∈ Dalpha D β ∧ γ ∉ blockLine D hC.alpha β := by
  by_contra hcon
  push Not at hcon
  exact h.not_localSecond
    (localSecond_of_DalphaStar_triangles hC fun x hx y hy t ht htri =>
      orderOf_mul_eq_four_of_mem_DalphaStar h hβ hcon hx hy ht htri)

private theorem mul_not_mem_pCore_of_not_mem_blockLine (h : MainHyp hC) {δ₀ θ : Set G}
    (hδ₀ : δ₀ ∈ Dalpha D hC.alpha) (hθ : θ ∈ Dalpha D hC.alpha)
    (hθδ₀ : θ ∈ Dalpha D δ₀) (hθline : θ ∉ blockLine D hC.alpha δ₀)
    {c v : Halpha D hC.alpha} (hcθ : (c : G) ∈ θ) (hvδ₀ : (v : G) ∈ δ₀)
    (hcv : Commute (c : G) (v : G)) : c * v ∉ CFSG.pCore 2 (Halpha D hC.alpha) := by
  intro hq
  have hvv : (v : G) * (v : G) = 1 := hC.setup.oddT.mul_self_eq_one (hδ₀.2.1 hvδ₀)
  have hwq : (c : G) = ((c * v : Halpha D hC.alpha) : G) * (v : G) := by
    change (c : G) = (c : G) * (v : G) * (v : G)
    rw [mul_assoc, hvv, mul_one]
  obtain ⟨r, hrQ, hrconj⟩ :=
    h.exists_pCore_conj_eq (subset_DalphaStar hδ₀ hvδ₀) (hθ.2.1 hcθ) hq hwq
  have hrδ₀ : cimg (r : G) δ₀ ∈ blockClass hC.alpha := by
    have h1 : cimg (r : G) δ₀ ∈ blockClass (cimg (r : G) δ₀) := mem_blockClass_self _
    rwa [blockClass_cimg, blockClass_eq_of_mem hδ₀.1] at h1
  have hcimg : (c : G) ∈ cimg (r : G) δ₀ := by
    rw [← hrconj]
    exact ⟨(v : G), hvδ₀, rfl⟩
  have heq : θ = cimg (r : G) δ₀ :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha hθ.1 hrδ₀ ⟨(c : G), hcθ, hcimg⟩
  apply hθline
  rw [heq, h.blockLine_eq hδ₀]
  refine Set.mem_insert_of_mem _ ⟨(r : G), ?_, rfl⟩
  exact ⟨r, hrQ, rfl⟩

theorem cimg_twoOddCore_mem_Dalpha (h : MainHyp hC) {δ₀ θ : Set G}
    (hδ₀ : δ₀ ∈ Dalpha D hC.alpha) (hθ : θ ∈ Dalpha D hC.alpha)
    (hθδ₀ : θ ∈ Dalpha D δ₀) (hθline : θ ∉ blockLine D hC.alpha δ₀)
    {v : G} (hv : v ∈ δ₀) {k : Halpha D hC.alpha}
    (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (hnc : ¬ Commute v ((k : G) * v * (k : G)⁻¹)) :
    cimg (k : G) δ₀ ∈ Dalpha D θ := by
  obtain ⟨s, hs⟩ := mem_blockClass_iff.mp hθ.1
  have hcθ : s * hC.d * s⁻¹ ∈ θ := by
    rw [hs]
    exact ⟨hC.d, hC.d_mem_alpha, rfl⟩
  have hcD : s * hC.d * s⁻¹ ∈ D := hθ.2.1 hcθ
  have hcv : Commute (s * hC.d * s⁻¹) v := (hθδ₀.2.2.2 v hv (s * hC.d * s⁻¹) hcθ).symm
  set cH : Halpha D hC.alpha :=
    ⟨s * hC.d * s⁻¹, Subgroup.subset_closure (subset_DalphaStar hθ hcθ)⟩
  set vH : Halpha D hC.alpha := ⟨v, Subgroup.subset_closure (subset_DalphaStar hδ₀ hv)⟩
  have hQ : cH * vH ∉ CFSG.pCore 2 (Halpha D hC.alpha) :=
    mul_not_mem_pCore_of_not_mem_blockLine h hδ₀ hθ hθδ₀ hθline hcθ hv
      (by simpa only [cH, vH] using hcv)
  have hcommk : Commute (s * hC.d * s⁻¹) ((k : G) * v * (k : G)⁻¹) :=
    commute_conj_of_mul_not_mem_pCore hC (by simpa only [cH] using hcD)
      (by simpa only [vH] using hδ₀.2.1 hv) (by simpa only [cH, vH] using hcv) hQ hk
  have hkv : (k : G) * v * (k : G)⁻¹ ∈ cimg (k : G) δ₀ := ⟨v, hv, rfl⟩
  have hkδ₀ : cimg (k : G) δ₀ ∈ blockClass hC.alpha := by
    have h1 : cimg (k : G) δ₀ ∈ blockClass (cimg (k : G) δ₀) := mem_blockClass_self _
    rwa [blockClass_cimg, blockClass_eq_of_mem hδ₀.1] at h1
  have hperp : cimg (k : G) δ₀ ∈ perp D θ :=
    mem_perp_of_commute hC hθ.1 hkδ₀ hcθ hkv hcommk
  have hne : cimg (k : G) δ₀ ≠ θ := by
    intro heq
    exact hnc (hθδ₀.2.2.2 v hv ((k : G) * v * (k : G)⁻¹) (heq ▸ hkv))
  rcases mem_perp_iff.mp hperp with h | h
  · exact h
  · exact absurd h hne

private theorem blockLine_pair_transport_data (h : MainHyp hC) {β α₁ γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hα₁ : α₁ ∈ blockLine D hC.alpha β)
    (hα₁α : α₁ ≠ hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha) (hγβ : γ ∈ Dalpha D β)
    (hγline : γ ∉ blockLine D hC.alpha β) :
    (α₁ ∈ Dalpha D γ ∧ β ∈ Dalpha D γ ∧ hC.alpha ∈ Dalpha D γ) ∧
      (β ∉ blockLine D hC.alpha γ ∧ α₁ ∉ blockLine D hC.alpha γ) := by
  have hα₁Dα : α₁ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hα₁ hα₁α
  have hα₁perpγ : α₁ ∈ perp D γ :=
    hα₁.2 γ ⟨mem_perp_iff.mpr (Or.inl hγ), mem_perp_iff.mpr (Or.inl hγβ)⟩
  have hγα₁ : γ ≠ α₁ := fun heq => hγline (heq ▸ hα₁)
  have hα₁Dγ : α₁ ∈ Dalpha D γ := by
    rcases mem_perp_iff.mp hα₁perpγ with h | h
    · exact h
    · exact absurd h.symm hγα₁
  have hβperpγ : β ∈ perp D γ :=
    mem_perp_symm (mem_perp_iff.mpr (Or.inl hγβ)) hβ.2.1
  have hβγ : β ≠ γ := fun heq => hγline (heq ▸ right_mem_blockLine hβ.1 hβ.2.1)
  have hβDγ : β ∈ Dalpha D γ := by
    rcases mem_perp_iff.mp hβperpγ with h | h
    · exact h
    · exact absurd h hβγ
  have hαperpγ : hC.alpha ∈ perp D γ :=
    mem_perp_symm (mem_perp_iff.mpr (Or.inl hγ)) hC.isBlock_alpha.subset
  have hαγ : hC.alpha ≠ γ :=
    fun heq => hγline (heq ▸ left_mem_blockLine hC.isBlock_alpha.subset)
  have hαDγ : hC.alpha ∈ Dalpha D γ := by
    rcases mem_perp_iff.mp hαperpγ with h | h
    · exact h
    · exact absurd h hαγ
  have hβnot : β ∉ blockLine D hC.alpha γ := by
    intro hmem
    have heq : blockLine D hC.alpha β = blockLine D hC.alpha γ :=
      blockLine_eq_of_mem hC hγ hβ hmem
    exact hγline (by rw [heq]; exact right_mem_blockLine hγ.1 hγ.2.1)
  have hα₁not : α₁ ∉ blockLine D hC.alpha γ := by
    intro hmem
    have h1 : blockLine D hC.alpha α₁ = blockLine D hC.alpha γ :=
      blockLine_eq_of_mem hC hγ hα₁Dα hmem
    have h2 : blockLine D hC.alpha α₁ = blockLine D hC.alpha β :=
      blockLine_eq_of_mem hC hβ hα₁Dα hα₁
    exact hγline ((h1.symm.trans h2) ▸ right_mem_blockLine hγ.1 hγ.2.1)
  exact ⟨⟨hα₁Dγ, hβDγ, hαDγ⟩, hβnot, hα₁not⟩

private theorem cimg_not_mem_blockLine {β α₁ γ δ₀ θ₁ θ₂ : Set G} {g : G}
    (hγ : γ ∈ Dalpha D hC.alpha) (hgc : cimg g γ = hC.alpha)
    (hδ₀def : δ₀ = cimg g hC.alpha) (hθ₁def : θ₁ = cimg g β)
    (hθ₂def : θ₂ = cimg g α₁) (hβnot : β ∉ blockLine D hC.alpha γ)
    (hα₁not : α₁ ∉ blockLine D hC.alpha γ) :
    θ₁ ∉ blockLine D hC.alpha δ₀ ∧ θ₂ ∉ blockLine D hC.alpha δ₀ := by
  have hcomm : blockLine D γ hC.alpha = blockLine D hC.alpha γ :=
    blockLine_comm hγ.1
  have htransport : ∀ {ω θ : Set G}, θ = cimg g ω → ω ∉ blockLine D hC.alpha γ →
      θ ∉ blockLine D hC.alpha δ₀ := by
    intro ω θ hθdef hωnot hmem
    have hm : ω ∈ blockLine D γ hC.alpha := by
      have h := (cimg_mem_blockLine_iff hC.setup.normal g⁻¹ hC.alpha δ₀ θ).mpr hmem
      rw [show cimg g⁻¹ hC.alpha = γ from by rw [← hgc, cimg_inv_cimg],
        show cimg g⁻¹ δ₀ = hC.alpha from by rw [hδ₀def, cimg_inv_cimg]] at h
      rwa [hθdef, cimg_inv_cimg] at h
    exact hωnot (hcomm ▸ hm)
  exact ⟨htransport hθ₁def hβnot, htransport hθ₂def hα₁not⟩

private theorem exists_perp_perp_not_perp_of_conj (h : MainHyp hC) {β α₁ δ₀ θ₁ θ₂ : Set G}
    {g : G} (hδ₀ : δ₀ ∈ Dalpha D hC.alpha) (hθ₁ : θ₁ ∈ Dalpha D hC.alpha)
    (hθ₂ : θ₂ ∈ Dalpha D hC.alpha) (hθ₁δ₀ : θ₁ ∈ Dalpha D δ₀)
    (hθ₂δ₀ : θ₂ ∈ Dalpha D δ₀) (hθ₁line : θ₁ ∉ blockLine D hC.alpha δ₀)
    (hθ₂line : θ₂ ∉ blockLine D hC.alpha δ₀) (hδ₀def : δ₀ = cimg g hC.alpha)
    (hθ₁def : θ₁ = cimg g β) (hθ₂def : θ₂ = cimg g α₁) :
    ∃ δ : Set G, δ ∈ perp D β ∩ perp D α₁ ∧ δ ∉ perp D hC.alpha := by
  have hvδ₀ : g * hC.d * g⁻¹ ∈ δ₀ := by
    rw [hδ₀def]
    exact ⟨hC.d, hC.d_mem_alpha, rfl⟩
  obtain ⟨k, hk, hnc, hvk⟩ := h.exists_conj_not_commute hδ₀ hvδ₀
  have hδ'₁ : cimg (k : G) δ₀ ∈ Dalpha D θ₁ :=
    cimg_twoOddCore_mem_Dalpha h hδ₀ hθ₁ hθ₁δ₀ hθ₁line hvδ₀ hk hnc
  have hδ'₂ : cimg (k : G) δ₀ ∈ Dalpha D θ₂ :=
    cimg_twoOddCore_mem_Dalpha h hδ₀ hθ₂ hθ₂δ₀ hθ₂line hvδ₀ hk hnc
  have hδ'not : cimg (k : G) δ₀ ∉ perp D δ₀ := by
    intro hperp
    have hvk' : (k : G) * (g * hC.d * g⁻¹) * (k : G)⁻¹ ∈ cimg (k : G) δ₀ :=
      ⟨g * hC.d * g⁻¹, hvδ₀, rfl⟩
    rcases mem_perp_iff.mp hperp with h | h
    · exact hnc (h.2.2.2 (g * hC.d * g⁻¹) hvδ₀ _ hvk')
    · exact hvk (h ▸ hvk')
  refine ⟨cimg g⁻¹ (cimg (k : G) δ₀), ⟨?_, ?_⟩, ?_⟩
  · have h := (perp_cimg_mem hC.setup.normal g⁻¹ (α := θ₁) (γ := cimg (k : G) δ₀)).mpr
      (mem_perp_iff.mpr (Or.inl hδ'₁))
    rwa [show cimg g⁻¹ θ₁ = β from by rw [hθ₁def, cimg_inv_cimg]] at h
  · have h := (perp_cimg_mem hC.setup.normal g⁻¹ (α := θ₂) (γ := cimg (k : G) δ₀)).mpr
      (mem_perp_iff.mpr (Or.inl hδ'₂))
    rwa [show cimg g⁻¹ θ₂ = α₁ from by rw [hθ₂def, cimg_inv_cimg]] at h
  · intro hmem
    have h := (perp_cimg_mem hC.setup.normal g (α := hC.alpha)
      (γ := cimg g⁻¹ (cimg (k : G) δ₀))).mpr hmem
    rw [cimg_cimg_inv] at h
    exact hδ'not (by rwa [← hδ₀def] at h)

private theorem exists_perp_perp_not_perp (h : MainHyp hC) {β α₁ γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hα₁ : α₁ ∈ blockLine D hC.alpha β)
    (hα₁α : α₁ ≠ hC.alpha) (hα₁β : α₁ ≠ β) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∈ Dalpha D β) (hγline : γ ∉ blockLine D hC.alpha β) :
    ∃ δ : Set G, δ ∈ perp D β ∩ perp D α₁ ∧ δ ∉ perp D hC.alpha := by
  obtain ⟨⟨hα₁Dγ, hβDγ, hαDγ⟩, hβnot, hα₁not⟩ :=
    blockLine_pair_transport_data h hβ hα₁ hα₁α hγ hγβ hγline
  have hα₁Dα : α₁ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hα₁ hα₁α
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp (mem_blockClass_comm.mpr hγ.1)
  have hgc : cimg g γ = hC.alpha := hg.symm
  set δ₀ : Set G := cimg g hC.alpha with hδ₀def
  set θ₁ : Set G := cimg g β with hθ₁def
  set θ₂ : Set G := cimg g α₁ with hθ₂def
  have hδ₀ : δ₀ ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hαDγ g
    rw [← hgc]
    exact h
  have hθ₁ : θ₁ ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hβDγ g
    rw [← hgc]
    exact h
  have hθ₂ : θ₂ ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hα₁Dγ g
    rw [← hgc]
    exact h
  have hθ₁δ₀ : θ₁ ∈ Dalpha D δ₀ := Dalpha.conj hC.setup.normal hβ g
  have hθ₂δ₀ : θ₂ ∈ Dalpha D δ₀ := Dalpha.conj hC.setup.normal hα₁Dα g
  obtain ⟨hθ₁line, hθ₂line⟩ :=
    cimg_not_mem_blockLine hγ hgc hδ₀def hθ₁def hθ₂def hβnot hα₁not
  exact exists_perp_perp_not_perp_of_conj h hδ₀ hθ₁ hθ₂ hθ₁δ₀ hθ₂δ₀ hθ₁line hθ₂line
    hδ₀def hθ₁def hθ₂def

theorem blockLine_eq_pair (h : MainHyp hC) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    blockLine D hC.alpha β = {hC.alpha, β} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro α₁ hα₁
    by_cases hα₁α : α₁ = hC.alpha
    · simp [hα₁α]
    by_cases hα₁β : α₁ = β
    · simp [hα₁β]
    exfalso
    obtain ⟨γ, hγ, hγβ, hγline⟩ := h.exists_mem_Dalpha_not_mem_blockLine hβ
    obtain ⟨δ, hδ, hδnot⟩ := exists_perp_perp_not_perp h hβ hα₁ hα₁α hα₁β hγ hγβ hγline
    have hβmem : β ∈ blockLine D hC.alpha β := right_mem_blockLine hβ.1 hβ.2.1
    have hline : blockLine D β α₁ = blockLine D hC.alpha β :=
      blockLine_eq_of_mem_of_mem hC hβ hβmem hα₁ (Ne.symm hα₁β)
    have hαmem : hC.alpha ∈ blockLine D β α₁ := by
      rw [hline]
      exact left_mem_blockLine hC.isBlock_alpha.subset
    have hαperp : hC.alpha ∈ perp D δ := hαmem.2 δ hδ
    have hδD : δ ⊆ D := by
      rcases mem_perp_iff.mp hδ.1 with h | h
      · exact h.2.1
      · rw [h]; exact hβ.2.1
    exact hδnot (mem_perp_symm hαperp hδD)
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact left_mem_blockLine hC.isBlock_alpha.subset
    · exact right_mem_blockLine hβ.1 hβ.2.1

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
