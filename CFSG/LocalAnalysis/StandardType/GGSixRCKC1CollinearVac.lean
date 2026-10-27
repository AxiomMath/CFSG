module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearDefs
public import CFSG.LieType.HighestRoot.ModelCenter

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.ComponentClassification.RankTwoOddLie (CenterPPrime)

theorem rckCollinearVia_of_noFour {M : LieUniversal} {β : Fin M.D.rank → ℤ}
    (hZ : CenterPPrime M.K 2) (C : Set M.K)
    (hconj : ∀ x ∈ C, ∀ g : M.K, g * x * g⁻¹ ∈ C) (hinv : ∀ x ∈ C, x * x = 1)
    (hX : ∀ x ∈ M.D.rootGroup β, x ≠ 1 → x ∈ C)
    (hprod : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x * y = y * x → x * y ∉ C) :
    RCKCollinearVia M β := by
  classical
  intro X _ _ K R V hR _hR2 r hr hr1 hrV _hVK hV hV4 hconjV
  obtain ⟨φ, hφrange, hφker, u, hRu⟩ := hR
  have hr' : r ∈ ggRootSub M.D φ β u := by rw [← hRu]; exact hr
  rw [ggRootSub, Subgroup.mem_map] at hr'
  obtain ⟨xh, hxh, hxhr⟩ := hr'
  rw [Subgroup.mem_map] at hxh
  obtain ⟨x, hxmem, hxeq⟩ := hxh
  change MulAut.conj u x = xh at hxeq
  rw [MulAut.conj_apply] at hxeq
  let rt : M.K := u * x * u⁻¹
  have hφrt : φ rt = r := by
    change φ (u * x * u⁻¹) = r
    rw [hxeq]
    exact hxhr
  have hxne : x ≠ 1 := by
    intro hx1
    have h1 : φ rt = 1 := by
      change φ (u * x * u⁻¹) = 1
      rw [hx1]
      simp
    rw [h1] at hφrt
    exact hr1 hφrt.symm
  have hrtC : rt ∈ C := by
    change u * x * u⁻¹ ∈ C
    exact hconj x (hX x hxmem hxne) u
  have h1r : (⟨(1 : X), V.one_mem⟩ : V) ≠ ⟨r, hrV⟩ := by
    intro h
    have h' : (1 : X) = r := congrArg Subtype.val h
    exact hr1 h'.symm
  obtain ⟨s, -, hs⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({⟨(1 : X), V.one_mem⟩, ⟨r, hrV⟩} : Set V)) (t := Set.univ) (by
      rw [Set.ncard_pair h1r, Set.ncard_univ, hV4]
      norm_num)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  have hsV : (s : X) ∈ V := s.2
  have hs1 : (s : X) ≠ 1 := fun h => hs.1 (Subtype.ext h)
  have hsr : (s : X) ≠ r := fun h => hs.2 (Subtype.ext h)
  obtain ⟨k, hkK, hsk⟩ := hconjV (s : X) hsV hs1
  rw [← hφrange] at hkK
  obtain ⟨kt, hkt⟩ := hkK
  let st : M.K := kt * rt * kt⁻¹
  have hstC : st ∈ C := by
    change kt * rt * kt⁻¹ ∈ C
    exact hconj rt hrtC kt
  have hφst : φ st = (s : X) := by
    have h1 : φ st = k * r * k⁻¹ := by
      change φ (kt * rt * kt⁻¹) = k * r * k⁻¹
      rw [map_mul, map_mul, map_inv, hkt, hφrt]
    rw [h1, ← hsk]
  have hr2 : r * r = 1 := by
    have h := hV.2 r hrV
    rwa [pow_two] at h
  have hs2 : (s : X) * (s : X) = 1 := by
    have h := hV.2 (s : X) hsV
    rwa [pow_two] at h
  have hcommV : r * (s : X) = (s : X) * r :=
    congrArg Subtype.val (hV.1.is_comm.comm ⟨r, hrV⟩ ⟨s, hsV⟩)
  have hrs2X : (r * (s : X)) * (r * (s : X)) = 1 := by
    calc (r * (s : X)) * (r * (s : X)) = ((s : X) * r) * (r * (s : X)) := by rw [hcommV]
      _ = ((s : X) * (r * r)) * (s : X) := by group
      _ = 1 := by rw [hr2, mul_one, hs2]
  have ht1 : r * (s : X) ≠ 1 := by
    intro h
    apply hsr
    calc (s : X) = 1 * (s : X) := (one_mul _).symm
      _ = (r * r) * (s : X) := by rw [hr2]
      _ = r * (r * (s : X)) := by group
      _ = r * 1 := by rw [h]
      _ = r := mul_one r
  obtain ⟨k', hk'K, htk⟩ := hconjV (r * (s : X)) (V.mul_mem hrV hsV) ht1
  rw [← hφrange] at hk'K
  obtain ⟨kt', hkt'⟩ := hk'K
  let tt : M.K := kt' * rt * kt'⁻¹
  have httC : tt ∈ C := by
    change kt' * rt * kt'⁻¹ ∈ C
    exact hconj rt hrtC kt'
  have hφtt : φ tt = r * (s : X) := by
    have h1 : φ tt = k' * r * k'⁻¹ := by
      change φ (kt' * rt * kt'⁻¹) = k' * r * k'⁻¹
      rw [map_mul, map_mul, map_inv, hkt', hφrt]
    rw [h1, ← htk]
  have hrt2 : rt * rt = 1 := hinv rt hrtC
  have hst2 : st * st = 1 := hinv st hstC
  have hrt_inv : rt⁻¹ = rt := inv_eq_of_mul_eq_one_right hrt2
  have hst_inv : st⁻¹ = st := inv_eq_of_mul_eq_one_right hst2
  let c : M.K := rt * st * rt⁻¹ * st⁻¹
  have hc_eq : c = rt * st * rt * st := by simp [c, hrt_inv, hst_inv]
  have hφc : φ c = 1 := by
    rw [hc_eq]
    simp only [map_mul, hφrt, hφst]
    calc r * (s : X) * r * (s : X) = (r * (s : X)) * (r * (s : X)) := by group
      _ = 1 := hrs2X
  have hc_ker : c ∈ φ.ker := MonoidHom.mem_ker.mpr hφc
  have hc_center : c ∈ Subgroup.center M.K := hφker hc_ker
  have hcrt : rt * c = c * rt := Subgroup.mem_center_iff.mp hc_center rt
  have hc_inv_eq : c = c⁻¹ := by
    have h1 : st * rt * st = rt * st * rt * st * rt := by
      have h := hcrt
      rw [hc_eq] at h
      calc st * rt * st = (rt * rt) * (st * rt * st) := by rw [hrt2, one_mul]
        _ = rt * (rt * st * rt * st) := by group
        _ = (rt * st * rt * st) * rt := h
        _ = rt * st * rt * st * rt := by group
    have h2 : c = st * rt * st * rt := by
      rw [hc_eq]
      calc rt * st * rt * st = (rt * st * rt * st) * (rt * rt) := by rw [hrt2, mul_one]
        _ = (rt * st * rt * st * rt) * rt := by group
        _ = (st * rt * st) * rt := by rw [← h1]
        _ = st * rt * st * rt := by group
    have h3 : c⁻¹ = st * rt * st * rt := by
      rw [hc_eq]
      calc (rt * st * rt * st)⁻¹ = st⁻¹ * (rt⁻¹ * (st⁻¹ * rt⁻¹)) := by group
        _ = st * rt * st * rt := by rw [hrt_inv, hst_inv]; group
    exact h2.trans h3.symm
  have hc2 : c * c = 1 := by
    nth_rewrite 2 [hc_inv_eq]
    exact mul_inv_cancel c
  have hc1 : c = 1 := hZ c hc_center (by rw [pow_two]; exact hc2)
  have hcomm_rs : rt * st = st * rt := by
    have hrs2 : (rt * st) * (rt * st) = 1 := by
      have h : rt * st * rt * st = 1 := by rw [← hc_eq]; exact hc1
      calc (rt * st) * (rt * st) = rt * st * rt * st := by group
        _ = 1 := h
    have hinv' : (rt * st)⁻¹ = rt * st := inv_eq_of_mul_eq_one_right hrs2
    rw [← hinv', mul_inv_rev, hrt_inv, hst_inv]
  have htt_inv : tt⁻¹ = tt := inv_eq_of_mul_eq_one_right (hinv tt httC)
  let d : M.K := rt * st * tt⁻¹
  have hd_eq : d = rt * st * tt := by simp [d, htt_inv]
  have hφd : φ d = 1 := by
    rw [hd_eq]
    simp only [map_mul, hφrt, hφst, hφtt]
    exact hrs2X
  have hd_ker : d ∈ φ.ker := MonoidHom.mem_ker.mpr hφd
  have hd_center : d ∈ Subgroup.center M.K := hφker hd_ker
  have htd : tt * d = d * tt := Subgroup.mem_center_iff.mp hd_center tt
  have h1 : tt * rt * st * tt = rt * st := by
    have h := htd
    rw [hd_eq] at h
    calc tt * rt * st * tt = tt * (rt * st * tt) := by group
      _ = (rt * st * tt) * tt := h
      _ = rt * st * (tt * tt) := by group
      _ = rt * st := by rw [hinv tt httC, mul_one]
  have hd2 : d * d = 1 := by
    rw [hd_eq]
    calc (rt * st * tt) * (rt * st * tt) = rt * st * (tt * rt * st * tt) := by group
      _ = rt * st * (rt * st) := by rw [h1]
      _ = 1 := by
        have hrs2 : (rt * st) * (rt * st) = 1 := by
          have h : rt * st * rt * st = 1 := by rw [← hc_eq]; exact hc1
          calc (rt * st) * (rt * st) = rt * st * rt * st := by group
            _ = 1 := h
        exact hrs2
  have hd1 : d = 1 := hZ d hd_center (by rw [pow_two]; exact hd2)
  have hrs_eq_t : rt * st = tt := by
    have h : rt * st * tt = 1 := by rw [← hd_eq]; exact hd1
    calc rt * st = rt * st * 1 := (mul_one _).symm
      _ = rt * st * (tt * tt) := by rw [hinv tt httC]
      _ = (rt * st * tt) * tt := by group
      _ = 1 * tt := by rw [h]
      _ = tt := one_mul tt
  have hne : rt ≠ st := by
    intro h
    apply hsr
    have h' : r = (s : X) := by rw [← hφrt, ← hφst, h]
    exact h'.symm
  have hmem : rt * st ∈ C := by rw [hrs_eq_t]; exact httC
  exact absurd hmem (hprod rt hrtC st hstC hne hcomm_rs)

end CFSG.StandardType.RCKC1
