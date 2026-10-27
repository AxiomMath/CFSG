module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private def w16gZP (P : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  (Subgroup.center ↥P).map P.subtype

private def w16gZ2 (P : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  (Subgroup.upperCentralSeries ↥P 2).map P.subtype

private theorem w16g_conj_inv_of_involution {A : Type*} [Group A] {t y : A}
    (ht : t * t = 1) : t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by
  have hφ : MulAut.conj t (MulAut.conj t y) = y := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    rw [MulAut.conj_apply, MulAut.conj_apply, htinv]
    calc t * (t * y * t) * t = t * t * y * (t * t) := by group
      _ = y := by simp [ht]
  calc t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹
      = MulAut.conj t (y⁻¹ * (t * y * t⁻¹)) := (MulAut.conj_apply t _).symm
    _ = MulAut.conj t (y⁻¹ * MulAut.conj t y) := by
          rw [show t * y * t⁻¹ = MulAut.conj t y from (MulAut.conj_apply t y).symm]
    _ = (MulAut.conj t y)⁻¹ * y := by rw [map_mul, map_inv, hφ]
    _ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by rw [mul_inv_rev, inv_inv, MulAut.conj_apply]

private theorem w16g_mem_z2_iff {P : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ P) :
    x ∈ w16gZ2 P ↔ ∀ y ∈ P, ⁅x, y⁆ ∈ w16gZP P := by
  constructor
  · intro h y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp h
    have hmem : ⁅x', (⟨y, hy⟩ : ↥P)⁆ ∈ Subgroup.center ↥P := by
      have h2 := Subgroup.mem_upperCentralSeries_succ_iff.mp hx' (⟨y, hy⟩ : ↥P)
      rwa [Subgroup.upperCentralSeries_one] at h2
    refine Subgroup.mem_map.mpr ⟨⁅x', (⟨y, hy⟩ : ↥P)⁆, hmem, ?_⟩
    simpa using map_commutatorElement (f := P.subtype) x' (⟨y, hy⟩ : ↥P)
  · intro h
    refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro g
    rw [Subgroup.upperCentralSeries_one]
    obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp (h g.1 g.2)
    have heq : ⁅(⟨x, hx⟩ : ↥P), g⁆ = c := by
      apply P.subtype_injective
      rw [map_commutatorElement]
      exact hc_eq.symm
    rw [heq]
    exact hc

private theorem w16g_center_of_mem_centerMap {P : Subgroup (MulAut W)} {z : MulAut W}
    (hz : z ∈ w16gZP P) : z ∈ P ∧ ∀ y ∈ P, y * z = z * y := by
  obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hz
  refine ⟨?_, ?_⟩
  · rw [← hc_eq]; exact c.2
  · intro y hy
    rw [← hc_eq]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨y, hy⟩ : ↥P))

private theorem w16g_exists_z2_not_center {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 7 t P) (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) :
    ∃ s ∈ w16gZ2 P, s ∉ w16gZP P := by
  haveI : Fact (Nat.Prime 7) := ⟨h.hp⟩
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent h.hP
  have hZne : Subgroup.upperCentralSeries ↥P 1 ≠ Subgroup.upperCentralSeries ↥P 2 := by
    intro heq
    have htop := Subgroup.upperCentralSeries.eq_top (G := ↥P) (a := 1) (b := 2)
      (by norm_num) heq
    rw [Subgroup.upperCentralSeries_one] at htop
    have hcomm := (Subgroup.center_eq_top_iff.mp htop).is_comm
    obtain ⟨x, hxP, y, hyP, hxy⟩ := hnab
    exact hxy (congrArg Subtype.val (hcomm.comm ⟨x, hxP⟩ ⟨y, hyP⟩))
  have hle : Subgroup.upperCentralSeries ↥P 1 ≤ Subgroup.upperCentralSeries ↥P 2 :=
    Subgroup.upperCentralSeries_mono (G := ↥P) (by norm_num)
  have hnotle : ¬ Subgroup.upperCentralSeries ↥P 2 ≤ Subgroup.upperCentralSeries ↥P 1 :=
    fun h2 => hZne (le_antisymm hle h2)
  obtain ⟨x, hx2, hx1⟩ := Set.not_subset.mp hnotle
  rw [Subgroup.upperCentralSeries_one] at hx1
  refine ⟨(x : MulAut W), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨x, hx2, rfl⟩
  · intro hxZ
    obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hxZ
    have hcx : c = x := P.subtype_injective hc_eq
    rw [hcx] at hc
    exact hx1 hc

private theorem w16g_z2_le_center_of_fixes {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 7 t P)
    (hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    (htS : ∀ s ∈ w16gZ2 P, t * s * t⁻¹ = s) :
    w16gZ2 P ≤ w16gZP P := by
  have hKS : ⁅Subgroup.zpowers t, w16gZ2 P⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcomm : Commute t s := by
      rw [commute_iff_eq]
      have hfix := htS s hs
      calc t * s = t * s * t⁻¹ * t := by group
        _ = s * t := by rw [hfix]
    exact (hcomm.zpow_left k).eq.symm
  have h1 : ⁅⁅Subgroup.zpowers t, w16gZ2 P⁆, P⁆ = ⊥ := by
    rw [hKS, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact bot_le
  have hSP : ⁅w16gZ2 P, P⁆ ≤ w16gZP P := by
    rw [Subgroup.commutator_le]
    intro s hs p hp
    have hsP : s ∈ P := Subgroup.map_subtype_le _ hs
    exact (w16g_mem_z2_iff hsP).mp hs p hp
  have hZPK : ⁅w16gZP P, Subgroup.zpowers t⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hzcentral : ∀ w ∈ P, w * (z' : MulAut W) = (z' : MulAut W) * w := by
      intro w hw
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' (⟨w, hw⟩ : ↥P))
    have htz := hcen (z' : MulAut W) z'.2 hzcentral
    have hcomm : Commute t (z' : MulAut W) := by
      rw [commute_iff_eq]
      calc t * (z' : MulAut W) = t * (z' : MulAut W) * t⁻¹ * t := by group
        _ = (z' : MulAut W) * t := by rw [htz]
    exact (hcomm.zpow_left k).eq
  have h2 : ⁅⁅w16gZ2 P, P⁆, Subgroup.zpowers t⁆ = ⊥ := by
    have hle' := Subgroup.commutator_mono hSP (le_refl (Subgroup.zpowers t))
    rw [hZPK] at hle'
    exact le_bot_iff.mp hle'
  have hPS : ⁅P, w16gZ2 P⁆ = ⊥ := by
    have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := P)
      (H₂ := Subgroup.zpowers t) (H₃ := w16gZ2 P) h1 h2
    rwa [h.hc] at hrot
  intro s hs
  have hsP : s ∈ P := Subgroup.map_subtype_le _ hs
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hPS
  refine Subgroup.mem_map.mpr ⟨⟨s, hsP⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact ((Subgroup.mem_centralizer_iff.mp (hPS g.2)) s hs).symm

private theorem w16g_conj_mem_z2 {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 7 t P)
    (hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    {s : MulAut W} (hs : s ∈ w16gZ2 P) : t * s * t⁻¹ ∈ w16gZ2 P := by
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h2
    exact h2
  have hsP : s ∈ P := Subgroup.map_subtype_le _ hs
  rw [w16g_mem_z2_iff (h.hn s hsP)]
  intro y hy
  have hy' : t⁻¹ * y * t ∈ P := by
    have h1 := h.hn y hy
    rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left htt] at h1 ⊢
    exact h1
  have hcy := (w16g_mem_z2_iff hsP).mp hs (t⁻¹ * y * t) hy'
  obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hcy
  have hc_central : ∀ w ∈ P, w * (c : MulAut W) = (c : MulAut W) * w := by
    intro w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨w, hw⟩ : ↥P))
  have htc : t * (c : MulAut W) * t⁻¹ = (c : MulAut W) := hcen c c.2 hc_central
  refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
  calc P.subtype c = t * P.subtype c * t⁻¹ := htc.symm
    _ = t * ⁅s, t⁻¹ * y * t⁆ * t⁻¹ := by rw [hc_eq]
    _ = ⁅t * s * t⁻¹, t * (t⁻¹ * y * t) * t⁻¹⁆ :=
          conjugate_commutatorElement (g₁ := s) (g₂ := t⁻¹ * y * t) (g₃ := t)
    _ = ⁅t * s * t⁻¹, y⁆ := by rw [show t * (t⁻¹ * y * t) * t⁻¹ = y by group]

private theorem w16g_exists_t_moves_z2 {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 7 t P) (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x)
    (hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) :
    ∃ s ∈ w16gZ2 P, t * s * t⁻¹ ≠ s := by
  by_contra hcon
  push Not at hcon
  have hle := w16g_z2_le_center_of_fixes h hcen hcon
  obtain ⟨u, huS, huZ⟩ := w16g_exists_z2_not_center h hnab
  exact huZ (hle huS)

theorem beta2_exists_heisenberg {t : MulAut W} {P : Subgroup (MulAut W)} (h : InvCfg131 7 t P)
    (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x)
    (hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) :
    ∃ x z y : MulAut W, x ∈ P ∧ z ∈ P ∧ y ∈ P ∧ orderOf x = 7 ∧ orderOf z = 7 ∧
      t * x * t⁻¹ = x⁻¹ ∧ t * z * t⁻¹ = z ∧ x * z = z * x ∧ y * x * y⁻¹ = x * z ∧
      y * z = z * y := by
  haveI : Fact (Nat.Prime 7) := ⟨h.hp⟩
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h2
    exact h2
  obtain ⟨s, hsS, hsmove⟩ := w16g_exists_t_moves_z2 h hnab hcen
  set x : MulAut W := s⁻¹ * (t * s * t⁻¹) with hxdef
  have hxS : x ∈ w16gZ2 P := by
    rw [hxdef]
    exact (w16gZ2 P).mul_mem ((w16gZ2 P).inv_mem hsS) (w16g_conj_mem_z2 h hcen hsS)
  have hxP : x ∈ P := Subgroup.map_subtype_le _ hxS
  have hxinv : t * x * t⁻¹ = x⁻¹ := by
    rw [hxdef]
    exact w16g_conj_inv_of_involution htt
  have hxne : x ≠ 1 := by
    intro h1
    apply hsmove
    rw [hxdef] at h1
    calc t * s * t⁻¹ = s * (s⁻¹ * (t * s * t⁻¹)) := by group
      _ = s * 1 := by rw [h1]
      _ = s := mul_one s
  have hxord : orderOf x = 7 := by
    rcases eq_one_or_orderOf_eq_prime_of_inverted h hxP hxinv with h1 | h1
    · exact absurd h1 hxne
    · exact h1
  have hxnotZ : x ∉ w16gZP P := by
    intro hxZ
    obtain ⟨c, hc, hc_eq⟩ := Subgroup.mem_map.mp hxZ
    have hcx : (c : MulAut W) = x := hc_eq
    have hcent : ∀ y ∈ P, y * x = x * y := by
      intro y hy
      rw [← hcx]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨y, hy⟩ : ↥P))
    have htz := hcen x hxP hcent
    have hx2 : x ^ 2 = 1 := by
      have hxinv2 : x = x⁻¹ := htz.symm.trans hxinv
      calc x ^ 2 = x * x := by rw [pow_two]
        _ = x * x⁻¹ := congrArg (fun w => x * w) hxinv2
        _ = 1 := mul_inv_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rw [hxord] at hdvd
    norm_num at hdvd
  have hnotcent : ¬ ∀ y ∈ P, y * x = x * y := by
    intro hcomm
    apply hxnotZ
    refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2)
  push Not at hnotcent
  obtain ⟨y, hyP, hyx⟩ := hnotcent
  set z : MulAut W := x⁻¹ * (y * x * y⁻¹) with hzdef
  have hzcomm : z = ⁅x⁻¹, y⁆ := by
    rw [hzdef, commutatorElement_def]
    group
  have hzZ : z ∈ w16gZP P := by
    rw [hzcomm]
    exact (w16g_mem_z2_iff (P.inv_mem hxP)).mp ((w16gZ2 P).inv_mem hxS) y hyP
  have hzP : z ∈ P := (w16g_center_of_mem_centerMap hzZ).1
  have hzcent : ∀ w ∈ P, w * z = z * w := (w16g_center_of_mem_centerMap hzZ).2
  have hz1 : z ≠ 1 := by
    intro h1
    apply hyx
    have h2 : y * x * y⁻¹ = x := by
      have h3 := congrArg (fun w => x * w) h1
      simp only [mul_one] at h3
      rw [hzdef] at h3
      rwa [mul_inv_cancel_left] at h3
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [h2]
  have hzpow : z ^ 7 = 1 := by
    rw [hzcomm]
    have hzmem : ⁅x⁻¹, y⁆ ∈ w16gZP P :=
      (w16g_mem_z2_iff (P.inv_mem hxP)).mp ((w16gZ2 P).inv_mem hxS) y hyP
    have hcomm : Commute x⁻¹ ⁅x⁻¹, y⁆ := by
      rw [commute_iff_eq]
      exact (w16g_center_of_mem_centerMap hzmem).2 x⁻¹ (P.inv_mem hxP)
    have h7 : (x⁻¹) ^ 7 = 1 := by
      rw [inv_pow, show x ^ 7 = 1 by rw [← hxord, pow_orderOf_eq_one], inv_one]
    calc ⁅x⁻¹, y⁆ ^ 7 = ⁅(x⁻¹) ^ 7, y⁆ := hcomm.commutatorElement_pow_left 7
      _ = ⁅(1 : MulAut W), y⁆ := by rw [h7]
      _ = 1 := commutatorElement_one_left y
  have hzord : orderOf z = 7 := orderOf_eq_prime hzpow hz1
  have htz : t * z * t⁻¹ = z := hcen z hzP hzcent
  have hxz : x * z = z * x := hzcent x hxP
  have hyz : y * z = z * y := hzcent y hyP
  have hyxeq : y * x * y⁻¹ = x * z := by
    rw [hzdef]
    group
  exact ⟨x, z, y, hxP, hzP, hyP, hxord, hzord, hxinv, htz, hxz, hyxeq, hyz⟩

end CFSG.LocalAnalysis.WeakClosure81
