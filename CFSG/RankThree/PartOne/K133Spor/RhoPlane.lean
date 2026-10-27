module

public import CFSG.RankThree.PartOne.K133Spor.GBarSound
public import CFSG.RankThree.PartOne.K133Spor.HNHom
public import Certificates.Certificate14999

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Sporadic.HNOddCore CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer
  CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem closure_permsA_eq_arrGen (n : ℕ) (gs : Array (Array ℕ)) :
    Subgroup.closure (permsA n gs) = arrGen n gs := by
  unfold arrGen permsA
  congr 1

theorem kappa_range_eq_arrGen :
    kappa.range = arrGen 256 colPerms := by
  rw [range_eq_closure kappa closure_rhoGenR]
  have e : Subgroup.closure (Set.range fun g => kappa (rhoGenR g)) =
      Subgroup.closure (Set.range fun g : Fin 11 => pk g) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show kappa (rhoGenR g) ∈ _
      rw [kappa_gen]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show pk g ∈ _
      rw [← inv_inv (pk g), ← kappa_gen]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨g, rfl⟩)
  have hO : ∀ k < colPerms.size, PRep 256 colPerms[k]! (pk k) := fun k hk =>
    prep_pk (by rw [← q_parts.2.2.2.1]; exact hk)
  have e2 : Subgroup.closure (Set.range fun g : Fin 11 => pk g) = arrGen 256 colPerms := by
    rw [arrGen_eq hO]
    congr 1
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, by rw [q_parts.2.2.2.1]; exact g.2⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨⟨k, by rw [← q_parts.2.2.2.1]; exact hk⟩, rfl⟩
  rw [e, e2]

theorem kappa_mem_closure
    (z : rho4.range) :
    kappa z ∈ Subgroup.closure (permsA 256 colPerms) := by
  rw [closure_permsA_eq_arrGen, ← kappa_range_eq_arrGen]
  exact ⟨z, rfl⟩

theorem mem_Qr_of_kappa_eq_one
    {z : rho4.range} (h : kappa z = 1) : z ∈ Qr := by
  rw [← ker_conj, MonoidHom.mem_ker]
  apply kappa_injective_aut
  rw [map_one]
  exact h

theorem orderOf_dvd_of_mem_Qr
    {z : rho4.range}
    (hz : z ∈ Qr) : orderOf z ∣ 256 := by
  have h := orderOf_dvd_natCard (⟨z, hz⟩ : Qr)
  rw [card_Qr, Subgroup.orderOf_mk] at h
  exact h

theorem kappa_fix
    (x : rho4.range) (m : Fin 256)
    (h : x * (qrEquiv m : rho4.range) = (qrEquiv m : rho4.range) * x) : kappa x m = m := by
  rw [kappa_apply]
  have e : MulAut.conjNormal (H := Qr) x (qrEquiv m) = qrEquiv m := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, h, mul_assoc, mul_inv_cancel, mul_one]
  rw [e, Equiv.symm_apply_apply]

theorem rho4_planeFree :
    PlaneFreeGroup rho4.range := by
  intro x y u hx hy hyx hxy hu hux huy
  have hG : GBarOK := Certificates.certificate14999
  have hG' : enumOK 256 colPerms gbarKeys gbarCert = true ∧ gbarCheck 256 gbarCert.pts = true := by
    simpa only [Bool.and_eq_true] using hG
  obtain ⟨henum, hcheck⟩ := hG'
  have hps : ∀ p ∈ gbarKeys, p < 256 := by
    intro p hp
    simp only [gbarKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  have x5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have y5 : y ^ 5 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have u2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have x1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have y1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    omega
  have u1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    omega
  have kx5 : kappa x ^ 5 = 1 := by rw [← map_pow, x5, map_one]
  have ky5 : kappa y ^ 5 = 1 := by rw [← map_pow, y5, map_one]
  have kx1 : kappa x ≠ 1 := fun h => by
    have := orderOf_dvd_of_mem_Qr (mem_Qr_of_kappa_eq_one h)
    rw [hx] at this
    omega
  have ky1 : kappa y ≠ 1 := fun h => by
    have := orderOf_dvd_of_mem_Qr (mem_Qr_of_kappa_eq_one h)
    rw [hy] at this
    omega
  have kxy : kappa x * kappa y = kappa y * kappa x := by
    rw [← map_mul, ← map_mul, hxy]
  have kyx : kappa y ∉ Subgroup.zpowers (kappa x) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hyx
    have hc : Commute y (x ^ (-k)) := (Commute.zpow_right (show Commute y x from hxy.symm) _)
    have hz5 : (y * x ^ (-k)) ^ 5 = 1 := by
      rw [hc.mul_pow, y5, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        x5, one_zpow]
    have hzk : kappa (y * x ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, zpow_neg, ← hk]
      exact mul_inv_cancel _
    have hdv := orderOf_dvd_of_mem_Qr (mem_Qr_of_kappa_eq_one hzk)
    have hd5 : orderOf (y * x ^ (-k)) ∣ 5 := orderOf_dvd_of_pow_eq_one hz5
    have hd1 : orderOf (y * x ^ (-k)) = 1 := by
      have h' := Nat.dvd_gcd hd5 hdv
      have : Nat.gcd 5 256 = 1 := by norm_num
      rw [this] at h'
      exact Nat.dvd_one.1 h'
    have hz1 : y * x ^ (-k) = 1 := orderOf_eq_one_iff.1 hd1
    have hy' : y = x ^ k := by
      have := mul_eq_one_iff_eq_inv.1 hz1
      rwa [zpow_neg, inv_inv] at this
    exact ⟨k, hy'.symm⟩
  by_cases hku : kappa u = 1
  ·
    have huQ : u ∈ Qr := mem_Qr_of_kappa_eq_one hku
    set m : Fin 256 := qrEquiv.symm ⟨u, huQ⟩ with hm
    have hqm : (qrEquiv m : rho4.range) = u := by
      rw [hm, Equiv.apply_symm_apply]
    have hm0 : (m : ℕ) ≠ 0 := by
      intro h0
      have hmz : m = ⟨0, by norm_num⟩ := Fin.ext h0
      have h1 : ((qrEquiv m : rho4.range) : Perm (Fin 800)) = 1 := by
        rw [qrEquiv_val, hmz]
        exact qb_zero
      rw [hqm] at h1
      exact u1 (Subtype.ext h1)
    have hxm : kappa x m = m := kappa_fix x m (by rw [hqm]; exact hux.symm)
    have hym : kappa y m = m := kappa_fix y m (by rw [hqm]; exact huy.symm)
    exact gbar_fixFree hps henum hcheck (kappa_mem_closure x) (kappa_mem_closure y) kx5 kx1 ky5 ky1
      kyx kxy m hm0 hxm hym
  · have ku2 : kappa u * kappa u = 1 := by
      rw [← map_mul, ← sq, u2, map_one]
    have kux : kappa u * kappa x = kappa x * kappa u := by
      rw [← map_mul, ← map_mul, hux]
    have kuy : kappa u * kappa y = kappa y * kappa u := by
      rw [← map_mul, ← map_mul, huy]
    exact gbar_invFree hps henum hcheck (kappa_mem_closure u) (kappa_mem_closure x)
      (kappa_mem_closure y) ku2 hku kx5 kx1 ky5 ky1 kyx kxy kux kuy

end CFSG.RankThree.PartOne.K133Spor
