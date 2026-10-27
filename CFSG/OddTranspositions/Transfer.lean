module

public import CFSG.RankThree.GF2n.Tim79aSec23NoSq

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld

variable {Y : Type} [Group Y] [Finite Y] {D : Set Y}

theorem image_center_quotient_eq_bot
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  have hsolvZ : Group.IsSolvable (Subgroup.center (Y ⧸ Subgroup.center Y)) :=
    Group.isSolvable_of_comm fun a b =>
      Subtype.ext ((Subgroup.mem_center_iff.mp a.2 b).symm)
  exact solvable_normal_eq_bot_quotient_center hsolv
    (Subgroup.center (Y ⧸ Subgroup.center Y)) hsolvZ

theorem noSqE1_of_center_quotient
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g})
    (hroot : IsRootInvolutionSet D)
    (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4)
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    (hE1 : CFSG.RankThree.GF2n.Tim79a.NoSqE1
      (QuotientGroup.mk' (Subgroup.center Y) '' D)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  classical
  set Z := Subgroup.center Y with hZ
  set π := QuotientGroup.mk' Z with hπ
  have hcenter : Subgroup.center (Y ⧸ Z) = ⊥ := image_center_quotient_eq_bot hsolv
  intro d hd
  set C := CFSG.RankThree.GF2n.Tim79a.cenGen D d with hC
  have hmapC : C.map π = CFSG.RankThree.GF2n.Tim79a.cenGen (π '' D) (π d) := by
    rw [hC, CFSG.RankThree.GF2n.Tim79a.cenGen, CFSG.RankThree.GF2n.Tim79a.cenGen,
      MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      change π x ∈ Subgroup.centralizer ({π d} : Set (Y ⧸ Z))
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxd]
    · rintro ⟨⟨e, heD, rfl⟩, heC⟩
      have heC' : π e * π d = π d * π e :=
        Subgroup.mem_centralizer_singleton_iff.mp heC
      have hd2 : d * d = 1 := by
        rw [← sq, ← hroot.1 d hd]; exact pow_orderOf_eq_one d
      have he2 : e * e = 1 := by
        rw [← sq, ← hroot.1 e heD]; exact pow_orderOf_eq_one e
      have hπd2 : π d * π d = 1 := by rw [← map_mul, hd2, map_one]
      have hπe2 : π e * π e = 1 := by rw [← map_mul, he2, map_one]
      have hsq : π ((d * e) ^ 2) = 1 := by
        rw [sq, map_mul]
        calc (π d * π e) * (π d * π e)
            = π d * (π e * π d) * π e := by group
          _ = π d * (π d * π e) * π e := by rw [← heC']
          _ = (π d * π d) * (π e * π e) := by group
          _ = 1 := by rw [hπd2, hπe2, one_mul]
      rcases hroot.2.1 d hd e heD with h2 | h4 | hodd
      ·
        have h1 : (d * e) * (d * e) = 1 := by
          rw [← sq, ← h2]; exact pow_orderOf_eq_one _
        have hcomm : d * e = e * d := by
          calc d * e = (d * e)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
            _ = e⁻¹ * d⁻¹ := mul_inv_rev _ _
            _ = e * d := by
              rw [inv_eq_of_mul_eq_one_right he2, inv_eq_of_mul_eq_one_right hd2]
        exact ⟨e, ⟨heD, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩, rfl⟩
      · exact absurd h4 (hdeg d hd e heD)
      ·
        obtain ⟨k, hk⟩ := hodd
        have hpow : (d * e) ^ (2 * (k + 1)) = d * e := by
          calc (d * e) ^ (2 * (k + 1)) = (d * e) ^ (orderOf (d * e) + 1) := by
                rw [hk]; ring_nf
            _ = d * e := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
        have hone : π (d * e) = 1 := by
          rw [← hpow, pow_mul, map_pow, hsq, one_pow]
        have hπde : π d * π e = 1 := by rw [← map_mul, hone]
        have hπeq : π e = π d := by
          calc π e = (π d)⁻¹ := (inv_eq_of_mul_eq_one_right hπde).symm
            _ = π d := by rw [← map_inv, inv_eq_of_mul_eq_one_right hd2]
        exact ⟨d, ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, hπeq.symm⟩
  set B : Subgroup (Y ⧸ Z) := (inSubgroup (pCore 2) C).map π with hB
  have hB2 : IsPGroup 2 B := by
    rw [hB]
    exact IsPGroup.map (CFSG.RankThree.GF2n.inSubgroup_pCore_two C).1 π
  have hBle : B ≤ C.map π := by
    rw [hB]
    exact Subgroup.map_mono (f := π) (CFSG.RankThree.GF2n.inSubgroup_pCore_two C).2.1
  have hconj : ∀ m ∈ C.map π, ∀ p ∈ inSubgroup (pCore 2) C,
      m * π p * m⁻¹ ∈ B := by
    rintro m hm p hp
    obtain ⟨c, hc, rfl⟩ := hm
    rw [hB, Subgroup.mem_map]
    rw [inSubgroup] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    refine ⟨c * p * c⁻¹, ?_, ?_⟩
    · rw [← hqp, inSubgroup]
      exact ⟨⟨c, hc⟩ * q * ⟨c, hc⟩⁻¹,
        (pCore_normal (G := C) (p := 2)).conj_mem q hq ⟨c, hc⟩, rfl⟩
    · rw [map_mul, map_mul, map_inv]
  have hBnorm : C.map π ≤ Subgroup.normalizer (B : Set (Y ⧸ Z)) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hB, Subgroup.mem_map] at hy
      obtain ⟨q, hq, hqy⟩ := hy
      have h := hconj m hm q hq
      rwa [hqy] at h
    · intro hy
      rw [hB, Subgroup.mem_map] at hy
      obtain ⟨q, hq, hqy⟩ := hy
      have hm' : m⁻¹ ∈ C.map π := Subgroup.inv_mem _ hm
      have h := hconj m⁻¹ hm' q hq
      rw [inv_inv, hqy] at h
      have hy' : m⁻¹ * (m * y * m⁻¹) * m = y := by group
      rwa [hy'] at h
  have hBp : B ≤ inSubgroup (pCore 2) (C.map π) :=
    CFSG.RankThree.GF2n.Tim78.le_inSubgroup_pCore (M := C.map π) (B := B)
      hBle hBnorm hB2
  have hBp' : B ≤ inSubgroup (pCore 2)
      (CFSG.RankThree.GF2n.Tim79a.cenGen (π '' D) (π d)) := by
    simpa [← hmapC] using hBp
  have hE1d := hE1 (π d) ⟨d, hd, rfl⟩
  intro x hx
  have hπx : π x ∈ B := Subgroup.mem_map_of_mem π hx
  have hxE := hE1d (hBp' hπx)
  rw [hcenter, sup_bot_eq] at hxE
  have hπd2 : π d * π d = 1 := by
    have hd2 : d * d = 1 := by
      rw [← sq, ← hroot.1 d hd]; exact pow_orderOf_eq_one d
    rw [← map_mul, hd2, map_one]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxE
  have hpow2 : (π d) ^ (2 : ℤ) = 1 := by rw [zpow_two, hπd2]
  have hred : (π d) ^ n = (π d) ^ (n % 2) := zpow_eq_zpow_emod n hpow2
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  ·
    have hx1 : π x = 1 := by rw [← hn, hred, h0, zpow_zero]
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).1 hx1
    exact Subgroup.mem_sup_right hxZ
  ·
    have hx1 : π x = π d := by rw [← hn, hred, h1, zpow_one]
    have hxZ : d⁻¹ * x ∈ Z := by
      rw [← QuotientGroup.eq_one_iff (d⁻¹ * x)]
      change π (d⁻¹ * x) = 1
      rw [map_mul, map_inv, hx1, inv_mul_cancel]
    have hxd : x = d * (d⁻¹ * x) := by group
    rw [hxd]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
      (Subgroup.mem_sup_right hxZ)

end CFSG.OddTranspositions
