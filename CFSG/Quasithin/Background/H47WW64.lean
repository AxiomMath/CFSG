module

public import CFSG.Quasithin.Background.H47WBase
public import Certificates.Certificate7258
public import CFSG.Quasithin.Vol2.Ch9L34Norm64

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H13.Ch9.L34N CFSG.Fischer

theorem card_Wn64 : Nat.card (Wn 64) = 2 ^ 64 := card_of_coords (MaskCoords.std 64)

theorem rk_Wn64 : rk (Wn 64) = 64 := by
  unfold rk
  rw [card_Wn64, padicValNat.prime_pow]

theorem sq_eq_one_Wn64 (v : Wn 64) : v ^ 2 = 1 := by
  rw [sq]
  exact mul_self_of_coords (MaskCoords.std 64) v

theorem rk_fixV_w64_le
    {t : MulAut (Wn 64)} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hN : t ∈ Subgroup.normalizer (img64 : Set (MulAut (Wn 64)))) :
    rk ↥(fixV (Subgroup.zpowers t)) ≤ 60 := by
  obtain ⟨n, -, hn⟩ := exists_conj_le64 (A := Subgroup.zpowers t)
    (Subgroup.zpowers_le.2 hN) (isPGroup_two_zpowers ht)
  set t' : MulAut (Wn 64) := MulAut.conj n t with ht'def
  have ht' : t' * t' = 1 := by
    rw [ht'def, ← map_mul, ht, map_one]
  have hmapz : (Subgroup.zpowers t).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers t' := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hmapz] at hn
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.Ch9.L34M.exists_conj_le rho64 sylSig
    (B := Subgroup.zpowers t') hn (isPGroup_two_zpowers ht')
  have hmem := hg (Subgroup.mem_map.2 ⟨t', Subgroup.mem_zpowers t', rfl⟩)
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  rw [coe_sylSig] at hx
  set h : MulAut (Wn 64) := (rho64 g)⁻¹ * n with hh
  have hconj : rho64 x = h * t * h⁻¹ := by
    rw [hxe, ht'def, hh]
    show (rho64 g)⁻¹ * (n * t * n⁻¹) * (rho64 g)⁻¹⁻¹ = (rho64 g)⁻¹ * n * t * ((rho64 g)⁻¹ * n)⁻¹
    group
  have hc : rk ↥(fixV (Subgroup.zpowers (h * t * h⁻¹))) = rk ↥(fixV (Subgroup.zpowers t)) :=
    rk_fixV_zpowers_conj h t
  have hs2 : rho64 x * rho64 x = 1 := by
    rw [hconj]
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hs1 : rho64 x ≠ 1 := by
    intro h1
    apply ht1
    have : t = h⁻¹ * (h * t * h⁻¹) * h := by group
    rw [this, ← hconj, h1]
    group
  have hsS : rho64 x ∈ Sig.map rho64 := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  obtain ⟨d0, hd0, hdA⟩ := cov64 (rho64 x) hsS hs2 hs1
  have hchk : CFSG.Quasithin.H47W.chk64four = true := Certificates.certificate7258
  have hmem4 : (d0.1, pickWit 64 4 d0.1) ∈ CFSG.Quasithin.H47W.dat64four :=
    List.mem_map.2 ⟨d0, hd0, rfl⟩
  have hd4 := List.all_eq_true.1 hchk _ hmem4
  simp only [Bool.and_eq_true] at hd4
  obtain ⟨hall, hr⟩ := hd4
  obtain ⟨h4, hws, hnd4⟩ := rankOK_spec hr
  have key := two_pow_mul_card_le (t := rho64 x) (cs := d0.1) (ws := pickWit 64 4 d0.1) hdA
    hall hws hnd4 (F := fixV (Subgroup.zpowers (rho64 x)))
    (fun v hv => mem_fixV_zpowers_iff_apply.1 hv)
  have h1 : 2 ^ 4 ≤ 2 ^ (pickWit 64 4 d0.1).length := Nat.pow_le_pow_right (by norm_num) h4
  have h2 := le_trans (Nat.mul_le_mul_right _ h1) key
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers (rho64 x))) ≤ 2 ^ 60 := by
    norm_num at h2 ⊢
    omega
  have hrk := rk_le_of_card_le sq_eq_one_Wn64 _ hcard
  rw [hconj] at hrk
  omega

end CFSG.Quasithin.H47W
