module

public import CFSG.Quasithin.Background.H47WBase
public import CFSG.Quasithin.Vol2.Ch9L34Norm16

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Fischer

theorem card_Wn16 : Nat.card (Wn 16) = 2 ^ 16 := card_of_coords (MaskCoords.std 16)

theorem rk_Wn16 : rk (Wn 16) = 16 := by
  unfold rk
  rw [card_Wn16, padicValNat.prime_pow]

theorem sq_eq_one_Wn16 (v : Wn 16) : v ^ 2 = 1 := by
  rw [sq]
  exact mul_self_of_coords (MaskCoords.std 16) v

theorem rk_fixV_w16_le {t : MulAut (Wn 16)} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hN : t ∈ Subgroup.normalizer (img16 : Set (MulAut (Wn 16)))) :
    rk ↥(fixV (Subgroup.zpowers t)) ≤ 10 := by
  obtain ⟨n, -, hn⟩ := exists_conj_le16 (A := Subgroup.zpowers t)
    (Subgroup.zpowers_le.2 hN) (isPGroup_two_zpowers ht)
  set t' : MulAut (Wn 16) := MulAut.conj n t with ht'def
  have ht' : t' * t' = 1 := by
    rw [ht'def, ← map_mul, ht, map_one]
  have hmapz : (Subgroup.zpowers t).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers t' := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hmapz] at hn
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.Ch9.L34M.exists_conj_le rho16 sylSig
    (B := Subgroup.zpowers t') hn (isPGroup_two_zpowers ht')
  have hmem := hg (Subgroup.mem_map.2 ⟨t', Subgroup.mem_zpowers t', rfl⟩)
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  rw [coe_sylSig] at hx
  set h : MulAut (Wn 16) := (rho16 g)⁻¹ * n with hh
  have hconj : rho16 x = h * t * h⁻¹ := by
    rw [hxe, ht'def, hh]
    show (rho16 g)⁻¹ * (n * t * n⁻¹) * (rho16 g)⁻¹⁻¹ = (rho16 g)⁻¹ * n * t * ((rho16 g)⁻¹ * n)⁻¹
    group
  have hc : rk ↥(fixV (Subgroup.zpowers (h * t * h⁻¹))) = rk ↥(fixV (Subgroup.zpowers t)) :=
    rk_fixV_zpowers_conj h t
  have hs2 : rho16 x * rho16 x = 1 := by
    rw [hconj]
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hs1 : rho16 x ≠ 1 := by
    intro h1
    apply ht1
    have : t = h⁻¹ * (h * t * h⁻¹) * h := by group
    rw [this, ← hconj, h1]
    group
  have hsS : rho16 x ∈ Sig.map rho16 := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  obtain ⟨d, hd, hdA⟩ := cov16 (rho16 x) hsS hs2 hs1
  have hchk := chk2_dat16
  simp only [chk2, Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨hall, hr⟩ := hchk.1 d hd
  obtain ⟨h6, hws, hnd6⟩ := rankOK_spec hr
  have key := two_pow_mul_card_le (t := rho16 x) (cs := d.1) (ws := d.2) hdA hall hws hnd6
    (F := fixV (Subgroup.zpowers (rho16 x))) (fun v hv => mem_fixV_zpowers_iff_apply.1 hv)
  have h1 : 2 ^ 6 ≤ 2 ^ d.2.length := Nat.pow_le_pow_right (by norm_num) h6
  have h2 := le_trans (Nat.mul_le_mul_right _ h1) key
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers (rho16 x))) ≤ 2 ^ 10 := by
    norm_num at h2 ⊢
    omega
  have hrk := rk_le_of_card_le sq_eq_one_Wn16 _ hcard
  rw [hconj] at hrk
  omega

end CFSG.Quasithin.H47W
