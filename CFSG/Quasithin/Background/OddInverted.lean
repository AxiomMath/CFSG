module

public import CFSG.Quasithin.Background.D2Conj
public import CFSG.GroupTheory.SupZpowersIndexTwo
public import CFSG.RankThree.GF2n.Parrott.Section1

public section

namespace CFSG.Quasithin

theorem exists_odd_of_not_mem_centralizer {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ X →
      (∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) → IsPGroup 2 P → P = ⊥)
    {t : MulAut W} (ht : t ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (ht2 : orderOf t = 2)
    (htc : t ∉ Subgroup.centralizer (X : Set (MulAut W))) :
    ∃ y ∈ X, y ≠ 1 ∧ Odd (orderOf y) ∧
      rkIdx (fixV (Subgroup.zpowers y)) ≤ 2 * rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  let G : Subgroup (MulAut W) := X ⊔ Subgroup.zpowers t
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  let H := ↥G
  let tH : H := ⟨t, htG⟩
  have htH2 : orderOf tH = 2 := by
    have h := Subgroup.orderOf_coe tH
    rw [show (↑tH : MulAut W) = t from rfl, ht2] at h
    exact h.symm
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2, pow_two] at this
    exact this
  have htHt : tH * tH = 1 := by
    apply Subtype.ext
    change t * t = 1
    exact htt
  let XH : Subgroup H := X.subgroupOf G
  have hGnorm : G ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact Subgroup.zpowers_le.mpr ht
  have hXHnorm : XH.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hGnorm
  have htXH : ∀ y ∈ XH, tH * y * tH⁻¹ ∈ XH := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    change t * (y : MulAut W) * t⁻¹ ∈ X
    exact (Subgroup.mem_normalizer_iff.mp ht (y : MulAut W)).mp hy
  have hsup : XH ⊔ Subgroup.zpowers tH = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left le_sup_left, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  have hXHidx : XH.index ≤ 2 := by
    have h := CFSG.GroupTheory.relIndex_sup_zpowers_le_two (A := XH) (s := tH) htHt htXH
    rw [hsup, Subgroup.relIndex_top_right] at h
    exact h
  have htHpcore : tH ∉ CFSG.pCore 2 H := by
    intro hmem
    let P : Subgroup H := CFSG.pCore 2 H
    have hPnormP : P.Normal := CFSG.pCore_normal
    have hPX : P ⊓ XH = ⊥ := by
      let Q : Subgroup (MulAut W) := (P ⊓ XH).map G.subtype
      have hQle : Q ≤ X := by
        rintro q ⟨p, hp, rfl⟩
        exact (Subgroup.mem_inf.mp hp).2
      have hQinv : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
        intro x hx q hq
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
        have hxG : x ∈ G := Subgroup.mem_sup_left hx
        let xH : H := ⟨x, hxG⟩
        have hpP : p ∈ P := (Subgroup.mem_inf.mp hp).1
        have hpXH : p ∈ XH := (Subgroup.mem_inf.mp hp).2
        have hconjP : xH * p * xH⁻¹ ∈ P :=
          Subgroup.Normal.conj_mem hPnormP p hpP xH
        have hconjXH : xH * p * xH⁻¹ ∈ XH := by
          rw [Subgroup.mem_subgroupOf] at hpXH ⊢
          change x * (p : MulAut W) * x⁻¹ ∈ X
          exact X.mul_mem (X.mul_mem hx hpXH) (X.inv_mem hx)
        exact ⟨xH * p * xH⁻¹, Subgroup.mem_inf.mpr ⟨hconjP, hconjXH⟩, rfl⟩
      have hQp : IsPGroup 2 Q :=
        (CFSG.pCore_isPGroup (p := 2) (G := H)).to_inf_left.map G.subtype
      have hQbot : Q = ⊥ := hO2 Q hQle hQinv hQp
      rw [eq_bot_iff]
      intro p hp
      have hpQ : (p : MulAut W) ∈ Q := ⟨p, hp, rfl⟩
      rw [hQbot] at hpQ
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hpQ))
    have hcommP : ⁅P, XH⁆ ≤ P := @Subgroup.commutator_le_left H _ P XH hPnormP
    have hcommX : ⁅P, XH⁆ ≤ XH := @Subgroup.commutator_le_right H _ P XH hXHnorm
    have hcommbot : ⁅P, XH⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzinf : z ∈ P ⊓ XH := Subgroup.mem_inf.mpr ⟨hcommP hz, hcommX hz⟩
      rwa [hPX] at hzinf
    have hPcent : P ≤ Subgroup.centralizer (XH : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
    have htcentH : tH ∈ Subgroup.centralizer (XH : Set H) := hPcent hmem
    apply htc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxG : x ∈ G := Subgroup.mem_sup_left hx
    have hcomm := (Subgroup.mem_centralizer_iff.mp htcentH) ⟨x, hxG⟩
      (Subgroup.mem_subgroupOf.mpr hx)
    have hval := congrArg Subtype.val hcomm
    change x * t = t * x at hval
    exact hval
  obtain ⟨yH, hyH1, hyHodd, hyHinv⟩ :=
    CFSG.RankThree.GF2n.Parrott.prop1_inverts_odd htH2 htHpcore
  have hyHXH : yH ∈ XH := by
    have hpos : 0 < XH.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases (by omega : XH.index = 1 ∨ XH.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top yH
    · have hy2 : yH ^ 2 ∈ XH := Subgroup.sq_mem_of_index_two h2 yH
      obtain ⟨m, hm⟩ := hyHodd
      have he : yH = (yH ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = orderOf yH + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [he]
      exact XH.pow_mem hy2 (m + 1)
  let y : MulAut W := yH
  have hyX : y ∈ X := Subgroup.mem_subgroupOf.mp hyHXH
  have hy1 : y ≠ 1 := by
    intro h
    exact hyH1 (Subtype.ext h)
  have hyodd : Odd (orderOf y) := by
    change Odd (orderOf (yH : MulAut W))
    rw [Subgroup.orderOf_coe]
    exact hyHodd
  have hconj : t * y * t⁻¹ = y⁻¹ := by
    have h := congrArg Subtype.val hyHinv
    change t * (yH : MulAut W) * t⁻¹ = (yH : MulAut W)⁻¹ at h
    simpa [y] using h
  have hyodd' : Odd (orderOf y) := hyodd
  obtain ⟨m, hm⟩ := hyodd
  let z : MulAut W := y ^ m
  have hty : t * y = y⁻¹ * t := by
    calc t * y = (t * y * t⁻¹) * t := by group
      _ = y⁻¹ * t := by rw [hconj]
  have hpow : t * y ^ (m + 1) = (y⁻¹) ^ (m + 1) * t := by
    have h := conj_pow (i := m + 1) (a := t) (b := y)
    rw [hconj] at h
    calc t * y ^ (m + 1) = (t * y ^ (m + 1) * t⁻¹) * t := by group
      _ = (y⁻¹) ^ (m + 1) * t := by rw [← h]
  have hpowinv : (y⁻¹) ^ (m + 1) = y ^ m := by
    have hord : y ^ (m + 1) * y ^ m = 1 := by
      rw [← pow_add, show m + 1 + m = orderOf y by omega, pow_orderOf_eq_one]
    rw [inv_pow, inv_eq_of_mul_eq_one_right hord]
  have hcommz : (t * y) * z = z * t := by
    calc (t * y) * z = t * (y * z) := by rw [mul_assoc]
      _ = t * y ^ (m + 1) := by
        rw [show y * z = y ^ (m + 1) by simpa [z, pow_succ']]
      _ = (y⁻¹) ^ (m + 1) * t := hpow
      _ = y ^ m * t := by rw [hpowinv]
      _ = z * t := rfl
  have hz : z * t * z⁻¹ = t * y := by
    calc z * t * z⁻¹ = ((t * y) * z) * z⁻¹ := by rw [hcommz]
      _ = t * y := by group
  have hpowers : Subgroup.zpowers (t * y) = conjBy z (Subgroup.zpowers t) := by
    rw [← hz, conjBy, MonoidHom.map_zpowers]
    rfl
  let Ct : Subgroup W := fixV (Subgroup.zpowers t)
  let Cty : Subgroup W := fixV (Subgroup.zpowers (t * y))
  let Cy : Subgroup W := fixV (Subgroup.zpowers y)
  have hCty : Cty = Ct.map z.toMonoidHom := by
    rw [show Cty = fixV (Subgroup.zpowers (t * y)) from rfl, hpowers]
    exact CFSG.Quasithin.fixV_conjBy z (Subgroup.zpowers t)
  have hcardCty : Nat.card ↥Cty = Nat.card ↥Ct := by
    rw [hCty]
    exact Subgroup.card_map_of_injective (f := z.toMonoidHom) (MulEquiv.injective z)
  have hle : Ct ⊓ Cty ≤ Cy := by
    intro w hw
    rw [Subgroup.mem_inf, mem_fixV, mem_fixV] at hw
    rw [mem_fixV]
    intro a ha
    have htfix : t w = w := hw.1 t (Subgroup.mem_zpowers t)
    have htyfix : (t * y) w = w := hw.2 (t * y) (Subgroup.mem_zpowers (t * y))
    have hyfix : y w = w := by
      have h1 : t (t (y w)) = y w := by
        rw [← MulAut.mul_apply, htt, MulAut.one_apply]
      have h2 : t (t (y w)) = w := by
        calc t (t (y w)) = t ((t * y) w) := by rw [MulAut.mul_apply]
          _ = t w := by rw [htyfix]
          _ = w := htfix
      exact h1.symm.trans h2
    have hstab : y ∈ MulAction.stabilizer (MulAut W) w := by
      rw [MulAction.mem_stabilizer_iff]
      exact hyfix
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hstab ha)
  have hsuprk : rk ↥(Ct ⊔ Cty) ≤ rk W := by
    have := rk_mono (le_top : Ct ⊔ Cty ≤ ⊤)
    simpa [rk_top] using this
  have hinfrk : rk ↥(Ct ⊓ Cty) ≤ rk ↥Cy := rk_mono hle
  have hsum := rk_sup_add_rk_inf Ct Cty
  have hCy := rk_add_rkIdx Cy
  have hCt := rk_add_rkIdx Ct
  have hCtyrk : rk ↥Cty = rk ↥Ct := by
    unfold rk
    rw [hcardCty]
  refine ⟨y, hyX, hy1, hyodd', ?_⟩
  change rkIdx Cy ≤ 2 * rkIdx Ct
  omega

end CFSG.Quasithin
