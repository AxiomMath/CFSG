module

public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Background.B1More8
public import CFSG.Quasithin.Background.B1MoreSevenA

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B1Red

section Reduction

variable {V : Type*} [CommGroup V]

theorem conj_mem_pCoreOf {H : Subgroup (MulAut V)} {h q : MulAut V} (hh : h ∈ H)
    (hq : q ∈ pCoreOf 2 H) : h * q * h⁻¹ ∈ pCoreOf 2 H :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) q).mp hq

theorem fixV_pCoreOf_inv {H : Subgroup (MulAut V)} :
    ∀ h ∈ H, ∀ u ∈ fixV (pCoreOf 2 H), h u ∈ fixV (pCoreOf 2 H) := by
  intro h hh u hu q hq
  have h1 : h⁻¹ * q * h ∈ pCoreOf 2 H := by
    have := conj_mem_pCoreOf (H.inv_mem hh) hq
    simpa using this
  have h2 := hu _ h1
  have h3 : h ((h⁻¹ * q * h) u) = h u := by rw [h2]
  simpa [MulAut.mul_apply] using h3

theorem le_stabSub_fixV_pCoreOf (H : Subgroup (MulAut V)) :
    H ≤ stabSub (fixV (pCoreOf 2 H)) :=
  B1.le_stabSub_of_invariant fixV_pCoreOf_inv

theorem eq_one_of_odd_of_centSub [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    (hQ : IsPGroup 2 ↥Q) {x : MulAut V} (hxo : Odd (orderOf x))
    (hxQ : ∀ q ∈ Q, x * q = q * x) (hxU : x ∈ centSub (fixV Q)) : x = 1 := by
  have hodd : Odd (Nat.card ↥(Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact hxo
  have hcomm : ∀ y ∈ Subgroup.zpowers x, ∀ b ∈ Q, y * b = b * y := by
    intro y hy b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_left (hxQ b hb : Commute x b) k
  have hfix : ∀ y ∈ Subgroup.zpowers x, ∀ m ∈ (⊤ : Subgroup V) ⊓ fixV Q, y m = m := by
    intro y hy m hm
    have : x ∈ MulAction.stabilizer (MulAut V) m := hxU m hm.2
    exact (Subgroup.zpowers_le.2 this) hy
  have h := B1.axb hV hodd hQ hcomm (M := ⊤) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial) hfix
  ext v
  exact h (Subgroup.mem_top v) x (Subgroup.mem_zpowers x)

theorem kernel_eq_pCoreOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {H D : Subgroup (MulAut V)}
    (hD : ∀ x ∈ H, Odd (orderOf x) → x ∈ D)
    (hDQ : ∀ x ∈ D, ∀ q ∈ pCoreOf 2 H, x * q = q * x) :
    H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  apply le_antisymm
  · set C := H ⊓ centSub (fixV (pCoreOf 2 H)) with hC
    have hCn : H ≤ Subgroup.normalizer (C : Set (MulAut V)) :=
      le_normalizer_of_conj fun x hx y hy =>
        ⟨H.mul_mem (H.mul_mem hx hy.1) (H.inv_mem hx),
          conj_mem_centSub (le_stabSub_fixV_pCoreOf H hx) hy.2⟩
    have hC2 : IsPGroup 2 ↥C := by
      rw [IsPGroup.iff_orderOf]
      intro c
      have hcH : (c : MulAut V) ∈ H := c.2.1
      have hcU : (c : MulAut V) ∈ centSub (fixV (pCoreOf 2 H)) := c.2.2
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c : MulAut V)).ne'
      refine ⟨k, ?_⟩
      rw [← Subgroup.orderOf_coe]
      set x := (c : MulAut V) ^ 2 ^ k with hx
      have hxo : orderOf x = m := by
        have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
        rw [hx, orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left,
          Nat.mul_div_cancel_left _ (by positivity)]
      have hxH : x ∈ H := H.pow_mem hcH _
      have hxU : x ∈ centSub (fixV (pCoreOf 2 H)) := (centSub _).pow_mem hcU _
      have hx1 : x = 1 :=
        eq_one_of_odd_of_centSub hV hQ2 (hxo ▸ hm) (hDQ x (hD x hxH (hxo ▸ hm))) hxU
      have hm1 : m = 1 := by rw [← hxo, hx1, orderOf_one]
      rw [hkm, hm1, mul_one]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hC2
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) fun q hq u hu => hu q hq

theorem pCoreOf_autSub_eq_bot [Finite V] {H : Subgroup (MulAut V)}
    (hker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H) :
    pCoreOf 2 (autSub H (fixV (pCoreOf 2 H))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQdef
  set U := fixV Q with hUdef
  have hst : H ≤ stabSub U := le_stabSub_fixV_pCoreOf H
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  set Nbar := pCoreOf 2 (autSub H U) with hNbar
  have hNb2 : IsPGroup 2 ↥Nbar :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autSub H U)
  have hNbn : autSub H U ≤ Subgroup.normalizer (Nbar : Set (MulAut ↥U)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  let N : Subgroup (MulAut V) := (Nbar.comap (resHom U)).map (stabSub U).subtype ⊓ H
  have hmemN : ∀ g : MulAut V, g ∈ N ↔ g ∈ H ∧ ∃ hg : g ∈ stabSub U, resHom U ⟨g, hg⟩ ∈ Nbar := by
    intro g
    constructor
    · rintro ⟨⟨g', hg', rfl⟩, hgH⟩
      exact ⟨hgH, g'.2, hg'⟩
    · rintro ⟨hgH, hg, hmem⟩
      exact ⟨⟨⟨g, hg⟩, hmem, rfl⟩, hgH⟩
  have hNH : N ≤ H := inf_le_right
  have hNn : H ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
    refine le_normalizer_of_conj fun x hx n hn => ?_
    obtain ⟨hnH, hns, hnm⟩ := (hmemN n).1 hn
    have hgn : x * n * x⁻¹ ∈ stabSub U :=
      (stabSub U).mul_mem ((stabSub U).mul_mem (hst hx) hns) ((stabSub U).inv_mem (hst hx))
    refine (hmemN _).2 ⟨H.mul_mem (H.mul_mem hx hnH) (H.inv_mem hx), hgn, ?_⟩
    have hxbar : resHom U ⟨x, hst hx⟩ ∈ autSub H U := mem_autSub.2 ⟨⟨x, hst hx⟩, hx, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hNbn hxbar) _).mp hnm
    have e : resHom U ⟨x * n * x⁻¹, hgn⟩ = resHom U ⟨x, hst hx⟩ * resHom U ⟨n, hns⟩ *
        (resHom U ⟨x, hst hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact this
  have hN2 : IsPGroup 2 ↥N := by
    intro n
    obtain ⟨hnH, hns, hnm⟩ := (hmemN (n : MulAut V)).1 n.2
    obtain ⟨k, hk⟩ := hNb2 ⟨_, hnm⟩
    have hk' : resHom U ⟨(n : MulAut V) ^ 2 ^ k, (stabSub U).pow_mem hns _⟩ = 1 := by
      have := congrArg Subtype.val hk
      simpa [← map_pow] using this
    have hker' : (n : MulAut V) ^ 2 ^ k ∈ H ⊓ centSub U := by
      refine ⟨H.pow_mem hnH _, ?_⟩
      have h1 : (⟨(n : MulAut V) ^ 2 ^ k, (stabSub U).pow_mem hns _⟩ : stabSub U) ∈
          (resHom U).ker := hk'
      rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
      exact h1
    rw [hker] at hker'
    obtain ⟨j, hj⟩ := hQ2 ⟨_, hker'⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hle : N ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH hNn hN2
  refine (Subgroup.eq_bot_iff_forall _).2 fun φ hφ => ?_
  obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hφ)
  have hgN : (g : MulAut V) ∈ N := (hmemN _).2 ⟨hgH, g.2, hφ⟩
  have hgQ := hle hgN
  have hgU : (g : MulAut V) ∈ centSub U := fun u hu => hu _ hgQ
  have : g ∈ (resHom U).ker := by
    rw [ker_resHom, Subgroup.mem_subgroupOf]
    exact hgU
  exact this

end Reduction

end B1Red

end CFSG.Quasithin
