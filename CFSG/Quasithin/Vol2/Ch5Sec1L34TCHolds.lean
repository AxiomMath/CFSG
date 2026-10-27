module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34TCCount
public import CFSG.Quasithin.Vol2.Ch5Sec1L34TCInv
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsOddAm
public import CFSG.Quasithin.Vol2.Ch5Sec1L34TCModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.H13.TorusComm

namespace TorusComm

variable {W : Type*} [CommGroup W]

theorem fixV_conj (s x : MulAut W) :
    fixV (Subgroup.zpowers (s * x * s⁻¹)) = (fixV (Subgroup.zpowers x)).map s.toMonoidHom :=
  CFSG.Quasithin.fixV_zpowers_conj s x

theorem fixV_sq {x : MulAut W} (hx3 : x ^ 3 = 1) :
    fixV (Subgroup.zpowers (x ^ 2)) = fixV (Subgroup.zpowers x) := by
  ext w
  rw [mem_fixV_zpowers, mem_fixV_zpowers, sq, MulAut.mul_apply]
  constructor
  · intro h
    have h1 := congrArg x h
    rw [apply_three hx3] at h1
    exact h1.symm
  · intro h
    rw [h, h]

theorem card_fixV_of_conjPm [Finite W] {y x : MulAut W} (hy3 : y ^ 3 = 1) (h : ConjPm y x) :
    Nat.card (fixV (Subgroup.zpowers x)) = Nat.card (fixV (Subgroup.zpowers y)) := by
  obtain ⟨s, rfl | rfl⟩ := h
  · rw [fixV_conj, Subgroup.card_map_of_injective s.injective]
  · rw [fixV_conj, Subgroup.card_map_of_injective s.injective, fixV_sq hy3]

theorem conjPm_coe {G : Type*} [Group G] {K : Subgroup G} {y x : K} (h : ConjPm y x) :
    ConjPm (y : G) (x : G) := by
  obtain ⟨s, h | h⟩ := h
  · exact ⟨s, Or.inl (by rw [h]; rfl)⟩
  · exact ⟨s, Or.inr (by rw [h]; rfl)⟩

end TorusComm

theorem l34TorusCommFact_holds : L34TorusCommFact := by
  intro W _ _ hW2 K d t n hK hn hd hKd hfd ht2 _ htN htC
  have hmem : ∀ x : MulAut W, x ∈ K → t * x * t⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
  let τ : MulAut ↥K :=
    { toFun := fun x => ⟨t * x * t⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨t * x * t⁻¹, hmem x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show t * (t * (x : MulAut W) * t⁻¹) * t⁻¹ = x
        rw [hti]
        calc t * (t * (x : MulAut W) * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [← sq, ht2, one_mul, mul_one])
      right_inv := fun x => Subtype.ext (by
        show t * (t * (x : MulAut W) * t⁻¹) * t⁻¹ = x
        rw [hti]
        calc t * (t * (x : MulAut W) * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [← sq, ht2, one_mul, mul_one])
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hτapp : ∀ x : ↥K, ((τ x : ↥K) : MulAut W) = t * x * t⁻¹ := fun x => rfl
  have hτ2 : τ * τ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [MulAut.mul_apply, hτapp, hτapp, MulAut.one_apply]
    calc t * (t * (x : MulAut W) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [← sq, ht2, inv_one, one_mul, mul_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply htC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : MulAut W)) h1
    simp only [hτapp, MulAut.one_apply] at h2
    calc x * t = (t * x * t⁻¹) * t := by rw [h2]
      _ = t * x := by group
  obtain ⟨y, hy3, hyτ⟩ := exists_inv_three hK hτ2 hτ1
  have hy3' : orderOf (y : MulAut W) = 3 := by rw [Subgroup.orderOf_coe, hy3]
  have hyy : (y : MulAut W) ^ 3 = 1 := by rw [← hy3']; exact pow_orderOf_eq_one _
  have hy1 : (y : MulAut W) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy3'
    exact absurd hy3' (by norm_num)
  have hty : t * (y : MulAut W) * t⁻¹ = (y : MulAut W)⁻¹ := by
    rw [← hτapp, hyτ]
    rfl
  obtain ⟨b, hb3, hyb, hc2, hc3, hc4⟩ := exists_partner hK hy3
  have hbb : (b : MulAut W) ^ 3 = 1 := by
    have := congrArg (fun z : ↥K => (z : MulAut W)) hb3
    simpa using this
  have hyb' : (y : MulAut W) * b = b * y := congrArg (fun z : ↥K => (z : MulAut W)) hyb
  have hfd' : ∀ w : W, d w = w → w = 1 := by
    intro w hw
    have h1 : w ∈ fixV (Subgroup.zpowers d) := mem_fixV_zpowers.mpr hw
    rw [hfd, Subgroup.mem_bot] at h1
    exact h1
  have h18 := two_pow_eighteen_le_index hW2 hyy hbb hyb' (hKd _ y.2) (hKd _ b.2) hn hd hfd' hy1
    (card_fixV_of_conjPm hyy (conjPm_coe hc2))
    (by simpa using card_fixV_of_conjPm hyy (conjPm_coe hc3))
    (by simpa using card_fixV_of_conjPm hyy (conjPm_coe hc4))
  have hyt : (y : MulAut W) = t * ((y : MulAut W) * t * (y : MulAut W)⁻¹) := by
    have h1 : t * ((y : MulAut W) * t * (y : MulAut W)⁻¹) =
        (t * (y : MulAut W) * t⁻¹) * (y : MulAut W)⁻¹ := by
      rw [hti]
      group
    rw [h1, hty]
    calc (y : MulAut W) = (y : MulAut W) ^ 3 * ((y : MulAut W)⁻¹ * (y : MulAut W)⁻¹) := by group
      _ = _ := by rw [hyy, one_mul]
  set t' := (y : MulAut W) * t * (y : MulAut W)⁻¹ with ht'
  have hle : fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers t') ≤
      fixV (Subgroup.zpowers (y : MulAut W)) := by
    intro w hw
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hw
    rw [mem_fixV_zpowers] at h1 h2 ⊢
    rw [hyt, MulAut.mul_apply, h2, h1]
  have hidx : (fixV (Subgroup.zpowers t')).index = (fixV (Subgroup.zpowers t)).index := by
    rw [ht', fixV_conj, Subgroup.index_map_of_bijective (MulEquiv.bijective _)]
  have h1 : (fixV (Subgroup.zpowers (y : MulAut W))).index ≤
      (fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers t')).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have h2 : (fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers t')).index ≤
      (fixV (Subgroup.zpowers t)).index * (fixV (Subgroup.zpowers t')).index :=
    Subgroup.index_inf_le
  rw [hidx] at h2
  have h3 := h18.trans (h1.trans h2)
  by_contra h4
  push Not at h4
  have h5 := Nat.mul_lt_mul'' h4 h4
  omega

end CFSG.Quasithin.H13
