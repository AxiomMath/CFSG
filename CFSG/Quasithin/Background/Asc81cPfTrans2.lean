module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.Asc81cPfTrans1
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] [Finite W]

section Aux

theorem rkIdx_le_of_card_le (hW : ∀ w : W, w ^ 2 = 1) {H K : Subgroup W}
    (h : Nat.card H ≤ Nat.card K) : rkIdx K ≤ rkIdx H := by
  have h1 := rk_add_rkIdx H
  have h2 := rk_add_rkIdx K
  have h3 : rk H ≤ rk K := by
    rw [card_eq_two_pow hW H, card_eq_two_pow hW K] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  omega

theorem rkIdx_fixV_eq (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) : rkIdx (fixV X) = rk (commSub (⊤ : Subgroup W) X) := by
  have h1 := rk_add_rkIdx (fixV X)
  have h2 : rk (fixV X) + rk (commSub (⊤ : Subgroup W) X) = rk W := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_fixV_mul_card_commSub hW hX]
  omega

omit [Finite W] in
theorem mem_fixV_zpowers {t : MulAut W} {v : W} (h : t v = v) :
    v ∈ fixV (Subgroup.zpowers t) :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply.2 h

theorem mParam_le_of_orderOf_two {G : Subgroup (MulAut W)} {t : MulAut W} (ht : t ∈ G)
    (ht2 : orderOf t = 2) : E3.mParam G ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have := finite_mulAut (W := W)
  refine E3.mParam_le_rkIdx_fixV ((Subgroup.zpowers_le).2 ht) ?_ ?_
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  · intro h0
    have h1 := (Subgroup.zpowers_eq_bot).1 h0
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by decide)

omit [Finite W] in
theorem apply_eq_of_mul_self_apply_eq {y : MulAut W} (hy : Odd (orderOf y)) {u : W}
    (h : (y * y) u = u) : y u = u := by
  obtain ⟨m, hm⟩ := hy
  have h1 : y = (y * y) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul]
    calc y = y ^ (orderOf y + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      _ = y ^ (2 * (m + 1)) := by rw [hm]; ring_nf
  rw [h1]
  exact_mod_cast zpow_apply_eq h ((m + 1 : ℕ) : ℤ)

omit [Finite W] in
theorem apply_commutator_eq (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W} (ht : t * t = 1) (v : W) :
    t (t v * v⁻¹) = t v * v⁻¹ := by
  have h1 : t (t v) = v := by rw [← MulAut.mul_apply, ht, MulAut.one_apply]
  rw [map_mul, map_inv, h1]
  have hsq : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by rw [← pow_two, hW])
  rw [hsq (t v), hsq v, mul_comm]

end Aux

variable {G : Subgroup (MulAut W)} {Ω : Set (Subgroup (MulAut W))} {X₀ Y₀ : Subgroup (MulAut W)}

theorem TransSetting.card_fixV_le (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) {Z : Subgroup (MulAut W)}
    (hZ : Z ∈ Ω) :
    Nat.card (fixV Z) ≤ Nat.card (fixV G) * Nat.card (commSub (⊤ : Subgroup W) Z) := by
  obtain ⟨K, hK, hKX, hKY⟩ := hT.exists_third hW hX₀ hY₀ hnc
  obtain ⟨Z', hZ', hZZ'⟩ : ∃ Z' ∈ Ω, Z' ≠ Z := by
    by_cases h : X₀ = Z
    · exact ⟨K, hK, fun h' => hKX (h'.trans h.symm)⟩
    · exact ⟨X₀, hX₀, h⟩
  have hTI := hT.fixV_inf_eq hW hX₀ hY₀ hnc hZ hZ' (Ne.symm hZZ')
  have h1 := card_sup_mul_card_inf (fixV Z) (fixV Z')
  rw [hTI] at h1
  have h2 : Nat.card ↥(fixV Z ⊔ fixV Z') ≤ Nat.card W :=
    Nat.card_le_card_of_injective _ (fixV Z ⊔ fixV Z').subtype_injective
  have h3 := card_fixV_mul_card_commSub hW (hT.hyp Z hZ).1.2.2.2.1
  have h4 : Nat.card (fixV Z') = Nat.card (fixV Z) := by
    obtain ⟨g, -, rfl⟩ := hT.trans Z hZ Z' hZ'
    rw [fixV_map_conj, Subgroup.card_map_of_injective g.injective]
  rw [h4] at h1
  have hpos : 0 < Nat.card (fixV Z) := Nat.card_pos
  rw [← h3] at h2
  nlinarith

theorem TransSetting.eq_one_of_mod (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) {g : MulAut W} (hg : g ∈ G)
    (hgv : ∀ v, g v * v⁻¹ ∈ fixV G) : g = 1 := by
  have hfixG : ∀ h ∈ G, ∀ c ∈ fixV G, h c = c := fun h hh c hc => hc h hh
  let Q : Subgroup (MulAut W) :=
    { carrier := {q | q ∈ G ∧ ∀ v, q v * v⁻¹ ∈ fixV G}
      one_mem' := ⟨G.one_mem, fun v => by
        show (1 : MulAut W) v * v⁻¹ ∈ fixV G
        rw [MulAut.one_apply, mul_inv_cancel]
        exact (fixV G).one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨G.mul_mem ha.1 hb.1, fun v => by
        have h1 := (fixV G).mul_mem (ha.2 (b v)) (hb.2 v)
        have h2 : (a * b) v * v⁻¹ = a (b v) * (b v)⁻¹ * (b v * v⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [h2]
        exact h1⟩
      inv_mem' := fun {a} ha => ⟨G.inv_mem ha.1, fun v => by
        have h1 := (fixV G).inv_mem (ha.2 (a⁻¹ v))
        have h2 : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]
          group
        rw [h2]
        exact h1⟩ }
  have hQ : ∀ q, q ∈ Q ↔ q ∈ G ∧ ∀ v, q v * v⁻¹ ∈ fixV G := fun q => Iff.rfl
  have hQn : ∀ h ∈ G, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro h hh q hq
    refine ⟨G.mul_mem (G.mul_mem hh hq.1) (G.inv_mem hh), fun v => ?_⟩
    have h1 : (h * q * h⁻¹) v * v⁻¹ = h (q (h⁻¹ v) * (h⁻¹ v)⁻¹) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [h1]
    intro x hx
    rw [hfixG h hh _ (hq.2 _)]
    exact hq.2 _ x hx
  have hQ2 : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    ext v
    have h1 := hq.2 v
    have h2 : q (q v * v⁻¹) = q v * v⁻¹ := hfixG q hq.1 _ h1
    rw [map_mul, map_inv] at h2
    rw [MulAut.mul_apply, MulAut.one_apply]
    have h3 : q (q v) = q v * v⁻¹ * q v := by rw [← h2]; group
    rw [h3]
    have hsq : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hW])
    have hqq : q v * q v = 1 := by rw [← pow_two, hW]
    calc q v * v⁻¹ * q v = q v * q v * v⁻¹ := by rw [mul_assoc, mul_comm v⁻¹, ← mul_assoc]
      _ = v := by rw [hqq, one_mul, hsq]
  have hQZ : ∀ q ∈ Q, ∀ Z ∈ Ω, Commutes Z (Subgroup.zpowers q) ∧
      ∀ w ∈ commSub (⊤ : Subgroup W) Z, q w = w := by
    intro q hq Z hZ
    have hZh := (hT.hyp Z hZ).1
    have hqN : q ∈ Subgroup.normalizer (Z : Set (MulAut W)) :=
      mem_normalizer_of_mapsTo hZh hq.1 fun v hv => by
        have h1 : q v * v⁻¹ ∈ fixV Z := fun z hz => hq.2 v z (hZh.1 hz)
        have h2 := (fixV Z).mul_mem h1 hv
        rwa [inv_mul_cancel_right] at h2
    have hcomm : ∀ z ∈ Z, q * z = z * q := by
      intro z hz
      have h1 : q * z * q⁻¹ * z⁻¹ ∈ Z :=
        Z.mul_mem (conj_mem hqN ⟨z, hz⟩) (Z.inv_mem hz)
      have h2 : q * z * q⁻¹ * z⁻¹ ∈ Q := by
        have h3 := Q.mul_mem hq (hQn z ((hZh.1) hz) q⁻¹ (Q.inv_mem hq))
        have h4 : q * (z * q⁻¹ * z⁻¹) = q * z * q⁻¹ * z⁻¹ := by group
        rwa [h4] at h3
      have h3 := hQ2 _ h2
      have hodd := odd_orderOf_of_mem hZh.2.2.2.1 h1
      have h4 : orderOf (q * z * q⁻¹ * z⁻¹) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
      have h5 : orderOf (q * z * q⁻¹ * z⁻¹) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h6 | h6
        · exact h6
        · rw [h6] at hodd
          exact absurd hodd (by decide)
      have h6 := orderOf_eq_one_iff.1 h5
      calc q * z = q * z * q⁻¹ * z⁻¹ * (z * q) := by group
        _ = z * q := by rw [h6, one_mul]
    refine ⟨fun z hz b hb => ?_, fun w hw => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((show Commute q z from hcomm z hz).zpow_left k).eq.symm
    · have hqw : q w ∈ commSub (⊤ : Subgroup W) Z :=
        commSub_stable_of_commute (fun z hz => hcomm z hz) hw
      have h1 : q w * w⁻¹ ∈ fixV Z ⊓ commSub ⊤ Z :=
        ⟨fun z hz => hq.2 w z (hZh.1 hz), (commSub ⊤ Z).mul_mem hqw ((commSub ⊤ Z).inv_mem hw)⟩
      rw [fixV_inf_commSub_eq_bot' hW hZh.2.2.2.1] at h1
      exact mul_inv_eq_one.1 h1
  by_contra hg1
  have hgQ : g ∈ Q := ⟨hg, hgv⟩
  have hg2 : orderOf g = 2 := by
    have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hQ2 g hgQ)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hg1
    · exact h2
  have hle : commSub (⊤ : Subgroup W) X₀ ⊔ fixV G ≤ fixV (Subgroup.zpowers g) := by
    refine sup_le (fun w hw => mem_fixV_zpowers ((hQZ g hgQ X₀ hX₀).2 w hw))
      (fun c hc => mem_fixV_zpowers (hfixG g hg c hc))
  have hbot : commSub (⊤ : Subgroup W) X₀ ⊓ fixV G = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    have h1 : w ∈ fixV X₀ ⊓ commSub ⊤ X₀ :=
      ⟨fun z hz => hw2 z ((hT.hyp X₀ hX₀).1.1 hz), hw1⟩
    rwa [fixV_inf_commSub_eq_bot' hW (hT.hyp X₀ hX₀).1.2.2.2.1] at h1
  have h1 := Subgroup.card_le_of_le hle
  rw [card_sup_of_inf_eq_bot hbot] at h1
  have h2 := hT.card_fixV_le hW hX₀ hY₀ hnc hX₀
  have h3 : Nat.card (fixV X₀) ≤ Nat.card (fixV (Subgroup.zpowers g)) := by
    calc Nat.card (fixV X₀) ≤ Nat.card (fixV G) * Nat.card (commSub (⊤ : Subgroup W) X₀) := h2
      _ = Nat.card (commSub (⊤ : Subgroup W) X₀) * Nat.card (fixV G) := mul_comm _ _
      _ ≤ _ := h1
  have h4 := rkIdx_le_of_card_le hW h3
  rw [rkIdx_fixV_eq hW (hT.hyp X₀ hX₀).1.2.2.2.1] at h4
  have h5 := mParam_le_of_orderOf_two hg hg2
  have h6 := (hT.hyp X₀ hX₀).2
  omega

theorem TransSetting.normalizes_of_involution (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) {t : MulAut W} (ht : t ∈ G)
    (ht2 : orderOf t = 2) {Z : Subgroup (MulAut W)} (hZ : Z ∈ Ω) :
    Z.map (MulAut.conj t).toMonoidHom = Z := by
  by_contra hne
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hZh := (hT.hyp Z hZ).1
  have hZ' := hT.inv t ht Z hZ
  have hTI := hT.fixV_inf_eq hW hX₀ hY₀ hnc hZ hZ' (Ne.symm hne)
  have hfix' : fixV (Z.map (MulAut.conj t).toMonoidHom) = (fixV Z).map t.toMonoidHom :=
    fixV_map_conj Z t
  have hfixG : ∀ c ∈ fixV G, t c = c := fun c hc => hc t ht
  let φ : fixV Z →* W :=
    { toFun := fun v => t v * (v : W)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        ac_rfl }
  have hker : ∀ v : fixV Z, φ v = 1 → (v : W) ∈ fixV G := by
    intro v hv
    have h1 : t v = v := mul_inv_eq_one.1 hv
    have h2 : (v : W) ∈ fixV Z ⊓ fixV (Z.map (MulAut.conj t).toMonoidHom) := by
      refine ⟨v.2, ?_⟩
      rw [hfix']
      exact ⟨v, v.2, h1⟩
    rwa [hTI] at h2
  have hinf : φ.range ⊓ fixV G = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨v, hv1, rfl⟩, hv2⟩
    have h1 : t v ∈ fixV Z := by
      have h3 : φ v * v ∈ fixV Z :=
        (fixV Z).mul_mem (fun z hz => hv2 z (hZh.1 hz)) v.2
      have h4 : φ v * v = t v := inv_mul_cancel_right _ _
      rwa [h4] at h3
    have h2 : t v ∈ fixV Z ⊓ fixV (Z.map (MulAut.conj t).toMonoidHom) := by
      refine ⟨h1, ?_⟩
      rw [hfix']
      exact ⟨v, v.2, rfl⟩
    rw [hTI] at h2
    have h3 : (v : W) = t v := by
      calc (v : W) = t (t v) := by rw [← MulAut.mul_apply, htt, MulAut.one_apply]
        _ = t v := hfixG _ h2
    show t v * (v : W)⁻¹ = 1
    rw [← h3, mul_inv_cancel]
  have hle : φ.range ⊔ fixV G ≤ fixV (Subgroup.zpowers t) := by
    refine sup_le ?_ (fun c hc => mem_fixV_zpowers (hfixG c hc))
    rintro _ ⟨v, rfl⟩
    exact mem_fixV_zpowers (apply_commutator_eq hW htt v)
  have hkercard : Nat.card φ.ker ≤ Nat.card (fixV G) := by
    refine Nat.card_le_card_of_injective (fun k => (⟨k.1.1, hker k.1 k.2⟩ : fixV G)) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val hab :))
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 := Subgroup.card_le_of_le hle
  rw [card_sup_of_inf_eq_bot hinf] at h2
  have h3 : Nat.card (fixV Z) ≤ Nat.card (fixV (Subgroup.zpowers t)) := by
    calc Nat.card (fixV Z) = Nat.card φ.ker * Nat.card φ.range := h1.symm
      _ ≤ Nat.card (fixV G) * Nat.card φ.range := Nat.mul_le_mul_right _ hkercard
      _ = Nat.card φ.range * Nat.card (fixV G) := mul_comm _ _
      _ ≤ _ := h2
  have h4 := rkIdx_le_of_card_le hW h3
  rw [rkIdx_fixV_eq hW hZh.2.2.2.1] at h4
  have h5 := mParam_le_of_orderOf_two ht ht2
  have h6 := (hT.hyp Z hZ).2
  omega

omit [Finite W] in
theorem eq_one_of_mul_self_eq_one {x : MulAut W} (hx : Odd (orderOf x)) (h : x * x = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · rw [h2] at hx
    exact absurd hx (by decide)

omit [Finite W] in
theorem fixes_commSub_of_commute {G Z : Subgroup (MulAut W)} (hZ : Hyp101 G Z) {t : MulAut W}
    (htt : t * t = 1) (hc : ∀ z ∈ Z, t * z = z * t) :
    ∀ w ∈ commSub (⊤ : Subgroup W) Z, t w = w := by
  obtain ⟨x₀, hx₀, hx₀v⟩ := exists_eq_on_commSub hZ hc
  obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one hZ
  have h1 : (x₀ * x₀) w₀ = w₀ := by
    have h2 : t (t w₀) = w₀ := by rw [← MulAut.mul_apply, htt, MulAut.one_apply]
    rw [hx₀v _ (commSub_stable_of_commute hc hw₀), hx₀v w₀ hw₀] at h2
    rw [MulAut.mul_apply]
    exact h2
  have h3 := eq_one_of_apply_eq hZ (Z.mul_mem hx₀ hx₀) hw₀ hw₀1 h1
  have h4 := eq_one_of_mul_self_eq_one (odd_orderOf_of_mem hZ.2.2.2.1 hx₀) h3
  intro w hw
  rw [hx₀v w hw, h4, MulAut.one_apply]

theorem card_mul_add_le_of_free (hW : ∀ w : W, w ^ 2 = 1) {G H S : Subgroup (MulAut W)}
    (hHh : Hyp101 G H) (hSH : S ≤ H) {U C : Subgroup W} (hCU : C ≤ U)
    (hSU : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) (hSC : ∀ s ∈ S, ∀ c ∈ C, s c = c)
    (hUH : U ⊓ fixV H = C) (hu : ∃ u ∈ U, u ∉ C) :
    Nat.card S * Nat.card C + Nat.card C ≤ Nat.card U := by
  classical
  obtain ⟨u, huU, huC⟩ := hu
  have hmem : ∀ p : S × C, (p.1 : MulAut W) u * (p.2 : W) ∈ ((U : Set W) \ C) := by
    rintro ⟨s, c⟩
    refine ⟨U.mul_mem (hSU s s.2 u huU) (hCU c.2), fun h => huC ?_⟩
    have h1 : (s : MulAut W) u ∈ C := by
      have h2 := C.mul_mem h (C.inv_mem c.2)
      rwa [mul_inv_cancel_right] at h2
    have h3 := hSC _ (S.inv_mem s.2) _ h1
    rw [MulAut.inv_apply_self] at h3
    rw [h3]
    exact h1
  let Ψ : S × C → ↥((U : Set W) \ C) := fun p => ⟨_, hmem p⟩
  have hΨ : Function.Injective Ψ := by
    rintro ⟨s, c⟩ ⟨s', c'⟩ h
    have h1 : (s : MulAut W) u * (c : W) = (s' : MulAut W) u * (c' : W) := congrArg Subtype.val h
    set y := (s' : MulAut W)⁻¹ * s with hy
    have hyS : y ∈ S := S.mul_mem (S.inv_mem s'.2) s.2
    have hd : (c' : W) * (c : W)⁻¹ ∈ C := C.mul_mem c'.2 (C.inv_mem c.2)
    have h2 : y u = u * ((c' : W) * (c : W)⁻¹) := by
      have h3 : (s : MulAut W) u = (s' : MulAut W) u * ((c' : W) * (c : W)⁻¹) := by
        rw [← mul_assoc, ← h1, mul_inv_cancel_right]
      rw [hy, MulAut.mul_apply, h3, map_mul, MulAut.inv_apply_self,
        hSC _ (S.inv_mem s'.2) _ hd]
    have h4 : (y * y) u = u := by
      rw [MulAut.mul_apply, h2, map_mul, h2, hSC y hyS _ hd, mul_assoc, ← pow_two, hW, mul_one]
    have h5 := apply_eq_of_mul_self_apply_eq (odd_orderOf_of_mem hHh.2.2.2.1 (hSH hyS)) h4
    have hy1 : y = 1 := by
      by_contra hy1
      apply huC
      rw [← hUH]
      refine ⟨huU, ?_⟩
      have hzp : Subgroup.zpowers y ≤ H := (Subgroup.zpowers_le).2 (hSH hyS)
      have hzp1 : Subgroup.zpowers y ≠ ⊥ := fun h0 => hy1 ((Subgroup.zpowers_eq_bot).1 h0)
      rw [← fixV_eq_of_le hW hHh hzp hzp1]
      exact mem_fixV_zpowers h5
    have hss : s = s' := by
      apply Subtype.ext
      rw [hy, inv_mul_eq_one] at hy1
      exact hy1.symm
    subst hss
    have hcc : (c : W) = c' := by
      have h6 := h1
      exact mul_left_cancel h6
    rw [show c = c' from Subtype.ext hcc]
  have h1 := Nat.card_le_card_of_injective Ψ hΨ
  rw [Nat.card_prod, Nat.card_coe_set_eq, Set.ncard_sdiff (show (C : Set W) ⊆ U from hCU),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h1
  have h2 : Nat.card C ≤ Nat.card U := Subgroup.card_le_of_le hCU
  change Nat.card S * Nat.card C ≤ Nat.card U - Nat.card C at h1
  omega

theorem TransSetting.odd_card (hW : ∀ w : W, w ^ 2 = 1) (hT : TransSetting G Ω)
    (hX₀ : X₀ ∈ Ω) (hY₀ : Y₀ ∈ Ω) (hnc : ¬ Commutes X₀ Y₀) : Odd (Nat.card G) := by
  have := finite_mulAut (W := W)
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.1 hodd)
  obtain ⟨t, htdef⟩ : ∃ t : MulAut W, t = (t₀ : MulAut W) := ⟨_, rfl⟩
  have ht : t ∈ G := htdef ▸ t₀.2
  have ht2 : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe, ht₀]
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htN := fun Z (hZ : Z ∈ Ω) => hT.normalizes_of_involution hW hX₀ hY₀ hnc ht ht2 hZ
  have hG : X₀ ⊔ Y₀ = G := (hT.dich X₀ hX₀ Y₀ hY₀).resolve_left hnc
  by_cases hall : ∀ Z ∈ Ω, ∀ z ∈ Z, t * z = z * t
  ·
    have htG : ∀ g ∈ G, t * g = g * t := by
      have hle : X₀ ⊔ Y₀ ≤ Subgroup.centralizer {t} := sup_le
        (fun x hx => Subgroup.mem_centralizer_iff.2 fun c hc => by
          rw [Set.mem_singleton_iff.1 hc]
          exact hall X₀ hX₀ x hx)
        (fun y hy => Subgroup.mem_centralizer_iff.2 fun c hc => by
          rw [Set.mem_singleton_iff.1 hc]
          exact hall Y₀ hY₀ y hy)
      intro g hg
      rw [← hG] at hg
      exact Subgroup.mem_centralizer_iff.1 (hle hg) t (Set.mem_singleton t)
    have hfixVG : ∀ w ∈ commSub (⊤ : Subgroup W) G, t w = w := by
      have hle : commSub (⊤ : Subgroup W) G ≤ fixV (Subgroup.zpowers t) := by
        rw [hT.commSub_eq_sup hX₀ hY₀ hnc]
        exact sup_le
          (fun w hw => mem_fixV_zpowers
            (fixes_commSub_of_commute (hT.hyp X₀ hX₀).1 htt (hall X₀ hX₀) w hw))
          (fun w hw => mem_fixV_zpowers
            (fixes_commSub_of_commute (hT.hyp Y₀ hY₀).1 htt (hall Y₀ hY₀) w hw))
      intro w hw
      exact hle hw t (Subgroup.mem_zpowers t)
    apply (show t ≠ 1 from fun h => by rw [h, orderOf_one] at ht2; exact absurd ht2 (by decide))
    refine hT.eq_one_of_mod hW hX₀ hY₀ hnc ht fun v g hg => ?_
    have hc : g v * v⁻¹ ∈ commSub (⊤ : Subgroup W) G :=
      Subgroup.subset_closure ⟨g, hg, v, Subgroup.mem_top v, rfl⟩
    have h1 : g (t v * v⁻¹) = t (g v) * (g v)⁻¹ := by
      rw [map_mul, map_inv, ← MulAut.mul_apply, ← htG g hg, MulAut.mul_apply]
    rw [h1]
    have h2 : g v = (g v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    rw [h2, map_mul, hfixVG _ hc, mul_inv_rev, mul_comm (g v * v⁻¹) (t v), mul_assoc,
      ← mul_assoc (g v * v⁻¹), mul_comm (g v * v⁻¹) v⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  · push Not at hall
    obtain ⟨H, hH, x, hx, htx⟩ := hall
    have hHh := (hT.hyp H hH).1
    have htNH : t ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (htN H hH)
    have hsq := sq_card_centralizer_le hW hHh htNH ⟨x, hx, htx⟩
    have hmem : ∀ y : H, t * (y : MulAut W) * t⁻¹ * (y : MulAut W)⁻¹ ∈ H := fun y =>
      H.mul_mem (conj_mem htNH y) (H.inv_mem y.2)
    let φ : H →* H :=
      { toFun := fun y => ⟨_, hmem y⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          show t * ((a : MulAut W) * b) * t⁻¹ * ((a : MulAut W) * b)⁻¹ =
            t * a * t⁻¹ * (a : MulAut W)⁻¹ * (t * b * t⁻¹ * (b : MulAut W)⁻¹)
          have e1 : (a : MulAut W)⁻¹ * (t * b * t⁻¹ * (b : MulAut W)⁻¹) =
              (t * b * t⁻¹ * (b : MulAut W)⁻¹) * (a : MulAut W)⁻¹ :=
            mul_comm_of_isCyclic hHh.2.2.1 (H.inv_mem a.2) (hmem b)
          calc t * ((a : MulAut W) * b) * t⁻¹ * ((a : MulAut W) * b)⁻¹
              = t * a * t⁻¹ * ((t * b * t⁻¹ * (b : MulAut W)⁻¹) * (a : MulAut W)⁻¹) := by
                group
            _ = _ := by rw [← e1]; group) }
    have hcardker : Nat.card φ.ker = Nat.card ↥(H ⊓ Subgroup.centralizer {t}) := by
      refine Nat.card_congr
        { toFun := fun k => ⟨k.1, k.1.2, Subgroup.mem_centralizer_iff.2 fun c hc => by
            rw [Set.mem_singleton_iff.1 hc]
            have h1 : t * (k.1 : MulAut W) * t⁻¹ * (k.1 : MulAut W)⁻¹ = 1 :=
              congrArg Subtype.val (MonoidHom.mem_ker.1 k.2)
            calc t * (k.1 : MulAut W) = t * k.1 * t⁻¹ * (k.1 : MulAut W)⁻¹ * (k.1 * t) := by
                  group
              _ = k.1 * t := by rw [h1, one_mul]⟩
          invFun := fun k => ⟨⟨k.1, k.2.1⟩, MonoidHom.mem_ker.2 (Subtype.ext (by
            show t * (k : MulAut W) * t⁻¹ * (k : MulAut W)⁻¹ = 1
            rw [Subgroup.mem_centralizer_iff.1 k.2.2 t (Set.mem_singleton t)]
            group))⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hkr := Subgroup.card_ker_mul_card_range φ
    rw [hcardker] at hkr
    have hrangeN : ∀ r ∈ φ.range, ∀ K ∈ Ω,
        K.map (MulAut.conj (r : MulAut W)).toMonoidHom = K := by
      rintro _ ⟨y, rfl⟩ K hK
      have hyG : (y : MulAut W) ∈ G := hHh.1 y.2
      have h1 : orderOf ((y : MulAut W) * t * (y : MulAut W)⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
      have h2 := hT.normalizes_of_involution hW hX₀ hY₀ hnc
        (G.mul_mem (G.mul_mem hyG ht) (G.inv_mem hyG)) h1 hK
      have h3 : (t * (y : MulAut W) * t⁻¹ * (y : MulAut W)⁻¹ : MulAut W) =
          t * ((y : MulAut W) * t * (y : MulAut W)⁻¹) := by
        have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
        rw [ht']
        group
      show K.map (MulAut.conj (t * (y : MulAut W) * t⁻¹ * (y : MulAut W)⁻¹)).toMonoidHom = K
      rw [h3, ← map_conj_map_conj, h2, htN K hK]
    obtain ⟨K₃, hK₃, hK₃X, hK₃Y⟩ := hT.exists_third hW hX₀ hY₀ hnc
    have hXY : X₀ ≠ Y₀ := fun h => hnc (h ▸ commutes_self_of_isCyclic (hT.hyp X₀ hX₀).1.2.2.1)
    obtain ⟨K₁, hK₁, K₂, hK₂, hK₁H, hK₂H, hK₁₂⟩ : ∃ K₁ ∈ Ω, ∃ K₂ ∈ Ω, K₁ ≠ H ∧ K₂ ≠ H ∧
        K₁ ≠ K₂ := by
      by_cases h1 : X₀ = H
      · exact ⟨Y₀, hY₀, K₃, hK₃, fun h => hXY (h1.trans h.symm),
          fun h => hK₃X (h.trans h1.symm), fun h => hK₃Y h.symm⟩
      · by_cases h2 : Y₀ = H
        · exact ⟨X₀, hX₀, K₃, hK₃, h1, fun h => hK₃Y (h.trans h2.symm),
            fun h => hK₃X h.symm⟩
        · exact ⟨X₀, hX₀, Y₀, hY₀, h1, h2, hXY⟩
    have hc1 : 0 < Nat.card ↥(H ⊓ Subgroup.centralizer {t}) := Nat.card_pos
    have hcH := card_commSub hHh
    have hi3 : 2 ≤ Nat.card φ.range := by nlinarith
    obtain ⟨h₀, hh₀, hh₀1⟩ : ∃ h ∈ φ.range, h ≠ 1 := by
      by_contra hall
      push Not at hall
      have : φ.range = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
      rw [this, Subgroup.card_bot] at hi3
      omega
    have hh₀H : (h₀ : MulAut W) ∈ H := h₀.2
    have hh₀1' : (h₀ : MulAut W) ≠ 1 := fun h => hh₀1 (Subtype.ext h)
    have hzp : Subgroup.zpowers (h₀ : MulAut W) ≤ H := (Subgroup.zpowers_le).2 hh₀H
    have hzp1 : Subgroup.zpowers (h₀ : MulAut W) ≠ ⊥ := fun h =>
      hh₀1' ((Subgroup.zpowers_eq_bot).1 h)
    have hzpodd : Odd (Nat.card (Subgroup.zpowers (h₀ : MulAut W))) :=
      Odd.of_dvd_nat hHh.2.2.2.1 (Subgroup.card_dvd_of_le hzp)
    have hUK : ∀ K ∈ Ω, K ≠ H → fixV K ≤ commSub (⊤ : Subgroup W) H ⊔ fixV G := by
      intro K hK hKH
      have hinv : ∀ b ∈ Subgroup.zpowers (h₀ : MulAut W), ∀ m ∈ fixV K, b m ∈ fixV K := by
        intro b hb m hm
        have h1 : (h₀ : MulAut W) ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.2 (hrangeN h₀ hh₀ K hK)
        exact fixV_stable_of_normalizer ((Subgroup.zpowers_le.2 h1) hb) hm
      obtain ⟨hdec, -⟩ := B1.coprime_decomp hW hzpodd (M := fixV K) hinv
      have h1 : fixV K ⊓ fixV (Subgroup.zpowers (h₀ : MulAut W)) = fixV G := by
        rw [fixV_eq_of_le hW hHh hzp hzp1, hT.fixV_inf_eq hW hX₀ hY₀ hnc hK hH hKH]
      have h2 : commSub (fixV K) (Subgroup.zpowers (h₀ : MulAut W)) ≤
          commSub (⊤ : Subgroup W) H := by
        rw [← commSub_eq_of_le hW hHh hzp hzp1]
        exact commSub_mono le_top le_rfl
      calc fixV K = _ := hdec.symm
        _ ≤ _ := by
          rw [h1]
          exact sup_le le_sup_right (h2.trans le_sup_left)
    let S : Subgroup (MulAut W) := φ.range.map H.subtype
    have hSH : S ≤ H := by
      rintro _ ⟨r, -, rfl⟩
      exact r.2
    have hcardS : Nat.card S = Nat.card φ.range :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hfree : ∀ K ∈ Ω, K ≠ H →
        Nat.card S * Nat.card (fixV G) + Nat.card (fixV G) ≤ Nat.card (fixV K) := by
      intro K hK hKH
      refine card_mul_add_le_of_free hW hHh hSH (fun c hc z hz => hc z ((hT.hyp K hK).1.1 hz))
        ?_ (fun s hs c hc => hc s (hHh.1 (hSH hs))) ?_ ?_
      · rintro _ ⟨r, hr, rfl⟩ m hm
        exact fixV_stable_of_normalizer
          (Subgroup.mem_normalizer_iff_map_conj_eq.2 (hrangeN r hr K hK)) hm
      · exact hT.fixV_inf_eq hW hX₀ hY₀ hnc hK hH hKH
      · by_contra hall
        push Not at hall
        have h1 : fixV K ≤ fixV H := fun v hv => by
          have h2 := hall v hv
          exact fun z hz => h2 z (hHh.1 hz)
        have h3 : Nat.card (fixV K) = Nat.card (fixV H) := by
          obtain ⟨g, -, rfl⟩ := hT.trans H hH K hK
          rw [fixV_map_conj, Subgroup.card_map_of_injective g.injective]
        exact hKH (eq_of_fixV_eq hW (hT.hyp K hK).1 hHh
          (Subgroup.eq_of_le_of_card_ge h1 h3.ge))
    have hbot : commSub (⊤ : Subgroup W) H ⊓ fixV G = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hw1, hw2⟩
      have h1 : w ∈ fixV H ⊓ commSub ⊤ H := ⟨fun z hz => hw2 z (hHh.1 hz), hw1⟩
      rwa [fixV_inf_commSub_eq_bot' hW hHh.2.2.2.1] at h1
    have hT12 : Nat.card (fixV K₁) * Nat.card (fixV K₂) ≤
        Nat.card (commSub (⊤ : Subgroup W) H) * Nat.card (fixV G) * Nat.card (fixV G) := by
      have h1 := card_sup_mul_card_inf (fixV K₁) (fixV K₂)
      rw [hT.fixV_inf_eq hW hX₀ hY₀ hnc hK₁ hK₂ hK₁₂] at h1
      have h2 := Subgroup.card_le_of_le (sup_le (hUK K₁ hK₁ hK₁H) (hUK K₂ hK₂ hK₂H))
      rw [card_sup_of_inf_eq_bot hbot] at h2
      rw [← h1]
      exact Nat.mul_le_mul_right _ h2
    have hK₁₂c : Nat.card (fixV K₂) = Nat.card (fixV K₁) := by
      obtain ⟨g, -, rfl⟩ := hT.trans K₁ hK₁ K₂ hK₂
      rw [fixV_map_conj, Subgroup.card_map_of_injective g.injective]
    have hf1 := hfree K₁ hK₁ hK₁H
    rw [hcardS] at hf1
    rw [hK₁₂c] at hT12
    set i := Nat.card φ.range
    set c := Nat.card ↥(H ⊓ Subgroup.centralizer {t})
    set c0 := Nat.card (fixV G)
    set F := Nat.card (fixV K₁)
    have hc0 : 0 < c0 := Nat.card_pos
    have hq : Nat.card (commSub (⊤ : Subgroup W) H) = c * i + 1 := by rw [hcH, ← hkr]
    rw [hq] at hsq hT12
    have e1 : (i + 1) * c0 ≤ F := by nlinarith
    have e2 : (i + 1) * (i + 1) * (c0 * c0) ≤ (c * i + 1) * (c0 * c0) := by
      calc (i + 1) * (i + 1) * (c0 * c0) = ((i + 1) * c0) * ((i + 1) * c0) := by ring
        _ ≤ F * F := Nat.mul_le_mul e1 e1
        _ ≤ (c * i + 1) * c0 * c0 := hT12
        _ = (c * i + 1) * (c0 * c0) := by ring
    have e3 : (i + 1) * (i + 1) ≤ c * i + 1 := Nat.le_of_mul_le_mul_right e2 (by positivity)
    have hi0 : 0 < i := Nat.card_pos
    have e4 : i * (i + 2) ≤ i * c := by nlinarith
    have e5 : c * (c + 2) ≤ c * i := by nlinarith
    have e6 := Nat.le_of_mul_le_mul_left e4 hi0
    have e7 := Nat.le_of_mul_le_mul_left e5 hc1
    omega

end Pf

end Asc81c

end CFSG.Quasithin
