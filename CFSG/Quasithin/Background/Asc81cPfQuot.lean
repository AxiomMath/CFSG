module

public import CFSG.Quasithin.Background.Asc81cPfTrans2

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W]

section Act

theorem map_fixV_eq_self {H : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ H) :
    (fixV H).map (g : W →* W) = fixV H := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : g w = w := hw g hg
    show g w ∈ fixV H
    rw [h1]
    exact hw
  · intro hv
    exact ⟨v, hv, hv g hg⟩

@[expose] noncomputable def quoAct (H : Subgroup (MulAut W)) : H →* MulAut (W ⧸ fixV H) where
  toFun g := QuotientGroup.congr (fixV H) (fixV H) (g : MulAut W) (map_fixV_eq_self g.2)
  map_one' := by
    ext q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  map_mul' g h := by
    ext q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

theorem quoAct_mk (H : Subgroup (MulAut W)) (g : H) (w : W) :
    quoAct H g (w : W ⧸ fixV H) = ((g : MulAut W) w : W ⧸ fixV H) := rfl

theorem mul_self_eq_one_of_quoAct (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} {g : H}
    (hg : quoAct H g = 1) : (g : MulAut W) * g = 1 := by
  ext w
  have h1 : quoAct H g (w : W ⧸ fixV H) = w := by rw [hg]; rfl
  rw [quoAct_mk] at h1
  have hc : ((g : MulAut W) w)⁻¹ * w ∈ fixV H := QuotientGroup.eq.1 h1
  have hgc : (g : MulAut W) (((g : MulAut W) w)⁻¹ * w) = ((g : MulAut W) w)⁻¹ * w :=
    hc g g.2
  rw [map_mul, map_inv] at hgc
  rw [MulAut.mul_apply, MulAut.one_apply]
  have h2 : (g : MulAut W) ((g : MulAut W) w) = ((g : MulAut W) w) * ((g : MulAut W) w)⁻¹ *
      ((g : MulAut W) ((g : MulAut W) w)) := by group
  calc (g : MulAut W) ((g : MulAut W) w)
      = ((g : MulAut W) ((g : MulAut W) w))⁻¹ * ((g : MulAut W) ((g : MulAut W) w)) ^ 2 := by
        rw [pow_two]; group
    _ = ((g : MulAut W) ((g : MulAut W) w))⁻¹ := by rw [hW, mul_one]
    _ = w := by
        have h3 : ((g : MulAut W) ((g : MulAut W) w))⁻¹ * (g : MulAut W) w =
            ((g : MulAut W) w)⁻¹ * w := hgc
        have h4 := congrArg (fun z => z * ((g : MulAut W) w)⁻¹) h3
        simp only [mul_assoc, mul_inv_cancel, mul_one] at h4
        rw [h4]
        calc ((g : MulAut W) w)⁻¹ * (w * ((g : MulAut W) w)⁻¹)
            = w * (((g : MulAut W) w)⁻¹) ^ 2 := by rw [pow_two, mul_left_comm]
          _ = w := by rw [hW, mul_one]

theorem quoAct_mk_eq_iff (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} {g : H}
    (hodd : Odd (orderOf (g : MulAut W))) (w : W) :
    quoAct H g (w : W ⧸ fixV H) = w ↔ (g : MulAut W) w = w := by
  rw [quoAct_mk]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hc : ((g : MulAut W) w)⁻¹ * w ∈ fixV H := QuotientGroup.eq.1 h
  set c := ((g : MulAut W) w)⁻¹ * w with hcdef
  have hgc : (g : MulAut W) c = c := hc g g.2
  have hgw : (g : MulAut W) w = w * c⁻¹ := by rw [hcdef]; group
  have hpow : ∀ k : ℕ, ((g : MulAut W) ^ k) w = w * c⁻¹ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, map_inv, hgc, hgw, pow_succ',
        mul_assoc]
  obtain ⟨j, hj⟩ := hodd
  have h1 := hpow (orderOf (g : MulAut W))
  rw [pow_orderOf_eq_one, MulAut.one_apply, hj, pow_succ, pow_mul, hW, one_pow, one_mul] at h1
  have h2 : c⁻¹ = 1 := by
    have := congrArg (fun z => w⁻¹ * z) h1
    simpa using this.symm
  rw [hgw, h2, mul_one]

end Act

section Crit

variable [Finite W]

@[expose] def critSub (H : Subgroup (MulAut W)) (g₁ g₂ u : H) : Subgroup (W ⧸ fixV H) where
  carrier := {q | ∃ d, quoAct H g₁ d = d ∧ quoAct H g₂ d = d ∧
    ∃ p, q = d * (p * (quoAct H u p)⁻¹)}
  one_mem' := ⟨1, map_one _, map_one _, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨d, hd1, hd2, p, rfl⟩ ⟨d', hd1', hd2', p', rfl⟩
    refine ⟨d * d', by rw [map_mul, hd1, hd1'], by rw [map_mul, hd2, hd2'], p * p', ?_⟩
    rw [map_mul, mul_inv]
    simp only [mul_assoc, mul_left_comm]
  inv_mem' := by
    rintro _ ⟨d, hd1, hd2, p, rfl⟩
    refine ⟨d⁻¹, by rw [map_inv, hd1], by rw [map_inv, hd2], p⁻¹, ?_⟩
    rw [map_inv, mul_inv, mul_inv, inv_inv]

theorem rkIdx_le_two {Γ : Type*} [Group Γ] {K : Subgroup Γ} (h0 : K.index ≠ 0)
    (h : K.index ≤ 4) : rkIdx K ≤ 2 := by
  unfold rkIdx
  by_contra hlt
  push Not at hlt
  have h1 : 2 ^ padicValNat 2 K.index ∣ K.index := pow_padicValNat_dvd
  have h2 : 2 ^ 3 ≤ 2 ^ padicValNat 2 K.index := Nat.pow_le_pow_right (by norm_num) hlt
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h1
  omega

theorem rkIdx_fixV_le_critSub (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} {g₁ g₂ u : H}
    (hu : (u : MulAut W) * u = 1) (h₁ : Odd (orderOf (g₁ : MulAut W)))
    (h₂ : Odd (orderOf (g₂ : MulAut W))) (hu₁₂ : u ∈ Subgroup.closure {g₁, g₂}) :
    rkIdx (fixV (Subgroup.zpowers (u : MulAut W))) ≤ rkIdx (critSub H g₁ g₂ u) := by
  set S := (critSub H g₁ g₂ u).comap (QuotientGroup.mk' (fixV H)) with hS
  have hSidx : S.index = (critSub H g₁ g₂ u).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hle : S ≤ fixV (Subgroup.zpowers (u : MulAut W)) := by
    intro w hw
    obtain ⟨d, hd1, hd2, p, hp⟩ := hw
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective p
    have hv1 : (g₁ : MulAut W) v = v := (quoAct_mk_eq_iff hW h₁ v).1 hd1
    have hv2 : (g₂ : MulAut W) v = v := (quoAct_mk_eq_iff hW h₂ v).1 hd2
    have huv : (u : MulAut W) v = v := by
      have key : ∀ g ∈ Subgroup.closure ({g₁, g₂} : Set H), (g : MulAut W) v = v := by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem g hg =>
          rcases hg with rfl | rfl
          · exact hv1
          · exact hv2
        | one => rfl
        | mul a b _ _ ha hb => rw [Subgroup.coe_mul, MulAut.mul_apply, hb, ha]
        | inv a _ ha =>
          rw [Subgroup.coe_inv]
          calc ((a : MulAut W))⁻¹ v = ((a : MulAut W))⁻¹ ((a : MulAut W) v) := by rw [ha]
            _ = v := MulAut.inv_apply_self _ _ _
      exact key u hu₁₂
    have hw' : (w : W ⧸ fixV H) = ((v * (r * ((u : MulAut W) r)⁻¹) : W) : W ⧸ fixV H) := by
      rw [show ((QuotientGroup.mk' (fixV H)) w : W ⧸ fixV H) = (w : W ⧸ fixV H) from rfl] at hp
      rw [hp, quoAct_mk]
      rfl
    have hc : w⁻¹ * (v * (r * ((u : MulAut W) r)⁻¹)) ∈ fixV H := QuotientGroup.eq.1 hw'
    have huc := hc u u.2
    have hur : (u : MulAut W) ((u : MulAut W) r) = r := by
      rw [← MulAut.mul_apply, hu, MulAut.one_apply]
    have hinv : ∀ z : W, z⁻¹ = z := fun z => by
      have h := hW z
      rw [pow_two] at h
      exact inv_eq_of_mul_eq_one_right h
    have hus : (u : MulAut W) (v * (r * ((u : MulAut W) r)⁻¹)) =
        v * (r * ((u : MulAut W) r)⁻¹) := by
      rw [map_mul, map_mul, map_inv, huv, hur]
      congr 1
      rw [← hinv (r * ((u : MulAut W) r)⁻¹), mul_inv_rev, inv_inv]
    have huw : (u : MulAut W) w = w := by
      rw [map_mul, map_inv, hus] at huc
      exact inv_injective (mul_right_cancel huc)
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have : ∀ k : ℕ, ((u : MulAut W) ^ k) w = w := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, huw]
    rcases k with k | k
    · simpa using this k
    · rw [zpow_negSucc]
      calc (((u : MulAut W) ^ (k + 1))⁻¹) w = (((u : MulAut W) ^ (k + 1))⁻¹)
            (((u : MulAut W) ^ (k + 1)) w) := by rw [this]
        _ = w := MulAut.inv_apply_self _ _ _
  have h1 := rkIdx_anti hle
  unfold rkIdx at h1 ⊢
  rwa [hSidx] at h1

end Crit

section Ord3

variable [Finite W] {G X Y : Subgroup (MulAut W)}

theorem index_fixV_eq_four (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hX3 : Nat.card X = 3) :
    (fixV X).index = 4 ∧ rk (commSub (⊤ : Subgroup W) X) = 2 := by
  have h4 : Nat.card (commSub (⊤ : Subgroup W) X) = 4 := by rw [card_commSub hX, hX3]
  refine ⟨?_, by rw [rk, h4, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]⟩
  have h1 := card_fixV_mul_card_commSub hW hX.2.2.2.1
  have h2 := (fixV X).card_mul_index
  rw [h4] at h1
  have hpos : 0 < Nat.card (fixV X) := Nat.card_pos
  rw [← h2] at h1
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

theorem index_fixV_sup_le (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (hX3 : Nat.card X = 3) (hY3 : Nat.card Y = 3) : (fixV (X ⊔ Y)).index ≤ 16 := by
  rw [fixV_sup]
  have h := Subgroup.index_inf_le (H := fixV X) (K := fixV Y)
  rw [(index_fixV_eq_four hW hX hX3).1, (index_fixV_eq_four hW hY hY3).1] at h
  exact h

theorem eight_le_index_fixV_sup (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (hX3 : Nat.card X = 3) (hY3 : Nat.card Y = 3) (hXY : X ≠ Y) : 8 ≤ (fixV (X ⊔ Y)).index := by
  have hQ : ∀ q : W ⧸ fixV (X ⊔ Y), q ^ 2 = 1 := fun q => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hW, QuotientGroup.mk_one]
  have hpow : (fixV (X ⊔ Y)).index = 2 ^ rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) := by
    rw [Subgroup.index_eq_card, ← card_eq_two_pow hQ ⊤, Subgroup.card_top]
  have hle : ∀ Z : Subgroup (MulAut W), Hyp101 G Z → Nat.card Z = 3 → fixV (X ⊔ Y) ≤ fixV Z →
      (fixV (X ⊔ Y)).index = 4 → fixV (X ⊔ Y) = fixV Z := by
    intro Z hZ hZ3 hle h4
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := (fixV Z).card_mul_index
    have h2 := (fixV (X ⊔ Y)).card_mul_index
    rw [(index_fixV_eq_four hW hZ hZ3).1] at h1
    rw [h4] at h2
    omega
  have hXle : fixV (X ⊔ Y) ≤ fixV X := by rw [fixV_sup]; exact inf_le_left
  have hYle : fixV (X ⊔ Y) ≤ fixV Y := by rw [fixV_sup]; exact inf_le_right
  have h4le : 4 ≤ (fixV (X ⊔ Y)).index := by
    have h1 := Subgroup.index_dvd_of_le hXle
    rw [(index_fixV_eq_four hW hX hX3).1] at h1
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hne4 : (fixV (X ⊔ Y)).index ≠ 4 := fun h4 =>
    hXY (eq_of_fixV_eq hW hX hY ((hle X hX hX3 hXle h4).symm.trans (hle Y hY hY3 hYle h4)))
  rw [hpow] at h4le hne4 ⊢
  by_contra hlt
  push Not at hlt
  have h1 : rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y))) < 3 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
    omega
  interval_cases (rk (⊤ : Subgroup (W ⧸ fixV (X ⊔ Y)))) <;> simp_all

theorem quoAct_injective_of_le (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    (hX : Hyp102 G X) (hX3 : Nat.card X = 3) (hHG : H ≤ G) (hXH : X ≤ H)
    (hidx16 : (fixV H).index ≤ 16) : Function.Injective (quoAct H) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hq2 : (q : MulAut W) * q = 1 := mul_self_eq_one_of_quoAct hW hq
  have hqw : ∀ w : W, ((q : MulAut W) w)⁻¹ * w ∈ fixV H := fun w => by
    have h1 : quoAct H q (w : W ⧸ fixV H) = w := by rw [hq]; rfl
    rw [quoAct_mk] at h1
    exact QuotientGroup.eq.1 h1
  have hfix : ∀ Z : Subgroup (MulAut W), Z ≤ H → Hyp101 G Z →
      ∀ w ∈ commSub (⊤ : Subgroup W) Z, (q : MulAut W) w = w := by
    intro Z hZH hZ
    have hCZ : fixV H ≤ fixV Z := fun v hv z hz => hv z (hZH hz)
    have hqZ : ∀ v ∈ fixV Z, (q : MulAut W) v ∈ fixV Z := fun v hv => by
      have h1 : (q : MulAut W) v = v * (((q : MulAut W) v)⁻¹ * v)⁻¹ := by group
      rw [h1]
      exact (fixV Z).mul_mem hv ((fixV Z).inv_mem (hCZ (hqw v)))
    have hmap : (fixV Z).map (q : MulAut W).toMonoidHom = fixV Z := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hqZ w hw
      · intro hv
        refine ⟨(q : MulAut W) v, hqZ v hv, ?_⟩
        show (q : MulAut W) ((q : MulAut W) v) = v
        rw [← MulAut.mul_apply, hq2, MulAut.one_apply]
    have hcomm : ∀ z ∈ Z, (q : MulAut W) * z = z * q := by
      intro z hz
      have hconj := hZ.2.2.2.2.2 q (hHG q.2) hmap z hz
      have hk : (q : MulAut W) * z * (q : MulAut W)⁻¹ * z⁻¹ ∈ Z := Z.mul_mem hconj (Z.inv_mem hz)
      have hzH : z ∈ H := hZH hz
      have hkq : quoAct H (q * ⟨z, hzH⟩ * q⁻¹ * ⟨z, hzH⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hq, one_mul, inv_one, mul_one,
          mul_inv_cancel]
      have hk2 := mul_self_eq_one_of_quoAct hW hkq
      have hk1 : (q : MulAut W) * z * (q : MulAut W)⁻¹ * z⁻¹ = 1 :=
        eq_one_of_mul_self_eq_one (odd_orderOf_of_mem hZ.2.2.2.1 hk) hk2
      calc (q : MulAut W) * z = (q : MulAut W) * z * (q : MulAut W)⁻¹ * z⁻¹ * (z * q) := by group
        _ = z * q := by rw [hk1, one_mul]
    intro w hw
    have h1 : (q : MulAut W) w ∈ commSub (⊤ : Subgroup W) Z := commSub_stable_of_commute hcomm hw
    have h2 : ((q : MulAut W) w)⁻¹ * w ∈ fixV Z ⊓ commSub ⊤ Z :=
      ⟨hCZ (hqw w), (commSub ⊤ Z).mul_mem ((commSub ⊤ Z).inv_mem h1) hw⟩
    rw [fixV_inf_commSub_eq_bot' hW hZ.2.2.2.1, Subgroup.mem_bot] at h2
    have := congrArg (fun z => (q : MulAut W) w * z) h2
    simpa using this.symm
  by_contra hq1
  have hq1' : (q : MulAut W) ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hord : orderOf (q : MulAut W) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hq2) hq1'
  have hm := mParam_le_of_orderOf_two (hHG q.2) hord
  have hle : fixV H ⊔ commSub ⊤ X ≤ fixV (Subgroup.zpowers (q : MulAut W)) := by
    refine sup_le (fun v hv z hz => ?_) (fun w hw z hz => ?_)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (mem_fixV_zpowers (hv q q.2)) _ ⟨k, rfl⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (mem_fixV_zpowers (hfix X hXH hX.1 w hw)) _ ⟨k, rfl⟩
  have hbot : fixV H ⊓ commSub ⊤ X = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ fixV X ⊓ commSub ⊤ X := ⟨fun x hx => hv.1 x (hXH hx), hv.2⟩
    rwa [fixV_inf_commSub_eq_bot' hW hX.1.2.2.2.1] at h1
  have hcard := card_sup_mul_card_inf (fixV H) (commSub (⊤ : Subgroup W) X)
  rw [hbot, Subgroup.card_bot, mul_one, card_commSub hX.1, hX3] at hcard
  have hidx : (fixV H ⊔ commSub ⊤ X).index ≤ 4 := by
    have h1 := (fixV H ⊔ commSub ⊤ X).card_mul_index
    have h2 := (fixV H).card_mul_index
    have h3 : (fixV H).index ≤ 16 := hidx16
    have hpos : 0 < Nat.card (fixV H) := Nat.card_pos
    rw [hcard, ← h2] at h1
    have h5 : (3 + 1) * (fixV H ⊔ commSub ⊤ X).index = (fixV H).index := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [← mul_assoc]
      exact h1
    omega
  have h1 := rkIdx_anti hle
  have h2 := rkIdx_le_two Subgroup.index_ne_zero_of_finite hidx
  have h3 := hX.2
  rw [(index_fixV_eq_four hW hX.1 hX3).2] at h3
  omega

theorem quoAct_injective (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp102 G X) (hY : Hyp102 G Y)
    (hX3 : Nat.card X = 3) (hY3 : Nat.card Y = 3) : Function.Injective (quoAct (X ⊔ Y)) :=
  quoAct_injective_of_le hW hX hX3 (sup_le hX.1.1 hY.1.1) le_sup_left
    (index_fixV_sup_le hW hX.1 hY.1 hX3 hY3)

end Ord3

end Pf

end Asc81c

end CFSG.Quasithin
