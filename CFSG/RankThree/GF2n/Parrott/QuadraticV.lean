module

public import CFSG.RankThree.GF2n.Parrott.ActionV

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem sq_eq_one_of_mem_card_two {A : Subgroup G} (hA : Nat.card A = 2) {a : G}
    (ha : a ∈ A) : a * a = 1 := by
  have h1 : (⟨a, ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
  rw [hA] at h1
  have := congrArg Subtype.val h1
  simpa [pow_two] using this

theorem center_map_eq_zpowers (h : Tim79a.ParrottHyp z) {T F : Subgroup G}
    (hTF : T ⊔ F = J z) (hF : IsExtraspecial2 F) :
    (Subgroup.center F).map F.subtype = Subgroup.zpowers z := by
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  have hF_le : F ≤ J z := hTF ▸ le_sup_right
  have hFF_le : ⁅F, F⁆ ≤ Subgroup.zpowers z := by
    rw [← hJcomm]
    exact Subgroup.commutator_mono hF_le hF_le
  have hcard : Nat.card ↥(Subgroup.zpowers z) ≤ Nat.card ↥⁅F, F⁆ := by
    rw [Nat.card_zpowers, h.1, hF.2.2]
  have hFF_eq : ⁅F, F⁆ = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hFF_le hcard
  rw [← hF.2.1]
  exact hFF_eq

theorem sq_mem_zpowers_z (h : Tim79a.ParrottHyp z) {x : G} (hx : x ∈ J z) :
    x * x ∈ Subgroup.zpowers z := by
  have hpar := h
  obtain ⟨-, ⟨T, F, hT, hF, hFc, hdisj, hcomm, hsup⟩, -, -, -⟩ := h
  have hTF : T ⊔ F = J z := by simpa [J, H] using hsup
  have hcenter := center_map_eq_zpowers hpar hTF hF
  rw [J_eq_sup_T_F hpar hTF] at hx
  obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have ht2 : t * t = 1 := sq_eq_one_of_mem_card_two hT ht
  have hff : f * f ∈ (Subgroup.center F).map F.subtype :=
    CFSG.IsExtraspecial2.mul_self_mem_center_map hF hf
  have heq : (t * f) * (t * f) = f * f := by
    have htf : Commute t f := hcomm t ht f hf
    calc (t * f) * (t * f) = t * (f * (t * f)) := by rw [mul_assoc]
      _ = t * ((f * t) * f) := by rw [mul_assoc]
      _ = t * ((t * f) * f) := by rw [htf.eq]
      _ = (t * t) * (f * f) := by group
      _ = f * f := by rw [ht2, one_mul]
  rw [heq, ← hcenter]
  exact hff

theorem commutator_mem_zpowers_z (h : Tim79a.ParrottHyp z) {x y : G}
    (hx : x ∈ J z) (hy : y ∈ J z) : ⁅x, y⁆ ∈ Subgroup.zpowers z := by
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  rw [← hJcomm]
  exact Subgroup.commutator_mem_commutator hx hy

theorem sq_eq_one_of_mem_zpowers (h : Tim79a.ParrottHyp z) {a : G}
    (ha : a ∈ Subgroup.zpowers z) : a * a = 1 := by
  have hdvd : orderOf a ∣ 2 := by
    have hdvd0 := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) ha
    rwa [Nat.card_zpowers, h.1] at hdvd0
  have h2 : a ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  simpa [pow_two] using h2

theorem zpowers_commute (h : Tim79a.ParrottHyp z) {a b : G}
    (ha : a ∈ Subgroup.zpowers z) (hb : b ∈ Subgroup.zpowers z) : a * b = b * a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

theorem zpowers_centralizes_J (h : Tim79a.ParrottHyp z) {a : G}
    (ha : a ∈ Subgroup.zpowers z) : a ∈ Subgroup.centralizer (J z) :=
  Subgroup.zpowers_le_of_mem (z_centralizes_J h) ha

theorem zpowers_centralizes_H (h : Tim79a.ParrottHyp z) {a : G}
    (ha : a ∈ Subgroup.zpowers z) : a ∈ Subgroup.centralizer (H z) :=
  Subgroup.zpowers_le_of_mem (z_centralizes_H h) ha

@[expose] def qJ (h : Tim79a.ParrottHyp z) (x : J z) : Subgroup.zpowers z :=
  ⟨(x : G) ^ 2, by simpa [pow_two] using sq_mem_zpowers_z h x.2⟩

@[simp] theorem qJ_coe (h : Tim79a.ParrottHyp z) (x : J z) :
    ((qJ h x : Subgroup.zpowers z) : G) = (x : G) ^ 2 := rfl

theorem qJ_eq_of_mem_centerIn (h : Tim79a.ParrottHyp z) {a b : J z}
    (hb : ((a⁻¹ * b : J z) : G) ∈ centerIn (J z)) : qJ h a = qJ h b := by
  let c : J z := a⁻¹ * b
  have hc : (c : G) ∈ centerIn (J z) := hb
  have hbc : b = a * c := by
    show b = a * (a⁻¹ * b)
    group
  have hca : (c : G) * (a : G) = (a : G) * (c : G) :=
    (Subgroup.mem_centralizer_iff.mp hc.2 (a : G) a.2).symm
  have hc2 : (c : G) * (c : G) = 1 := centerIn_J_sq h hc
  have hsq : ((a * c : J z) : G) ^ 2 = (a : G) ^ 2 := by
    rw [Subgroup.coe_mul]
    calc ((a : G) * (c : G)) ^ 2 = (a : G) * (c : G) * ((a : G) * (c : G)) := by
          rw [pow_two]
      _ = (a : G) * ((c : G) * ((a : G) * (c : G))) := by rw [mul_assoc]
      _ = (a : G) * (((c : G) * (a : G)) * (c : G)) := by rw [mul_assoc]
      _ = (a : G) * (((a : G) * (c : G)) * (c : G)) := by rw [hca]
      _ = ((a : G) * (a : G)) * ((c : G) * (c : G)) := by group
      _ = (a : G) * (a : G) := by rw [hc2, mul_one]
      _ = (a : G) ^ 2 := by rw [pow_two]
  rw [hbc]
  apply Subtype.ext
  rw [qJ_coe, qJ_coe]
  exact hsq.symm

@[expose] noncomputable def qV (h : Tim79a.ParrottHyp z) (v : QuotientV.V z) :
    Subgroup.zpowers z :=
  Quotient.lift (fun x : J z => qJ h x) (by
    intro a b hab
    exact qJ_eq_of_mem_centerIn h
      (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))) v

@[simp] theorem qV_pi (h : Tim79a.ParrottHyp z) (x : J z) :
    qV h (QuotientV.pi z x) = qJ h x := rfl

@[simp] theorem qV_pi_coe (h : Tim79a.ParrottHyp z) (x : J z) :
    ((qV h (QuotientV.pi z x) : Subgroup.zpowers z) : G) = (x : G) ^ 2 := rfl

private theorem mul_sq_of_commute {x y : G} (h : Commute x ⁅y, x⁆) :
    (x * y) ^ 2 = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by
  have hyx : y * x = ⁅y, x⁆ * x * y := by
    rw [commutatorElement_def]
    group
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [hyx]
    _ = (x * ⁅y, x⁆) * (x * y * y) := by group
    _ = (⁅y, x⁆ * x) * (x * y * y) := by rw [h.eq]
    _ = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group

theorem qJ_mul (h : Tim79a.ParrottHyp z) (x y : J z) :
    qJ h (x * y) = qJ h x * qJ h y *
      ⟨⁅(x : G), (y : G)⁆, commutator_mem_zpowers_z h x.2 y.2⟩ := by
  let c : G := ⁅(x : G), (y : G)⁆
  have hcZ : c ∈ Subgroup.zpowers z := commutator_mem_zpowers_z h x.2 y.2
  have hcC : c ∈ centerIn (J z) := commutator_mem_centerIn_J h x.2 y.2
  have hxc : (x : G) * c = c * (x : G) :=
    Subgroup.mem_centralizer_iff.mp hcC.2 (x : G) x.2
  have hyc : (y : G) * c = c * (y : G) :=
    Subgroup.mem_centralizer_iff.mp hcC.2 (y : G) y.2
  have hc2 : c * c = 1 := centerIn_J_sq h hcC
  have hcomm_inv : ⁅(y : G), (x : G)⁆ = c⁻¹ := by
    simp only [c, commutatorElement_def]
    group
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hxcomm : Commute (x : G) ⁅(y : G), (x : G)⁆ := by
    rw [hcomm_inv, hc_inv]
    exact hxc
  have hcx2 : Commute c ((x : G) ^ 2) := (Commute.symm hxc).pow_right 2
  have hcy2 : Commute c ((y : G) ^ 2) := (Commute.symm hyc).pow_right 2
  have hcx2y2 : Commute c ((x : G) ^ 2 * (y : G) ^ 2) := hcx2.mul_right hcy2
  have hmul : ((x : G) * (y : G)) ^ 2 = c * (x : G) ^ 2 * (y : G) ^ 2 := by
    calc ((x : G) * (y : G)) ^ 2 = ⁅(y : G), (x : G)⁆ * (x : G) ^ 2 * (y : G) ^ 2 :=
          mul_sq_of_commute hxcomm
      _ = c * (x : G) ^ 2 * (y : G) ^ 2 := by rw [hcomm_inv, hc_inv]
  have hfinal : ((x : G) * (y : G)) ^ 2 = (x : G) ^ 2 * (y : G) ^ 2 * c := by
    calc ((x : G) * (y : G)) ^ 2 = c * (x : G) ^ 2 * (y : G) ^ 2 := hmul
      _ = c * ((x : G) ^ 2 * (y : G) ^ 2) := by group
      _ = ((x : G) ^ 2 * (y : G) ^ 2) * c := hcx2y2.eq
  apply Subtype.ext
  simp only [Subgroup.coe_mul, qJ_coe]
  exact hfinal

private theorem mul_self_mul_self_mul_eq_of_comm {A : Type} [Group A] (a b c : A)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha : a * a = 1) (hb : b * b = 1) : a * b * c * a * b = c := by
  have habc : (a * b) * c = c * (a * b) :=
    (Commute.mul_left (show Commute a c from hac) (show Commute b c from hbc)).eq
  have hsq_comm : c * ((a * b) * (a * b)) = ((a * b) * (a * b)) * c := by
    exact ((Commute.symm habc).mul_right (Commute.symm habc)).eq
  calc a * b * c * a * b = (a * b) * c * (a * b) := by group
    _ = (a * b) * (a * b) * c := by
          calc (a * b) * c * (a * b) = c * ((a * b) * (a * b)) := by
                rw [habc]
                group
            _ = ((a * b) * (a * b)) * c := hsq_comm
    _ = (a * a) * (b * b) * c := by
          rw [show (a * b) * (a * b) = (a * b) ^ 2 by rw [pow_two],
            Commute.mul_pow (show Commute a b from hab) 2, pow_two, pow_two]
    _ = c := by rw [ha, hb, one_mul, one_mul]

private theorem mul_mul_mul_self_mul_self {A : Type} [Group A] (a b c : A)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha : a * a = 1) (hb : b * b = 1) : a * b * (c * a * b) = c := by
  calc a * b * (c * a * b) = a * b * c * a * b := by group
    _ = c := mul_self_mul_self_mul_eq_of_comm a b c hab hac hbc ha hb

@[expose] noncomputable def polarV (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) : Subgroup.zpowers z :=
  qV h (v * w) * qV h v * qV h w

theorem polarV_pi (h : Tim79a.ParrottHyp z) (x y : J z) :
    polarV h (QuotientV.pi z x) (QuotientV.pi z y) =
      ⟨⁅(x : G), (y : G)⁆, commutator_mem_zpowers_z h x.2 y.2⟩ := by
  unfold polarV
  rw [← map_mul (QuotientV.pi z) x y, qV_pi, qV_pi, qV_pi, qJ_mul]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_mk]
  exact mul_self_mul_self_mul_eq_of_comm
    ((qJ h x : Subgroup.zpowers z) : G) ((qJ h y : Subgroup.zpowers z) : G)
    ⁅(x : G), (y : G)⁆
    (zpowers_commute h (qJ h x).2 (qJ h y).2)
    (zpowers_commute h (qJ h x).2 (commutator_mem_zpowers_z h x.2 y.2))
    (zpowers_commute h (qJ h y).2 (commutator_mem_zpowers_z h x.2 y.2))
    (sq_eq_one_of_mem_zpowers h (qJ h x).2)
    (sq_eq_one_of_mem_zpowers h (qJ h y).2)

theorem qJ_conj (h : Tim79a.ParrottHyp z) (g : H z) (x : J z) :
    qJ h (conjJ' z g x) = qJ h x := by
  have hx2Z : (x : G) ^ 2 ∈ Subgroup.zpowers z := by
    simpa [pow_two] using sq_mem_zpowers_z h x.2
  have hgx2 : Commute (g : G) ((x : G) ^ 2) := by
    exact Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h hx2Z) (g : G) g.2
  apply Subtype.ext
  change ((conjJ' z g x : J z) : G) ^ 2 = (x : G) ^ 2
  rw [conjJ'_apply_coe]
  calc ((g : G) * (x : G) * (g : G)⁻¹) ^ 2
      = (g : G) * (x : G) ^ 2 * (g : G)⁻¹ := by rw [conj_pow]
    _ = ((x : G) ^ 2) * (g : G) * (g : G)⁻¹ := by rw [hgx2.eq]
    _ = (x : G) ^ 2 := by group

theorem qV_conj (h : Tim79a.ParrottHyp z) (g : H z) (v : QuotientV.V z) :
    qV h (conjV h g v) = qV h v := by
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  rw [conjV_mk, qV_pi, qV_pi, qJ_conj]

noncomputable def zpowersEquivZModTwo (h : Tim79a.ParrottHyp z) :
    Subgroup.zpowers z ≃* Multiplicative (ZMod 2) :=
  (zmodMulEquivOfGenerator (G := Subgroup.zpowers z)
    (g := ⟨z, Subgroup.mem_zpowers z⟩) (by
      intro x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)
    (n := 2) (by rw [Nat.card_zpowers, h.1])).symm

@[simp] theorem zpowersEquivZModTwo_apply_z (h : Tim79a.ParrottHyp z) :
    zpowersEquivZModTwo h ⟨z, Subgroup.mem_zpowers z⟩ = Multiplicative.ofAdd 1 := by
  unfold zpowersEquivZModTwo
  simp

@[expose] noncomputable def qVZMod (h : Tim79a.ParrottHyp z) (v : QuotientV.V z) : ZMod 2 :=
  Multiplicative.toAdd (zpowersEquivZModTwo h (qV h v))

@[expose] noncomputable def polarVZMod (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) : ZMod 2 :=
  Multiplicative.toAdd (zpowersEquivZModTwo h (polarV h v w))

theorem qV_mul_polar (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) :
    qV h (v * w) = qV h v * qV h w * polarV h v w := by
  unfold polarV
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_mk]
  exact (mul_mul_mul_self_mul_self
    ((qV h v : Subgroup.zpowers z) : G) ((qV h w : Subgroup.zpowers z) : G)
    ((qV h (v * w) : Subgroup.zpowers z) : G)
    (zpowers_commute h (qV h v).2 (qV h w).2)
    (zpowers_commute h (qV h v).2 (qV h (v * w)).2)
    (zpowers_commute h (qV h w).2 (qV h (v * w)).2)
    (sq_eq_one_of_mem_zpowers h (qV h v).2)
    (sq_eq_one_of_mem_zpowers h (qV h w).2)).symm

theorem qVZMod_mul_add (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) :
    qVZMod h (v * w) = qVZMod h v + qVZMod h w + polarVZMod h v w := by
  unfold qVZMod polarVZMod
  rw [qV_mul_polar]
  simp only [map_mul, toAdd_mul]

theorem qVZMod_conj (h : Tim79a.ParrottHyp z) (g : H z) (v : QuotientV.V z) :
    qVZMod h (conjV h g v) = qVZMod h v := by
  unfold qVZMod
  rw [qV_conj]

theorem polarV_comm (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) :
    polarV h v w = polarV h w v := by
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  obtain ⟨y, rfl⟩ := QuotientV.pi_surjective z w
  rw [polarV_pi, polarV_pi]
  have hc2 : ⁅(x : G), (y : G)⁆ * ⁅(x : G), (y : G)⁆ = 1 :=
    sq_eq_one_of_mem_zpowers h (commutator_mem_zpowers_z h x.2 y.2)
  have hinv : ⁅(x : G), (y : G)⁆⁻¹ = ⁅(x : G), (y : G)⁆ :=
    inv_eq_of_mul_eq_one_right hc2
  apply Subtype.ext
  simp only [Subgroup.coe_mk]
  calc ⁅(x : G), (y : G)⁆ = (⁅(x : G), (y : G)⁆)⁻¹ := hinv.symm
    _ = ⁅(y : G), (x : G)⁆ := by
          rw [commutatorElement_def, commutatorElement_def]
          group

end CFSG.RankThree.GF2n.Parrott
