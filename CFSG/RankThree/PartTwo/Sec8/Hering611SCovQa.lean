module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpA

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

@[expose] def covW {P : Type*} [Group P] (Zh : Subgroup P) (hZc : Zh ≤ Subgroup.center P) :
    Subgroup P where
  carrier := {p | ∀ q : P, p * q * p⁻¹ * q⁻¹ ∈ Zh}
  mul_mem' := by
    intro a b ha hb q
    have hz : b * q * b⁻¹ * q⁻¹ ∈ Subgroup.center P := hZc (hb q)
    have hc : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ = b * q * b⁻¹ * q⁻¹ := by
      have := Subgroup.mem_center_iff.mp hz a
      rw [this]
      group
    have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
    show a * b * q * (a * b)⁻¹ * q⁻¹ ∈ Zh
    rw [e, hc]
    exact Zh.mul_mem (hb q) (ha q)
  one_mem' := fun q => by simpa using Zh.one_mem
  inv_mem' := by
    intro a ha q
    have hz : (a * q * a⁻¹ * q⁻¹)⁻¹ ∈ Subgroup.center P :=
      (Subgroup.center P).inv_mem (hZc (ha q))
    have hc : a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a = (a * q * a⁻¹ * q⁻¹)⁻¹ := by
      have := Subgroup.mem_center_iff.mp hz a⁻¹
      rw [this]
      group
    have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a := by group
    show a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ ∈ Zh
    rw [e, hc]
    exact Zh.inv_mem (ha q)

theorem mem_covW {P : Type*} [Group P] {Zh : Subgroup P} {hZc : Zh ≤ Subgroup.center P} {p : P} :
    p ∈ covW Zh hZc ↔ ∀ q : P, p * q * p⁻¹ * q⁻¹ ∈ Zh := Iff.rfl

structure CoverP (P : Type*) [Group P] (σ : MulAut P) (Zh : Subgroup P) : Prop where
  central : Zh ≤ Subgroup.center P
  card_Z : Nat.card Zh = 3
  card_P : Nat.card P = 81
  pgroup : IsPGroup 3 P
  nonab : ∃ x y : P, x * y * x⁻¹ * y⁻¹ ∉ Zh
  sigma_pow : σ ^ 8 = 1
  sigma_Z : ∀ z ∈ Zh, σ z = z
  singer : ∀ W : Subgroup P, Zh ≤ W → W.index = 3 → W.map (σ ^ 2).toMonoidHom ≠ W

variable {P : Type*} [Group P] [Finite P] {σ : MulAut P} {Zh : Subgroup P}

private theorem mk_comm_iff {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (a b : G) :
    (a : G ⧸ N) * (b : G ⧸ N) = (b : G ⧸ N) * (a : G ⧸ N) ↔ a * b * a⁻¹ * b⁻¹ ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

private theorem mem_covW_iff_mem_center [Zh.Normal] (hZc : Zh ≤ Subgroup.center P) (p : P) :
    p ∈ covW Zh hZc ↔ (p : P ⧸ Zh) ∈ Subgroup.center (P ⧸ Zh) := by
  rw [mem_covW, Subgroup.mem_center_iff]
  constructor
  · intro hp g
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
    exact ((mk_comm_iff Zh p q).mpr (hp q)).symm
  · intro hc q
    exact (mk_comm_iff Zh p q).mp (hc (q : P ⧸ Zh)).symm

private theorem covQ_card_quot (h : CoverP P σ Zh) : Nat.card (P ⧸ Zh) = 27 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Zh
  rw [h.card_P, h.card_Z] at h1
  omega

private theorem covQ_nonab [Zh.Normal] (h : CoverP P σ Zh) :
    ∃ a b : P ⧸ Zh, a * b ≠ b * a := by
  obtain ⟨x, y, hxy⟩ := h.nonab
  exact ⟨x, y, fun heq => hxy ((mk_comm_iff Zh x y).mp heq)⟩

private theorem conj_eq_of_mem_center {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (p : G) : p * z * p⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz p, mul_inv_cancel_right]

theorem Zh_le_covW (h : CoverP P σ Zh) : Zh ≤ covW Zh h.central := by
  intro z hz
  rw [mem_covW]
  intro q
  have hc : q * z = z * q := Subgroup.mem_center_iff.mp (h.central hz) q
  have e : z * q * z⁻¹ * q⁻¹ = 1 := by
    rw [← hc]
    group
  rw [e]
  exact Zh.one_mem

theorem covW_card (h : CoverP P σ Zh) : Nat.card (covW Zh h.central) = 9 := by
  haveI : Zh.Normal := Subgroup.normal_of_le_center h.central
  have hZ := CFSG.Quasithin.SzN31.card_center_eq_three_of_card_27 (covQ_card_quot h)
    (covQ_nonab h)
  have hidx : (covW Zh h.central).index = 9 := by
    have e : covW Zh h.central = (Subgroup.center (P ⧸ Zh)).comap (QuotientGroup.mk' Zh) := by
      ext p
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
      exact mem_covW_iff_mem_center h.central p
    rw [e, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Zh)]
    have h1 := Subgroup.card_mul_index (Subgroup.center (P ⧸ Zh))
    rw [hZ, covQ_card_quot h] at h1
    omega
  have h2 := Subgroup.card_mul_index (covW Zh h.central)
  rw [hidx, h.card_P] at h2
  omega

theorem commutator_mem_covW (h : CoverP P σ Zh) (x y : P) :
    x * y * x⁻¹ * y⁻¹ ∈ covW Zh h.central := by
  haveI : Zh.Normal := Subgroup.normal_of_le_center h.central
  rw [mem_covW_iff_mem_center]
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
    CFSG.Quasithin.SzN31.SmD6Grp.commutator_mem_center (covQ_card_quot h) (covQ_nonab h)
      (x : P ⧸ Zh) (y : P ⧸ Zh)

theorem pow_three_mem_covW (h : CoverP P σ Zh) (x : P) : x ^ 3 ∈ covW Zh h.central := by
  haveI : Zh.Normal := Subgroup.normal_of_le_center h.central
  rw [mem_covW_iff_mem_center, QuotientGroup.mk_pow]
  exact CFSG.Quasithin.SzN31.SmD6Grp.cube_mem_center (covQ_card_quot h) (covQ_nonab h) _

theorem conj_mem_covW (h : CoverP P σ Zh) {w : P} (hw : w ∈ covW Zh h.central) (p : P) :
    p * w * p⁻¹ ∈ covW Zh h.central := by
  rw [mem_covW]
  intro q
  have hz := mem_covW.mp hw (p⁻¹ * q * p)
  have e : p * w * p⁻¹ * q * (p * w * p⁻¹)⁻¹ * q⁻¹ =
      p * (w * (p⁻¹ * q * p) * w⁻¹ * (p⁻¹ * q * p)⁻¹) * p⁻¹ := by
    group
  rw [e, conj_eq_of_mem_center (h.central hz) p]
  exact hz

theorem sigma_mem_covW (h : CoverP P σ Zh) {w : P} (hw : w ∈ covW Zh h.central) :
    σ w ∈ covW Zh h.central := by
  rw [mem_covW]
  intro q
  obtain ⟨r, rfl⟩ := σ.surjective q
  have hz := mem_covW.mp hw r
  have e : σ w * σ r * (σ w)⁻¹ * (σ r)⁻¹ = σ (w * r * w⁻¹ * r⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e, h.sigma_Z _ hz]
  exact hz

end CFSG.RankThree.PartTwo.Sec8.Hering611
