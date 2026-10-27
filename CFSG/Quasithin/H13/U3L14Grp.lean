module

public import CFSG.Quasithin.Background.G2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_map_conj_iff {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conj_mem_map_conj {H : Subgroup G} {g y : G} (hy : y ∈ H) :
    g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
  mem_map_conj_iff.2 (by simpa [mul_assoc] using hy)

theorem comm_mem_pCoreOf_of_central {L : Subgroup G}
    (hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L))
    {y : G} (hy : y ∈ normalizer (L : Set G))
    (h : ∀ l ∈ L, ∀ m ∈ L, (y * l * y⁻¹ * l⁻¹) * m * (y * l * y⁻¹ * l⁻¹)⁻¹ * m⁻¹ ∈ pCoreOf 2 L) :
    ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  have hmemO : ∀ x : ↥L, (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.pCore 2 ↥L := fun x => by
    rw [pCoreOf, mem_map]
    constructor
    · rintro ⟨z, hz, hzx⟩
      rwa [← Subtype.ext hzx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  let σ₀ : MulAut ↥L := L.normalizerMonoidHom ⟨y, hy⟩
  have hσ₀ : ∀ l : ↥L, ((σ₀ l : ↥L) : G) = y * l * y⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨y, hy⟩ l
  have hchar : (CFSG.pCore 2 ↥L).map (σ₀ : ↥L →* ↥L) = CFSG.pCore 2 ↥L :=
    (Subgroup.characteristic_iff_map_eq.1 inferInstance) σ₀
  let σ : MulAut Q := QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) σ₀ hchar
  have hσ : ∀ l : ↥L, σ (l : Q) = ((σ₀ l : ↥L) : Q) := fun l => rfl
  have hcen : ∀ x : Q, σ x * x⁻¹ ∈ Subgroup.center Q := by
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hσ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff]
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    set c : ↥L := σ₀ l * l⁻¹ with hc
    have hcG : (c : G) = y * l * y⁻¹ * l⁻¹ := by rw [hc, coe_mul, coe_inv, hσ₀]
    have h1 : c * m * c⁻¹ * m⁻¹ ∈ CFSG.pCore 2 ↥L := by
      rw [← hmemO]
      simpa [hcG] using h l l.2 m m.2
    have h2 : ((c * m * c⁻¹ * m⁻¹ : ↥L) : Q) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    calc (m : Q) * (c : Q) = ((c : Q) * m * (c : Q)⁻¹ * (m : Q)⁻¹)⁻¹ * ((c : Q) * m) := by group
      _ = (c : Q) * m := by rw [h2, inv_one, one_mul]
  have hid : ∀ x : Q, σ x = x := by
    let H : Subgroup Q := MonoidHom.eqLocus (σ : Q →* Q) (MonoidHom.id Q)
    have hcomm : ∀ a b : Q, ⁅a, b⁆ ∈ H := by
      intro a b
      obtain ⟨z, hz, hza⟩ : ∃ z ∈ Subgroup.center Q, σ a = z * a := ⟨σ a * a⁻¹, hcen a, by group⟩
      obtain ⟨w, hw, hwb⟩ : ∃ w ∈ Subgroup.center Q, σ b = w * b := ⟨σ b * b⁻¹, hcen b, by group⟩
      show σ ⁅a, b⁆ = ⁅a, b⁆
      have hz' := Subgroup.mem_center_iff.1 hz
      have hw' := Subgroup.mem_center_iff.1 hw
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hza, hwb]
      have cz : ∀ x : Q, z * x * z⁻¹ = x := fun x => by rw [← hz' x, mul_inv_cancel_right]
      have cw : ∀ x : Q, w * x * w⁻¹ = x := fun x => by rw [← hw' x, mul_inv_cancel_right]
      calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
          = z * (a * w * b * a⁻¹) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
        _ = (a * w * b * a⁻¹) * (b⁻¹ * w⁻¹) := by rw [cz]
        _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by rw [show a * w = w * a from hw' a]; group
        _ = a * b * a⁻¹ * b⁻¹ := cw _
    have hle : commutator Q ≤ H := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro u _ v _
      exact hcomm u v
    intro x
    exact hle (hperf.commutator_eq_top ▸ Subgroup.mem_top x)
  intro l hl
  have h1 := hid ((⟨l, hl⟩ : ↥L) : Q)
  rw [hσ] at h1
  have h2 : (((σ₀ ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L)⁻¹ : ↥L)) : Q) = 1 := by
    rw [QuotientGroup.mk_mul, h1, QuotientGroup.mk_inv, mul_inv_cancel]
  have h3 := (QuotientGroup.eq_one_iff _).1 h2
  rw [← hmemO] at h3
  simpa [hσ₀] using h3

variable [Finite G]

theorem isPGroup_of_oTwoUpper_eq_bot {X : Subgroup G} (h : oTwoUpper X = ⊥) : IsPGroup 2 X :=
  isPGroup_two_of_odd_orderOf_eq_one fun y hy ho => by
    have : y ∈ oTwoUpper X := mem_oTwoUpper_of_odd hy ho
    rw [h] at this
    exact this

omit [Finite G] in
theorem oTwoUpper_sup_eq {Y Q : Subgroup G} (hY : Y = oTwoUpper Y) (hQ : IsPGroup 2 Q)
    (hQY : Q ≤ normalizer (Y : Set G)) : oTwoUpper (Y ⊔ Q) = Y := by
  refine le_antisymm ?_ (hY.le.trans (oTwoUpper_mono le_sup_left))
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hmul : ((Y ⊔ Q : Subgroup G) : Set G) = (Y : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y Q hQY
  obtain ⟨y, hy, q, hq, rfl⟩ : x ∈ (Y : Set G) * (Q : Set G) := by rw [← hmul]; exact hx
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hQ hq
  obtain ⟨y', hy', he⟩ := A4.exists_pow_mul_eq hy (hQY hq) (2 ^ k)
  exact ⟨k, by rw [he, hk, mul_one]; exact hy'⟩

theorem not_isPGroup_of_perfect {K : Subgroup G} (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    ¬ IsPGroup 2 K := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent K := h2.isNilpotent
  have hsolv : Group.IsSolvable K := inferInstance
  have h1 := (isSolvable_iff_perfectCore_eq_bot K).1 hsolv
  rw [perfectCore_eq_self_of_perfect hK] at h1
  exact hK1 h1

end CFSG.Quasithin.H13.U3
