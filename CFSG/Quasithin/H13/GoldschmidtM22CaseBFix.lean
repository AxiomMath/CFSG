module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBSetup

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem exists_comm_of_card_le {V : Subgroup G} (hV : IsElemAbelian 2 V) {u : G}
    (hu : u ∈ Subgroup.normalizer (V : Set G)) (hu2 : u * u = 1)
    (hcard : Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) ^ 2 ≤ Nat.card V) :
    ∀ x ∈ V ⊓ Subgroup.centralizer ({u} : Set G), ∃ v ∈ V, x = v * u * v⁻¹ * u⁻¹ := by
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hV hx hy
  have hinv : ∀ x ∈ V, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV.2 x hx)
  have hmem : ∀ v ∈ V, v * u * v⁻¹ * u⁻¹ ∈ V := by
    intro v hv
    have : u * v⁻¹ * u⁻¹ ∈ V := conj_mem hu (V.inv_mem hv)
    simpa [mul_assoc] using V.mul_mem hv this
  let f : ↥V →* ↥V := MonoidHom.mk' (fun v => ⟨v * u * v⁻¹ * u⁻¹, hmem v v.2⟩) (by
    intro v w
    apply Subtype.ext
    have hfw := hmem w w.2
    have hfv := hmem v v.2
    show (v * w : G) * u * ((v * w : G))⁻¹ * u⁻¹ =
      ((v : G) * u * (v : G)⁻¹ * u⁻¹) * ((w : G) * u * (w : G)⁻¹ * u⁻¹)
    calc (v * w : G) * u * ((v * w : G))⁻¹ * u⁻¹
        = (v : G) * ((w : G) * u * (w : G)⁻¹ * u⁻¹) * (u * (v : G)⁻¹ * u⁻¹) := by group
      _ = ((w : G) * u * (w : G)⁻¹ * u⁻¹) * (v : G) * (u * (v : G)⁻¹ * u⁻¹) := by
          rw [hcomm _ v.2 _ hfw]
      _ = ((w : G) * u * (w : G)⁻¹ * u⁻¹) * ((v : G) * u * (v : G)⁻¹ * u⁻¹) := by group
      _ = ((v : G) * u * (v : G)⁻¹ * u⁻¹) * ((w : G) * u * (w : G)⁻¹ * u⁻¹) := by
          rw [hcomm _ hfw _ hfv])
  let C : Subgroup ↥V := (V ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf V
  have hker : f.ker = C := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show (⟨(v : G) * u * (v : G)⁻¹ * u⁻¹, hmem v v.2⟩ : ↥V) = 1 ↔ _
    rw [Subtype.ext_iff]
    simp only [Subgroup.coe_one, mul_inv_eq_one]
    constructor
    · intro h
      refine ⟨v.2, ?_⟩
      calc (v : G) * u = ((v : G) * u * (v : G)⁻¹) * v := by group
        _ = u * v := by rw [h]
    · rintro ⟨-, h⟩
      calc (v : G) * u * (v : G)⁻¹ = u * v * (v : G)⁻¹ := by rw [h]
        _ = u := by group
  have hrange : f.range ≤ C := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(f v).2, ?_⟩
    have hp : u * (v : G) * u⁻¹ ∈ V := conj_mem hu v.2
    have hu1 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
    have hz : u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹ = (v : G) * u * (v : G)⁻¹ * u⁻¹ := by
      have e1 : u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹ = (u * (v : G) * u⁻¹) * (v : G)⁻¹ := by
        calc u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹
            = u * v * u * (v : G)⁻¹ * (u⁻¹ * u⁻¹) := by group
          _ = u * v * u * (v : G)⁻¹ := by rw [hu1, mul_one]
          _ = (u * v * u⁻¹) * (u * u) * (v : G)⁻¹ := by group
          _ = (u * (v : G) * u⁻¹) * (v : G)⁻¹ := by rw [hu2, mul_one]
      have e2 : (v : G) * u * (v : G)⁻¹ * u⁻¹ = (v : G) * (u * (v : G) * u⁻¹)⁻¹ := by group
      rw [e1, e2, hinv _ v.2, hinv _ hp]
      exact hcomm _ hp _ v.2
    show (f v : G) * u = u * (f v : G)
    have hfv : (f v : G) = (v : G) * u * (v : G)⁻¹ * u⁻¹ := rfl
    rw [hfv]
    calc ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u
        = (u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) * u⁻¹) * u := by rw [hz]
      _ = u * ((v : G) * u * (v : G)⁻¹ * u⁻¹) := by group
  have hcardC : Nat.card C = Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hker] at hmul
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hle : Nat.card C ≤ Nat.card f.range := by
    have h1 : Nat.card C * Nat.card C ≤ Nat.card C * Nat.card f.range := by
      rw [hmul, ← pow_two, hcardC]
      have : Nat.card ↥V = Nat.card V := rfl
      exact hcard
    exact Nat.le_of_mul_le_mul_left h1 hCpos
  have heq : f.range = C := Subgroup.eq_of_le_of_card_ge hrange hle
  intro x hx
  have hxC : (⟨x, hx.1⟩ : ↥V) ∈ C := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  rw [← heq] at hxC
  obtain ⟨v, hv⟩ := hxC
  exact ⟨v, v.2, (congrArg Subtype.val hv).symm⟩

namespace BCtx

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx T M L V g D)

include c in
theorem card_inf_centralizer_le_four {u : G} (hu : u ∈ Subgroup.normalizer (V : Set G))
    (hu2 : u * u = 1) (hu1 : u ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := c.h.toHyp611.isElemAbelian
  have hA : IsElemAbelian 2 (Subgroup.zpowers u) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : u ^ (↑(2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two]; exact hu2
    rw [this, one_zpow]
  have hAN : Subgroup.zpowers u ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hu
  have hAM : Subgroup.zpowers u ≤ M := hAN.trans (c.hl.h621 G T M L V c.h).2
  have hle : autI hV (Subgroup.zpowers u) ≤ autI hV M := autI_mono hV hAM
  have hne : autI hV (Subgroup.zpowers u) ≠ ⊥ :=
    fun h => hu1 ((autI_eq_bot_iff hV hAN).mp h (Subgroup.mem_zpowers u))
  have hp : IsPGroup 2 (autI hV (Subgroup.zpowers u)) :=
    isPGroup_of_isElemAbelian2 (isElemAbelian2_autI hV hA hAN)
  have h1 := mParam_le_rkIdx_fixV hle hp hne
  have h2 : mParam (autI hV M) = 2 := ((c.hl.h6110 G T M L V 2 c.h.toHyp611Nat).2.1 hV).2
  rw [h2] at h1
  have hFcard : Nat.card (fixV (autI hV (Subgroup.zpowers u))) =
      Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [card_fixV_autI hV hAN, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hidx := Subgroup.index_mul_card (fixV (autI hV (Subgroup.zpowers u)))
  have hV16 : Nat.card (IntMod V hV) = 16 := KData.card_V c.h
  rw [hV16, hFcard] at hidx
  have hne0 : (fixV (autI hV (Subgroup.zpowers u))).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : 2 ^ 2 ∣ (fixV (autI hV (Subgroup.zpowers u))).index :=
    (padicValNat_dvd_iff_le hne0).mpr h1
  have h5 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) h4
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) := Nat.card_pos
  generalize (fixV (autI hV (Subgroup.zpowers u))).index = i at *
  generalize Nat.card ↥(V ⊓ Subgroup.centralizer ({u} : Set G)) = n at *
  nlinarith

include c in
theorem exists_comm_of_involution {u : G} (hu : u ∈ Subgroup.normalizer (V : Set G))
    (hu2 : u * u = 1) (hu1 : u ∉ Subgroup.centralizer (V : Set G)) :
    ∀ x ∈ V ⊓ Subgroup.centralizer ({u} : Set G), ∃ v ∈ V, x = v * u * v⁻¹ * u⁻¹ := by
  refine exists_comm_of_card_le c.h.toHyp611.isElemAbelian hu hu2 ?_
  have h4 := c.card_inf_centralizer_le_four hu hu2 hu1
  rw [KData.card_V c.h]
  nlinarith

end BCtx

end CFSG.Quasithin.H13.GM22
