module

public import CFSG.RankThree.GF2n.Parrott.Section4InvolutionCoset
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveStructure
public import CFSG.RankThree.GF2n.Parrott.QuadraticV
public import CFSG.GroupTheory.CentralizerSylowFusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem qVZMod_eq_zero_iff (h : Tim79a.ParrottHyp z) (v : QuotientV.V z) :
    qVZMod h v = 0 ↔ qV h v = 1 := by
  unfold qVZMod
  rw [show (0 : ZMod 2) = Multiplicative.toAdd (1 : Multiplicative (ZMod 2)) from rfl,
    Equiv.apply_eq_iff_eq (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
  exact (zpowersEquivZModTwo h).map_eq_one_iff

theorem exists_mul_inv_eq_of_fixDimV_eq_four (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z)
    (hxx : x * x = 1) (hV : fixDimV h ⟨x, hxH⟩ = 4) {v : QuotientV.V z}
    (hv : conjV h ⟨x, hxH⟩ v = v) :
    ∃ u : QuotientV.V z, conjV h ⟨x, hxH⟩ u * u⁻¹ = v := by
  have hcomm : IsMulCommutative (QuotientV.V z) := QuotientV.isMulCommutative_V h
  have hc : ∀ a b : QuotientV.V z, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  set σ : MulAut (QuotientV.V z) := conjV h ⟨x, hxH⟩ with hσ
  have hσσ : ∀ v, σ (σ v) = v := by
    intro v
    have h1 : (⟨x, hxH⟩ : ↥(H z)) * ⟨x, hxH⟩ = 1 := Subtype.ext hxx
    rw [hσ, ← MulAut.mul_apply, ← map_mul, h1, map_one, MulAut.one_apply]
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  let φ : QuotientV.V z →* QuotientV.V z :=
    MonoidHom.mk' (fun v => σ v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * ((σ b * b⁻¹) * a⁻¹) := by group
        _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [hc (σ b * b⁻¹) a⁻¹]
        _ = σ a * a⁻¹ * (σ b * b⁻¹) := by group)
  have hker : ∀ v, v ∈ φ.ker ↔ σ v = v := by
    intro v
    rw [MonoidHom.mem_ker]
    exact mul_inv_eq_one
  have hkerEq : φ.ker = autFixedSubgroup σ := Subgroup.ext fun v => by
    rw [hker, mem_autFixedSubgroup]
  have hkcard : Nat.card φ.ker = 2 ^ 4 := by
    rw [hkerEq, card_fix h ⟨x, hxH⟩, hV]
  have hrle : φ.range ≤ φ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [hker]
    show σ (σ v * v⁻¹) = σ v * v⁻¹
    rw [map_mul, map_inv, hσσ]
    have h1 : v = v⁻¹ := (inv_eq_of_mul_eq_one_left (hsq v)).symm
    have h2 : σ v = (σ v)⁻¹ := (inv_eq_of_mul_eq_one_left (hsq (σ v))).symm
    rw [← h1, ← h2]
    exact hc _ _
  have hcard : Nat.card φ.ker * Nat.card φ.range = 2 ^ 8 := by
    rw [Subgroup.card_ker_mul_card_range φ, QuotientV.card_V h]
  have hrcard : Nat.card φ.range = 2 ^ 4 := by
    rw [hkcard] at hcard
    omega
  have hreq : φ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hrle (by rw [hkcard, hrcard])
  have hvker : v ∈ φ.ker := (hker v).mpr hv
  rw [← hreq] at hvker
  exact hvker

theorem exists_involution_lift_of_fixed_of_qVZMod_eq_zero (h : Tim79a.ParrottHyp z) {x : G}
    (hxH : x ∈ H z) (hxx : x * x = 1) (hV : fixDimV h ⟨x, hxH⟩ = 4) {v : QuotientV.V z}
    (hv : conjV h ⟨x, hxH⟩ v = v) (hq : qVZMod h v = 0) :
    ∃ (j : G) (hj : j ∈ J z), QuotientV.pi z ⟨j, hj⟩ = v ∧ j * j = 1 ∧ x * j = j * x := by
  obtain ⟨ū, hū⟩ := exists_mul_inv_eq_of_fixDimV_eq_four h hxH hxx hV hv
  obtain ⟨u, rfl⟩ := QuotientV.pi_surjective z ū
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  let j' : J z := conjJ' z ⟨x, hxH⟩ u * u⁻¹
  have hj'G : (j' : G) = x * (u : G) * x⁻¹ * (u : G)⁻¹ := by
    simp only [j', Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
  have hpi : QuotientV.pi z j' = v := by
    show QuotientV.pi z (conjJ' z ⟨x, hxH⟩ u * u⁻¹) = v
    rw [map_mul, map_inv, ← conjV_mk h ⟨x, hxH⟩ u]
    exact hū
  have hsq : (j' : G) * (j' : G) = 1 := by
    have h1 : ((qV h (QuotientV.pi z j') : Subgroup.zpowers z) : G) = 1 := by
      rw [hpi, (qVZMod_eq_zero_iff h v).mp hq]
      rfl
    rw [qV_pi_coe, pow_two] at h1
    exact h1
  have hxjx : x * (j' : G) * x⁻¹ = (j' : G)⁻¹ := by
    rw [hj'G, hxinv]
    calc x * (x * (u : G) * x * (u : G)⁻¹) * x = (x * x) * (u : G) * x * (u : G)⁻¹ * x := by
          group
      _ = (u : G) * x * (u : G)⁻¹ * x := by rw [hxx, one_mul]
      _ = (x * (u : G) * x * (u : G)⁻¹)⁻¹ := by
          have e : (x * (u : G) * x * (u : G)⁻¹)⁻¹ = (u : G) * x⁻¹ * (u : G)⁻¹ * x⁻¹ := by group
          rw [e, hxinv]
  have hjinv : (j' : G)⁻¹ = (j' : G) := inv_eq_of_mul_eq_one_right hsq
  refine ⟨(j' : G), j'.2, hpi, hsq, ?_⟩
  rw [hjinv] at hxjx
  exact mul_inv_eq_iff_eq_mul.mp hxjx

section Centre

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem mem_J_or_mul_of_mem_centre_sylow (h : Tim79a.ParrottHyp z) {x : G} (hxH : x ∈ H z)
    (hxx : x * x = 1) (hV : fixDimV h ⟨x, hxH⟩ = 4)
    (hV4 : ∀ y : ↥(H z), qH D ⟨x, hxH⟩ * qH D y = qH D y * qH D ⟨x, hxH⟩ →
      (∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v → qVZMod h v = 0 → conjV h y v = v) →
        qH D y = 1 ∨ qH D y = qH D ⟨x, hxH⟩)
    {Y : Subgroup G} (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G))) :
    ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j := by
  intro w hw
  obtain ⟨hwY, hwc⟩ := mem_inf.mp hw
  obtain ⟨hwH, hwx⟩ := mem_inf.mp (hY.le hwY)
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hJY : J z ⊓ centralizer ({x} : Set G) ≤ Y := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hY
      (fun j hj => mem_inf.mpr ⟨J_le_H hj.1, hj.2⟩) ?_ (isPGroup_J h).to_inf_left
    have key : ∀ c ∈ H z ⊓ centralizer ({x} : Set G), ∀ j ∈ J z ⊓ centralizer ({x} : Set G),
        c * j * c⁻¹ ∈ J z ⊓ centralizer ({x} : Set G) := by
      intro c hc j hj
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1) j).mp hj.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc.2
      have hjx : j * x = x * j := mem_centralizer_singleton_iff.mp hj.2
      have hcx' : c⁻¹ * x = x * c⁻¹ := by
        calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
          _ = x * c⁻¹ := by group
      calc c * j * c⁻¹ * x = c * j * (c⁻¹ * x) := by group
        _ = c * j * (x * c⁻¹) := by rw [hcx']
        _ = c * (j * x) * c⁻¹ := by group
        _ = c * (x * j) * c⁻¹ := by rw [hjx]
        _ = (c * x) * j * c⁻¹ := by group
        _ = (x * c) * j * c⁻¹ := by rw [hcx]
        _ = x * (c * j * c⁻¹) := by group
    intro c hc
    rw [mem_normalizer_iff]
    intro j
    refine ⟨key c hc j, fun hj => ?_⟩
    have h1 := key c⁻¹ (inv_mem hc) _ hj
    simpa [mul_assoc] using h1
  have hfix : ∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v → qVZMod h v = 0 →
      conjV h ⟨w, hwH⟩ v = v := by
    intro v hv hq
    obtain ⟨j, hj, hjv, hjj, hxj⟩ :=
      exists_involution_lift_of_fixed_of_qVZMod_eq_zero h hxH hxx hV hv hq
    have hjY : j ∈ Y := hJY (mem_inf.mpr ⟨hj, mem_centralizer_singleton_iff.mpr hxj.symm⟩)
    have hjw : j * w = w * j := mem_centralizer_iff.mp hwc j hjY
    rw [← hjv, conjV_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    calc w * j * w⁻¹ = j * w * w⁻¹ := by rw [← hjw]
      _ = j := by group
  have hcomm : qH D ⟨x, hxH⟩ * qH D ⟨w, hwH⟩ = qH D ⟨w, hwH⟩ * qH D ⟨x, hxH⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp hwx).symm
  rcases hV4 ⟨w, hwH⟩ hcomm hfix with h1 | h1
  · exact Or.inl ((J_mem_iff D _).mpr h1)
  · right
    have h2 : qH D ((⟨x, hxH⟩ : ↥(H z))⁻¹ * ⟨w, hwH⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x⁻¹ * w ∈ J z := (J_mem_iff D _).mpr h2
    exact ⟨x⁻¹ * w, h3, by group⟩

end Centre

section Hzs

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem hZs_of_fixed_space_data (h : Tim79a.ParrottHyp z)
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
      centralizer (B : Set A45) = B ⊔ zpowers w)
    (hV4 : ∀ y y' : ↥(H z), IsConj (qH D y) (uA * vA) → qH D y * qH D y' = qH D y' * qH D y →
      (∀ v : QuotientV.V z, conjV h y v = v → qVZMod h v = 0 → conjV h y' v = v) →
        qH D y' = 1 ∨ qH D y' = qH D y) :
    ∀ B : Subgroup G, IsSylowOf 5 B (H z) → ∀ x₀ ∈ H z, x₀ * x₀ = 1 →
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) → (∀ b ∈ B, x₀ * b = b * x₀) →
      ∀ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x₀} : Set G)) →
        ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x₀ * j := by
  intro B hB5 x₀ hx₀H hx₀x₀ hx₀N hx₀B Y hY w hw
  have hx₀J : x₀ ∉ J z := fun hx => hx₀N (hJN hx)
  have hconj := isConj_qH_of_involution_mem_centralizer_five D h hC5 hB5 hx₀H hx₀x₀ hx₀J hx₀B
  exact mem_J_or_mul_of_mem_centre_sylow D h hx₀H hx₀x₀ (hV2 _ hconj)
    (fun y' hc hf => hV4 ⟨x₀, hx₀H⟩ y' hconj hc hf) hY w hw

end Hzs

end CFSG.RankThree.GF2n.Parrott
