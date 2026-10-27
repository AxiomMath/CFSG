module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Setup

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def imV (z : G) (A : Subgroup G) : Subgroup (V z) :=
  (A.subgroupOf (J z)).map (pi z)

theorem mem_imV {A : Subgroup G} {v : V z} :
    v ∈ imV z A ↔ ∃ a : J z, (a : G) ∈ A ∧ pi z a = v := by
  simp only [imV, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem pi_mem_imV {A : Subgroup G} {a : J z} (ha : (a : G) ∈ A) : pi z a ∈ imV z A :=
  mem_imV.mpr ⟨a, ha, rfl⟩

theorem conjVA_pi (g : H z) (a : J z) :
    conjVA z g (pi z a) =
      pi z ⟨(g : G) * a * (g : G)⁻¹, by
        rw [← conjJ'_apply_coe]; exact (conjJ' z g a).2⟩ := by
  have e : conjJ' z g a = ⟨(g : G) * a * (g : G)⁻¹, by
      rw [← conjJ'_apply_coe]; exact (conjJ' z g a).2⟩ := Subtype.ext (conjJ'_apply_coe g a)
  rw [conjVA_mk, e]

omit [Finite G] in
theorem conj_eq_of_mem_zpowers {g e : G} (hg : g ∈ H z) (he : e ∈ zpowers z) :
    g * e * g⁻¹ = e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  have hc : Commute g z := (commute_z_of_mem_H hg)
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]

section A1

variable (hA1 : Tim79a.ParrottHypA1 z)
include hA1

theorem pi_eq_pi_iff {a b : J z} : pi z a = pi z b ↔ (a : G)⁻¹ * b ∈ zpowers z := by
  rw [QuotientV.pi, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, centerIn_J_eq_zpowers_A1 hA1]
  simp

theorem pi_eq_one_iff {a : J z} : pi z a = 1 ↔ (a : G) ∈ zpowers z := by
  rw [← map_one (pi z), pi_eq_pi_iff hA1]
  simp

theorem V_comm (v w : V z) : v * w = w * v := by
  obtain ⟨a, rfl⟩ := pi_surjective z v
  obtain ⟨b, rfl⟩ := pi_surjective z w
  rw [← map_mul, ← map_mul, pi_eq_pi_iff hA1]
  have hmem : ⁅(a : G)⁻¹, (b : G)⁻¹⁆ ∈ ⁅J z, J z⁆ :=
    Subgroup.commutator_mem_commutator ((J z).inv_mem a.2) ((J z).inv_mem b.2)
  rw [hA1.commutator, commutatorElement_def] at hmem
  have : ((a * b : J z) : G)⁻¹ * ((b * a : J z) : G) = ((a : G)⁻¹ * (b : G)⁻¹ * (a : G)⁻¹⁻¹ *
      (b : G)⁻¹⁻¹)⁻¹ ^ (1 : ℤ) := by
    simp only [Subgroup.coe_mul, inv_inv, zpow_one]
    group
  rw [this]
  exact (zpowers z).zpow_mem ((zpowers z).inv_mem hmem) 1

theorem V_sq (v : V z) : v * v = 1 := by
  obtain ⟨a, rfl⟩ := pi_surjective z v
  rw [← map_mul, pi_eq_one_iff hA1]
  have hc := CFSG.IsExtraspecial2.mul_self_mem_center_map hA1.extraspecial a.2
  rw [← CFSG.centerIn_eq_map_center, centerIn_J_eq_zpowers_A1 hA1] at hc
  simpa using hc

theorem pi_mem_imV_iff {A : Subgroup G} (hzA : zpowers z ≤ A) {a : J z} :
    pi z a ∈ imV z A ↔ (a : G) ∈ A := by
  constructor
  · intro ha
    obtain ⟨b, hb, hab⟩ := mem_imV.mp ha
    have h := (pi_eq_pi_iff hA1).mp hab
    have : (a : G) = b * ((b : G)⁻¹ * a)⁻¹⁻¹ := by group
    rw [this]
    exact A.mul_mem hb (A.inv_mem (A.inv_mem (hzA h)))
  · exact pi_mem_imV

theorem card_imV {A : Subgroup G} (hAJ : A ≤ J z) (hzA : zpowers z ≤ A) :
    Nat.card (imV z A) * 2 = Nat.card A := by
  let ρ : ↥A →* V z := (pi z).comp (Subgroup.inclusion hAJ)
  have hrange : ρ.range = imV z A := by
    ext v
    rw [MonoidHom.mem_range, mem_imV]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hAJ a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hker : ρ.ker = (zpowers z).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact pi_eq_one_iff hA1
  have h := Subgroup.card_ker_mul_card_range ρ
  rw [hker, hrange] at h
  have hz : Nat.card ((zpowers z).subgroupOf A) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers,
      orderOf_z_A1 hA1]
  rw [hz] at h
  omega

theorem conjVA_pi_eq_iff (g : H z) (a : J z) :
    conjVA z g (pi z a) = pi z a ↔ (g : G) * a * (g : G)⁻¹ * (a : G)⁻¹ ∈ zpowers z := by
  rw [conjVA_pi, pi_eq_pi_iff hA1]
  have haH : (a : G) ∈ H z := J_le_H a.2
  change ((g : G) * a * (g : G)⁻¹)⁻¹ * a ∈ zpowers z ↔ _
  constructor
  · intro h
    have e1 : (g : G) * a * (g : G)⁻¹ * (a : G)⁻¹ =
        ((a : G) * (((g : G) * a * (g : G)⁻¹)⁻¹ * a) * (a : G)⁻¹)⁻¹ := by group
    rw [e1, conj_eq_of_mem_zpowers haH h]
    exact (zpowers z).inv_mem h
  · intro h
    have e1 : ((g : G) * a * (g : G)⁻¹)⁻¹ * a =
        ((a : G)⁻¹ * ((g : G) * a * (g : G)⁻¹ * (a : G)⁻¹) * (a : G)⁻¹⁻¹)⁻¹ := by group
    rw [e1, conj_eq_of_mem_zpowers ((H z).inv_mem haH) h]
    exact (zpowers z).inv_mem h

theorem conjVA_mem_imV_iff {A : Subgroup G} (hzA : zpowers z ≤ A) (g : H z)
    (hgA : ∀ a : G, a ∈ A ↔ (g : G) * a * (g : G)⁻¹ ∈ A) (v : V z) :
    conjVA z g v ∈ imV z A ↔ v ∈ imV z A := by
  obtain ⟨a, rfl⟩ := pi_surjective z v
  rw [conjVA_pi, pi_mem_imV_iff hA1 hzA, pi_mem_imV_iff hA1 hzA]
  exact (hgA a).symm

theorem conjVA_apply_of_mem_J {g : H z} (hg : (g : G) ∈ J z) (v : V z) : conjVA z g v = v := by
  obtain ⟨a, rfl⟩ := pi_surjective z v
  rw [conjVA_pi_eq_iff hA1]
  have hmem : ⁅(g : G), (a : G)⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator hg a.2
  rw [hA1.commutator, commutatorElement_def] at hmem
  exact hmem

end A1

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
