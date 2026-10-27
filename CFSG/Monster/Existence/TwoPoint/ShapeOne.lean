module

public import CFSG.Monster.Existence.TwoPointTwoB
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.Monster.Existence

open scoped commutatorElement

variable {G X : Type} [Group G] [Group X]

section Conj

variable {u : G}

theorem conj_sign_mul {c₁ c₂ e₁ e₂ : G} (h₁ : c₁ * u * c₁⁻¹ = e₁ * u)
    (h₂ : c₂ * u * c₂⁻¹ = e₂ * u) (hc : c₁ * e₂ = e₂ * c₁) :
    (c₁ * c₂) * u * (c₁ * c₂)⁻¹ = e₂ * e₁ * u := by
  calc (c₁ * c₂) * u * (c₁ * c₂)⁻¹ = c₁ * (c₂ * u * c₂⁻¹) * c₁⁻¹ := by group
    _ = c₁ * (e₂ * u) * c₁⁻¹ := by rw [h₂]
    _ = (c₁ * e₂) * u * c₁⁻¹ := by group
    _ = (e₂ * c₁) * u * c₁⁻¹ := by rw [hc]
    _ = e₂ * (c₁ * u * c₁⁻¹) := by group
    _ = e₂ * e₁ * u := by rw [h₁, mul_assoc]

theorem conj_sign_inv {c e : G} (h : c * u * c⁻¹ = e * u) (hc : c⁻¹ * e = e * c⁻¹)
    (he : e * e = 1) : c⁻¹ * u * c⁻¹⁻¹ = e * u := by
  have key : u = e * (c⁻¹ * u * c) := by
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = c⁻¹ * (e * u) * c := by rw [h]
      _ = (c⁻¹ * e) * u * c := by group
      _ = (e * c⁻¹) * u * c := by rw [hc]
      _ = e * (c⁻¹ * u * c) := by group
  rw [inv_inv]
  calc c⁻¹ * u * c = e * (e * (c⁻¹ * u * c)) := by rw [← mul_assoc, he, one_mul]
    _ = e * u := by rw [← key]

variable {a : G}

theorem commute_of_eq_or {c e : G} (hca : c * a = a * c) (he : e = 1 ∨ e = a) :
    c * e = e * c := by
  rcases he with rfl | rfl
  · rw [mul_one, one_mul]
  · exact hca

theorem inv_mul_comm_of_mul_comm {c : G} (hca : c * a = a * c) : c⁻¹ * a = a * c⁻¹ := by
  calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
    _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hca]
    _ = a * c⁻¹ := by group

theorem inv_commute_of_eq_or {c e : G} (hca : c * a = a * c) (he : e = 1 ∨ e = a) :
    c⁻¹ * e = e * c⁻¹ :=
  commute_of_eq_or (inv_mul_comm_of_mul_comm hca) he

theorem sign_mul_self (ha : a * a = 1) {e : G} (he : e = 1 ∨ e = a) : e * e = 1 := by
  rcases he with rfl | rfl
  · rw [mul_one]
  · exact ha

theorem commutator_conj_self (ha : a * a = 1) {c₁ c₂ e₁ e₂ : G} (hc₁ : c₁ * a = a * c₁)
    (hc₂ : c₂ * a = a * c₂) (he₁ : e₁ = 1 ∨ e₁ = a) (he₂ : e₂ = 1 ∨ e₂ = a)
    (h₁ : c₁ * u * c₁⁻¹ = e₁ * u) (h₂ : c₂ * u * c₂⁻¹ = e₂ * u) :
    ⁅c₁, c₂⁆ * u * ⁅c₁, c₂⁆⁻¹ = u := by
  have i₁ := conj_sign_inv h₁ (inv_commute_of_eq_or hc₁ he₁) (sign_mul_self ha he₁)
  have i₂ := conj_sign_inv h₂ (inv_commute_of_eq_or hc₂ he₂) (sign_mul_self ha he₂)
  have hc₁₂ : (c₁ * c₂) * a = a * (c₁ * c₂) := by
    rw [mul_assoc, hc₂, ← mul_assoc, hc₁, mul_assoc]
  have hc₁₂₁ : (c₁ * c₂ * c₁⁻¹) * a = a * (c₁ * c₂ * c₁⁻¹) := by
    rw [mul_assoc, inv_mul_comm_of_mul_comm hc₁, ← mul_assoc, hc₁₂, mul_assoc]
  have s₁ := conj_sign_mul h₁ h₂ (commute_of_eq_or hc₁ he₂)
  have s₂ := conj_sign_mul s₁ i₁ (commute_of_eq_or hc₁₂ he₁)
  have s₃ := conj_sign_mul s₂ i₂ (commute_of_eq_or hc₁₂₁ he₂)
  rw [commutatorElement_def, s₃]
  have hcomm : e₁ * e₂ = e₂ * e₁ := by
    rcases he₁ with rfl | rfl
    · rw [one_mul, mul_one]
    · rcases he₂ with rfl | rfl
      · rw [one_mul, mul_one]
      · rfl
  have h1 : e₂ * (e₁ * (e₂ * e₁)) = 1 := by
    calc e₂ * (e₁ * (e₂ * e₁)) = e₂ * (e₂ * e₁ * e₁) := by rw [← mul_assoc e₁, hcomm]
      _ = 1 := by
        rw [mul_assoc e₂ e₁ e₁, sign_mul_self ha he₁, mul_one, sign_mul_self ha he₂]
  rw [h1, one_mul]

end Conj

section Hom

variable {a u : G} (hau : u * a = a * u) (π : ↥(cent a) →* X)

@[expose] def uIn : ↥(cent a) := ⟨u, Subgroup.mem_centralizer_singleton_iff.2 hau⟩

@[simp] theorem coe_uIn : ((uIn hau : ↥(cent a)) : G) = u := rfl

@[expose] noncomputable def cent2Hom : ↥(cent2 a u) →* X :=
  π.comp (Subgroup.inclusion (inf_le_left : cent2 a u ≤ cent a))

theorem cent2Hom_apply (h : ↥(cent2 a u)) :
    cent2Hom π h = π ⟨h, (Subgroup.mem_inf.1 h.2).1⟩ := rfl

variable {π}
variable (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a)
include hker

theorem conj_eq_or_of_mem_centralizer {c : ↥(cent a)}
    (hc : π c ∈ Subgroup.centralizer ({π (uIn hau)} : Set X)) :
    ∃ e : G, (e = 1 ∨ e = a) ∧ (c : G) * u * (c : G)⁻¹ = e * u := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have h1 : π (c * uIn hau * c⁻¹ * (uIn hau)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  refine ⟨(c : G) * u * (c : G)⁻¹ * u⁻¹, ?_, by group⟩
  simpa using (hker _).1 h1

variable (hπ : Function.Surjective π) (ha : a * a = 1)
include hπ ha

theorem le_range_cent2Hom {K : Subgroup X}
    (hK : K ≤ Subgroup.centralizer ({π (uIn hau)} : Set X)) (hperf : ⁅K, K⁆ = K) :
    K ≤ (cent2Hom (u := u) π).range := by
  rw [← hperf, Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨c₁, rfl⟩ := hπ k₁
  obtain ⟨c₂, rfl⟩ := hπ k₂
  obtain ⟨e₁, he₁, h₁⟩ := conj_eq_or_of_mem_centralizer hau hker (hK hk₁)
  obtain ⟨e₂, he₂, h₂⟩ := conj_eq_or_of_mem_centralizer hau hker (hK hk₂)
  have hc₁ : (c₁ : G) * a = a * c₁ := Subgroup.mem_centralizer_singleton_iff.1 c₁.2
  have hc₂ : (c₂ : G) * a = a * c₂ := Subgroup.mem_centralizer_singleton_iff.1 c₂.2
  have hfix := commutator_conj_self ha hc₁ hc₂ he₁ he₂ h₁ h₂
  have hmem : ((⁅c₁, c₂⁆ : ↥(cent a)) : G) ∈ cent u := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : ((⁅c₁, c₂⁆ : ↥(cent a)) : G) = ⁅(c₁ : G), (c₂ : G)⁆ := by
      simp [commutatorElement_def]
    rw [e]
    calc ⁅(c₁ : G), (c₂ : G)⁆ * u = (⁅(c₁ : G), (c₂ : G)⁆ * u * ⁅(c₁ : G), (c₂ : G)⁆⁻¹) *
          ⁅(c₁ : G), (c₂ : G)⁆ := by group
      _ = u * ⁅(c₁ : G), (c₂ : G)⁆ := by rw [hfix]
  refine ⟨⟨(⁅c₁, c₂⁆ : ↥(cent a)), Subgroup.mem_inf.2 ⟨(⁅c₁, c₂⁆ : ↥(cent a)).2, hmem⟩⟩, ?_⟩
  rw [cent2Hom_apply, ← map_commutatorElement]

end Hom

section Quot

variable {a u : G} {π : ↥(cent a) →* X}

theorem self_mem_cent2_left (hau : u * a = a * u) : a ∈ cent2 a u :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
    Subgroup.mem_centralizer_singleton_iff.2 hau.symm⟩

theorem self_mem_cent2_right (hau : u * a = a * u) : u ∈ cent2 a u :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hau,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem cent2Hom_eq_one_iff (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a)
    {h : ↥(cent2 a u)} : cent2Hom π h = 1 ↔ (h : G) = 1 ∨ (h : G) = a := by
  rw [cent2Hom_apply, hker]

theorem cent2Hom_eq_iff (hau : u * a = a * u)
    (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a) (hu2 : u * u = 1)
    {h : ↥(cent2 a u)} : cent2Hom π h = π (uIn hau) ↔ (h : G) = u ∨ (h : G) = a * u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have e : cent2Hom π h = π (uIn hau) ↔
      π (⟨h, (Subgroup.mem_inf.1 h.2).1⟩ * (uIn hau)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one, cent2Hom_apply]
  rw [e, hker]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_uIn, hui]
  constructor
  · rintro (h1 | h1)
    · left
      calc (h : G) = (h : G) * u * u := by rw [mul_assoc, hu2, mul_one]
        _ = u := by rw [h1, one_mul]
    · right
      calc (h : G) = (h : G) * u * u := by rw [mul_assoc, hu2, mul_one]
        _ = a * u := by rw [h1]
  · rintro (h1 | h1)
    · left
      rw [h1, hu2]
    · right
      rw [h1, mul_assoc, hu2, mul_one]

theorem card_ker_cent2Hom (hau : u * a = a * u)
    (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a) (ha1 : a ≠ 1) :
    Nat.card (cent2Hom (u := u) π).ker = 2 := by
  rw [Nat.card_eq_two_iff' (1 : (cent2Hom (u := u) π).ker)]
  refine ⟨⟨⟨a, self_mem_cent2_left hau⟩, (cent2Hom_eq_one_iff hker).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    apply ha1
    have := congrArg (fun x : (cent2Hom (u := u) π).ker => ((x : ↥(cent2 a u)) : G)) h
    simpa using this
  · intro y hy
    rcases (cent2Hom_eq_one_iff hker).1 y.2 with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hy
    · exact Subtype.ext (Subtype.ext h)

theorem card_range_cent2Hom_mul_two (hau : u * a = a * u)
    (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a) (ha1 : a ≠ 1) :
    Nat.card (cent2Hom (u := u) π).range * 2 = Nat.card ↥(cent2 a u) := by
  calc Nat.card (cent2Hom (u := u) π).range * 2
      = Nat.card (cent2Hom (u := u) π).ker * (cent2Hom (u := u) π).ker.index := by
        rw [card_ker_cent2Hom hau hker ha1, Subgroup.index_ker, mul_comm]
    _ = Nat.card ↥(cent2 a u) := Subgroup.card_mul_index _

structure ShapeOneData (a u : G) (π : ↥(cent a) →* X) (K : Subgroup X) : Prop where
  hau : u * a = a * u
  hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a
  hπ : Function.Surjective π
  ha : a * a = 1
  ha1 : a ≠ 1
  hu2 : u * u = 1
  hu1 : u ≠ 1
  hua : u ≠ a
  hK : K ≤ Subgroup.centralizer ({π (uIn hau)} : Set X)
  hperf : ⁅K, K⁆ = K
  hcard : Nat.card ↥(cent2 a u) = 2 * Nat.card K
  hZ : Nat.card ↥(Subgroup.center ↥K) = 2

variable [Finite G]

theorem range_cent2Hom_eq (hau : u * a = a * u)
    (hker : ∀ c : ↥(cent a), π c = 1 ↔ (c : G) = 1 ∨ (c : G) = a)
    (hπ : Function.Surjective π) (ha : a * a = 1) (ha1 : a ≠ 1) {K : Subgroup X}
    (hK : K ≤ Subgroup.centralizer ({π (uIn hau)} : Set X)) (hperf : ⁅K, K⁆ = K)
    (hcard : Nat.card ↥(cent2 a u) = 2 * Nat.card K) :
    (cent2Hom (u := u) π).range = K := by
  have : Finite (cent2Hom (u := u) π).range :=
    Finite.of_surjective _ (cent2Hom (u := u) π).rangeRestrict_surjective
  refine (Subgroup.eq_of_le_of_card_ge (le_range_cent2Hom hau hker hπ ha hK hperf) ?_).symm
  have := card_range_cent2Hom_mul_two hau hker ha1
  omega

namespace ShapeOneData

variable {K : Subgroup X} (D : ShapeOneData a u π K)
include D

theorem range_eq : (cent2Hom (u := u) π).range = K :=
  range_cent2Hom_eq D.hau D.hker D.hπ D.ha D.ha1 D.hK D.hperf D.hcard

theorem mem (h : ↥(cent2 a u)) : cent2Hom π h ∈ K := by
  rw [← D.range_eq]
  exact ⟨h, rfl⟩

@[expose] noncomputable def toQuot : ↥(cent2 a u) →* ↥K ⧸ Subgroup.center ↥K :=
  (QuotientGroup.mk' _).comp ((cent2Hom π).codRestrict K D.mem)

theorem toQuot_surjective : Function.Surjective D.toQuot := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hk : (k : X) ∈ (cent2Hom (u := u) π).range := by
    rw [D.range_eq]
    exact k.2
  obtain ⟨h, hh⟩ := hk
  refine ⟨h, ?_⟩
  simp only [toQuot, MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext hh

@[expose] def four : Subgroup G := kleinSubgroup a u D.ha D.hu2 D.hau.symm

omit [Finite G] in
theorem four_le_cent2 : D.four ≤ cent2 a u := by
  intro g hg
  rcases (mem_kleinSubgroup).1 hg with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact self_mem_cent2_left D.hau
  · exact self_mem_cent2_right D.hau
  · exact Subgroup.mul_mem _ (self_mem_cent2_left D.hau) (self_mem_cent2_right D.hau)

theorem ker_toQuot : D.toQuot.ker = D.four.subgroupOf (cent2 a u) := by
  have huK : π (uIn D.hau) ∈ K := by
    have := D.mem ⟨u, self_mem_cent2_right D.hau⟩
    rwa [cent2Hom_apply] at this
  set ub : ↥K := ⟨π (uIn D.hau), huK⟩ with hub
  have hubZ : ub ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (D.hK g.2))
  have hub1 : (⟨ub, hubZ⟩ : ↥(Subgroup.center ↥K)) ≠ 1 := by
    intro h
    have h' : π (uIn D.hau) = 1 := by
      have := congrArg (fun x : ↥(Subgroup.center ↥K) => ((x : ↥K) : X)) h
      simpa [hub] using this
    rcases (D.hker _).1 h' with h'' | h''
    · exact D.hu1 h''
    · exact D.hua h''
  have hZ' := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥K))).1 D.hZ
  have hcen : ∀ z ∈ Subgroup.center ↥K, z = 1 ∨ z = ub := by
    intro z hz
    by_cases h1 : (⟨z, hz⟩ : ↥(Subgroup.center ↥K)) = 1
    · left
      have := congrArg (fun x : ↥(Subgroup.center ↥K) => (x : ↥K)) h1
      simpa using this
    · right
      have := hZ'.unique h1 hub1
      have := congrArg (fun x : ↥(Subgroup.center ↥K) => (x : ↥K)) this
      simpa using this
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, four, mem_kleinSubgroup]
  simp only [toQuot, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hz
    rcases hcen _ hz with h1 | h1
    · have h2 : cent2Hom π h = 1 := by
        have := congrArg (fun x : ↥K => (x : X)) h1
        simpa using this
      rcases (cent2Hom_eq_one_iff D.hker).1 h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    · have h2 : cent2Hom π h = π (uIn D.hau) := by
        have := congrArg (fun x : ↥K => (x : X)) h1
        simpa [hub] using this
      rcases (cent2Hom_eq_iff D.hau D.hker D.hu2).1 h2 with h3 | h3
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr h3))
  · intro hh
    have e1 : ∀ y : ↥K, (y : X) = 1 → y ∈ Subgroup.center ↥K := fun y hy => by
      rw [show y = 1 from Subtype.ext hy]
      exact Subgroup.one_mem _
    have e2 : ∀ y : ↥K, (y : X) = π (uIn D.hau) → y ∈ Subgroup.center ↥K := fun y hy => by
      rw [show y = ub from Subtype.ext hy]
      exact hubZ
    rcases hh with h1 | h1 | h1 | h1
    · exact e1 _ ((cent2Hom_eq_one_iff D.hker).2 (Or.inl h1))
    · exact e1 _ ((cent2Hom_eq_one_iff D.hker).2 (Or.inr h1))
    · exact e2 _ ((cent2Hom_eq_iff D.hau D.hker D.hu2).2 (Or.inl h1))
    · exact e2 _ ((cent2Hom_eq_iff D.hau D.hker D.hu2).2 (Or.inr h1))

noncomputable def quotEquiv : ↥(cent2 a u) ⧸ D.toQuot.ker ≃* ↥K ⧸ Subgroup.center ↥K :=
  QuotientGroup.quotientKerEquivOfSurjective _ D.toQuot_surjective

theorem twoPointShape_one
    (hL : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .twistedE6 0 2 1) :
    TwoPointShape (cent2 a u) 1 := by
  have eF : ↥D.toQuot.ker ≃* ↥D.four :=
    (MulEquiv.subgroupCongr D.ker_toQuot).trans (Subgroup.subgroupOfEquivOfLe D.four_le_cent2)
  refine ⟨D.toQuot.ker, inferInstance, ?_, ?_, ?_⟩
  · have : IsElementaryAbelian 2 ↥D.four := isElementaryAbelian_kleinSubgroup
    exact isElementaryAbelian_of_mulEquiv eF.symm
  · rw [Nat.card_congr eF.toEquiv, four, natCard_kleinSubgroup D.ha1 D.hu1 D.hua.symm]
    norm_num
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv D.quotEquiv.symm hL

end ShapeOneData

end Quot

end CFSG.Monster.Existence
