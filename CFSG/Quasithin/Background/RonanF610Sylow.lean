module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Foundations.Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.RonanF610

open CFSG.Open

theorem not_isCyclic_sylow_two_of_isPerfect {G : Type*} [Group G] [Finite G]
    (hperf : Group.IsPerfect G) (P : Sylow 2 G) (hP : Nat.card ↥(P : Subgroup G) ≠ 1) :
    ¬ IsCyclic ↥(P : Subgroup G) := by
  intro hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hP (by simpa using ha)
  have h2 : 2 ∣ Nat.card G :=
    (dvd_pow_self 2 ha0).trans (ha ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G))
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hnorm := IsCyclic.normalizer_le_centralizer hmin hcyc
  have hcomp := IsCyclic.isComplement' hmin hcyc
  let f := MonoidHom.transferSylow P hnorm
  have hle : commutator G ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      (IsMulCommutative.is_comm (M := ↥(P : Subgroup G))).comm (f g₁) (f g₂)]
    group
  have hker : f.ker = ⊤ := by
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle
  have hcard := hcomp.card_mul_card
  rw [hker, Subgroup.card_top] at hcard
  exact hP (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans (mul_one _).symm))

theorem four_le_card_of_isPGroup {G : Type*} [Group G] [Finite G] (h : IsPGroup 2 G)
    (h1 : Nat.card G ≠ 1) (h2 : Nat.card G ≠ 2) : 4 ≤ Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h.exists_card_eq
  rw [hk] at h1 h2 ⊢
  rcases k with _ | _ | k
  · simp at h1
  · simp at h2
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem four_le_relIndex_center {K : Type*} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (P : Sylow 2 K) : 4 ≤ (Subgroup.center K).relIndex (P : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect K := hK.1
  set Z := Subgroup.center K with hZ
  set π : K →* K ⧸ Z := QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hidx : Z.relIndex (P : Subgroup K) = Nat.card ↥((P : Subgroup K).map π) := by
    have e1 : (π.comp (P : Subgroup K).subtype).ker = Z.subgroupOf (P : Subgroup K) := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, hπdef,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    have e2 : (π.comp (P : Subgroup K).subtype).range = (P : Subgroup K).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [Subgroup.relIndex, ← e1, Subgroup.index_ker, e2]
  rw [hidx]
  set P' : Sylow 2 (K ⧸ Z) := P.mapSurjective hπ with hP'def
  have hP' : (P' : Subgroup (K ⧸ Z)) = (P : Subgroup K).map π := Sylow.coe_mapSurjective hπ P
  rw [← hP']
  have hQperf : Group.IsPerfect (K ⧸ Z) := inferInstance
  have : IsSimpleGroup (K ⧸ Z) := hK.2.1
  have h2 : 2 ∣ Nat.card (K ⧸ Z) := by
    by_contra hodd
    have hodd' : Odd (Nat.card (K ⧸ Z)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    exact Group.IsPerfect.not_isSolvable (K ⧸ Z) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd')
  have hne1 : Nat.card ↥(P' : Subgroup (K ⧸ Z)) ≠ 1 := by
    intro h1
    exact P'.ne_bot_of_dvd_card h2 (Subgroup.card_eq_one.mp h1)
  have hnc := not_isCyclic_sylow_two_of_isPerfect hQperf P' hne1
  refine four_le_card_of_isPGroup P'.isPGroup' hne1 fun h2' => hnc ?_
  exact isCyclic_of_prime_card h2'

theorem centerOf_subgroupOf {D : Type*} [Group D] (K : Subgroup D) :
    (centerOf K).subgroupOf K = Subgroup.center ↥K := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro hx g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) g g.2)
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (hx ⟨g, hg⟩)

variable {D : Type*} [Group D] [Finite D]

theorem four_le_relIndex_centerOf {K S : Subgroup D} (hK : CFSG.IsQuasisimple ↥K)
    (hS : IsSylowIn 2 S K) : 4 ≤ (centerOf K).relIndex S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := four_le_relIndex_center hK hS.toSylow
  rwa [IsSylowIn.coe_toSylow, ← centerOf_subgroupOf, Subgroup.relIndex_subgroupOf hS.le] at h

theorem not_isCyclic_of_isSylowIn {K S : Subgroup D} (hK : CFSG.IsQuasisimple ↥K)
    (hS : IsSylowIn 2 S K) (hS1 : Nat.card ↥S ≠ 1) : ¬ IsCyclic ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  have e : ↥(S.subgroupOf K) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS.le
  have hc' : IsCyclic ↥(hS.toSylow : Subgroup ↥K) := by
    rw [IsSylowIn.coe_toSylow]
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcard : Nat.card ↥(hS.toSylow : Subgroup ↥K) ≠ 1 := by
    rw [IsSylowIn.coe_toSylow, Nat.card_congr e.toEquiv]
    exact hS1
  exact not_isCyclic_sylow_two_of_isPerfect hK.1 hS.toSylow hcard hc'

theorem relIndex_le_card (H S : Subgroup D) : H.relIndex S ≤ Nat.card ↥S := by
  have h := Subgroup.relIndex_mul_card (H := H) (K := S)
  have hpos : 0 < Nat.card ↥(H ⊓ S) := Nat.card_pos
  nlinarith

theorem four_mul_card_le_card_sup {X Y K : Subgroup D}
    (hXK : X ≤ Subgroup.centralizer (K : Set D)) (hYK : Y ≤ K)
    (h4 : 4 ≤ (centerOf K).relIndex Y) : 4 * Nat.card ↥X ≤ Nat.card ↥(X ⊔ Y) := by
  have hXY : X ⊓ Y ≤ centerOf K := fun x hx => ⟨hYK hx.2, hXK hx.1⟩
  have h1 : (centerOf K).relIndex Y ≤ X.relIndex Y := by
    rw [← Subgroup.inf_relIndex_right X Y]
    exact Subgroup.relIndex_le_of_le_left hXY Subgroup.index_ne_zero_of_finite
  have h2 : X.relIndex Y ≤ X.relIndex (X ⊔ Y) :=
    Subgroup.relIndex_le_of_le_right le_sup_right Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_card (H := X) (K := X ⊔ Y)
  rw [inf_eq_left.mpr le_sup_left] at h3
  have h5 : 4 ≤ X.relIndex (X ⊔ Y) := h4.trans (h1.trans h2)
  rw [← h3]
  exact Nat.mul_le_mul_right _ h5

theorem sixteen_mul_card_le {X₁ X₂ X₃ K₁ K₂ K₃ : Subgroup D} (h₁ : X₁ ≤ K₁) (h₂ : X₂ ≤ K₂)
    (h₃ : X₃ ≤ K₃) (c₁₂ : K₁ ≤ Subgroup.centralizer (K₂ : Set D))
    (c₁₃ : K₁ ≤ Subgroup.centralizer (K₃ : Set D)) (c₂₃ : K₂ ≤ Subgroup.centralizer (K₃ : Set D))
    (h4₂ : 4 ≤ (centerOf K₂).relIndex X₂) (h4₃ : 4 ≤ (centerOf K₃).relIndex X₃) :
    16 * Nat.card ↥X₁ ≤ Nat.card ↥(X₁ ⊔ X₂ ⊔ X₃) := by
  have e1 := four_mul_card_le_card_sup (h₁.trans c₁₂) h₂ h4₂
  have e2 := four_mul_card_le_card_sup (X := X₁ ⊔ X₂)
    (sup_le (h₁.trans c₁₃) (h₂.trans c₂₃)) h₃ h4₃
  omega

theorem sq_eq_one_of_card_eq_four {S : Subgroup D} (h4 : Nat.card ↥S = 4) (hnc : ¬ IsCyclic ↥S)
    {x : D} (hx : x ∈ S) : x ^ 2 = 1 := by
  set y : ↥S := ⟨x, hx⟩
  have hdvd : orderOf y ∣ 4 := h4 ▸ orderOf_dvd_natCard y
  have hne : orderOf y ≠ 4 := fun h => hnc (isCyclic_of_orderOf_eq_card y (h.trans h4.symm))
  have h2 : orderOf y ∣ 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf y <;> simp_all
  have hy : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
  have := congrArg Subtype.val hy
  simpa [y] using this

theorem eight_le_card_inf_centralizer {P : Subgroup D}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x ^ 2 = 1)
    (hcard : Nat.card ↥P = 64) {t : D} (htN : t ∈ Subgroup.normalizer (P : Set D))
    (ht2 : t ^ 2 ∈ P) : 8 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set D)) := by
  have hc : ∀ x ∈ P, t * x * t⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  let f : ↥P →* ↥P := MonoidHom.mk' (fun x => ⟨(x : D)⁻¹ * (t * x * t⁻¹),
      P.mul_mem (P.inv_mem x.2) (hc _ x.2)⟩) (by
    intro x y
    apply Subtype.ext
    change ((x : D) * y)⁻¹ * (t * (x * y) * t⁻¹) = (x : D)⁻¹ * (t * x * t⁻¹) *
      ((y : D)⁻¹ * (t * y * t⁻¹))
    have hcomm : (y : D)⁻¹ * ((x : D)⁻¹ * (t * x * t⁻¹)) =
        (x : D)⁻¹ * (t * x * t⁻¹) * (y : D)⁻¹ :=
      hab _ (P.inv_mem y.2) _ (P.mul_mem (P.inv_mem x.2) (hc _ x.2))
    calc ((x : D) * y)⁻¹ * (t * (x * y) * t⁻¹)
        = (y : D)⁻¹ * ((x : D)⁻¹ * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
      _ = (x : D)⁻¹ * (t * x * t⁻¹) * (y : D)⁻¹ * (t * y * t⁻¹) := by rw [hcomm]
      _ = (x : D)⁻¹ * (t * x * t⁻¹) * ((y : D)⁻¹ * (t * y * t⁻¹)) := by group)
  have hf : ∀ x : ↥P, ((f x : ↥P) : D) = (x : D)⁻¹ * (t * x * t⁻¹) := fun x => rfl
  have hrange : f.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hf, hf]
    set a : D := (x : D) with ha_def
    have ha : a ∈ P := x.2
    have ha' : t * a * t⁻¹ ∈ P := hc a ha
    have hta : t ^ 2 * a * (t ^ 2)⁻¹ = a := by
      rw [hab _ ht2 _ ha]
      group
    have hsq' : (a⁻¹ * (t * a * t⁻¹)) * (a⁻¹ * (t * a * t⁻¹)) = 1 := by
      have := hsq _ (P.mul_mem (P.inv_mem ha) ha')
      rwa [pow_two] at this
    have hinv : a⁻¹ * (t * a * t⁻¹) = (t * a * t⁻¹)⁻¹ * a := by
      have h1 : a⁻¹ * (t * a * t⁻¹) = (a⁻¹ * (t * a * t⁻¹))⁻¹ :=
        eq_inv_of_mul_eq_one_left hsq'
      rw [h1]
      group
    have hconj : t * (a⁻¹ * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹)⁻¹ * a := by
      calc t * (a⁻¹ * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹)⁻¹ * (t ^ 2 * a * (t ^ 2)⁻¹) := by
            group
        _ = (t * a * t⁻¹)⁻¹ * a := by rw [hta]
    rw [hconj, ← hinv, inv_mul_cancel]
    rfl
  have hk := Subgroup.card_ker_mul_card_range f
  have hle : Nat.card ↥f.range ≤ Nat.card ↥f.ker := Subgroup.card_le_of_le hrange
  have h8 : 8 ≤ Nat.card ↥f.ker := by nlinarith
  have hmap : f.ker.map P.subtype ≤ P ⊓ Subgroup.centralizer ({t} : Set D) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : D) ∈ Subgroup.centralizer ({t} : Set D)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ((f x : ↥P) : D) = 1 := by
      have hx' : f x = 1 := hx
      rw [hx']
      rfl
    rw [hf] at h1
    have h2 : t * x * t⁻¹ = x := by
      calc t * (x : D) * t⁻¹ = (x : D) * ((x : D)⁻¹ * (t * x * t⁻¹)) := by group
        _ = x := by rw [h1, mul_one]
    calc (x : D) * t = t * x * t⁻¹ * t := by rw [h2]
      _ = t * x := by group
  calc 8 ≤ Nat.card ↥f.ker := h8
    _ = Nat.card ↥(f.ker.map P.subtype) :=
        (Subgroup.card_map_of_injective P.subtype_injective).symm
    _ ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set D)) := Subgroup.card_le_of_le hmap

end CFSG.Quasithin.RonanF610
