module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryLinearNineSylow

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_card_pCoreOf_mul (Y : Subgroup G) :
    Nat.card Y = Nat.card (pCoreOf 2 Y) * (pCoreOf 2 Y).relIndex Y := by
  have h := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
  rw [inf_eq_left.2 (pCoreOf_le 2 Y)] at h
  rw [← h, mul_comm]

theorem exists_le_card_nine {Y : Subgroup G} (h9 : (pCoreOf 2 Y).relIndex Y = 9) :
    ∃ D : Subgroup G, D ≤ Y ∧ Nat.card D = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 2 ∣ Nat.card Y := by
    rw [card_eq_card_pCoreOf_mul, h9]
    exact dvd_mul_left _ _
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨D.map Y.subtype, Subgroup.map_subtype_le D, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hD]
  norm_num

theorem inf_pCoreOf_eq_bot {Y D : Subgroup G} (hD : Nat.card D = 9) :
    D ⊓ pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 Y)
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hD, ha]
  exact Nat.Coprime.pow_right a (by norm_num)

theorem exists_inv_mul_mem {Y D : Subgroup G} (hDY : D ≤ Y) (hD : Nat.card D = 9)
    (h9 : (pCoreOf 2 Y).relIndex Y = 9) {y : G} (hy : y ∈ Y) :
    ∃ d ∈ D, d⁻¹ * y ∈ pCoreOf 2 Y := by
  let f : D → ↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y := fun d => QuotientGroup.mk ⟨d, hDY d.2⟩
  have hinj : Function.Injective f := by
    intro d d' h
    have h' := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h'
    have hmem : (d : G)⁻¹ * d' ∈ D ⊓ pCoreOf 2 Y :=
      ⟨D.mul_mem (D.inv_mem d.2) d'.2, by simpa using h'⟩
    rw [inf_pCoreOf_eq_bot hD, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.1 hmem)
  have hcard : Nat.card (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) ≤ Nat.card D := by
    rw [hD, ← h9]
    exact le_rfl
  obtain ⟨d, hd⟩ := (hinj.bijective_of_nat_card_le hcard).2 (QuotientGroup.mk ⟨y, hy⟩)
  refine ⟨d, d.2, ?_⟩
  have h' := QuotientGroup.eq.1 hd
  rw [Subgroup.mem_subgroupOf] at h'
  simpa using h'

theorem pCoreOf_le_of_le_normalizer {Y : Subgroup G} (U : Sylow 2 G)
    (hUY : (U : Subgroup G) ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (U : Subgroup G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hUY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have h1 : IsPGroup 2 (↑U ⊔ pCoreOf 2 Y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' U.isPGroup' (pCoreOf_isPGroup 2 Y) hN
  exact le_sup_right.trans (U.is_maximal' h1 le_sup_left).le

omit [Finite G] in
theorem mul_comm_of_le_normalizer {Y D U : Subgroup G} (hDY : D ≤ Y)
    (hUY : U ≤ Subgroup.normalizer (Y : Set G)) (hPU : pCoreOf 2 Y ≤ U)
    (hdec : ∀ y ∈ Y, ∃ d ∈ D, d⁻¹ * y ∈ pCoreOf 2 Y) :
    (D : Set G) * (U : Set G) = (U : Set G) * (D : Set G) := by
  ext x
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨d, hd, u, hu, rfl⟩
    have hy : u⁻¹ * d * u ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.1 (hUY (U.inv_mem hu)) d).1 (hDY hd)
      simpa using this
    obtain ⟨d', hd', hp⟩ := hdec _ (Y.inv_mem hy)
    exact ⟨u * (d'⁻¹ * (u⁻¹ * d * u)⁻¹)⁻¹, U.mul_mem hu (U.inv_mem (hPU hp)), d'⁻¹,
      D.inv_mem hd', by group⟩
  · rintro ⟨u, hu, d, hd, rfl⟩
    have hy : u * d * u⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hUY hu) d).1 (hDY hd)
    obtain ⟨d', hd', hp⟩ := hdec _ hy
    exact ⟨d', hd', d'⁻¹ * (u * d * u⁻¹) * u, U.mul_mem (hPU hp) hu, by group⟩

omit [Finite G] in
theorem le_sup_of_dec {Y D U : Subgroup G} (hPU : pCoreOf 2 Y ≤ U)
    (hdec : ∀ y ∈ Y, ∃ d ∈ D, d⁻¹ * y ∈ pCoreOf 2 Y) : Y ≤ D ⊔ U := by
  intro y hy
  obtain ⟨d, hd, hp⟩ := hdec y hy
  have hy' : y = d * (d⁻¹ * y) := by group
  rw [hy']
  exact Subgroup.mul_mem_sup hd (hPU hp)

omit [Finite G] in
theorem commutator_mem_pCoreOf {Y H R : Subgroup G} (hYH : Y ≤ H) (hR : IsPGroup 2 R)
    (hRH : ∀ x ∈ H, ∀ r ∈ R, x * r * x⁻¹ ∈ R) {c w : G} (hc : c ∈ R)
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y) :
    c * w * c⁻¹ * w⁻¹ ∈ pCoreOf 2 Y := by
  have hRY : R ⊓ Y ≤ pCoreOf 2 Y := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun y hy => ?_) (hR.to_le inf_le_left)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hzR, hzY⟩
      exact ⟨hRH y (hYH hy) z hzR, Y.mul_mem (Y.mul_mem hy hzY) (Y.inv_mem hy)⟩
    · rintro ⟨hzR, hzY⟩
      have h1 := hRH y⁻¹ (hYH (Y.inv_mem hy)) _ hzR
      have h2 : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ ∈ Y :=
        Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hzY) (Y.inv_mem (Y.inv_mem hy))
      have he : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
      rw [he] at h1 h2
      exact ⟨h1, h2⟩
  refine hRY ⟨?_, ?_⟩
  · have h1 := hRH w (hYH hw) _ (R.inv_mem hc)
    have he : c * w * c⁻¹ * w⁻¹ = c * (w * c⁻¹ * w⁻¹) := by group
    rw [he]
    exact R.mul_mem hc h1
  · exact Y.mul_mem ((Subgroup.mem_normalizer_iff.1 hcY w).1 hw) (Y.inv_mem hw)

end General

section Linear

open Matrix CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] [Finite K]

theorem mul_comm_of_isPGroup_GL_two (hK : Nat.card K = 2) {H : Subgroup (GL (Fin 2) K)}
    (hH : IsPGroup 2 H) {x y : GL (Fin 2) K} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hH
  have h6 : 2 ^ k ∣ 6 := by
    rw [← hk, ← SteinbergCH.card_GL_two_of_card_two hK]
    exact Subgroup.card_subgroup_dvd_card H
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans h6
    norm_num at h4
  interval_cases k
  · have hbot : H = ⊥ := Subgroup.eq_bot_of_card_eq H (by simpa using hk)
    rw [hbot, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · have : IsCyclic H := isCyclic_of_prime_card (p := 2) (by simpa using hk)
    have h := (IsMulCommutative.is_comm (M := H)).comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val h

theorem exists_radical_of_card_nine (hK : Nat.card K = 2) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (B₂ : Sylow 2 (SpecialLinearGroup (Fin n) K)) {D : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hD : Nat.card D = 9)
    (hDB : (D : Set (SpecialLinearGroup (Fin n) K)) * (B₂ : Set (SpecialLinearGroup (Fin n) K)) =
      (B₂ : Set (SpecialLinearGroup (Fin n) K)) * (D : Set (SpecialLinearGroup (Fin n) K))) :
    ∃ R : Subgroup (SpecialLinearGroup (Fin n) K), R ≤ D ⊔ B₂ ∧ IsPGroup 2 R ∧
      (∀ x ∈ D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)), ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      ∀ a ∈ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)),
        ∀ b ∈ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)), a * b * a⁻¹ * b⁻¹ ∈ R := by
  obtain ⟨-, -, hrest⟩ :=
    binary_linear_four_five_nine_Sylow_products_have_abelian_inner_common_action hK hn B₂
  obtain ⟨-, ⟨g, a, -, -, -, -, -, hRle, hRnormal, hRp, φ, -, hφker, -, -, -⟩, -⟩ :=
    hrest D hD hDB
  refine ⟨_, hRle, hRp, fun x hx r hr => hRnormal.conj_mem ⟨r, hRle hr⟩ hr ⟨x, hx⟩,
    fun u hu v hv => ?_⟩
  set f := φ.comp (Subgroup.inclusion
    (le_sup_right : (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) ≤ D ⊔ B₂)) with hf
  have hcomm : f ⟨u, hu⟩ * f ⟨v, hv⟩ = f ⟨v, hv⟩ * f ⟨u, hu⟩ := by
    have hp1 : IsPGroup 2 ((MonoidHom.fst _ _).comp f).range :=
      B₂.isPGroup'.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have hp2 : IsPGroup 2 ((MonoidHom.snd _ _).comp f).range :=
      B₂.isPGroup'.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    refine Prod.ext ?_ ?_
    · exact mul_comm_of_isPGroup_GL_two hK hp1 ⟨⟨u, hu⟩, rfl⟩ ⟨⟨v, hv⟩, rfl⟩
    · exact mul_comm_of_isPGroup_GL_two hK hp2 ⟨⟨u, hu⟩, rfl⟩ ⟨⟨v, hv⟩, rfl⟩
  have hker : f (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hmem : (Subgroup.inclusion le_sup_right (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ :
      ↥(B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) :
        ↥(D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)))) ∈ φ.ker := hker
  rw [hφker] at hmem
  exact hmem

end Linear

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
