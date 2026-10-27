module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H30

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem pow_four_eq {G : Type*} [Monoid G] (x : G) : x ^ 2 ^ 2 = x * x * (x * x) := by
  rw [show 2 ^ 2 = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one]
  simp only [mul_assoc]

theorem false_of_flag14 {X : Subgroup (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))}
    (h1 : InvStd X 1) (h4 : InvStd X 4) (hfix : ∀ v ∈ fixN X, v ∈ stdE (1 + 4) 1)
    (hcard : Nat.card X = Nat.card (o2G X) * 168)
    {y : Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))))
    (hy3 : orderOf y = 3) (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X) : False := by
  have hX1 : X ≤ stabStd 1 4 := le_stabStd_of_invStd h1
  obtain ⟨φ, hφd⟩ : ∃ φ : ↥X →* Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2),
      φ = (botH 1 4).comp (Subgroup.inclusion hX1) := ⟨_, rfl⟩
  have hφx : ∀ x : ↥X, φ x = botH 1 4 ⟨x.1, hX1 x.2⟩ := fun x => by rw [hφd]; rfl
  have hφS : ∀ x : ↥X, φ x ∈ stabStd 3 1 := by
    intro x
    rw [mem_stabStd, hφx]
    intro i j
    have hc : Pi.single (Fin.natAdd 1 (Fin.castAdd 1 j)) (1 : ZMod 2) ∈ stdE (1 + 4) 4 :=
      single_mem_stdE (by simp; omega)
    have h := h4 x.1 x.2 _ hc (Fin.natAdd 1 (Fin.natAdd 3 i)) (by simp)
    rw [smul_eq_mulVec', mulVec_single_one] at h
    exact h
  have hX' : φ.range ≤ stabStd 3 1 := by
    rintro _ ⟨x, rfl⟩
    exact hφS x
  obtain ⟨φ₃, hφ₃⟩ : ∃ φ₃ : ↥X →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      φ₃ = (topH 3 1).comp (φ.codRestrict (stabStd 3 1) hφS) := ⟨_, rfl⟩
  have hφ₃x : ∀ x : ↥X, φ₃ x = topH 3 1 ⟨φ x, hφS x⟩ := fun x => by rw [hφ₃]; rfl
  have hker : ∀ x, φ₃ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    rw [hφ₃x] at hx
    have h2 : φ x * φ x = 1 := sq_eq_one_of_blocks (hφS x) (congrArg Subtype.val hx)
      (botB_eq_one_of_one ⟨φ x, hφS x⟩)
    have hxx : x.1 * x.1 ∈ stabStd 1 4 := hX1 (X.mul_mem x.2 x.2)
    have h3 : (x.1 * x.1) * (x.1 * x.1) = 1 := by
      refine sq_eq_one_of_blocks hxx (topB_eq_one_of_one ⟨_, hxx⟩) ?_
      have : φ (x * x) = 1 := by rw [map_mul, h2]
      rw [hφx] at this
      exact congrArg Subtype.val this
    exact ⟨2, Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_four_eq, h3, Subgroup.coe_one])⟩
  have hle : φ₃.range ≤ (φ.range.subgroupOf (stabStd 3 1)).map (topH 3 1) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨φ x, hφS x⟩, Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩, (hφ₃x x).symm⟩
  have himg : (φ.range.subgroupOf (stabStd 3 1)).map (topH 3 1) = ⊤ :=
    Subgroup.eq_top_of_le_card _ (by
      rw [card_SL_three_two]
      exact (card_range_ge φ₃ hker hcard).trans (Subgroup.card_le_of_le hle))
  have he0 : ∀ v ∈ stdE (1 + 4) 1, v ∈ fixN X := fun v hv x hx =>
    smul_eq_of_topB_one (hX1 hx) (topB_eq_one_of_one ⟨x, hX1 hx⟩) hv
  have hyS : y ∈ stabStd 1 4 := presStd_of_smul_mem fun j =>
    hfix _ (smul_mem_fixN hyN (he0 _ (castAdd_mem_stdE j)))
  obtain ⟨y', hy'⟩ : ∃ y' : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2),
      y' = botH 1 4 ⟨y, hyS⟩ := ⟨_, rfl⟩
  have hyX : ∀ x : ↥X, ∃ x' : ↥X, φ x' = y' * φ x * y'⁻¹ ∧ x'.1 = y * x.1 * y⁻¹ := by
    intro x
    have hxt : y * x.1 * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hyN _).mp x.2
    refine ⟨⟨_, hxt⟩, ?_, rfl⟩
    rw [hφx, hφx, hy', show (⟨y * x.1 * y⁻¹, hX1 hxt⟩ : ↥(stabStd 1 4)) =
      ⟨y, hyS⟩ * ⟨x.1, hX1 x.2⟩ * (⟨y, hyS⟩)⁻¹ from rfl, map_mul, map_mul, map_inv]
  have hy'3 : y' ^ 3 = 1 := by rw [hy', ← map_pow, pow_three_stab hy3 hyS, map_one]
  have hfwd : ∀ z ∈ φ.range, y' * z * y'⁻¹ ∈ φ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx', -⟩ := hyX x
    exact ⟨x', hx'⟩
  have hyN' : y' ∈ Subgroup.normalizer
      (φ.range : Set (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd z, fun hz => ?_⟩
    have h2 := hfwd _ (hfwd _ hz)
    have hy'3' : y' * y' * y' = 1 := by rw [mul_assoc, ← pow_three]; exact hy'3
    rwa [show y' * (y' * (y' * z * y'⁻¹) * y'⁻¹) * y'⁻¹ =
      (y' * y' * y') * z * (y' * y' * y')⁻¹ by group, hy'3', one_mul, inv_one, mul_one] at h2
  have hNle : (CFSG.pCore 2 ↥X).map φ ≤ o2G φ.range := by
    refine le_o2G φ.range (Subgroup.map_le_range _ _) ?_ (CFSG.pCore_isPGroup.map φ)
    refine le_normalizer_of_conj ?_
    rintro _ ⟨x, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨x * q * x⁻¹, CFSG.pCore_normal.conj_mem q hq x, by rw [map_mul, map_mul, map_inv]⟩
  have hyc' : ∀ z ∈ φ.range, y' * z * y'⁻¹ * z⁻¹ ∈ o2G φ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx', hx'1⟩ := hyX x
    have hq : x' * x⁻¹ ∈ CFSG.pCore 2 ↥X := (mem_pCore_iff _).mpr (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hx'1]
      exact hyc x.1 x.2)
    refine hNle ⟨x' * x⁻¹, hq, ?_⟩
    rw [map_mul, map_inv, hx']
  have hy'S := mem_stabStd_of_normalizer (k := 1) hX' himg (fun x _ => sl1_eq_one _) hyN'
  have htop := eq_one_of_center_section hX' (topH 3 1) himg (y := ⟨y', hy'S⟩) hyc'
  have hy'2 : y' * y' = 1 := sq_eq_one_of_blocks hy'S (congrArg Subtype.val htop)
    (botB_eq_one_of_one ⟨y', hy'S⟩)
  have hyy : y * y ∈ stabStd 1 4 := (stabStd 1 4).mul_mem hyS hyS
  have hy4 : (y * y) * (y * y) = 1 := by
    refine sq_eq_one_of_blocks hyy (topB_eq_one_of_one ⟨_, hyy⟩) ?_
    have : botH 1 4 ⟨y * y, hyy⟩ = 1 := by
      rw [show (⟨y * y, hyy⟩ : ↥(stabStd 1 4)) = ⟨y, hyS⟩ * ⟨y, hyS⟩ from rfl, map_mul, ← hy',
        hy'2]
    exact congrArg Subtype.val this
  have hy1 : y = 1 := by
    have h3 : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
    calc y = (y * y) * (y * y) * (y ^ 3)⁻¹ := by group
      _ = 1 := by rw [hy4, h3]; group
  rw [hy1, orderOf_one] at hy3
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
