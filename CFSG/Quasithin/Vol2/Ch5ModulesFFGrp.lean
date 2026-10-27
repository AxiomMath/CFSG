module

public import CFSG.Quasithin.Vol2.Ch5ModulesFFOrd
public import CFSG.Quasithin.Background.JonesParshallG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open Matrix
open scoped commutatorElement

theorem isPGroup_closure_pair {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 4 = 1) : IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxx : ∀ g : G, x * (x * g) = g := fun g => by rw [← mul_assoc, hx, one_mul]
  have hyy : ∀ g : G, y * (y * g) = g := fun g => by rw [← mul_assoc, hy, one_mul]
  have hyx : y * x = (x * y)⁻¹ := by rw [_root_.mul_inv_rev, hxi, hyi]
  have hrel : x * (y * (x * y)) = y * (x * (y * x)) := by
    have ha : (x * y) ^ 2 * (x * y) ^ 2 = 1 := by rw [← pow_add]; exact hxy
    have hb : (x * y) ^ 2 = ((x * y) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left ha
    rw [← inv_pow, ← hyx] at hb
    simpa only [pow_two, mul_assoc] using hb
  let D : Set G := {1, x, y, x * y, y * x, x * (y * x), y * (x * y), x * (y * (x * y))}
  have hD : ∀ g ∈ Subgroup.closure ({x, y} : Set G), g ∈ D := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => simp [D]
    | mul_left s hs g _ ih =>
      rcases hs with rfl | rfl
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
        rcases ih with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hxx, hx]
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
        rcases ih with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hyy, hy, hrel]
    | inv_mul_cancel s hs g _ ih =>
      rcases hs with rfl | rfl
      · rw [hxi]
        simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
        rcases ih with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hxx, hx]
      · rw [hyi]
        simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
        rcases ih with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hyy, hy, hrel]
  have hsq : ∀ g : G, g * g = 1 → g ^ 4 = 1 := fun g hg => by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_two g, hg, one_pow]
  have hpow : ∀ g ∈ D, g ^ 4 = 1 := by
    intro g hg
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> rw [h]
    · exact one_pow 4
    · exact hsq x hx
    · exact hsq y hy
    · exact hxy
    · rw [hyx, inv_pow, hxy, inv_one]
    · exact hsq _ (by simp only [mul_assoc, hxx, hyy, hx])
    · exact hsq _ (by simp only [mul_assoc, hxx, hyy, hy])
    · have h2 : x * (y * (x * y)) = (x * y) ^ 2 := by rw [pow_two, mul_assoc]
      rw [h2, ← pow_mul, show 2 * 4 = 4 * 2 by rfl, pow_mul, hxy, one_pow]
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  simpa using hpow g (hD g g.2)

theorem psl2_sq_eq_one_of_pow_four {f : ℕ} (hf : 2 ≤ f)
    {x y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : (x * y) ^ 4 = 1) : (x * y) ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (isPGroup_closure_pair hx hy hxy).exists_le_sylow
  have hab := (CFSG.Walter.psl2_even_sylow_two hf S).1
  have hxS : x ∈ (S : Subgroup _) := hS (Subgroup.subset_closure (by simp))
  have hyS : y ∈ (S : Subgroup _) := hS (Subgroup.subset_closure (by simp))
  have hc : x * y = y * x :=
    congrArg Subtype.val (hab.toIsMulCommutative.is_comm.comm ⟨x, hxS⟩ ⟨y, hyS⟩)
  rw [pow_two, mul_assoc, ← mul_assoc y x y, ← hc, mul_assoc, hy, mul_one, hx]

section SL3

variable {F : Type} [Field F]

theorem g2A_injective : Function.Injective (g2A : SL3 F →* ↥(cayleyGroup F)) := by
  intro A B h
  have hu : ∀ u : Fin 3 → F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ u =
      (B : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
    intro u
    have h1 := congrArg (fun g : ↥(cayleyGroup F) =>
      (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ((0 : F), u, (0 : Fin 3 → F), (0 : F))) h
    simp only [g2A_apply, gAFun] at h1
    exact congrArg (fun x : quasithinZorn F => x.2.1) h1
  exact Subtype.ext (Matrix.ext_iff_mulVec.mpr hu)

theorem sl3_map_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) f) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 3) S =>
    (C : Matrix (Fin 3) (Fin 3) S) i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h1
  exact hf h1

@[expose] def sl3x0 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

@[expose] def sl3y0 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

theorem sl3x0_mul_self : sl3x0 * sl3x0 = 1 := by decide

theorem sl3y0_mul_self : sl3y0 * sl3y0 = 1 := by decide

theorem sl3x0y0_pow_four : (sl3x0 * sl3y0) ^ 4 = 1 := by decide

theorem sl3x0y0_sq_ne_one : (sl3x0 * sl3y0) ^ 2 ≠ 1 := by decide

end SL3

@[expose] def sl3t13 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

@[expose] def sl3t32 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by rw [Matrix.det_fin_three]; decide⟩

@[expose] def sl3t21 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

theorem sl3x0_eq_commutator : ⁅sl3t13, sl3t32⁆ = sl3x0 := by decide

theorem sl3y0_eq_commutator : ⁅sl3t21, sl3t13⁆ = sl3y0 := by decide

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hF])

theorem exists_injective_sl3_g2 {F : Type} [Field F] [CharP F 2] :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* ↥(quasithinG2 F),
      Function.Injective φ := by
  have hEq : quasithinG2 F = cayleyGroup F :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  let ι : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  refine ⟨(MulEquiv.subgroupCongr hEq).symm.toMonoidHom.comp
    ((g2A : SL3 F →* ↥(cayleyGroup F)).comp (Matrix.SpecialLinearGroup.map ι)), ?_⟩
  exact (MulEquiv.subgroupCongr hEq).symm.injective.comp
    (g2A_injective.comp (sl3_map_injective ι.injective))

theorem false_of_mulEquiv_psl2_of_d8 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (eL : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) {x y : X}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 4 = 1) (h2 : (x * y) ^ 2 ≠ 1) : False := by
  have h1 := psl2_sq_eq_one_of_pow_four hn (x := eL x) (y := eL y)
    (by rw [← map_mul, hx, map_one]) (by rw [← map_mul, hy, map_one])
    (by rw [← map_mul, ← map_pow, hxy, map_one])
  rw [← map_mul, ← map_pow, MulEquiv.map_eq_one_iff] at h1
  exact h2 h1

theorem false_of_mulEquiv_psl2_of_d8_mem {Y : Type} [Group Y] {H : Subgroup Y} {n : ℕ}
    (hn : 2 ≤ n) (eL : ↥H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {x y : Y} (hxH : x ∈ H) (hyH : y ∈ H) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 4 = 1) (h2 : (x * y) ^ 2 ≠ 1) : False := by
  refine false_of_mulEquiv_psl2_of_d8 hn eL (x := ⟨x, hxH⟩) (y := ⟨y, hyH⟩)
    (Subtype.ext hx) (Subtype.ext hy) (Subtype.ext (by simpa using hxy)) fun h => h2 ?_
  simpa using congrArg Subtype.val h

theorem exists_d8_g2 {F : Type} [Field F] [CharP F 2] :
    ∃ x y : quasithinZorn F ≃ₗ[F] quasithinZorn F,
      x ∈ ⁅quasithinG2 F, quasithinG2 F⁆ ∧ y ∈ ⁅quasithinG2 F, quasithinG2 F⁆ ∧
      x * x = 1 ∧ y * y = 1 ∧ (x * y) ^ 4 = 1 ∧ (x * y) ^ 2 ≠ 1 := by
  obtain ⟨φ, hφ⟩ := exists_injective_sl3_g2 (F := F)
  let c : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) → quasithinZorn F ≃ₗ[F] quasithinZorn F :=
    fun g => (φ g : quasithinZorn F ≃ₗ[F] quasithinZorn F)
  have hc : ∀ g h, c (g * h) = c g * c h := fun g h => by
    simp only [c, map_mul, Subgroup.coe_mul]
  have hc1 : c 1 = 1 := by simp only [c, map_one, Subgroup.coe_one]
  have hcpow : ∀ g (k : ℕ), c (g ^ k) = c g ^ k := fun g k => by
    simp only [c, map_pow, Subgroup.coe_pow]
  have hcinv : ∀ g, c g⁻¹ = (c g)⁻¹ := fun g => by
    simp only [c, map_inv, Subgroup.coe_inv]
  have hcomm : ∀ g h, c ⁅g, h⁆ ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := fun g h => by
    have e1 : c ⁅g, h⁆ = ⁅c g, c h⁆ := by
      rw [commutatorElement_def, commutatorElement_def, hc, hc, hc, hcinv, hcinv]
    rw [e1]
    exact Subgroup.commutator_mem_commutator (φ g).2 (φ h).2
  refine ⟨c sl3x0, c sl3y0, sl3x0_eq_commutator ▸ hcomm _ _, sl3y0_eq_commutator ▸ hcomm _ _,
    by rw [← hc, sl3x0_mul_self, hc1], by rw [← hc, sl3y0_mul_self, hc1],
    by rw [← hc, ← hcpow, sl3x0y0_pow_four, hc1], fun h => sl3x0y0_sq_ne_one ?_⟩
  rw [← hc, ← hcpow, ← hc1] at h
  exact hφ (Subtype.ext h)

theorem false_of_mulEquiv_psl2_g2 {X : Type} [Group X] {n m : ℕ} (hn : 2 ≤ n)
    (eL : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ m) (eG : X ≃* ↥(quasithinG2 F)) : False := by
  have := charP_two_of_card hF
  obtain ⟨x, y, hxD, hyD, hx, hy, hxy, h2⟩ := exists_d8_g2 (F := F)
  have hle : ⁅quasithinG2 F, quasithinG2 F⁆ ≤ quasithinG2 F :=
    Subgroup.commutator_le.mpr fun a ha b hb =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)
  exact false_of_mulEquiv_psl2_of_d8_mem hn (eG.symm.trans eL) (hle hxD) (hle hyD) hx hy hxy h2

theorem false_of_mulEquiv_psl2_g2_commutator {X : Type} [Group X] {n m : ℕ} (hn : 2 ≤ n)
    (eL : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ m)
    (eG : X ≃* ↥⁅quasithinG2 F, quasithinG2 F⁆) : False := by
  have := charP_two_of_card hF
  obtain ⟨x, y, hxD, hyD, hx, hy, hxy, h2⟩ := exists_d8_g2 (F := F)
  exact false_of_mulEquiv_psl2_of_d8_mem hn (eG.symm.trans eL) hxD hyD hx hy hxy h2

theorem seven_dvd_card_g2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    7 ∣ Nat.card ↥(quasithinG2 F) := by
  obtain ⟨φ, hφ⟩ := exists_injective_sl3_g2 (F := F)
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
      (ZMod 2)).toEquiv]
    exact card_statedSL_three_zmodTwo
  have h2 : Nat.card φ.range = 168 := by
    rw [← h1]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  have h3 : 168 ∣ Nat.card ↥(quasithinG2 F) := h2 ▸ Subgroup.card_subgroup_dvd_card φ.range
  exact (show (7 : ℕ) ∣ 168 by norm_num).trans h3

end CFSG.Quasithin.H13
