module

public import CFSG.RankThree.PartOne.KFR4.BlkShort
public import CFSG.RankThree.PartOne.KFR4.BlkLong

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Unitary

namespace Blk

section Images

variable {G H : Type*} [Group G] [Group H]

theorem isSimpleGroup_of_range [IsSimpleGroup H] {f : H →* G} (hf : Function.Injective f)
    {B : Subgroup G} (hB : f.range = B) : IsSimpleGroup B := by
  subst hB
  exact (MonoidHom.ofInjective hf).symm.isSimpleGroup

theorem commutator_eq_of_range [Group.IsPerfect H] (f : H →* G) {B : Subgroup G}
    (hB : f.range = B) : ⁅B, B⁆ = B := by
  subst hB
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)

theorem eq_bot_or_eq_of_isSimpleGroup {B N : Subgroup G} [IsSimpleGroup B] (hN : N ≤ B)
    (hnorm : (N.subgroupOf B).Normal) : N = ⊥ ∨ N = B := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.mp (h.mono_right hN)
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hN h

end Images

section Coords

variable {p : ℕ}

theorem fin3_cases {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : Fin 3) :
    x = i ∨ x = j ∨ x = k := by
  by_cases hxi : x = i
  · exact Or.inl hxi
  · by_cases hxj : x = j
    · exact Or.inr (Or.inl hxj)
    · exact Or.inr (Or.inr (fin3_eq_of_ne hij hik hjk hxi hxj))

theorem exists_smul_single_iff (i : Fin 3) (a : Fin 3 → ZMod p) :
    (∃ l : ZMod p, a = l • (Pi.single i 1 : Fin 3 → ZMod p)) ↔ ∀ j, j ≠ i → a j = 0 := by
  constructor
  · rintro ⟨l, rfl⟩ j hj
    simp [hj]
  · intro h
    refine ⟨a i, funext fun x => ?_⟩
    by_cases hx : x = i
    · subst hx
      simp
    · simp [hx, h x hx]

theorem exists_smul_sub_iff {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Fin 3 → ZMod p) :
    (∃ l : ZMod p, a = l • ((Pi.single i 1 : Fin 3 → ZMod p) - Pi.single j 1)) ↔
      a k = 0 ∧ a i + a j = 0 := by
  constructor
  · rintro ⟨l, rfl⟩
    simp [hij, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  · rintro ⟨hk, hs⟩
    refine ⟨a i, funext fun x => ?_⟩
    rcases fin3_cases hij hik hjk x with rfl | rfl | rfl
    · simp [hij]
    · simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, Ne.symm hij, ↓reduceIte,
        smul_eq_mul]
      linear_combination hs
    · simp [Ne.symm hik, Ne.symm hjk, hk]

theorem exists_smul_add_iff {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Fin 3 → ZMod p) :
    (∃ l : ZMod p, a = l • ((Pi.single i 1 : Fin 3 → ZMod p) + Pi.single j 1)) ↔
      a k = 0 ∧ a i = a j := by
  constructor
  · rintro ⟨l, rfl⟩
    simp [hij, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  · rintro ⟨hk, hs⟩
    refine ⟨a i, funext fun x => ?_⟩
    rcases fin3_cases hij hik hjk x with rfl | rfl | rfl
    · simp [hij]
    · simp [Ne.symm hij, hs]
    · simp [Ne.symm hik, Ne.symm hjk, hk]

theorem vecp_s1 : Root.vecp p .s1 = Pi.single 0 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_s2 : Root.vecp p .s2 = Pi.single 1 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_s3 : Root.vecp p .s3 = Pi.single 2 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_m12 : Root.vecp p .m12 = Pi.single 0 1 - Pi.single 1 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_m13 : Root.vecp p .m13 = Pi.single 0 1 - Pi.single 2 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_m23 : Root.vecp p .m23 = Pi.single 1 1 - Pi.single 2 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_p12 : Root.vecp p .p12 = Pi.single 0 1 + Pi.single 1 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_p13 : Root.vecp p .p13 = Pi.single 0 1 + Pi.single 2 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem vecp_p23 : Root.vecp p .p23 = Pi.single 1 1 + Pi.single 2 1 := by
  funext x; fin_cases x <;> simp [Root.vecp, Root.vec]

theorem flipVec_self (k : Fin 3) (a : Fin 3 → ZMod p) : flipVec k a k = -(a k) :=
  Function.update_self _ _ _

theorem flipVec_of_ne {k x : Fin 3} (h : x ≠ k) (a : Fin 3 → ZMod p) : flipVec k a x = a x :=
  Function.update_of_ne h _ _

theorem flipVec_flipVec (k : Fin 3) (a : Fin 3 → ZMod p) : flipVec k (flipVec k a) = a := by
  funext x
  by_cases hx : x = k
  · subst hx
    rw [flipVec_self, flipVec_self, neg_neg]
  · rw [flipVec_of_ne hx, flipVec_of_ne hx]

end Coords

section Kinds

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  (S : StdData K E p)

include S in
theorem four_le_card : 4 ≤ Nat.card K := by
  have h1 := Nat.le_of_dvd (Nat.succ_pos _) S.hpq
  have h2 := S.hp5
  omega

include S in
theorem four_le_card_E : 4 ≤ Nat.card E := by
  rw [S.D.card_E]
  have := four_le_card S
  nlinarith

theorem long_model {i j : Fin 3} (hij : i ≠ j) : ∃ (H : Type) (_ : Group H), IsSimpleGroup H ∧
    Group.IsPerfect H ∧ ∃ f : H →* (Vs K E ≃ₗ[K] Vs K E), Function.Injective f ∧
      f.range = longBlock S.D i j := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := S.D.finite_E
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  obtain ⟨ψ⟩ := nonempty_sl2_mulEquiv_SUid S.D hf
  have hE : Nat.card E = (2 ^ f) ^ 2 := by rw [S.D.card_E, hf]
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield E 2 f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hE, ← hf]
    exact four_le_card S
  exact ⟨_, _, sl2_isSimpleGroup h4, sl2_isPerfect h4, _, longHom_injective S.D hij ψ,
    (longBlock_eq_range S.D hij ψ).symm⟩

theorem plong_model {i j : Fin 3} (hij : i ≠ j) : ∃ (H : Type) (_ : Group H),
    IsSimpleGroup H ∧ Group.IsPerfect H ∧ ∃ f : H →* (Vs K E ≃ₗ[K] Vs K E),
      Function.Injective f ∧
        f.range = (longBlock S.D i j).map (MulAut.conj (conjCoord S.D j)).toMonoidHom := by
  obtain ⟨H, _, hs, hp, f, hf, hB⟩ := long_model S hij
  refine ⟨H, inferInstance, hs, hp, (MulAut.conj (conjCoord S.D j)).toMonoidHom.comp f,
    (MulAut.conj (conjCoord S.D j)).injective.comp hf, ?_⟩
  rw [MonoidHom.range_comp, hB]

theorem plong_le_O (i j : Fin 3) :
    (longBlock S.D i j).map (MulAut.conj (conjCoord S.D j)).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (Qs S.D) := by
  rintro _ ⟨g, hg, rfl⟩
  have hc := conjCoord_mem_O S.D j
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact mul_mem (mul_mem hc (longBlock_le_O S.D i j hg)) (inv_mem hc)

theorem plong_commute {i j : Fin 3} (hij : i ≠ j) {a : Fin 3 → ZMod p} (ha : a i + a j = 0)
    {g : Vs K E ≃ₗ[K] Vs K E}
    (hg : g ∈ (longBlock S.D i j).map (MulAut.conj (conjCoord S.D j)).toMonoidHom) :
    g * tor S a = tor S a * g := by
  obtain ⟨_, ⟨M, hM, rfl⟩, rfl⟩ := hg
  have hflip : flipVec j a i = flipVec j a j := by
    rw [flipVec_of_ne hij, flipVec_self]
    linear_combination ha
  have h1 := matToG_commute_tor S hM hflip
  have h2 : tor S a = conjCoord S.D j * tor S (flipVec j a) * (conjCoord S.D j)⁻¹ := by
    rw [conj_tor, flipVec_flipVec]
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h2]
  calc conjCoord S.D j * matToG K M * (conjCoord S.D j)⁻¹ *
        (conjCoord S.D j * tor S (flipVec j a) * (conjCoord S.D j)⁻¹)
      = conjCoord S.D j * (matToG K M * tor S (flipVec j a)) * (conjCoord S.D j)⁻¹ := by group
    _ = conjCoord S.D j * (tor S (flipVec j a) * matToG K M) * (conjCoord S.D j)⁻¹ := by rw [h1]
    _ = conjCoord S.D j * tor S (flipVec j a) * (conjCoord S.D j)⁻¹ *
        (conjCoord S.D j * matToG K M * (conjCoord S.D j)⁻¹) := by group

theorem tor_mem_plong_iff {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Fin 3 → ZMod p) :
    tor S a ∈ (longBlock S.D i j).map (MulAut.conj (conjCoord S.D j)).toMonoidHom ↔
      a k = 0 ∧ a i = a j := by
  have h2 : tor S a = conjCoord S.D j * tor S (flipVec j a) * (conjCoord S.D j)⁻¹ := by
    rw [conj_tor, flipVec_flipVec]
  have h3 : (conjCoord S.D j)⁻¹ * tor S a * conjCoord S.D j = tor S (flipVec j a) := by
    rw [h2]
    group
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, h3, tor_mem_longBlock_iff S hij hik hjk,
    flipVec_of_ne (Ne.symm hjk), flipVec_of_ne hij, flipVec_self, ← sub_eq_add_neg, sub_eq_zero]

variable [Module.Finite K E]

theorem short_model (i : Fin 3) : ∃ (H : Type) (_ : Group H), IsSimpleGroup H ∧
    Group.IsPerfect H ∧ ∃ f : H →* (Vs K E ≃ₗ[K] Vs K E), Function.Injective f ∧
      f.range = Supp S.D {i} ⊓ Om S.D := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  exact ⟨_, _, sl2_isSimpleGroup (four_le_card_E S), sl2_isPerfect (four_le_card_E S), _,
    extS_comp_rho_injective S.D i (four_le_card_E S), (supp_inf_Om_eq_range S.D i).symm⟩

end Kinds

section All

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

theorem exists_model (ρ : Root) : ∃ (H : Type) (_ : Group H), IsSimpleGroup H ∧
    Group.IsPerfect H ∧ ∃ f : H →* (Vs K E ≃ₗ[K] Vs K E), Function.Injective f ∧
      f.range = Block S.D ρ := by
  cases ρ
  · exact short_model S 0
  · exact short_model S 1
  · exact short_model S 2
  · exact long_model S (by decide)
  · exact long_model S (by decide)
  · exact long_model S (by decide)
  · exact plong_model S (by decide)
  · exact plong_model S (by decide)
  · exact plong_model S (by decide)

omit [Module.Finite K E] in
theorem block_le_O (ρ : Root) : Block S.D ρ ≤ TauCeti.QuadraticMap.orthogonalGroup (Qs S.D) := by
  cases ρ
  · exact fun g hg => (Subgroup.mem_inf.mp hg).1.1
  · exact fun g hg => (Subgroup.mem_inf.mp hg).1.1
  · exact fun g hg => (Subgroup.mem_inf.mp hg).1.1
  · exact longBlock_le_O S.D 0 1
  · exact longBlock_le_O S.D 0 2
  · exact longBlock_le_O S.D 1 2
  · exact plong_le_O S 0 1
  · exact plong_le_O S 0 2
  · exact plong_le_O S 1 2

theorem isSimpleGroup_block (ρ : Root) : IsSimpleGroup (Block S.D ρ) := by
  obtain ⟨H, _, hs, -, f, hf, hB⟩ := exists_model S ρ
  exact isSimpleGroup_of_range hf hB

theorem commutator_block (ρ : Root) : ⁅Block S.D ρ, Block S.D ρ⁆ = Block S.D ρ := by
  obtain ⟨H, _, -, hp, f, -, hB⟩ := exists_model S ρ
  exact commutator_eq_of_range f hB

end All

end Blk

section Std

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

theorem block_le_Om (ρ : Root) : Block S.D ρ ≤ Om S.D := by
  rw [← Blk.commutator_block S ρ]
  exact Subgroup.commutator_mono (Blk.block_le_O S ρ) (Blk.block_le_O S ρ)

theorem block_simple_std (ρ : Root) (N : Subgroup (Vs K E ≃ₗ[K] Vs K E)) (hN : N ≤ Block S.D ρ)
    (hnorm : (N.subgroupOf (Block S.D ρ)).Normal) : N = ⊥ ∨ N = Block S.D ρ := by
  have := Blk.isSimpleGroup_block S ρ
  exact Blk.eq_bot_or_eq_of_isSimpleGroup hN hnorm

theorem block_perfect_std (ρ : Root) : ⁅Block S.D ρ, Block S.D ρ⁆ = Block S.D ρ :=
  Blk.commutator_block S ρ

set_option linter.unusedSectionVars false in
theorem block_cent_std (ρ : Root) (a : Fin 3 → ZMod p) (ha : ρ.vecp p ⬝ᵥ a = 0)
    (g : Vs K E ≃ₗ[K] Vs K E) (hg : g ∈ Block S.D ρ) : g * tor S a = tor S a * g := by
  cases ρ
  · rw [Blk.vecp_s1, single_one_dotProduct] at ha
    exact Blk.tor_commute_of_mem_supp S 0 ha (Subgroup.mem_inf.mp hg).1
  · rw [Blk.vecp_s2, single_one_dotProduct] at ha
    exact Blk.tor_commute_of_mem_supp S 1 ha (Subgroup.mem_inf.mp hg).1
  · rw [Blk.vecp_s3, single_one_dotProduct] at ha
    exact Blk.tor_commute_of_mem_supp S 2 ha (Subgroup.mem_inf.mp hg).1
  · rw [Blk.vecp_m12, sub_dotProduct, single_one_dotProduct, single_one_dotProduct,
      sub_eq_zero] at ha
    obtain ⟨M, hM, rfl⟩ := hg
    exact Blk.matToG_commute_tor S hM ha
  · rw [Blk.vecp_m13, sub_dotProduct, single_one_dotProduct, single_one_dotProduct,
      sub_eq_zero] at ha
    obtain ⟨M, hM, rfl⟩ := hg
    exact Blk.matToG_commute_tor S hM ha
  · rw [Blk.vecp_m23, sub_dotProduct, single_one_dotProduct, single_one_dotProduct,
      sub_eq_zero] at ha
    obtain ⟨M, hM, rfl⟩ := hg
    exact Blk.matToG_commute_tor S hM ha
  · rw [Blk.vecp_p12, add_dotProduct, single_one_dotProduct, single_one_dotProduct] at ha
    exact Blk.plong_commute S (by decide) ha hg
  · rw [Blk.vecp_p13, add_dotProduct, single_one_dotProduct, single_one_dotProduct] at ha
    exact Blk.plong_commute S (by decide) ha hg
  · rw [Blk.vecp_p23, add_dotProduct, single_one_dotProduct, single_one_dotProduct] at ha
    exact Blk.plong_commute S (by decide) ha hg

theorem block_T_std (ρ : Root) (a : Fin 3 → ZMod p) :
    tor S a ∈ Block S.D ρ ↔ ∃ l : ZMod p, a = l • ρ.vecp p := by
  cases ρ
  · rw [Blk.vecp_s1, Blk.exists_smul_single_iff]
    exact Blk.tor_mem_supp_inf_Om_iff S 0 a
  · rw [Blk.vecp_s2, Blk.exists_smul_single_iff]
    exact Blk.tor_mem_supp_inf_Om_iff S 1 a
  · rw [Blk.vecp_s3, Blk.exists_smul_single_iff]
    exact Blk.tor_mem_supp_inf_Om_iff S 2 a
  · rw [Blk.vecp_m12, Blk.exists_smul_sub_iff (k := 2) (by decide) (by decide) (by decide)]
    exact Blk.tor_mem_longBlock_iff S (by decide) (by decide) (by decide) a
  · rw [Blk.vecp_m13, Blk.exists_smul_sub_iff (k := 1) (by decide) (by decide) (by decide)]
    exact Blk.tor_mem_longBlock_iff S (by decide) (by decide) (by decide) a
  · rw [Blk.vecp_m23, Blk.exists_smul_sub_iff (k := 0) (by decide) (by decide) (by decide)]
    exact Blk.tor_mem_longBlock_iff S (by decide) (by decide) (by decide) a
  · rw [Blk.vecp_p12, Blk.exists_smul_add_iff (k := 2) (by decide) (by decide) (by decide)]
    exact Blk.tor_mem_plong_iff S (by decide) (by decide) (by decide) a
  · rw [Blk.vecp_p13, Blk.exists_smul_add_iff (k := 1) (by decide) (by decide) (by decide)]
    exact Blk.tor_mem_plong_iff S (by decide) (by decide) (by decide) a
  · rw [Blk.vecp_p23, Blk.exists_smul_add_iff (k := 0) (by decide) (by decide) (by decide)]
    exact Blk.tor_mem_plong_iff S (by decide) (by decide) (by decide) a

end Std

end CFSG.RankThree.PartOne.KFR4
