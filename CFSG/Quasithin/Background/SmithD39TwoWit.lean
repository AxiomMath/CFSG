module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Cent

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Matrix

section Transport

variable {H G : Type*} [Group H] [Group G]

theorem not_mem_zpowers_of_pow_three {u w : G} (hu3 : u ^ 3 = 1) (h1 : w ≠ 1) (h2 : w ≠ u)
    (h3 : w ≠ u⁻¹) : w ∉ Subgroup.zpowers u := by
  intro hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, show u ^ (3 : ℤ) = 1 by exact_mod_cast hu3, one_zpow, mul_one]
  rw [hk] at h1 h2 h3
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr <;> rw [hr] at h1 h2 h3
  · exact h1 (zpow_zero u)
  · exact h2 (zpow_one u)
  · apply h3
    have h4 : u ^ (2 : ℤ) * u = 1 := by
      rw [← zpow_add_one]
      exact_mod_cast hu3
    exact eq_inv_of_mul_eq_one_left h4

theorem not_mem_zpowers_of_inv {i y z : G} (hiy : i * y * i⁻¹ = y⁻¹) (hiz : i * z = z * i)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : z ∉ Subgroup.zpowers y := by
  intro hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h1 : i * y ^ k * i⁻¹ = (y ^ k)⁻¹ := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hiy, inv_zpow]
  rw [hiz, mul_inv_cancel_right] at h1
  apply hz1
  have h5 : y ^ k * y ^ k = 1 := by
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  have h6 : (y ^ k) ^ 3 = y ^ k := by rw [pow_succ, pow_two, h5, one_mul]
  rw [← h6]
  exact hz3

theorem inv_pair_map (f : H →* G) (hf : Function.Injective f) {u s : H}
    (h : u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) :
    f u ^ 3 = 1 ∧ f u ≠ 1 ∧ f s ^ 2 = 1 ∧ f s * f u * (f s)⁻¹ = (f u)⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [← map_pow, h1, map_one], fun h => h2 (hf (h.trans (map_one f).symm)),
    by rw [← map_pow, h3, map_one], ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, h4, map_inv]

theorem e9_pair_map (f : H →* G) (hf : Function.Injective f) {u w : H}
    (h : u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ∉ Subgroup.zpowers u) :
    f u ^ 3 = 1 ∧ f w ^ 3 = 1 ∧ f u * f w = f w * f u ∧ f u ≠ 1 ∧
      f w ∉ Subgroup.zpowers (f u) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [← map_pow, h1, map_one], by rw [← map_pow, h2, map_one],
    by rw [← map_mul, h3, map_mul], fun h => h4 (hf (h.trans (map_one f).symm)), ?_⟩
  intro hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← map_zpow] at hk
  exact h5 (Subgroup.mem_zpowers_iff.mpr ⟨k, hf hk⟩)

theorem four_map (f : H →* G) (hf : Function.Injective f) {g h : H}
    (hgh : g ^ 4 = 1 ∧ g ^ 2 * h ≠ h * g ^ 2) : f g ^ 4 = 1 ∧ f g ^ 2 * f h ≠ f h * f g ^ 2 := by
  obtain ⟨h1, h2⟩ := hgh
  refine ⟨by rw [← map_pow, h1, map_one], fun he => h2 (hf ?_)⟩
  rw [map_mul, map_mul, map_pow, he]

theorem exists_inv_of_hom {L : Subgroup G} (π : H →* ↥L) (hπ : Function.Injective π)
    (h : ∃ u s : H, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) :
    ∃ u ∈ L, ∃ s ∈ L, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹ := by
  obtain ⟨u, s, hus⟩ := h
  exact ⟨_, (π u).2, _, (π s).2,
    inv_pair_map (L.subtype.comp π) (L.subtype_injective.comp hπ) hus⟩

theorem exists_e9_of_hom {L : Subgroup G} (π : H →* ↥L) (hπ : Function.Injective π)
    (h : ∃ u w : H, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ∉ Subgroup.zpowers u) :
    ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
      w ∉ Subgroup.zpowers u := by
  obtain ⟨u, w, huw⟩ := h
  exact ⟨_, (π u).2, _, (π w).2,
    e9_pair_map (L.subtype.comp π) (L.subtype_injective.comp hπ) huw⟩

theorem exists_four_of_hom {L : Subgroup G} (π : H →* ↥L) (hπ : Function.Injective π)
    (h : ∃ g h : H, g ^ 4 = 1 ∧ g ^ 2 * h ≠ h * g ^ 2) :
    ∃ g ∈ L, g ^ 4 = 1 ∧ ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2 := by
  obtain ⟨g, h, hgh⟩ := h
  obtain ⟨h1, h2⟩ := four_map (L.subtype.comp π) (L.subtype_injective.comp hπ) hgh
  exact ⟨_, (π g).2, h1, _, (π h).2, h2⟩

end Transport

section Fields

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have h1 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h1
  push_cast at h1
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (pow_eq_zero_iff'.mp h1).1

theorem det_eq_one_of_zmod_two {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι (ZMod 2)) :
    (g : Matrix ι ι (ZMod 2)).det = 1 := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (g : Matrix ι ι (ZMod 2)).det with h | h
  · exfalso
    have h1 : IsUnit (g : Matrix ι ι (ZMod 2)).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    rw [h] at h1
    exact not_isUnit_zero h1
  · exact h

theorem glMap_injective {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K] [CharP K 2] :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) (ZMod.castHom (dvd_refl 2) K)) := by
  intro a b hab
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have h1 := congrArg (fun x : GL ι K => (x : Matrix ι ι K) i j) hab
  exact (RingHom.injective (ZMod.castHom (dvd_refl 2) K)) h1

theorem exists_hom_statedSL (d : ℕ) (K : Type) [Field K] [CharP K 2] :
    ∃ ι : GL (Fin d) (ZMod 2) →* ↥(StatedSL d K), Function.Injective ι := by
  set f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hmem : ∀ g : GL (Fin d) (ZMod 2), Matrix.GeneralLinearGroup.map f g ∈ StatedSL d K := by
    intro g
    apply Subgroup.subset_closure
    show (f.mapMatrix (g : Matrix (Fin d) (Fin d) (ZMod 2))).det = 1
    rw [← RingHom.map_det, det_eq_one_of_zmod_two, map_one]
  refine ⟨(Matrix.GeneralLinearGroup.map f).codRestrict (StatedSL d K) hmem, fun a b hab => ?_⟩
  exact glMap_injective K (congrArg Subtype.val hab)

theorem exists_hom_statedSp (K : Type) [Field K] [CharP K 2] :
    ∃ ι : ↥(StatedSp 2 (ZMod 2)) →* ↥(StatedSp 2 K), Function.Injective ι := by
  set f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map f = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_map]
    simp only [Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · exact (map_neg f 1).trans (by rw [map_one])
    · exact (map_neg f 0).trans (by rw [map_zero, neg_zero])
  have hle : StatedSp 2 (ZMod 2) ≤
      (StatedSp 2 K).comap (Matrix.GeneralLinearGroup.map f) := by
    refine (Subgroup.closure_le _).mpr fun A hA => ?_
    apply Subgroup.subset_closure
    have hA' : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))ᵀ *
        Matrix.fromBlocks 0 1 (-1) 0 * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      Matrix.fromBlocks 0 1 (-1) 0 := hA
    show ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map f)ᵀ *
        Matrix.fromBlocks 0 1 (-1) 0 * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map f =
      Matrix.fromBlocks 0 1 (-1) 0
    rw [← hJ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hA']
  refine ⟨((Matrix.GeneralLinearGroup.map f).comp (StatedSp 2 (ZMod 2)).subtype).codRestrict
    (StatedSp 2 K) (fun g => hle g.2), fun a b hab => ?_⟩
  exact Subtype.ext (glMap_injective K (congrArg Subtype.val hab))

end Fields

section F2

theorem exists_inv_GL3 : ∃ u s : GL (Fin 3) (ZMod 2),
    u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹ := by
  refine ⟨⟨!![0,1,0; 1,1,0; 0,0,1], !![1,1,0; 1,0,0; 0,0,1], by decide, by decide⟩,
    ⟨!![0,1,0; 1,0,0; 0,0,1], !![0,1,0; 1,0,0; 0,0,1], by decide, by decide⟩, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (apply Units.ext; decide)
    | (intro h; have h' := congrArg Units.val h; revert h'; decide)

theorem exists_four_GL3 : ∃ g h : GL (Fin 3) (ZMod 2), g ^ 4 = 1 ∧ g ^ 2 * h ≠ h * g ^ 2 := by
  refine ⟨⟨!![1,1,0; 0,1,1; 0,0,1], !![1,1,1; 0,1,1; 0,0,1], by decide, by decide⟩,
    ⟨!![0,1,0; 1,0,0; 0,0,1], !![0,1,0; 1,0,0; 0,0,1], by decide, by decide⟩, ?_, ?_⟩
  · apply Units.ext
    decide
  · intro h
    have h' := congrArg Units.val h
    revert h'
    decide

theorem exists_e9_GL45 {n : ℕ} (hn : n = 4 ∨ n = 5) : ∃ u w : GL (Fin n) (ZMod 2),
    u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ∉ Subgroup.zpowers u := by
  obtain ⟨y, z, i, hyz, hy3, hz3, hy1, hz1, -, -, hiz, hiy⟩ := SmithD391.exists_e9_GL hn
  exact ⟨y, z, hy3, hz3, hyz, hy1, not_mem_zpowers_of_inv hiy hiz hz3 hz1⟩

theorem exists_inv_GL45 {n : ℕ} (hn : n = 4 ∨ n = 5) : ∃ u s : GL (Fin n) (ZMod 2),
    u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹ := by
  obtain ⟨y, -, i, -, hy3, -, hy1, -, hi2, -, -, hiy⟩ := SmithD391.exists_e9_GL hn
  exact ⟨y, i, hy3, hy1, hi2, hiy⟩

theorem mem_statedSp_two {A : GL (Fin 2 ⊕ Fin 2) (ZMod 2)}
    (h : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) = Matrix.fromBlocks 0 1 (-1) 0) :
    A ∈ StatedSp 2 (ZMod 2) :=
  Subgroup.subset_closure h

theorem exists_inv_e9_Sp4 : ∃ u w s : ↥(StatedSp 2 (ZMod 2)),
    (u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) ∧
      (u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ∉ Subgroup.zpowers u) := by
  refine ⟨⟨⟨Matrix.fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![1,0;0,1],
      Matrix.fromBlocks !![1,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1], by decide, by decide⟩,
      mem_statedSp_two (by decide)⟩,
    ⟨⟨Matrix.fromBlocks !![1,0;0,0] !![0,0;0,1] !![0,0;0,1] !![1,0;0,1],
      Matrix.fromBlocks !![1,0;0,1] !![0,0;0,1] !![0,0;0,1] !![1,0;0,0], by decide, by decide⟩,
      mem_statedSp_two (by decide)⟩,
    ⟨⟨Matrix.fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1],
      Matrix.fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1], by decide, by decide⟩,
      mem_statedSp_two (by decide)⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  rotate_right
  · refine not_mem_zpowers_of_pow_three ?_ ?_ ?_ ?_
    all_goals first
      | (apply Subtype.ext; apply Units.ext; decide)
      | (intro h; have h' := congrArg (fun x : ↥(StatedSp 2 (ZMod 2)) =>
          ((x : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))) h;
          revert h'; decide)
  all_goals first
    | (apply Subtype.ext; apply Units.ext; decide)
    | (intro h; have h' := congrArg (fun x : ↥(StatedSp 2 (ZMod 2)) =>
        ((x : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))) h;
        revert h'; decide)

end F2

section Alt

theorem exists_inv_e9_alt6 : ∃ u w s : ↥(alternatingGroup (Fin 6)),
    (u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) ∧
      (u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ∉ Subgroup.zpowers u) := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  rotate_right
  · refine not_mem_zpowers_of_pow_three ?_ ?_ ?_ ?_
    all_goals first
      | (apply Subtype.ext; decide)
      | (intro h; have h' := congrArg Subtype.val h; revert h'; decide)
  all_goals first
    | (apply Subtype.ext; decide)
    | (intro h; have h' := congrArg Subtype.val h; revert h'; decide)

theorem exists_inv_e9_alt7 : ∃ u w s : ↥(alternatingGroup (Fin 7)),
    (u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) ∧
      (u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧ w ∉ Subgroup.zpowers u) := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  rotate_right
  · refine not_mem_zpowers_of_pow_three ?_ ?_ ?_ ?_
    all_goals first
      | (apply Subtype.ext; decide)
      | (intro h; have h' := congrArg Subtype.val h; revert h'; decide)
  all_goals first
    | (apply Subtype.ext; decide)
    | (intro h; have h' := congrArg Subtype.val h; revert h'; decide)

end Alt

section Diag

variable {K : Type} [Field K]

@[expose] def diagHom (K : Type) [Field K] : (Fin 3 → Kˣ) →* GL (Fin 3) K where
  toFun a := ⟨Matrix.diagonal fun i => (a i : K), Matrix.diagonal fun i => ((a i)⁻¹ : K),
    by simp, by simp⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp

theorem diagHom_injective : Function.Injective (diagHom K) := by
  intro a b hab
  funext i
  apply Units.ext
  have h1 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i i) hab
  simpa [diagHom] using h1

theorem exists_e9_SL3 {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ u w : ↥(StatedSL 3 K), u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
      w ∉ Subgroup.zpowers u := by
  set S : Subgroup (Fin 3 → Kˣ) := (StatedSL 3 K).comap (diagHom K) with hS
  have hdet : ∀ c : Fin 3 → Kˣ, c 0 * c 1 * c 2 = 1 → c ∈ S := by
    intro c hc
    apply Subgroup.subset_closure
    show (Matrix.diagonal fun i => (c i : K)).det = 1
    rw [Matrix.det_diagonal, Fin.prod_univ_three, ← Units.val_mul, ← Units.val_mul, hc,
      Units.val_one]
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h]; group
  have hω6 : ω ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  set a : Fin 3 → Kˣ := ![ω, ω ^ 2, 1] with ha
  set b : Fin 3 → Kˣ := ![1, ω, ω ^ 2] with hb
  have haS : a ∈ S := hdet a (by simp [ha, ← pow_succ', hω3])
  have hbS : b ∈ S := hdet b (by simp [hb, ← pow_succ', hω3])
  let φ : ↥S →* ↥(StatedSL 3 K) := ((diagHom K).comp S.subtype).codRestrict _ fun c => c.2
  have hφ : Function.Injective φ := fun c d hcd =>
    Subtype.ext (diagHom_injective (congrArg Subtype.val hcd))
  refine ⟨φ ⟨a, haS⟩, φ ⟨b, hbS⟩, e9_pair_map φ hφ ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · apply Subtype.ext
    funext i
    fin_cases i <;> simp [ha, ← pow_mul, hω3, hω6]
  · apply Subtype.ext
    funext i
    fin_cases i <;> simp [hb, ← pow_mul, hω3, hω6]
  · exact Subtype.ext (mul_comm a b)
  · intro h
    exact hω1 (congrFun (congrArg Subtype.val h) 0)
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 := congrFun (congrArg Subtype.val hk) 2
    simp [ha, hb] at h1
    exact hω2 h1.symm

end Diag

section Models

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

theorem exists_equiv_of_binaryNaturalSL {d a : ℕ} (h : BinaryNaturalSL L U Z d a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      ∃ e : ↥(StatedSL d K) ≃* ↥L,
        (FFModel.nat (StatedSL d K)).RealizesVia L U Z e.toMonoidHom := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hinj : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  exact ⟨K, inferInstance, inferInstance, hK, MulEquiv.ofBijective π ⟨hinj, hπ.1⟩, hπ⟩

theorem exists_equiv_of_binaryNaturalSp4 {a : ℕ} (h : BinaryNaturalSp4 L U Z a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      ∃ e : ↥(StatedSp 2 K) ≃* ↥L,
        (FFModel.nat (StatedSp 2 K)).RealizesVia L U Z e.toMonoidHom := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have hinj : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  exact ⟨K, inferInstance, inferInstance, hK, MulEquiv.ofBijective π ⟨hinj, hπ.1⟩, hπ⟩

theorem exists_hom_of_alternatingNatural6 (h : AlternatingNatural L U Z 6) :
    ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥L, Function.Injective π := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ⟩

theorem exists_hom_of_a7Four (h : A7Four L U Z) :
    ∃ π : ↥(alternatingGroup (Fin 7)) →* ↥L, Function.Injective π := by
  obtain ⟨α, π, hπ⟩ := h
  exact ⟨π, FFC.injective_of_faithful_sec (FFC.a7Four_faithful α) hπ⟩

theorem exists_inv_of_binaryNaturalSL {d a : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 5)
    (h : BinaryNaturalSL L U Z d a) :
    ∃ u ∈ L, ∃ s ∈ L, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹ := by
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL h
  have := charP_two_of_card hK
  obtain ⟨ι, hι⟩ := exists_hom_statedSL d K
  refine exists_inv_of_hom (e.toMonoidHom.comp ι) (e.injective.comp hι) ?_
  rcases hd with rfl | hd
  · exact exists_inv_GL3
  · exact exists_inv_GL45 hd

theorem exists_e9_of_binaryNaturalSL45 {d a : ℕ} (hd : d = 4 ∨ d = 5)
    (h : BinaryNaturalSL L U Z d a) :
    ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
      w ∉ Subgroup.zpowers u := by
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL h
  have := charP_two_of_card hK
  obtain ⟨ι, hι⟩ := exists_hom_statedSL d K
  exact exists_e9_of_hom (e.toMonoidHom.comp ι) (e.injective.comp hι) (exists_e9_GL45 hd)

theorem exists_e9_of_binaryNaturalSL3 {a : ℕ} (ha : Even a) (h : BinaryNaturalSL L U Z 3 a) :
    ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
      w ∉ Subgroup.zpowers u := by
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Kˣ := by
    obtain ⟨m, rfl⟩ := ha
    rw [Nat.card_units, hK, ← two_mul, pow_mul]
    have h1 := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 m
    rwa [one_pow] at h1
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    exact absurd hω (by norm_num)
  exact exists_e9_of_hom e.toMonoidHom e.injective (exists_e9_SL3 hω3 hω1)

theorem exists_four_of_binaryNaturalSL3 {a : ℕ} (h : BinaryNaturalSL L U Z 3 a) :
    ∃ g ∈ L, g ^ 4 = 1 ∧ ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2 := by
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL h
  have := charP_two_of_card hK
  obtain ⟨ι, hι⟩ := exists_hom_statedSL 3 K
  exact exists_four_of_hom (e.toMonoidHom.comp ι) (e.injective.comp hι) exists_four_GL3

theorem exists_inv_e9_of_binaryNaturalSp4 {a : ℕ} (h : BinaryNaturalSp4 L U Z a) :
    (∃ u ∈ L, ∃ s ∈ L, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) ∧
      ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
        w ∉ Subgroup.zpowers u := by
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSp4 h
  have := charP_two_of_card hK
  obtain ⟨ι, hι⟩ := exists_hom_statedSp K
  obtain ⟨u, w, s, hinv, he9⟩ := exists_inv_e9_Sp4
  exact ⟨exists_inv_of_hom (e.toMonoidHom.comp ι) (e.injective.comp hι) ⟨u, s, hinv⟩,
    exists_e9_of_hom (e.toMonoidHom.comp ι) (e.injective.comp hι) ⟨u, w, he9⟩⟩

theorem exists_inv_e9_of_alternatingNatural6 (h : AlternatingNatural L U Z 6) :
    (∃ u ∈ L, ∃ s ∈ L, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) ∧
      ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
        w ∉ Subgroup.zpowers u := by
  obtain ⟨π, hπ⟩ := exists_hom_of_alternatingNatural6 h
  obtain ⟨u, w, s, hinv, he9⟩ := exists_inv_e9_alt6
  exact ⟨exists_inv_of_hom π hπ ⟨u, s, hinv⟩, exists_e9_of_hom π hπ ⟨u, w, he9⟩⟩

theorem exists_inv_e9_of_a7Four (h : A7Four L U Z) :
    (∃ u ∈ L, ∃ s ∈ L, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹) ∧
      ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
        w ∉ Subgroup.zpowers u := by
  obtain ⟨π, hπ⟩ := exists_hom_of_a7Four h
  obtain ⟨u, w, s, hinv, he9⟩ := exists_inv_e9_alt7
  exact ⟨exists_inv_of_hom π hπ ⟨u, s, hinv⟩, exists_e9_of_hom π hπ ⟨u, w, he9⟩⟩

end Models

section D35

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V : Subgroup W}

theorem exists_inv_of_d35Five (h5 : D35Five L V) :
    ∃ u ∈ L, ∃ s ∈ L, u ^ 3 = 1 ∧ u ≠ 1 ∧ s ^ 2 = 1 ∧ s * u * s⁻¹ = u⁻¹ := by
  rcases h5 with ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h
  · exact exists_inv_of_binaryNaturalSL (Or.inl rfl) h
  · exact (exists_inv_e9_of_binaryNaturalSp4 h).1
  · exact (exists_inv_e9_of_alternatingNatural6 h).1
  · exact exists_inv_of_binaryNaturalSL (Or.inr (Or.inl rfl)) h
  · exact exists_inv_of_binaryNaturalSL (Or.inr (Or.inr rfl)) h
  · exact (exists_inv_e9_of_a7Four h).1

theorem alpha_or_e9_of_d35Five (h5 : D35Five L V) :
    (∃ n, Odd n ∧ BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨
      ∃ u ∈ L, ∃ w ∈ L, u ^ 3 = 1 ∧ w ^ 3 = 1 ∧ u * w = w * u ∧ u ≠ 1 ∧
        w ∉ Subgroup.zpowers u := by
  rcases h5 with ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h
  · rcases Nat.even_or_odd n with hn | hn
    · exact Or.inr (exists_e9_of_binaryNaturalSL3 hn h)
    · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (exists_inv_e9_of_binaryNaturalSp4 h).2
  · exact Or.inr (exists_inv_e9_of_alternatingNatural6 h).2
  · exact Or.inr (exists_e9_of_binaryNaturalSL45 (Or.inl rfl) h)
  · exact Or.inr (exists_e9_of_binaryNaturalSL45 (Or.inr rfl) h)
  · exact Or.inr (exists_inv_e9_of_a7Four h).2

end D35

end CFSG.Quasithin.SmithD39Two
