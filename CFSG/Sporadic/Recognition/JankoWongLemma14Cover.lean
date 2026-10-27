module

public import CFSG.Sporadic.Recognition.JankoWongLemma13b

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

@[expose] def permW : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 4 2 * swap 2 5

theorem permW_conj_permA3 : permW * permA3 * permW⁻¹ = permB3 := by
  unfold permW permA3 permB3; decide

theorem permW_conj_permB3 : permW * permB3 * permW⁻¹ = permA3⁻¹ := by
  unfold permW permA3 permB3; decide

theorem permW_inv_conj_permA3 : permW⁻¹ * permA3 * permW = permB3⁻¹ := by
  unfold permW permA3 permB3; decide

theorem permW_inv_conj_permB3 : permW⁻¹ * permB3 * permW = permA3 := by
  unfold permW permA3 permB3; decide

theorem permW_pow_four : permW ^ 4 = 1 := by unfold permW; decide

theorem sign_permW : sign permW = 1 := by unfold permW; decide

theorem permW_sq_cycleType : (permW ^ 2).cycleType = {2, 2} := by
  have : permW ^ 2 = swap 1 2 * swap 4 5 := by unfold permW; decide
  rw [this]
  exact cycleType_type22_of_card (by decide) (by decide)

theorem permD_mul_permW_cycleType : (permD * permW).cycleType = {2, 2} := by
  unfold permW permD
  exact cycleType_type22_of_card (by decide) (by decide)

theorem permD_ne_permW_pow (n : ℕ) : permD ≠ permW ^ n := by
  have h : ∀ k : Fin 4, permD ≠ permW ^ (k : ℕ) := by unfold permD permW; decide
  intro e
  have hn : permW ^ n = permW ^ (n % 4) := by
    conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, permW_pow_four, one_pow, mul_one]
  rw [hn] at e
  exact h ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ e

section SemidihedralRecognition

variable {M : Type*} [Group M]

theorem exists_hom_semidihedral_four (x y : M) (hx : x ^ 8 = 1) (hy : y ^ 2 = 1)
    (hxy : y * x * y⁻¹ = x ^ 3) :
    ∃ φ : SemidihedralGroup 4 →* M, φ (CFSG.Semidihedral.r 4) = x ∧
      φ (CFSG.Semidihedral.s 4) = y := by
  have hxy' : y * x * y⁻¹ = x ^ (2 ^ (4 - 2) - 1) := by
    rw [show (2 ^ (4 - 2) - 1 : ℕ) = 3 by norm_num]
    exact hxy
  have hrels : ∀ r ∈ semidihedralRels 4, FreeGroup.lift ![x, y] r = 1 := by
    rintro r (rfl | rfl | rfl)
    · simpa using hx
    · simpa using hy
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hxy', mul_inv_cancel]
  refine ⟨PresentedGroup.toGroup hrels, ?_, ?_⟩
  · exact (PresentedGroup.toGroup.of hrels).trans (by simp)
  · exact (PresentedGroup.toGroup.of hrels).trans (by simp)

theorem injective_of_orderOf_eight (φ : SemidihedralGroup 4 →* M)
    (hx : orderOf (φ (CFSG.Semidihedral.r 4)) = 8)
    (hy : φ (CFSG.Semidihedral.s 4) ∉ zpowers (φ (CFSG.Semidihedral.r 4))) :
    Function.Injective φ := by
  have : Finite (SemidihedralGroup 4) := CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  have hcard : Nat.card (SemidihedralGroup 4) = 16 := by
    rw [CFSG.Semidihedral.card 4 (by norm_num)]; norm_num
  set x := φ (CFSG.Semidihedral.r 4) with hxdef
  have hxR : zpowers x ≤ φ.range := by
    rw [Subgroup.zpowers_le]; exact ⟨_, rfl⟩
  have hyR : φ (CFSG.Semidihedral.s 4) ∈ φ.range := ⟨_, rfl⟩
  have hlt : zpowers x < φ.range :=
    lt_of_le_of_ne hxR (fun e => hy (by rw [e]; exact hyR))
  have hfin : Finite φ.range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective φ)
  have h8 : Nat.card (zpowers x) = 8 := by rw [Nat.card_zpowers, hx]
  have hdvd : Nat.card (zpowers x) ∣ Nat.card φ.range := Subgroup.card_dvd_of_le hxR
  have hne : Nat.card (zpowers x) ≠ Nat.card φ.range := fun e => by
    have := Subgroup.eq_of_le_of_card_ge hxR (by rw [e])
    exact absurd this (ne_of_lt hlt)
  have hle : Nat.card φ.range ≤ 16 := by
    rw [← hcard]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective φ)
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rw [h8] at hk hne
  have hk2 : k = 2 := by
    rcases k with _ | _ | _ | k
    · omega
    · omega
    · rfl
    · omega
  rw [hk2] at hk
  have hker := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hk, hcard] at hker
  have h1 : Nat.card φ.ker = 1 := by omega
  rw [injective_iff_map_eq_one]
  intro a ha
  have : a ∈ φ.ker := ha
  have hbot : φ.ker = ⊥ := Subgroup.card_eq_one.mp h1
  rw [hbot] at this
  exact this

end SemidihedralRecognition

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem exists_W : ∃ w : S.H, S.ρ w = permW ∧ w ^ 4 = zIn S.z ∧ w ^ 8 = 1 ∧
    c.d * w * c.d⁻¹ = w ^ 3 ∧ w * c.a * w⁻¹ = c.b ∧ w * c.b * w⁻¹ = c.a⁻¹ := by
  obtain ⟨w, hw⟩ := S.cover.exists_lift sign_permW
  have hw4 : w ^ 4 = zIn S.z := by
    have h := S.cover.sq_eq_z_of_type22 (x := w ^ 2)
      (by rw [map_pow, hw]; exact permW_sq_cycleType)
    rwa [← pow_mul] at h
  have hw8 : w ^ 8 = 1 := by
    rw [show 8 = 4 * 2 by norm_num, pow_mul, hw4, S.zIn_sq]
  have hdw : (c.d * w) ^ 2 = zIn S.z := S.cover.sq_eq_z_of_type22
    (by rw [map_mul, c.hd, hw]; exact permD_mul_permW_cycleType)
  have hdinv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact c.hd2)
  have hzc : ∀ y : S.H, y * zIn S.z = zIn S.z * y := fun y => S.cover.mul_z_comm y
  have hdwd : c.d * w * c.d⁻¹ = w ^ 3 := by
    have h1 : c.d * w * c.d * w = zIn S.z := by
      have := hdw; rw [pow_two] at this
      simpa [mul_assoc] using this
    have h2 : c.d * w * c.d = zIn S.z * w⁻¹ := by
      calc c.d * w * c.d = (c.d * w * c.d * w) * w⁻¹ := by group
        _ = zIn S.z * w⁻¹ := by rw [h1]
    have h3 : w ^ 3 = zIn S.z * w⁻¹ := by
      calc w ^ 3 = w ^ 4 * w⁻¹ := by group
        _ = zIn S.z * w⁻¹ := by rw [hw4]
    rw [hdinv, h2, h3]
  have hwa : w * c.a * w⁻¹ = c.b := by
    have h3 : (w * c.a * w⁻¹) ^ 3 = 1 := by
      have : (w * c.a * w⁻¹) ^ 3 = w * c.a ^ 3 * w⁻¹ := by simp [pow_succ, mul_assoc]
      rw [this, c.ha3]; simp
    refine S.cover.eq_of_cube_one h3 c.hb3 ?_
    rw [map_mul, map_mul, map_inv, hw, c.ha, c.hb]
    exact permW_conj_permA3
  have hwb : w * c.b * w⁻¹ = c.a⁻¹ := by
    have h3 : (w * c.b * w⁻¹) ^ 3 = 1 := by
      have : (w * c.b * w⁻¹) ^ 3 = w * c.b ^ 3 * w⁻¹ := by simp [pow_succ, mul_assoc]
      rw [this, c.hb3]; simp
    have h3' : (c.a⁻¹) ^ 3 = 1 := by rw [inv_pow, c.ha3, inv_one]
    refine S.cover.eq_of_cube_one h3 h3' ?_
    rw [map_mul, map_mul, map_inv, map_inv, hw, c.ha, c.hb]
    exact permW_conj_permB3
  exact ⟨w, hw, hw4, hw8, hdwd, hwa, hwb⟩

theorem mem_normalizer_PG_of {g : G} (h1 : ∀ y ∈ c.PG, g * y * g⁻¹ ∈ c.PG)
    (h2 : ∀ y ∈ c.PG, g⁻¹ * y * g ∈ c.PG) : g ∈ normalizer (c.PG : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  simpa [mul_assoc] using this

theorem conj_mem_PG_of_gens {g : G} (ha : g * (c.a : G) * g⁻¹ ∈ c.PG)
    (hb : g * (c.b : G) * g⁻¹ ∈ c.PG) : ∀ y ∈ c.PG, g * y * g⁻¹ ∈ c.PG := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨i, j, -, -, rfl⟩ := c.P_decomp p hp
  have : g * (((c.a ^ i * c.b ^ j : S.H)) : G) * g⁻¹ =
      (g * (c.a : G) * g⁻¹) ^ i * (g * (c.b : G) * g⁻¹) ^ j := by
    rw [conj_pow, conj_pow]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    group
  change g * (((c.a ^ i * c.b ^ j : S.H)) : G) * g⁻¹ ∈ c.PG
  rw [this]
  exact c.PG.mul_mem (c.PG.pow_mem ha i) (c.PG.pow_mem hb j)

theorem mem_normalizer_PG_of_gens {g : G} (ha : g * (c.a : G) * g⁻¹ ∈ c.PG)
    (hb : g * (c.b : G) * g⁻¹ ∈ c.PG) (ha' : g⁻¹ * (c.a : G) * g ∈ c.PG)
    (hb' : g⁻¹ * (c.b : G) * g ∈ c.PG) : g ∈ normalizer (c.PG : Set G) := by
  refine c.mem_normalizer_PG_of (c.conj_mem_PG_of_gens ha hb) ?_
  have := c.conj_mem_PG_of_gens (g := g⁻¹) (by simpa using ha') (by simpa using hb')
  intro y hy
  simpa using this y hy

theorem d_mem_normalizer_PG : (c.d : G) ∈ normalizer (c.PG : Set G) :=
  c.mem_normalizer_PG_of c.PG_normalizes_d.1 c.PG_normalizes_d.2

theorem t_mem_normalizer_PG : (c.t : G) ∈ normalizer (c.PG : Set G) :=
  c.mem_normalizer_PG_of c.PG_normalizes_t.1 c.PG_normalizes_t.2

theorem exists_semidihedral_embedding :
    ∃ φ : SemidihedralGroup 4 →* G, Function.Injective φ ∧ (∀ x, φ x ∈ S.H) ∧
      (∀ x, φ x ∈ normalizer (c.PG : Set G)) ∧
      φ (CFSG.Semidihedral.r 4 ^ 4) = S.z ∧ φ (CFSG.Semidihedral.s 4) = (c.d : G) ∧
      φ (CFSG.Semidihedral.r 4) * (c.a : G) * (φ (CFSG.Semidihedral.r 4))⁻¹ = (c.b : G) ∧
      φ (CFSG.Semidihedral.r 4) * (c.b : G) * (φ (CFSG.Semidihedral.r 4))⁻¹ = (c.a : G)⁻¹ := by
  obtain ⟨w, hw, hw4, hw8, hdw, hwa, hwb⟩ := c.exists_W
  have hwo : orderOf w = 8 := by
    have h1 : ¬ w ^ 2 ^ 2 = 1 := fun e => by
      have : w ^ 4 = 1 := by simpa using e
      rw [hw4] at this
      exact S.cover.ne_one this
    have h2 : w ^ 2 ^ (2 + 1) = 1 := by simpa using hw8
    have := orderOf_eq_prime_pow h1 h2
    simpa using this
  obtain ⟨φH, hφr, hφs⟩ := exists_hom_semidihedral_four w c.d hw8 c.hd2 hdw
  have hinjH : Function.Injective φH := by
    refine injective_of_orderOf_eight φH (by rw [hφr]; exact hwo) ?_
    rw [hφr, hφs]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 := congrArg S.ρ hk
    rw [c.hd, map_zpow, hw] at h1
    have ho : orderOf permW = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := permW)
        (by unfold permW; decide) (by simpa using permW_pow_four)
      simpa using h
    have h2 := zpow_mod_orderOf permW k
    rw [ho] at h2
    have hnn : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnn
    rw [hm, zpow_natCast, h1] at h2
    exact permD_ne_permW_pow m h2.symm
  have hcoe : ∀ {u v : S.H}, u = v → (u : G) = (v : G) := fun h => congrArg Subtype.val h
  have h1 : (w : G) * (c.a : G) * (w : G)⁻¹ = (c.b : G) := by simpa using hcoe hwa
  have h2 : (w : G) * (c.b : G) * (w : G)⁻¹ = (c.a : G)⁻¹ := by simpa using hcoe hwb
  have hwG : (w : G) ∈ normalizer (c.PG : Set G) := by
    have h3 : (w : G)⁻¹ * (c.a : G) * (w : G) = (c.b : G)⁻¹ := by
      have : c.b = w⁻¹ * c.a⁻¹ * w := by
        calc c.b = w⁻¹ * (w * c.b * w⁻¹) * w := by group
          _ = w⁻¹ * c.a⁻¹ * w := by rw [hwb]
      have h := hcoe this
      calc (w : G)⁻¹ * (c.a : G) * (w : G) = ((w : G)⁻¹ * (c.a : G)⁻¹ * (w : G))⁻¹ := by group
        _ = (c.b : G)⁻¹ := by simpa using congrArg (fun y => y⁻¹) h.symm
    have h4 : (w : G)⁻¹ * (c.b : G) * (w : G) = (c.a : G) := by
      have : c.a = w⁻¹ * c.b * w := by
        calc c.a = w⁻¹ * (w * c.a * w⁻¹) * w := by group
          _ = w⁻¹ * c.b * w := by rw [hwa]
      simpa using (hcoe this).symm
    have haPG : (c.a : G) ∈ c.PG := c.a_mem_PG
    have hbPG : (c.b : G) ∈ c.PG := ⟨c.b, c.hbP, rfl⟩
    refine c.mem_normalizer_PG_of_gens ?_ ?_ ?_ ?_
    · rw [h1]; exact hbPG
    · rw [h2]; exact c.PG.inv_mem haPG
    · rw [h3]; exact c.PG.inv_mem hbPG
    · rw [h4]; exact haPG
  refine ⟨S.H.subtype.comp φH, S.H.subtype_injective.comp hinjH, fun x => (φH x).2, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x
    have hle : (normalizer (c.PG : Set G)).comap (S.H.subtype.comp φH) = ⊤ := by
      rw [eq_top_iff, ← PresentedGroup.closure_range_of (semidihedralRels 4), Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · show (S.H.subtype (φH (CFSG.Semidihedral.r 4))) ∈ normalizer (c.PG : Set G)
        rw [hφr]; exact hwG
      · show (S.H.subtype (φH (CFSG.Semidihedral.s 4))) ∈ normalizer (c.PG : Set G)
        rw [hφs]; exact c.d_mem_normalizer_PG
    have : x ∈ (normalizer (c.PG : Set G)).comap (S.H.subtype.comp φH) := by rw [hle]; trivial
    exact this
  · show ((φH (CFSG.Semidihedral.r 4 ^ 4) : S.H) : G) = S.z
    rw [map_pow, hφr, hw4]; rfl
  · show ((φH (CFSG.Semidihedral.s 4) : S.H) : G) = (c.d : G)
    rw [hφs]
  · show ((φH (CFSG.Semidihedral.r 4) : S.H) : G) * (c.a : G) *
      ((φH (CFSG.Semidihedral.r 4) : S.H) : G)⁻¹ = (c.b : G)
    rw [hφr]; exact h1
  · show ((φH (CFSG.Semidihedral.r 4) : S.H) : G) * (c.b : G) *
      ((φH (CFSG.Semidihedral.r 4) : S.H) : G)⁻¹ = (c.a : G)⁻¹
    rw [hφr]; exact h2

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
