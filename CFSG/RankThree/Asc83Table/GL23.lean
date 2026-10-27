module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup

abbrev GL23 : Type := GL (Fin 2) (ZMod 3)

theorem card_GL23 : Nat.card GL23 = 48 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

@[expose] def gl23 (M N : Matrix (Fin 2) (Fin 2) (ZMod 3)) (h₁ : M * N = 1) (h₂ : N * M = 1) :
    GL23 :=
  ⟨M, N, h₁, h₂⟩

@[expose] def qI : GL23 := gl23 !![0, 2; 1, 0] !![0, 1; 2, 0] (by decide) (by decide)

@[expose] def qJ : GL23 := gl23 !![1, 1; 1, 2] !![2, 2; 2, 1] (by decide) (by decide)

@[expose] def quatFun : QuaternionGroup 2 → GL23
  | .a i => qI ^ i.val
  | .xa i => qJ * qI ^ i.val

@[expose] def quatHom : QuaternionGroup 2 →* GL23 where
  toFun := quatFun
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem quatHom_injective : Function.Injective quatHom := by
  intro x y h
  revert x y
  decide +kernel

theorem quatHom_a_one : quatHom (.a 1) = qI := by decide +kernel

theorem quatHom_xa_zero : quatHom (.xa 0) = qJ := by decide +kernel

theorem closure_quaternion :
    Subgroup.closure ({.a 1, .xa 0} : Set (QuaternionGroup 2)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have ha : (QuaternionGroup.a 1 : QuaternionGroup 2) ∈ Subgroup.closure {.a 1, .xa 0} :=
    subset_closure (by simp)
  have hx : (QuaternionGroup.xa 0 : QuaternionGroup 2) ∈ Subgroup.closure {.a 1, .xa 0} :=
    subset_closure (by simp)
  have hpow : ∀ i : ZMod (2 * 2), (QuaternionGroup.a i : QuaternionGroup 2) =
      QuaternionGroup.a 1 ^ i.val := by decide
  have hxa : ∀ i : ZMod (2 * 2), (QuaternionGroup.xa i : QuaternionGroup 2) =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ i.val := by decide
  cases g with
  | a i => rw [hpow i]; exact pow_mem ha _
  | xa i => rw [hxa i]; exact mul_mem hx (pow_mem ha _)

theorem range_quatHom : quatHom.range = Subgroup.closure {qI, qJ} := by
  rw [MonoidHom.range_eq_map, ← closure_quaternion, MonoidHom.map_closure, Set.image_pair,
    quatHom_a_one, quatHom_xa_zero]

@[expose] def borel : Subgroup GL23 where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0}
  mul_mem' {a b} ha hb := by
    change ((a * b : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0
    change (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0 at ha
    change (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0 at hb
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    ring
  one_mem' := rfl
  inv_mem' {a} ha := by
    change (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0 at ha
    change ((a⁻¹ : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0
    revert a
    decide +kernel

instance : DecidablePred (· ∈ borel) := fun g =>
  inferInstanceAs (Decidable ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0))

theorem mem_borel {g : GL23} : g ∈ borel ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0 :=
  Iff.rfl

@[expose] def bR : GL23 := gl23 !![2, 2; 0, 2] !![2, 1; 0, 2] (by decide) (by decide)

@[expose] def bS : GL23 := gl23 !![2, 0; 0, 1] !![2, 0; 0, 1] (by decide) (by decide)

@[expose] def w0 : GL23 := gl23 !![0, 1; 1, 0] !![0, 1; 1, 0] (by decide) (by decide)

@[expose] def unip (k : ZMod 3) : GL23 := gl23 !![1, k; 0, 1] !![1, -k; 0, 1]
  (by revert k; decide) (by revert k; decide)

@[expose] def dihedralFun : DihedralGroup 6 → GL23
  | .r i => bR ^ i.val
  | .sr i => bS * bR ^ i.val

@[expose] def dihedralHom : DihedralGroup 6 →* GL23 where
  toFun := dihedralFun
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem dihedralHom_injective : Function.Injective dihedralHom := by
  intro x y h
  revert x y
  decide +kernel

theorem dihedralHom_r_one : dihedralHom (.r 1) = bR := by decide +kernel

theorem dihedralHom_sr_zero : dihedralHom (.sr 0) = bS := by decide +kernel

theorem range_dihedralHom : dihedralHom.range = borel := by
  ext g
  rw [MonoidHom.mem_range, mem_borel]
  revert g
  decide +kernel

theorem closure_dihedral : Subgroup.closure ({.r 1, .sr 0} : Set (DihedralGroup 6)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hr : (DihedralGroup.r 1 : DihedralGroup 6) ∈ Subgroup.closure {.r 1, .sr 0} :=
    subset_closure (by simp)
  have hs : (DihedralGroup.sr 0 : DihedralGroup 6) ∈ Subgroup.closure {.r 1, .sr 0} :=
    subset_closure (by simp)
  have hpow : ∀ i : ZMod 6, (DihedralGroup.r i : DihedralGroup 6) =
      DihedralGroup.r 1 ^ i.val := by decide
  have hsr : ∀ i : ZMod 6, (DihedralGroup.sr i : DihedralGroup 6) =
      DihedralGroup.sr 0 * DihedralGroup.r 1 ^ i.val := by decide
  cases g with
  | r i => rw [hpow i]; exact pow_mem hr _
  | sr i => rw [hsr i]; exact mul_mem hs (pow_mem hr _)

theorem borel_eq_closure : borel = Subgroup.closure {bR, bS} := by
  rw [← range_dihedralHom, MonoidHom.range_eq_map, ← closure_dihedral, MonoidHom.map_closure,
    Set.image_pair, dihedralHom_r_one, dihedralHom_sr_zero]

theorem unip_mem_borel (k : ZMod 3) : unip k ∈ borel := by
  rw [mem_borel]
  rfl

theorem bruhat : ∀ g : GL23, g ∈ borel ∨ ∃ k : ZMod 3, (unip k * w0)⁻¹ * g ∈ borel := by
  decide +kernel

theorem eq_top_of_borel_le {H : Subgroup GL23} (hB : borel ≤ H) (hw : w0 ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rcases bruhat g with h | ⟨k, hk⟩
  · exact hB h
  · have : g = unip k * w0 * ((unip k * w0)⁻¹ * g) := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (hB (unip_mem_borel k)) hw) (hB hk)

theorem eq_borel_or_eq_top {H : Subgroup GL23} (hB : borel ≤ H) : H = borel ∨ H = ⊤ := by
  by_cases h : H ≤ borel
  · exact Or.inl (le_antisymm h hB)
  · right
    obtain ⟨g, hg, hgb⟩ := Set.not_subset.1 h
    rcases bruhat g with h' | ⟨k, hk⟩
    · exact absurd h' hgb
    · refine eq_top_of_borel_le hB ?_
      have : w0 = (unip k)⁻¹ * g * ((unip k * w0)⁻¹ * g)⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem (hB (unip_mem_borel k))) hg) (H.inv_mem (hB hk))

section Semidihedral

open CFSG.Open CFSG.Semidihedral

variable {G : Type*} [Group G]

@[expose] noncomputable def sdHom (R S : G) (h8 : R ^ 8 = 1) (h2 : S ^ 2 = 1)
    (hc : S * R * S⁻¹ = R ^ 3) : SemidihedralGroup 4 →* G :=
  PresentedGroup.toGroup (f := ![R, S]) (by
    intro r hr
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using h8
    · simpa using h2
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hc]
      norm_num)

theorem sdHom_r (R S : G) (h8 : R ^ 8 = 1) (h2 : S ^ 2 = 1) (hc : S * R * S⁻¹ = R ^ 3) :
    sdHom R S h8 h2 hc (r 4) = R := PresentedGroup.toGroup.of _

theorem sdHom_s (R S : G) (h8 : R ^ 8 = 1) (h2 : S ^ 2 = 1) (hc : S * R * S⁻¹ = R ^ 3) :
    sdHom R S h8 h2 hc (s 4) = S := PresentedGroup.toGroup.of _

theorem nonempty_mulEquiv_semidihedral {H : Subgroup G} [Finite H] (hH : Nat.card H ∣ 16)
    {R S : G} (hR : R ∈ H) (hS : S ∈ H) (h8 : R ^ 8 = 1) (h2 : S ^ 2 = 1)
    (hc : S * R * S⁻¹ = R ^ 3)
    (hne : ∀ i : Fin 8, ∀ e : Fin 2, R ^ (i : ℕ) * S ^ (e : ℕ) = 1 → i = 0 ∧ e = 0) :
    Nonempty (H ≃* SemidihedralGroup 4) := by
  set φ := sdHom R S h8 h2 hc
  have hmod : modulus 4 = 8 := rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [mem_bot]
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv 4 (by norm_num)).symm.surjective g
    change φ (element 4 (by norm_num) i e) = 1 at hg
    change element 4 (by norm_num) i e = 1
    rw [element_eq] at hg ⊢
    rw [map_mul, map_pow, map_pow, sdHom_r, sdHom_s] at hg
    have hi : i.val < 8 := hmod ▸ ZMod.val_lt i
    have he : e.val < 2 := ZMod.val_lt e
    obtain ⟨h1, h2⟩ := hne ⟨i.val, hi⟩ ⟨e.val, he⟩ hg
    have hi0 : i.val = 0 := congrArg Fin.val h1
    have he0 : e.val = 0 := congrArg Fin.val h2
    rw [hi0, he0, pow_zero, pow_zero, one_mul]
  have hle : φ.range ≤ H := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      closure_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    fin_cases k
    · exact (sdHom_r R S h8 h2 hc) ▸ hR
    · exact (sdHom_s R S h8 h2 hc) ▸ hS
  have hcard : Nat.card φ.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card 4 (by norm_num)]
    norm_num
  have heq : φ.range = H := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard]
    exact Nat.le_of_dvd (by norm_num) hH
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans (MonoidHom.ofInjective hinj).symm⟩

end Semidihedral

end CFSG.RankThree.Asc83Table
