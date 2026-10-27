module

public import CFSG.Quasithin.Background.A3StructureDefs


public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique

theorem comm_of_fix_zero : ∀ σ τ : Equiv.Perm (Fin 3), σ 0 = 0 → τ 0 = 0 → σ * τ = τ * σ := by
  decide

theorem le_center_of_card_three {X : Type*} [Group X] (hperf : commutator X = ⊤)
    {N : Subgroup X} [hN : N.Normal] (h3 : Nat.card N = 3) : N ≤ Subgroup.center X := by
  classical
  have : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  let e₀ : ↥N ≃ Fin 3 := Finite.equivFinOfCardEq h3
  set e : ↥N ≃ Fin 3 := e₀.trans (Equiv.swap (e₀ 1) 0) with he
  have he1 : e 1 = 0 := by simp [he, Equiv.swap_apply_left]
  let ρ : X →* Equiv.Perm (Fin 3) :=
    { toFun := fun x => e.permCongr (MulAut.conjNormal (H := N) x).toEquiv
      map_one' := by ext i; simp
      map_mul' := fun x y => by ext i; simp [Equiv.permCongr_apply] }
  have hfix : ∀ x, ρ x 0 = 0 := by
    intro x
    show e ((MulAut.conjNormal (H := N) x) (e.symm 0)) = 0
    rw [← he1, Equiv.symm_apply_apply, map_one, he1]
  have hcomm : commutator X ≤ ρ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul,
      map_inv, map_inv, comm_of_fix_zero _ _ (hfix x) (hfix y)]
    group
  rw [hperf] at hcomm
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : ρ x = 1 := hcomm (Subgroup.mem_top x)
  have h1 : (MulAut.conjNormal (H := N) x) ⟨n, hn⟩ = ⟨n, hn⟩ := by
    have := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (e ⟨n, hn⟩)) hx
    simp only [ρ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply,
      Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at this
    exact e.injective this
  have h2 := congrArg Subtype.val h1
  simp only [MulAut.conjNormal_apply] at h2
  calc x * n = x * n * x⁻¹ * x := by group
    _ = n * x := by rw [h2]

theorem isHat_of_surj {X S : Type} [Group X] [Group S] [hS : IsSimpleGroup S]
    (hnc : ∃ x y : S, x * y ≠ y * x) (hperf : commutator X = ⊤) (φ : X →* S)
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3) : CFSG.Quasithin.IsHat X S := by
  have hZS : Subgroup.center S = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have : x ∈ Subgroup.center S := by rw [h]; trivial
      exact hxy (Subgroup.mem_center_iff.mp this y).symm
  have hle : φ.ker ≤ Subgroup.center X := le_center_of_card_three hperf hk
  have hge : Subgroup.center X ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : φ z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨x, rfl⟩ := hφ s
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz x)]
    rw [hZS, Subgroup.mem_bot] at this
    exact this
  have hZ : Subgroup.center X = φ.ker := le_antisymm hge hle
  let eq : X ⧸ Subgroup.center X ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hsimp : IsSimpleGroup (X ⧸ Subgroup.center X) := eq.isSimpleGroup
  refine ⟨⟨⟨hperf⟩, hsimp, ?_⟩, by rw [hZ, hk], ⟨eq⟩⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨eq.symm x, eq.symm y, fun h => hxy (by simpa using congrArg eq h)⟩

section Blocks

variable {α : Type*} [DecidableEq α] {k : ℕ} (B : Fin k → Finset α)

@[expose] def blockStab (hB : Function.Injective B) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ i, ∃ j, (B i).image g = B j}
  mul_mem' := by
    rintro a b ha hb i
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨l, hl⟩ := ha j
    refine ⟨l, ?_⟩
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, hj, hl]
  one_mem' := fun i => ⟨i, by simp⟩
  inv_mem' := by
    rintro a ha i
    choose f hf using ha
    have hfi : Function.Injective f := by
      intro j j' hjj'
      apply hB
      have h1 := hf j
      have h2 := hf j'
      rw [hjj'] at h1
      rw [← h1] at h2
      exact Finset.image_injective a.injective h2.symm
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hfi) i
    refine ⟨j, ?_⟩
    rw [← hj, ← hf j, Finset.image_image]
    simp

variable {B} (hB : Function.Injective B)

theorem exists_image_block (g : ↥(blockStab B hB)) (i : Fin k) :
    ∃ j, (B i).image (g : Equiv.Perm α) = B j := g.2 i

@[expose] noncomputable def blockFun (g : ↥(blockStab B hB)) (i : Fin k) : Fin k :=
  (exists_image_block hB g i).choose

theorem blockFun_spec (g : ↥(blockStab B hB)) (i : Fin k) :
    (B i).image (g : Equiv.Perm α) = B (blockFun hB g i) :=
  (exists_image_block hB g i).choose_spec

theorem blockFun_eq {g : ↥(blockStab B hB)} {i j : Fin k}
    (h : (B i).image (g : Equiv.Perm α) = B j) : blockFun hB g i = j :=
  hB ((blockFun_spec hB g i).symm.trans h)

theorem blockFun_mul (g h : ↥(blockStab B hB)) (i : Fin k) :
    blockFun hB (g * h) i = blockFun hB g (blockFun hB h i) := by
  apply blockFun_eq
  rw [Subgroup.coe_mul, Equiv.Perm.coe_mul, ← Finset.image_image, blockFun_spec hB h i,
    blockFun_spec hB g]

theorem blockFun_one (i : Fin k) : blockFun hB 1 i = i := blockFun_eq hB (by simp)

@[expose] noncomputable def blockAct : ↥(blockStab B hB) →* Equiv.Perm (Fin k) where
  toFun g :=
    { toFun := blockFun hB g
      invFun := blockFun hB g⁻¹
      left_inv := fun i => by rw [← blockFun_mul, inv_mul_cancel, blockFun_one]
      right_inv := fun i => by rw [← blockFun_mul, mul_inv_cancel, blockFun_one] }
  map_one' := Equiv.ext fun i => blockFun_one hB i
  map_mul' g h := Equiv.ext fun i => blockFun_mul hB g h i

theorem image_block (g : ↥(blockStab B hB)) (i : Fin k) :
    (B i).image (g : Equiv.Perm α) = B (blockAct hB g i) :=
  blockFun_spec hB g i

theorem blockAct_eq_one_iff (g : ↥(blockStab B hB)) :
    blockAct hB g = 1 ↔ ∀ i, (B i).image (g : Equiv.Perm α) = B i := by
  constructor
  · intro h i
    rw [image_block, h, Equiv.Perm.one_apply]
  · intro h
    ext i
    exact congrArg Fin.val (blockFun_eq hB (h i))

end Blocks

end CFSG.Quasithin.KGC31

end
