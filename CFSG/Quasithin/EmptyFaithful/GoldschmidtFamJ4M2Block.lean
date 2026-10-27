module

public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.Quasithin.J4M2

section Image

variable {α : Type*} [DecidableEq α]

theorem image_perm_mul (g h : Equiv.Perm α) (s : Finset α) :
    s.image ⇑(g * h) = (s.image ⇑h).image ⇑g := by
  rw [Finset.image_image, Equiv.Perm.coe_mul]

theorem image_perm_one (s : Finset α) : s.image ⇑(1 : Equiv.Perm α) = s := by
  rw [Equiv.Perm.coe_one, Finset.image_id]

theorem image_perm_inv_image (g : Equiv.Perm α) (s : Finset α) :
    (s.image ⇑g).image ⇑(g⁻¹) = s := by
  rw [← image_perm_mul, inv_mul_cancel, image_perm_one]

end Image

variable {α ι : Type*} [DecidableEq α] [Finite ι]

@[expose] def blockStab (B : ι → Finset α) (hB : Function.Injective B) :
    Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ i, ∃ j, (B i).image g = B j}
  mul_mem' := by
    intro g h hg hh i
    obtain ⟨j, hj⟩ := hh i
    obtain ⟨k, hk⟩ := hg j
    exact ⟨k, by rw [image_perm_mul, hj, hk]⟩
  one_mem' := fun i => ⟨i, image_perm_one _⟩
  inv_mem' := by
    intro g hg
    choose f hf using hg
    have hinj : Function.Injective f := fun i i' h =>
      hB (Finset.image_injective g.injective (by rw [hf i, hf i', h]))
    intro j
    obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hinj j
    exact ⟨i, by rw [← hf i, image_perm_inv_image]⟩

variable {B : ι → Finset α} {hB : Function.Injective B}

theorem mem_blockStab {g : Equiv.Perm α} :
    g ∈ blockStab B hB ↔ ∀ i, ∃ j, (B i).image g = B j :=
  Iff.rfl

noncomputable def blockFun (g : blockStab B hB) (i : ι) : ι :=
  Classical.choose (mem_blockStab.1 g.2 i)

theorem blockFun_spec (g : blockStab B hB) (i : ι) :
    (B i).image (g : Equiv.Perm α) = B (blockFun g i) :=
  Classical.choose_spec (mem_blockStab.1 g.2 i)

theorem blockFun_eq_iff (g : blockStab B hB) (i j : ι) :
    blockFun g i = j ↔ (B i).image (g : Equiv.Perm α) = B j :=
  ⟨fun h => by subst h; exact blockFun_spec g i,
    fun h => hB ((blockFun_spec g i).symm.trans h)⟩

theorem blockFun_mul (g h : blockStab B hB) (i : ι) :
    blockFun (g * h) i = blockFun g (blockFun h i) := by
  rw [blockFun_eq_iff, Subgroup.coe_mul, image_perm_mul, blockFun_spec h i, blockFun_spec g]

theorem blockFun_one (i : ι) : blockFun (1 : blockStab B hB) i = i := by
  rw [blockFun_eq_iff, Subgroup.coe_one, image_perm_one]

noncomputable def blockHom (B : ι → Finset α) (hB : Function.Injective B) :
    blockStab B hB →* Equiv.Perm ι :=
  MonoidHom.mk'
    (fun g =>
      { toFun := blockFun g
        invFun := blockFun g⁻¹
        left_inv := fun i => by rw [← blockFun_mul, inv_mul_cancel, blockFun_one]
        right_inv := fun i => by rw [← blockFun_mul, mul_inv_cancel, blockFun_one] })
    (fun g h => Equiv.ext fun i => by
      rw [Equiv.Perm.mul_apply]
      exact blockFun_mul g h i)

theorem blockHom_apply_eq_iff (g : blockStab B hB) (i j : ι) :
    blockHom B hB g i = j ↔ (B i).image (g : Equiv.Perm α) = B j :=
  blockFun_eq_iff g i j

theorem closure_le_blockStab (B : ι → Finset α) (hB : Function.Injective B)
    (S : Set (Equiv.Perm α)) (hS : ∀ g ∈ S, ∀ i, ∃ j, (B i).image g = B j) :
    Subgroup.closure S ≤ blockStab B hB :=
  (Subgroup.closure_le _).2 hS

@[expose] noncomputable def restrictedBlockHom (B : ι → Finset α) (hB : Function.Injective B)
    {H : Subgroup (Equiv.Perm α)} (hH : H ≤ blockStab B hB) : H →* Equiv.Perm ι :=
  (blockHom B hB).comp (Subgroup.inclusion hH)

theorem restrictedBlockHom_apply_eq_iff {H : Subgroup (Equiv.Perm α)} (hH : H ≤ blockStab B hB)
    (g : H) (i j : ι) :
    restrictedBlockHom B hB hH g i = j ↔ (B i).image (g : Equiv.Perm α) = B j := by
  rw [restrictedBlockHom, MonoidHom.comp_apply, blockHom_apply_eq_iff, Subgroup.coe_inclusion]

theorem restrictedBlockHom_spec {H : Subgroup (Equiv.Perm α)} (hH : H ≤ blockStab B hB)
    (g : H) (i : ι) :
    (B i).image (g : Equiv.Perm α) = B (restrictedBlockHom B hB hH g i) :=
  (restrictedBlockHom_apply_eq_iff hH g i _).1 rfl

theorem restrictedBlockHom_eq_iff {H : Subgroup (Equiv.Perm α)} (hH : H ≤ blockStab B hB)
    (g : H) (σ : Equiv.Perm ι) :
    restrictedBlockHom B hB hH g = σ ↔ ∀ i, (B i).image (g : Equiv.Perm α) = B (σ i) := by
  rw [Equiv.ext_iff]
  exact forall_congr' fun i => restrictedBlockHom_apply_eq_iff hH g i (σ i)

theorem mem_ker_restrictedBlockHom {H : Subgroup (Equiv.Perm α)} (hH : H ≤ blockStab B hB)
    (g : H) :
    g ∈ (restrictedBlockHom B hB hH).ker ↔ ∀ i, (B i).image (g : Equiv.Perm α) = B i := by
  rw [MonoidHom.mem_ker, restrictedBlockHom_eq_iff]
  simp

theorem restrictedBlockHom_injective_of_simple {H : Subgroup (Equiv.Perm α)}
    (hH : H ≤ blockStab B hB) [IsSimpleGroup H]
    (hmove : ∃ g ∈ H, ∃ i, (B i).image g ≠ B i) :
    Function.Injective (restrictedBlockHom B hB hH) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (restrictedBlockHom B hB hH).ker with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg, i, hi⟩ := hmove
    have hmem : (⟨g, hg⟩ : H) ∈ (restrictedBlockHom B hB hH).ker := by
      rw [h]
      trivial
    exact hi ((mem_ker_restrictedBlockHom hH ⟨g, hg⟩).1 hmem i)

end CFSG.Quasithin.J4M2
