module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34ModDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.F53.Stellmacher.S34.C3b

open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 Equiv

theorem S5Syl_le_S4pt : S5Syl ≤ S4pt := by
  unfold S5Syl S4pt
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    decide
  · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    decide

theorem index_S4pt : S4pt.index = 5 := by
  unfold S4pt
  rw [MulAction.index_stabilizer_of_transitive]
  simp

theorem le_S4pt_of_syl_le {R : Subgroup (Perm (Fin 5))} (hR : S5Syl ≤ R) (hne : R ≠ ⊤) :
    R ≤ S4pt := by
  obtain ⟨T, hST, hT, hmax⟩ := exists_unique_max_card_eight S5Syl card_S5Syl
  have hS4top : S4pt ≠ ⊤ := fun h => by
    have := index_S4pt
    rw [h, Subgroup.index_top] at this
    omega
  have h1 : S4pt ≤ T := hmax S4pt S5Syl_le_S4pt hS4top
  have h2 : T = S4pt := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h1 ?_
    have a1 := Subgroup.card_mul_index T
    have a2 := Subgroup.card_mul_index S4pt
    rw [hT] at a1
    rw [index_S4pt] at a2
    omega
  rw [← h2]
  exact hmax R hR hne

theorem card_closure_range_le {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (b : Fin 5 → V) : Nat.card (Subgroup.closure (Set.range b)) ≤ 2 ^ 5 := by
  classical
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hpow : ∀ (v : V) (n : ℕ), v ^ n = v ^ (n % 2) := fun v n => by
    conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, hV' v, one_pow, one_mul]
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  have key : ∀ x ∈ Subgroup.closure (Set.range b),
      ∃ ε : Fin 5 → ZMod 2, x = ∏ i, b i ^ (ε i).val := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ ε : Fin 5 → ZMod 2, x = ∏ i, b i ^ (ε i).val) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, ?_⟩
      rw [Finset.prod_eq_single j]
      · have : (1 : ZMod 2).val = 1 := by decide
        simp [this]
      · intro i _ hij
        simp [hij]
      · simp
    · exact ⟨0, by simp⟩
    · rintro x y - - ⟨ε, rfl⟩ ⟨δ, rfl⟩
      refine ⟨ε + δ, ?_⟩
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, hpow (b i) ((ε i).val + (δ i).val), Pi.add_apply, ZMod.val_add]
    · rintro x - ⟨ε, rfl⟩
      exact ⟨ε, hinv _⟩
  have hmem : ∀ ε : Fin 5 → ZMod 2, (∏ i, b i ^ (ε i).val) ∈ Subgroup.closure (Set.range b) :=
    fun ε => Subgroup.prod_mem _ fun i _ =>
      Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  let f : (Fin 5 → ZMod 2) → ↥(Subgroup.closure (Set.range b)) := fun ε => ⟨_, hmem ε⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨ε, rfl⟩ := key x hx
    exact ⟨ε, rfl⟩
  calc Nat.card ↥(Subgroup.closure (Set.range b)) ≤ Nat.card (Fin 5 → ZMod 2) :=
        Nat.card_le_card_of_surjective f hf
    _ = 2 ^ 5 := by simp [Nat.card_eq_fintype_card]

theorem act_eq_act_swap (M : Model 5) {w : M.W} (hw : w ∈ fixW M S4pt) (σ : Perm (Fin 5)) :
    M.act σ w = M.act (swap (σ 4) 4) w := by
  have hmem : (swap (σ 4) 4) * σ ∈ S4pt := by
    unfold S4pt
    rw [MulAction.mem_stabilizer_iff]
    show (swap (σ 4) 4) (σ 4) = 4
    simp
  have h1 := hw _ hmem
  have h2 : M.act ((swap (σ 4) 4)⁻¹) (M.act ((swap (σ 4) 4) * σ) w) = M.act σ w := by
    rw [← MulAut.mul_apply, ← map_mul]
    simp
  rw [h1] at h2
  rw [← h2]
  simp

end CFSG.Quasithin.F53.Stellmacher.S34.C3b
