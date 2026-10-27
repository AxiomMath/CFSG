module

public import CFSG.Quasithin.EmptyFaithful.SzN32ModelData

public section

namespace CFSG.Quasithin.SzN32

namespace Model

private def T6 : Subgroup (GL (Fin 6) (ZMod 2)) := Subgroup.closure {ga, gs}

private def nfSet : Set (GL (Fin 6) (ZMod 2)) :=
  Set.range fun x : Fin 3 × Fin 3 × Fin 3 × Fin 3 => nf x.1 x.2.1 x.2.2.1 x.2.2.2

private def nf0Set : Set (GL (Fin 6) (ZMod 2)) :=
  Set.range fun x : Fin 3 × Fin 3 × Fin 3 => nf x.1 x.2.1 x.2.2 0

private theorem ga_mem : ga ∈ T6 := Subgroup.subset_closure (by simp)

private theorem gs_mem : gs ∈ T6 := Subgroup.subset_closure (by simp)

private theorem ga_inv : ga⁻¹ = ga * ga :=
  inv_eq_of_mul_eq_one_right ((pow_three ga).symm.trans cubes.1)

private theorem gs_inv : gs⁻¹ = gs * gs :=
  inv_eq_of_mul_eq_one_right ((pow_three gs).symm.trans cubes.2.1)

private theorem ga1_inv : ga1⁻¹ = ga1 * ga1 :=
  inv_eq_of_mul_eq_one_right ((pow_three ga1).symm.trans cubes.2.2.1)

private theorem ga2_inv : ga2⁻¹ = ga2 * ga2 :=
  inv_eq_of_mul_eq_one_right ((pow_three ga2).symm.trans cubes.2.2.2)

private theorem ga1_mem : ga1 ∈ T6 :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ gs_mem) ga_mem) gs_mem

private theorem ga2_mem : ga2 ∈ T6 :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ gs_mem) ga1_mem) gs_mem

private theorem nf_mem (i j k l : Fin 3) : nf i j k l ∈ T6 :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ga_mem _)
    (Subgroup.pow_mem _ ga1_mem _)) (Subgroup.pow_mem _ ga2_mem _)) (Subgroup.pow_mem _ gs_mem _)

private theorem nfSet_mul_ga {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ nfSet) : g * ga ∈ nfSet := by
  obtain ⟨⟨i, j, k, l⟩, rfl⟩ := hg
  obtain ⟨i', j', k', l', h⟩ := nf_mul_ga i j k l
  exact ⟨(i', j', k', l'), h.symm⟩

private theorem nfSet_mul_gs {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ nfSet) : g * gs ∈ nfSet := by
  obtain ⟨⟨i, j, k, l⟩, rfl⟩ := hg
  obtain ⟨i', j', k', l', h⟩ := nf_mul_gs i j k l
  exact ⟨(i', j', k', l'), h.symm⟩

private theorem mem_T6_iff (g : GL (Fin 6) (ZMod 2)) : g ∈ T6 ↔ g ∈ nfSet := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨(0, 0, 0, 0), by simp [nf]⟩
    | mul_right x hx y hy ih =>
      rcases hy with rfl | hy
      · exact nfSet_mul_ga ih
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact nfSet_mul_gs ih
    | mul_inv_cancel x hx y hy ih =>
      rcases hy with rfl | hy
      · rw [ga_inv, ← mul_assoc]
        exact nfSet_mul_ga (nfSet_mul_ga ih)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [gs_inv, ← mul_assoc]
        exact nfSet_mul_gs (nfSet_mul_gs ih)
  · rintro ⟨⟨i, j, k, l⟩, rfl⟩
    exact nf_mem i j k l

private theorem nf_injective :
    Function.Injective fun x : Fin 3 × Fin 3 × Fin 3 × Fin 3 => nf x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
  obtain ⟨h1, h2, h3, h4⟩ := nf_inj i j k l i' j' k' l' h
  subst h1 h2 h3 h4
  rfl

private theorem card_T6 : Nat.card T6 = 81 := by
  have h : (T6 : Set (GL (Fin 6) (ZMod 2))) = nfSet := Set.ext fun g => mem_T6_iff g
  calc Nat.card T6 = Nat.card (T6 : Set (GL (Fin 6) (ZMod 2))) := rfl
    _ = Nat.card nfSet := by rw [h]
    _ = Nat.card (Fin 3 × Fin 3 × Fin 3 × Fin 3) := Nat.card_range_of_injective nf_injective
    _ = 81 := by simp

private def D6 : Subgroup (GL (Fin 6) (ZMod 2)) := Subgroup.closure {ga, ga1, ga2}

private theorem D6_le : D6 ≤ T6 := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  rcases hg with rfl | rfl | hg
  · exact ga_mem
  · exact ga1_mem
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ga2_mem

private theorem nf0Set_mul {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ nf0Set) :
    g * ga ∈ nf0Set ∧ g * ga1 ∈ nf0Set ∧ g * ga2 ∈ nf0Set := by
  obtain ⟨⟨i, j, k⟩, rfl⟩ := hg
  obtain ⟨i1, j1, k1, h1⟩ := nf0_mul_ga i j k
  obtain ⟨i2, j2, k2, h2⟩ := nf0_mul_ga1 i j k
  obtain ⟨i3, j3, k3, h3⟩ := nf0_mul_ga2 i j k
  exact ⟨⟨(i1, j1, k1), h1.symm⟩, ⟨(i2, j2, k2), h2.symm⟩, ⟨(i3, j3, k3), h3.symm⟩⟩

private theorem mem_D6_iff (g : GL (Fin 6) (ZMod 2)) : g ∈ D6 ↔ g ∈ nf0Set := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨(0, 0, 0), by simp [nf]⟩
    | mul_right x hx y hy ih =>
      rcases hy with rfl | rfl | hy
      · exact (nf0Set_mul ih).1
      · exact (nf0Set_mul ih).2.1
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (nf0Set_mul ih).2.2
    | mul_inv_cancel x hx y hy ih =>
      rcases hy with rfl | rfl | hy
      · rw [ga_inv, ← mul_assoc]
        exact (nf0Set_mul (nf0Set_mul ih).1).1
      · rw [ga1_inv, ← mul_assoc]
        exact (nf0Set_mul (nf0Set_mul ih).2.1).2.1
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [ga2_inv, ← mul_assoc]
        exact (nf0Set_mul (nf0Set_mul ih).2.2).2.2
  · rintro ⟨⟨i, j, k⟩, rfl⟩
    have h1 : ga ∈ D6 := Subgroup.subset_closure (by simp)
    have h2 : ga1 ∈ D6 := Subgroup.subset_closure (by simp)
    have h3 : ga2 ∈ D6 := Subgroup.subset_closure (by simp)
    unfold nf
    simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 _)
      (Subgroup.pow_mem _ h2 _)) (Subgroup.pow_mem _ h3 _)

private theorem card_D6 : Nat.card D6 = 27 := by
  have hinj : Function.Injective fun x : Fin 3 × Fin 3 × Fin 3 => nf x.1 x.2.1 x.2.2 0 := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    obtain ⟨h1, h2, h3, -⟩ := nf_inj i j k 0 i' j' k' 0 h
    subst h1 h2 h3
    rfl
  have h : (D6 : Set (GL (Fin 6) (ZMod 2))) = nf0Set := Set.ext fun g => mem_D6_iff g
  calc Nat.card D6 = Nat.card (D6 : Set (GL (Fin 6) (ZMod 2))) := rfl
    _ = Nat.card nf0Set := by rw [h]
    _ = Nat.card (Fin 3 × Fin 3 × Fin 3) := Nat.card_range_of_injective hinj
    _ = 27 := by simp

private theorem T6_tdata : TData (⟨ga, ga_mem⟩ : T6) ⟨gs, gs_mem⟩ := by
  have hz3 : ∀ k : ℤ, cm (cm ga gs) gs ^ k = cm (cm ga gs) gs ^ (k % 3) := by
    intro k
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    have : cm (cm ga gs) gs ^ (3 : ℤ) = 1 := by simpa using uz_cube.2
    rw [this, one_zpow, mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : Subgroup.closure (((↑) : T6 → GL (Fin 6) (ZMod 2)) ⁻¹'
        ({ga, gs} : Set (GL (Fin 6) (ZMod 2)))) = ⊤ := Subgroup.closure_closure_coe_preimage
    have hset : (((↑) : T6 → GL (Fin 6) (ZMod 2)) ⁻¹' ({ga, gs} : Set (GL (Fin 6) (ZMod 2)))) =
        ({⟨ga, ga_mem⟩, ⟨gs, gs_mem⟩} : Set T6) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
    rwa [hset] at h
  · exact Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact cubes.1)
  · exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact u_comm_a)
  · exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact z_comm_a)
  · exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact z_comm_s)
  · intro h
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_one] at h'
    exact z_ne_one h'
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h' : cm (cm ga gs) gs ^ k = cm ga gs := congrArg Subtype.val hk
    rw [hz3 k] at h'
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    obtain ⟨hu1, hu2, hu3⟩ := u_ne
    rcases hk3 with h0 | h1 | h2
    · rw [h0, zpow_zero] at h'
      exact hu1 h'.symm
    · rw [h1, zpow_one] at h'
      exact hu2 h'.symm
    · rw [h2, zpow_two] at h'
      exact hu3 h'.symm
  · exact Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact uz_cube.1)
  · exact Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact uz_cube.2)
  · refine ⟨D6.subgroupOf T6, ?_, ?_, ?_⟩
    · have : Nat.card (D6.subgroupOf T6) = Nat.card D6 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe D6_le).toEquiv
      rw [this]
      exact card_D6
    · intro x hx
      obtain ⟨⟨i, j, k⟩, hxe⟩ := (mem_D6_iff _).1 (hx : (x : GL (Fin 6) (ZMod 2)) ∈ D6)
      have hxe' : (x : GL (Fin 6) (ZMod 2)) = nf i j k 0 := hxe.symm
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [hxe']
      exact nf0_cube i j k
    · intro x hx y hy
      obtain ⟨⟨i, j, k⟩, hxe⟩ := (mem_D6_iff _).1 (hx : (x : GL (Fin 6) (ZMod 2)) ∈ D6)
      obtain ⟨⟨i', j', k'⟩, hye⟩ := (mem_D6_iff _).1 (hy : (y : GL (Fin 6) (ZMod 2)) ∈ D6)
      have hxe' : (x : GL (Fin 6) (ZMod 2)) = nf i j k 0 := hxe.symm
      have hye' : (y : GL (Fin 6) (ZMod 2)) = nf i' j' k' 0 := hye.symm
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hxe', hye']
      exact nf0_comm i j k i' j' k'

private def φ : GL (Fin 6) (ZMod 2) ≃* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2))

end Model

theorem model_exists :
    ∃ T₀ : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)),
      Nat.card T₀ = 81 ∧ ∃ a σ : T₀, TData a σ := by
  refine ⟨Model.T6.map Model.φ.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Model.φ.injective]
    exact Model.card_T6
  · let e : Model.T6 ≃* Model.T6.map Model.φ.toMonoidHom :=
      Subgroup.equivMapOfInjective Model.T6 Model.φ.toMonoidHom Model.φ.injective
    exact ⟨e ⟨Model.ga, Model.ga_mem⟩, e ⟨Model.gs, Model.gs_mem⟩,
      Model.T6_tdata.of_mulEquiv e⟩

end CFSG.Quasithin.SzN32
