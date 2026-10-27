module

public import CFSG.Quasithin.EmptyFaithful.S151YE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def ya7Rel (π : Equiv.Perm (Fin 7)) (P : Finset (Finset (Fin 7))) :
    Finset (Finset (Fin 7)) :=
  P.image (Finset.image π)

theorem ya7Rel_inv (π : Equiv.Perm (Fin 7)) (P : Finset (Finset (Fin 7))) :
    ya7Rel π⁻¹ (ya7Rel π P) = P := by
  unfold ya7Rel
  rw [Finset.image_image]
  have : Finset.image ⇑π⁻¹ ∘ Finset.image ⇑π = id := by
    funext B
    simp [Finset.image_image]
  rw [this, Finset.image_id]

theorem ya7Rel_inv' (π : Equiv.Perm (Fin 7)) (P : Finset (Finset (Fin 7))) :
    ya7Rel π (ya7Rel π⁻¹ P) = P := by
  simpa using ya7Rel_inv π⁻¹ P

theorem ya7Rel_type {P : Finset (Finset (Fin 7))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (π : Equiv.Perm (Fin 7)) :
    IsPartitionOfType (ya7Rel π P) sizes :=
  ya7_isPartitionOfType_image hP π

theorem ya7_stab_conj_iff (π : Equiv.Perm (Fin 7)) {σ : Equiv.Perm (Fin 7)}
    {P : Finset (Finset (Fin 7))} :
    StabilizesPartition (π * σ * π⁻¹) (ya7Rel π P) ↔ StabilizesPartition σ P := by
  refine ⟨fun h => ?_, ya7_stab_conj π⟩
  have h' := ya7_stab_conj π⁻¹ h
  have e : π⁻¹ * (π * σ * π⁻¹) * π⁻¹⁻¹ = σ := by group
  rw [e] at h'
  have h'' : StabilizesPartition σ (ya7Rel π⁻¹ (ya7Rel π P)) := h'
  rwa [ya7Rel_inv] at h''

@[expose] def ya7Act (g : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  fun i => v (g⁻¹ i)

theorem ya7Act_injective (g : Equiv.Perm (Fin 7)) : Function.Injective (ya7Act g) := by
  intro v w h
  funext i
  have := congrFun h (g i)
  simpa [ya7Act] using this

theorem ya7Act_mem_delta (g : Equiv.Perm (Fin 7)) {v : Fin 7 → ZMod 2} (hv : v ∈ ya7Delta) :
    ya7Act g v ∈ ya7Delta := by
  simp only [ya7Delta, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  have : (∑ i, ya7Act g v i) = ∑ i, v i := Equiv.sum_comp g⁻¹ v
  rw [this]
  exact hv

theorem ya7Sub_conj (g σ : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2) :
    ya7Sub (g * σ * g⁻¹) (ya7Act g v) = ya7Act g (ya7Sub σ v) := by
  funext i
  simp [ya7Sub, ya7Act, mul_assoc]

theorem ya7Sub3_conj (g σ : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2) :
    ya7Sub3 (g * σ * g⁻¹) (ya7Act g v) = ya7Act g (ya7Sub3 σ v) := by
  unfold ya7Sub3
  rw [ya7Sub_conj, ya7Sub_conj, ya7Sub_conj]

theorem ya7_imCard3_conj (g σ : Equiv.Perm (Fin 7)) :
    (ya7ImVecs3 (g * σ * g⁻¹)).card = (ya7ImVecs3 σ).card := by
  have h1 : ya7ImVecs3 (g * σ * g⁻¹) = (ya7ImVecs3 σ).image (ya7Act g) := by
    ext y
    simp only [ya7ImVecs3, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨ya7Sub3 σ (ya7Act g⁻¹ z), ⟨ya7Act g⁻¹ z, ya7Act_mem_delta g⁻¹ hz, rfl⟩, ?_⟩
      rw [← ya7Sub3_conj]
      congr 1
      funext i
      simp [ya7Act]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨ya7Act g z, ya7Act_mem_delta g hz, ya7Sub3_conj g σ z⟩
  rw [h1, Finset.card_image_of_injective _ (ya7Act_injective g)]

theorem ya7_card_le_of_range (σ : Equiv.Perm (Fin 7)) {X : Type*} [Finite X]
    (F : X → (Fin 7 → ZMod 2)) (hF : ∀ z ∈ ya7Delta, ∃ x, F x = ya7Sub3 σ z) :
    (ya7ImVecs3 σ).card ≤ Nat.card X := by
  have hsub : (↑(ya7ImVecs3 σ) : Set (Fin 7 → ZMod 2)) ⊆ Set.range F := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx⟩ := hF z hz
    exact ⟨x, hx⟩
  calc (ya7ImVecs3 σ).card = (↑(ya7ImVecs3 σ) : Set (Fin 7 → ZMod 2)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (Set.range F).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (Set.range F) := by
        rw [Nat.card_coe_set_eq]
    _ ≤ Nat.card X := Finite.card_range_le F

theorem ya7_data (D : Subgroup (alternatingGroup (Fin 7))) (hD : IsSylowTwoOf D ⊤)
    {P : Finset (Finset (Fin 7))} (hP : IsPartitionOfType P {2, 2, 2, 1})
    (hst : ∀ d ∈ D, StabilizesPartition (d : Equiv.Perm (Fin 7)) P) :
    D ≤ ya7PartStab P ∧ Nat.card ↥(ya7PartStab P) = 24 ∧
      (∀ K : Subgroup (alternatingGroup (Fin 7)), D ≤ K → K ≤ ya7PartStab P →
        K = D ∨ K = ya7PartStab P) ∧
      (∃ q ∈ ya7PartStab P, ∃ d ∈ D, q * d * q⁻¹ ∉ D) ∧
      (∀ P' : Finset (Finset (Fin 7)), IsPartitionOfType P' {2, 2, 2, 1} →
        (∀ d ∈ D, StabilizesPartition (d : Equiv.Perm (Fin 7)) P') → P' = P) ∧
      (∀ σ ∈ ya7PartStab P, σ ^ 3 = 1 → σ ≠ 1 →
        16 ≤ (ya7ImVecs3 (σ : Equiv.Perm (Fin 7))).card) ∧
      (∀ σ ∈ ya7PartStab P, ∀ τ ∈ ya7PartStab P, σ ^ 3 = 1 → σ ≠ 1 → τ ^ 3 = 1 → τ ≠ 1 →
        σ * τ = τ * σ → τ = σ ∨ τ = σ⁻¹) := by
  obtain ⟨h, -, hDh⟩ := IsSylowTwoOf.exists_conj ya7D0_sylow hD
  set g : Equiv.Perm (Fin 7) := (h : Equiv.Perm (Fin 7)) with hg
  have hred : ∀ P' : Finset (Finset (Fin 7)), IsPartitionOfType P' {2, 2, 2, 1} →
      (∀ d ∈ D, StabilizesPartition (d : Equiv.Perm (Fin 7)) P') →
      ya7Rel g⁻¹ P' = ya7P0 := by
    intro P' hP' hst'
    refine ya7_unique_stable (ya7Rel_type hP' g⁻¹) (fun i => ?_)
    have hmem : (h * (⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩ :
        alternatingGroup (Fin 7)) * h⁻¹ : alternatingGroup (Fin 7)) ∈ D := by
      rw [hDh]
      refine Subgroup.mem_map.mpr ⟨⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩,
        ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr ⟨i, rfl⟩
      · simp [MulAut.conj_apply]
    have h1 : StabilizesPartition (g⁻¹ * ((h * (⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩ :
        alternatingGroup (Fin 7)) * h⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * g⁻¹⁻¹)
        (ya7Rel g⁻¹ P') := ya7_stab_conj g⁻¹ (hst' _ hmem)
    have hcoe : ((h * (⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩ :
        alternatingGroup (Fin 7)) * h⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          g * ya7E i * g⁻¹ := rfl
    have e : g⁻¹ * (g * ya7E i * g⁻¹) * g⁻¹⁻¹ = ya7E i := by group
    rw [hcoe, e] at h1
    exact h1
  have hP0 : ya7Rel g⁻¹ P = ya7P0 := hred P hP hst
  have hQ : ∀ σ : alternatingGroup (Fin 7),
      σ ∈ ya7PartStab P ↔ (h⁻¹ * σ * h) ∈ ya7PartStab ya7P0 := by
    intro σ
    show StabilizesPartition (σ : Equiv.Perm (Fin 7)) P ↔
      StabilizesPartition ((h⁻¹ * σ * h : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ya7P0
    have hcoe : ((h⁻¹ * σ * h : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        g⁻¹ * (σ : Equiv.Perm (Fin 7)) * g⁻¹⁻¹ := rfl
    rw [hcoe, ← hP0]
    exact (ya7_stab_conj_iff g⁻¹).symm
  set c : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj h with hc
  have hcσ : ∀ σ : alternatingGroup (Fin 7), c.symm σ = h⁻¹ * σ * h := fun σ => by
    simp [hc, MulAut.conj_symm_apply]
  have hcapp : ∀ σ : alternatingGroup (Fin 7), c σ = h * σ * h⁻¹ := fun σ => by
    simp [hc, MulAut.conj_apply]
  have hQmem : ∀ σ : alternatingGroup (Fin 7), c σ ∈ ya7PartStab P ↔ σ ∈ ya7PartStab ya7P0 := by
    intro σ
    rw [hQ, ← hcσ, c.symm_apply_apply]
  have hDmap : D = ya7D0.map c.toMonoidHom := hDh
  have hDmem : ∀ σ : alternatingGroup (Fin 7), c σ ∈ D ↔ σ ∈ ya7D0 := by
    intro σ
    rw [hDmap, Subgroup.mem_map_equiv, c.symm_apply_apply]
  have hDQ : D ≤ ya7PartStab P := fun d hd => hst d hd
  refine ⟨hDQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hmap : ya7PartStab P = (ya7PartStab ya7P0).map c.toMonoidHom := by
      ext σ
      rw [Subgroup.mem_map_equiv]
      rw [hQ, hcσ]
    rw [hmap, Subgroup.card_map_of_injective c.injective, ya7_card_Q0]
  ·
    intro K hDK hKQ
    set K' : Subgroup (alternatingGroup (Fin 7)) := K.comap c.toMonoidHom with hK'
    have h1 : ya7D0 ≤ K' := fun x hx => hDK ((hDmem x).mpr hx)
    have h2 : K' ≤ ya7PartStab ya7P0 := fun x hx => (hQmem x).mp (hKQ hx)
    have hKeq : K'.map c.toMonoidHom = K := Subgroup.map_comap_eq_self_of_surjective c.surjective K
    rcases ya7_between K' h1 h2 with h3 | h3
    · left
      rw [← hKeq, h3, ← hDmap]
    · right
      have hmap : ya7PartStab P = (ya7PartStab ya7P0).map c.toMonoidHom := by
        ext σ
        rw [Subgroup.mem_map_equiv]
        rw [hQ, hcσ]
      rw [← hKeq, h3, ← hmap]
  ·
    obtain ⟨q, hq, d, hd, hnot⟩ := ya7_D0_not_normal
    refine ⟨c q, (hQmem q).mpr hq, c d, (hDmem d).mpr hd, fun hmem => hnot ?_⟩
    have : c (q * d * q⁻¹) ∈ D := by rwa [map_mul, map_mul, map_inv]
    exact (hDmem _).mp this
  ·
    intro P' hP' hst'
    have h1 : ya7Rel g⁻¹ P' = ya7Rel g⁻¹ P := (hred P' hP' hst').trans hP0.symm
    have h2 := congrArg (ya7Rel g) h1
    rwa [ya7Rel_inv', ya7Rel_inv'] at h2
  ·
    intro σ hσ h3 h1
    have hσ0 : (h⁻¹ * σ * h) ∈ ya7PartStab ya7P0 := (hQ σ).mp hσ
    obtain ⟨i, hi⟩ := ya7Q_complete _ hσ0
    have h3' : (ya7Q i) ^ 3 = 1 := by
      rw [← hi]
      have := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7)))
        (show (h⁻¹ * σ * h) ^ 3 = 1 by rw [← hcσ, ← map_pow, h3, map_one])
      simpa using this
    have h1' : ya7Q i ≠ 1 := by
      rw [← hi]
      intro hone
      apply h1
      have : h⁻¹ * σ * h = 1 := Subtype.ext hone
      rw [← hcσ] at this
      exact c.symm.injective (by rw [this, map_one])
    have h16 := ya7_im3_card i h3' h1'
    have hcard := ya7_imCard3_conj g⁻¹ (σ : Equiv.Perm (Fin 7))
    rw [← hi] at h16
    have hcoe : ((h⁻¹ * σ * h : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        g⁻¹ * (σ : Equiv.Perm (Fin 7)) * g⁻¹⁻¹ := rfl
    rw [hcoe, hcard] at h16
    exact h16
  ·
    intro σ hσ τ hτ hσ3 hσ1 hτ3 hτ1 hcomm
    have hσ0 : (h⁻¹ * σ * h) ∈ ya7PartStab ya7P0 := (hQ σ).mp hσ
    have hτ0 : (h⁻¹ * τ * h) ∈ ya7PartStab ya7P0 := (hQ τ).mp hτ
    obtain ⟨i, hi⟩ := ya7Q_complete _ hσ0
    obtain ⟨j, hj⟩ := ya7Q_complete _ hτ0
    have hcubic : ∀ x : alternatingGroup (Fin 7), x ^ 3 = 1 → ((h⁻¹ * x * h : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) ^ 3 = 1 := by
      intro x hx
      have := congrArg (fun y : alternatingGroup (Fin 7) => (y : Equiv.Perm (Fin 7)))
        (show (h⁻¹ * x * h) ^ 3 = 1 by rw [← hcσ, ← map_pow, hx, map_one])
      simpa using this
    have hne1 : ∀ x : alternatingGroup (Fin 7), x ≠ 1 → ((h⁻¹ * x * h : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) ≠ 1 := by
      intro x hx hone
      apply hx
      have : h⁻¹ * x * h = 1 := Subtype.ext hone
      rw [← hcσ] at this
      exact c.symm.injective (by rw [this, map_one])
    have hcomm0 : (h⁻¹ * σ * h) * (h⁻¹ * τ * h) = (h⁻¹ * τ * h) * (h⁻¹ * σ * h) := by
      calc (h⁻¹ * σ * h) * (h⁻¹ * τ * h) = h⁻¹ * (σ * τ) * h := by group
        _ = h⁻¹ * (τ * σ) * h := by rw [hcomm]
        _ = (h⁻¹ * τ * h) * (h⁻¹ * σ * h) := by group
    have hcomm' : ya7Q i * ya7Q j = ya7Q j * ya7Q i := by
      rw [← hi, ← hj]
      exact congrArg Subtype.val hcomm0
    have key := ya7_comm_three i j (hi ▸ hcubic σ hσ3) (hi ▸ hne1 σ hσ1) (hj ▸ hcubic τ hτ3)
      (hj ▸ hne1 τ hτ1) hcomm'
    rcases key with hk | hk
    · left
      have : h⁻¹ * τ * h = h⁻¹ * σ * h := Subtype.ext (by rw [← hi, ← hj] at hk; exact hk)
      rw [← hcσ, ← hcσ] at this
      exact c.symm.injective this
    · right
      have : h⁻¹ * τ * h = (h⁻¹ * σ * h)⁻¹ :=
        Subtype.ext (by rw [← hi, ← hj] at hk; exact hk)
      rw [← hcσ, ← hcσ, ← map_inv] at this
      exact c.symm.injective this

end CFSG.Quasithin
