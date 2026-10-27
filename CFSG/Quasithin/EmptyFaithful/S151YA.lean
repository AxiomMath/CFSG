module

public import CFSG.Quasithin.EmptyFaithful.T1515Concl
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem ya7_stab_conj {σ : Equiv.Perm (Fin 7)} (π : Equiv.Perm (Fin 7))
    {P : Finset (Finset (Fin 7))} (h : StabilizesPartition σ P) :
    StabilizesPartition (π * σ * π⁻¹) (P.image (Finset.image π)) := by
  unfold StabilizesPartition at h ⊢
  rw [Finset.image_image]
  have hcomp : (Finset.image (π * σ * π⁻¹)) ∘ (Finset.image π) =
      (Finset.image π) ∘ (Finset.image σ) := by
    funext B
    simp only [Function.comp_apply, Finset.image_image]
    congr 1
    funext b
    simp
  rw [hcomp, ← Finset.image_image, h]

theorem ya7_isPartitionOfType_image {n : ℕ} {P : Finset (Finset (Fin n))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (π : Equiv.Perm (Fin n)) :
    IsPartitionOfType (P.image (Finset.image π)) sizes := by
  obtain ⟨hne, hdisj, hcov, hcard⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    exact (hne B₀ hB₀).image π
  · intro B hB B' hB' hne'
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨B₀', hB₀', rfl⟩ := Finset.mem_image.mp hB'
    have hne₀ : B₀ ≠ B₀' := fun h => hne' (by rw [h])
    exact (Finset.disjoint_image π.injective).mpr (hdisj B₀ hB₀ B₀' hB₀' hne₀)
  · have : (P.image (Finset.image π)).biUnion id = Finset.image π (P.biUnion id) := by
      rw [Finset.image_biUnion, Finset.biUnion_image]
      rfl
    rw [this, hcov]
    exact Finset.image_univ_of_surjective π.surjective
  · have hinj : Function.Injective (Finset.image π) := Finset.image_injective π.injective
    rw [Finset.image_val_of_injOn hinj.injOn, Multiset.map_map, ← hcard]
    apply Multiset.map_congr rfl
    intro B _
    exact Finset.card_image_of_injective _ π.injective

@[expose] def ya7MkP (t ti : List (Fin 7)) (h1 : ∀ x : Fin 7, ti.getD (t.getD x.val 0).val 0 = x)
    (h2 : ∀ x : Fin 7, t.getD (ti.getD x.val 0).val 0 = x) : Equiv.Perm (Fin 7) :=
  ⟨fun x => t.getD x.val 0, fun x => ti.getD x.val 0, h1, h2⟩

@[expose] def ya7E : Fin 8 → Equiv.Perm (Fin 7)
  | 0 => ya7MkP [0,1,2,3,4,5,6] [0,1,2,3,4,5,6] (by decide) (by decide)
  | 1 => ya7MkP [1,0,2,3,5,4,6] [1,0,2,3,5,4,6] (by decide) (by decide)
  | 2 => ya7MkP [0,1,3,2,5,4,6] [0,1,3,2,5,4,6] (by decide) (by decide)
  | 3 => ya7MkP [1,0,3,2,4,5,6] [1,0,3,2,4,5,6] (by decide) (by decide)
  | 4 => ya7MkP [2,3,0,1,4,5,6] [2,3,0,1,4,5,6] (by decide) (by decide)
  | 5 => ya7MkP [3,2,1,0,4,5,6] [3,2,1,0,4,5,6] (by decide) (by decide)
  | 6 => ya7MkP [2,3,1,0,5,4,6] [3,2,0,1,5,4,6] (by decide) (by decide)
  | 7 => ya7MkP [3,2,0,1,5,4,6] [2,3,1,0,5,4,6] (by decide) (by decide)

@[expose] def ya7P0 : Finset (Finset (Fin 7)) := {{0, 1}, {2, 3}, {4, 5}, {6}}

@[expose] def ya7Sigma0 : Equiv.Perm (Fin 7) :=
  ya7MkP [4,5,2,3,0,1,6] [4,5,2,3,0,1,6] (by decide) (by decide)

theorem ya7P0_type : IsPartitionOfType ya7P0 {2, 2, 2, 1} := by
  unfold IsPartitionOfType ya7P0; decide +kernel

theorem ya7E_mul : ∀ i j : Fin 8, ∃ k : Fin 8, ya7E i * ya7E j = ya7E k := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7E_inv : ∀ i : Fin 8, ∃ k : Fin 8, (ya7E i)⁻¹ = ya7E k := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7E_zero : ya7E 0 = 1 := by unfold ya7E ya7MkP; decide +kernel

theorem ya7E_inj : ∀ i j : Fin 8, ya7E i = ya7E j → i = j := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7E_sign : ∀ i : Fin 8, Equiv.Perm.sign (ya7E i) = 1 := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7E_stab : ∀ i : Fin 8, StabilizesPartition (ya7E i) ya7P0 := by
  unfold ya7E ya7MkP StabilizesPartition ya7P0; decide +kernel

theorem ya7_fixed_pair : ∀ s : Finset (Fin 7), s.card = 2 →
    (∀ i : Fin 8, s.image (ya7E i) = s) → s = {4, 5} := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7Sigma0_sign : Equiv.Perm.sign ya7Sigma0 = 1 := by unfold ya7Sigma0 ya7MkP; decide +kernel

theorem ya7Sigma0_stab : StabilizesPartition ya7Sigma0 ya7P0 := by
  unfold ya7Sigma0 ya7MkP StabilizesPartition ya7P0; decide +kernel

theorem ya7Sigma0_move : ({4, 5} : Finset (Fin 7)).image ya7Sigma0 ≠ {4, 5} := by
  unfold ya7Sigma0 ya7MkP; decide +kernel

@[expose] def ya7D0Perm : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := Set.range ya7E
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := ya7E_mul i j
    exact ⟨k, hk.symm⟩
  one_mem' := ⟨0, ya7E_zero⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := ya7E_inv i
    exact ⟨k, hk.symm⟩

@[expose] def ya7D0 : Subgroup (alternatingGroup (Fin 7)) :=
  ya7D0Perm.subgroupOf (alternatingGroup (Fin 7))

theorem ya7D0Perm_le : ya7D0Perm ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨i, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)

theorem ya7D0_card : Nat.card ↥ya7D0 = 8 := by
  rw [ya7D0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe ya7D0Perm_le).toEquiv]
  have h : Nat.card ↥ya7D0Perm = Nat.card (Fin 8) :=
    Nat.card_range_of_injective (fun i j hij => ya7E_inj i j hij)
  rw [h]
  simp

theorem ya7D0_sylow : IsSylowTwoOf ya7D0 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [ya7D0_card]; norm_num), ?_⟩
  have h1 : (ya7D0.subgroupOf ⊤).index = ya7D0.index := Subgroup.relIndex_top_right ya7D0
  have h2 := Subgroup.card_mul_index ya7D0
  rw [ya7D0_card, nat_card_alternatingGroup (α := Fin 7)] at h2
  have h3 : (Nat.card (Fin 7)).factorial / 2 = 2520 := by
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  rw [h3] at h2
  rw [h1]
  omega

theorem ya7_partition_data (D : Subgroup (alternatingGroup (Fin 7))) (hD : IsSylowTwoOf D ⊤)
    (s : Finset (Fin 7)) (hs : s.card = 2)
    (hDs : ∀ d ∈ D, s.image (d : Equiv.Perm (Fin 7)) = s) :
    ∃ P : Finset (Finset (Fin 7)), IsPartitionOfType P {2, 2, 2, 1} ∧ s ∈ P ∧
      (∀ d ∈ D, StabilizesPartition (d : Equiv.Perm (Fin 7)) P) ∧
      ∃ σ : alternatingGroup (Fin 7), StabilizesPartition (σ : Equiv.Perm (Fin 7)) P ∧
        s.image (σ : Equiv.Perm (Fin 7)) ≠ s := by
  obtain ⟨h, -, hDh⟩ := IsSylowTwoOf.exists_conj ya7D0_sylow hD
  set g : Equiv.Perm (Fin 7) := (h : Equiv.Perm (Fin 7)) with hg
  set gi : Equiv.Perm (Fin 7) := g⁻¹ with hgi
  have hmemD : ∀ i : Fin 8, (h * (⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩ :
      alternatingGroup (Fin 7)) * h⁻¹ : alternatingGroup (Fin 7)) ∈ D := by
    intro i
    rw [hDh]
    refine Subgroup.mem_map.mpr ⟨⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨i, rfl⟩
    · simp [MulAut.conj_apply]
  have hfix : ∀ i : Fin 8, (s.image gi).image (ya7E i) = s.image gi := by
    intro i
    have hd := hDs _ (hmemD i)
    have hcoe : ((h * (⟨ya7E i, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign i)⟩ :
        alternatingGroup (Fin 7)) * h⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          g * ya7E i * gi := rfl
    rw [hcoe] at hd
    calc (s.image gi).image (ya7E i) = (s.image (g * ya7E i * gi)).image gi := by
          rw [Finset.image_image, Finset.image_image]
          congr 1
          funext x
          simp [hgi]
      _ = s.image gi := by rw [hd]
  have hcard' : (s.image gi).card = 2 := by
    rw [Finset.card_image_of_injective _ gi.injective, hs]
  have hs45 : s.image gi = {4, 5} := ya7_fixed_pair _ hcard' hfix
  have hsg : s = ({4, 5} : Finset (Fin 7)).image g := by
    rw [← hs45, Finset.image_image]
    ext x
    simp [hgi]
  refine ⟨ya7P0.image (Finset.image g), ya7_isPartitionOfType_image ya7P0_type g, ?_, ?_, ?_⟩
  · rw [hsg]
    exact Finset.mem_image_of_mem _ (by decide : ({4, 5} : Finset (Fin 7)) ∈ ya7P0)
  · intro d hd
    rw [hDh] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨i, hi⟩ := Subgroup.mem_subgroupOf.mp hd₀
    have hcoe : (((MulEquiv.toMonoidHom (MulAut.conj h)) d₀ : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) = g * (d₀ : Equiv.Perm (Fin 7)) * gi := rfl
    rw [hcoe, ← hi]
    exact ya7_stab_conj g (ya7E_stab i)
  · refine ⟨h * ⟨ya7Sigma0, Equiv.Perm.mem_alternatingGroup.mpr ya7Sigma0_sign⟩ * h⁻¹, ?_, ?_⟩
    · exact ya7_stab_conj g ya7Sigma0_stab
    · intro heq
      have hcoe : ((h * (⟨ya7Sigma0, Equiv.Perm.mem_alternatingGroup.mpr ya7Sigma0_sign⟩ :
          alternatingGroup (Fin 7)) * h⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
            g * ya7Sigma0 * gi := rfl
      rw [hcoe] at heq
      apply ya7Sigma0_move
      apply Finset.image_injective g.injective
      have h1 : (({4, 5} : Finset (Fin 7)).image ya7Sigma0).image g =
          (({4, 5} : Finset (Fin 7)).image g).image (g * ya7Sigma0 * gi) := by
        rw [Finset.image_image, Finset.image_image]
        congr 1
        funext x
        simp [hgi]
      rw [h1, ← hsg, heq]

@[expose] def ya7Supp (v : ↥(evenWeight 7)) : Finset (Fin 7) :=
  Finset.univ.filter fun i => (v : Fin 7 → ZMod 2) i ≠ 0

theorem ya7_permWeight_eq_iff (σ : Equiv.Perm (Fin 7)) (v : ↥(evenWeight 7)) :
    permWeight 7 σ v = v ↔ (ya7Supp v).image σ = ya7Supp v := by
  have hz : ∀ a b : ZMod 2, a = b ↔ (a ≠ 0 ↔ b ≠ 0) := by decide
  rw [Subtype.ext_iff]
  show (fun i => (v : Fin 7 → ZMod 2) (σ⁻¹ i)) = (v : Fin 7 → ZMod 2) ↔ _
  rw [funext_iff]
  simp only [hz]
  constructor
  · intro h
    ext i
    simp only [ya7Supp, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have := h (σ a)
      simpa using this.mp (by simpa using ha)
    · intro hi
      exact ⟨σ⁻¹ i, (h i).mpr hi, by simp⟩
  · intro hsup i
    have hi : i ∈ (ya7Supp v).image σ ↔ i ∈ ya7Supp v := by rw [hsup]
    simp only [ya7Supp, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    constructor
    · intro h
      exact hi.mp ⟨σ⁻¹ i, h, by simp⟩
    · intro h
      obtain ⟨a, ha, rfl⟩ := hi.mpr h
      simpa using ha

theorem ya7_mem_stabilizer_iff (v : ↥(evenWeight 7)) (σ : alternatingGroup (Fin 7)) :
    σ ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) (↑(ya7Supp v) : Set (Fin 7)) ↔
      permWeight 7 (σ : Equiv.Perm (Fin 7)) v = v := by
  rw [ya7_permWeight_eq_iff, MulAction.mem_stabilizer_iff]
  have : σ • (↑(ya7Supp v) : Set (Fin 7)) =
      ↑((ya7Supp v).image (σ : Equiv.Perm (Fin 7))) := by
    rw [Finset.coe_image, ← Set.image_smul]
    rfl
  rw [this, Finset.coe_inj]

theorem ya7_isCoatom_stabilizer (v : ↥(evenWeight 7)) (hv : HasWeightTwo (v : Fin 7 → ZMod 2)) :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 7)) (↑(ya7Supp v) : Set (Fin 7))) := by
  have hcard : (ya7Supp v).card = 2 := hv
  have hncard : (↑(ya7Supp v) : Set (Fin 7)).ncard = 2 := by
    rw [Set.ncard_coe_finset, hcard]
  have hsum := Set.ncard_add_ncard_compl (↑(ya7Supp v) : Set (Fin 7))
  rw [hncard, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  refine alternatingGroup.isCoatom_stabilizer ?_ ?_ ?_
  · exact Finset.coe_nonempty.mpr (Finset.card_pos.mp (by rw [hcard]; norm_num))
  · refine Set.nonempty_of_ncard_ne_zero ?_
    omega
  · rw [hncard, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num

theorem ya7_eq_top_of_stab_le (v : ↥(evenWeight 7)) (hv : HasWeightTwo (v : Fin 7 → ZMod 2))
    (K : Subgroup (alternatingGroup (Fin 7)))
    (h1 : ∀ σ : alternatingGroup (Fin 7), permWeight 7 (σ : Equiv.Perm (Fin 7)) v = v → σ ∈ K)
    (h2 : ∃ τ ∈ K, permWeight 7 (τ : Equiv.Perm (Fin 7)) v ≠ v) : K = ⊤ := by
  have hc := ya7_isCoatom_stabilizer v hv
  have hle : MulAction.stabilizer (alternatingGroup (Fin 7)) (↑(ya7Supp v) : Set (Fin 7)) ≤ K :=
    fun σ hσ => h1 σ ((ya7_mem_stabilizer_iff v σ).mp hσ)
  obtain ⟨τ, hτK, hτ⟩ := h2
  refine hc.2 K (lt_of_le_of_ne hle ?_)
  intro heq
  exact hτ ((ya7_mem_stabilizer_iff v τ).mp (heq ▸ hτK))

end CFSG.Quasithin
