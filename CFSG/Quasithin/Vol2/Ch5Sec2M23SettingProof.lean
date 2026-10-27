module

import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Setting

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def m23T0List : List (Equiv.Perm (Fin 7)) :=
  [1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 5 6,
    Equiv.swap 2 3 * Equiv.swap 5 6,
    Equiv.swap 0 1 * Equiv.swap 5 6 * (Equiv.swap 0 2 * Equiv.swap 1 3),
    Equiv.swap 0 1 * Equiv.swap 5 6 * (Equiv.swap 0 3 * Equiv.swap 1 2)]

theorem m23T0List_mul : ∀ σ ∈ m23T0List, ∀ τ ∈ m23T0List, σ * τ ∈ m23T0List := by
  intro σ hσ τ hτ
  simp only [m23T0List, List.mem_cons, List.not_mem_nil, or_false] at hσ hτ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem m23T0List_inv : ∀ σ ∈ m23T0List, σ⁻¹ ∈ m23T0List := by
  intro σ hσ
  simp only [m23T0List, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem m23T0List_alt : ∀ σ ∈ m23T0List, σ ∈ alternatingGroup (Fin 7) := by
  intro σ hσ
  simp only [m23T0List, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem m23T0List_nodup : m23T0List.Nodup := by decide +kernel

theorem m23T0List_orbits :
    ∀ i j : Fin 7, (∃ σ ∈ m23T0List, σ i = j) ↔ omegaTOrbit i = omegaTOrbit j := by
  decide +kernel

@[expose] def m23T0 : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := {σ | σ ∈ m23T0List}
  mul_mem' := fun {a b} ha hb => m23T0List_mul a ha b hb
  one_mem' := by
    show (1 : Equiv.Perm (Fin 7)) ∈ m23T0List
    decide +kernel
  inv_mem' := fun {a} ha => m23T0List_inv a ha

theorem card_m23T0 : Nat.card m23T0 = 8 := by
  have h : (m23T0 : Set (Equiv.Perm (Fin 7))) = ↑m23T0List.toFinset := by
    ext σ
    simp [m23T0]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup m23T0List_nodup]
  rfl

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_perm, Nat.card_fin] at h
  have : (7 : ℕ).factorial = 5040 := by decide
  omega

@[expose] noncomputable def m23T0Sylow : Sylow 2 (alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (IsPGroup.of_card (n := 3) (G := m23T0.subgroupOf (alternatingGroup (Fin 7))) ?_).toSylow
    ?_
  · rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← card_m23T0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun σ hσ => m23T0List_alt σ hσ).toEquiv
  · intro h2
    have hc := Subgroup.card_mul_index (m23T0.subgroupOf (alternatingGroup (Fin 7)))
    have h8 : Nat.card (m23T0.subgroupOf (alternatingGroup (Fin 7))) = 8 := by
      rw [← card_m23T0]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun σ hσ => m23T0List_alt σ hσ).toEquiv
    rw [h8, card_alternatingGroup_seven] at hc
    omega

@[expose] def Stmt5_2_11_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (K' : Subgroup G),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T → oTwoUpper H < K' →
    quasithinIsMaximalLocal T K' → CFSG.Quasithin.IsExcA7Block K' → InM T K'

theorem stmt5_2_10_setting_of (h528 : Stmt5_2_8) (h5211 : Stmt5_2_11_four) :
    Stmt5_2_10_setting := by
  intro G _ _ T M L V H B D L₂ n hyp hM23
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h528 G T M L V H B D L₂ n hyp with hK | ⟨-, K', hKK', hmax, hexc⟩
  · exact absurd hK hM23.2
  have hTK : T ≤ K' := (h5211 G T M L V H B D L₂ n K' hyp hM23 hKK' hmax hexc).2
  obtain ⟨hshort, ⟨α, hαs, hαk⟩, hidx⟩ := hexc
  have hTs : IsSylowTwoOf T K' := isSylowTwoOf_of_isSylowTwo hyp.sylow hTK
  have hTK2 : IsPGroup 2 (T.subgroupOf K') :=
    hTs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  set PT : Sylow 2 ↥K' := hTK2.toSylow hTs.2.2 with hPT
  set P := PT.mapSurjective hαs with hP
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) P m23T0Sylow
  set π : ↥K' →* Equiv.Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp ((MulAut.conj c).toMonoidHom.comp α) with hπ
  have hπapp : ∀ g : ↥K', π g = ((c * α g * c⁻¹ : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) := fun g => rfl
  refine ⟨K', π, ⟨hKK', hmax, ⟨hshort, ⟨α, hαs, hαk⟩, hidx⟩, hTK, ?_, ?_, ?_⟩⟩
  ·
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact (c * α g * c⁻¹).2
    · intro hσ
      obtain ⟨g, hg⟩ := hαs (c⁻¹ * ⟨σ, hσ⟩ * c)
      refine ⟨g, ?_⟩
      rw [hπapp, hg]
      simp [mul_assoc]
  ·
    ext g
    rw [MonoidHom.mem_ker, hπapp]
    have hk : g ∈ α.ker ↔ g ∈ (pCoreOf 2 K').subgroupOf K' := by
      rw [hαk, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨g', hg', hgg'⟩ => (Subtype.ext hgg' : g' = g) ▸ hg'⟩
    rw [← hk, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : c * α g * c⁻¹ = 1 := Subtype.ext h
      have : α g = 1 := by
        have := congrArg (fun x => c⁻¹ * x * c) h'
        simpa [mul_assoc] using this
      exact this
    · intro h
      rw [h]
      simp
  ·
    intro i j
    rw [← m23T0List_orbits]
    constructor
    · rintro ⟨g, hgT, hgij⟩
      refine ⟨π g, ?_, hgij⟩
      have hmem : c * α g * c⁻¹ ∈ (m23T0Sylow : Subgroup (alternatingGroup (Fin 7))) := by
        rw [← hc, Sylow.coe_subgroup_smul]
        refine Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨α g, ?_, ?_⟩
        · rw [hP, Sylow.coe_mapSurjective]
          exact ⟨g, (show g ∈ (PT : Subgroup ↥K') from hgT), rfl⟩
        · simp [MulAut.smul_def]
      exact hmem
    · rintro ⟨σ, hσ, hσij⟩
      have hσA : σ ∈ alternatingGroup (Fin 7) := m23T0List_alt σ hσ
      have hmem : (⟨σ, hσA⟩ : alternatingGroup (Fin 7)) ∈
          (m23T0Sylow : Subgroup (alternatingGroup (Fin 7))) := hσ
      rw [← hc, Sylow.coe_subgroup_smul] at hmem
      obtain ⟨τ, hτ, hτσ⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hmem
      rw [hP, Sylow.coe_mapSurjective] at hτ
      obtain ⟨g, hgT, rfl⟩ := hτ
      refine ⟨g, hgT, ?_⟩
      rw [hπapp]
      have : c * α g * c⁻¹ = ⟨σ, hσA⟩ := by
        rw [← hτσ]
        simp [MulAut.smul_def]
      rw [this]
      exact hσij

end CFSG.Quasithin.H13
