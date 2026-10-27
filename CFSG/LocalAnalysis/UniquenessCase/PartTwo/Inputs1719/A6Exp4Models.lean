module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AltPerm
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18HS
public import CFSG.Quasithin.EmptyFaithful.T1531In68b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Equiv CFSG.QuasithinUnique.Setup.X3 CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_relStab_blkX6 : Nat.card ↥(relStab blkX6) = 48 := by
  have h : Fintype.card {σ : Perm (Fin 6) // σ ∈ relStab blkX6} = 48 := by decide +kernel
  rw [Nat.card_eq_fintype_card]
  exact h

theorem card_relStab_blkY6 : Nat.card ↥(relStab blkY6) = 48 := by
  have h : Fintype.card {σ : Perm (Fin 6) // σ ∈ relStab blkY6} = 48 := by decide +kernel
  rw [Nat.card_eq_fintype_card]
  exact h

theorem relStab_blkX6_not_le_normalizer :
    ¬ relStab blkX6 ≤ Subgroup.normalizer ((relStab blkX6 ⊓ relStab blkY6 :
      Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
  intro h
  have hg : (swap (0 : Fin 6) 1 * swap 0 2 : Perm (Fin 6)) ∈ relStab blkX6 := by decide +kernel
  have hu : swap (0 : Fin 6) 1 ∈ relStab blkX6 ⊓ relStab blkY6 :=
    Subgroup.mem_inf.2 ⟨by decide +kernel, by decide +kernel⟩
  have hc := (Subgroup.mem_normalizer_iff.1 (h hg) _).1 hu
  rw [Subgroup.mem_inf] at hc
  revert hc
  decide +kernel

theorem relStab_blkY6_not_le_normalizer :
    ¬ relStab blkY6 ≤ Subgroup.normalizer ((relStab blkX6 ⊓ relStab blkY6 :
      Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
  intro h
  have hg : (swap (0 : Fin 6) 4 * swap 0 2 * (swap 1 5 * swap 1 3) : Perm (Fin 6)) ∈
      relStab blkY6 := by decide +kernel
  have hu : (swap (0 : Fin 6) 2 * swap 1 3 : Perm (Fin 6)) ∈ relStab blkX6 ⊓ relStab blkY6 :=
    Subgroup.mem_inf.2 ⟨by decide +kernel, by decide +kernel⟩
  have hc := (Subgroup.mem_normalizer_iff.1 (h hg) _).1 hu
  rw [Subgroup.mem_inf] at hc
  revert hc
  decide +kernel

@[expose] def IsSThreeOver {Y : Type*} [Group Y] (S Q : Subgroup Y) : Prop :=
  S ≤ Q ∧ Nat.card Q = 3 * Nat.card S ∧ ¬ Q ≤ Subgroup.normalizer (S : Set Y)

theorem IsSThreeOver.bar2 {Y : Type} [Group Y] [Finite Y] {S Q : Subgroup Y}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (h : IsSThreeOver S Q) :
    Nonempty (Bar2 Q ≃* Perm (Fin 3)) := by
  obtain ⟨hSQ, hc, hN⟩ := h
  have hS0 : 0 < Nat.card S := Nat.card_pos
  have h3 : S.relIndex Q = 3 := by
    have h := Subgroup.relIndex_mul_card S Q
    rw [inf_eq_left.2 hSQ, hc] at h
    exact Nat.eq_of_mul_eq_mul_right hS0 h
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf S Q :=
    ⟨hSQ, hS.2.1, by
      rw [show (S.subgroupOf Q).index = S.relIndex Q from rfl, h3]
      norm_num⟩
  obtain ⟨φ⟩ := CFSG.Quasithin.nonempty_quotient_pCore_of_relIndex_eq_three' hsyl h3 hN
  exact ⟨φ⟩

theorem exists_sThree_pair_of_iso {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) {Γ : Type} [Group Γ] [Finite Γ] (e : Y ≃* Γ)
    {U P₀ P₁ : Subgroup Γ} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (h₀ : IsSThreeOver U P₀) (h₁ : IsSThreeOver U P₁) (hgen : P₀ ⊔ P₁ = ⊤) :
    ∃ Q₀ Q₁ : Subgroup Y, IsSThreeOver S Q₀ ∧ IsSThreeOver S Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ := by
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.Stellmacher.L3YC.Row18.exists_equiv_sylow hU e hS
  have hcU : Nat.card U = Nat.card S := by
    rw [← hψ, Subgroup.card_map_of_injective ψ.injective]
  have hmemU : ∀ x : Γ, x ∈ U ↔ ψ.symm x ∈ S := fun x => by
    rw [← hψ, Subgroup.mem_map_equiv]
  have key : ∀ P : Subgroup Γ, IsSThreeOver U P →
      IsSThreeOver S (P.map ψ.symm.toMonoidHom) := by
    rintro P ⟨hUP, hc, hn⟩
    refine ⟨fun s hs => ⟨ψ s, hUP ((hmemU _).2 (by simpa using hs)), by simp⟩, ?_,
      fun hle => hn fun p hp => ?_⟩
    · rw [Subgroup.card_map_of_injective ψ.symm.injective, hc, hcU]
    · have hq : ψ.symm p ∈ Subgroup.normalizer (S : Set Y) := hle ⟨p, hp, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro u
      rw [hmemU, hmemU, map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.1 hq _
  refine ⟨_, _, key P₀ h₀, key P₁ h₁, ?_⟩
  rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ ψ.symm.surjective]

theorem isSylowTwoOf_inf_blk6 :
    CFSG.QuasithinUnique.IsSylowTwoOf (relStab blkX6 ⊓ relStab blkY6)
      (⊤ : Subgroup (Perm (Fin 6))) := by
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [card6]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index (relStab blkX6 ⊓ relStab blkY6)
  rw [card6, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : (relStab blkX6 ⊓ relStab blkY6).index = 45 := by
    have h720 : Nat.factorial 6 = 720 := rfl
    omega
  rw [show ((relStab blkX6 ⊓ relStab blkY6).subgroupOf ⊤).index =
    (relStab blkX6 ⊓ relStab blkY6).index from Subgroup.relIndex_top_right _, h2]
  decide

theorem exists_sThree_pair_of_perm_six {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (e : Y ≃* Perm (Fin 6)) :
    ∃ Q₀ Q₁ : Subgroup Y, IsSThreeOver S Q₀ ∧ IsSThreeOver S Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ :=
  exists_sThree_pair_of_iso hS e isSylowTwoOf_inf_blk6
    ⟨inf_le_left, by rw [card_relStab_blkX6, card6], relStab_blkX6_not_le_normalizer⟩
    ⟨inf_le_right, by rw [card_relStab_blkY6, card6], relStab_blkY6_not_le_normalizer⟩ sup6

theorem card_subgroupOf_alt_six {H : Subgroup (Perm (Fin 6))} (hH : swap (0 : Fin 6) 1 ∈ H) :
    2 * Nat.card ↥(H.subgroupOf (alternatingGroup (Fin 6))) = Nat.card H := by
  rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
    Subgroup.subgroupOf_map_subtype,
    card_eq_two_mul_card_inf_alt hH (Perm.sign_swap (by decide))]

theorem isSylowTwoOf_inf_blk6_alt :
    CFSG.QuasithinUnique.IsSylowTwoOf ((relStab blkX6 ⊓ relStab blkY6).subgroupOf
      (alternatingGroup (Fin 6))) ⊤ := by
  have hc := card_subgroupOf_alt_six (H := relStab blkX6 ⊓ relStab blkY6)
    (Subgroup.mem_inf.2 ⟨by decide +kernel, by decide +kernel⟩)
  rw [card6] at hc
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by norm_num; omega), ?_⟩
  have h1 := Subgroup.card_mul_index ((relStab blkX6 ⊓ relStab blkY6).subgroupOf
    (alternatingGroup (Fin 6)))
  have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h8 : Nat.card ↥((relStab blkX6 ⊓ relStab blkY6).subgroupOf (alternatingGroup (Fin 6))) =
      8 := by
    omega
  rw [hA, h8] at h1
  have h2 : ((relStab blkX6 ⊓ relStab blkY6).subgroupOf (alternatingGroup (Fin 6))).index = 45 := by
    omega
  rw [show (((relStab blkX6 ⊓ relStab blkY6).subgroupOf (alternatingGroup (Fin 6))).subgroupOf
      ⊤).index = ((relStab blkX6 ⊓ relStab blkY6).subgroupOf (alternatingGroup (Fin 6))).index
      from Subgroup.relIndex_top_right _, h2]
  decide

theorem sup6_alt : (relStab blkX6).subgroupOf (alternatingGroup (Fin 6)) ⊔
    (relStab blkY6).subgroupOf (alternatingGroup (Fin 6)) = ⊤ := by
  have h := alt_le_sup_of_common_odd (s := swap (0 : Fin 6) 1) (f := swap 0 1 * swap 0 2)
    (by decide +kernel) (by decide +kernel) (Perm.sign_swap (by decide)) sup6
    (by simp) (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))
    (by decide +kernel)
  rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective
    (alternatingGroup (Fin 6)).subtype_injective, Subgroup.map_sup,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact h

theorem relStab_blkX6_alt_not_le_normalizer :
    ¬ (relStab blkX6).subgroupOf (alternatingGroup (Fin 6)) ≤ Subgroup.normalizer
      (((relStab blkX6 ⊓ relStab blkY6).subgroupOf (alternatingGroup (Fin 6)) :
        Subgroup ↥(alternatingGroup (Fin 6))) : Set ↥(alternatingGroup (Fin 6))) := by
  intro h
  have hgA : (swap (0 : Fin 6) 1 * swap 0 2 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
    mem_alt_swap_mul_swap (by decide) (by decide)
  have huA : (swap (0 : Fin 6) 1 * swap 4 5 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
    mem_alt_swap_mul_swap (by decide) (by decide)
  have hgX : (swap (0 : Fin 6) 1 * swap 0 2 : Perm (Fin 6)) ∈ relStab blkX6 := by decide +kernel
  have huU : (swap (0 : Fin 6) 1 * swap 4 5 : Perm (Fin 6)) ∈ relStab blkX6 ⊓ relStab blkY6 :=
    Subgroup.mem_inf.2 ⟨by decide +kernel, by decide +kernel⟩
  have hbad : ¬ ((swap (0 : Fin 6) 1 * swap 0 2) * (swap 0 1 * swap 4 5) *
      (swap (0 : Fin 6) 1 * swap 0 2)⁻¹ : Perm (Fin 6)) ∈ relStab blkX6 ⊓ relStab blkY6 := by
    rw [Subgroup.mem_inf]
    decide +kernel
  have hn := @h ⟨_, hgA⟩ (Subgroup.mem_subgroupOf.2 hgX)
  rw [Subgroup.mem_normalizer_iff] at hn
  have hc := (hn ⟨_, huA⟩).1 (Subgroup.mem_subgroupOf.2 huU)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hc
  exact hbad hc

theorem relStab_blkY6_alt_not_le_normalizer :
    ¬ (relStab blkY6).subgroupOf (alternatingGroup (Fin 6)) ≤ Subgroup.normalizer
      (((relStab blkX6 ⊓ relStab blkY6).subgroupOf (alternatingGroup (Fin 6)) :
        Subgroup ↥(alternatingGroup (Fin 6))) : Set ↥(alternatingGroup (Fin 6))) := by
  intro h
  have hgA : (swap (0 : Fin 6) 4 * swap 0 2 * (swap 1 5 * swap 1 3) : Perm (Fin 6)) ∈
      alternatingGroup (Fin 6) :=
    (alternatingGroup (Fin 6)).mul_mem (mem_alt_swap_mul_swap (by decide) (by decide))
      (mem_alt_swap_mul_swap (by decide) (by decide))
  have huA : (swap (0 : Fin 6) 2 * swap 1 3 : Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
    mem_alt_swap_mul_swap (by decide) (by decide)
  have hgY : (swap (0 : Fin 6) 4 * swap 0 2 * (swap 1 5 * swap 1 3) : Perm (Fin 6)) ∈
      relStab blkY6 := by decide +kernel
  have huU : (swap (0 : Fin 6) 2 * swap 1 3 : Perm (Fin 6)) ∈ relStab blkX6 ⊓ relStab blkY6 :=
    Subgroup.mem_inf.2 ⟨by decide +kernel, by decide +kernel⟩
  have hbad : ¬ ((swap (0 : Fin 6) 4 * swap 0 2 * (swap 1 5 * swap 1 3)) * (swap 0 2 * swap 1 3) *
      (swap (0 : Fin 6) 4 * swap 0 2 * (swap 1 5 * swap 1 3))⁻¹ : Perm (Fin 6)) ∈
      relStab blkX6 ⊓ relStab blkY6 := by
    rw [Subgroup.mem_inf]
    decide +kernel
  have hn := @h ⟨_, hgA⟩ (Subgroup.mem_subgroupOf.2 hgY)
  rw [Subgroup.mem_normalizer_iff] at hn
  have hc := (hn ⟨_, huA⟩).1 (Subgroup.mem_subgroupOf.2 huU)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hc
  exact hbad hc

theorem exists_sThree_pair_of_alt_six {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (e : Y ≃* ↥(alternatingGroup (Fin 6))) :
    ∃ Q₀ Q₁ : Subgroup Y, IsSThreeOver S Q₀ ∧ IsSThreeOver S Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ := by
  have hU := card_subgroupOf_alt_six (H := relStab blkX6 ⊓ relStab blkY6)
    (Subgroup.mem_inf.2 ⟨by decide +kernel, by decide +kernel⟩)
  have hX := card_subgroupOf_alt_six (H := relStab blkX6) (by decide +kernel)
  have hY := card_subgroupOf_alt_six (H := relStab blkY6) (by decide +kernel)
  rw [card6] at hU
  rw [card_relStab_blkX6] at hX
  rw [card_relStab_blkY6] at hY
  exact exists_sThree_pair_of_iso hS e isSylowTwoOf_inf_blk6_alt
    ⟨fun x hx => (Subgroup.mem_subgroupOf.1 hx).1, by omega, relStab_blkX6_alt_not_le_normalizer⟩
    ⟨fun x hx => (Subgroup.mem_subgroupOf.1 hx).2, by omega, relStab_blkY6_alt_not_le_normalizer⟩
    sup6_alt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
