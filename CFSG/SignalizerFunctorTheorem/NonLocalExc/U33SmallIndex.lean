module

public import CFSG.GH74.KGroups.U33
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.SmallIndex
public import Certificates.Certificate14953

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

theorem mem_Bsub {g : Equiv.Perm (Fin 28)} :
    g ∈ Bsub ↔ g ∈ QP.originalSubgroup ∧ g 0 = 0 := by
  simp [Bsub, MulAction.mem_stabilizer_iff]

theorem cube_mul :
    ∀ x ∈ Bsub, ∀ y ∈ Bsub, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1 :=
  Certificates.certificate14953.2.1

@[expose] def Psub : Subgroup (Equiv.Perm (Fin 28)) where
  carrier := {g | g ∈ Bsub ∧ g ^ 3 = 1}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, cube_mul a ha.1 b hb.1 ha.2 hb.2⟩
  one_mem' := ⟨one_mem _, one_pow 3⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_Psub_iff_Bsub {g : Equiv.Perm (Fin 28)} :
    g ∈ Psub ↔ g ∈ Bsub ∧ g ^ 3 = 1 := Iff.rfl

theorem mem_Psub {g : Equiv.Perm (Fin 28)} :
    g ∈ Psub ↔ g ∈ QP.originalSubgroup ∧ g 0 = 0 ∧ g ^ 3 = 1 := by
  rw [mem_Psub_iff_Bsub, mem_Bsub, and_assoc]

theorem mem_Bl {g : Equiv.Perm (Fin 28)} :
    g ∈ Bl ↔ g ∈ QP.originalSubgroup ∧ g 0 = 0 := by
  simp [Bl, mem_elemsT QP QP_ok]

theorem mem_Pl {g : Equiv.Perm (Fin 28)} :
    g ∈ Pl ↔ g ∈ QP.originalSubgroup ∧ g 0 = 0 ∧ g ^ 3 = 1 := by
  simp [Pl, mem_Bl, and_assoc]

theorem Bl_norm :
    ∀ x ∈ Bl, ∀ p ∈ Pl, x * p * x⁻¹ ∈ Pl := by
  intro x hx p hp
  have hxB : x ∈ Bsub := mem_Bsub.2 (mem_Bl.1 hx)
  have hpP : p ∈ Psub := mem_Psub.2 (mem_Pl.1 hp)
  have hc : x * p * x⁻¹ ∈ Psub := ⟨mul_mem (mul_mem hxB hpP.1) (inv_mem hxB), by
    rw [conj_pow, hpP.2, mul_one, mul_inv_cancel]⟩
  exact mem_Pl.2 (mem_Psub.1 hc)

theorem card_Bsub : Nat.card Bsub = 216 :=
  Certificates.certificate14953.1

theorem card_Psub : Nat.card Psub = 27 :=
  Certificates.certificate14953.2.2.1

theorem Psub_le_Bsub : Psub ≤ Bsub := fun _ hg => hg.1

instance : Finite Bsub :=
  Nat.finite_of_card_ne_zero (by rw [card_Bsub]; norm_num)

theorem Bsub_le : Bsub ≤ QP.originalSubgroup :=
  fun _ hg => (mem_Bsub.1 hg).1

theorem exists_z_small_index :
    ∃ z : Equiv.Perm (Fin 28), z ∈ Psub ∧ z ≠ 1 ∧
    ∀ K : Subgroup (Equiv.Perm (Fin 28)), K ≤ Bsub → 14 < Nat.card K → z ∈ K := by
  obtain ⟨-, -, -, z, hzB, hz3, hz1, ⟨x0, hx0, y0, hy0, hx3, hy3, hzc⟩, hN⟩ :=
    Certificates.certificate14953
  refine ⟨z, ⟨hzB, hz3⟩, hz1, fun K hKB hK => ?_⟩
  by_contra hzK
  have hmain := card_le_fourteen_of_not_mem Bsub Psub Psub_le_Bsub
    (fun x hx p hp => ⟨mul_mem (mul_mem hx hp.1) (inv_mem hx), by
      rw [conj_pow, hp.2, mul_one, mul_inv_cancel]⟩) card_Psub card_Bsub
    (fun p hp => hp.2) ⟨x0, ⟨hx0, hx3⟩, y0, ⟨hy0, hy3⟩, hzc⟩ ?_ K hKB hzK
  · omega
  · intro a haP ha1 haz haz'
    have hfin : {x | x ∈ Bsub ∧ ¬ x ^ 3 = 1 ∧ (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹)}.Finite :=
      Set.toFinite _
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
      exact hN a haP.1 haP.2 ha1 haz haz'
    · intro x hx hxP hxa
      rw [Set.Finite.mem_toFinset]
      exact ⟨hx, fun h => hxP ⟨hx, h⟩, hxa⟩

theorem exists_z_action :
    ∃ z : ↥QP.originalSubgroup, z ≠ 1 ∧
    ∀ (Ψ : Type) [Finite Ψ], Nat.card Ψ ≤ 14 →
      ∀ β : ↥QP.originalSubgroup →* Equiv.Perm Ψ, β z = 1 := by
  obtain ⟨z, hzP, hz1, hz⟩ := exists_z_small_index
  have hzG : z ∈ QP.originalSubgroup := (mem_Psub.1 hzP).1
  refine ⟨⟨z, hzG⟩, fun h => hz1 (congrArg Subtype.val h), ?_⟩
  intro Ψ _ hΨ β
  by_contra hβ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, β ⟨z, hzG⟩ ψ ≠ ψ := by
    by_contra h
    push Not at h
    exact hβ (Equiv.ext h)
  set B' : Subgroup ↥QP.originalSubgroup := Bsub.subgroupOf QP.originalSubgroup with hB'
  let _ : MulAction B' Ψ := MulAction.compHom Ψ (β.comp B'.subtype)
  have hB'card : Nat.card B' = 216 := by
    rw [← card_Bsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Bsub_le).toEquiv
  set Kb : Subgroup B' := MulAction.stabilizer B' ψ with hKb
  have h1 := Subgroup.card_mul_index Kb
  have h2 : Kb.index = (MulAction.orbit B' ψ).ncard := MulAction.index_stabilizer B' ψ
  have h3 : (MulAction.orbit B' ψ).ncard ≤ Nat.card Ψ := Set.ncard_le_card _
  set K : Subgroup (Equiv.Perm (Fin 28)) :=
    (Kb.map B'.subtype).map QP.originalSubgroup.subtype with hK
  have hKcard : Nat.card K = Nat.card Kb := by
    rw [hK, Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective Subtype.val_injective]
  have hKB : K ≤ Bsub := by
    rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.1 b.2
  have hzK : z ∉ K := by
    rintro ⟨_, ⟨b, hb, rfl⟩, hbz⟩
    have hbz' : (b : ↥QP.originalSubgroup) = ⟨z, hzG⟩ := Subtype.ext hbz
    have : β ⟨z, hzG⟩ ψ = ψ := by
      rw [← hbz']
      exact hb
    exact hψ this
  have hbig : 14 < Nat.card K := by
    rw [hKcard]
    by_contra hle
    push Not at hle
    have hidx : Kb.index ≤ 14 := by omega
    have := Nat.mul_le_mul hle hidx
    omega
  exact hzK (hz K hKB hbig)

theorem action_eq_one_of_simple
    {G : Type*} [Group G] [IsSimpleGroup G] (e : G ≃* ↥QP.originalSubgroup) {Ψ : Type}
    [Finite Ψ] (hΨ : Nat.card Ψ ≤ 14) (α : G →* Equiv.Perm Ψ) : α = 1 := by
  obtain ⟨z, hz1, hz⟩ := exists_z_action
  have h := hz Ψ hΨ (α.comp e.symm.toMonoidHom)
  have hmem : e.symm z ∈ α.ker := by
    rw [MonoidHom.mem_ker]
    exact h
  have hne : e.symm z ≠ 1 := fun h1 => hz1 (by simpa using congrArg e h1)
  have hker : α.ker = ⊤ := by
    rcases (inferInstance : α.ker.Normal).eq_bot_or_eq_top with h0 | h0
    · rw [h0, Subgroup.mem_bot] at hmem
      exact absurd hmem hne
    · exact h0
  refine MonoidHom.ext fun g => ?_
  have : g ∈ α.ker := hker ▸ Subgroup.mem_top g
  rw [MonoidHom.one_apply]
  exact MonoidHom.mem_ker.1 this

end CFSG.SignalizerFunctorTheorem.NonLocalExc
