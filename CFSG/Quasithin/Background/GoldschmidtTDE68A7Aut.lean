module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Cent
public import CFSG.Quasithin.Background.GoldschmidtTDE68Ind
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.E6.Alt.A7

open Equiv Equiv.Perm CFSG.Quasithin.E6.Bar

abbrev G7 : Type := ↥(alternatingGroup (Fin 7))

@[expose] noncomputable def cj : Perm (Fin 7) →* MulAut G7 := MulAut.conjNormal

theorem cj_bijective : Function.Bijective cj :=
  CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)

theorem cj_apply (σ : Perm (Fin 7)) (g : G7) : ((cj σ g : G7) : Perm (Fin 7)) = σ * g * σ⁻¹ :=
  MulAut.conjNormal_apply σ g

theorem conj_eq_cj (d : G7) : MulAut.conj d = cj (d : Perm (Fin 7)) := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [cj_apply]
  rfl

theorem cj_eq_one_iff (σ : Perm (Fin 7)) : cj σ = 1 ↔ σ = 1 := by
  rw [← map_one cj]
  exact cj_bijective.1.eq_iff

theorem cj_mem_invSet_iff (σ : Perm (Fin 7)) :
    cj σ ∈ InvSet D7q ↔ σ ≠ 1 ∧ σ * σ = 1 ∧ ∀ d ∈ D7, σ * d = d * σ := by
  unfold InvSet
  simp only [Set.mem_ofPred_eq]
  refine and_congr (not_congr (cj_eq_one_iff σ)) (and_congr ?_ ?_)
  · rw [← map_mul, ← cj_eq_one_iff]
  · constructor
    · intro h d hd
      have := h ⟨d, D7_le_alt hd⟩ hd
      rw [conj_eq_cj, ← map_mul, ← map_mul] at this
      exact cj_bijective.1 this
    · intro h d hd
      rw [conj_eq_cj, ← map_mul, ← map_mul]
      exact congrArg cj (h d hd)

theorem pa_ne_one : pa ≠ 1 := fun h => by
  have := congrArg toT h
  rw [toT_pa, toT_one] at this
  exact absurd this (by decide)

theorem pb_ne_one : pb ≠ 1 := fun h => by
  have := congrArg toT h
  rw [toT_pb, toT_one] at this
  exact absurd this (by decide)

theorem pa_mul_pa : pa * pa = 1 :=
  toT_injective (by rw [toT_mul, toT_pa, toT_one]; decide +kernel)

theorem pb_mul_pb : pb * pb = 1 :=
  toT_injective (by rw [toT_mul, toT_pb, toT_one]; decide +kernel)

theorem pa_mul_pb : pa * pb = pb * pa :=
  toT_injective (by rw [toT_mul, toT_mul, toT_pa, toT_pb]; decide +kernel)

theorem pab_ne_one : pa * pb ≠ 1 := fun h => by
  have := congrArg toT h
  rw [toT_mul, toT_pa, toT_pb, toT_one] at this
  exact absurd this (by decide +kernel)

theorem pab_mul_pab : (pa * pb) * (pa * pb) = 1 := by
  calc (pa * pb) * (pa * pb) = pa * (pb * pa) * pb := by group
    _ = pa * (pa * pb) * pb := by rw [pa_mul_pb]
    _ = (pa * pa) * (pb * pb) := by group
    _ = 1 := by rw [pa_mul_pa, pb_mul_pb, one_mul]

theorem pab_comm (d : Perm (Fin 7)) (hd : d ∈ D7) : (pa * pb) * d = d * (pa * pb) := by
  calc (pa * pb) * d = pa * (pb * d) := by group
    _ = pa * (d * pb) := by rw [pb_comm d hd]
    _ = (pa * d) * pb := by group
    _ = (d * pa) * pb := by rw [pa_comm d hd]
    _ = d * (pa * pb) := by group

theorem invSet_eq : InvSet D7q = {cj pa, cj pb, cj (pa * pb)} := by
  ext β
  obtain ⟨σ, rfl⟩ := cj_bijective.2 β
  rw [cj_mem_invSet_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, -, h3⟩
    rcases cent_D7 σ h3 with h | h | h | h
    · exact absurd h h1
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]))
  · rintro (h | h | h)
    · have := cj_bijective.1 h
      subst this
      exact ⟨pa_ne_one, pa_mul_pa, pa_comm⟩
    · have := cj_bijective.1 h
      subst this
      exact ⟨pb_ne_one, pb_mul_pb, pb_comm⟩
    · have := cj_bijective.1 h
      subst this
      exact ⟨pab_ne_one, pab_mul_pab, pab_comm⟩

theorem encard_invSet_le : (InvSet D7q).encard ≤ 3 := by
  rw [invSet_eq]
  calc ({cj pa, cj pb, cj (pa * pb)} : Set (MulAut G7)).encard
      ≤ ({cj pb, cj (pa * pb)} : Set (MulAut G7)).encard + 1 := Set.encard_insert_le _ _
    _ ≤ (({cj (pa * pb)} : Set (MulAut G7)).encard + 1) + 1 := by
        gcongr
        exact Set.encard_insert_le _ _
    _ = 3 := by
        rw [Set.encard_singleton]
        norm_num

end CFSG.Quasithin.E6.Alt.A7
