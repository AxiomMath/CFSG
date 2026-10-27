
module

public import CFSG.Monster.B.Fischer.Fi22CentralizerBase1

public import CFSG.Monster.B.Fischer.Fi22Cover
public import CFSG.Monster.B.Fischer.Fi22CentralizerBase

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem fi22OuterZ_mem_P :
    fi22OuterZ ∈ fi22P :=
  fi22OuterXRep_two ▸ (fi22OuterXRep_spec (i := 2) (by norm_num)).1

theorem orderOf_fi22OuterZ :
    orderOf fi22OuterZ = 2 :=
  fi22OuterXRep_two ▸ (fi22OuterXRep_spec (i := 2) (by norm_num)).2

@[expose] def fi22OuterZP :
    fi22P := ⟨fi22OuterZ, fi22OuterZ_mem_P⟩

theorem fi22OuterZP_eq :
    fi22OuterZP = ⟨fi22OuterZ, fi22OuterZ_mem_P⟩ := rfl

theorem fi22OuterXRep_mem
    {i : ℕ} (hi : i < 3) : fi22OuterXRep i ∈ fi22P :=
  (fi22OuterXRep_spec hi).1

theorem fi22OuterX₁_mem :
    fi22OuterXRep 0 ∈ fi22P := fi22OuterXRep_mem (by norm_num)

theorem fi22OuterX₂_mem :
    fi22OuterXRep 1 ∈ fi22P := fi22OuterXRep_mem (by norm_num)

theorem fi22OuterZ_mem_M :
    fi22OuterZ ∈ fi22OuterM := by
  rw [fi22OuterM_eq]
  refine ⟨fi22OuterZ_mem_P, MulAction.mem_stabilizer_iff.2 ?_⟩
  rw [Equiv.Perm.smul_def]
  apply Fin.ext
  rw [← rep_fi22OuterZ 0]
  exact fi22Centralizer_check.1

theorem fi22OuterM_subgroupOf_eq :
    fi22OuterM.subgroupOf fi22P = Subgroup.centralizer {fi22OuterZP} := by
  have hH : fi22OuterM.subgroupOf fi22P ≤ Subgroup.centralizer {fi22OuterZP} := by
    intro g hg
    rw [fi22OuterZP_eq, centralizer_mk_eq, Subgroup.mem_subgroupOf]
    exact fi22OuterM_le_centralizer (Subgroup.mem_subgroupOf.1 hg)
  have horb : (fi22OuterM.subgroupOf fi22P).index ≤
      (Set.range fun g : fi22P => g • {p : Fin 3510 | fi22OuterZP • p = p}).ncard := by
    rw [fi22OuterM_subgroupOf_index, fi22OuterZP_eq]
    have h := le_ncard_orbit_fixedSet rep_fi22OuterZ fi22OuterZ_mem_P
      fi22Centralizer_check.2.2.2.2.2.2.2.2.1 fi22Centralizer_check.2.2.2.2.2.2.2.2.2.1
    rw [fi22Centralizer_check.2.2.2.2.2.2.2.2.2.2] at h
    exact h
  exact (fixed_point_set_orbit_centralizer_bound fi22OuterZP _ hH horb).1

theorem fi22OuterM_eq_centralizer :
    fi22OuterM = fi22P ⊓ Subgroup.centralizer {fi22OuterZ} := by
  have h := fi22OuterM_subgroupOf_eq
  rw [fi22OuterZP_eq, centralizer_mk_eq, Subgroup.subgroupOf_inj] at h
  rw [inf_comm, ← h]
  exact (inf_eq_left.2 fi22OuterM_le_P).symm

theorem card_centralizer_x₁ :
    Nat.card (Subgroup.centralizer
      {(⟨fi22OuterXRep 0, fi22OuterX₁_mem⟩ : fi22P)}) < 18393661440 := by
  apply card_centralizer_lt_of_orbit
  have h := le_ncard_orbit_fixedSet (rep_fi22OuterXRep (i := 0) (by norm_num))
    fi22OuterX₁_mem fi22Centralizer_check.2.2.1 fi22Centralizer_check.2.2.2.1
  rw [fi22Centralizer_check.2.2.2.2.1] at h
  exact h

theorem card_centralizer_x₂ :
    Nat.card (Subgroup.centralizer
      {(⟨fi22OuterXRep 1, fi22OuterX₂_mem⟩ : fi22P)}) < 18393661440 := by
  apply card_centralizer_lt_of_orbit
  have h := le_ncard_orbit_fixedSet (rep_fi22OuterXRep (i := 1) (by norm_num))
    fi22OuterX₂_mem fi22Centralizer_check.2.2.2.2.2.1
    fi22Centralizer_check.2.2.2.2.2.2.1
  rw [fi22Centralizer_check.2.2.2.2.2.2.2.1] at h
  exact h

theorem card_inf_centralizer_x₁ :
    Nat.card (fi22P ⊓ Subgroup.centralizer {fi22OuterXRep 0} :
      Subgroup (Equiv.Perm (Fin 3510))) < 18393661440 := by
  rw [card_inf_eq_card_subgroupOf, ← centralizer_mk_eq fi22OuterX₁_mem]
  exact card_centralizer_x₁

theorem card_inf_centralizer_x₂ :
    Nat.card (fi22P ⊓ Subgroup.centralizer {fi22OuterXRep 1} :
      Subgroup (Equiv.Perm (Fin 3510))) < 18393661440 := by
  rw [card_inf_eq_card_subgroupOf, ← centralizer_mk_eq fi22OuterX₂_mem]
  exact card_centralizer_x₂

@[expose] def fi22OuterXP :
    Fin 2 → fi22P :=
  ![⟨fi22OuterXRep 0, fi22OuterX₁_mem⟩, ⟨fi22OuterXRep 1, fi22OuterX₂_mem⟩]

theorem fi22OuterXP_zero :
    fi22OuterXP 0 = ⟨fi22OuterXRep 0, fi22OuterX₁_mem⟩ := rfl

theorem fi22OuterXP_one :
    fi22OuterXP 1 = ⟨fi22OuterXRep 1, fi22OuterX₂_mem⟩ := rfl

theorem fi22P_involution_isConj
    (y : fi22P) (hy : orderOf y = 2) :
    IsConj fi22OuterZP y ∨ ∃ i : Fin 2, IsConj (fi22OuterXP i) y := by
  have hy' : orderOf (y : Equiv.Perm (Fin 3510)) = 2 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨k, hk, hc⟩ := fi22P_involution_conj y y.2 hy'
  have hconj : ∀ (w : Equiv.Perm (Fin 3510)) (hw : w ∈ fi22P),
      k * (y : Equiv.Perm (Fin 3510)) * k⁻¹ = w → IsConj (⟨w, hw⟩ : fi22P) y :=
    fun w hw h => (isConj_iff.2 ⟨⟨k, hk⟩, Subtype.ext h⟩).symm
  rcases hc with h | h | h
  · refine Or.inr ⟨0, ?_⟩
    rw [fi22OuterXP_zero]
    exact hconj _ _ h
  · refine Or.inr ⟨1, ?_⟩
    rw [fi22OuterXP_one]
    exact hconj _ _ h
  · rw [fi22OuterZP_eq]
    exact Or.inl (hconj _ _ h)

theorem fi22P_aut_class
    (α : MulAut fi22P) :
    IsConj fi22OuterZP (α fi22OuterZP) ∧ ∃ g : fi22P,
      (fi22OuterM.subgroupOf fi22P).map α.toMonoidHom =
        (fi22OuterM.subgroupOf fi22P).map (MulAut.conj g).toMonoidHom := by
  have hz : orderOf fi22OuterZP = 2 := by
    rw [fi22OuterZP_eq, Subgroup.orderOf_mk, orderOf_fi22OuterZ]
  have hx : ∀ i : Fin 2, orderOf (fi22OuterXP i) = 2 := by
    intro i
    fin_cases i
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, fi22OuterXP_zero, Subgroup.orderOf_mk]
      exact (fi22OuterXRep_spec (by norm_num)).2
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, fi22OuterXP_one, Subgroup.orderOf_mk]
      exact (fi22OuterXRep_spec (by norm_num)).2
  have hcard : ∀ i : Fin 2, Nat.card (Subgroup.centralizer {fi22OuterXP i}) <
      Nat.card (Subgroup.centralizer {fi22OuterZP}) := by
    intro i
    rw [← fi22OuterM_subgroupOf_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22OuterM_le_P).toEquiv, card_fi22OuterM]
    fin_cases i
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, fi22OuterXP_zero]
      exact card_centralizer_x₁
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, fi22OuterXP_one]
      exact card_centralizer_x₂
  have h := involution_class_centralizer_recovery hz fi22OuterXP hx fi22P_involution_isConj
    hcard α
  rw [← fi22OuterM_subgroupOf_eq] at h
  exact h

theorem AT_Fi22_involution_centralizer_class :
    fi22OuterZ ∈ fi22OuterM ∧ orderOf fi22OuterZ = 2 ∧
    fi22OuterM = fi22P ⊓ Subgroup.centralizer {fi22OuterZ} ∧
    fi22OuterM.subgroupOf fi22P = Subgroup.centralizer {fi22OuterZP} ∧
    Nat.card fi22OuterM = 18393661440 ∧
    Nat.card (fi22P ⊓ Subgroup.centralizer {fi22OuterXRep 0} :
      Subgroup (Equiv.Perm (Fin 3510))) < Nat.card fi22OuterM ∧
    Nat.card (fi22P ⊓ Subgroup.centralizer {fi22OuterXRep 1} :
      Subgroup (Equiv.Perm (Fin 3510))) < Nat.card fi22OuterM ∧
    ∀ α : MulAut fi22P, IsConj fi22OuterZP (α fi22OuterZP) ∧ ∃ g : fi22P,
      (fi22OuterM.subgroupOf fi22P).map α.toMonoidHom =
        (fi22OuterM.subgroupOf fi22P).map (MulAut.conj g).toMonoidHom := by
  refine ⟨fi22OuterZ_mem_M, orderOf_fi22OuterZ, fi22OuterM_eq_centralizer,
    fi22OuterM_subgroupOf_eq, card_fi22OuterM, ?_, ?_, fi22P_aut_class⟩
  · rw [card_fi22OuterM]
    exact card_inf_centralizer_x₁
  · rw [card_fi22OuterM]
    exact card_inf_centralizer_x₂

end CFSG.Monster.B.Fischer
