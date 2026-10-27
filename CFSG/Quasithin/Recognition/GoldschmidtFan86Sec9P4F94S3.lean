module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalPerm3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Cfg

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem xβ_mem_stabilizer_beta : S.xβ ∈ MulAction.stabilizer G S.beta :=
  MulAction.mem_stabilizer_iff.2 S.xβ_smul_beta

theorem t_mem_stabilizer_beta (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) :
    S.t ∈ MulAction.stabilizer G S.beta := by
  refine MulAction.mem_stabilizer_iff.2 (S.t_smul_eq h81 (Or.inr ?_))
  rw [SimpleGraph.dist_comm]
  exact (S.D.dist_vert_ne F h71c (i := 2) (j := 0) (by decide) (m := 1) (m' := 1)
    (by norm_num) (by norm_num)).le

theorem xβ_not_mem_nbrStab : S.xβ ∉ nbrStab Γ G S.beta := fun h => by
  have h1 : S.xβ • S.α = S.α := mem_nbrStab.1 h S.α (S.D.adj_start_beta 2).symm
  exact S.alpha_ne_xβ_inv (inv_smul_eq_iff.2 h1.symm)

theorem stabilizer_beta_eq (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) :
    MulAction.stabilizer G S.beta =
      Subgroup.closure ({S.xβ, S.t} : Set G) ⊔ nbrStab Γ G S.beta := by
  have hv : Fan86.valence Γ S.beta = 3 := S.D.valence_beta F 2
  obtain ⟨φ, hsurj, hker⟩ := F.exists_perm3 hv
  have hx : S.xβ ∈ MulAction.stabilizer G S.beta := S.xβ_mem_stabilizer_beta
  have ht : S.t ∈ MulAction.stabilizer G S.beta := S.t_mem_stabilizer_beta F h71c h81
  set X : ↥(MulAction.stabilizer G S.beta) := ⟨S.xβ, hx⟩ with hX
  set T : ↥(MulAction.stabilizer G S.beta) := ⟨S.t, ht⟩ with hT
  have hX3 : X ^ 3 = 1 := Subtype.ext S.xβ_pow_three
  have hT2 : T * T = 1 := Subtype.ext (S.t_sq h71c)
  have hTX : T * X * T = X⁻¹ := Subtype.ext (S.t_conj_xβ h71c)
  have hX1 : φ X ≠ 1 := fun h => S.xβ_not_mem_nbrStab ((hker X).1 h)
  have hφX : orderOf (φ X) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by rw [← map_pow, hX3, map_one]) hX1
  have hT1 : φ T ≠ 1 := by
    intro h
    have h1 : φ X = (φ X)⁻¹ := by
      have e := congrArg φ hTX
      rw [map_mul, map_mul, h, map_inv] at e
      simpa using e
    have h2 : (φ X) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h1]
      exact inv_mul_cancel _
    have h3 : orderOf (φ X) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hφX] at h3
    omega
  have hφT : orderOf (φ T) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two, ← map_mul, hT2, map_one]) hT1
  set Q : Subgroup (Perm (Fin 3)) := Subgroup.closure ({φ X, φ T} : Set (Perm (Fin 3))) with hQ
  have hXQ : φ X ∈ Q := Subgroup.subset_closure (by simp)
  have hTQ : φ T ∈ Q := Subgroup.subset_closure (by simp)
  have h3 : 3 ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨φ X, hXQ⟩ : Q)
    rwa [Subgroup.orderOf_mk, hφX] at this
  have h2 : 2 ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨φ T, hTQ⟩ : Q)
    rwa [Subgroup.orderOf_mk, hφT] at this
  have h6 : Nat.card Q ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [Nat.card_eq_fintype_card (α := Perm (Fin 3)), Fintype.card_perm, Fintype.card_fin] at this
  have hcard : Nat.card Q = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) h6
    generalize Nat.card Q = m at h3 h2 h6 hle ⊢
    interval_cases m <;> omega
  have hQtop : Q = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, Nat.card_eq_fintype_card (α := Perm (Fin 3)), Fintype.card_perm, Fintype.card_fin]
    rfl
  refine le_antisymm (fun g hg => ?_) (sup_le ((Subgroup.closure_le _).2 ?_)
    (F.nbrStab_le_stabilizer S.beta))
  · set g' : ↥(MulAction.stabilizer G S.beta) := ⟨g, hg⟩ with hg'
    have hmem : φ g' ∈ Q := hQtop ▸ Subgroup.mem_top _
    have himg : Q = (Subgroup.closure ({X, T} : Set ↥(MulAction.stabilizer G S.beta))).map φ := by
      rw [hQ, MonoidHom.map_closure]
      congr 1
      ext a
      simp [Set.image_insert_eq]
    rw [himg] at hmem
    obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.1 hmem
    have hk : (m⁻¹ * g' : ↥(MulAction.stabilizer G S.beta)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel]
    have hkK : ((m⁻¹ * g' : ↥(MulAction.stabilizer G S.beta)) : G) ∈ nbrStab Γ G S.beta :=
      (hker _).1 hk
    have hmG : (m : G) ∈ Subgroup.closure ({S.xβ, S.t} : Set G) := by
      have : (m : G) ∈ (Subgroup.closure ({X, T} : Set ↥(MulAction.stabilizer G S.beta))).map
          (MulAction.stabilizer G S.beta).subtype := Subgroup.mem_map.2 ⟨m, hm, rfl⟩
      rw [MonoidHom.map_closure] at this
      convert this using 2
      ext a
      simp [Set.image_insert_eq, hX, hT]
    have : g = (m : G) * ((m⁻¹ * g' : ↥(MulAction.stabilizer G S.beta)) : G) := by
      simp [hg']
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hmG) (Subgroup.mem_sup_right hkK)
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hx
    · exact ht

end Sec9Cfg

end CFSG.Quasithin.Fan86
