module

public import CFSG.Quasithin.EmptyFaithful.S153XLoc

public section

namespace CFSG.Quasithin.X1469

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF
open scoped Pointwise commutatorElement

namespace Irr

variable {G : Type} [Group G]

private theorem conj_mem {N : Subgroup G} {g n : G} (hg : g ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) : g * n * g⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.1 hg n).1 hn

private theorem comm_mem {N : Subgroup G} {s s' y : G} (hy : y ∈ Subgroup.normalizer (N : Set G))
    (hys : y * s' = s' * y) (hn : s * s' ∈ N) : s * y * s⁻¹ * y⁻¹ ∈ N := by
  have e : s * y * s⁻¹ * y⁻¹ = (s * s') * (y * (s * s')⁻¹ * y⁻¹) := by
    calc s * y * s⁻¹ * y⁻¹ = s * (y * s') * s'⁻¹ * s⁻¹ * y⁻¹ := by group
      _ = s * (s' * y) * s'⁻¹ * s⁻¹ * y⁻¹ := by rw [hys]
      _ = (s * s') * (y * (s * s')⁻¹ * y⁻¹) := by group
  rw [e]
  exact N.mul_mem hn (conj_mem hy (N.inv_mem hn))

private theorem comm_mem_self {H : Subgroup G} {s y : G} (hy : y ∈ Subgroup.normalizer (H : Set G))
    (hs : s ∈ H) : s * y * s⁻¹ * y⁻¹ ∈ H := by
  have e : s * y * s⁻¹ * y⁻¹ = s * (y * s⁻¹ * y⁻¹) := by group
  rw [e]
  exact H.mul_mem hs (conj_mem hy (H.inv_mem hs))

theorem le_sup_blockU_of_mem {S Iz K K' N : Subgroup G} {c s s' : G} (BF : BlockFacts S Iz K c)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hN : K ⊓ Iz ≤ Subgroup.normalizer (N : Set G))
    (hs : s ∈ S ⊓ K) (hs' : s' ∈ K') (hn : s * s' ∈ N) (hsU : s ∉ blockU K) :
    S ⊓ K ≤ N ⊔ blockU K := by
  have hN₁ : K ⊓ Iz ≤ Subgroup.normalizer ((N ⊓ (S ⊓ K) : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2 ⟨hN hy, BF.Y_le_N_B hy⟩)
  rcases BF.irred_B (N ⊓ (S ⊓ K)) inf_le_right hN₁ with h | h
  · refine absurd (BF.fix_B s hs fun y hy => h (Subgroup.mem_inf.2 ⟨?_, ?_⟩)) hsU
    · exact comm_mem (hN hy) (hcomm y (Subgroup.mem_inf.1 hy).1 s' hs') hn
    · exact comm_mem_self (BF.Y_le_N_B hy) hs
  · exact h.trans (sup_le_sup_right inf_le_left _)

theorem Esub_le_of_mem {S Iz K K' N : Subgroup G} {c e e' : G} (BF : BlockFacts S Iz K c)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hN : K ⊓ Iz ≤ Subgroup.normalizer (N : Set G))
    (he : e ∈ Esub K Iz) (he' : e' ∈ K') (hn : e * e' ∈ N) (heZ : e ∉ Zsub S K) :
    Esub K Iz ≤ N := by
  have hYE : K ⊓ Iz ≤ Subgroup.normalizer ((Esub K Iz : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hN₁ : K ⊓ Iz ≤ Subgroup.normalizer ((N ⊓ Esub K Iz : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2 ⟨hN hy, hYE hy⟩)
  rcases BF.irred_E (N ⊓ Esub K Iz) inf_le_right hN₁ with h | h
  · refine absurd (BF.fix_E e he fun y hy => h (Subgroup.mem_inf.2 ⟨?_, ?_⟩)) heZ
    · exact comm_mem (hN hy) (hcomm y (Subgroup.mem_inf.1 hy).1 e' he') hn
    · exact comm_mem_self (hYE hy) he
  · exact inf_eq_right.1 h

end Irr

open Irr

theorem irred_Rz_of {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G} {t z c₁ c₂ : G}
    (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁) (BF₂ : BlockFacts S Iz K₂ c₂) :
    ∀ N : Subgroup G, N ≤ rz Iz → Iz ≤ Subgroup.normalizer (N : Set G) →
      N ≤ pCoreOf 2 I ∨ N ⊔ pCoreOf 2 I = rz Iz := by
  intro N hNR hNn
  by_cases hNQ : N ≤ pCoreOf 2 I
  · exact Or.inl hNQ
  right
  obtain ⟨n, hnN, hnQ⟩ := IsConcreteLE.not_le_iff_exists.1 hNQ
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := PG.R_decomp n (hNR hnN)
  have hs₁K : s₁ ∈ K₁ := (Subgroup.mem_inf.1 hs₁).2
  have hs₂K : s₂ ∈ K₂ := (Subgroup.mem_inf.1 hs₂).2
  have htI : t ∈ Iz := PG.S_le_Iz PG.t_mem
  have ht : t ∈ Subgroup.normalizer ((N ⊔ pCoreOf 2 I : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.2 ⟨hNn htI, PG.Iz_N_Q htI⟩)
  have hB : S ⊓ K₁ ≤ N ⊔ pCoreOf 2 I ∧ S ⊓ K₂ ≤ N ⊔ pCoreOf 2 I := by
    by_cases h₁ : s₁ ∈ blockU K₁
    · have h₂ : s₂ ∉ blockU K₂ := fun h₂ => hnQ (mul_mem (PG.U₁_le_Q h₁) (PG.U₂_le_Q h₂))
      have hn : s₂ * s₁ ∈ N := by
        rw [← PG.comm s₁ hs₁K s₂ hs₂K]
        exact hnN
      have hB₂ : S ⊓ K₂ ≤ N ⊔ pCoreOf 2 I :=
        (le_sup_blockU_of_mem BF₂ (fun a ha b hb => (PG.comm b hb a ha).symm)
          (inf_le_right.trans hNn) hs₂ hs₁K hn h₂).trans (sup_le_sup_left PG.U₂_le_Q _)
      refine ⟨fun b hb => ?_, hB₂⟩
      simpa [mul_assoc] using conj_mem (inv_mem ht) (hB₂ (PG.swap_B b hb))
    · have hB₁ : S ⊓ K₁ ≤ N ⊔ pCoreOf 2 I :=
        (le_sup_blockU_of_mem BF₁ PG.comm (inf_le_right.trans hNn) hs₁ hs₂K hnN h₁).trans
          (sup_le_sup_left PG.U₁_le_Q _)
      refine ⟨hB₁, fun b hb => ?_⟩
      simpa [mul_assoc] using conj_mem ht (hB₁ (PG.swap_B' b hb))
  refine le_antisymm (sup_le hNR PG.Q_le_R) fun g hg => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := PG.R_decomp g hg
  exact mul_mem (hB.1 ha) (hB.2 hb)

theorem irred_E0_of {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G} {t z c₁ c₂ : G}
    (PG : PairGen I S Iz K₁ K₂ t z) (BF₁ : BlockFacts S Iz K₁ c₁) (BF₂ : BlockFacts S Iz K₂ c₂) :
    ∀ N : Subgroup G, N ≤ E0 K₁ K₂ Iz → Iz ≤ Subgroup.normalizer (N : Set G) →
      N ≤ z0 Iz ∨ E0 K₁ K₂ Iz ≤ N ⊔ z0 Iz := by
  intro N hNE hNn
  by_cases hNZ : N ≤ z0 Iz
  · exact Or.inl hNZ
  right
  obtain ⟨n, hnN, hnZ⟩ := IsConcreteLE.not_le_iff_exists.1 hNZ
  have hE₁K : Esub K₁ Iz ≤ K₁ :=
    Subgroup.commutator_le_of_le (PG.U₁_le_B.trans inf_le_right) inf_le_left
  have hE₂K : Esub K₂ Iz ≤ K₂ :=
    Subgroup.commutator_le_of_le (PG.U₂_le_B.trans inf_le_right) inf_le_left
  have hEn : Esub K₁ Iz ≤ Subgroup.normalizer ((Esub K₂ Iz : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.2 <| Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def, PG.comm a (hE₁K ha) b (hE₂K hb), mul_inv_cancel_right,
        mul_inv_cancel]
      exact one_mem _
  have hn : n ∈ ((Esub K₁ Iz ⊔ Esub K₂ Iz : Subgroup G) : Set G) := hNE hnN
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hEn] at hn
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Set.mem_mul.1 hn
  have htN : t ∈ Subgroup.normalizer (N : Set G) := hNn (PG.S_le_Iz PG.t_mem)
  have hE : Esub K₁ Iz ≤ N ∧ Esub K₂ Iz ≤ N := by
    by_cases h₁ : e₁ ∈ Zsub S K₁
    · have h₂ : e₂ ∉ Zsub S K₂ := fun h₂ => hnZ (mul_mem (PG.Z₁_le_z0 h₁) (PG.Z₂_le_z0 h₂))
      have hn' : e₂ * e₁ ∈ N := by
        rw [← PG.comm e₁ (hE₁K he₁) e₂ (hE₂K he₂)]
        exact hnN
      have hE₂ : Esub K₂ Iz ≤ N :=
        Esub_le_of_mem BF₂ (fun a ha b hb => (PG.comm b hb a ha).symm) (inf_le_right.trans hNn)
          he₂ (hE₁K he₁) hn' h₂
      refine ⟨fun e he => ?_, hE₂⟩
      simpa [mul_assoc] using conj_mem (inv_mem htN) (hE₂ (PG.swap_E e he))
    · have hE₁ : Esub K₁ Iz ≤ N :=
        Esub_le_of_mem BF₁ PG.comm (inf_le_right.trans hNn) he₁ (hE₂K he₂) hnN h₁
      refine ⟨hE₁, fun e he => ?_⟩
      simpa [mul_assoc] using conj_mem htN (hE₁ (PG.swap_E' e he))
  exact sup_le (hE.1.trans le_sup_left) (hE.2.trans le_sup_left)

end CFSG.Quasithin.X1469
