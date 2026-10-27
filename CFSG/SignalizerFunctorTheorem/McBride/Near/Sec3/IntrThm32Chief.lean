module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped Pointwise commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

variable {Γ : Type*} [Group Γ] {p : ℕ}

structure ChiefSetting (p : ℕ) (A G K D : Subgroup Γ) : Prop where
  near : NearAsolvAction p A G
  K_le : K ≤ G
  D_le : D ≤ G
  D_cen : D ≤ Subgroup.centralizer (A : Set Γ)
  sup_eq : K ⊔ D = G
  chief : IsChiefFactorOf (G ⊔ A) K ⊥
  cen_bot : G ⊓ Subgroup.centralizer (K : Set Γ) = ⊥

namespace ChiefSetting

variable {A G K D : Subgroup Γ} (H : ChiefSetting p A G K D)

include H

theorem GA_le_nor_K : G ⊔ A ≤ Subgroup.normalizer (K : Set Γ) := H.chief.2.1.2

theorem G_le_nor_K : G ≤ Subgroup.normalizer (K : Set Γ) := le_sup_left.trans H.GA_le_nor_K

theorem A_le_nor_G : A ≤ Subgroup.normalizer (G : Set Γ) := H.near.admits

theorem GA_le_nor_G : G ⊔ A ≤ Subgroup.normalizer (G : Set Γ) :=
  sup_le Subgroup.le_normalizer H.A_le_nor_G

theorem K_ne_bot : K ≠ ⊥ := H.chief.2.2.1.ne'

theorem not_comm : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  apply H.K_ne_bot
  have h1 : K ≤ G ⊓ Subgroup.centralizer (K : Set Γ) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨H.K_le hx,
      Subgroup.mem_centralizer_iff.mpr fun y hy => hcon y hy x hx⟩
  rw [H.cen_bot] at h1
  exact le_bot_iff.mp h1

theorem not_isSolvable : ¬ Group.IsSolvable ↥K := not_isSolvable_of_chief_bot H.chief H.not_comm

theorem sol_eq_bot [Finite Γ] : sol G = ⊥ := by
  have hSG : sol G ≤ G := sol_le G
  have hSn : G ⊔ A ≤ Subgroup.normalizer (sol G : Set Γ) :=
    H.GA_le_nor_G.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol G)
  have hn : G ⊔ A ≤ Subgroup.normalizer ((sol G ⊓ K : Subgroup Γ) : Set Γ) :=
    le_normalizer_inf hSn H.GA_le_nor_K
  have hle : sol G ⊓ K ≤ G ⊔ A := inf_le_left.trans (hSG.trans le_sup_left)
  rcases H.chief.2.2.2 (sol G ⊓ K) ⟨hle, hn⟩ bot_le inf_le_right with h | h
  · refine eq_bot_iff.mpr fun s hs => ?_
    have hsC : s ∈ Subgroup.centralizer (K : Set Γ) := by
      refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
      exact (mul_comm_of_inf_eq_bot (S := sol G) (K := K) (hSG.trans H.G_le_nor_K)
        (H.K_le.trans (le_sup_left.trans hSn)) h hs hk).symm
    have h1 : s ∈ G ⊓ Subgroup.centralizer (K : Set Γ) := Subgroup.mem_inf.mpr ⟨hSG hs, hsC⟩
    rw [H.cen_bot] at h1
    exact h1
  · exfalso
    have hKS : K ≤ sol G := inf_eq_right.mp h
    exact H.not_isSolvable (Thm211.isSolvable_of_le hKS (isSolvable_sol G))

theorem layerIn_eq [Finite Γ] : layerIn G = K := by
  have hsol := H.sol_eq_bot
  have hk : layerIn G = kOf G := (kOf_eq_map_layer hsol).symm
  rw [hk]
  have hEn : G ⊔ A ≤ Subgroup.normalizer (kOf G : Set Γ) :=
    H.GA_le_nor_G.trans (Thm211.normalizer_le_normalizer_kOf G)
  have hKE : K ≤ kOf G := by
    have hn : G ⊔ A ≤ Subgroup.normalizer ((K ⊓ kOf G : Subgroup Γ) : Set Γ) :=
      le_normalizer_inf H.GA_le_nor_K hEn
    have hle : K ⊓ kOf G ≤ G ⊔ A := inf_le_left.trans (H.K_le.trans le_sup_left)
    rcases H.chief.2.2.2 (K ⊓ kOf G) ⟨hle, hn⟩ bot_le inf_le_left with h | h
    · exfalso
      have hE1 : kOf G ≤ Subgroup.centralizer (K : Set Γ) :=
        le_centralizer_of_inf_eq_bot ((kOf_le G).trans H.G_le_nor_K)
          (H.K_le.trans (le_sup_left.trans hEn)) (by rw [inf_comm]; exact h)
      have hE2 : kOf G = ⊥ := by
        have h1 : kOf G ≤ G ⊓ Subgroup.centralizer (K : Set Γ) := le_inf (kOf_le G) hE1
        rw [H.cen_bot] at h1
        exact le_bot_iff.mp h1
      have hG := centralizer_kOf_eq_bot hsol
      rw [hE2, Thm211.centralizer_bot, inf_top_eq] at hG
      exact H.K_ne_bot (le_bot_iff.mp (hG ▸ H.K_le))
    · exact inf_eq_left.mp h
  have hss : IsSemisimple (kOf G) := isSemisimple_kOf hsol
  have hN : (K.subgroupOf (kOf G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mpr
      ((kOf_le G).trans H.G_le_nor_K)
  have hP := hss.isDirectPair_of_normal hKE hN
  have hcen : kOf G ⊓ Subgroup.centralizer (K : Set Γ) = ⊥ := by
    rw [eq_bot_iff, ← H.cen_bot]
    exact inf_le_inf_right _ (kOf_le G)
  rw [← hP.sup_eq, hcen, sup_bot_eq]

theorem prod_eq [Finite Γ] : (layerIn G : Set Γ) * (cenIn G (A : Set Γ) : Set Γ) = G := by
  rw [H.layerIn_eq]
  have hDK : D ≤ Subgroup.normalizer (K : Set Γ) := H.D_le.trans H.G_le_nor_K
  have hDc : (D : Set Γ) ⊆ (cenIn G (A : Set Γ) : Set Γ) := fun d hd =>
    Subgroup.mem_inf.mpr ⟨H.D_le hd, H.D_cen hd⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨k, hk, c, hc, rfl⟩
    exact mul_mem (H.K_le hk) (Subgroup.mem_inf.mp hc).1
  · intro g hg
    have hg' : g ∈ K ⊔ D := H.sup_eq ▸ hg
    obtain ⟨k, hk, d, hd, rfl⟩ := (mem_sup_iff_mul hDK).mp hg'
    exact ⟨k, hk, d, hDc hd, rfl⟩

theorem exists_B
    [Finite Γ] : ∃ B : Subgroup Γ, B ≤ A ∧ CyclicMod A B ∧
    ¬ Group.IsSolvable ↥(cenIn K (B : Set Γ)) ∧
    IsChiefFactorOf (A ⊔ cenIn G (B : Set Γ)) (cenIn K (B : Set Γ)) ⊥ ∧
    sol (cenIn G (B : Set Γ)) = ⊥ := by
  have hmin : IsChiefFactorOf (G ⊔ A) (layerIn G) ⊥ := by
    rw [H.layerIn_eq]
    exact H.chief
  obtain ⟨B, hBA, hcyc, hns, hch, -, hsol⟩ := lemma212 H.near H.sol_eq_bot hmin H.prod_eq
  rw [H.layerIn_eq] at hns hch
  exact ⟨B, hBA, hcyc, hns, hch, hsol⟩

end ChiefSetting

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32
