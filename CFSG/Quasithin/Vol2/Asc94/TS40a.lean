module

public import CFSG.Quasithin.Vol2.Asc94.TS39g

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

structure Frame4 (G : Type) [Group G] (z : G) extends Frame3 G z where
  z_mem_A' : z ∈ A'
  Γ : Fin 6 → Set G
  Γ_disj : ∀ i j, i ≠ j → Disjoint (Γ i) (Γ j)
  Γ_union : (⋃ i, Γ i) = ((A ⊓ A' : Subgroup G) : Set G) \ {1}
  Γ_inv : ∀ i, ∀ a ∈ Γ i, ∀ x ∈ T, x⁻¹ * a * x ∈ Γ i
  Γ_trans : ∀ i, ∀ a ∈ Γ i, ∀ b ∈ Γ i, ∃ x ∈ T, b = x⁻¹ * a * x
  Γ_card : ∀ i, (Γ i).ncard = ![1, 2, 2, 2, 4, 4] i
  Γ0 : Γ 0 = {z}
  Γ1 : Γ 1 = ((A ⊓ A' ⊓ U : Subgroup G) : Set G) \ {1, z}
  Γ2 : Γ 2 = ((A ⊓ A' ⊓ U2 : Subgroup G) : Set G) \ {1, z}
  Γ3 : Γ 3 = {a | a ∈ A ∧ a ∈ A' ∧ a ∈ Q ∧ a ≠ 1 ∧ a ∉ U ∧ a ∉ U2}
  card_B : Nat.card ↥(A ⊓ A') = 16
  NH_J : ∀ x ∈ Cz z, x ∈ Subgroup.normalizer ((A ⊔ A' : Subgroup G) : Set G) → x ∈ T
  Bsub : Subgroup G
  card_Bsub : Nat.card Bsub = 8
  Γ012_le_Bsub : ∀ i : Fin 6, i.val ≤ 2 → ∀ a ∈ Γ i, a ∈ Bsub
  Δ_Q : ∀ i : Fin 7, i.val ≤ 3 → ∀ a ∈ Δ i, a ∈ Q
  TQ_not_U : ∀ t ∈ TQ, t ∉ U ∧ t ∉ U2 ∧ t ∈ Q

@[expose] def Frame2.J (F : Frame2 G z) : Subgroup G := F.A ⊔ F.A'

theorem Frame2.J_le_T (F : Frame2 G z) : F.J ≤ F.T := sup_le F.A_le_T F.A'_le_T

theorem Frame2.isPGroup_J (F : Frame2 G z) : IsPGroup 2 F.J :=
  F.toFrame1.toFrame0.isPGroup_T.to_le F.J_le_T

theorem Frame2.weaklyClosed_A (F : Frame2 G z) : WeaklyClosedIn F.A F.T := s39_6_2 F

theorem Frame2.weaklyClosed_A' (F : Frame2 G z) : WeaklyClosedIn F.A' F.T := by
  refine ⟨F.A'_le_T, fun g hg => ?_⟩
  have hel := Gen.isElemAbelian_conjSubgroup g F.A'_elem
  have hcard : Nat.card (cjS g F.A') = 64 := by rw [Gen.card_conjSubgroup, F.card_A']
  rcases F.A_max _ hg hel hcard with h | h
  · exfalso
    apply s39_6_1 F
    refine ⟨g⁻¹, ?_⟩
    have := congrArg (cjS g⁻¹) h
    rw [Gen.cj_inv_cj] at this
    exact this.symm
  · exact h

theorem Frame2.weaklyClosed_J (F : Frame2 G z) : WeaklyClosedIn F.J F.T := by
  refine ⟨F.J_le_T, fun g hg => ?_⟩
  have hA : cjS g F.A ≤ F.T := (Subgroup.map_mono le_sup_left).trans hg
  have hA' : cjS g F.A' ≤ F.T := (Subgroup.map_mono le_sup_right).trans hg
  show cjS g (F.A ⊔ F.A') = F.A ⊔ F.A'
  have e1 := F.weaklyClosed_A.2 g hA
  have e2 := F.weaklyClosed_A'.2 g hA'
  show (F.A ⊔ F.A').map _ = F.A ⊔ F.A'
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) e1 e2

theorem Frame2.normalizer_J_le (F : Frame2 G z) {x : G}
    (hx : x ∈ Subgroup.normalizer (F.J : Set G)) :
    x ∈ Subgroup.normalizer (F.A : Set G) ∧ x ∈ Subgroup.normalizer (F.A' : Set G) := by
  have hxJ : cjS x F.J = F.J := Gen.mem_normalizer_iff_cj.1 hx
  have hA : cjS x F.A ≤ F.T := by
    refine le_trans ?_ F.J_le_T
    rw [← hxJ]
    exact Subgroup.map_mono le_sup_left
  have hA' : cjS x F.A' ≤ F.T := by
    refine le_trans ?_ F.J_le_T
    rw [← hxJ]
    exact Subgroup.map_mono le_sup_right
  exact ⟨Gen.mem_normalizer_iff_cj.2 (F.weaklyClosed_A.2 x hA),
    Gen.mem_normalizer_iff_cj.2 (F.weaklyClosed_A'.2 x hA')⟩

theorem Frame2.T_le_normalizer_J (F : Frame2 G z) : F.T ≤ Subgroup.normalizer (F.J : Set G) := by
  intro t ht
  rw [Gen.mem_normalizer_iff_cj]
  have hA : cjS t F.A = F.A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have := F.A_normal t⁻¹ (F.T.inv_mem ht) a ha
      simpa using this
    · intro a ha
      refine ⟨t⁻¹ * a * t, F.A_normal t ht a ha, ?_⟩
      show t * (t⁻¹ * a * t) * t⁻¹ = a
      group
  have hA' : cjS t F.A' = F.A' := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have := F.A'_normal t⁻¹ (F.T.inv_mem ht) a ha
      simpa using this
    · intro a ha
      refine ⟨t⁻¹ * a * t, F.A'_normal t ht a ha, ?_⟩
      show t * (t⁻¹ * a * t) * t⁻¹ = a
      group
  show (F.A ⊔ F.A').map _ = F.A ⊔ F.A'
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hA hA'

theorem Frame2.B_central (F : Frame2 G z) {b y : G} (hb : b ∈ F.A ⊓ F.A') (hy : y ∈ F.J) :
    b * y = y * b := by
  have hle : F.J ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (F.comm_A ha (Subgroup.mem_inf.1 hb).1))
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (F.A'_elem.1.is_comm.comm (⟨b, (Subgroup.mem_inf.1 hb).2⟩ : F.A')
          ⟨a, ha⟩)).symm)
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  exact this.symm

theorem Frame2.fusion_B (F : Frame2 G z) {a b g : G} (ha : a ∈ F.A ⊓ F.A') (hb : b ∈ F.A ⊓ F.A')
    (hab : g⁻¹ * a * g = b) :
    ∃ n ∈ Subgroup.normalizer (F.J : Set G), n⁻¹ * a * n = b := by
  obtain ⟨P, hP⟩ := s39_2 F.toFrame1.toFrame0
  have hwc : WeaklyClosedIn F.J (P : Subgroup G) := by
    rw [hP]
    exact F.weaklyClosed_J
  exact normalizer_controls_fusion_of_weaklyClosedIn_pGroup F.isPGroup_J
    (Gen.weaklyClosedIn_of_sylow P hwc) (fun s hs => F.B_central ha hs)
    (fun s hs => F.B_central hb hs) hab

end CFSG.Quasithin.A94
