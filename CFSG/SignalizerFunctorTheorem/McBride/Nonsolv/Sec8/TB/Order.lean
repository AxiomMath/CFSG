module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Diagonal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Fam

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace IsRegFam

variable {G : Type*} [Group G] {A H N : Subgroup G} {Ω : Set (Subgroup G)}

theorem card_eq_of_mem (hΩ : IsRegFam A H Ω N) {X Y : Subgroup G} (hX : X ∈ Ω) (hY : Y ∈ Ω) :
    Nat.card X = Nat.card Y := by
  obtain ⟨a, -, rfl⟩ := hΩ.transitive X hX Y hY
  exact (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm

end IsRegFam

namespace TB

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K F₁ F₂ : Subgroup G}

theorem nonempty_mulEquiv_sup
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) : Nonempty (↥(thetaOf θ (F₁ ⊔ F₂)) ≃* ↥K) :=
  h.nonempty_mulEquiv_complement_of_typeB hB.toTypeBCore (hT.mem_E2_sup h) (hT.not_le_sup h)

theorem thetaOf_sup_ne_bot
    (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    thetaOf θ (F₁ ⊔ F₂) ≠ ⊥ := by
  intro hbot
  apply h.not_isSolvable_D
  have : thetaOf θ A = ⊥ :=
    le_bot_iff.mp (hbot ▸ thetaOf_anti (sup_le hT.mem₁.1 hT.mem₂.1 : F₁ ⊔ F₂ ≤ A))
  rw [this]
  infer_instance

theorem thetaOf_sup_le (h : Counterexample p A θ) (hT : TwoLines p A E F₁ F₂) :
    thetaOf θ (F₁ ⊔ F₂) ≤ sSup (Msig p A θ) ∧
      thetaOf θ (F₁ ⊔ F₂) ≤ Subgroup.centralizer ((F₁ ⊔ F₂ : Subgroup G) : Set G) :=
  ⟨le_sSup (h.thetaOf_mem_msig (sup_le hT.mem₁.1 hT.mem₂.1) (h.ne_bot_of_mem_E2
    (hT.mem_E2_sup h))), h.isFunctor.thetaOf_le_centralizer (sup_le hT.mem₁.1 hT.mem₂.1)⟩

theorem projIn_omegaFam_eq
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) {X : Subgroup G} (hX : X ∈ omegaFam θ E F₁ F₂) :
    projIn (omegaFam θ E F₁ F₂) X (thetaOf θ (F₁ ⊔ F₂)) = X ∧
      Nat.card X = Nat.card (thetaOf θ (F₁ ⊔ F₂)) := by
  have hΩ := isRegFam_omegaFam h hB hT
  have hΩB := isRegFam_omegaFam_sup h hB hT
  obtain ⟨hMW, hMC⟩ := thetaOf_sup_le h hT
  have hproj := T81.isRegFam_projFam hΩB hMW hMC (thetaOf_sup_ne_bot h hT)
  have hsSup : sSup (T81.projFam (omegaFam θ E F₁ F₂) (thetaOf θ (F₁ ⊔ F₂))) =
      sSup (Msig p A θ) := by
    rw [← iSup_projIn_eq h hB hT]
    refine le_antisymm (sSup_le ?_) (iSup₂_le fun Y hY => le_sSup ⟨Y, hY, rfl⟩)
    rintro _ ⟨Y, hY, rfl⟩
    exact le_iSup₂_of_le Y hY le_rfl
  have hiso : ∀ Y ∈ omegaFam θ E F₁ F₂, Nat.card (projIn (omegaFam θ E F₁ F₂) Y
      (thetaOf θ (F₁ ⊔ F₂))) = Nat.card (thetaOf θ (F₁ ⊔ F₂)) := fun Y hY =>
    Nat.card_congr (T81.nonempty_mulEquiv_projIn hΩB hMW hMC hY).some.toEquiv
  have hcard1 :
      Nat.card (sSup (Msig p A θ) : Subgroup G) = Nat.card (thetaOf θ (F₁ ⊔ F₂)) ^ p ^ 2 := by
    have h1 := hproj.card_eq_pow (m := Nat.card (thetaOf θ (F₁ ⊔ F₂))) (by
      rintro _ ⟨Y, hY, rfl⟩
      exact hiso Y hY)
    have h2 := hproj.card_mul_card
    rw [Subgroup.card_bot, mul_one, (hT.mem_E2_sup h).2] at h2
    rwa [h2, hsSup] at h1
  have hcard2 : Nat.card (sSup (Msig p A θ) : Subgroup G) = Nat.card X ^ p ^ 2 := by
    have h1 := hΩ.card_eq_pow (m := Nat.card X) fun Y hY => hΩ.card_eq_of_mem hY hX
    rwa [card_omegaFam h hB hT] at h1
  have hcard : Nat.card X = Nat.card (thetaOf θ (F₁ ⊔ F₂)) :=
    Nat.pow_left_injective (pow_pos h.prime.pos 2).ne' (hcard2.symm.trans hcard1)
  exact ⟨Subgroup.eq_of_le_of_card_ge (projIn_le X _) (hcard.le.trans (hiso X hX).ge), hcard⟩

theorem nonempty_mulEquiv_omegaFam
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) {X : Subgroup G} (hX : X ∈ omegaFam θ E F₁ F₂) :
    Nonempty (↥X ≃* ↥(thetaOf θ (F₁ ⊔ F₂))) := by
  have hΩB := isRegFam_omegaFam_sup h hB hT
  obtain ⟨hMW, hMC⟩ := thetaOf_sup_le h hT
  obtain ⟨e⟩ := T81.nonempty_mulEquiv_projIn hΩB hMW hMC hX
  exact ⟨(MulEquiv.subgroupCongr (projIn_omegaFam_eq h hB hT hX).1.symm).trans e⟩

theorem card_omegaFam_member
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) {X : Subgroup G} (hX : X ∈ omegaFam θ E F₁ F₂) :
    Nat.card X = Nat.card K :=
  (projIn_omegaFam_eq h hB hT hX).2.trans
    (Nat.card_congr (nonempty_mulEquiv_sup h hB hT).some.toEquiv)

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
