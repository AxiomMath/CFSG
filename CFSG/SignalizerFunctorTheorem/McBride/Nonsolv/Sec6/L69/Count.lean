module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

variable {Γ : Type*} [Group Γ]

theorem card_orbit_mul_card_inf_normalizer (H V : Subgroup Γ)
    (hV : V ≤ Subgroup.normalizer (H : Set Γ)) {J₀ : Subgroup Γ} (hJ₀ : J₀ ∈ lcal H) :
    Nat.card {J : Subgroup Γ // J ∈ lcal H ∧ ∃ v ∈ V, J = J₀.map (MulAut.conj v).toMonoidHom} *
      Nat.card (V ⊓ Subgroup.normalizer (J₀ : Set Γ) : Subgroup Γ) = Nat.card V := by
  let _ : MulAction V (lcal H) :=
    { smul := fun v J => ⟨J.1.map (MulAut.conj (v : Γ)).toMonoidHom,
        map_conj_mem_lcal J.2 (hV v.2)⟩
      one_smul := fun J => Subtype.ext (map_conj_one J.1)
      mul_smul := fun v w J => Subtype.ext (L514.map_conj_map_conj J.1 (w : Γ) (v : Γ)).symm }
  let x : lcal H := ⟨J₀, hJ₀⟩
  have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup V x)
  rw [Nat.card_prod] at h1
  let e1 : MulAction.orbit V x ≃
      {J : Subgroup Γ // J ∈ lcal H ∧ ∃ v ∈ V, J = J₀.map (MulAut.conj v).toMonoidHom} :=
    { toFun := fun y => ⟨y.1.1, y.1.2, by
        obtain ⟨v, hv⟩ := MulAction.mem_orbit_iff.mp y.2
        exact ⟨v, v.2, (congrArg Subtype.val hv).symm⟩⟩
      invFun := fun J => ⟨⟨J.1, J.2.1⟩, by
        obtain ⟨v, hv, h⟩ := J.2.2
        exact MulAction.mem_orbit_iff.mpr ⟨⟨v, hv⟩, Subtype.ext h.symm⟩⟩
      left_inv := fun y => rfl
      right_inv := fun J => rfl }
  let e2 : MulAction.stabilizer V x ≃ (V ⊓ Subgroup.normalizer (J₀ : Set Γ) : Subgroup Γ) :=
    { toFun := fun v => ⟨v.1, Subgroup.mem_inf.mpr ⟨v.1.2,
        map_conj_eq_self_iff.mp (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp v.2))⟩⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩,
        MulAction.mem_stabilizer_iff.mpr
          (Subtype.ext (map_conj_eq_self_iff.mpr (Subgroup.mem_inf.mp g.2).2))⟩
      left_inv := fun v => rfl
      right_inv := fun g => rfl }
  rw [← Nat.card_congr e1, ← Nat.card_congr e2]
  exact h1

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

open L69

theorem card_lcal_mul_card_bN
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : Nat.card (lcal (thetaOf θ B)) * Nat.card (bN A θ B) = Nat.card A := by
  obtain ⟨L, hL⟩ := h.lcal_thetaOf_nonempty hBA hB
  have h1 := card_orbit_mul_card_inf_normalizer (thetaOf θ B) A
    (h.isFunctor.normalizes_thetaOf hBA) hL
  have e : {J : Subgroup G // J ∈ lcal (thetaOf θ B) ∧
      ∃ v ∈ A, J = L.map (MulAut.conj v).toMonoidHom} ≃ lcal (thetaOf θ B) :=
    Equiv.subtypeEquivRight fun J =>
      ⟨fun hJ => hJ.1, fun hJ => ⟨hJ, h.exists_conj_eq_of_mem_lcal hBA hB hL hJ⟩⟩
  rw [Nat.card_congr e, ← h.bN_eq_inf_normalizer hBA hB hL] at h1
  exact h1

open scoped Classical in
theorem card_lcal_thetaOf
    (h : Counterexample p A θ) {F E : Subgroup G} (hF : F ≤ A)
    (hF0 : F ≠ ⊥) (hE : E ≤ A) (hEp : Nat.card E = p) :
    Nat.card (lcal (thetaOf θ F)) = (if E ≤ bN A θ F then 1 else p) *
      Nat.card (lcal (thetaOf θ F ⊓ Subgroup.centralizer (E : Set G))) := by
  set H := thetaOf θ F
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := h.isFunctor.normalizes_thetaOf hF
  obtain ⟨-, hlcal, hfib⟩ :=
    theorem_5_15_f (h.kSetting_thetaOf hF hF0) (h.kDown_thetaOf hF hF0) hE
  let Φ : lcal H → lcal (H ⊓ Subgroup.centralizer (E : Set G)) := fun J =>
    ⟨CFSG.inSubgroup CFSG.generalizedFitting (smear J.1 E), by rw [hlcal]; exact ⟨J.1, J.2, rfl⟩⟩
  have hΦs : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    rw [hlcal] at hy
    obtain ⟨J, hJ, hJy⟩ := hy
    exact ⟨⟨J, hJ⟩, Subtype.ext hJy.symm⟩
  have hΦfib : ∀ J J₀ : lcal H, Φ J = Φ J₀ ↔
      ∃ b ∈ E, J.1 = J₀.1.map (MulAut.conj b).toMonoidHom := fun J J₀ => by
    rw [Subtype.ext_iff]
    exact eq_comm.trans (hfib J₀.1 J₀.2 J.1 J.2)
  have hfibcard : ∀ y, Nat.card {J : lcal H // Φ J = y} = if E ≤ bN A θ F then 1 else p := by
    intro y
    obtain ⟨J₀, rfl⟩ := hΦs y
    let e : {J : lcal H // Φ J = Φ J₀} ≃ {J : Subgroup G // J ∈ lcal H ∧
        ∃ v ∈ E, J = J₀.1.map (MulAut.conj v).toMonoidHom} :=
      { toFun := fun J => ⟨J.1.1, J.1.2, (hΦfib J.1 J₀).mp J.2⟩
        invFun := fun J => ⟨⟨J.1, J.2.1⟩, (hΦfib ⟨J.1, J.2.1⟩ J₀).mpr J.2.2⟩
        left_inv := fun J => rfl
        right_inv := fun J => rfl }
    rw [Nat.card_congr e]
    have hos := card_orbit_mul_card_inf_normalizer H E (hE.trans hAH) J₀.2
    have hstab : E ⊓ Subgroup.normalizer (J₀.1 : Set G) = E ⊓ bN A θ F := by
      rw [h.bN_eq_inf_normalizer hF hF0 J₀.2, ← inf_assoc, inf_eq_left.mpr hE]
    rw [hstab, hEp] at hos
    have hp : 0 < p := by
      rw [← hEp]
      exact Nat.card_pos
    split_ifs with hle
    · rw [inf_eq_left.mpr hle, hEp] at hos
      exact Nat.eq_of_mul_eq_mul_right hp (hos.trans (one_mul p).symm)
    · have hdvd : Nat.card ↥(E ⊓ bN A θ F) ∣ p := hEp ▸ Subgroup.card_dvd_of_le inf_le_left
      have hne : Nat.card ↥(E ⊓ bN A θ F) ≠ p := by
        intro hcard
        refine hle ?_
        have : E ⊓ bN A θ F = E := Subgroup.eq_of_le_of_card_ge inf_le_left (hEp ▸ hcard.ge)
        exact this ▸ inf_le_right
      have h1 : Nat.card ↥(E ⊓ bN A θ F) = 1 :=
        ((Nat.dvd_prime h.prime).mp hdvd).resolve_right hne
      rw [h1, mul_one] at hos
      exact hos
  have : Fintype (lcal (H ⊓ Subgroup.centralizer (E : Set G))) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv Φ), Nat.card_sigma]
  simp only [hfibcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card, mul_comm]

open scoped Classical in
theorem card_lcal_thetaOf_sup
    (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ∈ signalizerFunctorEk p 1 A) :
    Nat.card (lcal (thetaOf θ F)) = (if E ≤ bN A θ F then 1 else p) *
      Nat.card (lcal (thetaOf θ (E ⊔ F))) := by
  obtain ⟨f, hfA, hf1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  have hF0 : Subgroup.zpowers f ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hf1
  have hsup : thetaOf θ (Subgroup.zpowers f) ⊓ Subgroup.centralizer (E : Set G) =
      thetaOf θ (E ⊔ Subgroup.zpowers f) := by
    rw [h.isFunctor.thetaOf_zpowers hfA hf1, h.isFunctor.inf_centralizer_eq_thetaOf hfA hf1 hE.1,
      sup_comm]
  rw [← hsup]
  exact h.card_lcal_thetaOf hF.1 hF0 hE.1 (hE.2.trans (pow_one p))

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
