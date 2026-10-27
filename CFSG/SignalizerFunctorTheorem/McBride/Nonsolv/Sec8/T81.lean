module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.Member
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Coord
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Plane
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Cover
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Decomp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Triple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.TripleApp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Diagonal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Gen
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Final

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem theorem_8_1
    (h : Counterexample p A θ) : ¬ TypeA p A θ := by
  intro hA
  obtain ⟨r, hr⟩ := h.exists_inPiTheta
  obtain ⟨S, hS⟩ := h.exists_isSr hr
  obtain ⟨B₁, B₂, B₃, c₁₂, c₁₃, hP⟩ := T81.exists_threePlanes h
  obtain ⟨a₀, ha₀, ha₀1⟩ := h.exists_ne_one
  have hA1 : A ≠ ⊥ := fun hbot => ha₀1 (by simpa [hbot] using ha₀)
  have hΩ := T81.isRegFam_triple h hA hr hS hP
  set W : Subgroup G := sSup (Msig p A θ) with hW
  set D : Subgroup G := thetaOf θ A with hD
  set Ω : Set (Subgroup G) := T81.tripleFam (T81.mFam θ (zOf S) B₁) (T81.mFam θ (zOf S) B₂)
    (T81.mFam θ (zOf S) B₃) with hΩdef
  have hDa₀ : D ≤ θ a₀ := thetaOf_le_apply ha₀ ha₀1
  have hDW : D ≤ W := hDa₀.trans (h.apply_le_sSup_msig ha₀ ha₀1)
  have hDA : D ≤ Subgroup.centralizer (A : Set G) := h.isFunctor.thetaOf_le_centralizer le_rfl
  have hD1 : D ≠ ⊥ := fun hbot => h.not_isSolvable_D (by rw [← hD, hbot]; infer_instance)
  have hΩ' := T81.isRegFam_projFam hΩ hDW hDA hD1
  have hiso : ∀ X ∈ Ω, Nonempty (↥(projIn Ω X D) ≃* ↥D) := fun X hX =>
    T81.nonempty_mulEquiv_projIn hΩ hDW hDA hX
  have hdp : IsDirectProduct Ω W := hΩ.isDirectProduct
  have hle₁ := T81.thetaOf_plane_le_sSup_projFam h hA hr hS hP.mem₁ hdp
    (fun X hX => (T81.tripleFam_le hX).1)
  have hle₂ := T81.thetaOf_plane_le_sSup_projFam h hA hr hS hP.mem₂ hdp
    (fun X hX => (T81.tripleFam_le hX).2.1)
  have hle₃ := T81.thetaOf_plane_le_sSup_projFam h hA hr hS hP.mem₃ hdp
    (fun X hX => (T81.tripleFam_le hX).2.2)
  have hc₁₂ := T81.theta_le_of_lines h hA hP.mem₁ hP.mem₂ hP.c₁₂_ne hP.zpowers_c₁₂ hle₁ hle₂
  have hc₁₃ := T81.theta_le_of_lines h hA hP.mem₁ hP.mem₃ hP.c₁₃_ne hP.zpowers_c₁₃ hle₁ hle₃
  have hc₁₂A : c₁₂ ∈ A :=
    hP.mem₁.1 ((inf_le_left : B₁ ⊓ B₂ ≤ B₁) (hP.zpowers_c₁₂ ▸ Subgroup.mem_zpowers c₁₂))
  have hc₁₃A : c₁₃ ∈ A :=
    hP.mem₁.1 ((inf_le_left : B₁ ⊓ B₃ ≤ B₁) (hP.zpowers_c₁₃ ▸ Subgroup.mem_zpowers c₁₃))
  have hne : c₁₃ ∉ Subgroup.zpowers c₁₂ := by
    intro hmem
    have h1 : c₁₃ ∈ B₁ ⊓ B₂ ⊓ B₃ := Subgroup.mem_inf.mpr ⟨hP.zpowers_c₁₂ ▸ hmem,
      (inf_le_right : B₁ ⊓ B₃ ≤ B₃) (hP.zpowers_c₁₃ ▸ Subgroup.mem_zpowers c₁₃)⟩
    rw [hP.inf_eq_bot, Subgroup.mem_bot] at h1
    exact hP.c₁₃_ne h1
  have hWle : W ≤ sSup (T81.projFam Ω D) :=
    T81.sSup_msig_le_of_lines h hA hc₁₂A hP.c₁₂_ne hc₁₃A hP.c₁₃_ne hne hc₁₂ hc₁₃
  have hleW : sSup (T81.projFam Ω D) ≤ W := by
    refine sSup_le ?_
    rintro _ ⟨X, hX, rfl⟩
    exact (projIn_le X D).trans (hdp.le hX)
  have hEq : sSup (T81.projFam Ω D) = W := le_antisymm hleW hWle
  have hmem : ∀ Y ∈ T81.projFam Ω D, Nonempty (↥Y ≃* ↥D) := by
    rintro _ ⟨X, hX, rfl⟩
    exact hiso X hX
  have hΩ'W : IsRegFam A W (T81.projFam Ω D) ⊥ := hEq ▸ hΩ'
  have hcard : Nat.card ↥W = Nat.card ↥D ^ Nat.card (T81.projFam Ω D) :=
    hΩ'W.card_eq_pow (m := Nat.card ↥D) fun Y hY => Nat.card_congr (hmem Y hY).some.toEquiv
  have hcop : Nat.Coprime p (Nat.card ↥W) := by
    rw [hcard]
    exact (h.isFunctor.coprime_thetaOf le_rfl hA1).pow_right _
  have hB : signalizerMcBrideHypothesisB p W :=
    T81.hypB_of_isDirectProduct h.prime (h.hypC a₀ ha₀ ha₀1) hDa₀ hΩ'W.isDirectProduct hmem hcop
  refine h.false_of_inf_centralizer_eq h.normalizes_sSup_msig hcop hB fun a ha ha1 => ?_
  have hcardW : Nat.card ↥(W ⊓ Subgroup.centralizer {a}) = Nat.card ↥D ^ (p ^ 2) :=
    T81.card_inf_centralizer_of_isRegFam h.prime hΩ'W h.elemAbelian.1 h.card
      (fun Y hY => Nat.card_congr (hmem Y hY).some.toEquiv) ha (h.card_zpowers ha ha1)
  have hθa : Nat.card ↥(θ a) = Nat.card ↥D ^ (p ^ 2) := by
    have := card_line_of_typeA h hA (h.zpowers_mem_E1 ha ha1)
    rwa [h.isFunctor.thetaOf_zpowers ha ha1] at this
  have hle : θ a ≤ W ⊓ Subgroup.centralizer {a} :=
    le_inf (h.apply_le_sSup_msig ha ha1) (h.isFunctor.le_centralizer a ha ha1)
  exact (Subgroup.eq_of_le_of_card_ge hle (hcardW.le.trans hθa.ge)).symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
