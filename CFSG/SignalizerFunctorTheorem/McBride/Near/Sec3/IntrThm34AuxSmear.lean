module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210j

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

abbrev smearSet (A G : Subgroup Γ) : Set (Subgroup Γ) :=
  {X | ∃ J ∈ lcal G, X = smear J A}

theorem exists_smear_conj (H : Lemma212.Hyp p A G) {J₁ J₂ : Subgroup Γ} (h₁ : J₁ ∈ lcal G)
    (h₂ : J₂ ∈ lcal G) :
    ∃ d ∈ cenIn G (A : Set Γ),
      smear J₂ A = (smear J₁ A).map (MulAut.conj d).toMonoidHom := by
  obtain ⟨a, ha, d, hd, rfl⟩ := H.transitive h₁ h₂
  refine ⟨d, hd, ?_⟩
  have hdA : ∀ b ∈ A, b * d = d * b := fun b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 b hb
  rw [Lemma212.smear_map_conj_of_commute J₁ A hdA, ← Thm210.map_conj_map_conj J₁ d a]
  unfold smear
  rw [Lemma212.orbitClosure_map_conj_of_mem (J₁.map (MulAut.conj d).toMonoidHom) ha]

section Semisimple

variable (h : SemisimpleAction p A G)

include h

theorem projIn_fittingSubgroupOf_cenIn_le {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    projIn (smearSet A G) (smear J A) (CFSG.fittingSubgroupOf (cenIn G (A : Set Γ))) ≤
      CFSG.fittingSubgroupOf (smear J A) := by
  have hT := h.isDirectProduct_smear
  have hS : smear J A ∈ smearSet A G := ⟨J, hJ, rfl⟩
  have hFD : CFSG.fittingSubgroupOf (cenIn G (A : Set Γ)) ≤ cenIn G (A : Set Γ) :=
    Subgroup.map_subtype_le _
  refine Thm210.le_fittingSubgroupOf_of_nilpotent (projIn_le _ _) ?_
    (Thm210.isNilpotent_projIn hT hS hFD (Thm210.isNilpotent_fittingSubgroupOf _))
  refine Thm210.le_normalizer_of_conj_mem fun c hc z hz => ?_
  have hcD : c ∈ projIn (smearSet A G) (smear J A) (cenIn G (A : Set Γ)) :=
    (hT.mem_projIn_iff hS).mpr ⟨⟨c, h.smear_le_cenIn hJ hc⟩, h.smear_le_cenIn hJ hc,
      hT.coord_of_mem hS hc⟩
  exact Thm210.projIn_conj_mem hT hS
    (fun y hy x hx => Thm210.fittingSubgroupOf_conj_mem hy hx) c hcD z hz

theorem fittingSubgroupOf_cenIn_le_sSup :
    CFSG.fittingSubgroupOf (cenIn G (A : Set Γ)) ≤
      sSup {X | ∃ S ∈ smearSet A G, X = CFSG.fittingSubgroupOf S} := by
  have hT := h.isDirectProduct_smear
  refine (Thm210.le_sSup_image_iff hT (T := fun S => CFSG.fittingSubgroupOf S)
    (fun S _ => Subgroup.map_subtype_le _)).mpr ⟨Subgroup.map_subtype_le _, ?_⟩
  rintro _ ⟨J, hJ, rfl⟩
  exact projIn_fittingSubgroupOf_cenIn_le h hJ

theorem exists_fittingSubgroupOf_smear_le
    {N : Subgroup Γ} (hN : N ≤ cenIn G (A : Set Γ))
    (hNA : Admits (cenIn G (A : Set Γ) ⊔ A) N) (hN1 : N ≠ ⊥) :
    ∃ J ∈ lcal G, CFSG.fittingSubgroupOf (smear J A) ≤ N := by
  have hT := h.isDirectProduct_smear
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
  refine hn1 (Subtype.ext ?_)
  show n = 1
  have hnD : n ∈ cenIn G (A : Set Γ) := hN hn
  have hcoord : ∀ (S : Subgroup Γ) (hS : S ∈ smearSet A G), hT.coord hS ⟨n, hnD⟩ = 1 := by
    intro S hS
    obtain ⟨J, hJ, hSJ⟩ := id hS
    subst hSJ
    refine (hT.coord_eq_one_iff hS _).mpr ?_
    have hle := (thm210j h (X := N) (hN.trans inf_le_left) hNA hJ (hcon J hJ)).1
    have := hle (Subgroup.mem_inf.mpr ⟨hn, hnD⟩)
    rw [h.cenIn_cenIn_smear hJ] at this
    exact this
  have h1 : (⟨n, hnD⟩ : ↥(cenIn G (A : Set Γ))) = 1 :=
    hT.ext_coord fun S hS => by rw [hcoord S hS, map_one]
  exact congrArg Subtype.val h1

theorem fittingSubgroupOf_cenIn_le_of_normal
    {D N : Subgroup Γ}
    (hDc : cenIn G (A : Set Γ) ≤ D)
    (htrans : ∀ J₁ ∈ lcal G, ∀ J₂ ∈ lcal G, ∃ d ∈ D,
      smear J₂ A = (smear J₁ A).map (MulAut.conj d).toMonoidHom)
    (hN : N ≤ cenIn G (A : Set Γ)) (hND : D ≤ Subgroup.normalizer (N : Set Γ))
    (hN1 : N ≠ ⊥) : CFSG.fittingSubgroupOf (cenIn G (A : Set Γ)) ≤ N := by
  have hNA : Admits (cenIn G (A : Set Γ) ⊔ A) N := by
    refine sup_le (hDc.trans hND) (Thm210.le_normalizer_of_conj_mem fun a ha x hx => ?_)
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hN hx)).2 a ha
    have : a * x * a⁻¹ = x := by rw [h1]; group
    rw [this]
    exact hx
  obtain ⟨J₀, hJ₀, hFJ₀⟩ := exists_fittingSubgroupOf_smear_le h hN hNA hN1
  have hall : ∀ J ∈ lcal G, CFSG.fittingSubgroupOf (smear J A) ≤ N := by
    intro J hJ
    obtain ⟨d, hdD, hd⟩ := htrans J₀ hJ₀ J hJ
    rw [hd, Thm210.fittingSubgroupOf_map_of_injective (MulAut.conj d).toMonoidHom
      (MulAut.conj d).injective]
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hND hdD) y).mp (hFJ₀ hy)
  refine (fittingSubgroupOf_cenIn_le_sSup h).trans (sSup_le ?_)
  rintro _ ⟨_, ⟨J, hJ, rfl⟩, rfl⟩
  exact hall J hJ

theorem fittingSubgroupOf_cenIn_ne_bot
    {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (cenIn G (A : Set Γ)) ≠ ⊥ := fun hbot =>
  h.fittingSubgroupOf_smear_ne_bot hJ
    (le_bot_iff.mp (hbot ▸ h.fittingSubgroupOf_smear_le hJ))

end Semisimple

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34
