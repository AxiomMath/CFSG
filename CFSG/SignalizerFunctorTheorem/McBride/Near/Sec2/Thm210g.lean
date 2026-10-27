module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupOrbit

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

open Thm210g

theorem thm210h
    (h : SemisimpleAction p A G) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) {J : Subgroup Γ} (hJ : J ∈ lcal G)
    (hnn : ¬ Group.IsNilpotent (projIn (lcal G) J X)) :
    CFSG.fittingSubgroupOf (smear J A) ≤ X := by
  have hG := h.isDirectProduct_lcal
  have hXA : Admits A X := le_sup_right.trans hX
  have hXD : Admits (cenIn G A) X := le_sup_left.trans hX
  have hcomm := commute_orbitClosure_outOrbit h hJ
  obtain ⟨X₁, hX₁⟩ : ∃ X₁, X₁ = proj (orbitClosure J A) (outOrbit G A J) X := ⟨_, rfl⟩
  have hmem : ∀ y, y ∈ X₁ ↔ y ∈ orbitClosure J A ∧ ∃ l ∈ outOrbit G A J, y * l ∈ X :=
    fun y => hX₁ ▸ mem_proj_iff hcomm
  have hX₁G₁ : X₁ ≤ orbitClosure J A := hX₁ ▸ proj_le_left _ _ _
  have hX₁A : Admits A X₁ := fun a ha => hX₁ ▸ Thm210g.mem_normalizer_proj hcomm
    (Thm210.admits_orbitClosure J ha) (admits_outOrbit h ha) (hXA ha)
  have hX₁D : Admits (cenIn G A) X₁ := fun d hd => hX₁ ▸ Thm210g.mem_normalizer_proj hcomm
    (le_normalizer_orbitClosure h hJ (Thm210.mem_cenIn_iff.1 hd).1)
    (le_normalizer_outOrbit h (Thm210.mem_cenIn_iff.1 hd).1) (hXD hd)
  have hPJ : projIn (lcal G) J X ≤ projIn (lcal G) J X₁ := by
    intro z hz
    obtain ⟨x, hxX, rfl⟩ := (hG.mem_projIn_iff hJ).1 hz
    obtain ⟨y, hy, l, hl, hyl⟩ := exists_mul_orbitClosure_outOrbit h hJ (hXG hxX)
    have hyG : y ∈ G := orbitClosure_le_group h hJ hy
    have hlG : l ∈ G := outOrbit_le G A J hl
    refine (hG.mem_projIn_iff hJ).2 ⟨⟨y, hyG⟩, (hmem y).2 ⟨hy, l, hl, by rw [hyl]; exact hxX⟩, ?_⟩
    have hx : x = ⟨y, hyG⟩ * ⟨l, hlG⟩ := Subtype.ext hyl.symm
    have hcl : hG.coord hJ ⟨l, hlG⟩ = 1 :=
      (hG.coord_eq_one_iff hJ _).2 (outOrbit_le_sSup_diff G A J hl)
    rw [hx, map_mul, hcl, mul_one]
  have hX₁n : ¬ Group.IsNilpotent ↥(projIn (lcal G) J X₁) := fun hn => hnn (by
    have := hn
    exact Thm210.isNilpotent_of_injective (Subgroup.inclusion hPJ)
      (Subgroup.inclusion_injective hPJ))
  have hYn : ¬ X₁ ≤ fProd A G := by
    intro hle
    have hle' := (h.le_fProd_iff.1 hle).2 J hJ
    have : Group.IsNilpotent ↥(CFSG.fittingSubgroupOf (kJ A J)) :=
      Thm210.isNilpotent_fittingSubgroupOf _
    exact hX₁n (Thm210.isNilpotent_of_injective (Subgroup.inclusion hle')
      (Subgroup.inclusion_injective hle'))
  have hne := h.inf_smear_ne_bot hJ hX₁G₁ hX₁A hX₁D hYn
  have hF₁ : CFSG.fittingSubgroupOf (smear J A) ≤ X₁ :=
    h.fittingSubgroupOf_smear_le_of_inf_ne_bot hJ (fun d hd => hX₁D (h.smear_le_cenIn hJ hd)) hne
  obtain ⟨x, hx, d, hd, hdx⟩ := h.exists_noncomm_smear hJ
  obtain ⟨-, l, hl, hxl⟩ := (hmem x).1 (hF₁ hx)
  have hdl : Commute d l := hcomm d (smear_le_orbitClosure J A hd) l hl
  have hdX : d ∈ Subgroup.normalizer (X : Set Γ) := hXD (h.smear_le_cenIn hJ hd)
  have hwX : d * x * d⁻¹ * x⁻¹ ∈ X := by
    have h1 : d * (x * l) * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hdX _).1 hxl
    have h2 := mul_mem h1 (inv_mem hxl)
    have e : d * (x * l) * d⁻¹ * (x * l)⁻¹ = d * x * d⁻¹ * x⁻¹ := by
      have hc : d⁻¹ * l = l * d⁻¹ := hdl.inv_left.eq
      calc d * (x * l) * d⁻¹ * (x * l)⁻¹ = d * x * (l * d⁻¹) * l⁻¹ * x⁻¹ := by group
        _ = d * x * (d⁻¹ * l) * l⁻¹ * x⁻¹ := by rw [hc]
        _ = d * x * d⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  have hwF : d * x * d⁻¹ * x⁻¹ ∈ CFSG.fittingSubgroupOf (smear J A) :=
    mul_mem (Thm210.fittingSubgroupOf_conj_mem hd hx) (inv_mem hx)
  have hne' : X ⊓ smear J A ≠ ⊥ := by
    intro hbot
    have : d * x * d⁻¹ * x⁻¹ ∈ X ⊓ smear J A :=
      Subgroup.mem_inf.2 ⟨hwX, Subgroup.map_subtype_le _ hwF⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact hdx this
  exact h.fittingSubgroupOf_smear_le_of_inf_ne_bot hJ (fun d hd => hXD (h.smear_le_cenIn hJ hd))
    hne'

theorem thm210g
    (h : SemisimpleAction p A G) {X : Subgroup Γ} (hXG : X ≤ G)
    (hX : Admits (cenIn G A ⊔ A) X) {J : Subgroup Γ} (hJ : J ∈ lcal G)
    (hns : ¬ Group.IsSolvable (projIn (lcal G) J X)) :
    projIn (lcal G) J X = J ∧ smear J A ≤ X := by
  have hG := h.isDirectProduct_lcal
  have hJs : IsSimpleGroup ↥J := (mem_lcal_iff.1 hJ).2.2.1
  have hXA : Admits A X := le_sup_right.trans hX
  have hXD : Admits (cenIn G A) X := le_sup_left.trans hX
  have hnn : ¬ Group.IsNilpotent ↥(projIn (lcal G) J X) := fun hn => by
    have := hn
    exact hns inferInstance
  have hF := thm210h h hXG hX hJ hnn
  have hGN : ∀ g ∈ G, g ∈ Subgroup.normalizer (orbitClosure J A : Set Γ) :=
    fun g hg => le_normalizer_orbitClosure h hJ hg
  have hX₁A : Admits A (X ⊓ orbitClosure J A) :=
    Thm210g.admits_inf hXA (Thm210.admits_orbitClosure J)
  have hX₁D : Admits (cenIn G A) (X ⊓ orbitClosure J A) :=
    Thm210g.admits_inf hXD fun d hd => hGN d (Thm210.mem_cenIn_iff.1 hd).1
  have hX₁X : Admits X (X ⊓ orbitClosure J A) :=
    Thm210g.admits_inf Subgroup.le_normalizer fun x hx => hGN x (hXG hx)
  have hF₁ : CFSG.fittingSubgroupOf (smear J A) ≤ X ⊓ orbitClosure J A :=
    le_inf hF ((Subgroup.map_subtype_le _).trans (smear_le_orbitClosure J A))
  have hP₁ne : projIn (lcal G) J (X ⊓ orbitClosure J A) ≠ ⊥ := by
    intro hbot
    apply h.fittingSubgroupOf_cenIn_ne_bot hJ
    rw [← h.projIn_fittingSubgroupOf_smear hJ, eq_bot_iff]
    exact (Thm210.projIn_mono J hF₁).trans hbot.le
  have hCP : cenIn J (norIn A J) ≤
      Subgroup.normalizer (projIn (lcal G) J (X ⊓ orbitClosure J A) : Set Γ) := by
    rw [← h.projIn_cenIn hJ]
    exact Thm210.le_normalizer_of_conj_mem (Thm210.projIn_conj_mem hG hJ fun d hd z hz =>
      (Subgroup.mem_normalizer_iff.1 (hX₁D hd) z).1 hz)
  have hXP : projIn (lcal G) J X ≤
      Subgroup.normalizer (projIn (lcal G) J (X ⊓ orbitClosure J A) : Set Γ) :=
    Thm210.le_normalizer_of_conj_mem (Thm210.projIn_conj_mem hG hJ fun x hx z hz =>
      (Subgroup.mem_normalizer_iff.1 (hX₁X hx) z).1 hz)
  have hJN : J ≤ Subgroup.normalizer (projIn (lcal G) J (X ⊓ orbitClosure J A) : Set Γ) := by
    rcases h.le_kJ_or_le_normalizer hJ (projIn_le J X) hCP hXP with h1 | h1
    · exfalso
      apply hns
      have := h.isSolvable_kJ hJ
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)
    · exact h1
  have hP₁J : projIn (lcal G) J (X ⊓ orbitClosure J A) = J := by
    rcases Thm210g.eq_bot_or_eq_of_le_normalizer hJs (projIn_le J _) hJN with h1 | h1
    · exact absurd h1 hP₁ne
    · exact h1
  refine ⟨le_antisymm (projIn_le J X) ?_,
    (h.smear_le_of_projIn_eq hJ inf_le_right hX₁A hX₁D hP₁J).trans inf_le_left⟩
  calc J = projIn (lcal G) J (X ⊓ orbitClosure J A) := hP₁J.symm
    _ ≤ projIn (lcal G) J X := Thm210.projIn_mono J inf_le_left

end CFSG.SignalizerFunctorTheorem.McBride.Near
