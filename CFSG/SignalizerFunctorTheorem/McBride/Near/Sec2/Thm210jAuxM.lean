module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_conj_le [Finite Γ] {H : Subgroup Γ} {g : Γ}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_normalizer_inf {H K : Subgroup Γ} {g : Γ} (hH : g ∈ Subgroup.normalizer (H : Set Γ))
    (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup Γ) : Set Γ) := by
  have hH' : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp hH
  have hK' : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hK
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  show (H ⊓ K).map (MulAut.conj g).toMonoidHom = H ⊓ K
  rw [Subgroup.map_inf_eq H K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hH', hK']

theorem mem_normalizer_of_conj_eq {P : Subgroup Γ} {c g : Γ}
    (h : ∀ x ∈ P, c * x * c⁻¹ = g * x * g⁻¹) (hg : g ∈ Subgroup.normalizer (P : Set Γ)) :
    c ∈ Subgroup.normalizer (P : Set Γ) := by
  have hg' : P.map (MulAut.conj g).toMonoidHom = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  show P.map (MulAut.conj c).toMonoidHom = P
  refine Eq.trans ?_ hg'
  ext y
  simp only [Subgroup.mem_map]
  refine exists_congr fun x => and_congr_right fun hx => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h x hx]

theorem mem_normalizer_sup [Finite Γ] {H K : Subgroup Γ} {g : Γ}
    (hH : g ∈ Subgroup.normalizer (H : Set Γ)) (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup Γ) : Set Γ) := by
  have hH' : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp hH
  have hK' : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hK
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  show (H ⊔ K).map (MulAut.conj g).toMonoidHom = H ⊔ K
  rw [Subgroup.map_sup, hH', hK']

theorem sectionCentralizer_conj_mem {X Y : Subgroup Γ} {q g : Γ}
    (hqX : q ∈ Subgroup.normalizer (X : Set Γ)) (hqY : q ∈ Subgroup.normalizer (Y : Set Γ))
    (hg : g ∈ sectionCentralizer X Y) : q * g * q⁻¹ ∈ sectionCentralizer X Y := by
  obtain ⟨hgX, hgY, hgc⟩ := mem_sectionCentralizer_iff.mp hg
  refine mem_sectionCentralizer_iff.mpr ⟨?_, ?_, fun y hy => ?_⟩
  · exact mul_mem (mul_mem hqX hgX) (inv_mem hqX)
  · exact mul_mem (mul_mem hqY hgY) (inv_mem hqY)
  · have hy' : q⁻¹ * y * q ∈ Y := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hqY) y).mp hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hqX _).mp (hgc _ hy')
    have h2 : q * ⁅g, q⁻¹ * y * q⁆ * q⁻¹ = ⁅q * g * q⁻¹, y⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [h2] at h1

theorem sectionCentralizer_le_sup [Finite Γ] {X Y V : Subgroup Γ} (hXY : X ≤ Y) (hVY : V ≤ Y) :
    sectionCentralizer X Y ≤ sectionCentralizer X (X ⊔ V) := by
  intro g hg
  obtain ⟨hgX, hgY, hgc⟩ := mem_sectionCentralizer_iff.mp hg
  have hgXV : g ∈ Subgroup.normalizer ((X ⊔ V : Subgroup Γ) : Set Γ) := by
    refine mem_normalizer_of_conj_le fun x hx => ?_
    have hle : (X ⊔ V).map (MulAut.conj g).toMonoidHom ≤ X ⊔ V := by
      rw [Subgroup.map_sup]
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · obtain ⟨y, hy, rfl⟩ := hz
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hgX y).mp hy)
      · obtain ⟨y, hy, rfl⟩ := hz
        have h2 : g * y * g⁻¹ = ⁅g, y⁆ * y := by
          simp only [commutatorElement_def]
          group
        change g * y * g⁻¹ ∈ _
        rw [h2]
        exact mul_mem (Subgroup.mem_sup_left (hgc y (hVY hy))) (Subgroup.mem_sup_right hy)
    exact hle ⟨x, hx, rfl⟩
  exact mem_sectionCentralizer_iff.mpr ⟨hgX, hgXV, fun y hy => hgc y (sup_le hXY hVY hy)⟩

theorem isSolvable_sup_of_le_normalizer {T D : Subgroup Γ}
    (hD : D ≤ Subgroup.normalizer (T : Set Γ)) (hT : Group.IsSolvable T)
    (hD' : Group.IsSolvable D) : Group.IsSolvable ↥(D ⊔ T) := by
  have hnorm : (T.subgroupOf (D ⊔ T)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hD
  have hnormD : (T.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hD
  have hker : (QuotientGroup.mk' (T.subgroupOf (D ⊔ T))).ker ≤
      (T.subgroupOf (D ⊔ T)).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  let e₁ := Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ D ⊔ T)
  have h1 : Group.IsSolvable ↥(T.subgroupOf (D ⊔ T)) :=
    Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  let e₂ := QuotientGroup.quotientInfEquivProdNormalizerQuotient D T hD
  have h2 : Group.IsSolvable (↥(D ⊔ T) ⧸ T.subgroupOf (D ⊔ T)) := by
    have : Group.IsSolvable (↥D ⧸ T.subgroupOf D) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact Group.isSolvable_of_surjective (f := e₂.toMonoidHom) e₂.surjective
  exact Group.isSolvable_of_ker_le_range _ _ hker

section Coordinates

variable [Finite Γ] {S : Set (Subgroup Γ)} {L : Subgroup Γ}

theorem coord_inv_mul_mem (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S) {y : Γ}
    (hy : y ∈ L) : ((hL.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹ * y ∈ sSup (S \ {J}) := by
  have hcL : ((hL.coord hJ ⟨y, hy⟩ : J) : Γ) ∈ L := hL.le hJ (hL.coord hJ ⟨y, hy⟩).2
  rw [← hL.coord_eq_one_iff hJ ⟨((hL.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹ * y, mul_mem (inv_mem hcL) hy⟩]
  have : (⟨((hL.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹ * y, mul_mem (inv_mem hcL) hy⟩ : L) =
      ⟨((hL.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹, inv_mem hcL⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul]
  have h1 : hL.coord hJ ⟨((hL.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹, inv_mem hcL⟩ =
      (hL.coord hJ ⟨y, hy⟩)⁻¹ :=
    Subtype.ext (hL.coord_of_mem hJ (inv_mem (hL.coord hJ ⟨y, hy⟩).2))
  rw [h1, inv_mul_cancel]

theorem coord_eq_of_inv_mul_mem (hL : IsDirectProduct S L) {J : Subgroup Γ} (hJ : J ∈ S)
    {y c : Γ} (hy : y ∈ L) (hc : c ∈ L) (h : c⁻¹ * y ∈ sSup (S \ {J})) :
    hL.coord hJ ⟨y, hy⟩ = hL.coord hJ ⟨c, hc⟩ := by
  have h1 : hL.coord hJ ⟨c⁻¹ * y, mul_mem (inv_mem hc) hy⟩ = 1 :=
    (hL.coord_eq_one_iff hJ _).mpr h
  have h2 : (⟨y, hy⟩ : L) = ⟨c, hc⟩ * ⟨c⁻¹ * y, mul_mem (inv_mem hc) hy⟩ :=
    Subtype.ext (by simp)
  rw [h2, map_mul, h1, mul_one]

end Coordinates

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210
