module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdLayer

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

private theorem le_of_map_le (hker : ψ.ker ≤ Subgroup.center L') {Y J : Subgroup L'}
    (hY : ⁅Y, Y⁆ = Y) (hle : Y.map ψ ≤ J.map ψ) : Y ≤ J := by
  have h := CFSG.RankThree.PartOne.S15K.le_iSup_of_isPerfect_of_map_le (ι := Unit) hker
    (Q := fun _ => J) (F := fun _ => J.map ψ) (fun _ => rfl) hY (by rwa [iSup_const])
  rwa [iSup_const] at h

theorem commutator_eq_self_of_isComponentOf {J K : Subgroup L'} (hJ : IsComponentOf J K) :
    ⁅J, J⁆ = J :=
  Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩

theorem eq_of_map_eq (hker : ψ.ker ≤ Subgroup.center L') {J₁ J₂ : Subgroup L'}
    (h₁ : ⁅J₁, J₁⁆ = J₁) (h₂ : ⁅J₂, J₂⁆ = J₂) (h : J₁.map ψ = J₂.map ψ) : J₁ = J₂ :=
  le_antisymm (le_of_map_le hker h₁ h.le) (le_of_map_le hker h₂ h.ge)

theorem isComponentOf_map_iff (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {φ : MulAut R} (hφ : ∀ l, φ (ψ l) = ψ (a l)) {J : Subgroup L'}
    (hJ : ⁅J, J⁆ = J) : IsComponentOf J (ggFix a) ↔ IsComponentOf (J.map ψ) (ggFix φ) := by
  have hc : ∀ x, ψ (a x) = φ (ψ x) := fun x => (hφ x).symm
  refine ⟨LayerCC.isComponentOf_map_ggFix hψ hker hc, fun hM => ?_⟩
  obtain ⟨hJ', hmap⟩ := LayerCC.isComponentOf_commutator_comap_ggFix hψ hker hc hM
  rwa [eq_of_map_eq hker (commutator_eq_self_of_isComponentOf hJ') hJ hmap] at hJ'

theorem exists_isComponentOf_map_eq (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'} {φ : MulAut R}
    (hφ : ∀ l, φ (ψ l) = ψ (a l)) {M : Subgroup R} (hM : IsComponentOf M (ggFix φ)) :
    ∃ J : Subgroup L', IsComponentOf J (ggFix a) ∧ J.map ψ = M :=
  ⟨_, LayerCC.isComponentOf_commutator_comap_ggFix hψ hker (fun x => (hφ x).symm) hM⟩

theorem mapsTo_map_iff (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'} {φ : MulAut R}
    (hφ : ∀ l, φ (ψ l) = ψ (a l)) {J : Subgroup L'} (hJ : ⁅J, J⁆ = J) :
    (∀ l ∈ J, a l ∈ J) ↔ ∀ m ∈ J.map ψ, φ m ∈ J.map ψ := by
  constructor
  · rintro ha _ ⟨l, hl, rfl⟩
    exact ⟨a l, ha l hl, (hφ l).symm⟩
  · intro hb l hl
    have hY : ⁅J.map a.toMonoidHom, J.map a.toMonoidHom⁆ = J.map a.toMonoidHom := by
      rw [← Subgroup.map_commutator, hJ]
    have hle : (J.map a.toMonoidHom).map ψ ≤ J.map ψ := by
      rintro _ ⟨_, ⟨l', hl', rfl⟩, rfl⟩
      have h := hb (ψ l') ⟨l', hl', rfl⟩
      rw [hφ] at h
      exact h
    exact le_of_map_le hker hY hle ⟨l, hl, rfl⟩

theorem fixes_map_iff (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'} {φ : MulAut R}
    (hφ : ∀ l, φ (ψ l) = ψ (a l)) {J : Subgroup L'} (hJ : ⁅J, J⁆ = J) :
    (∀ l ∈ J, a l = l) ↔ ∀ m ∈ J.map ψ, φ m = m := by
  constructor
  · rintro ha _ ⟨l, hl, rfl⟩
    rw [hφ, ha l hl]
  · intro hb l hl
    have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker
      (Subgroup.isPerfect_iff.2 hJ) ((a : L' →* L').comp J.subtype) J.subtype (fun u => by
        change ψ (a (u : L')) = ψ (u : L')
        rw [← hφ]
        exact hb _ ⟨u, u.2, rfl⟩)
    exact key ⟨l, hl⟩

theorem induced_mul {a₁ a₂ : MulAut L'} {φ₁ φ₂ : MulAut R} (h₁ : ∀ l, φ₁ (ψ l) = ψ (a₁ l))
    (h₂ : ∀ l, φ₂ (ψ l) = ψ (a₂ l)) (l : L') : (φ₁ * φ₂) (ψ l) = ψ ((a₁ * a₂) l) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, h₂, h₁]

theorem induced_eq_one_iff (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hL : commutator L' = ⊤) {a : MulAut L'} {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) :
    φ = 1 ↔ a = 1 := by
  constructor
  · rintro rfl
    exact TypeA.mulAut_eq_of_forall ψ hker hL fun l => by rw [← h]; rfl
  · rintro rfl
    exact TypeA.induced_unique ψ hψ h fun _ => rfl

theorem induced_commute_iff (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hL : commutator L' = ⊤) {a₁ a₂ : MulAut L'} {φ₁ φ₂ : MulAut R}
    (h₁ : ∀ l, φ₁ (ψ l) = ψ (a₁ l)) (h₂ : ∀ l, φ₂ (ψ l) = ψ (a₂ l)) :
    φ₁ * φ₂ = φ₂ * φ₁ ↔ a₁ * a₂ = a₂ * a₁ := by
  constructor
  · intro hc
    apply TypeA.mulAut_eq_of_forall ψ hker hL
    intro l
    rw [← induced_mul h₁ h₂, ← induced_mul h₂ h₁, hc]
  · intro hc
    apply TypeA.induced_unique ψ hψ (induced_mul h₁ h₂)
    rw [hc]
    exact induced_mul h₂ h₁

theorem induced_mem_zpowers_iff (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hL : commutator L' = ⊤) {a a₀ : MulAut L'}
    {φ φ₀ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) (h₀ : ∀ l, φ₀ (ψ l) = ψ (a₀ l)) :
    φ ∈ Subgroup.zpowers φ₀ ↔ a ∈ Subgroup.zpowers a₀ := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, TypeA.mulAut_eq_of_forall ψ hker hL fun l => ?_⟩
    rw [← TableBUD.induced_zpow h₀ k, h]
  · rintro ⟨k, rfl⟩
    exact ⟨k, TypeA.induced_unique ψ hψ (TableBUD.induced_zpow h₀ k) h⟩

theorem inducedSub_subset (hψ : Function.Surjective ψ) {I : Set (MulAut R)}
    {A : Subgroup (MulAut L')} (hA : ∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l)) :
    ∀ φ ∈ TypeA.inducedSub ψ A, φ ∈ I := by
  intro φ hφ
  obtain ⟨a, ha, h⟩ := TypeA.mem_inducedSub.1 hφ
  obtain ⟨φ', hφ'I, h'⟩ := hA a ha
  rwa [TypeA.induced_unique ψ hψ h h']

end CFSG.StandardType.SCFourCover

end
