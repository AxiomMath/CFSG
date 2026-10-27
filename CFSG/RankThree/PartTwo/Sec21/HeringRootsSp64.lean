module

public import CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64Transport
public import CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64Std1

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringRootsSp64

open CFSG.RankThree.PartTwo.Sec21.TablesSp64 CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem components_std0' {c : Sp} (hc : c = δ (Multiplicative.ofAdd (std 0)))
    {Y : Subgroup (Subgroup.centralizer ({c} : Set Sp))} (hY : CFSG.IsComponent Y) :
    Y.map (Subgroup.centralizer ({c} : Set Sp)).subtype = S4 := by
  subst hc
  exact components_std0 hY

theorem components_std1' {c : Sp} (hc : c = δ (Multiplicative.ofAdd (std 1)))
    {Y : Subgroup (Subgroup.centralizer ({c} : Set Sp))} (hY : CFSG.IsComponent Y) :
    Y.map (Subgroup.centralizer ({c} : Set Sp)).subtype = S2 ∨
      Y.map (Subgroup.centralizer ({c} : Set Sp)).subtype = Levi2 := by
  subst hc
  exact components_std1 hY

theorem components_std2' {c : Sp} (hc : c = δ (Multiplicative.ofAdd (std 2)))
    {Y : Subgroup (Subgroup.centralizer ({c} : Set Sp))} (hY : CFSG.IsComponent Y) :
    Y.map (Subgroup.centralizer ({c} : Set Sp)).subtype = leviSL3.range := by
  subst hc
  exact components_std2 hY

theorem map_reindexSp_inv {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3)
    (Z : Subgroup Sp) :
    (Z.map (reindexSp π (Jm_submatrix_of_mem hπ)).toMonoidHom).map
      (reindexSp π⁻¹ (Jm_submatrix_of_mem (inv_mem hπ))).toMonoidHom = Z := by
  rw [Subgroup.map_map]
  have h : (reindexSp π⁻¹ (Jm_submatrix_of_mem (inv_mem hπ))).toMonoidHom.comp
      (reindexSp π (Jm_submatrix_of_mem hπ)).toMonoidHom = MonoidHom.id Sp := by
    ext g : 1
    apply mat_injective
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, mat_reindexSp,
      mat_reindexSp, Matrix.submatrix_submatrix]
    ext x y
    simp
  rw [h, Subgroup.map_id]

theorem fin3_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

theorem rootModel_Sp : RootModel A0 := by
  intro D hrefl hconj hcl b hbA hb1 Y hY
  have hs2 := sAut_s2_mem hrefl hconj hcl
  have hρ := sAut_rho01_mem hrefl hconj hcl
  obtain ⟨v, rfl⟩ : ∃ v : Fin 3 → ZMod 3, b = δ (Multiplicative.ofAdd v) := by
    obtain ⟨y, hy⟩ : b ∈ δ.range := hbA
    exact ⟨Multiplicative.toAdd y, by rw [← hy, ofAdd_toAdd]⟩
  have hv : v ≠ 0 := by
    rintro rfl
    apply hb1
    rw [show Multiplicative.ofAdd (0 : Fin 3 → ZMod 3) = 1 from rfl, map_one]
  obtain ⟨σ, s, i, hσ⟩ := exists_flip_perm_std v hv
  have hπ : sgnW σ s ∈ signedPermGroup 3 := sgnW_mem σ s
  have hφb : reindexSp (sgnW σ s) (Jm_submatrix_of_mem hπ) (δ (Multiplicative.ofAdd v)) =
      δ (Multiplicative.ofAdd (std i)) := by
    apply reindexSp_δ (w := std i)
    rw [ext_comp_signed hπ v, wv_sgnW]
    exact congrArg ext hσ
  obtain ⟨Y', hY', hYY'⟩ :=
    exists_component_map (reindexSp (sgnW σ s) (Jm_submatrix_of_mem hπ)) _ hY
  have hgood : Good D ((Y.map (Subgroup.centralizer
      ({δ (Multiplicative.ofAdd v)} : Set Sp)).subtype).map
        (reindexSp (sgnW σ s) (Jm_submatrix_of_mem hπ)).toMonoidHom) := by
    rw [← hYY']
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [components_std0' hφb hY']
      exact good_S4 hs2
    · rcases components_std1' hφb hY' with h | h
      · rw [h]
        exact good_S2 hs2
      · rw [h]
        exact good_Levi2 hρ
    · rw [components_std2' hφb hY']
      exact good_S3 hρ
  have h := good_map hconj (inv_mem hπ) hgood
  rwa [map_reindexSp_inv hπ] at h

theorem exists_Phi_Sp {G : Type} [Group G] {I A : Subgroup G} (hAI : A ≤ I)
    (hAe : IsElemAbelian 3 A) (e : I ≃* projSp 3 (GaloisField 2 2)) (hA : Nat.card A = 3 ^ 3) :
    ∃ Φ : I ≃* Sp, (A.subgroupOf I).map Φ.toMonoidHom = A0 := by
  set e' : I ≃* Sp := e.trans equivSp with he'
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  refine ⟨e'.trans (MulAut.conj x), ?_⟩
  rw [← hx, Subgroup.map_map]
  rfl

end HeringRootsSp64

theorem terminalRootComponentsSp64 :
    ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
      (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) →
      ∀ D : Set (MulAut A), (∀ φ ∈ D, IsReflectionOn φ) →
        (∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D) → Subgroup.closure D = starOf A I →
        ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
          ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
            CFSG.IsComponent X → ∃ φ ∈ D, ∀ P : Subgroup G, P ≤ I →
              P ≤ Subgroup.centralizer (fixedInG A φ : Set G) → Group.IsPerfect P →
                P ≤ X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype := by
  intro G _ _ I A hAI hAe hT D hrefl hconj hcl B hBA hB3 X hX
  obtain ⟨⟨e⟩, hA⟩ := hT
  obtain ⟨Φ, hΦA⟩ := HeringRootsSp64.exists_Phi_Sp hAI hAe e hA
  exact HeringRootsSp64.root_of_model hAI Φ hΦA HeringRootsSp64.rootModel_Sp D hrefl hconj hcl B
    hBA hB3 X hX

end CFSG.RankThree.PartTwo.Sec21

end
