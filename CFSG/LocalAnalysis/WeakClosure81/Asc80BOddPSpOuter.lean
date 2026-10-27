module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.Models.Blueprint
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpField
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpIsotropic
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpDiag
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm)

private theorem mem_of_congr_eq_conj {G : Type} [Group G] {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) {X : Type} [Group X] (ψ : ↥L ≃* X) {t : G}
    {g' : X} (h : MulAut.congr ψ (MulAut.conjNormal t) = MulAut.conj g') : t ∈ L := by
  set l₀ : ↥L := ψ.symm g' with hl₀
  have hσx : ∀ x : ↥L, MulAut.conjNormal t x = l₀ * x * l₀⁻¹ := by
    intro x
    have h1 : ψ (MulAut.conjNormal t x) = MulAut.congr ψ (MulAut.conjNormal t) (ψ x) := by
      simp [MulAut.congr_apply]
    rw [h, MulAut.conj_apply] at h1
    apply ψ.injective
    rw [h1, map_mul, map_mul, map_inv, hl₀, MulEquiv.apply_symm_apply]
  have hc : (l₀ : G)⁻¹ * t ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (hσx ⟨x, hx⟩)
    rw [MulAut.conjNormal_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc x * ((l₀ : G)⁻¹ * t) = (l₀ : G)⁻¹ * ((l₀ : G) * x * (l₀ : G)⁻¹) * t := by group
      _ = (l₀ : G)⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
      _ = (l₀ : G)⁻¹ * t * x := by group
  rw [hC, Subgroup.mem_bot] at hc
  have ht : t = l₀ := by
    calc t = (l₀ : G) * ((l₀ : G)⁻¹ * t) := by group
      _ = l₀ := by rw [hc, mul_one]
  rw [ht]
  exact l₀.2

@[expose] def SeitzFourSp4DiagAniso : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ E : Subgroup (MulAut (StatedProj (StatedSp 2 F))), IsElemAbelian 2 E → Nat.card E = 4 →
    E ≤ spLinearAutGroup 2 F →
    ¬ E ≤ (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range →
    (∀ W : Submodule F (Fin 2 ⊕ Fin 2 → F), (∀ x ∈ W, ∀ y ∈ W, spForm 2 F x y = 0) →
      (∀ A : gsp 2 F, conjAut 2 F A ∈ E →
        ∀ w ∈ W, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W) →
      W = ⊥) →
    PlaneGen E

theorem seitzFourOuter_psp_of_sp4DiagAniso (hD : SeitzFourSp4DiagAniso) :
    SeitzFourOuter fun X _ => ∃ n p f : ℕ, 2 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSp n p f := by
  intro G _ _ L E hLn hLs hnab ⟨n, p, f, hn, hp2, hm⟩ hC hE h4 hEL
  classical
  have : L.Normal := hLn
  have hm' : CFSG.Models.LieModel ↥L .PSp n p f := hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) hm'
  have hKchar : ringChar K ≠ 2 := by
    have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hp hf hK
    rw [ringChar.eq K p]
    exact hp2
  set E' : Subgroup (MulAut ↥L) := E.map (MulAut.conjNormal : G →* MulAut ↥L) with hE'
  have hE' : IsElemAbelian 2 E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE _
  have h4' : Nat.card E' = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective
      (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
    norm_num
  set E'' : Subgroup (MulAut (StatedProj (StatedSp n K))) :=
    E'.map (MulAut.congr eS).toMonoidHom with hE''
  have hE'' : IsElemAbelian 2 E'' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE' _
  have h4'' : Nat.card E'' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr eS).injective, h4']
    norm_num
  apply iSup_centralizer_eq_of_seitzHyperGamma hC h4
  rw [(planeGen_iff_seitzHyperGamma Nat.prime_two h4').symm, ← planeGen_map_congr eS E']
  change PlaneGen E''
  by_cases hσ : ∃ e ∈ E'', e ∉ spLinearAutGroup n K
  · exact planeGen_of_not_spLinear hn hKchar hE'' h4'' hσ
  · push Not at hσ
    have hlin : E'' ≤ spLinearAutGroup n K := hσ
    have hout : ¬ E'' ≤ (MulAut.conj : StatedProj (StatedSp n K) →* MulAut _).range := by
      intro hrange
      apply hEL
      intro t ht
      have ht' : MulAut.conjNormal t ∈ E' := Subgroup.mem_map_of_mem _ ht
      have ht'' : MulAut.congr eS (MulAut.conjNormal t) ∈ E'' := Subgroup.mem_map_of_mem _ ht'
      obtain ⟨g', hg'⟩ := hrange ht''
      exact mem_of_congr_eq_conj hC eS hg'.symm
    by_cases hiso : ∃ W : Submodule K (Fin n ⊕ Fin n → K), W ≠ ⊥ ∧
        (∀ x ∈ W, ∀ y ∈ W, spForm n K x y = 0) ∧
        ∀ A : gsp n K, conjAut n K A ∈ E'' →
          ∀ w ∈ W, ((A : GL (Fin n ⊕ Fin n) K) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w ∈ W
    · obtain ⟨W, hW0, hW, hst⟩ := hiso
      exact planeGen_of_isotropic_sp hKchar hE'' h4'' hlin W hW0 hW hst
    · by_cases hn3 : 3 ≤ n
      · obtain ⟨W, hW0, hW, hst⟩ :=
          exists_isotropic_of_spLinear_of_not_inner hn3 hKchar hE'' h4'' hlin hout
        exfalso
        exact hiso ⟨W, hW0, hW, hst⟩
      · have hn2 : n = 2 := by omega
        subst hn2
        refine hD K hKchar E'' hE'' h4'' hlin hout ?_
        intro W hW hst
        by_contra hW0
        exact hiso ⟨W, hW0, hW, hst⟩

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
