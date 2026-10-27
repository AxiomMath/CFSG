module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Off

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X S Z Z₀ : Subgroup G} {θ : ↥X →* Perm (Fin 5)}

theorem pu4_core (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X)
    (hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A)
    (h4 : (Z ⊓ Subgroup.centralizer (thompsonJ S : Set G)).relIndex Z ≤ 4)
    (hgen : ∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X)
    (hidx : 16 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z) :
    Z ≤ thompsonJ S ∧
      Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) ≤ omegaOneCenterOf (thompsonJ S) ∧
      ∀ r ∈ pResidualOf 2 X ⊓ pCoreOf 2 X, ∀ w ∈ omegaOneCenterOf (thompsonJ S), r * w = w * r := by
  set J := thompsonJ S with hJdef
  set L := pResidualOf 2 X with hL
  set Q := pCoreOf 2 X with hQ
  set W := omegaOneCenterOf J with hW
  have hSX : S ≤ X := h.le_self
  have hJS : J ≤ S := thompsonJ_le_self S
  have hJX : J ≤ X := hJS.trans hSX
  have hLX : L ≤ X := pResidualOf_le_self X
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_pResidualOf X
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  obtain ⟨hmS, -, -, hWWQ⟩ := offender_equality h hA₀ (hall A₀ hA₀ hA₀Q)
  have hZJ : Z ≤ J := le_sup_right.trans (le_thompsonJ_of_isMax' hmS)
  obtain ⟨g₀, hg₀, hgen'⟩ := hgen
  obtain ⟨hIeq, hLI⟩ := conjJoin_eq_sup_cj h hg₀ hgen'
  set I := conjJoin X J with hI
  set M := W ⊔ Z with hM
  have hIN : ∀ i ∈ I, i ∈ Subgroup.normalizer (M : Set G) := fun i hi =>
    conjJoin_le_normalizer_sup h hall hWWQ hi
  have hWJ : W ≤ J ⊓ Subgroup.centralizer (J : Set G) := omegaOneCenterOf_le_inf J
  have hWX : W ≤ X := hWJ.trans (inf_le_left.trans hJX)
  have hMX : M ≤ X := sup_le hWX (h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
  have hZM : Z ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (Z : Set G) := hMX.trans h.normal
  have hrJ : (M ⊓ Subgroup.centralizer (J : Set G)).relIndex M ≤ 4 := by
    set C := M ⊓ Subgroup.centralizer (J : Set G) with hC
    have hWC : W ≤ C := le_inf le_sup_left (hWJ.trans inf_le_right)
    have hMC : M ≤ Z ⊔ C := sup_le (hWC.trans le_sup_right) le_sup_left
    have h1 : C.relIndex M = (Z ⊓ C).relIndex Z :=
      relIndex_eq_of_le_sup hZM inf_le_left (inf_le_left.trans hMN) hMC
    have h2 : Z ⊓ C = Z ⊓ Subgroup.centralizer (J : Set G) := by
      rw [hC, ← inf_assoc, inf_of_le_left hZM]
    rw [h1, h2]
    exact h4
  have hg₀N : g₀ ∈ Subgroup.normalizer (M : Set G) := hIN g₀ (hLI hg₀)
  have hcount : (M ⊓ Subgroup.centralizer (I : Set G)).relIndex M ≤ 16 := by
    rw [hIeq]
    exact (relIndex_inf_centralizer_sup_cj_le hg₀N).trans
      ((Nat.pow_le_pow_left hrJ 2).trans (by norm_num))
  set D := M ⊓ Subgroup.centralizer (L : Set G) with hD
  have hDM : D ≤ M := inf_le_left
  have hDZ : D ≤ Subgroup.normalizer (Z : Set G) := hDM.trans hMN
  have hDle : D.relIndex M ≤ 16 := by
    refine le_trans (relIndex_le_of_le M ?_) hcount
    exact inf_le_inf_left M (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLI))
  obtain ⟨hMD, -⟩ := eq_sup_centralizer_of_count hZM hMN hDle hidx
  refine ⟨hZJ, ?_, ?_⟩
  · intro z hz
    refine Subgroup.subset_closure ⟨⟨hZJ hz.1, hz.2⟩, ?_⟩
    have := h.elemAbelian.2 z hz.1
    exact this
  · intro r hr w hw
    obtain ⟨z, hz, c, hc, hwzc⟩ := mem_sup_of_le_normalizer (N := Z) (K := D) hDZ
      (hMD (le_sup_left (a := W) (b := Z) hw))
    have hrz : z * r = r * z := Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hr.2) z hz
    have hrc : r * c = c * r := Subgroup.mem_centralizer_iff.mp hc.2 r hr.1
    rw [hwzc]
    calc r * (z * c) = (r * z) * c := (mul_assoc _ _ _).symm
      _ = (z * r) * c := by rw [hrz]
      _ = z * (r * c) := mul_assoc _ _ _
      _ = z * (c * r) := by rw [hrc]
      _ = (z * c) * r := (mul_assoc _ _ _).symm

theorem baum_image_le (h : PushHyp X S Z) (hF : OrthFacts X S Z Z₀ θ)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X)
    (hFW : Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) ≤ omegaOneCenterOf (thompsonJ S))
    {s : G} (hsX : s ∈ X) (hsB : s ∈ baum S) : θ ⟨s, hsX⟩ ∈ S5That := by
  by_contra hσT
  set J := thompsonJ S with hJdef
  have hJX : J ≤ X := (thompsonJ_le_self S).trans h.le_self
  obtain ⟨hFeq, hF4⟩ := centralizer_thompsonJ h hF hJ
  have hsS : s ∈ S := hsB.1
  have hsC : s ∈ Subgroup.centralizer (omegaOneCenterOf J : Set G) := hsB.2
  have hσD : θ ⟨s, hsX⟩ ∈ S5Syl := by
    rw [← hF.map_S]
    exact ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  set A' := J ⊔ Subgroup.zpowers s with hA'
  have hA'X : A' ≤ X := sup_le hJX ((Subgroup.zpowers_le).mpr hsX)
  have hFA : fixSecIn A' Z₀ Z = Z ⊓ Subgroup.centralizer (J : Set G) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzZ, hzA⟩ := (hF.mem_fix _ z).mp hz
      rw [hFeq]
      exact (hF.mem_fix _ z).mpr ⟨hzZ, fun a ha => hzA a (Subgroup.mem_sup_left ha)⟩
    · intro z hz
      refine (hF.mem_fix _ z).mpr ⟨hz.1, fun a ha => ?_⟩
      have hzW : z ∈ omegaOneCenterOf J := hFW hz
      have hJz : J ≤ Subgroup.centralizer ({z} : Set G) := by
        intro j hj
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hz.2 j hj
      have hsz : Subgroup.zpowers s ≤ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hsC z hzW).symm
      have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (sup_le hJz hsz ha)
      have : a * z * a⁻¹ * z⁻¹ = 1 := by rw [haz]; group
      rw [this]
      exact one_mem _
  have h1 := hF.relIndex_fix A' hA'X
  rw [hFA, hF4] at h1
  have hcard : Nat.card (fixW orth ((A'.subgroupOf X).map θ)) ≤ 2 := by
    obtain ⟨j₁, hj₁, hj₁J, hj₁θ⟩ := exists_mem_thompsonJ h hF hJ (σ := swap 0 2)
      (by rw [mem_S5That_iff]; unfold S5ThatF; decide +kernel)
    obtain ⟨j₂, hj₂, hj₂J, hj₂θ⟩ := exists_mem_thompsonJ h hF hJ (σ := swap 1 3)
      (by rw [mem_S5That_iff]; unfold S5ThatF; decide +kernel)
    refine card_fixW_le_two (σ := θ ⟨s, hsX⟩) ?_ ?_ hσD hσT ?_
    · exact ⟨⟨j₁, hj₁⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hj₁J), hj₁θ⟩
    · exact ⟨⟨j₂, hj₂⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hj₂J), hj₂θ⟩
    · exact ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)),
        rfl⟩
  have h16 := OrthFacts.index_mul_card ((A'.subgroupOf X).map θ)
  rw [← h1] at h16
  omega

end CFSG.Quasithin.F53Push
