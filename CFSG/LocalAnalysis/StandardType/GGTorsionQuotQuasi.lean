module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionQuotQuasi

private theorem tqq_ker_comp_mk'_center {X R : Type*} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) :
    (((θ : X ⧸ Subgroup.center X →* R).comp
        (QuotientGroup.mk' (Subgroup.center X))).ker) = Subgroup.center X := by
  rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective θ),
    QuotientGroup.ker_mk']

private theorem tqq_map_commutator_eq {G H : Type*} [Group G] [Group H]
    (ρ : G →* H) (hρ : Function.Surjective ρ) :
    (commutator G).map ρ = commutator H := by
  rw [commutator_def G, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective ρ hρ,
    commutator_def H]

private theorem tqq_center_comap {G H : Type*} [Group G] [Group H]
    (ρ : G →* H) (hρ : Function.Surjective ρ) (hG : commutator G = ⊤)
    (hK : ρ.ker ≤ Subgroup.center G) :
    (Subgroup.center H).comap ρ = Subgroup.center G := by
  apply le_antisymm
  · let N : Subgroup G := (Subgroup.center H).comap ρ
    change N ≤ Subgroup.center G
    have h1 : ⁅N, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G := by
      rw [Subgroup.commutator_le]
      intro n hn g _
      apply hK
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hn) (ρ g)).symm)
    have h2 : ⁅⁅N, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
      rw [eq_bot_iff]
      calc ⁅⁅N, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ ≤ ⁅Subgroup.center G, (⊤ : Subgroup G)⁆ :=
            Subgroup.commutator_mono_left h1
        _ = ⊥ := Subgroup.commutator_center_left (⊤ : Subgroup G)
    have h3 : ⁅⁅(⊤ : Subgroup G), N⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (⊤ : Subgroup G) N]
      exact h2
    have h4 : ⁅(⊤ : Subgroup G), N⁆ = ⊥ := by
      have h := Subgroup.commutator_commutator_eq_bot_of_rotate
        (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G)) (H₃ := N) h3 h2
      rw [← commutator_def G, hG] at h
      exact h
    intro n hn
    exact (Subgroup.commutator_top_left_eq_bot_iff_le_center.mp h4) hn
  · intro g hg
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro h
    obtain ⟨g', rfl⟩ := hρ h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg g']

theorem ggTorsion_centerQuot_image_equiv {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {J : Subgroup X} (hJ : commutator ↥J = ⊤) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X)))) ⧸
        Subgroup.center ↥(J.map ((θ : X ⧸ Subgroup.center X →* R).comp
          (QuotientGroup.mk' (Subgroup.center X))))) := by
  let π : X →* R := (θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))
  let Jb : Subgroup R := J.map π
  let ρ : ↥J →* ↥Jb := π.subgroupMap J
  have hρ : Function.Surjective ρ := MonoidHom.subgroupMap_surjective π J
  have hρapply : ∀ j : ↥J, (ρ j : R) = π (j : X) := fun j => rfl
  have hK : ρ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    have hπ : π (j : X) = 1 := by
      have h := congrArg Subtype.val hj
      rw [hρapply j] at h
      simpa using h
    have hx : (j : X) ∈ Subgroup.center X := by
      rw [← tqq_ker_comp_mk'_center θ, MonoidHom.mem_ker]
      exact hπ
    exact Subgroup.mem_center_iff.mp hx (j' : X)
  have hcenter : (Subgroup.center ↥Jb).comap ρ = Subgroup.center ↥J :=
    tqq_center_comap ρ hρ hJ hK
  let σ : ↥J →* ↥Jb ⧸ Subgroup.center ↥Jb :=
    (QuotientGroup.mk' (Subgroup.center ↥Jb)).comp ρ
  have hσ : Function.Surjective σ :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥Jb)).comp hρ
  have hkerσ : σ.ker = Subgroup.center ↥J := by
    have h := MonoidHom.comap_ker (QuotientGroup.mk' (Subgroup.center ↥Jb)) ρ
    rw [QuotientGroup.ker_mk'] at h
    rw [← h]
    exact hcenter
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerσ).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective σ hσ)⟩

theorem ggTorsion_quasisimple_image {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {J : Subgroup X} (hJ : Assembly.IsQuasisimple J) :
    Assembly.IsQuasisimple
      (J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X)))) := by
  let π : X →* R := (θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))
  let Jb : Subgroup R := J.map π
  change Assembly.IsQuasisimple Jb
  let ρ : ↥J →* ↥Jb := π.subgroupMap J
  have hρ : Function.Surjective ρ := MonoidHom.subgroupMap_surjective π J
  constructor
  · rw [← tqq_map_commutator_eq ρ hρ, hJ.1, Subgroup.map_top_of_surjective ρ hρ]
  · obtain ⟨e⟩ := ggTorsion_centerQuot_image_equiv θ hJ.1
    exact (MulEquiv.isSimpleGroup_congr e).mp hJ.2

end TorsionQuotQuasi

end CFSG.StandardType
