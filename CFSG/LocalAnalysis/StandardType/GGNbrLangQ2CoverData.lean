module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

@[expose] def q2CoverMap {X R : Type} [Group X] [Group R] (θ : X ⧸ Subgroup.center X ≃* R) : X →* R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))

private theorem l02qq2cd_commutatorElement_mul_right_center {X : Type*} [Group X] {x y z : X}
    (hy : ⁅x, y⁆ ∈ Subgroup.center X) (hz : ⁅x, z⁆ ∈ Subgroup.center X) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  have h2 : x * z * x⁻¹ = ⁅x, z⁆ * z := by rw [commutatorElement_def]; group
  have h3 : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    rw [Subgroup.mem_center_iff.mp hz y]
    group
  calc
    ⁅x, y * z⁆ = (x * y * x⁻¹) * (x * z * x⁻¹) * (z⁻¹ * y⁻¹) := by
      rw [commutatorElement_def, mul_inv_rev]; group
    _ = (⁅x, y⁆ * y) * (⁅x, z⁆ * z) * (z⁻¹ * y⁻¹) := by rw [h1, h2]
    _ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [h3]

private theorem l02qq2cd_exists_quotientCentralEquiv
    {J J₀ : Type*} [Group J] [Group J₀]
    (ψ : J →* J₀) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center J) (hperf : commutator J = ⊤) :
    ∃ e : J ⧸ Subgroup.center J ≃* J₀ ⧸ Subgroup.center J₀,
      ∀ x : J, e (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := by
  have hle : Subgroup.center J ≤
      ((QuotientGroup.mk' (Subgroup.center J₀)).comp ψ).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (ψ x : J₀ ⧸ Subgroup.center J₀) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.map_center_le_center (f := ψ) hψ (Subgroup.mem_map_of_mem ψ hx)
  let F : J ⧸ Subgroup.center J →* J₀ ⧸ Subgroup.center J₀ :=
    QuotientGroup.lift (Subgroup.center J)
      ((QuotientGroup.mk' (Subgroup.center J₀)).comp ψ) hle
  have hFmk : ∀ x : J, F (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := by
    intro x
    rw [QuotientGroup.lift_mk]
    rfl
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J₀) y
    obtain ⟨x, rfl⟩ := hψ y'
    exact ⟨QuotientGroup.mk x, hFmk x⟩
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      intro hx
      rw [hFmk x] at hx
      rw [QuotientGroup.eq_one_iff] at hx
      rw [QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_center_iff]
      intro y
      have hmem : ∀ z : J, ⁅x, z⁆ ∈ Subgroup.center J := by
        intro z
        apply hker
        rw [MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hx (ψ z)).symm
      let f : J →* Subgroup.center J :=
        { toFun := fun z => ⟨⁅x, z⁆, hmem z⟩
          map_one' := by
            apply Subtype.ext
            simp [commutatorElement_one_right]
          map_mul' := fun z w => by
            apply Subtype.ext
            simp only [Subgroup.coe_mul]
            exact l02qq2cd_commutatorElement_mul_right_center (hmem z) (hmem w) }
      have hfcomm : commutator J ≤ f.ker :=
        Subgroup.commutator_le.2 fun a _ b _ => by
          rw [MonoidHom.mem_ker, map_commutatorElement,
            commutatorElement_eq_one_iff_mul_comm]
          apply Subtype.ext
          simpa using (Subgroup.mem_center_iff.mp (f a).2 (f b)).symm
      have hftriv : f.ker = ⊤ := le_antisymm le_top (hperf ▸ hfcomm)
      have hf1 : f y = 1 := MonoidHom.mem_ker.mp (by rw [hftriv]; trivial)
      have hy1 : ⁅x, y⁆ = 1 := by
        have h := congrArg (fun t : Subgroup.center J => (t : J)) hf1
        simpa [f] using h
      exact (commutatorElement_eq_one_iff_mul_comm (g₁ := y) (g₂ := x)).mp (by
        have h := congrArg Inv.inv hy1
        rwa [commutatorElement_inv, inv_one] at h)
  have hFbij : Function.Bijective F := ⟨hFinj, hFsurj⟩
  refine ⟨MulEquiv.ofBijective F hFbij, ?_⟩
  intro x
  rw [MulEquiv.ofBijective_apply]
  exact hFmk x

theorem q2_cover_data {X R : Type} [Group X] [Finite X] [Group R] (hX : commutator X = ⊤)
    (θ : X ⧸ Subgroup.center X ≃* R) (u : MulAut X) (J : Subgroup X)
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u)) :
    CFSG.Open.IsComponentOf (J.map (q2CoverMap θ)) (ggAutFixedSubgroup (ggInducedAut θ u)) ∧
    ∃ ι : ↥J ⧸ Subgroup.center ↥J ≃*
        ↥(J.map (q2CoverMap θ)) ⧸ Subgroup.center ↥(J.map (q2CoverMap θ)),
      ∀ j : ↥J, ι (QuotientGroup.mk j) =
        QuotientGroup.mk ⟨q2CoverMap θ (j : X), Subgroup.mem_map_of_mem _ j.2⟩ := by
  let π : X →* R := q2CoverMap θ
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker_le : π.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : X ⧸ Subgroup.center X) = 1 := by
      apply θ.injective
      simpa [π, q2CoverMap] using hx
    rwa [QuotientGroup.eq_one_iff] at h1
  have hcomm_all : ∀ (b : MulAut X) (x : X),
      π (b.toMonoidHom x) = ggInducedAut θ b (π x) := by
    intro b x
    simpa [π, q2CoverMap] using (ggInducedAut_apply θ b x).symm
  have hJ' : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hJ
  obtain ⟨hJ₀, -⟩ := CFSG.StandardType.S2MathAs51600.centralFixedComponentTransfer_holds
    π hπ hker_le u (ggInducedAut θ u) (fun x => hcomm_all u x) J hJ'
  have hJ₀open : CFSG.Open.IsComponentOf (J.map π) (ggAutFixedSubgroup (ggInducedAut θ u)) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hJ₀
  have hJcomm : commutator ↥J = ⊤ := hJ.2.2.1
  let ψ : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective J
  have hψker : ψ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (x : X) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have h2 : ((ψ x : ↥(J.map π)) : R) = 1 := by
        simpa using congrArg Subtype.val hx
      simpa [ψ, MonoidHom.subgroupMap_apply_coe] using h2
    have hxc : (x : X) ∈ Subgroup.center X := hker_le hx1
    apply Subtype.ext
    simpa using Subgroup.mem_center_iff.mp hxc (y : X)
  obtain ⟨ι, ι_mk⟩ := l02qq2cd_exists_quotientCentralEquiv ψ hψ hψker hJcomm
  refine ⟨hJ₀open, ι, ?_⟩
  intro j
  rw [ι_mk j]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  rfl

end CFSG.StandardType

end
