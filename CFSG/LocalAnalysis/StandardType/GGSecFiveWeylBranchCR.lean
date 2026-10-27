module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCR3OfPump

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFive_not_cr_branch
    (hJA2 : GGSecFiveJA2Input) (hJr : GGSecFiveJrInput) (hCR : GGSecFiveCRInput)
    (hCR3 : GGSecFiveCR3Input)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod p) V} {Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)}
    {ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar}
    (hD : GGSecFiveBarData p B Bs x L D J ι U Abar ρ)
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    : ¬ (∀ r ∈ Abar, ZS.IsRefl p r → ZS.WitCR p Abar r ∨ ZS.WitL51 p Abar r) := by
  intro h
  obtain ⟨r₁, hr₁J, r₂, hr₂J, hr₁, hr₂, hord⟩ :=
    hJA2 G p B Bs x L D J 𝒦 hcfg hsplit
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hconf.2.2
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  have hr₁A : r₁ ∈ ggAInf p B Bs x L D J := by
    unfold ggAInf
    exact le_sup_left (b := ⨆ (y : G) (K : Subgroup G)
      (_ : GGNbr p B x D J y K), ggAutomizer K Bs) (ggAutomizer_mono Bs hJL hr₁J)
  have hr₂A : r₂ ∈ ggAInf p B Bs x L D J := by
    unfold ggAInf
    exact le_sup_left (b := ⨆ (y : G) (K : Subgroup G)
      (_ : GGNbr p B x D J y K), ggAutomizer K Bs) (ggAutomizer_mono Bs hJL hr₂J)
  let x₁ : ↥(ggAInf p B Bs x L D J) := ⟨r₁, hr₁A⟩
  let x₂ : ↥(ggAInf p B Bs x L D J) := ⟨r₂, hr₂A⟩
  let A₁ : ↥Abar := ρ x₁
  let A₂ : ↥Abar := ρ x₂
  have ha₁refl : ZS.IsRefl p ((A₁ : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) :=
    (hD.2.2.2.2.2.1 x₁).mp hr₁
  have ha₂refl : ZS.IsRefl p ((A₂ : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) :=
    (hD.2.2.2.2.2.1 x₂).mp hr₂
  have hA₁A₂ : A₁ * A₂ = ρ (x₁ * x₂) := by
    change ρ x₁ * ρ x₂ = ρ (x₁ * x₂)
    rw [map_mul]
  have hordA : orderOf (A₁ * A₂) = 3 := by
    have hx : ((x₁ * x₂ : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs) = r₁ * r₂ := rfl
    rw [hA₁A₂, MulEquiv.orderOf_eq ρ (x₁ * x₂),
      ← Subgroup.orderOf_coe (x₁ * x₂), hx, hord]
  have hordA' : orderOf ((A₁ : ↥U ≃ₗ[ZMod p] ↥U) * (A₂ : ↥U ≃ₗ[ZMod p] ↥U)) = 3 := by
    have hcoe : ((A₁ * A₂ : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) =
        (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * (A₂ : ↥U ≃ₗ[ZMod p] ↥U) := rfl
    rw [← hcoe, Subgroup.orderOf_coe, hordA]
  have hAinf_le : ggAInf p B Bs x L D J ≤ ggAutomizer ⊤ Bs := by
    unfold ggAInf
    refine sup_le (ggAutomizer_mono Bs le_top) ?_
    exact iSup_le fun y => iSup_le fun K => iSup_le fun _ => ggAutomizer_mono Bs le_top
  have hAinf_ind : ∀ b : ↥(ggAInf p B Bs x L D J),
      (b : MulAut ↥Bs) ∈ ggInduced ⊤ Bs := by
    intro b
    have h1 : (b : MulAut ↥Bs) ∈ ggAutomizer ⊤ Bs := hAinf_le b.2
    rw [ggAutomizer_eq] at h1
    exact h1
  rcases h (A₁ : ↥U ≃ₗ[ZMod p] ↥U) A₁.2 ha₁refl with hcr | hl51
  ·
    obtain ⟨g, hgAbar, hgt⟩ := hcr
    let gbar : ↥Abar := ⟨g, hgAbar⟩
    let b : ↥(ggAInf p B Bs x L D J) := ρ.symm gbar
    have hbρ : ρ b = gbar := MulEquiv.apply_symm_apply ρ gbar
    let t' : MulAut ↥Bs := (b : MulAut ↥Bs) * r₁ * (b : MulAut ↥Bs)⁻¹
    have ht'_refl : GGIsReflection p t' := by
      change GGIsReflection p ((b : MulAut ↥Bs) * r₁ * (b : MulAut ↥Bs)⁻¹)
      exact hr₁.conj' (b : MulAut ↥Bs)
    obtain ⟨n, -, hnN, hn⟩ := hAinf_ind b
    have hb_eq : ggConjAut Bs hnN = (b : MulAut ↥Bs) :=
      MulEquiv.ext fun y => Subtype.ext (by rw [ggConjAut_apply, hn y])
    have ht'_real : GGRealized p Bs t' := by
      change GGRealized p Bs ((b : MulAut ↥Bs) * r₁ * (b : MulAut ↥Bs)⁻¹)
      have hconj := GGRealized.conj (p := p) (Fact.out : p.Prime)
        (hJr G p B Bs x L D J 𝒦 hcfg hsplit r₁ hr₁J hr₁) hnN
      rwa [hb_eq] at hconj
    have hgtbar : 4 < orderOf (A₁ * (gbar * A₁ * gbar⁻¹)) := by
      have hcoe : ((A₁ * (gbar * A₁ * gbar⁻¹) : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) =
          (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * (g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹) := rfl
      rwa [← Subgroup.orderOf_coe (A₁ * (gbar * A₁ * gbar⁻¹)), hcoe]
    have hρeq : A₁ * (gbar * A₁ * gbar⁻¹) = ρ (x₁ * (b * x₁ * b⁻¹)) := by
      show ρ x₁ * (gbar * ρ x₁ * gbar⁻¹) =
        ρ (x₁ * (ρ.symm gbar * x₁ * (ρ.symm gbar)⁻¹))
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hgtInf : 4 < orderOf (x₁ * (b * x₁ * b⁻¹)) := by
      rw [← MulEquiv.orderOf_eq ρ (x₁ * (b * x₁ * b⁻¹)), ← hρeq]
      exact hgtbar
    have hgt' : 4 < orderOf (r₁ * t') := by
      have hxcoe : ((x₁ * (b * x₁ * b⁻¹) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs) =
          r₁ * t' := rfl
      rwa [← Subgroup.orderOf_coe (x₁ * (b * x₁ * b⁻¹)), hxcoe] at hgtInf
    have hle := hCR G p B Bs x L D J 𝒦 hcfg hsplit r₁ t'
      ⟨r₁, hr₁J, hr₁, 1, one_mem_ggInduced ⊤ Bs, by simp⟩ ht'_refl ht'_real
    omega
  ·
    obtain ⟨g, hgAbar, hnc, hcard48⟩ :=
      hl51 (A₂ : ↥U ≃ₗ[ZMod p] ↥U) A₂.2 ha₂refl hordA'
    let gbar : ↥Abar := ⟨g, hgAbar⟩
    let b : ↥(ggAInf p B Bs x L D J) := ρ.symm gbar
    have hbρ : ρ b = gbar := MulEquiv.apply_symm_apply ρ gbar
    let t' : MulAut ↥Bs := (b : MulAut ↥Bs) * r₁ * (b : MulAut ↥Bs)⁻¹
    have ht'_refl : GGIsReflection p t' := by
      change GGIsReflection p ((b : MulAut ↥Bs) * r₁ * (b : MulAut ↥Bs)⁻¹)
      exact hr₁.conj' (b : MulAut ↥Bs)
    obtain ⟨n, -, hnN, hn⟩ := hAinf_ind b
    have hb_eq : ggConjAut Bs hnN = (b : MulAut ↥Bs) :=
      MulEquiv.ext fun y => Subtype.ext (by rw [ggConjAut_apply, hn y])
    have ht'_real : GGRealized p Bs t' := by
      change GGRealized p Bs ((b : MulAut ↥Bs) * r₁ * (b : MulAut ↥Bs)⁻¹)
      have hconj := GGRealized.conj (p := p) (Fact.out : p.Prime)
        (hJr G p B Bs x L D J 𝒦 hcfg hsplit r₁ hr₁J hr₁) hnN
      rwa [hb_eq] at hconj
    let F : ↥(ggAInf p B Bs x L D J) →* (↥U ≃ₗ[ZMod p] ↥U) :=
      (Subgroup.subtype Abar).comp ρ.toMonoidHom
    have hF_inj : Function.Injective F :=
      (Subgroup.subtype_injective Abar).comp ρ.injective
    have hF1 : F x₁ = (A₁ : ↥U ≃ₗ[ZMod p] ↥U) := rfl
    have hF2 : F x₂ = (A₂ : ↥U ≃ₗ[ZMod p] ↥U) := rfl
    have hF3 : F (b * x₁ * b⁻¹) = g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹ := by
      change ((ρ (b * x₁ * b⁻¹) : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) =
        g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹
      simp only [map_mul, map_inv, hbρ, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    have hcommF₁ : Commute (g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹)
        (A₁ : ↥U ≃ₗ[ZMod p] ↥U) ↔ Commute (b * x₁ * b⁻¹) x₁ := by
      rw [← hF3, ← hF1]
      exact commute_map_iff (f := F) hF_inj
    have hcommF₂ : Commute (g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹)
        (A₂ : ↥U ≃ₗ[ZMod p] ↥U) ↔ Commute (b * x₁ * b⁻¹) x₂ := by
      rw [← hF3, ← hF2]
      exact commute_map_iff (f := F) hF_inj
    have hnc_inf : ¬ (Commute (b * x₁ * b⁻¹) x₁ ∧ Commute (b * x₁ * b⁻¹) x₂) := by
      intro hh
      exact hnc ⟨hcommF₁.mpr hh.1, hcommF₂.mpr hh.2⟩
    let G' : ↥(ggAInf p B Bs x L D J) →* MulAut ↥Bs := Subgroup.subtype _
    have hG'inj : Function.Injective G' := Subgroup.subtype_injective _
    have hG'1 : G' x₁ = r₁ := rfl
    have hG'2 : G' x₂ = r₂ := rfl
    have hG'3 : G' (b * x₁ * b⁻¹) = t' := rfl
    have hcomm₁ : Commute t' r₁ ↔ Commute (b * x₁ * b⁻¹) x₁ := by
      rw [← hG'3, ← hG'1]
      exact commute_map_iff (f := G') hG'inj
    have hcomm₂ : Commute t' r₂ ↔ Commute (b * x₁ * b⁻¹) x₂ := by
      rw [← hG'3, ← hG'2]
      exact commute_map_iff (f := G') hG'inj
    have hnc' : ¬ (Commute t' r₁ ∧ Commute t' r₂) := by
      intro hh
      exact hnc_inf ⟨hcomm₁.mp hh.1, hcomm₂.mp hh.2⟩
    let S : Set ↥(ggAInf p B Bs x L D J) := {x₁, x₂, b * x₁ * b⁻¹}
    have hS : (Subgroup.subtype (ggAInf p B Bs x L D J)) '' S =
        ({r₁, r₂, t'} : Set (MulAut ↥Bs)) := by
      show (Subgroup.subtype (ggAInf p B Bs x L D J)) ''
          ({x₁, x₂, b * x₁ * b⁻¹} : Set ↥(ggAInf p B Bs x L D J)) = _
      simp only [Set.image_insert_eq, Set.image_singleton]
      rfl
    have hSF : F '' S = ({(A₁ : ↥U ≃ₗ[ZMod p] ↥U), (A₂ : ↥U ≃ₗ[ZMod p] ↥U),
        g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹} : Set (↥U ≃ₗ[ZMod p] ↥U)) := by
      rw [show S = insert x₁ (insert x₂ {b * x₁ * b⁻¹}) from rfl,
        Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hF1, hF2, hF3]
    have hcard₁ : Nat.card (Subgroup.closure ({r₁, r₂, t'} : Set (MulAut ↥Bs))) =
        Nat.card (Subgroup.closure S) := by
      rw [← hS, ← MonoidHom.map_closure]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have hcard₂ : Nat.card (Subgroup.closure ({(A₁ : ↥U ≃ₗ[ZMod p] ↥U),
        (A₂ : ↥U ≃ₗ[ZMod p] ↥U), g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹} :
          Set (↥U ≃ₗ[ZMod p] ↥U))) = Nat.card (Subgroup.closure S) := by
      rw [← hSF, ← MonoidHom.map_closure]
      exact Subgroup.card_map_of_injective hF_inj
    have hcard_eq : Nat.card (Subgroup.closure ({r₁, r₂, t'} : Set (MulAut ↥Bs))) =
        Nat.card (Subgroup.closure ({(A₁ : ↥U ≃ₗ[ZMod p] ↥U), (A₂ : ↥U ≃ₗ[ZMod p] ↥U),
          g * (A₁ : ↥U ≃ₗ[ZMod p] ↥U) * g⁻¹} : Set (↥U ≃ₗ[ZMod p] ↥U))) :=
      hcard₁.trans hcard₂.symm
    have hres := hCR3 G p B Bs x L D J 𝒦 hcfg hsplit r₁ hr₁J r₂ hr₂J hr₁ hr₂ hord
      (1 : MulAut ↥Bs) (one_mem_ggInduced ⊤ Bs) t' ht'_refl ht'_real
      (by simpa using hnc')
    have hres' : Nat.card (Subgroup.closure ({r₁, r₂, t'} : Set (MulAut ↥Bs))) ∣ 48 := by
      simpa using hres
    rw [hcard_eq] at hres'
    exact hcard48 hres'

end CFSG.StandardType

end
