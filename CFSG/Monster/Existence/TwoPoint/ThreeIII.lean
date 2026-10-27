module

public import CFSG.Monster.Existence.TwoPoint.Fi23Sp8Glue
public import CFSG.Monster.Existence.TwoPoint.GriessGraph
public import CFSG.Monster.Existence.TwoPoint.ThreeV

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section General

variable {G : Type} [Group G]

@[expose] def gammaSet (a c α β : G) : Set G :=
  {γ | IsConj a γ ∧ IsConj (α * γ) c ∧ IsConj a (β * γ)}

@[expose] def ThreeIIIData (a c α β : G) : Prop :=
  (gammaSet a c α β).Nonempty ∧
    (∀ γ ∈ gammaSet a c α β, ∀ γ' ∈ gammaSet a c α β, ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
    ∀ γ ∈ gammaSet a c α β, CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1

theorem isConj_conj_right {x y : G} (g : G) (h : IsConj x y) : IsConj x (g * y * g⁻¹) :=
  h.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem isConj_of_conj_right {x y : G} (g : G) (h : IsConj x (g * y * g⁻¹)) : IsConj x y :=
  h.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)

theorem mem_gammaSet_conj {a c α β γ : G} (g : G) (h : γ ∈ gammaSet a c α β) :
    g * γ * g⁻¹ ∈ gammaSet a c (g * α * g⁻¹) (g * β * g⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isConj_conj_right g h1, ?_, ?_⟩
  · rw [show g * α * g⁻¹ * (g * γ * g⁻¹) = g * (α * γ) * g⁻¹ by group]
    exact (isConj_iff.2 ⟨g⁻¹, by group⟩).trans h2
  · rw [show g * β * g⁻¹ * (g * γ * g⁻¹) = g * (β * γ) * g⁻¹ by group]
    exact isConj_conj_right g h3

theorem mem_gammaSet_of_conj {a c α β γ : G} (g : G)
    (h : g * γ * g⁻¹ ∈ gammaSet a c (g * α * g⁻¹) (g * β * g⁻¹)) : γ ∈ gammaSet a c α β := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isConj_of_conj_right g h1, ?_, ?_⟩
  · rw [show g * α * g⁻¹ * (g * γ * g⁻¹) = g * (α * γ) * g⁻¹ by group] at h2
    exact (isConj_iff.2 ⟨g, rfl⟩).trans h2
  · rw [show g * β * g⁻¹ * (g * γ * g⁻¹) = g * (β * γ) * g⁻¹ by group] at h3
    exact isConj_of_conj_right g h3

theorem map_conj_cent (g x : G) :
    (cent x).map (MulAut.conj g).toMonoidHom = cent (g * x * g⁻¹) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group

theorem map_conj_cent2_inf_cent (g α β γ : G) :
    (cent2 α β ⊓ cent γ).map (MulAut.conj g).toMonoidHom =
      cent2 (g * α * g⁻¹) (g * β * g⁻¹) ⊓ cent (g * γ * g⁻¹) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_cent2, map_conj_cent]

noncomputable def cent2InfCentConjEquiv (g α β γ : G) :
    ↥(cent2 α β ⊓ cent γ) ≃* ↥(cent2 (g * α * g⁻¹) (g * β * g⁻¹) ⊓ cent (g * γ * g⁻¹)) :=
  ((cent2 α β ⊓ cent γ).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (map_conj_cent2_inf_cent g α β γ))

theorem ThreeIIIData.conj {a c α β : G} (g : G) (h : ThreeIIIData a c α β) :
    ThreeIIIData a c (g * α * g⁻¹) (g * β * g⁻¹) := by
  obtain ⟨⟨γ₀, h₀⟩, htr, hL⟩ := h
  refine ⟨⟨g * γ₀ * g⁻¹, mem_gammaSet_conj g h₀⟩, ?_, ?_⟩
  · intro γ hγ γ' hγ'
    obtain ⟨δ, rfl⟩ : ∃ δ, γ = g * δ * g⁻¹ := ⟨g⁻¹ * γ * g, by group⟩
    obtain ⟨δ', rfl⟩ : ∃ δ', γ' = g * δ' * g⁻¹ := ⟨g⁻¹ * γ' * g, by group⟩
    obtain ⟨k, hk, hkδ⟩ := htr δ (mem_gammaSet_of_conj g hγ) δ' (mem_gammaSet_of_conj g hγ')
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · rw [← map_conj_cent2]
      exact ⟨k, hk, rfl⟩
    · rw [← hkδ]
      group
  · intro γ hγ
    obtain ⟨δ, rfl⟩ : ∃ δ, γ = g * δ * g⁻¹ := ⟨g⁻¹ * γ * g, by group⟩
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (cent2InfCentConjEquiv g α β δ)
      (hL δ (mem_gammaSet_of_conj g hγ))

end General

section MGriess

open CFSG.Monster CFSG.Monster.Griess

theorem seventeen_dvd_card_spL :
    17 ∣ Nat.card ↥Fi23Sp8.spL := by
  classical
  have hp : Fi23Sp8.piF 0 ∈ Fi23Sp8.Sg := Fi23Sp8.LbF_piF (Fi23Sp8.mem_gIdx_iff.2 ⟨by norm_num,
    by norm_num⟩)
  have horb : MulAction.orbit ↥Fi23Sp8.spL (Fi23Sp8.piF 0) = Fi23Sp8.Sg := by
    ext q
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      exact Fi23Sp8.smul_mem_Sg hl hp
    · intro hq
      obtain ⟨l, hl, hlq⟩ := Fi23Sp8.exists_smul_iff.2 (show Fi23Sp8.LbF (Fi23Sp8.piF 0) =
        Fi23Sp8.LbF q from hp.trans hq.symm)
      exact ⟨⟨l, hl⟩, hlq⟩
  have hS : Fi23Sp8.Sg = ↑(Finset.univ.filter fun p : Fi23Sp8.Pt => Fi23Sp8.LbF p = 0) := by
    ext p
    simp [Fi23Sp8.Sg]
  have hcard : (MulAction.orbit ↥Fi23Sp8.spL (Fi23Sp8.piF 0)).ncard = 255 := by
    rw [horb, hS, Set.ncard_coe_finset]
    exact Fi23Sp8.card_label_values.1
  have hdvd := (MulAction.stabilizer ↥Fi23Sp8.spL (Fi23Sp8.piF 0)).index_dvd_card
  rw [MulAction.index_stabilizer, hcard] at hdvd
  exact (show (17 : ℕ) ∣ 255 by norm_num).trans hdvd

theorem orderOf_fiAlpha_mul_gammaZero :
    orderOf (fiAlpha * gammaZero) = 3 :=
  orderOf_eq_prime fiAlpha_mul_gammaZero_pow_three fiAlpha_mul_gammaZero_ne_one

theorem gammaZero_ne_fiAlpha :
    gammaZero ≠ fiAlpha := fun h =>
  fiAlpha_mul_gammaZero_ne_one (by rw [h, fiAlpha_mul_self])

theorem fiK_eq_cent2_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    fiK = cent2 fiAlpha fiBeta := by
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨y, hy, hs3, -, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard (natCard_cent_tGriess_of hA) hTh
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  have hfr : IsConj (fiAlpha * fiBeta) (tGriess * y 0) :=
    isConj_fiAlpha_mul_fiBeta.trans h3A.symm
  obtain ⟨ψ⟩ := twoPointShape_of_isConj I hG hex hsep isConj_fiAlpha isConj_fiBeta (hy 0).1.1
    hfr hs3
  exact fiK_eq_cent2_of_card (by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Fi23.card_Fi23])

theorem isConj_fiAlpha_mul_gammaZero
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    IsConj (fiAlpha * gammaZero) threeARep := by
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨y, hy, -, hs4, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard (natCard_cent_tGriess_of hA) hTh
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  have hKeq := fiK_eq_cent2_MGriess I hex hcard hA hTh
  have hmem : gammaZero ∈ oddNbr tGriess xGriess fiAlpha :=
    hex fiAlpha gammaZero isConj_fiAlpha isConj_gammaZero gammaZero_ne_fiAlpha
      (by rw [orderOf_fiAlpha_mul_gammaZero]; decide)
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG
    isConj_fiAlpha hmem
  fin_cases k
  · exact (isConj_mul_of_oddNbrType I (hy 0).1 (hy 0).2 isConj_fiAlpha hmem hk).trans h3A
  · exfalso
    have hc := isConj_mul_of_oddNbrType I (hy 1).1 (hy 1).2 isConj_fiAlpha hmem hk
    obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_of_isConj I hG hex hsep isConj_fiAlpha
      isConj_gammaZero (hy 1).1.1 hc
    have hs := TwoPointShape.conj g hs4
    rw [hg1, hg2] at hs
    obtain ⟨e⟩ := hs
    have hTh' : Nat.card ↥(cent2 fiAlpha gammaZero) = CFSG.Open.monsterThOrder := by
      rw [Nat.card_congr e.toEquiv, CFSG.Monster.Existence.Compat.card_nativeTh]
    have hle : cent2 fiAlpha fiBeta ⊓ cent gammaZero ≤ cent2 fiAlpha gammaZero :=
      fun z hz => ⟨hz.1.1, hz.2⟩
    have h17 : 17 ∣ Nat.card ↥(cent2 fiAlpha gammaZero) := by
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le hle)
      rw [Nat.card_congr (interEquivSpL hKeq (fun _ hi hi8 => fiE_commute_gammaZero hi hi8)
        fiE_eight_not_commute_gammaZero).toEquiv]
      exact seventeen_dvd_card_spL
    rw [hTh'] at h17
    norm_num [CFSG.Open.monsterThOrder] at h17
  · exfalso
    obtain ⟨w, hwB, hw⟩ := oddNbr.exists_isOddPair isConj_fiAlpha hmem
    have ho := (s348_card hk hw.mem_inf hwB).1
    rw [orderOf_fiAlpha_mul_gammaZero] at ho
    simp [oddTypeOrder] at ho

theorem gammaZero_mem_gammaSet
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    gammaZero ∈ gammaSet tGriess threeARep fiAlpha fiBeta :=
  ⟨isConj_gammaZero, isConj_fiAlpha_mul_gammaZero I hex hcard hA hTh,
    isConj_fiBeta_mul_gammaZero⟩

theorem threeIIIData_frame
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (htr : ∀ γ ∈ gammaSet tGriess threeARep fiAlpha fiBeta,
      ∀ γ' ∈ gammaSet tGriess threeARep fiAlpha fiBeta,
        ∃ g ∈ cent2 fiAlpha fiBeta, g * γ * g⁻¹ = γ') :
    ThreeIIIData tGriess threeARep fiAlpha fiBeta := by
  have hKeq := fiK_eq_cent2_MGriess I hex hcard hA hTh
  have h₀ := gammaZero_mem_gammaSet I hex hcard hA hTh
  refine ⟨⟨gammaZero, h₀⟩, htr, fun γ hγ => ?_⟩
  obtain ⟨g, hg, rfl⟩ := htr gammaZero h₀ γ hγ
  have hga : g * fiAlpha * g⁻¹ = fiAlpha := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hg.1, mul_inv_cancel_right]
  have hgb : g * fiBeta * g⁻¹ = fiBeta := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hg.2, mul_inv_cancel_right]
  have e := cent2InfCentConjEquiv g fiAlpha fiBeta gammaZero
  rw [hga, hgb] at e
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e
    (lieModel_cent2_inf_cent_gammaZero hKeq)

theorem threeIIIData_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (htr : ∀ γ ∈ gammaSet tGriess threeARep fiAlpha fiBeta,
      ∀ γ' ∈ gammaSet tGriess threeARep fiAlpha fiBeta,
        ∃ g ∈ cent2 fiAlpha fiBeta, g * γ * g⁻¹ = γ') :
    ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β → IsConj (α * β) threeARep →
      ThreeIIIData tGriess threeARep α β := by
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨y, hy, -, -, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard (natCard_cent_tGriess_of hA) hTh
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  have hy0 : IsConj tGriess (y 0) := (hy 0).1.1
  have hfr : IsConj (fiAlpha * fiBeta) (tGriess * y 0) :=
    isConj_fiAlpha_mul_fiBeta.trans h3A.symm
  have hframe := threeIIIData_frame I hex hcard hA hTh htr
  intro α β hα hβ hαβ
  obtain ⟨g₁, hg₁a, hg₁y⟩ := exists_conj_pair_of_isConj I hG hex hsep isConj_fiAlpha
    isConj_fiBeta hy0 hfr
  obtain ⟨g₂, hg₂a, hg₂y⟩ := exists_conj_pair_of_isConj I hG hex hsep hα hβ hy0
    (hαβ.trans h3A.symm)
  have := hframe.conj (g₂ * g₁⁻¹)
  have e1 : g₂ * g₁⁻¹ * fiAlpha * (g₂ * g₁⁻¹)⁻¹ = α := by
    rw [← hg₁a, ← hg₂a]; group
  have e2 : g₂ * g₁⁻¹ * fiBeta * (g₂ * g₁⁻¹)⁻¹ = β := by
    rw [← hg₁y, ← hg₂y]; group
  rwa [e1, e2] at this

theorem hiii_of_threeIIIData
    (h : ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β → IsConj (α * β) threeARep →
      ThreeIIIData tGriess threeARep α β) :
    ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β →
      IsConj (α * β) threeARep →
      (∃ γ, IsConj tGriess γ ∧ IsConj (α * γ) threeARep ∧ IsConj tGriess (β * γ)) ∧
      (∀ γ γ', IsConj tGriess γ → IsConj (α * γ) threeARep → IsConj tGriess (β * γ) →
        IsConj tGriess γ' → IsConj (α * γ') threeARep → IsConj tGriess (β * γ') →
        ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj tGriess γ → IsConj (α * γ) threeARep → IsConj tGriess (β * γ) →
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1 := by
  intro α β hα hβ hαβ
  obtain ⟨⟨γ₀, h₀⟩, htr, hL⟩ := h α β hα hβ hαβ
  exact ⟨⟨γ₀, h₀⟩, fun γ γ' h1 h2 h3 h1' h2' h3' => htr γ ⟨h1, h2, h3⟩ γ' ⟨h1', h2', h3'⟩,
    fun γ h1 h2 h3 => hL γ ⟨h1, h2, h3⟩⟩

end MGriess

end CFSG.Monster.Existence
