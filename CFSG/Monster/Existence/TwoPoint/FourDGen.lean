module

public import CFSG.Monster.Existence.TwoPoint.FourDStab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Monster.GMS

theorem fd_mem_cent_gamma_iff
    (hG : Gmat = AutO) {w : CVert} {γ : MGriess}
    (hγ : FourDGammaData hG w γ) (e : ↥(cent2 tGriess uGriess)) :
    e.1 ∈ cent γ ↔ ((fdEdgeShat hG e : Shat) : Dfull) * clabel w =
      clabel w * ((fdEdgeShat hG e : Shat) : Dfull) := by
  rw [coe_fdEdgeShat]
  set ε : cent tGriess := ⟨e.1, e.2.1⟩ with hε
  set g : cent tGriess := ⟨γ, hγ.mem_cent⟩ with hg
  have hπg : ((centToShat hG g : Shat) : Dfull) = clabel w := hγ.pi_eq
  constructor
  · intro h
    have h' : ε * g = g * ε := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 h)
    have := congrArg (fun z => ((centToShat hG z : Shat) : Dfull)) h'
    simp only [map_mul, Subgroup.coe_mul, hπg] at this
    exact this
  · intro h
    have hcomm : centToShat hG ε * centToShat hG g = centToShat hG g * centToShat hG ε := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hπg]
      exact h
    have h1 : centToShat hG (ε * g * ε⁻¹ * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hu : e.1 * uGriess * e.1⁻¹ = uGriess := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 e.2.2]; group
    have htγ : tGriess * γ = γ * tGriess :=
      (Subgroup.mem_centralizer_singleton_iff.1 hγ.mem_cent).symm
    rcases (centToShat_eq_one_iff hG _).1 h1 with h2 | h2
    · have h2' : e.1 * γ * e.1⁻¹ * γ⁻¹ = 1 := h2
      apply Subgroup.mem_centralizer_singleton_iff.2
      calc e.1 * γ = (e.1 * γ * e.1⁻¹ * γ⁻¹) * (γ * e.1) := by group
        _ = γ * e.1 := by rw [h2', one_mul]
    · exfalso
      have h2' : e.1 * γ * e.1⁻¹ * γ⁻¹ = tGriess := h2
      have hconj : e.1 * γ * e.1⁻¹ = tGriess * γ := by
        calc e.1 * γ * e.1⁻¹ = (e.1 * γ * e.1⁻¹ * γ⁻¹) * γ := by group
          _ = tGriess * γ := by rw [h2']
      apply hγ.not_isConj_ut
      have h3 : e.1 * (uGriess * γ) * e.1⁻¹ = uGriess * γ * tGriess := by
        calc e.1 * (uGriess * γ) * e.1⁻¹ = (e.1 * uGriess * e.1⁻¹) * (e.1 * γ * e.1⁻¹) := by
              group
          _ = uGriess * (tGriess * γ) := by rw [hu, hconj]
          _ = uGriess * γ * tGriess := by rw [htγ]; group
      rw [← h3]
      exact hγ.isConj_u.trans (isConj_iff.2 ⟨e.1, rfl⟩)

variable {ρ : vStab cv0 →* GStar} {iv : cgraph.neighborSet cv0 ≃ rootClass}

theorem fd_stabAct_eq_iff (hρ : FourDLocalMap ρ iv) (y : vStab cv0) (z : cgraph.neighborSet cv0) :
    stabAct y z = z ↔ Commute (ρ y) (SemidirectProduct.inl (iv z : stdGroup)) := by
  calc stabAct y z = z ↔ iv (stabAct y z) = iv z := iv.injective.eq_iff.symm
    _ ↔ (SemidirectProduct.inl (iv (stabAct y z) : stdGroup) : GStar) =
        SemidirectProduct.inl (iv z : stdGroup) := by
      rw [SemidirectProduct.inl_injective.eq_iff]
      exact Subtype.coe_inj.symm
    _ ↔ (ρ y)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ y =
        SemidirectProduct.inl (iv z : stdGroup) := by rw [hρ.equivar y z]
    _ ↔ Commute (ρ y) (SemidirectProduct.inl (iv z : stdGroup)) := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul, commute_iff_eq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem fd_mem_cent_gamma_iff_commute
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (hρ : FourDLocalMap ρ iv) (z : cgraph.neighborSet cv0) {γ : MGriess}
    (hγ : FourDGammaData hG z.1 γ) (e : ↥(cent2 tGriess uGriess)) :
    e.1 ∈ cent γ ↔ Commute (fdEdgeRho hG hC ρ e) (SemidirectProduct.inl (iv z : stdGroup)) := by
  rw [fd_mem_cent_gamma_iff hG hγ e, hC z.1 (fdEdgeShat hG e)]
  have h1 : cvMul z.1 (fdEdgeShat hG e) = z.1 ↔ stabAct (fdEdgeV hG hC e) z = z := by
    rw [Subtype.ext_iff, coe_stabAct]
    rfl
  exact h1.trans (fd_stabAct_eq_iff hρ _ z)

theorem fd_ker_fdEdgeRho_le
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (hρ : FourDLocalMap ρ iv) (z : cgraph.neighborSet cv0) {γ : MGriess}
    (hγ : FourDGammaData hG z.1 γ) :
    (fdEdgeRho hG hC ρ).ker ≤ (cent γ).subgroupOf (cent2 tGriess uGriess) := by
  intro e he
  show e.1 ∈ cent γ
  rw [fd_mem_cent_gamma_iff_commute hG hC hρ z hγ e, MonoidHom.mem_ker.1 he]
  exact Commute.one_left _

theorem fd_map_cent_gamma_eq
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (hρ : FourDLocalMap ρ iv) (z : cgraph.neighborSet cv0) {γ : MGriess}
    (hγ : FourDGammaData hG z.1 γ) :
    ((cent γ).subgroupOf (cent2 tGriess uGriess)).map (fdEdgeRho hG hC ρ) =
      (Subgroup.centralizer ({(iv z : stdGroup)} : Set stdGroup)).map
        SemidirectProduct.inl := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    have hr : fdEdgeRho hG hC ρ e ∈ Ginl := by
      rw [← fdEdgeRho_range hG hC hρ]
      exact ⟨e, rfl⟩
    obtain ⟨q, hq⟩ := hr
    refine ⟨q, ?_, hq⟩
    have hc := (fd_mem_cent_gamma_iff_commute hG hC hρ z hγ e).1 he
    rw [← hq] at hc
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    apply inl_injective
    rw [map_mul, map_mul]
    exact hc.eq
  · rintro ⟨q, hq, rfl⟩
    have hr : (SemidirectProduct.inl q : GStar) ∈ (fdEdgeRho hG hC ρ).range := by
      rw [fdEdgeRho_range hG hC hρ]
      exact ⟨q, rfl⟩
    obtain ⟨e, he⟩ := hr
    refine ⟨e, ?_, he⟩
    show e.1 ∈ cent γ
    rw [fd_mem_cent_gamma_iff_commute hG hC hρ z hγ e, he, commute_iff_eq, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hq]

theorem fd_sup_eq_edge_of_dvd
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (hρ : FourDLocalMap ρ iv) (z : cgraph.neighborSet cv0) {γ : MGriess}
    (hγ : FourDGammaData hG z.1 γ) {D : Subgroup MGriess} (hD : D ≤ cent2 tGriess uGriess)
    (h17 : 17 ∣ Nat.card D) :
    (cent2 tGriess uGriess ⊓ cent γ) ⊔ D = cent2 tGriess uGriess := by
  have hp : (iv z : stdGroup) ∈ rootClass := (iv z).2
  have hsup : (cent γ).subgroupOf (cent2 tGriess uGriess) ⊔ D.subgroupOf (cent2 tGriess uGriess) =
      ⊤ := by
    refine fd_sup_eq_top_of_map (fdEdgeRho hG hC ρ) (fd_ker_fdEdgeRho_le hG hC hρ z hγ) ?_ ?_
    · intro B hlt hB
      rw [fd_map_cent_gamma_eq hG hC hρ z hγ] at hlt
      rw [fdEdgeRho_range hG hC hρ] at hB ⊢
      exact fd_eq_Ginl_of_lt_map_inl hp hlt hB
    · rw [fd_map_cent_gamma_eq hG hC hρ z hγ]
      refine fd_not_map_le_of_dvd (fdEdgeRho hG hC ρ) (p := 17) (by norm_num) ?_ ?_ ?_
      · rw [natCard_ker_fdEdgeRho hG hC hρ]
        norm_num
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv]
        exact h17
      · rw [Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
        exact fd_not_seventeen_dvd_card_centralizer hp
  have h1 := congrArg (Subgroup.map (cent2 tGriess uGriess).subtype) hsup
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.map_top, Subgroup.range_subtype, inf_of_le_left hD, inf_comm] at h1
  exact h1

end CFSG.Monster.Existence
