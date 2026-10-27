module

public import CFSG.Sporadic.Fi24.Class
public import CFSG.Fischer.Uniq.F24Uniq
public import CFSG.Sporadic.Fi23.Rigid

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem index_MR_centralizer :
    (MR.subgroupOf (Subgroup.centralizer ({tR} : Set R))).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨tR, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩, fun c => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  show Xor ((c : R) * tR ∈ MR) ((c : R) ∈ MR)
  rcases mem_MR_or_of_commute c.2 with h | h
  · refine Or.inr ⟨h, fun h' => tR_not_mem_MR ?_⟩
    have := MR.mul_mem (MR.inv_mem h) h'
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨h, fun h' => tR_not_mem_MR ?_⟩
    have := MR.mul_mem (MR.inv_mem h') h
    rwa [inv_mul_cancel_left] at this

theorem card_centralizer_tR :
    Nat.card (Subgroup.centralizer ({tR} : Set R)) = 2 * Nat.card Fi23.J := by
  have hle : MR ≤ Subgroup.centralizer ({tR} : Set R) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.2 (commute_tR_of_mem_MR hm)
  have h := (MR.subgroupOf (Subgroup.centralizer ({tR} : Set R))).card_mul_index
  rw [index_MR_centralizer, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr fi23EquivJMR.toEquiv] at h
  omega

theorem isSimpleGroup_commutator_R :
    IsSimpleGroup (commutator R) :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J
    ((MulEquiv.subgroupCongr (commutator_R.trans range_jR.symm)).trans
      (MonoidHom.ofInjective jR_injective).symm)

theorem exists_commuting_pair_D24 :
    ∃ e f, e ∈ D24 ∧ f ∈ D24 ∧ e ≠ f ∧ e * f = f * e := by
  obtain ⟨f₁, hf₁, -⟩ := exists_two_mem_localClass
  exact ⟨tR, f₁, tR_mem_D24, hf₁.1, hf₁.2.1.symm, hf₁.2.2.symm⟩

theorem connected_D24 :
    (commGraph D24).Connected :=
  Pair.connected_of_simple pair_R isSimpleGroup_commutator_R exists_commuting_pair_D24

section Rigid

variable (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts) {tr cs : Set (Set Fi23.D23)}
  {r : tr} (hTF : Fi23Facts tr cs r)
include hPF hHF hFF hTF

theorem card_stabT_D24_le :
    Nat.card (stabT pair_R tR_mem_D24) ≤ 2 * Nat.card Fi23.J := by
  have h := coverHyp_tr hPF hHF hTF pair_R localPoints_D24 tR_mem_D24 localPoints_tR
  have hXi := connected_of_D2 r hTF.xi24_D2
  have hmu : ∀ c ∈ D24, c * tR ≠ tR * c → (muSet D24 tR c).Nonempty := fun c hc hcd =>
    Pair.muSet_nonempty pair_R connected_D24 tR_mem_D24 hc hcd
  exact Pair.card_stabT_le_of_rigid Fi23.pair_J pair_R tR_mem_D24 Fi23.center_J localPoints_tR h
    hXi hmu fun σ _ => Fi23.tauGroup_D23_eq_range hPF hHF hFF σ

theorem tauGroup_D24_eq_range
    (σ : tauGroup pair_R) : σ ∈ (innerTau pair_R).range :=
  Pair.mem_range_innerTau_of_card_stabT pair_R center_R tR_mem_D24
    (by rw [card_centralizer_tR]; exact card_stabT_D24_le hPF hHF hFF hTF) σ

theorem complete_R :
    ∀ φ : MulAut R, ∃ g : R, φ = MulAut.conj g :=
  @complete_of_tauGroup (↥R) inferInstance D24 pair_R (pair_eq_D24 hPF)
    (tauGroup_D24_eq_range hPF hHF hFF hTF)

end Rigid

end CFSG.Sporadic.Fi24
