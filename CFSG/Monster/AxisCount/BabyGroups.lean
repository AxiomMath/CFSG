module

public import CFSG.Monster.AxisCount.SetupGroups
public import CFSG.Monster.AxisCount.AxisFacts
public import CFSG.Monster.B.TwoA.Triality.PermMain

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short

open CFSG.Monster.B.TwoA (hE0 hE0_mem_Jstar)

theorem Jstar_le_Gvis : Jstar ≤ Gvis := inf_le_left

instance finite_Jstar : Finite Jstar :=
  Finite.of_injective (Subgroup.inclusion Jstar_le_Gvis) (Subgroup.inclusion_injective _)

theorem Jstar_inf_Nfr_le_Jstar : Jstar ⊓ Nfr ≤ Jstar := inf_le_left

theorem Jstar_inf_Nfr'_le : Jstar ⊓ Nfr' ≤ Jstar ⊓ Nfr := inf_le_inf_left _ Nfr'_le_Nfr

theorem Jstar_inf_Nfr'_le_Jstar : Jstar ⊓ Nfr' ≤ Jstar := inf_le_left

theorem Jstar_inf_Nfr_le_Gvis : Jstar ⊓ Nfr ≤ Gvis := inf_le_left.trans Jstar_le_Gvis

theorem hE0_mem_Jstar_inf_Nfr : hE0 ∈ Jstar ⊓ Nfr := ⟨hE0_mem_Jstar, hE0_mem_Nfr⟩

theorem hE0_notMem_Jstar_inf_Nfr' : hE0 ∉ Jstar ⊓ Nfr' := fun h => hE0_notMem_Nfr' h.2

theorem relIndex_inf_eq_two {G : Type*} [Group G] {K N N' : Subgroup G}
    (h : N'.relIndex N = 2) {a : G} (haK : a ∈ K) (haN : a ∈ N) (haN' : a ∉ N') :
    (K ⊓ N').relIndex (K ⊓ N) = 2 := by
  have hidx : (N'.subgroupOf N).index = 2 := h
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨a, ⟨haK, haN⟩, fun b hb => ?_⟩
  have e1 : b * a ∈ N' ↔ (b ∈ N' ↔ a ∈ N') :=
    Subgroup.mul_mem_iff_of_index_two (a := (⟨b, hb.2⟩ : N)) (b := (⟨a, haN⟩ : N)) hidx
  have hba : (b * a ∈ K ⊓ N') ↔ b * a ∈ N' := ⟨fun x => x.2, fun x => ⟨K.mul_mem hb.1 haK, x⟩⟩
  have hb' : (b ∈ K ⊓ N') ↔ b ∈ N' := ⟨fun x => x.2, fun x => ⟨hb.1, x⟩⟩
  rw [hba, hb', e1]
  by_cases hbN' : b ∈ N'
  · exact Or.inr ⟨hbN', fun hp => haN' (hp.1 hbN')⟩
  · exact Or.inl ⟨⟨fun h => absurd h hbN', fun h => absurd h haN'⟩, hbN'⟩

theorem relIndex_Jstar_inf_Nfr'_Nfr : (Jstar ⊓ Nfr').relIndex (Jstar ⊓ Nfr) = 2 :=
  relIndex_inf_eq_two relIndex_Nfr'_Nfr hE0_mem_Jstar hE0_mem_Nfr hE0_notMem_Nfr'

theorem commute_tauB_tStar : Commute tauB tStar := commute_tStar_of_mem_Cgen tauB_mem_Cgen

theorem conj_mem_Jstar_of_mem_Gvis {c n : SpaceB ≃ₗ[ℚ] SpaceB} (hc : Commute c tStar)
    (hn : n ∈ Jstar) (h : c * n * c⁻¹ ∈ Gvis) : c * n * c⁻¹ ∈ Jstar :=
  ⟨h, Subgroup.mem_centralizer_singleton_iff.2
    ((hc.mul_left (Subgroup.mem_centralizer_singleton_iff.1 hn.2)).mul_left hc.inv_left)⟩

theorem tauB_conj_mem_Jstar_inf_Nfr' {n : SpaceB ≃ₗ[ℚ] SpaceB} (hn : n ∈ Jstar ⊓ Nfr') :
    tauB * n * tauB⁻¹ ∈ Jstar ⊓ Nfr' :=
  have h := tauB_conj_mem_Nfr' hn.2
  ⟨conj_mem_Jstar_of_mem_Gvis commute_tauB_tStar hn.1 (Nfr'_le_Gvis h), h⟩

theorem tauB_inv_conj_mem_Jstar_inf_Nfr' {n : SpaceB ≃ₗ[ℚ] SpaceB} (hn : n ∈ Jstar ⊓ Nfr') :
    tauB⁻¹ * n * tauB ∈ Jstar ⊓ Nfr' := by
  have h := tauB_inv_conj_mem_Nfr' hn.2
  have key := conj_mem_Jstar_of_mem_Gvis (c := tauB⁻¹) commute_tauB_tStar.inv_left hn.1
    (by simpa using Nfr'_le_Gvis h)
  exact ⟨by simpa using key, h⟩

theorem closure_Jstar_union_tauB :
    Subgroup.closure ((Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {tauB}) = Cgen := by
  rw [Set.union_comm, ← Set.insert_eq]
  rfl

theorem fix_aStarMinus_of_mem_Jstar {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) :
    g aStarMinus = aStarMinus := by
  refine (mul_rhoEquiv_zQ_mul_comm_iff (Hmat_le_Gmat hg.1)).1 ?_
  rw [rhoEquiv_zQ_mul_rStar]
  have c₁ : Commute g tStar := Subgroup.mem_centralizer_singleton_iff.1 hg.2
  have c₂ : Commute g xmat := by
    have := mul_xB_comm_of_mem_Gvis hg.1
    rwa [← xmat_eq_xB] at this
  exact c₁.mul_right c₂

theorem Cgen_inf_stabilizer_aStarMinus :
    Cgen ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStarMinus = Jstar := by
  ext g
  constructor
  · rintro ⟨hgC, hgs⟩
    exact mem_Jstar_of_fix_of_fix (Cgen_le_Gmat hgC) (fix_aStar_of_mem_Cgen hgC)
      (MulAction.mem_stabilizer_iff.1 hgs)
  · intro hg
    exact ⟨Jstar_le_Cgen hg, MulAction.mem_stabilizer_iff.2 (fix_aStarMinus_of_mem_Jstar hg)⟩

theorem natCard_Cgen_eq_orbit_mul_Jstar :
    Nat.card Cgen = Nat.card (MulAction.orbit Cgen aStarMinus) * Nat.card Jstar := by
  have h := card_orbit_mul_card_stabilizer (K := Cgen) aStarMinus
  rw [natCard_stabilizer_subgroup, Cgen_inf_stabilizer_aStarMinus] at h
  exact h.symm

@[expose] noncomputable def psiOn {H : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hH : H ≤ Gvis) :
    H →* GLV :=
  psiVis.comp (Subgroup.inclusion hH)

theorem psiOn_apply {H : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hH : H ≤ Gvis) (g : H) :
    psiOn hH g = psiVis ⟨g, hH g.2⟩ := rfl

theorem subgroupOf_inf_Nfr {H : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hH : H ≤ Gvis) :
    (H ⊓ Nfr).subgroupOf H = (MulAction.stabilizer GLV twoΩCls).comap (psiOn hH) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, psiOn_apply]
  constructor
  · intro h
    obtain ⟨hg, hf⟩ := mem_Nfr.1 (Subgroup.mem_inf.1 h).2
    exact hf
  · intro h
    exact Subgroup.mem_inf.2 ⟨g.2, mem_Nfr.2 ⟨hH g.2, h⟩⟩

theorem relIndex_inf_Nfr {H : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hH : H ≤ Gvis) :
    (H ⊓ Nfr).relIndex H = (MulAction.orbit (psiOn hH).range twoΩCls).ncard := by
  rw [Subgroup.relIndex, subgroupOf_inf_Nfr hH, Subgroup.index_comap, Subgroup.relIndex]
  have e : (MulAction.stabilizer GLV twoΩCls).subgroupOf (psiOn hH).range =
      MulAction.stabilizer (psiOn hH).range twoΩCls := by
    ext k
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl
  rw [e, MulAction.index_stabilizer]

theorem two_mul_natCard_Jstar (h : (Jstar ⊓ Nfr).relIndex Jstar = 46575) :
    2 * Nat.card Jstar = Nat.card (Jstar ⊓ Nfr : Subgroup _) * 93150 := by
  have h1 := Subgroup.relIndex_mul_card (Jstar ⊓ Nfr) Jstar
  rw [h, inf_of_le_left Jstar_inf_Nfr_le_Jstar] at h1
  rw [← h1]
  ring

end CFSG.Monster.AxisCount
