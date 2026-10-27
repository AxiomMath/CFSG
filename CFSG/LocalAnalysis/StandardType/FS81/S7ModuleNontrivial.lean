module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped commutatorElement

local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "s₇" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q₇" => EPilot.highRadical Tag.E7 (ZMod 2)

section E7Model


private lemma pinnedElt_mem_highRadical_of_mem_Deg1 {τ : Tag} {K : Type} [Field K]
    (hnode : Heis.iθ τ = highNode τ) {β : Fin τ.rank → ℤ} (hβ : β ∈ Heis.Deg1 τ) :
    EPilot.pinnedElt τ β (1 : K) ∈ EPilot.highRadical τ K := by
  refine Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan ?_ (1 : K))
  rw [EPilot.mem_parabolicRadicalRoots_perpNodes]
  exact ⟨(Heis.CoordAux.mem_Deg1.1 hβ).1,
    by rw [← hnode, (Heis.CoordAux.mem_Deg1.1 hβ).2]; norm_num⟩

private lemma heisCoord_eq_zero_of_mem_zpowers_pinnedElt_highRoot {τ : Tag} {K : Type} [Field K]
    {x : adjointGroup τ K}
    (hx : x ∈ Subgroup.zpowers (EPilot.pinnedElt τ (highRoot τ) (1 : K))) :
    Heis.heisCoord τ K (x : ModGL τ K) = 0 := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hs : ((EPilot.pinnedElt τ (highRoot τ) (1 : K) : adjointGroup τ K) : ModGL τ K) ∈
      Heis.Uθ τ K :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have hpow : (((EPilot.pinnedElt τ (highRoot τ) (1 : K) : adjointGroup τ K) :
      ModGL τ K) ^ n) ∈ Heis.Uθ τ K :=
    Subgroup.zpow_mem (Heis.Uθ τ K) hs n
  have hQ : (((EPilot.pinnedElt τ (highRoot τ) (1 : K) : adjointGroup τ K) :
      ModGL τ K) ^ n) ∈ Heis.Qθ τ K :=
    Heis.Uθ_le_Qθ hpow
  have h0 : Heis.heisCoord τ K ((((EPilot.pinnedElt τ (highRoot τ) (1 : K) :
      adjointGroup τ K) : ModGL τ K)) ^ n) = 0 :=
    ((Heis.heisCoord_spec τ K).eq_zero_iff _ hQ).2 hpow
  rw [← hn, Subgroup.coe_zpow]
  exact h0

private lemma heisCoord_commutator_E7 {μ γ : Fin (Tag.rank .E7) → ℤ}
    (hμD : μ ∈ Heis.Deg1 .E7) (hγ_root : IsRoot .E7 γ) (hγ0 : γ (Heis.iθ .E7) = 0)
    (hν_root : μ + γ ∈ rootFinset .E7)
    (hμQ : pinnedX .E7 (ZMod 2) μ 1 ∈ Heis.Qθ .E7 (ZMod 2)) (hne : μ + γ ≠ μ) :
    Heis.heisCoord .E7 (ZMod 2)
      (pinnedX .E7 (ZMod 2) γ 1 * pinnedX .E7 (ZMod 2) μ 1 *
        (pinnedX .E7 (ZMod 2) γ 1)⁻¹ * (pinnedX .E7 (ZMod 2) μ 1)⁻¹) (μ + γ) = 1 := by
  have hkey := EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E7) (K := ZMod 2)
    (Or.inr (Or.inl rfl)) hγ_root hγ0 (1 : ZMod 2) hμQ
  have hsingle : Heis.heisCoord .E7 (ZMod 2) (pinnedX .E7 (ZMod 2) μ 1) = Pi.single μ 1 :=
    (Heis.heisCoord_spec .E7 (ZMod 2)).pinnedX_deg1 μ hμD 1
  have hXcoord : Heis.heisCoord .E7 (ZMod 2)
      (pinnedX .E7 (ZMod 2) γ 1 * pinnedX .E7 (ZMod 2) μ 1 *
        (pinnedX .E7 (ZMod 2) γ 1)⁻¹) (μ + γ) = 1 := by
    rw [hkey.2 (μ + γ), hsingle, if_pos hν_root]
    have hsub : μ + γ - γ = μ := by abel
    rw [hsub, Pi.single_eq_of_ne hne, Pi.single_eq_same]
    norm_num
  rw [(Heis.heisCoord_spec .E7 (ZMod 2)).mul _ hkey.1 _ (inv_mem hμQ),
    Pi.add_apply, hXcoord, Heis.heisCoord_inv hμQ, hsingle, Pi.neg_apply,
    Pi.single_eq_of_ne hne, neg_zero, add_zero]

private lemma heisCoord_conj_deg_zero_E8 {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ)
    (hγ0 : γ (Heis.iθ .E8) = 0)
    {q : ModGL .E8 (GaloisField 2 1)} (hq : q ∈ Heis.Qθ .E8 (GaloisField 2 1)) :
    Heis.heisCoord .E8 (GaloisField 2 1)
      (pinnedX .E8 (GaloisField 2 1) γ 1 * q * (pinnedX .E8 (GaloisField 2 1) γ 1)⁻¹) =
      Heis.heisCoord .E8 (GaloisField 2 1) q +
        (fun ρ => if ρ ∈ rootFinset .E8 then (1 : GaloisField 2 1) *
          Heis.heisCoord .E8 (GaloisField 2 1) q (ρ - γ) else 0) := by
  funext ρ
  exact (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8) (K := GaloisField 2 1)
    (Or.inr (Or.inr rfl)) hγ hγ0 (1 : GaloisField 2 1) hq).2 ρ

private lemma commutator_notMem_zpowers_E7 {μ γ : Fin (Tag.rank .E7) → ℤ}
    (hμD : μ ∈ Heis.Deg1 .E7) (hγ_root : IsRoot .E7 γ) (hγ0 : γ (Heis.iθ .E7) = 0)
    (hν_root : μ + γ ∈ rootFinset .E7)
    (hμQ : pinnedX .E7 (ZMod 2) μ 1 ∈ Heis.Qθ .E7 (ZMod 2)) (hne : μ + γ ≠ μ) :
    (EPilot.pinnedElt .E7 γ (1 : ZMod 2) * EPilot.pinnedElt .E7 μ (1 : ZMod 2) *
      (EPilot.pinnedElt .E7 γ (1 : ZMod 2))⁻¹ *
      (EPilot.pinnedElt .E7 μ (1 : ZMod 2))⁻¹ : adjointGroup .E7 (ZMod 2)) ∉
      Subgroup.zpowers s₇ := by
  intro hc
  have hzero := heisCoord_eq_zero_of_mem_zpowers_pinnedElt_highRoot (τ := .E7) (K := ZMod 2) hc
  have h1 : Heis.heisCoord .E7 (ZMod 2)
      (((EPilot.pinnedElt .E7 γ (1 : ZMod 2) * EPilot.pinnedElt .E7 μ (1 : ZMod 2) *
        (EPilot.pinnedElt .E7 γ (1 : ZMod 2))⁻¹ *
        (EPilot.pinnedElt .E7 μ (1 : ZMod 2))⁻¹ : adjointGroup .E7 (ZMod 2)) :
          ModGL .E7 (ZMod 2))) (μ + γ) = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, EPilot.pinnedElt]
    exact heisCoord_commutator_E7 hμD hγ_root hγ0 hν_root hμQ hne
  have h0 := congrFun hzero (μ + γ)
  exact one_ne_zero (h1.symm.trans h0)

theorem exists_perpLevi_E7_not_trivial_on_highRadical :
    ∃ j ∈ EPilot.perpLevi .E7 (ZMod 2), ∃ y ∈ Q₇, j * y * j⁻¹ * y⁻¹ ∉ Subgroup.zpowers s₇ := by
  obtain ⟨j', hj'ne, hj'root⟩ :=
    EPilot.exists_add_single_mem_rootFinset_of_deg_one (τ := .E7) (Or.inr (Or.inl rfl))
      (Pi.single (0 : Fin 7) 1) (mem_rootFinset.2 (isRoot_single .E7 0)) (by decide)
      (by decide)
  set μ : Fin (Tag.rank .E7) → ℤ := Pi.single (0 : Fin 7) 1 with hμdef
  set γ : Fin (Tag.rank .E7) → ℤ := Pi.single j' 1 with hγdef
  have hμ_root : IsRoot .E7 μ := by rw [hμdef]; exact isRoot_single .E7 0
  have hμ1 : μ (Heis.iθ .E7) = 1 := by rw [hμdef]; decide
  have hμD : μ ∈ Heis.Deg1 .E7 := Heis.CoordAux.mem_Deg1.2 ⟨hμ_root, hμ1⟩
  have hγ_root : IsRoot .E7 γ := by rw [hγdef]; exact isRoot_single .E7 j'
  have hγ0 : γ (Heis.iθ .E7) = 0 := by
    rw [hγdef]
    simp [Ne.symm hj'ne]
  have hγperp : γ ∈ EPilot.perpRoots .E7 := EPilot.single_mem_perpRoots hj'ne
  have hν_root : μ + γ ∈ rootFinset .E7 := by rw [hμdef, hγdef]; exact hj'root
  have hγ_ne_zero : γ ≠ 0 := by
    rw [hγdef]
    intro h
    have := congrFun h j'
    simp at this
  have hne : μ + γ ≠ μ := by
    intro h
    apply hγ_ne_zero
    have h1 : μ + γ = μ + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h1
  have hyQ : pinnedX .E7 (ZMod 2) μ 1 ∈ Heis.Qθ .E7 (ZMod 2) := by
    refine pinnedX_mem_rootSpan ?_ 1
    rw [Heis.CoordAux.mem_radRoots_iff]
    exact Or.inl hμD
  exact ⟨EPilot.pinnedElt .E7 γ (1 : ZMod 2), EPilot.pinnedElt_mem_perpLevi hγperp 1,
    EPilot.pinnedElt .E7 μ (1 : ZMod 2), pinnedElt_mem_highRadical_of_mem_Deg1 (by rfl) hμD,
    commutator_notMem_zpowers_E7 hμD hγ_root hγ0 hν_root hyQ hne⟩

private lemma modW_commutator_notMem_zpowers_E8 {γ₇ : Fin (Tag.rank .E7) → ℤ}
    {δ ν : Fin (Tag.rank .E8) → ℤ}
    (hej : e7Incl (EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2)) =
      EPilot.pinnedElt .E8 δ (1 : GaloisField 2 1))
    (hδ_root : IsRoot .E8 δ) (hδ0 : δ (Heis.iθ .E8) = 0)
    (hνδ_root : ν + δ ∈ rootFinset .E8) {w : adjointGroup .E8 (GaloisField 2 1)}
    (hwQ : (w : ModGL .E8 (GaloisField 2 1)) ∈ Heis.Qθ .E8 (GaloisField 2 1))
    (hw_ν : Heis.heisCoord .E8 (GaloisField 2 1)
      ((w : adjointGroup .E8 (GaloisField 2 1)) : ModGL .E8 (GaloisField 2 1)) ν = 1) :
    e7Incl (EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2)) * w *
      (e7Incl (EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2)))⁻¹ * w⁻¹ ∉ Subgroup.zpowers tθ := by
  intro hc
  have hz_coord : Heis.heisCoord .E8 (GaloisField 2 1)
      (((e7Incl (EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2)) * w *
        (e7Incl (EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2)))⁻¹ * w⁻¹ :
          adjointGroup .E8 (GaloisField 2 1)) : ModGL .E8 (GaloisField 2 1))) (ν + δ) = 1 := by
    rw [hej]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, EPilot.pinnedElt]
    have hXQ := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8) (K := GaloisField 2 1)
      (Or.inr (Or.inr rfl)) hδ_root hδ0 (1 : GaloisField 2 1) hwQ).1
    rw [(Heis.heisCoord_spec .E8 (GaloisField 2 1)).mul _ hXQ _ (inv_mem hwQ),
      heisCoord_conj_deg_zero_E8 hδ_root hδ0 hwQ, Pi.add_apply, Pi.add_apply,
      Heis.heisCoord_inv hwQ]
    have hsub : ν + δ - δ = ν := by abel
    rw [hsub, if_pos hνδ_root, Pi.neg_apply, hw_ν]
    ring
  have hzero := heisCoord_eq_zero_of_mem_zpowers_pinnedElt_highRoot (τ := .E8)
    (K := GaloisField 2 1) hc
  have h0 := congrFun hzero (ν + δ)
  rw [hz_coord] at h0
  exact one_ne_zero h0

theorem exists_perpLevi_E7_not_trivial_on_modW :
    ∃ j ∈ EPilot.perpLevi .E7 (ZMod 2), ∃ w ∈ modW Qθ tθ (e7Incl s₇),
      e7Incl j * w * (e7Incl j)⁻¹ * w⁻¹ ∉ Subgroup.zpowers tθ := by
  set μ : Fin (Tag.rank .E8) → ℤ := Pi.single (7 : Fin 8) 1 with hμdef
  set γ₇ : Fin (Tag.rank .E7) → ℤ := Pi.single (6 : Fin 7) 1 with hγdef
  set θ' : Fin (Tag.rank .E8) → ℤ := E8Pilot.e7Embed (highRoot .E7) with hθ'def
  set δ : Fin (Tag.rank .E8) → ℤ := E8Pilot.e7Embed γ₇ with hδdef
  set ν : Fin (Tag.rank .E8) → ℤ := μ + θ' with hνdef
  have hμ_root : IsRoot .E8 μ := by rw [hμdef]; exact isRoot_single .E8 7
  have hμ1 : μ (Heis.iθ .E8) = 1 := by rw [hμdef]; decide +kernel
  have hμD : μ ∈ Heis.Deg1 .E8 := Heis.CoordAux.mem_Deg1.2 ⟨hμ_root, hμ1⟩
  have hγ_root : IsRoot .E7 γ₇ := by rw [hγdef]; exact isRoot_single .E7 6
  have hγ0 : γ₇ (Heis.iθ .E7) = 0 := by rw [hγdef]; decide +kernel
  have hγperp : γ₇ ∈ EPilot.perpRoots .E7 := by
    rw [hγdef]
    have h6 : (6 : Fin 7) ≠ highNode .E7 := by
      rw [show highNode .E7 = (0 : Fin 7) from rfl]
      decide
    exact EPilot.single_mem_perpRoots h6
  have hδ_root : IsRoot .E8 δ := by rw [hδdef]; exact E8Pilot.isRoot_e7Embed hγ_root
  have hδ0 : δ (Heis.iθ .E8) = 0 := by rw [hδdef]; exact E8Pilot.e7Embed_highNode γ₇
  have hθ'_root : IsRoot .E8 θ' := by
    rw [hθ'def]; exact E8Pilot.isRoot_e7Embed (isRoot_highRoot .E7)
  have hθ'0 : θ' (Heis.iθ .E8) = 0 := by
    rw [hθ'def]; exact E8Pilot.e7Embed_highNode (highRoot .E7)
  have hν_root : ν ∈ rootFinset .E8 := by rw [hνdef, hμdef, hθ'def]; decide +kernel
  have hνδ_root : ν + δ ∈ rootFinset .E8 := by
    rw [hνdef, hμdef, hθ'def, hδdef]; decide +kernel
  have hμQ : pinnedX .E8 (GaloisField 2 1) μ 1 ∈ Heis.Qθ .E8 (GaloisField 2 1) := by
    refine pinnedX_mem_rootSpan ?_ 1
    rw [Heis.CoordAux.mem_radRoots_iff]
    exact Or.inl hμD
  have hj : EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2) ∈ EPilot.perpLevi .E7 (ZMod 2) :=
    EPilot.pinnedElt_mem_perpLevi hγperp 1
  have hej : e7Incl (EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2)) =
      EPilot.pinnedElt .E8 δ (1 : GaloisField 2 1) := by
    rw [hδdef, e7Incl_pinnedElt hγ_root 1, map_one]
  have hσ : e7Incl s₇ = EPilot.pinnedElt .E8 θ' (1 : GaloisField 2 1) := by
    rw [show s₇ = EPilot.pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) from rfl]
    rw [e7Incl_pinnedElt (isRoot_highRoot .E7) 1, map_one, hθ'def]
  set y : adjointGroup .E8 (GaloisField 2 1) := EPilot.pinnedElt .E8 μ 1 with hydef
  have hy : y ∈ Qθ := by
    rw [hydef]; exact pinnedElt_mem_highRadical_of_mem_Deg1 (by rfl) hμD
  have hsingle_y : Heis.heisCoord .E8 (GaloisField 2 1)
      (pinnedX .E8 (GaloisField 2 1) μ 1) = Pi.single μ 1 :=
    (Heis.heisCoord_spec .E8 (GaloisField 2 1)).pinnedX_deg1 μ hμD 1
  have hkey_y := EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8) (K := GaloisField 2 1)
    (Or.inr (Or.inr rfl)) hθ'_root hθ'0 (1 : GaloisField 2 1) hμQ
  set w : adjointGroup .E8 (GaloisField 2 1) :=
    e7Incl s₇ * y * (e7Incl s₇)⁻¹ * y⁻¹ with hwdef
  have hwQ : (w : ModGL .E8 (GaloisField 2 1)) ∈ Heis.Qθ .E8 (GaloisField 2 1) := by
    rw [hwdef, hσ, hydef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, EPilot.pinnedElt]
    exact mul_mem hkey_y.1 (inv_mem hμQ)
  have hw : w ∈ modW Qθ tθ (e7Incl s₇) := by
    rw [hwdef]
    refine Subgroup.mem_sup_left ?_
    have hmem : ⁅e7Incl s₇, y⁆ ∈ ⁅Subgroup.zpowers (e7Incl s₇), Qθ⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) hy
    rw [Subgroup.commutator_comm] at hmem
    exact hmem
  refine ⟨EPilot.pinnedElt .E7 γ₇ (1 : ZMod 2), hj, w, hw, ?_⟩
  have hθ'_ne_zero : θ' ≠ 0 := hθ'_root.ne_zero
  have hne_ν' : ν ≠ μ := by
    rw [hνdef]
    intro h
    apply hθ'_ne_zero
    have h1 : μ + θ' = μ + 0 := by rw [add_zero]; exact h
    exact add_left_cancel h1
  have hw_ν : Heis.heisCoord .E8 (GaloisField 2 1)
      ((w : adjointGroup .E8 (GaloisField 2 1)) : ModGL .E8 (GaloisField 2 1)) ν = 1 := by
    rw [hwdef, hσ, hydef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, EPilot.pinnedElt]
    rw [(Heis.heisCoord_spec .E8 (GaloisField 2 1)).mul _ hkey_y.1 _ (inv_mem hμQ),
      heisCoord_conj_deg_zero_E8 hθ'_root hθ'0 hμQ, Heis.heisCoord_inv hμQ, hsingle_y]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
    rw [if_pos hν_root]
    have hsubν : ν - θ' = μ := by rw [hνdef]; abel
    rw [hsubν]
    simp [hne_ν']
  exact modW_commutator_notMem_zpowers_E8 hej hδ_root hδ0 hνδ_root hwQ hw_ν

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
