module

public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
import TauCeti.GroupTheory.SemidirectProduct
import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

namespace Sec45Shape

variable {H : Subgroup G} {h₀ : G}

theorem exists_eq_mul_commutator_of_mem_plane (h : RootHyp M V)
    (hS : Sec45Shape M V H h₀) {y x w : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H)
    (hw : w ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) :
    ∃ v ∈ V, ∃ t ∈ conjSubgroup y V, w = v * ⁅x, t⁆ := by
  classical
  have hW := hS.isElemAbelian h
  have hAW : conjSubgroup y V ≤ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy
  have hplane : V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ =
      Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) :=
    (sup_commutator_eq h hS hy hyV hx hxK).1
  have hwE : w ∈ V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ := by
    rw [hplane]
    exact hw
  have hBle : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤ Pc M V := by
    have h1 : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤
        V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ := le_sup_right
    rw [hplane] at h1
    exact h1.trans (xOf_inf_centralizer_le_and_card h hS hx hxK).1
  have hBN : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤
      Subgroup.normalizer (V : Set G) :=
    hBle.trans (h.toHyp.Pc_le_M.trans h.toHyp.le_normalizer)
  have hZA : Tim79a.xOf V H ≤ Subgroup.centralizer (conjSubgroup y V : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (congrArg Subtype.val (hW.1.is_comm.comm ⟨z, hz⟩ ⟨a, hAW ha⟩)).symm
  have hxN : x ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H (hS.Pc_le hx)
  have hxA : ∀ a ∈ conjSubgroup y V, ⁅x, a⁆ ∈ Tim79a.xOf V H := fun a ha =>
    (Tim79a.xOf V H).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN a).mp (hAW ha))
      ((Tim79a.xOf V H).inv_mem (hAW ha))
  have hBx : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤
      Subgroup.centralizer ({x} : Set G) := by
    have h1 : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ ≤
        V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ := le_sup_right
    rw [hplane] at h1
    exact h1.trans inf_le_right
  have hB := commutator_zpowers_eq_range (A := conjSubgroup y V) (x := x) hZA hxA hBx
  obtain ⟨v, hv, b, hb, hwb⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := V) hBN).mp hwE
  rw [hB] at hb
  obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.mp hb
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hz
  refine ⟨v, hv, t, t.2, ?_⟩
  have hb_eq : b = ⁅x, (t : G)⁆ := by
    rw [← hzb, ← ht]
    exact CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom_apply x hZA hxA t
  rw [hwb, hb_eq]

end Sec45Shape

namespace Sec5Hyp

private theorem le_xOf_sup_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    ∃ (H : Subgroup G) (h₀ y : G), Sec45Shape M V H h₀ ∧ y ∈ H ∧
      U ⊔ ⁅Pc M V, U⁆ ≤ Tim79a.xOf V H := by
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, -, hE, -, -⟩ := hS.exists_sigma_data hU
  refine ⟨hOf M V g, g, y, hSg, hyH, ?_⟩
  refine sup_le ?_ ?_
  · intro z hz
    have hz' : z ∈ conjSubgroup y V := by rwa [hUeq, hVy] at hz
    exact conjSubgroup_le_xOf_of_mem hyH hz'
  · intro z hz
    rw [hE] at hz
    exact hz.2

theorem mul_comm_of_mem_sup_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    ∀ x ∈ U ⊔ ⁅Pc M V, U⁆, ∀ y ∈ U ⊔ ⁅Pc M V, U⁆, x * y = y * x := by
  obtain ⟨H, h₀, y, hSg, -, hle⟩ := hS.le_xOf_sup_commutator hU
  have hW := hSg.isElemAbelian hS.toRootHyp
  intro x hx y hy
  exact congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hle hx⟩ ⟨y, hle hy⟩)

theorem mul_self_eq_one_of_mem_sup_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    ∀ x ∈ U ⊔ ⁅Pc M V, U⁆, x * x = 1 := by
  obtain ⟨H, h₀, y, hSg, -, hle⟩ := hS.le_xOf_sup_commutator hU
  have hW := hSg.isElemAbelian hS.toRootHyp
  intro x hx
  simpa [pow_two] using hW.2 x (hle hx)

theorem exists_conj_eq_conj_of_pow_three_mem (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1)
    (hab : (a * b) ^ 3 ∈ Pc M V) :
    ∃ r ∈ Pc M V, conjSubgroup a U' = conjSubgroup r (conjSubgroup b U) := by
  have haM : a ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 ha
  have hbM : b ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hb
  have hU₁ : conjSubgroup b U ∈ sigmaSet M V := hS.conj_mem_sigmaSet hbM hU
  have hU₂ : conjSubgroup a U' ∈ sigmaSet M V := hS.conj_mem_sigmaSet haM hU'
  have ha2 : a * a = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU a (Subgroup.mem_sup_left ha)
  have hb2 : b * b = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU' b (Subgroup.mem_sup_left hb)
  have ha_inv : a⁻¹ = a := (inv_eq_iff_mul_eq_one).mpr ha2
  have hb_inv : b⁻¹ = b := (inv_eq_iff_mul_eq_one).mpr hb2
  have hx1 : b * a * b⁻¹ ∈ conjSubgroup b U := by
    rw [mem_conjSubgroup, show b⁻¹ * (b * a * b⁻¹) * b = a by group]
    exact ha
  have hx2 : a * b * a⁻¹ ∈ conjSubgroup a U' := by
    rw [mem_conjSubgroup, show a⁻¹ * (a * b * a⁻¹) * a = b by group]
    exact hb
  have hprod : a * b * a⁻¹ * (b * a * b⁻¹) = (a * b) ^ 3 := by
    rw [ha_inv, hb_inv, pow_three']
    group
  have hx2eq : a * b * a⁻¹ = (a * b) ^ 3 * (b * a * b⁻¹)⁻¹ := by
    rw [← hprod]
    group
  have hx2sup : a * b * a⁻¹ ∈ conjSubgroup b U ⊔ Pc M V := by
    rw [hx2eq]
    have h := Subgroup.mul_mem_sup hab ((conjSubgroup b U).inv_mem hx1)
    rwa [sup_comm] at h
  have hx2ne : a * b * a⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have hb_eq : b = 1 := by
      have := congrArg (fun z => a⁻¹ * z * a) h
      rw [show a⁻¹ * (a * b * a⁻¹) * a = b by group] at this
      simpa using this
    exact hb_eq
  have hne : conjSubgroup a U' ⊓ (conjSubgroup b U ⊔ Pc M V) ≠ ⊥ := by
    intro hbot
    have hmem : a * b * a⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hx2, hx2sup⟩
    exact hx2ne (Subgroup.mem_bot.mp hmem)
  exact hS.stmt55 (conjSubgroup b U) hU₁ (conjSubgroup a U') hU₂ hne

theorem mem_centralizer_of_commutator_mem (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {v p : G} (hv : v ∈ U) (hv1 : v ≠ 1)
    (hp : p ∈ Pc M V) (hpv : ⁅p, v⁆ ∈ V) :
    p ∈ Subgroup.centralizer (U : Set G) := by
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, hyV, -, hC, -⟩ := hS.exists_sigma_data hU
  have hv' : v ∈ conjSubgroup y V := by rwa [hUeq, hVy] at hv
  have hk : p ∈ kOf V (hOf M V g) :=
    Sec45Shape.mem_kOf_of_commutator_mem hS.toRootHyp hSg hyH hyV hv' hv1 hp hpv
  have hpC : p ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G) := by
    rw [hC]
    exact Subgroup.mem_inf.mpr ⟨hp, hk⟩
  exact hpC.2

theorem commutator_commutator_eq_one (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {w x : G} (hw : w ∈ U ⊔ ⁅Pc M V, U⁆)
    (hx : x ∈ Pc M V) : ⁅⁅w, x⁆, x⁆ = 1 := by
  obtain ⟨H, h₀, y, hSg, -, hle⟩ := hS.le_xOf_sup_commutator hU
  exact Sec45Shape.commutator_commutator_eq_one hS.toRootHyp hSg hx (hle hw)

theorem sup_commutator_zpowers_eq (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {x : G} (hx : x ∈ Pc M V)
    (hxU : x ∉ Subgroup.centralizer (U : Set G)) :
    V ⊔ ⁅U, Subgroup.zpowers x⁆ = ⁅Pc M V, U⁆ ⊓ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, hyV, hE, hC, -⟩ := hS.exists_sigma_data hU
  have hxK : x ∉ kOf V (hOf M V g) := by
    intro hk
    apply hxU
    have hmem : x ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G) := by
      rw [hC]
      exact Subgroup.mem_inf.mpr ⟨hx, hk⟩
    exact hmem.2
  have hsup : V ⊔ ⁅conjSubgroup y V, Subgroup.zpowers x⁆ =
      Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x} : Set G) :=
    (Sec45Shape.sup_commutator_eq hS.toRootHyp hSg hyH hyV hx hxK).1
  have hleP : Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x} : Set G) ≤ Pc M V :=
    (Sec45Shape.xOf_inf_centralizer_le_and_card hS.toRootHyp hSg hx hxK).1
  rw [hE, hUeq, hVy, inf_assoc, inf_eq_right.mpr hleP, ← hsup]

theorem exists_eq_mul_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {x w : G} (hx : x ∈ Pc M V)
    (hxU : x ∉ Subgroup.centralizer (U : Set G)) (hw : w ∈ ⁅Pc M V, U⁆)
    (hwx : w * x = x * w) : ∃ v ∈ V, ∃ t ∈ U, w = v * ⁅x, t⁆ := by
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, hyV, hE, hC, -⟩ := hS.exists_sigma_data hU
  have hxK : x ∉ kOf V (hOf M V g) := by
    intro hk
    apply hxU
    have hmem : x ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G) := by
      rw [hC]
      exact Subgroup.mem_inf.mpr ⟨hx, hk⟩
    exact hmem.2
  have hwW : w ∈ Tim79a.xOf V (hOf M V g) := by
    rw [hE] at hw
    exact hw.2
  have hwC : w ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwx
  obtain ⟨v, hv, t, ht, hwt⟩ :=
    Sec45Shape.exists_eq_mul_commutator_of_mem_plane hS.toRootHyp hSg hyH hyV hx hxK
      (Subgroup.mem_inf.mpr ⟨hwW, hwC⟩)
  refine ⟨v, hv, t, ?_, hwt⟩
  simpa [hUeq, hVy] using ht

end Sec5Hyp

end CFSG.RankThree.GF2n.Tim81

end
