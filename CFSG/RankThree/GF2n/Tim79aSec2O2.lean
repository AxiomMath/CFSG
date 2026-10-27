module

public import CFSG.RankThree.GF2n.Tim79aSec2Basic
public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
public import CFSG.Foundations
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.RankThree.GF2n.Tim78S4Basic
public import CFSG.RankThree.GF2n.Tim79aSec2Defs
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem eOf_inf_V_ne_bot : eOf H ⊓ V ≠ ⊥ := by
  have hP2 : IsPGroup 2 P := hc.isPGroup_P
  have hE2 : IsPGroup 2 (eOf H) := (isPGroup_pCore H).to_le (eOf_le_pCore H)
  have hO : inSubgroup (pCore 2) H ≠ ⊥ := hc.o2H
  have hEne : eOf H ≠ ⊥ := by
    have := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      (isPGroup_pCore H) (isPGroup_pCore H) hO Subgroup.le_normalizer
    exact this
  have hPN : P ≤ Subgroup.normalizer (eOf H : Set G) := fun p hp =>
    H_le_normalizer_eOf H (hc.PleH hp)
  have := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two hP2
    hE2 hEne hPN
  rwa [hc.centralizer_P_eq] at this

theorem pCoreH_le_M : inSubgroup (pCore 2) H ≤ M := by
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.eOf_inf_V_ne_bot
  obtain ⟨heE, heV⟩ := Subgroup.mem_inf.mp he
  intro o ho
  have hcomm : o * e = e * o := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heE).2 o ho
  exact hc.mem_M_of_commute heV (fun h => he1 (Subtype.ext h)) hcomm

theorem pCoreH_le_normalizer_conj {h : G} (hh : h ∈ H) :
    inSubgroup (pCore 2) H ≤ Subgroup.normalizer (conjSubgroup h V : Set G) := by
  intro o ho
  have ho' : h⁻¹ * o * h ∈ inSubgroup (pCore 2) H := by
    have := (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two H).2.2 (H.inv_mem hh)) o).mp ho
    simpa using this
  have hM : h⁻¹ * o * h ∈ Subgroup.normalizer (V : Set G) :=
    hc.normalizer_eq ▸ hc.pCoreH_le_M ho'
  rw [Subgroup.mem_normalizer_iff] at hM ⊢
  intro y
  rw [mem_conjSubgroup, mem_conjSubgroup]
  have := hM (h⁻¹ * y * h)
  rw [show h⁻¹ * o * h * (h⁻¹ * y * h) * (h⁻¹ * o * h)⁻¹ = h⁻¹ * (o * y * o⁻¹) * h by group] at this
  exact this

theorem eOf_inf_conj_ne_bot {h : G} (hh : h ∈ H) : eOf H ⊓ conjSubgroup h V ≠ ⊥ := by
  have hE : conjSubgroup h (eOf H) = eOf H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_eOf H hh)
  have e : eOf H ⊓ conjSubgroup h V = conjSubgroup h (eOf H ⊓ V) := by
    rw [conjSubgroup_inf, hE]
  rw [e]
  intro hbot
  apply hc.eOf_inf_V_ne_bot
  have : (eOf H ⊓ V).map (MulAut.conj h).toMonoidHom = ⊥ := hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj h).injective).mp this

theorem V_inf_wOf_eq : V ⊓ wOf V H = V ⊓ inSubgroup (pCore 2) H := by
  refine le_antisymm (inf_le_inf le_rfl (wOf_le_pCore V H)) fun x hx => ?_
  refine ⟨hx.1, inf_pCore_le_wOf (U := V) ⟨1, H.one_mem, (conjSubgroup_one V).symm⟩ ⟨hx.1, hx.2⟩⟩

theorem V_inf_wOf_ne_bot : V ⊓ wOf V H ≠ ⊥ := by
  rw [hc.V_inf_wOf_eq]
  intro hbot
  apply hc.eOf_inf_V_ne_bot
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ V ⊓ inSubgroup (pCore 2) H := ⟨hx.2, eOf_le_pCore H hx.1⟩
  rw [hbot] at this
  exact this

theorem not_V_le_wOf : ¬ V ≤ wOf V H := fun h => hc.notLe (h.trans (wOf_le_pCore V H))

theorem conj_inf_wOf_ne_bot {h : G} (hh : h ∈ H) : conjSubgroup h V ⊓ wOf V H ≠ ⊥ := by
  have hW : conjSubgroup h (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hh)
  have e : conjSubgroup h V ⊓ wOf V H = conjSubgroup h (V ⊓ wOf V H) := by
    rw [conjSubgroup_inf, hW]
  rw [e]
  intro hbot
  apply hc.V_inf_wOf_ne_bot
  have : (V ⊓ wOf V H).map (MulAut.conj h).toMonoidHom = ⊥ := hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj h).injective).mp this

theorem commute_of_mem_inf_pCore {g h : G} (hg : g ∈ H) (hh : h ∈ H) {x y : G}
    (hx : x ∈ conjSubgroup g V ⊓ inSubgroup (pCore 2) H)
    (hy : y ∈ conjSubgroup h V ⊓ inSubgroup (pCore 2) H) : x * y = y * x := by
  obtain ⟨hxA, hxO⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyB, hyO⟩ := Subgroup.mem_inf.mp hy
  by_cases hAB : conjSubgroup g V = conjSubgroup h V
  · exact congrArg Subtype.val ((isElemAbelian_conjSubgroup hc.elemAb g).1.is_comm.comm
      ⟨x, hxA⟩ ⟨y, hAB ▸ hyB⟩)
  · have hbot : conjSubgroup g V ⊓ conjSubgroup h V = ⊥ := by
      have hTIg := isTI_conjSubgroup hc.ti g
      have hk : conjSubgroup (h * g⁻¹) (conjSubgroup g V) = conjSubgroup h V := by
        rw [conjSubgroup_conjSubgroup, show h * g⁻¹ * g = h by group]
      have h' := inf_conjSubgroup_eq_bot_of_isTI hTIg (g := h * g⁻¹)
        (by rw [hk]; exact fun h'' => hAB h''.symm)
      rwa [hk] at h'
    have hB : x * y * x⁻¹ ∈ conjSubgroup h V :=
      (Subgroup.mem_normalizer_iff.mp (hc.pCoreH_le_normalizer_conj hh hxO) y).mp hyB
    have hA : y * x⁻¹ * y⁻¹ ∈ conjSubgroup g V :=
      (Subgroup.mem_normalizer_iff.mp (hc.pCoreH_le_normalizer_conj hg hyO) x⁻¹).mp
        ((conjSubgroup g V).inv_mem hxA)
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ conjSubgroup g V ⊓ conjSubgroup h V := by
      refine ⟨?_, (conjSubgroup h V).mul_mem hB ((conjSubgroup h V).inv_mem hyB)⟩
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact (conjSubgroup g V).mul_mem hxA hA
    rw [hbot, Subgroup.mem_bot] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]

theorem wOf_isElemAbelian : Assembly.IsElemAbelian 2 (wOf V H) := by
  unfold wOf
  rw [iSup_subtype']
  refine CFSG.CGT.Timmesfeld75.isElemAbelian_iSup_of_comm
    (fun U : ↥(omegaOf V H) => (U : Subgroup G) ⊓ inSubgroup (pCore 2) H) ?_ ?_
  · rintro ⟨U, h, hh, rfl⟩ x hx
    exact (isElemAbelian_conjSubgroup hc.elemAb h).2 x hx.1
  · rintro ⟨U, g, hg, rfl⟩ ⟨U', h, hh, rfl⟩ a ha b hb
    exact hc.commute_of_mem_inf_pCore hg hh ha hb

end MinCex

end CFSG.RankThree.GF2n.Tim79a
