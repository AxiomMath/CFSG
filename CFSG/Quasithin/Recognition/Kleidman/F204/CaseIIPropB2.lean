module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIPropB1
public import CFSG.Quasithin.Recognition.Kleidman.F204.NatAThree
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem elemAbelian_comm' {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

section PropB2

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem propB_quad {ρ : G} (hρα' : ρ ∈ stab α') (hρβ : ρ ∈ stab β) (hρ3 : ρ ^ 3 = 1)
    (hρ1 : ρ ≠ 1) :
    ∃ u ∈ nbrs α', vtype u = true ∧
      ∀ z ∈ Zv u, ∀ x ∈ Qv α', z * x * z⁻¹ * x⁻¹ ∈ Subgroup.centralizer (Qv α' : Set G) := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα'f, -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hαβ : α ∈ nbrs β := (show (graph _ _ _).Adj α β from hc.adj).symm
  have hV2β : IsElemAbelian 2 (Vn β) := hA.isElemAbelian_Vn hb3 β
  have hV2α' : IsElemAbelian 2 (Vn α') := hA.isElemAbelian_Vn hb3 α'
  obtain ⟨k, hkK, w, hw, hkw⟩ := t1II_comm_ne F hT1 hc hII
  obtain ⟨u, hu, z0, hz0, hkz0⟩ : ∃ u ∈ nbrs α', ∃ z ∈ Zv u, k * z ≠ z * k := by
    by_contra hcon
    push Not at hcon
    apply hkw
    have : Vn α' ≤ Subgroup.centralizer {k} := by
      refine iSup₂_le fun μ hμ => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcon μ hμ x hx).symm
    have := this hw
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  have huvt : vtype u = true := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj α' u from hu)
    rw [hα'f] at this
    simpa using this.symm
  have hαu : α' ∈ nbrs u := mem_nbrs_symm hu
  have hρu : ρ ∈ stab u := three_mem_stab_nbr F hα'f hu hρα' hρ3
  have hρQu : ρ ∉ Qv u := fun h => hρ1 (eq_one_of_mem_Qv_of_pow_three h hρ3)
  have hkQu : k ∉ Qv u := by
    intro hk
    exact hkz0 (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv u hz0).2 k hk)
  have hρK : ∀ k ∈ Vn β ⊓ Qv α', ρ * k * ρ⁻¹ ∈ Vn β ⊓ Qv α' := by
    intro k hk
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hρβ) k).mp hk.1
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab α') hρα') k).mp hk.2
  have hcover := klein_cover F huvt hαu (inf_le_right : Vn β ⊓ Qv α' ≤ Qv α') hρu hρ3 hρQu hρK
    ⟨k, hkK, hkQu⟩
  refine ⟨u, hu, huvt, ?_⟩
  intro z hz x hx
  have hQα'u : Qv α' ≤ stab u := hA.Qv_le_stab_of_mem_nbrs hu
  have hzcQ : ∀ q ∈ Qv u, ∀ y ∈ Zv u, q * y = y * q := fun q hq y hy =>
    Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv u hy).2 q hq
  obtain ⟨k', hk', hq⟩ := hcover x hx
  have hxk : x = k' * (k'⁻¹ * x) := by group
  have hzq : z * (k'⁻¹ * x) = (k'⁻¹ * x) * z := (hzcQ _ hq z hz).symm
  have hcomm : z * x * z⁻¹ * x⁻¹ = z * k' * z⁻¹ * k'⁻¹ := by
    set q := k'⁻¹ * x with hqdef
    have hzq' : q * z⁻¹ = z⁻¹ * q := by
      calc q * z⁻¹ = z⁻¹ * (z * q) * z⁻¹ := by group
        _ = z⁻¹ * (q * z) * z⁻¹ := by rw [← hzq]
        _ = z⁻¹ * q := by group
    calc z * x * z⁻¹ * x⁻¹ = z * (k' * q) * z⁻¹ * (k' * q)⁻¹ := by rw [← hxk]
      _ = z * k' * (q * z⁻¹) * q⁻¹ * k'⁻¹ := by group
      _ = z * k' * (z⁻¹ * q) * q⁻¹ * k'⁻¹ := by rw [hzq']
      _ = z * k' * z⁻¹ * k'⁻¹ := by group
  rw [hcomm]
  have hk'V : k' ∈ Vn β := hk'.1
  have hk'Q : k' ∈ Qv α' := hk'.2
  have hzW : z ∈ Vn α' := hA.Zv_le_Vn hu hz
  have hk'u : k' ∈ stab u := hQα'u hk'Q
  have hk'α' : k' ∈ stab α' := hVβ hk'V
  have hzβ : z ∈ stab β := hWβ hzW
  have hcZ : z * k' * z⁻¹ * k'⁻¹ ∈ Zv u := by
    have e : z * k' * z⁻¹ * k'⁻¹ = z * (k' * z⁻¹ * k'⁻¹) := by group
    rw [e]
    exact (Zv u).mul_mem hz ((Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv u hk'u) _).mp
      ((Zv u).inv_mem hz))
  have hcV : z * k' * z⁻¹ * k'⁻¹ ∈ Vn β := by
    have e : z * k' * z⁻¹ * k'⁻¹ = (z * k' * z⁻¹) * k'⁻¹ := rfl
    rw [e]
    exact (Vn β).mul_mem ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β hzβ) _).mp hk'V)
      ((Vn β).inv_mem hk'V)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k'', hk'', hq''⟩ := hcover y hy
  have hyk : y = k'' * (k''⁻¹ * y) := by group
  have h1 : (k''⁻¹ * y) * (z * k' * z⁻¹ * k'⁻¹) = (z * k' * z⁻¹ * k'⁻¹) * (k''⁻¹ * y) :=
    hzcQ _ hq'' _ hcZ
  have h2 : k'' * (z * k' * z⁻¹ * k'⁻¹) = (z * k' * z⁻¹ * k'⁻¹) * k'' :=
    elemAbelian_comm' hV2β hk''.1 hcV
  rw [hyk]
  calc k'' * (k''⁻¹ * y) * (z * k' * z⁻¹ * k'⁻¹)
      = k'' * ((k''⁻¹ * y) * (z * k' * z⁻¹ * k'⁻¹)) := by group
    _ = k'' * ((z * k' * z⁻¹ * k'⁻¹) * (k''⁻¹ * y)) := by rw [h1]
    _ = (k'' * (z * k' * z⁻¹ * k'⁻¹)) * (k''⁻¹ * y) := by group
    _ = ((z * k' * z⁻¹ * k'⁻¹) * k'') * (k''⁻¹ * y) := by rw [h2]
    _ = (z * k' * z⁻¹ * k'⁻¹) * (k'' * (k''⁻¹ * y)) := by group

end PropB2

end CFSG.Quasithin.Kleidman.F204
