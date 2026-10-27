module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7D
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7A

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
private theorem comm_of_elem {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

private theorem vtype_of_mem_nbrs {H M : Subgroup G} {u v : Geo H M} (h : v ∈ nbrs u) :
    vtype v = !vtype u := by
  have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
  cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
  (hb7 : 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hF1 : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → ∀ d ∈ nbrs x, ∀ d' ∈ nbrs x,
    d ≠ d' → Zv d ⊓ Zv d' = ⊥)
include F hT1 hc hII hb7 hF1

theorem Vball_inf_Qv_le {γ ε : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hγ : γ ∈ nbrs α')
    (hε : ε ∈ nbrs γ) (hdε : dist β ε + 3 = bMin (P1 L1 L2 S) (P2 L1 L2 S)) :
    Vball 3 β ⊓ Qv ε ≤ Qv γ := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  have hγt : vtype γ = true := by rw [vtype_of_mem_nbrs hγ, hα']; rfl
  have hU2 := hA.isElemAbelian_Vball (n := 3) (by omega) β
  intro y hy
  obtain ⟨hyU, hyε⟩ := Subgroup.mem_inf.mp hy
  by_contra hyγ
  have hγε : γ ∈ nbrs ε := mem_nbrs_symm hε
  have hyγs : y ∈ stab γ := hA.Qv_le_stab_of_mem_nbrs hγε hyε
  have hyεs : y ∈ stab ε := pCoreOf_le 2 _ hyε
  have hy2 : y ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hU2.2 y hyU
  have hα'γ : α' ∈ nbrs γ := mem_nbrs_symm hγ
  have hne : α' ≠ ε := by
    intro h
    have := hc.dist_eq'
    rw [h] at this
    omega
  have hyα' : y ∉ stab α' := fun h =>
    hyγ (mem_Qv_of_fix_two F hγt hε hα'γ hne hyγs hyεs h hy2)
  set yy : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨y, (mem_stab.mp hyγs).1⟩ with hyy
  have hyyγ : yy • γ = γ := smul_eq_of_mem_stab (g := yy) hyγs
  have hα'' : yy • α' ∈ nbrs γ := by
    have := (smul_adj yy).mpr (show (graph _ _ _).Adj γ α' from hα'γ)
    rwa [hyyγ] at this
  have hne' : α' ≠ yy • α' := fun h => hyα' (mem_stab_of_smul_eq (g := yy) h.symm)
  have hbot := hF1 γ hγt α' hα'γ (yy • α') hα'' hne'
  apply Zv_inf_Vn_ne_bot F hT1 hc hII
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨hrZ, hrV⟩ := Subgroup.mem_inf.mp hr
  have hrU : r ∈ Vball 3 β := (Vn_le_Vball_one β).trans (Vball_mono (by norm_num) β) hrV
  have hcomm : y * r = r * y := comm_of_elem hU2 hyU hrU
  have hr' : r ∈ Zv (yy • α') := by
    rw [Zv_smul, mem_conjSub]
    have e : y⁻¹ * r * y = r := by
      calc y⁻¹ * r * y = y⁻¹ * (r * y) := by group
        _ = y⁻¹ * (y * r) := by rw [hcomm]
        _ = r := by group
    show y⁻¹ * r * y ∈ Zv α'
    rw [e]; exact hrZ
  rw [← hbot]
  exact Subgroup.mem_inf.mpr ⟨hrZ, hr'⟩

end CaseII

end CFSG.Quasithin.Kleidman.F204
