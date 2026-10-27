module

public import CFSG.Quasithin.Vol2.Ch11SecB25
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom
open CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_frattini {C M Q : Subgroup G} (hCM : C ≤ M)
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) (hQ : QuasithinUnique.IsSylowTwoOf Q C)
    {m : G} (hm : m ∈ M) :
    ∃ c ∈ C, ∃ x ∈ M ⊓ Subgroup.normalizer (Q : Set G), m = c * x := by
  have hmQ : cjSub m Q ≤ C := by
    intro y hy
    rw [mem_cjSub] at hy
    have := (Subgroup.mem_normalizer_iff.mp (hMC hm) (m⁻¹ * y * m)).mp (hQ.1 hy)
    simpa [mul_assoc] using this
  have hQ2 : IsPGroup 2 ↥(cjSub m Q) := hQ.2.1.map (MulAut.conj m).toMonoidHom
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hQ hmQ hQ2
  have hcomp : cjSub h (cjSub m Q) = Q.map (MulAut.conj (h * m)).toMonoidHom := by
    ext y
    rw [mem_cjSub, mem_cjSub, mem_map_conj]
    simp only [mul_inv_rev, mul_assoc, iff_self]
  refine ⟨h⁻¹, C.inv_mem hh, h * m, ⟨M.mul_mem (hCM hh) hm, ?_⟩, by group⟩
  exact mem_normalizer_of_map_le (hcomp ▸ hle)

theorem mem_normalizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_le ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem exists_conj_commutator_of_amalgam {G₀ G₁ G₂ T V : Subgroup G}
    (hamal : AmalgamHypV G₀ G₁ G₂ T V) (hV1 : V ≠ ⊥) (hW : E3.wClos V 0 T ≤ pCoreOf 2 G₂) :
    ∃ g : G, conjSubgroup V g ≤ T ∧ ⁅V, conjSubgroup V g⁆ ≠ ⊥ ∧
      V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hb := even_critDist_of_weakClosureW0_le_G₂ hamal hV1
    ((weakClosureW0_le_wClos T V).trans hW)
  obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hamal hV1
  have hc := commutator_V_Vv_of_even hamal hV1 hb hγ hVγ
  obtain ⟨x, rfl⟩ := exists_smul_eq_γ₀ (vtype_eq_false_of_even hamal.gen (by rw [hγ]; exact hb))
  rw [Vv_smul_γ₀ hamal.normalizes] at hc
  obtain ⟨hne, hcl, hLT, -⟩ := hc
  have hVx2 : IsPGroup 2 (conjSub (x : G) V) := hamal.isPGroup.map (MulAut.conj (x : G)).toMonoidHom
  obtain ⟨h, hh, hle⟩ := E3.exists_le_conj_of_isSylowIn hamal.sylow₁ hLT hVx2
  have hLTV : G₁ ≤ Subgroup.normalizer (V : Set G) := hamal.normalizes
  have e1 : conjSub (x : G) V = conjSubgroup V (x : G)⁻¹ := by
    ext y
    rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
  have e2 : conjSubgroup V h⁻¹ = V := conjSubgroup_eq_iff_mem_normalizer.2 (hLTV (inv_mem hh))
  refine ⟨(x : G)⁻¹ * h⁻¹, ?_, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup, ← e1]
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have := hle hy
    rw [mem_conjSubgroup_iff] at this
    simpa [mul_assoc] using this
  · rw [← conjSubgroup_conjSubgroup, ← e1]
    intro hbot
    apply hne
    have h1 := E3.conjSubgroup_commutator V (conjSub (x : G) V) h⁻¹
    rw [e2, hbot] at h1
    have h2 := congrArg (fun K => conjSubgroup K h) h1
    simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
    rw [h2]
    ext y
    simp [mem_conjSubgroup_iff]
  · rw [← conjSubgroup_conjSubgroup, ← e1]
    have hN : V ≤ Subgroup.normalizer (conjSub (x : G) V : Set G) :=
      le_normalizer_of_commutator_le (hcl.trans inf_le_right)
    intro v hv
    have hv' : h⁻¹ * v * h⁻¹⁻¹ ∈ V :=
      ((Subgroup.mem_normalizer_iff.1 (hLTV (inv_mem hh))) v).1 hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have := (Subgroup.mem_normalizer_iff.1 (hN hv')) (h⁻¹ * y * h⁻¹⁻¹)
    rw [show h⁻¹ * (v * y * v⁻¹) * h⁻¹⁻¹ =
      (h⁻¹ * v * h⁻¹⁻¹) * (h⁻¹ * y * h⁻¹⁻¹) * (h⁻¹ * v * h⁻¹⁻¹)⁻¹ by group]
    exact this

end General

end CFSG.Quasithin.Vol2.Ch11.SecB
