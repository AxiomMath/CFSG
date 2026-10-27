module

public import CFSG.Quasithin.Vol2.GoldschmidtF431NFTI
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ClsRoot
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOne

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.NFLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.F431.NF
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem commutator_mem_Xc {x y : C K} (hx : x ∈ Q1 K) (hy : y ∈ Q1 K) : ⁅x, y⁆ ∈ Xc K := by
  obtain ⟨α, μ, ν, β, γ, rfl⟩ := mem_Q1_iff.mp hx
  obtain ⟨a, u, v, b, e, rfl⟩ := mem_Q1_iff.mp hy
  rw [nf_comm_Q1]
  exact xc_mem_Xc _

theorem mul_self_mem_Xc {x : C K} (hx : x ∈ Q1 K) : x * x ∈ Xc K := by
  obtain ⟨α, μ, ν, β, γ, rfl⟩ := mem_Q1_iff.mp hx
  rw [nf_sq_Q1]
  exact xc_mem_Xc _

theorem Xc_le_commutator : Xc K ≤ ⁅Xa K, Xb K⁆ := by
  rintro _ ⟨s, rfl⟩
  have h := Subgroup.commutator_mem_commutator (xa_mem_Xa (1 : K)) (xb_mem_Xb s)
  rwa [cm_ab, one_mul] at h

theorem xc_one_ne_one : xc (1 : K) ≠ 1 := fun h => one_ne_zero (xc_eq_one_iff.mp h)

theorem xu_one_not_mem_Xc : xu (1 : K) ∉ Xc K := by
  intro h
  obtain ⟨s, hs⟩ := mem_Xc_iff.mp h
  rw [xu_eq_nf, xc_eq_nf] at hs
  exact one_ne_zero (nf_injective hs.symm).2.2.1

theorem xa_comm_xu (s t : K) : xa s * xu t = xu t * xa s := (cc_au s t).eq

theorem xb_comm_xu (s t : K) : xb s * xu t = xu t * xb s := ((cc_ub t s).eq).symm

variable (K) in
@[expose] def nrC : C K :=
  ⟨weylElt Tag.G2 K Cls.iR 1, weylElt_mem_adjointGroup Cls.iR 1⟩

variable (K) in
@[expose] def naC : C K :=
  ⟨weylElt Tag.G2 K Cls.iA 1, weylElt_mem_adjointGroup Cls.iA 1⟩

theorem reflect_r_b : reflect Tag.G2 Cls.iR ![1, 3] = ![1, 0] :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_a_c : reflect Tag.G2 Cls.iA ![2, 3] = ![1, 3] :=
  List.ofFn_injective (by decide +kernel)

theorem nrC_conj_xb (s : K) : nrC K * xb s * (nrC K)⁻¹ = xa s := by
  refine Subtype.ext ?_
  have h := Cls.weylElt_conj_pinnedX (K := K) Cls.iR Cls.isRoot_b s
  rw [reflect_r_b] at h
  exact h

theorem naC_conj_xc (s : K) : naC K * xc s * (naC K)⁻¹ = xb s := by
  refine Subtype.ext ?_
  have h := Cls.weylElt_conj_pinnedX (K := K) Cls.iA Cls.isRoot_c s
  rw [reflect_a_c] at h
  exact h

theorem Xa_eq_cj : Xa K = cj (nrC K) (Xb K) := by
  ext x
  rw [mem_cj, mem_Xa_iff, mem_Xb_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by rw [← nrC_conj_xb s]; group⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, by rw [← nrC_conj_xb s, hs]; group⟩

theorem Xb_eq_cj : Xb K = cj (naC K) (Xc K) := by
  ext x
  rw [mem_cj, mem_Xb_iff, mem_Xc_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by rw [← naC_conj_xc s]; group⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, by rw [← naC_conj_xc s, hs]; group⟩

end CFSG.Quasithin.H13.F431.G2.NFLie
