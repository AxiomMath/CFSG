module

public import CFSG.Quasithin.EmptyFaithful.T1521SSzAmb
public import CFSG.Quasithin.EmptyFaithful.T1521SJ
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nrm1521_of_sz_normal
    {S L : Subgroup G} (hL : SzComponent1521 L) (hP : IsSylowTwoOf (S ⊓ L) L)
    (hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1)
    (hnorm : ∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) : Nrm1521 S L := by
  have hJ : thompsonJ S ≤ innerPart1521 S L := by
    refine (thompsonJ_le_self151 S).trans fun x hx => ?_
    obtain ⟨l, hl, c, hc, rfl⟩ := hL.exists_mul hP hS hx (hnorm x hx)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hc)
  refine nrm1521_of_inner hJ ?_
  intro v hvS hvN hvB
  obtain ⟨s, hs, c, hc, rfl⟩ := hL.exists_mul hP hS hvS hvN
  refine hL.centralizes_of_forall_odd hP hs hc.2 ?_
  intro h hh hodd
  have hvh := hvB h (mem_oTwoUpper_of_odd hh hodd)
  have hch : h * c = c * h := Subgroup.mem_centralizer_iff.mp hc.2 h hh.1
  have hsh : s * h = h * s := by
    have h1 : (s * h) * c = (h * s) * c :=
      calc s * h * c = s * (h * c) := by rw [mul_assoc]
        _ = s * (c * h) := by rw [hch]
        _ = s * c * h := by rw [mul_assoc]
        _ = h * (s * c) := hvh
        _ = h * s * c := by rw [mul_assoc]
    exact mul_right_cancel h1
  have h2 : ⁅s, h⁆ = 1 := by rw [commutatorElement_def, hsh]; group
  rw [h2]
  exact Subgroup.one_mem _

end CFSG.Quasithin
