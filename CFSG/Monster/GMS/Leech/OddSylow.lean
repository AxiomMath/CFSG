module

public import CFSG.Monster.GMS.Leech.OddType

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

@[expose] def tripleHom (t y : G) : ↥(leechTriple z t y) →* Co1 :=
  L.φ.comp (Subgroup.inclusion (show leechTriple z t y ≤ Subgroup.centralizer ({z} : Set G) from
    inf_le_left.trans inf_le_left))

theorem tripleHom_apply (t y : G) (x : ↥(leechTriple z t y)) :
    L.tripleHom t y x = L.φ ⟨(x : G), (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 x.2).1).1⟩ := rfl

omit L in
theorem odd_orderOf_of_leechOddType {t y : G} {k : Fin 3} (hk : LeechOddType z t y k) :
    Odd (orderOf (t * y)) := by
  fin_cases k
  · rw [hk.1]; decide
  · rw [hk.1]; decide
  · rw [hk.1]; decide

theorem sylow_center_of_odd_type
    [Finite G] (hI : Co1InvolutionFacts) (hO : Co1OddPairFacts)
    {t y : G} (h : IsLeechCentralLift z t) (h' : IsLeechCentralLift z y)
    (hconj : IsConj (L.φ ⟨t, h.mem_centralizer⟩) (L.φ ⟨y, h'.mem_centralizer⟩))
    (hfour : HasCommonLeechFour z t y) {k : Fin 3} (hk0 : k ≠ 0) (hk : LeechOddType z t y k)
    (S : Sylow 2 ↥(leechTriple z t y)) (s : ↥(leechTriple z t y))
    (hcent : ∀ s' : ↥(leechTriple z t y), s' ∈ (S : Subgroup ↥(leechTriple z t y)) →
      s * s' = s' * s) :
    (s : G) = 1 ∨ (s : G) = z := by
  have hodd := odd_orderOf_of_leechOddType hk
  have hco := (L.leechOddType_iff hI h h' hodd k).1 hk
  have hfour' := (L.hasCommonLeechFour_iff hI h h').1 hfour
  obtain ⟨hnd, hfaith⟩ := (hO _ (L.isCo1TwoA_phi hI h)).2.2.2 k _ hk0 hconj hfour' hco
  have hK2 : IsPGroup 2 (L.tripleHom t y).ker := by
    intro x
    refine ⟨2, ?_⟩
    have hxQ : (x : G) ∈ leechQ z := by
      have := x.2
      rw [MonoidHom.mem_ker, L.tripleHom_apply] at this
      exact (L.φ_ker _).1 this
    apply Subtype.ext
    apply Subtype.ext
    simpa using L.pow_four_eq_one hxQ
  have hKS : (L.tripleHom t y).ker ≤ (S : Subgroup ↥(leechTriple z t y)) :=
    hK2.le_sylow_of_normal S
  have hq_ker : ∀ q ∈ leechQ z,
      L.vec q ∈ co1Fix (L.φ ⟨t, h.mem_centralizer⟩) ∩ co1Fix (L.φ ⟨y, h'.mem_centralizer⟩) →
      ∃ x : ↥(leechTriple z t y), x ∈ (L.tripleHom t y).ker ∧ (x : G) = q := by
    intro q hq hv
    have hqt : q ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (L.commute_of_vec_mem_co1Fix hI h hq hv.1).symm
    have hqy : q ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (L.commute_of_vec_mem_co1Fix hI h' hq hv.2).symm
    have hqT : q ∈ leechTriple z t y :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨L.mem_centralizer hq, hqt⟩, hqy⟩
    refine ⟨⟨q, hqT⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, L.tripleHom_apply]
    exact (L.φ_ker _).2 hq
  have hcomm_q : ∀ q ∈ leechQ z,
      L.vec q ∈ co1Fix (L.φ ⟨t, h.mem_centralizer⟩) ∩ co1Fix (L.φ ⟨y, h'.mem_centralizer⟩) →
      (s : G) * q = q * (s : G) := by
    intro q hq hv
    obtain ⟨x, hx, rfl⟩ := hq_ker q hq hv
    exact congrArg Subtype.val (hcent x (hKS hx))
  have hsC : (s : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 s.2).1).1
  have hst : (s : G) ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 s.2).1).2
  have hsy : (s : G) ∈ Subgroup.centralizer ({y} : Set G) := (Subgroup.mem_inf.1 s.2).2
  have hψs : L.φ ⟨(s : G), hsC⟩ = 1 := by
    refine hfaith _ (Subgroup.mem_inf.2 ⟨?_, ?_⟩) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hst)
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hsy)
    · intro v hv
      obtain ⟨q, hq, rfl⟩ := L.vec_surj v
      show co1Act (L.φ ⟨(s : G), hsC⟩) (L.vec q) = L.vec q
      rw [← L.vec_conj ⟨(s : G), hsC⟩ q hq]
      show L.vec ((s : G) * q * (s : G)⁻¹) = L.vec q
      rw [hcomm_q q hq hv]
      congr 1
      group
  have hsQ : (s : G) ∈ leechQ z := (L.φ_ker ⟨(s : G), hsC⟩).1 hψs
  have hvec : L.vec (s : G) = 0 := by
    refine hnd _ ⟨L.vec_mem_co1Fix_of_comm h.mem_centralizer hsQ
      (Subgroup.mem_centralizer_singleton_iff.1 hst).symm,
      L.vec_mem_co1Fix_of_comm h'.mem_centralizer hsQ
        (Subgroup.mem_centralizer_singleton_iff.1 hsy).symm⟩ ?_
    intro v hv
    obtain ⟨q, hq, rfl⟩ := L.vec_surj v
    exact (L.comm_eq_one_iff hsQ hq).1
      (commutatorElement_eq_one_iff_mul_comm.2 (hcomm_q q hq hv))
  exact (L.vec_eq_zero _ hsQ).1 hvec

end LeechSystem

end CFSG.Monster.GMS
