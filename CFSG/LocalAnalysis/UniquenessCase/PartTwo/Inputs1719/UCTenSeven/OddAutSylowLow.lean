module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup

private theorem eq_one_of_odd_order_of_isPGroup_two {G : Type*} [Group G] (hG : IsPGroup 2 G)
    {x : G} (hx : Odd (orderOf x)) : x = 1 := by
  have hcop : (orderOf x).Coprime (orderOf x) := hG.orderOf_coprime hx.coprime_two_left x
  exact orderOf_eq_one_iff.mp ((Nat.coprime_self (orderOf x)).mp hcop)

private theorem isPGroup_mulAut_of_semidihedral_or_wreathed {S : Type*} [Group S]
    (hshape : (∃ m : ℕ, 4 ≤ m ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup m)) ∨
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (S ≃* CFSG.Open.WreathedTwoGroup m))) :
    IsPGroup 2 (MulAut S) := by
  rcases hshape with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact (CFSG.Semidihedral.FieldFactorOne.semidihedral_automorphism_isPGroup (n := m) hm).of_equiv
      (MulAut.congr e).symm
  · exact (CFSG.Wreathed.wreathedTwoGroup_automorphism_isPGroup m hm).of_equiv
      (MulAut.congr e).symm

private theorem autSylowAt_of_sylow_sdw3 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : Odd p)
    (hshape : ∀ Q : Sylow 2 G,
      (∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥Q ≃* CFSG.Open.SemidihedralGroup m)) ∨
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥Q ≃* CFSG.Open.WreathedTwoGroup m))) :
    AutSylowAt G p := by
  apply autSylowAt_of_sylow_mulAut
  intro S hS σ hσ
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let Q : Sylow 2 G :=
    hSiff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hQcoe : (Q : Subgroup G) = S := IsPGroup.toSylow_coe _ _
  have hshapeS :
      (∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup m)) ∨
        (∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.WreathedTwoGroup m)) := by
    rcases hshape Q with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
    · exact Or.inl ⟨m, hm, ⟨(MulEquiv.subgroupCongr hQcoe.symm).trans e⟩⟩
    · exact Or.inr ⟨m, hm, ⟨(MulEquiv.subgroupCongr hQcoe.symm).trans e⟩⟩
  exact eq_one_of_odd_order_of_isPGroup_two (isPGroup_mulAut_of_semidihedral_or_wreathed hshapeS)
    (hp.of_dvd_nat (orderOf_dvd_of_pow_eq_one hσ))

private theorem autSylowAt_of_isLnEps_projectiveSL_three {G : Type} [Group G] [Finite G]
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : CFSG.GH74.GLS.IVK.IsLnEps 3 G 1 (r ^ f)) {p : ℕ} (hp : Odd p) :
    AutSylowAt G p := by
  apply autSylowAt_of_sylow_sdw3 hp
  intro Q
  have hq1 : 1 < r ^ f := Nat.one_lt_pow (by omega) hr.one_lt
  have hqmod : r ^ f % 4 = 1 ∨ r ^ f % 4 = 3 :=
    Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ((hr.odd_of_ne_two hr2).pow))
  rcases hqmod with hq | hq
  · exact Or.inr (CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_wr
      (p := r) (n := f) hr hr2 h hq hq1 Q)
  · exact Or.inl (CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_sd
      (p := r) (n := f) hr hr2 h hq Q)

private theorem autSylowAt_of_isLnEps_projectiveSU_three {G : Type} [Group G] [Finite G]
    {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : CFSG.GH74.GLS.IVK.IsLnEps 3 G (-1) (r ^ f)) {p : ℕ} (hp : Odd p) :
    AutSylowAt G p := by
  apply autSylowAt_of_sylow_sdw3 hp
  intro Q
  have hq1 : 1 < r ^ f := Nat.one_lt_pow (by omega) hr.one_lt
  have hqmod : r ^ f % 4 = 1 ∨ r ^ f % 4 = 3 :=
    Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ((hr.odd_of_ne_two hr2).pow))
  rcases hqmod with hq | hq
  · exact Or.inl (CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_sd
      (p := r) (n := f) hr hr2 h hq hq1 Q)
  · exact Or.inr (CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_wr
      (p := r) (n := f) hr hr2 h hq Q)

theorem autSylowAt_projectiveSL_three {K : Type} [Field K] [Finite K] {r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) {p : ℕ} (hp : Odd p) :
    AutSylowAt (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) p := by
  let e : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)
  have hLn : CFSG.GH74.GLS.IVK.IsLnEps 3
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) 1 (r ^ f) :=
    Or.inl ⟨rfl, K, (inferInstance : Field K), (inferInstance : Finite K), hK, ⟨e⟩⟩
  exact autSylowAt_of_isLnEps_projectiveSL_three hr hr2 hf hLn hp

theorem autSylowAt_of_statedPSU_three {X : Type} [Group X] [Finite X] {r f : ℕ} (hr2 : r ≠ 2)
    (h : CFSG.Open.StatedClassicalModel X .PSU 3 r f) {p : ℕ} (hp : Odd p) :
    AutSylowAt X p := by
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := h
  have hr : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hLn : CFSG.GH74.GLS.IVK.IsLnEps 3 X (-1) (r ^ f) :=
    Or.inr ⟨rfl, K, hKfield, hKfin, hKcard, ⟨e⟩⟩
  exact autSylowAt_of_isLnEps_projectiveSU_three hr hr2 hf hLn hp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
