module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsOddAm
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522X
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem D_le_normalizer_H (hI : L2OddInnerFact) : D ≤ Subgroup.normalizer (H : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    s.hyp.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI s.odd)
  rw [s.hyp.H_eq_sup]
  exact le_normalizer_sup_of_le s.D_le_normalizer hDT

theorem two_rank_le
    (hI : L2OddInnerFact) (hAut : L34AutTwoRankFact) {E : Subgroup G} (hEH : E ≤ H ⊔ D)
    (hE : IsElemAbelian 2 E) : (pCoreOf 2 (H ⊔ D)).relIndex E ≤ 2 ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hHN : H ⊔ D ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (s.D_le_normalizer_H hI)
  have hH₁Mp : H ⊔ D ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le (le_normalizer_oTwoUpper H) s.D_le_normalizer
  have hEMp := hEH.trans hH₁Mp
  have hTsyl : IsSylowTwoOf T (H ⊔ D) := hh.isSylowTwoOf (hTH.trans le_sup_left)
  have hOQ : pCoreOf 2 H ≤ pCoreOf 2 (H ⊔ D) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 H).trans le_sup_left)
      (hHN.trans (normalizer_le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hEC : ∀ x ∈ E, x ∈ centralizerModO2 (oTwoUpper H) → x ∈ pCoreOf 2 (H ⊔ D) := by
    intro x hxE hxC
    have hxH : x ∈ H := by
      have hz2 : IsPGroup 2 (Subgroup.zpowers x) :=
        (isPGroup_of_isElemAbelian hE).to_le (Subgroup.zpowers_le.mpr hxE)
      obtain ⟨y, hy, hyT⟩ := exists_conj_le_of_isSylowTwoOf hTsyl
        ((Subgroup.zpowers_le.mpr hxE).trans hEH) hz2
      have h1 : y * x * y⁻¹ ∈ H := hTH (hyT (mul_mem_conjSub (Subgroup.mem_zpowers x)))
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHN (inv_mem hy)) _).mp h1
      simpa [mul_assoc] using h2
    exact hOQ (s.hyp.inf_centralizerModO2_le ⟨hxH, hxC⟩)
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  set φ := quotConjAut (oTwoUpper H) with hφ
  set E' := E.subgroupOf Mp with hE'
  have hE'ab : IsElemAbelian 2 E' :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (F7.isElemAbelian_comm hE a.2 b.2))⟩⟩,
      fun x hx => Subtype.ext (by simpa using hE.2 (x : G) hx)⟩
  have himg : Nat.card ↥(E'.map φ) ≤ 2 ^ 4 :=
    hAut _ s.hyp.l34 _ (CFSG.SectionRank.isElemAbelian_map hE'ab φ)
  rw [← Subgroup.relIndex_ker] at himg
  have h1 : (pCoreOf 2 (H ⊔ D)).relIndex E = ((pCoreOf 2 (H ⊔ D)).subgroupOf Mp).relIndex E' :=
    (Subgroup.relIndex_subgroupOf hEMp).symm
  have h2 : φ.ker ⊓ E' ≤ (pCoreOf 2 (H ⊔ D)).subgroupOf Mp ⊓ E' := by
    rintro x ⟨hxk, hxE⟩
    refine ⟨?_, hxE⟩
    show (x : G) ∈ pCoreOf 2 (H ⊔ D)
    exact hEC x hxE (mem_centralizerModO2_of_quotConjAut_eq_one hxk)
  have h3 := Subgroup.relIndex_le_of_le_left (L := E') h2 (Subgroup.index_ne_zero_of_finite)
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at h3
  rw [h1]
  exact h3.trans himg

end Setup5_1_17Odd

end CFSG.Quasithin.H13
