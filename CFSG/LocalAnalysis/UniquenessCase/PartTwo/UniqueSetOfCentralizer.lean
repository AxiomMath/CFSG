module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem mem_uniqueSet_of_centralizer {M B : Subgroup G} {p r : ℕ}
    (hp : p.Prime) (hsp : IsStronglyPEmbedded p M) (hr : r.Prime)
    (hBM : B ≤ M) (hBcard : Nat.card B = r)
    (hcent : Subgroup.centralizer (B : Set G) ≤ M)
    (hrank : 2 ≤ CFSG.Open.pRank r M)
    (hE : ∀ E : Subgroup G, E ≤ M → CFSG.Open.IsElemAbelian r E → Nat.card E = r ^ 2 →
      p ∣ Nat.card (M ⊓ Subgroup.centralizer (E : Set G) : Subgroup G)) :
    B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  refine ⟨hBM, ?_⟩
  intro g hBg
  set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hB'M : B' ≤ M := by
    have h1 : B' ≤ (M.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono hBg
    rw [Subgroup.map_map] at h1
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rwa [hcomp, Subgroup.map_id] at h1
  have hB'card : Nat.card B' = r := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hBcard]
  have hB'group : IsPGroup r B' :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hB'card)
  obtain ⟨P, hP, hB'P⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge hB'M hB'group
  have hrankP : 2 ≤ CFSG.Open.pRank r P := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hr hP]
    exact hrank
  obtain ⟨E, hB'E, hEP, hEel, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      hP.isPGroup hrankP hB'P hB'card
  have hEM : E ≤ M := hEP.trans hP.le
  have hEp : p ∣ Nat.card (M ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) :=
    hE E hEM hEel hEcard
  obtain ⟨x, hxord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ Subgroup.centralizer (E : Set G))) p hEp
  have hxM : (x : G) ∈ M := x.2.1
  have hxC : (x : G) ∈ Subgroup.centralizer (E : Set G) := x.2.2
  have hxCb : (x : G) ∈ Subgroup.centralizer (B' : Set G) :=
    (Subgroup.centralizer_le hB'E) hxC
  have hxordG : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hxord
  set y : G := MulAut.conj g (x : G) with hy
  have hyord : orderOf y = p := by
    rw [hy]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) (x : G)).trans hxordG
  have hyC : y ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : g⁻¹ * b * g ∈ B' := by
      rw [show B' = B.map (MulAut.conj g⁻¹).toMonoidHom from rfl]
      exact Subgroup.mem_map.mpr ⟨b, hb, by simp [MulAut.conj_apply]⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hxCb (g⁻¹ * b * g) hb'
    show b * y = y * b
    calc b * y = g * ((g⁻¹ * b * g) * (x : G)) * g⁻¹ := by
          simp only [hy, MulAut.conj_apply]
          group
      _ = g * ((x : G) * (g⁻¹ * b * g)) * g⁻¹ := by rw [hcomm]
      _ = y * b := by
          simp only [hy, MulAut.conj_apply]
          group
  have hyMg : y ∈ M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨(x : G), hxM, rfl⟩
  have hyinf : y ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    ⟨hcent hyC, hyMg⟩
  have hpdvd : p ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom) := by
    have h := Subgroup.orderOf_dvd_natCard (M ⊓ M.map (MulAut.conj g).toMonoidHom) hyinf
    rwa [hyord] at h
  have hgM : g ∈ M := by
    by_contra hg
    exact hsp.2.2 g hg hpdvd
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
