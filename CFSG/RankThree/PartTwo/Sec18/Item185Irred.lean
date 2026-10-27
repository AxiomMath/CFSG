module

import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec13.Item13Plane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem commute_of_mem_isMulCommutative {E : Subgroup G} (hE : IsMulCommutative E)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) : Commute x y :=
  congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem isElemAbelian_sup_of_commute {p : ℕ} {E B : Subgroup G}
    (hE : IsElemAbelian p E) (hB : IsElemAbelian p B)
    (hcomm : ∀ e ∈ E, ∀ b ∈ B, Commute e b) : IsElemAbelian p (E ⊔ B) := by
  have hEC : E ≤ Subgroup.centralizer (E : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => commute_of_mem_isMulCommutative hE.1 hy hx
  have hBC : B ≤ Subgroup.centralizer (E : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun e he => hcomm e he b hb
  have hEB : E ≤ Subgroup.centralizer (B : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm e he b hb).symm
  have hBB : B ≤ Subgroup.centralizer (B : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun b' hb' => commute_of_mem_isMulCommutative hB.1 hb' hb
  have hsupC : E ⊔ B ≤ Subgroup.centralizer (E : Set G) := sup_le hEC hBC
  have hsupB : E ⊔ B ≤ Subgroup.centralizer (B : Set G) := sup_le hEB hBB
  have hEN : E ≤ Subgroup.normalizer (B : Set G) :=
    hEB.trans (Subgroup.centralizer_le_normalizer _)
  have hdec : ∀ y ∈ E ⊔ B, ∃ e ∈ E, ∃ b ∈ B, e * b = y := by
    intro y hy
    have hy' : y ∈ (E : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E B hEN]
      exact hy
    obtain ⟨e, he, b, hb, rfl⟩ := Set.mem_mul.mp hy'
    exact ⟨e, he, b, hb, rfl⟩
  have hcommS : ∀ x ∈ E ⊔ B, ∀ y ∈ E ⊔ B, Commute x y := by
    intro x hx y hy
    obtain ⟨e, he, b, hb, rfl⟩ := hdec y hy
    refine Commute.mul_right ?_ ?_
    · exact (Subgroup.mem_centralizer_iff.mp (hsupC hx) e he).symm
    · exact (Subgroup.mem_centralizer_iff.mp (hsupB hx) b hb).symm
  refine ⟨⟨⟨fun u v => Subtype.ext (hcommS u.1 u.2 v.1 v.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨e, he, b, hb, rfl⟩ := hdec x hx
  rw [(hcomm e he b hb).mul_pow, hE.2 e he, hB.2 b hb, one_mul]

private theorem card_sup_of_commute {E B : Subgroup G} (hcomm : ∀ e ∈ E, ∀ b ∈ B, Commute e b)
    (hdisj : E ⊓ B = ⊥) : Nat.card (E ⊔ B : Subgroup G) = Nat.card E * Nat.card B := by
  have hc : ∀ (a : E) (b : B), Commute (E.subtype a) (B.subtype b) := fun a b =>
    hcomm (a : G) a.2 (b : G) b.2
  set f := MonoidHom.noncommCoprod E.subtype B.subtype hc with hf_def
  have hrange : f.range = E ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr ⟨E.subtype_injective, B.subtype_injective, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype]
      exact disjoint_iff.mpr hdisj⟩
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

private theorem commute_of_normalizes_inf_eq_bot {X B Y : Subgroup G}
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hV : Y ⊓ B = ⊥) {b e : G} (hb : b ∈ B) (hbX : b ∈ X) (heX : e ∈ X) (heY : e ∈ Y) :
    Commute e b := by
  have hwY : b * e * b⁻¹ * e⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXY hbX) e).mp heY) (Y.inv_mem heY)
  have hwB : b * e * b⁻¹ * e⁻¹ ∈ B := by
    have h1 : e * b⁻¹ * e⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hXB heX) b⁻¹).mp (B.inv_mem hb)
    have h2 : b * e * b⁻¹ * e⁻¹ = b * (e * b⁻¹ * e⁻¹) := by simp only [mul_assoc]
    rw [h2]
    exact B.mul_mem hb h1
  have hw1 : b * e * b⁻¹ * e⁻¹ = 1 := by
    have hmem : b * e * b⁻¹ * e⁻¹ ∈ Y ⊓ B := Subgroup.mem_inf.mpr ⟨hwY, hwB⟩
    rw [hV, Subgroup.mem_bot] at hmem
    exact hmem
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hw1)).symm

theorem exists_elemAbelian_le_inf {P Y E : Subgroup G} (hP : IsSylowOf 3 P ⊤)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hE : E ≤ Y) (hEa : IsElemAbelian 3 E) :
    ∃ E' ≤ P ⊓ Y, IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E := by
  have hPY' : IsSylowOf 3 (P ⊓ Y) Y :=
    (hP.of_le le_sup_left le_top).inf_of_le_normalizer le_sup_right
      (sup_le hPY Subgroup.le_normalizer)
  have hE3' : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEa.2 x x.2)⟩
  obtain ⟨Q, hQ⟩ := (hE3'.comap_subtype (K := Y)).exists_le_sylow
  have hQ' : IsSylowOf 3 ((Q : Subgroup Y).map Y.subtype) Y := ⟨Q, rfl⟩
  obtain ⟨k, -, hk⟩ := hPY'.exists_mem_conj hQ'
  have hEQ : E ≤ (Q : Subgroup Y).map Y.subtype := by
    intro x hx
    have hxY : x ∈ Y := hE hx
    have hmem : (⟨x, hxY⟩ : Y) ∈ E.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxY⟩, hQ hmem, rfl⟩
  refine ⟨E.map (MulAut.conj k⁻¹ : MulAut G).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h := (hk x).mp (hEQ hx)
    simpa [MulAut.conj_apply] using h
  · exact CFSG.SectionRank.isElemAbelian_map hEa _
  · exact Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective

theorem le_of_pRank_gt_one {X B Y P : Subgroup G} (hP : IsSylowOf 3 P ⊤) (hPX : P ≤ X)
    (hBP : B ≤ P) (hBe : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn X B))
    (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hY : ∃ E ≤ Y, IsElemAbelian 3 E ∧ 9 ≤ Nat.card E)
    (h27 : ∀ E ≤ P, IsElemAbelian 3 E → Nat.card E ≤ 27) : B ≤ Y := by
  have hKV : X ≤ Subgroup.normalizer ((Y ⊓ B : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hYx := Subgroup.mem_normalizer_iff.mp (hXY hx) h
    have hBx := Subgroup.mem_normalizer_iff.mp (hXB hx) h
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr hYx hBx
  rcases Sec13.eq_bot_or_eq_of_isIrreducibleOn (V := Y ⊓ B) hirr inf_le_right hKV with hV | hV
  · exfalso
    obtain ⟨E₀, hE₀Y, hE₀, hE₀card⟩ := hY
    have hPY : P ≤ Subgroup.normalizer (Y : Set G) := hPX.trans hXY
    obtain ⟨E, hEPY, hE, hEcard⟩ := exists_elemAbelian_le_inf hP hPY hE₀Y hE₀
    have hEY : E ≤ Y := hEPY.trans inf_le_right
    have hEX : E ≤ X := (hEPY.trans inf_le_left).trans hPX
    have hBX : B ≤ X := hBP.trans hPX
    have hcomm : ∀ e ∈ E, ∀ b ∈ B, Commute e b := fun e he b hb =>
      commute_of_normalizes_inf_eq_bot hXB hXY hV hb (hBX hb) (hEX he) (hEY he)
    have hdisj : E ⊓ B = ⊥ := eq_bot_iff.mpr ((inf_le_inf hEY le_rfl).trans hV.le)
    have hle : E ⊔ B ≤ P := sup_le (hEPY.trans inf_le_left) hBP
    have hbound := h27 (E ⊔ B) hle (isElemAbelian_sup_of_commute hE hBe hcomm)
    rw [card_sup_of_commute hcomm hdisj, hB9, hEcard] at hbound
    omega
  · exact (le_of_eq hV.symm).trans inf_le_left

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
