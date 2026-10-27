module

import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

private theorem sbidx2_exists_pow_mem_oResidual {Y : Type} [Group Y] [Finite Y] (x : Y) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oResidual 2 Y := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, Subgroup.subset_closure ?_⟩
  show Nat.Coprime (orderOf (x ^ 2 ^ k)) 2
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm.coprime_two_right

private theorem sbidx2_card_le {G : Type} [Group G] [Finite G] {m : ℕ} (hm5 : 5 ≤ m)
    (hm6 : m ≠ 6) (N : Subgroup G) [N.Normal] (e : N ≃* alternatingGroup (Fin m))
    (hO2 : CFSG.pCore 2 G = ⊥) (hpow : ∀ g : G, ∃ k : ℕ, g ^ 2 ^ k ∈ N) :
    Nat.card G ≤ 2 * Nat.card N := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcen : ∀ z : N, (∀ n : N, n * z = z * n) → z = 1 := by
    intro z hz
    have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨n, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz n]
    rw [alternatingGroup.center_eq_bot
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega), Subgroup.mem_bot] at h1
    exact e.injective (by rw [h1, map_one])
  have hC2 : IsPGroup 2 (Subgroup.centralizer (N : Set G)) := by
    intro c
    obtain ⟨k, hk⟩ := hpow (c : G)
    refine ⟨k, ?_⟩
    have hkC : (c : G) ^ 2 ^ k ∈ Subgroup.centralizer (N : Set G) := Subgroup.pow_mem _ c.2 _
    have h1 : (⟨(c : G) ^ 2 ^ k, hk⟩ : N) = 1 :=
      hcen ⟨(c : G) ^ 2 ^ k, hk⟩ fun n =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hkC n n.2)
    have h2 : (c : G) ^ 2 ^ k = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hCbot : Subgroup.centralizer (N : Set G) = ⊥ := by
    have hle : Subgroup.centralizer (N : Set G) ≤ CFSG.pCore 2 G := le_sSup ⟨inferInstance, hC2⟩
    rwa [hO2, le_bot_iff] at hle
  have hconj : Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := congrArg (fun φ : MulAut N => ((φ ⟨h, hh⟩ : N) : G)) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hCbot] at hgC
    exact hgC
  have hinj : Function.Injective (((MulAut.congr e).toMonoidHom).comp
      (MulAut.conjNormal : G →* MulAut N)) := (MulAut.congr e).injective.comp hconj
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6
  haveI : Finite (MulAut (alternatingGroup (Fin m))) := Finite.of_surjective _ hbij.2
  calc Nat.card G ≤ Nat.card (MulAut (alternatingGroup (Fin m))) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (Equiv.Perm (Fin m)) := (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = 2 * Nat.card (alternatingGroup (Fin m)) := (two_mul_nat_card_alternatingGroup).symm
    _ = 2 * Nat.card N := by rw [Nat.card_congr e.toEquiv]

private theorem sbidx2_index_le_two {G : Type} [Group G] [Finite G] {m : ℕ} (hm5 : 5 ≤ m)
    (hm6 : m ≠ 6) (N : Subgroup G) [N.Normal] (e : N ≃* alternatingGroup (Fin m))
    (hO2 : CFSG.pCore 2 G = ⊥) (hpow : ∀ g : G, ∃ k : ℕ, g ^ 2 ^ k ∈ N) : N.index ≤ 2 := by
  have hcard := sbidx2_card_le hm5 hm6 N e hO2 hpow
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hmul : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
  exact Nat.le_of_mul_le_mul_left (by rw [hmul, mul_comm]; exact hcard) hpos

theorem sup_normal_of_equiv_alt {m : ℕ} (hm : m = 5 ∨ m = 7)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* alternatingGroup (Fin m)) (S : Subgroup X) :
    (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).Normal := by
  haveI : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).Normal :=
    Stage1.Thm6.Prod.oResidual_normal 2 _
  have hidx : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).index ≤ 2 :=
    sbidx2_index_le_two (by omega) (by omega) _ e
      (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := X) (p := 2))
      fun g => sbidx2_exists_pow_mem_oResidual g
  have hmap : (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    Stage1.Thm6.Prod.map_oResidual _ (QuotientGroup.mk'_surjective _) Nat.prime_two
  have hLQ : oResidual 2 X ⊔ CFSG.pCore 2 X =
      (oResidual 2 (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hidx' : (oResidual 2 X ⊔ CFSG.pCore 2 X).index ≤ 2 := by
    rw [hLQ, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hidx
  have hle : oResidual 2 X ⊔ CFSG.pCore 2 X ≤ S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X :=
    sup_le_sup_right le_sup_right _
  have hne : (oResidual 2 X ⊔ CFSG.pCore 2 X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne' : (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Subgroup.index_dvd_of_le hle)
  rcases (show (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).index = 1 ∨
      (S ⊔ oResidual 2 X ⊔ CFSG.pCore 2 X).index = 2 by omega) with h | h
  · exact Subgroup.normal_of_index_eq_one h
  · exact Subgroup.normal_of_index_eq_two h

open Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)

private theorem sbidx2_projSL_eq_range (F : Type) [Field F] :
    projSL 2 F =
      (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

private noncomputable def sbidx2_projSLEquiv (F : Type) [Field F] [CharP F 2] :
    SL(2, F) ≃* projSL 2 F :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).codRestrict
      (projSL 2 F) (fun A => by rw [sbidx2_projSL_eq_range]; exact ⟨A, rfl⟩))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro A hA
      have h : A ∈ (Matrix.SpecialLinearGroup.toPGL :
          SL(2, F) →* ProjGenLinGroup (Fin 2) F).ker := by
        rw [MonoidHom.mem_ker] at hA ⊢
        exact congrArg Subtype.val hA
      rw [Matrix.SpecialLinearGroup.toPGL_ker,
        CFSG.CGT.PushingUpLit.CGT6.sl2_center_eq_bot] at h
      exact h,
     by
      rintro ⟨x, hx⟩
      rw [sbidx2_projSL_eq_range] at hx
      obtain ⟨A, rfl⟩ := hx
      exact ⟨A, rfl⟩⟩

theorem nonempty_projSL_four_equiv_alt5 :
    Nonempty (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 2) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨κ⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
  exact ⟨(sbidx2_projSLEquiv (GaloisField 2 2)).symm.trans κ⟩

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
