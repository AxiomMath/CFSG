module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SubgroupClasses
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Basic
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport
import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ABGLocalTools (IsSylowOf)

private instance k891classesFactPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem k891classes_isPGroup_R {G : Type} [Group G] {R : Subgroup G}
    (hR : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥R) :
    IsPGroup 3 R := by
  have hcard : Nat.card ↥R = 3 ^ (1 + 2 * 1) := hR.1
  refine IsPGroup.of_card (n := 3) ?_
  rw [hcard]

private theorem k891classes_sup_pCore_eq_of_bar_eq {G : Type} [Group G] [Finite G]
    {L B C : Subgroup G} (hBL : B ≤ L) (hCL : C ≤ L)
    (hmap : (B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
    B ⊔ (CFSG.pCore 2 ↥L).map L.subtype = C ⊔ (CFSG.pCore 2 ↥L).map L.subtype := by
  have h1 := (Subgroup.map_eq_map_iff (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))).mp hmap
  rw [QuotientGroup.ker_mk'] at h1
  have h2 := congrArg (Subgroup.map L.subtype) h1
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBL,
    Subgroup.map_subgroupOf_eq_of_le hCL] at h2
  exact h2

private theorem k891classes_isSylowOf_sup {G : Type} [Group G] [Finite G]
    (L B : Subgroup G) (hBL : B ≤ L) (hB : IsPGroup 3 B) :
    IsSylowOf 3 B (B ⊔ (CFSG.pCore 2 ↥L).map L.subtype) := by
  have hN : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hk]
    exact Nat.prime_two.coprime_pow_of_not_dvd (by norm_num : ¬ 2 ∣ 3)
  have hB' : IsPGroup 3 (B.subgroupOf L) := hB.comap_subtype
  have hsup := CFSG.ABGLocalTools.isSylowOf_sup_of_coprime (p := 3) hN hB'
  have hmap := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) L).mpr hsup
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBL] at hmap
  rwa [sup_comm] at hmap

private theorem k891classes_exists_conj_pCore {G : Type} [Group G] [Finite G]
    (L B C : Subgroup G) (hBL : B ≤ L) (hCL : C ≤ L)
    (hB : IsPGroup 3 B) (hC : IsPGroup 3 C)
    (hmap : (B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
    ∃ n ∈ (CFSG.pCore 2 ↥L).map L.subtype, C.map (MulAut.conj n).toMonoidHom = B := by
  have hNGL : (CFSG.pCore 2 ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hsup : B ⊔ (CFSG.pCore 2 ↥L).map L.subtype = C ⊔ (CFSG.pCore 2 ↥L).map L.subtype :=
    k891classes_sup_pCore_eq_of_bar_eq hBL hCL hmap
  have hBsyl : IsSylowOf 3 B (B ⊔ (CFSG.pCore 2 ↥L).map L.subtype) :=
    k891classes_isSylowOf_sup L B hBL hB
  have hCsyl : IsSylowOf 3 C (B ⊔ (CFSG.pCore 2 ↥L).map L.subtype) := by
    rw [hsup]; exact k891classes_isSylowOf_sup L C hCL hC
  obtain ⟨k, hkH, hk⟩ := hBsyl.exists_mem_conj hCsyl
  have hHleL : B ⊔ (CFSG.pCore 2 ↥L).map L.subtype ≤ L := sup_le hBL hNGL
  have hkL : k ∈ L := hHleL hkH
  have hsub : (B ⊔ (CFSG.pCore 2 ↥L).map L.subtype).subgroupOf L =
      (B.subgroupOf L) ⊔ (CFSG.pCore 2 ↥L) := by
    rw [Subgroup.subgroupOf_sup hBL hNGL]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hkmap : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (⟨k, hkL⟩ : ↥L) ∈
      (B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    have h1 : (⟨k, hkL⟩ : ↥L) ∈ ((B.subgroupOf L) ⊔ (CFSG.pCore 2 ↥L)) := by
      rw [← hsub]; exact hkH
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (⟨k, hkL⟩ : ↥L) ∈
        (((B.subgroupOf L) ⊔ (CFSG.pCore 2 ↥L)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
      Subgroup.mem_map_of_mem _ h1
    have hle : (((B.subgroupOf L) ⊔ (CFSG.pCore 2 ↥L)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ≤
        (B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk']
    exact hle h2
  obtain ⟨bL, hbL, hbLk⟩ := Subgroup.mem_map.mp hkmap
  have hb : (bL : G) ∈ B := hbL
  have hbker : (⟨k, hkL⟩ * bL⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.ker_mk' (N := CFSG.pCore 2 ↥L)]
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, hbLk, mul_inv_cancel]
  have hmem : (bL : G) * k⁻¹ ∈ (CFSG.pCore 2 ↥L).map L.subtype := by
    have h := Subgroup.mem_map_of_mem L.subtype (inv_mem hbker)
    simpa using h
  refine ⟨(bL : G) * k⁻¹, hmem, ?_⟩
  have hkmap' : C.map (MulAut.conj k⁻¹).toMonoidHom = B := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using (hk c).mp hc
    · intro hx
      refine ⟨MulAut.conj k x, (hk _).mpr ?_, ?_⟩
      · convert hx using 1
        simp only [MulAut.conj_apply]
        group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hconj : MulAut.conj ((bL : G) * k⁻¹) =
      MulAut.conj (bL : G) * MulAut.conj k⁻¹ := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    group
  calc C.map (MulAut.conj ((bL : G) * k⁻¹)).toMonoidHom
      = C.map (MulAut.conj (bL : G) * MulAut.conj k⁻¹).toMonoidHom := by rw [hconj]
    _ = (C.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj (bL : G)).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl
    _ = B := by
          rw [hkmap']
          exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp (B.le_normalizer hb)

private theorem k891classes_barImage_map_conj {G : Type} [Group G] [Finite G]
    (L K : Subgroup G) (hK : K ≤ L) {g : G} (hg : g ∈ L) :
    barImage L (K.map (MulAut.conj g).toMonoidHom) =
      (barImage L K).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g, hg⟩)).toMonoidHom := by
  have hKsub : (K.map (MulAut.conj g).toMonoidHom).subgroupOf L =
      (K.subgroupOf L).map (MulAut.conj (⟨g, hg⟩ : ↥L)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp (show (y : G) ∈ _ from hy)
      refine Subgroup.mem_map.mpr ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
      apply Subtype.ext
      simpa [MulAut.conj_apply] using hky
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr
        ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, ?_⟩)
      have h := congrArg Subtype.val hky
      simpa [MulAut.conj_apply] using h
  have hcomp : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
        (MulAut.conj (⟨g, hg⟩ : ↥L)).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨g, hg⟩)).toMonoidHom.comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    ext x
    simp [MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [barImage, barImage, hKsub, Subgroup.map_map, hcomp, ← Subgroup.map_map]

private theorem k891classes_conj_comp {G : Type} [Group G] (x y : G) :
    (MulAut.conj (x * y)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
  ext z
  show (x * y) * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹
  group

private theorem k891classes_map_conj_le {G : Type} [Group G] {L X : Subgroup G}
    (hXL : X ≤ L) {l : G} (hl : l ∈ L) :
    X.map (MulAut.conj l).toMonoidHom ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact L.mul_mem (L.mul_mem hl (hXL hx)) (L.inv_mem hl)

private theorem k891classes_barImage_centralizer_le {G : Type} [Group G] [Finite G]
    (L X : Subgroup G) (hXL : X ≤ L) (hX : IsPGroup 3 X) :
    barImage L (L ⊓ centralizer (X : Set G)) ≤
      ⊤ ⊓ centralizer (barImage L X : Set (Bar2 L)) :=
  le_of_eq (barImage_inf_centralizer_eq hXL Nat.prime_three (by norm_num) hX)

theorem s891_classes
    {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (R : Subgroup G) (hR : R891XShape D L S n R) :
    ∃ A : Subgroup G, A ≤ R ∧ R891Classes L S A := by
  set Z : Subgroup G := ZOf (S ⊓ L) with hZdef
  have hSp := hbasic.sylowL.isPGroup
  have hZR : Z ≤ R := by rw [hZdef]; exact hR.zLe
  have hZSp : Z ≤ S ⊓ L := by rw [hZdef]; exact inf_le_left
  have hZL : Z ≤ L := hZSp.trans inf_le_right
  have hZcard : Nat.card Z = 3 := by rw [hZdef]; exact hbasic.zOrder
  have hZp := hSp.to_le hZSp
  have hRcard : Nat.card ↥R = 3 ^ (1 + 2 * 1) := hR.rExtra.1
  have hRexp : Monoid.exponent ↥R = 3 := hR.rExtra.2.1
  have hR3 : IsPGroup 3 R := k891classes_isPGroup_R hR.rExtra
  have hZltR : Z < R := by
    refine lt_of_le_of_ne hZR ?_
    intro h
    have hcard : Nat.card R = Nat.card Z := by rw [h]
    rw [hRcard, hZcard] at hcard
    norm_num at hcard
  obtain ⟨a, haR, haZ⟩ := Set.exists_of_ssubset hZltR
  have ha3 : a ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨a, haR⟩ : ↥R)
    rw [hRexp] at h
    simpa using h
  have ha1 : a ≠ 1 := by
    intro h; exact haZ (h ▸ Z.one_mem)
  have haord : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ha3) with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h3
  set A : Subgroup G := Subgroup.zpowers a with hAdef
  have hAcard : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, haord]
  have hAR : A ≤ R := by rw [hAdef]; exact Subgroup.zpowers_le.mpr haR
  have hASp : A ≤ S ⊓ L := hAR.trans hR.rSylow
  have hAL : A ≤ L := hASp.trans inf_le_right
  have hAg := hR3.to_le hAR
  have hAneZ : A ≠ Z := by
    intro h; refine haZ ?_
    rw [← h, hAdef]; exact Subgroup.mem_zpowers a
  set P : Subgroup (Bar2 L) := barImage L (S ⊓ L) with hPdef
  have hcard_center : Nat.card (ZOf P) = 3 := by
    rw [hPdef, ← card_zOf_eq_card_zOf_barImage (inf_le_right : S ⊓ L ≤ L) hSp]
    exact hbasic.zOrder
  have hZbar_le_ZOfP : barImage L Z ≤ ZOf P := by
    refine le_inf ?_ ?_
    · rw [hPdef]; exact barImage_mono hZSp
    · have hZleH : Z ≤ L ⊓ centralizer ((S ⊓ L) : Set G) :=
        le_inf hZL (by rw [hZdef]; exact inf_le_right)
      have h1 : barImage L Z ≤ barImage L (L ⊓ centralizer ((S ⊓ L) : Set G)) :=
        barImage_mono hZleH
      have h2 : barImage L (L ⊓ centralizer ((S ⊓ L) : Set G)) ≤
          ⊤ ⊓ centralizer (barImage L (S ⊓ L) : Set (Bar2 L)) :=
        k891classes_barImage_centralizer_le L (S ⊓ L) inf_le_right hSp
      exact h1.trans (h2.trans (le_of_eq (by rw [hPdef, top_inf_eq])))
  have hZOfP : barImage L Z = ZOf P := by
    refine Subgroup.eq_of_le_of_card_ge hZbar_le_ZOfP ?_
    rw [hcard_center, card_barImage_of_isPGroup hZL Nat.prime_three (by norm_num) hZp, hZcard]
  have hnotConj : ∀ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≠ Z := by
    intro l hl hAl
    have hAlinv : Z.map (MulAut.conj l⁻¹).toMonoidHom = A := by
      rw [← hAl, CFSG.GroupTheory.map_conj_map_conj_inv]
    have hLM : L ≤ D.M := hset.mem.1.le
    have hle : Z.map (MulAut.conj l⁻¹).toMonoidHom ≤ R891X L Z n := by
      rw [hAlinv]
      exact hAR.trans hR.rLe
    have hEq : Z.map (MulAut.conj l⁻¹).toMonoidHom = Z :=
      hR.zWeak l⁻¹ (D.M.inv_mem (hLM hl)) hle
    exact hAneZ (hAlinv.symm.trans hEq)
  have hAb_notconj : ∀ g : Bar2 L,
      (barImage L A).map (MulAut.conj g).toMonoidHom ≠ ZOf P := by
    intro g hg
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
    have hAconjL := k891classes_map_conj_le hAL l.2
    have hAconjp := hAg.map (MulAut.conj (l : G)).toMonoidHom
    have hmap : barImage L (A.map (MulAut.conj (l : G)).toMonoidHom) = barImage L Z := by
      rw [k891classes_barImage_map_conj L A hAL l.2, hl, hg, hZOfP]
    obtain ⟨nn, hnnN, hnn⟩ := k891classes_exists_conj_pCore L Z
      (A.map (MulAut.conj (l : G)).toMonoidHom) hZL hAconjL hZp hAconjp hmap.symm
    have hnnL : nn ∈ L := by
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hnnN
      exact x.2
    have hfinal : A.map (MulAut.conj (nn * (l : G))).toMonoidHom = Z := by
      rw [← CFSG.GroupTheory.map_conj_map_conj, hnn]
    exact hnotConj (nn * (l : G)) (L.mul_mem hnnL l.2) hfinal
  have hclasses : ∀ B : Subgroup G, B ≤ L → Nat.card B = 3 →
      (∃ l ∈ L, B = Z.map (MulAut.conj l).toMonoidHom) ∨
        (∃ l ∈ L, B = A.map (MulAut.conj l).toMonoidHom) := by
    intro B hBL hBcard
    have hBp : IsPGroup 3 ↥B := IsPGroup.of_card (n := 1) (by rw [hBcard]; norm_num)
    have hBcardb : Nat.card (barImage L B) = 3 := by
      rw [card_barImage_of_isPGroup hBL Nat.prime_three (by norm_num) hBp, hBcard]
    have hAbcard : Nat.card (barImage L A) = 3 := by
      rw [card_barImage_of_isPGroup hAL Nat.prime_three (by norm_num) hAg, hAcard]
    rcases r891_subgroup_classes hset.d4 hcard_center hAbcard
        hAb_notconj (barImage L B) hBcardb with
      ⟨g, hg⟩ | ⟨g, hg⟩
    · obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
      have hZC : barImage L (Z.map (MulAut.conj (l : G)).toMonoidHom) = barImage L B := by
        rw [k891classes_barImage_map_conj L Z hZL l.2, hl, hg, hZOfP]
      obtain ⟨nn, hnnN, hnn⟩ := k891classes_exists_conj_pCore L B
        (Z.map (MulAut.conj (l : G)).toMonoidHom) hBL (k891classes_map_conj_le hZL l.2) hBp
        (hZp.map (MulAut.conj (l : G)).toMonoidHom) hZC.symm
      have hnnL : nn ∈ L := by
        obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hnnN
        exact x.2
      refine Or.inl ⟨nn * (l : G), L.mul_mem hnnL l.2, ?_⟩
      rw [← hnn, Subgroup.map_map, ← k891classes_conj_comp]
    · obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
      have hAC : barImage L (A.map (MulAut.conj (l : G)).toMonoidHom) = barImage L B := by
        rw [k891classes_barImage_map_conj L A hAL l.2, hl, hg]
      obtain ⟨nn, hnnN, hnn⟩ := k891classes_exists_conj_pCore L B
        (A.map (MulAut.conj (l : G)).toMonoidHom) hBL (k891classes_map_conj_le hAL l.2) hBp
        (hAg.map (MulAut.conj (l : G)).toMonoidHom) hAC.symm
      have hnnL : nn ∈ L := by
        obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hnnN
        exact x.2
      refine Or.inr ⟨nn * (l : G), L.mul_mem hnnL l.2, ?_⟩
      rw [← hnn, Subgroup.map_map, ← k891classes_conj_comp]
  exact ⟨A, hAR, hAL, hAcard, hnotConj, hclasses⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
