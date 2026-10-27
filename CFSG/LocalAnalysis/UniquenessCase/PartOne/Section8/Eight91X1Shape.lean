module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Model
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.H13.NQTermAmbientQuotient
import CFSG.GroupTheory.BarImageConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.ABGLocalTools (IsSylowOf)

private theorem k891x1shape_exists_conj_eq_of_map_eq {X : Type*} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {P Q : Subgroup X}
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (hPQ : P.map (QuotientGroup.mk' N) = Q.map (QuotientGroup.mk' N)) :
    ∃ x : X, Q = P.map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQM : Q ≤ N ⊔ Q := le_sup_right
  have hPM : P ≤ N ⊔ Q := by
    intro p hp
    have h1 : QuotientGroup.mk' N p ∈ Q.map (QuotientGroup.mk' N) := hPQ ▸ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := h1
    have h2 : q⁻¹ * p ∈ N := by
      rw [← QuotientGroup.eq]
      exact hqp
    have h3 : p = q * (q⁻¹ * p) := by group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left h2)
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hQ, pow_one])
  have hrelQ : ¬ 3 ∣ Q.relIndex (N ⊔ Q) := by
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal]
    intro h3
    exact hN (h3.trans (Subgroup.index_dvd_card _))
  have hrel : P.relIndex (N ⊔ Q) = Q.relIndex (N ⊔ Q) := by
    have h1 := Subgroup.relIndex_mul_card P (N ⊔ Q)
    have h2 := Subgroup.relIndex_mul_card Q (N ⊔ Q)
    rw [inf_eq_left.mpr hPM, hP] at h1
    rw [inf_eq_left.mpr hQM, hQ] at h2
    omega
  have hSP : IsSylowOf 3 P (N ⊔ Q) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPM, hP3, hrel ▸ hrelQ⟩
  have hSQ : IsSylowOf 3 Q (N ⊔ Q) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hQM, hQ3, hrelQ⟩
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSP hSQ
  refine ⟨k, ?_⟩
  ext x
  rw [hk x]
  constructor
  · intro hx
    refine ⟨k⁻¹ * x * k, hx, ?_⟩
    change k * (k⁻¹ * x * k) * k⁻¹ = x
    group
  · rintro ⟨y, hy, rfl⟩
    change k⁻¹ * (k * y * k⁻¹) * k ∈ P
    simpa [mul_assoc] using hy

private theorem k891x1shape_conj_of_barImage_eq {G : Type} [Group G] [Finite G]
    (L : Subgroup G) {P Q : Subgroup G} (hPL : P ≤ L) (hQL : Q ≤ L)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3)
    (h : (P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      (Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :
    ∃ x ∈ L, Q = P.map (MulAut.conj x).toMonoidHom := by
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) Nat.prime_three
      (by norm_num)
  have hP' : Nat.card (P.subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hP]
  have hQ' : Nat.card (Q.subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv, hQ]
  obtain ⟨x, hx⟩ := k891x1shape_exists_conj_eq_of_map_eq hN hP' hQ' h
  refine ⟨x, x.2, ?_⟩
  have hcomp : L.subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp L.subtype := by
    ext y
    rfl
  calc Q = (Q.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hQL).symm
    _ = ((P.subgroupOf L).map (MulAut.conj x).toMonoidHom).map L.subtype := by rw [hx]
    _ = (P.subgroupOf L).map (L.subtype.comp (MulAut.conj x).toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (P.subgroupOf L).map ((MulAut.conj (x : G)).toMonoidHom.comp L.subtype) := by
          rw [hcomp]
    _ = ((P.subgroupOf L).map L.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = P.map (MulAut.conj (x : G)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hPL]

private theorem k891x1shape_isPerfect_derInf8 {G : Type} [Group G] [Finite G]
    (X : Subgroup G) : Group.IsPerfect ↥(F08.DerInf8 X) := by
  have hperf : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥X n) : Subgroup ↥X) :=
    CFSG.perfect_residual_characterization.2.2.1
  unfold F08.DerInf8
  exact @Group.IsPerfect.map ↥X G _ _ (⨅ n : ℕ, derivedSeries ↥X n) X.subtype hperf

private theorem k891x1shape_pCore_two_eq_bot_of_perfect_simple {H : Type*} [Group H] [Finite H]
    (hsimple : IsSimpleGroup H) (hperf : Group.IsPerfect H) : CFSG.pCore 2 H = ⊥ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 H) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup H) := by
      have := CFSG.pCore_isPGroup (p := 2) (G := H)
      rwa [h] at this
    have hp' : IsPGroup 2 H := hp.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent H := hp'.isNilpotent
    exact @Group.IsPerfect.not_isNilpotent H _ hsimple.toNontrivial hperf hnil

theorem s891_x1_shape
    {G : Type} [Group G] [Finite G] (D : Data G)
    (L S A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hA : R891Classes L S A) :
    R891X1Shape L A n := by
  classical
  have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by rw [hA.aOrder, pow_one])
  have hPa3 : IsPGroup 3 ↥(S ⊓ L) := hbasic.sylowL.isPGroup
  have hZ3 : IsPGroup 3 ↥(ZOf (S ⊓ L)) := hPa3.to_le inf_le_left
  have hsylPbar : IsSylowOf 3 (barImage L (S ⊓ L)) ⊤ := by
    obtain ⟨hp, hidx⟩ := isPGroup_barImage_of_isSylowOf Nat.prime_three hbasic.sylowL
    exact (CFSG.ABGLocalTools.isSylowOf_iff (G := Bar2 L)).2
      ⟨le_top, hp, by rwa [Subgroup.relIndex_top_right]⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAbarCard : Nat.card (barImage L A) = 3 := by
    rw [card_barImage_of_isPGroup hA.aLe Nat.prime_three (by norm_num) hA3, hA.aOrder]
  have hZleP : ZOf (S ⊓ L) ≤ S ⊓ L := inf_le_left
  have hZleL : ZOf (S ⊓ L) ≤ L := hZleP.trans inf_le_right
  have hZleC : ZOf (S ⊓ L) ≤ centralizer ((S ⊓ L : Subgroup G) : Set G) := inf_le_right
  have hZbar_le_cent : barImage L (ZOf (S ⊓ L)) ≤
      centralizer (barImage L (S ⊓ L) : Set (Bar2 L)) := by
    have h1 : ZOf (S ⊓ L) ≤ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
      le_inf hZleL hZleC
    have h2 : barImage L (ZOf (S ⊓ L)) ≤
        barImage L (L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)) := barImage_mono h1
    rw [barImage_inf_centralizer_eq (L := L) (X := S ⊓ L) inf_le_right Nat.prime_three
      (by norm_num) hPa3] at h2
    exact h2.trans inf_le_right
  have hZbar_le : barImage L (ZOf (S ⊓ L)) ≤ ZOf (barImage L (S ⊓ L)) := by
    rw [ZOf]
    exact le_inf (barImage_mono hZleP) hZbar_le_cent
  have hZbarCard : Nat.card (barImage L (ZOf (S ⊓ L))) = 3 := by
    rw [card_barImage_of_isPGroup hZleL Nat.prime_three (by norm_num) hZ3, hbasic.zOrder]
  have hZofPbarCard : Nat.card (ZOf (barImage L (S ⊓ L))) = 3 :=
    (card_zOf_eq_card_zOf_barImage (inf_le_right : S ⊓ L ≤ L) hPa3).symm.trans hbasic.zOrder
  have hZeq : barImage L (ZOf (S ⊓ L)) = ZOf (barImage L (S ⊓ L)) :=
    Subgroup.eq_of_le_of_card_ge hZbar_le (by rw [hZofPbarCard, hZbarCard])
  have hnotconj : ∀ g : Bar2 L,
      (barImage L A).map (MulAut.conj g).toMonoidHom ≠ ZOf (barImage L (S ⊓ L)) := by
    intro g hg
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
    have hAlL : A.map (MulAut.conj (l : G)).toMonoidHom ≤ L := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      exact L.mul_mem (L.mul_mem l.2 (hA.aLe ha)) (L.inv_mem l.2)
    have hAlCard : Nat.card (A.map (MulAut.conj (l : G)).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (l : G)).injective, hA.aOrder]
    have hAl_img : barImage L (A.map (MulAut.conj (l : G)).toMonoidHom) =
        barImage L (ZOf (S ⊓ L)) := by
      have h1 : barImage L (A.map (MulAut.conj (l : G)).toMonoidHom) =
          (barImage L A).map
            (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l)).toMonoidHom := by
        exact CFSG.GroupTheory.barImage_map_conj L A hA.aLe l.2
      rw [h1, hl, hg, hZeq]
    obtain ⟨x, hxL, hx⟩ :=
      k891x1shape_conj_of_barImage_eq L hAlL hZleL hAlCard hbasic.zOrder
        (by simpa only [barImage] using hAl_img)
    have hfinal : ZOf (S ⊓ L) = A.map (MulAut.conj (x * l)).toMonoidHom := by
      rw [hx]
      rw [Subgroup.map_map]
      congr 1
      ext a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hA.notConj (x * l) (L.mul_mem hxL l.2) hfinal.symm
  obtain ⟨hLie₀, hCent⟩ := r891_x1_model_of_not_conj_sylow_center
    hset.d4 hsylPbar hZofPbarCard hAbarCard hnotconj
  have hLie : LieModel ↥(DerInf8 ((⊤ : Subgroup (Bar2 L)) ⊓
      centralizer (barImage L A : Set (Bar2 L)))) .PSL 2 2 (3 * n) := by
    rw [show (⊤ : Subgroup (Bar2 L)) ⊓ centralizer (barImage L A : Set (Bar2 L)) =
      centralizer (barImage L A : Set (Bar2 L)) from top_inf_eq _]
    exact hLie₀
  refine ⟨?_, hCent⟩
  obtain ⟨e⟩ := nonempty_bar2_derInf8_equiv (L := L) (X := A) hA.aLe Nat.prime_three
    (by norm_num) hA3
  have hHperf : Group.IsPerfect
      ↥(F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L)))) :=
    k891x1shape_isPerfect_derInf8 _
  have hHsimple : IsSimpleGroup
      ↥(F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L)))) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie
  have hHbot : CFSG.pCore 2
      ↥(F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L)))) = ⊥ :=
    k891x1shape_pCore_two_eq_bot_of_perfect_simple hHsimple hHperf
  have e2 : Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L)))) ≃*
      ↥(F08.DerInf8 (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L)))) :=
    (QuotientGroup.quotientMulEquivOfEq hHbot).trans QuotientGroup.quotientBot
  exact CFSG.Blueprint.LieModel.of_mulEquiv (e.trans e2).symm hLie

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
