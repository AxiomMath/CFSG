module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par
import CFSG.GroupTheory.AlternatingFive.PiSylowNormalizer
import CFSG.Quasithin.H13.NQCatRkOneProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotSpan
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
import CFSG.Quasithin.Vol2.Ch12Sec5FinC
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_alt_five_orbit_three_parabolic
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 3)
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5) :
    T3Parab
      (⨆ g : ↥(Mbar D.M V₀ V hV),
        (lBar V₀ V hV L).map
          (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom)
      (barSub V₀ V hV D.T) 3 := by
  classical
  set W := Vtil V₀ V hV
  set A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  set H : Subgroup (MulAut W) := lBar V₀ V hV L
  set T : Subgroup (MulAut W) := barSub V₀ V hV D.T
  set B : Subgroup (MulAut W) :=
    ⨆ g : A, H.map (MulAut.conj (g : MulAut W)).toMonoidHom
  set O : Set (Subgroup (MulAut W)) :=
    {X | ∃ g ∈ A, X = H.map (MulAut.conj (g : MulAut W)).toMonoidHom}
  let I : Type := ↥O
  let F : I → Subgroup (MulAut W) := fun i => i.1
  have hcardI : Nat.card I = 3 := by
    change Nat.card ↥O = 3
    rw [Nat.card_coe_set_eq]
    simpa [O, A, H, W, s15, lBar, Mbar] using hs
  have hfinI : Finite I := Nat.finite_of_card_ne_zero (by rw [hcardI]; norm_num)
  have hex (i : I) : ∃ g : A, F i = H.map (MulAut.conj (g : MulAut W)).toMonoidHom := by
    obtain ⟨g, hg, hX⟩ := i.2
    exact ⟨⟨g, hg⟩, hX⟩
  let gOf (i : I) : A := Classical.choose (hex i)
  have hFOf (i : I) : F i = H.map (MulAut.conj (gOf i : MulAut W)).toMonoidHom :=
    Classical.choose_spec (hex i)
  have hFcomp : ∀ i : I, IsComponentOf (F i) A := by
    intro i
    rw [hFOf i]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcomp (gOf i).2
  have hne : ∀ i j : I, i ≠ j → F i ≠ F j := by
    intro i j hij h
    exact hij (Subtype.ext h)
  have hcomm : Pairwise fun i j : I =>
      ∀ x y : MulAut W, x ∈ F i → y ∈ F j → Commute x y := by
    intro i j hij x y hx hy
    exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne
      (hFcomp i) (hFcomp j) (hne i j hij) hx hy
  let eH : ↥H ≃* alternatingGroup (Fin 5) := Classical.choice hA5
  let eF : ∀ i : I, F i ≃* alternatingGroup (Fin 5) := fun i =>
    ((Subgroup.equivMapOfInjective H (MulAut.conj (gOf i : MulAut W)).toMonoidHom
        (MulAut.conj (gOf i : MulAut W)).injective).trans
      (MulEquiv.subgroupCongr (hFOf i).symm)).symm.trans eH
  have hcenter : ∀ i : I, Subgroup.center (F i) = ⊥ := by
    intro i
    have hmap := Subgroup.map_center_eq (eF i)
    rw [alternatingGroup.center_eq_bot (α := Fin 5) (by norm_num)] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (F i))
      (f := (eF i).toMonoidHom) (eF i).injective).1 hmap
  have hZ : ∀ j, ∀ x ∈ F j, (∀ y ∈ F j, Commute x y) → x = 1 := by
    intro j x hx hxc
    have hxcenter : (⟨x, hx⟩ : F j) ∈ Subgroup.center (F j) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((hxc y y.2).symm)
    rw [hcenter j] at hxcenter
    have h1 := Subgroup.mem_bot.1 hxcenter
    simpa using congrArg Subtype.val h1
  have hind : iSupIndep F :=
    CFSG.Quasithin.H13.NQCat.RkOne.iSupIndep_of_commute F hcomm hZ
  obtain ⟨e, -⟩ := @CFSG.LocalCores.exists_mulEquiv_pi_iSup (MulAut W) _ I hfinI F hcomm hind
  have hB_eq : (⨆ i : I, F i) = B := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rw [hFOf i]
      exact le_iSup (fun g : A => H.map (MulAut.conj (g : MulAut W)).toMonoidHom) (gOf i)
    · refine iSup_le fun g => ?_
      exact le_iSup (fun i : I => F i)
        ⟨H.map (MulAut.conj (g : MulAut W)).toMonoidHom, ⟨g, g.2, rfl⟩⟩
  let eP : (∀ i : I, F i) ≃* (I → alternatingGroup (Fin 5)) :=
    MulEquiv.piCongrRight (fun i => eF i)
  let eB : ↥B ≃* (I → alternatingGroup (Fin 5)) :=
    ((e.trans (MulEquiv.subgroupCongr hB_eq)).symm).trans eP
  have hT : IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T A :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).2
      (s16c1_barSub_sylow c.m_le_stabTil hT)
  have hBA : B ≤ A := by
    refine iSup_le fun g => ?_
    calc H.map (MulAut.conj (g : MulAut W)).toMonoidHom
        ≤ A.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.map_mono hcomp.1
      _ = A := Subgroup.mem_normalizer_iff_map_conj_eq.1
          (Subgroup.le_normalizer (H := A) g.2)
  have hAnormB : A ≤ Subgroup.normalizer (B : Set (MulAut W)) := by
    have hnormal : (B.subgroupOf A).Normal :=
      s15_semiBot_iSup_map_conj_normal hcomp.1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).1 hnormal
  set S : Subgroup (MulAut W) := T ⊓ B
  have hSsylB : CFSG.ABGLocalTools.IsSylowOf 2 S B :=
    hTsyl.inf_of_le_normalizer hBA hAnormB
  obtain ⟨SB, hSB⟩ := hSsylB.exists_sylow_eq_subgroupOf
  let S' : Sylow 2 (I → alternatingGroup (Fin 5)) :=
    SB.mapSurjective (f := eB.toMonoidHom) (by simpa using eB.surjective)
  have hS'coe : (S' : Subgroup (I → alternatingGroup (Fin 5))) =
      (S.subgroupOf B).map eB.toMonoidHom := by
    dsimp only [S']
    rw [Sylow.coe_mapSurjective, hSB]
  have hmodel := CFSG.GroupTheory.AlternatingFive.sylow_two_pi_normalizer_facts
    (ι := I) (S := S')
  have hcardS' : Nat.card S' = Nat.card (S.subgroupOf B) := by
    rw [hS'coe, Subgroup.card_map_of_injective eB.injective]
  have hcardSsub : Nat.card (S.subgroupOf B) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := S) (K := B) inf_le_right).toEquiv
  have hcardS : Nat.card S = 4 ^ 3 := by
    rw [← hcardSsub, ← hcardS']
    rw [hmodel.1, hcardI]
  set P : Subgroup (MulAut W) := B ⊓ Subgroup.normalizer (S : Set (MulAut W))
  have hPmap : (P.subgroupOf B).map eB.toMonoidHom =
      Subgroup.normalizer (S' : Set (I → alternatingGroup (Fin 5))) := by
    dsimp only [P]
    rw [Subgroup.inf_subgroupOf_left (Subgroup.normalizer (S : Set (MulAut W))) B]
    rw [Subgroup.subgroupOf_normalizer_eq (H := S) (N := B) inf_le_right]
    rw [Subgroup.map_equiv_normalizer_eq (S.subgroupOf B) eB]
    rw [← hS'coe]
    rfl
  have hcardPsub : Nat.card (P.subgroupOf B) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P) (K := B) inf_le_left).toEquiv
  have hcardPmap : Nat.card ((P.subgroupOf B).map eB.toMonoidHom) =
      Nat.card (P.subgroupOf B) :=
    Subgroup.card_map_of_injective eB.injective
  have hcardP : Nat.card P = 12 ^ 3 := by
    rw [← hcardPsub, ← hcardPmap, hPmap]
    rw [hmodel.2.1, hcardI]
  have hexpP : ∀ x ∈ P, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
    intro x hx n hn
    have hxB : x ∈ B := (inf_le_left : P ≤ B) hx
    have hxN : eB ⟨x, hxB⟩ ∈ Subgroup.normalizer
        (S' : Set (I → alternatingGroup (Fin 5))) := by
      rw [← hPmap]
      exact Subgroup.mem_map_of_mem eB.toMonoidHom
        (show (⟨x, hxB⟩ : ↥B) ∈ P.subgroupOf B from hx)
    have hpow_sub : (⟨x, hxB⟩ : ↥B) ^ 3 ^ n = 1 := by
      apply Subtype.ext
      simpa using hn
    have hpow : (eB ⟨x, hxB⟩) ^ 3 ^ n = 1 := by
      rw [← map_pow, hpow_sub, map_one]
    have h3 := hmodel.2.2 (eB ⟨x, hxB⟩) hxN n hpow
    have hsub : (⟨x, hxB⟩ : ↥B) ^ 3 = 1 := by
      apply eB.injective
      rw [map_pow, h3, map_one]
    simpa using congrArg Subtype.val hsub
  have hTnormB : T ≤ Subgroup.normalizer (B : Set (MulAut W)) :=
    hTsyl.le.trans hAnormB
  have hTnormT : T ≤ Subgroup.normalizer (T : Set (MulAut W)) := Subgroup.le_normalizer
  have hTnormS : T ≤ Subgroup.normalizer (S : Set (MulAut W)) :=
    (le_inf hTnormT hTnormB).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := B))
  have hTnormNS : T ≤ Subgroup.normalizer
      (Subgroup.normalizer (S : Set (MulAut W)) : Set (MulAut W)) :=
    hTnormS.trans (Subgroup.le_normalizer (H := Subgroup.normalizer (S : Set (MulAut W))))
  have hTnormP : T ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
    (le_inf hTnormB hTnormNS).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := B)
        (K := Subgroup.normalizer (S : Set (MulAut W))))
  have hSP : S ≤ P := le_inf inf_le_right (Subgroup.le_normalizer (H := S))
  have hTinterP : T ⊓ P = S := by
    apply le_antisymm
    · calc T ⊓ P ≤ T ⊓ B := inf_le_inf le_rfl inf_le_left
        _ = S := rfl
    · exact le_inf inf_le_left hSP
  have hJle : T ⊔ P ≤ B ⊔ T :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  have hPcard : Nat.card P = 3 ^ 3 * Nat.card S := by
    rw [hcardP, hcardS]
    norm_num
  have hcardJ : Nat.card (T ⊔ P : Subgroup (MulAut W)) = 3 ^ 3 * Nat.card T := by
    have hprod := s16c7_card_sup_mul_card_inf (X := MulAut W) (A := T) (N := P) hTnormP
    rw [hTinterP] at hprod
    have hSpos : 0 < Nat.card S := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hSpos
    calc Nat.card (T ⊔ P : Subgroup (MulAut W)) * Nat.card S
        = Nat.card T * Nat.card P := hprod
      _ = Nat.card T * (3 ^ 3 * Nat.card S) := by rw [hPcard]
      _ = (3 ^ 3 * Nat.card T) * Nat.card S := by ring
  have hexpJ : ∀ x ∈ (T ⊔ P : Subgroup (MulAut W)), ∀ n : ℕ,
      x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
    intro x hx n hn
    have hx' : x ∈ P ⊔ T := by rwa [sup_comm] at hx
    have hxP : x ∈ P :=
      CFSG.Quasithin.H13.S125Fin.mem_of_mem_sup_of_pow
        (X := P) (T := T) hTsyl.isPGroup hTnormP hx' hn
    exact hexpP x hxP n hn
  change T3Parab B T 3
  exact ⟨T ⊔ P, le_sup_left, hJle, hcardJ, hexpJ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
