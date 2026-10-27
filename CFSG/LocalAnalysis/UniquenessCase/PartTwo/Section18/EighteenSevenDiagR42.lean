module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GLayerSub
public import CFSG.Timmesfeld.Bridge.RootClosureL2Chief
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.LocalAnalysis.WeakClosure81.CFAutTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonempty_bar2_image_mulEquiv_of_isSubnormal {H K : Subgroup G} (hKH : K ≤ H)
    (hsn : CFSG.Open.IsSubnormal K H) :
    Nonempty (Bar2 K ≃* ↥(imageBar2 H K)) :=
  CFSG.RankThree.PartTwo.Sec18.Claim184LcProof.quotient_mulEquiv_map hKH
    ((pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsn).le.trans inf_le_right)

theorem map_orbitClosure {H' Q : Type} [Group H'] [Group Q] (π : H' →* Q) (K T : Subgroup H') :
    orbitClosure (K.map π) (T.map π) = (orbitClosure K T).map π := by
  have hconj : ∀ t : H', (K.map (MulAut.conj t).toMonoidHom).map π =
      (K.map π).map (MulAut.conj (π t)).toMonoidHom := by
    intro t
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul]
  refine le_antisymm ?_ ?_
  · refine orbitClosure_le fun u hu => ?_
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← hconj t]
    exact Subgroup.map_mono (le_iSup₂_of_le t ht le_rfl)
  · rw [Subgroup.map_le_iff_le_comap]
    refine orbitClosure_le fun t ht => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    rw [hconj t]
    exact le_iSup₂_of_le (π t) (Subgroup.mem_map_of_mem π ht) le_rfl

theorem p42_swap_data {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : UC22.conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : UC22.conjClosure D.M L ≠ L) :
    ¬ D.T ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom = CFSG.Quasithin.conjSubgroup L x := by
  classical
  set K : Subgroup G := L.map (MulAut.conj x⁻¹).toMonoidHom with hKdef
  have hKconj : CFSG.Quasithin.conjSubgroup L x = K := rfl
  obtain ⟨-, hKne⟩ := conjSubgroup_mem_calC_and_ne hL hxM hXsup hne
  have hc2 : (conjSetOf D.M L).ncard = 2 := ncard_eq_two_of_p42 hL hxM hXsup hne
  have hpair : conjSetOf D.M L = {L, K} :=
    uc22p22d_conjSet_pair (M := D.M) (K := L) (t := x⁻¹) (D.M.inv_mem hxM) hKne hc2
  have hTsyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hPidx : ¬ 2 ∣ ((D.T).subgroupOf D.M).index := by
    simpa [Subgroup.relIndex] using hTsyl.2.2
  have hSyl2 : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M := ⟨hTsyl.1, hTsyl.2.1, hPidx⟩
  have hMT : D.T ⊔ S17.oUpperTwo D.M = D.M := by
    have h := CFSG.Quasithin.sup_twoResidual_eq (G := G) hSyl2
    rwa [← oUpperTwo_eq_twoResidual] at h
  have hO2N : S17.oUpperTwo D.M ≤ Subgroup.normalizer (L : Set G) := by
    rw [S17.oUpperTwo_eq_closure, Subgroup.closure_le]
    rintro g ⟨hgM, hodd⟩
    exact uc22p2214_mem_normalizer_of_odd hc2 hgM hodd
  have hTnot : ¬ D.T ≤ Subgroup.normalizer (L : Set G) := by
    intro hTN
    have hMN : D.M ≤ Subgroup.normalizer (L : Set G) := by
      rw [← hMT]
      exact sup_le hTN hO2N
    have hsingle : conjSetOf D.M L = {L} := by
      ext K'
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact Set.mem_singleton_iff.mpr
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMN hm))
      · intro hK'
        rw [Set.mem_singleton_iff.mp hK']
        exact ⟨1, D.M.one_mem, by ext y; simp [MulAut.conj_apply]⟩
    rw [hsingle, Set.ncard_singleton] at hc2
    omega
  obtain ⟨t, htT, htne⟩ : ∃ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom ≠ L := by
    by_contra h
    push Not at h
    exact hTnot fun t ht => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h t ht)
  have htmem : L.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M L :=
    ⟨t, D.sylowM.le htT, rfl⟩
  have htK : L.map (MulAut.conj t).toMonoidHom = K := by
    have hmem : L.map (MulAut.conj t).toMonoidHom ∈ ({L, K} : Set (Subgroup G)) := by
      rw [← hpair]; exact htmem
    rcases Set.mem_insert_iff.mp hmem with h1 | h1
    · exact absurd h1 htne
    · exact Set.mem_singleton_iff.mp h1
  exact ⟨hTnot, t, htT, htK.trans hKconj.symm⟩

theorem orbitClosure_eq_conjClosure_of_p42 {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : UC22.conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : UC22.conjClosure D.M L ≠ L) :
    orbitClosure L D.T = UC22.conjClosure D.M L := by
  obtain ⟨-, t, htT, htK⟩ := p42_swap_data hL hxM hXsup hne
  refine le_antisymm ?_ ?_
  · refine orbitClosure_le fun u hu => ?_
    exact le_iSup₂_of_le (L.map (MulAut.conj u).toMonoidHom)
      ⟨u, D.sylowM.le hu, rfl⟩ le_rfl
  · rw [hXsup]
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (1 : G) D.T.one_mem (le_of_eq (by ext y; simp [MulAut.conj_apply]))
    · exact le_iSup₂_of_le t htT (le_of_eq htK.symm)

theorem orbitClosure_imageBar2_sup_imageBar2_eq_top {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : UC22.conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : UC22.conjClosure D.M L ≠ L) {H : Subgroup G}
    (hH : H = UC22.conjClosure D.M L ⊔ D.T) :
    orbitClosure (imageBar2 H L) (imageBar2 H D.T) ⊔ imageBar2 H D.T = ⊤ := by
  classical
  subst hH
  have hXorbit : orbitClosure L D.T = UC22.conjClosure D.M L :=
    orbitClosure_eq_conjClosure_of_p42 hL hxM hXsup hne
  rw [← hXorbit]
  have hLX : L ≤ orbitClosure L D.T := le_iSup₂_of_le (1 : G) D.T.one_mem
    (le_of_eq (by ext y; simp [MulAut.conj_apply]))
  have hYH : orbitClosure L D.T ≤ orbitClosure L D.T ⊔ D.T := le_sup_left
  have hLH : L ≤ orbitClosure L D.T ⊔ D.T := hLX.trans hYH
  have hTH : D.T ≤ orbitClosure L D.T ⊔ D.T := le_sup_right
  have hYnorm : D.M ≤ Subgroup.normalizer (orbitClosure L D.T : Set G) := by
    rw [hXorbit]
    exact (conjSetOf_subset_calC_conjClosure hL).2.1
  have hLtY : ∀ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom ≤ orbitClosure L D.T :=
    fun t ht => le_iSup₂_of_le t ht le_rfl
  have hLtX : ∀ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom ≤ orbitClosure L D.T ⊔ D.T :=
    fun t ht => (hLtY t ht).trans hYH
  let π : ↥(orbitClosure L D.T ⊔ D.T) →* Bar2 (orbitClosure L D.T ⊔ D.T) :=
    piBar2 (orbitClosure L D.T ⊔ D.T)
  have hXle_sub : (orbitClosure L D.T).comap (orbitClosure L D.T ⊔ D.T).subtype ≤
      orbitClosure (L.comap (orbitClosure L D.T ⊔ D.T).subtype)
        (D.T.comap (orbitClosure L D.T ⊔ D.T).subtype) := by
    set H : Subgroup G := orbitClosure L D.T ⊔ D.T with hHdef
    let K : G → Subgroup G := fun i => L.map (MulAut.conj i).toMonoidHom
    have hKle : ∀ i, i ∈ D.T → K i ≤ H := fun i hi => hLtX i hi
    change (⨆ i, ⨆ (_ : i ∈ D.T), K i).comap H.subtype ≤ _
    have hcomap : (⨆ i, ⨆ (_ : i ∈ D.T), K i).comap H.subtype =
        ⨆ i, ⨆ (_ : i ∈ D.T), (K i).comap H.subtype := by
      simpa only [iSup_subtype] using
        CFSG.RankThree.Classical.comap_iSup_of_le_range (f := H.subtype) H.subtype_injective
          (L := fun j : {i // i ∈ D.T} => K j.1)
          (fun j => by simpa [Subgroup.range_subtype] using hKle j.1 j.2)
    rw [hcomap]
    refine iSup_le fun t => iSup_le fun ht => ?_
    change (L.map (MulAut.conj t).toMonoidHom).subgroupOf H ≤ _
    rw [subgroupOf_map_conj_of_le (K := L) hLH (hTH ht)]
    exact le_iSup₂_of_le (⟨t, hTH ht⟩ : ↥H) ht le_rfl
  have hXle : imageBar2 (orbitClosure L D.T ⊔ D.T) (orbitClosure L D.T) ≤
      orbitClosure (imageBar2 (orbitClosure L D.T ⊔ D.T) L)
        (imageBar2 (orbitClosure L D.T ⊔ D.T) D.T) := by
    have h := Subgroup.map_mono (f := π) hXle_sub
    rw [← map_orbitClosure π (L.comap (orbitClosure L D.T ⊔ D.T).subtype)
      (D.T.comap (orbitClosure L D.T ⊔ D.T).subtype)] at h
    exact h
  have horb_le : orbitClosure (imageBar2 (orbitClosure L D.T ⊔ D.T) L)
      (imageBar2 (orbitClosure L D.T ⊔ D.T) D.T) ≤
      imageBar2 (orbitClosure L D.T ⊔ D.T) (orbitClosure L D.T) := by
    refine orbitClosure_le fun u hu => ?_
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    have htT : ((t : ↥(orbitClosure L D.T ⊔ D.T)) : G) ∈ D.T := ht
    have hconj : (imageBar2 (orbitClosure L D.T ⊔ D.T) L).map
        (MulAut.conj (π t)).toMonoidHom =
        imageBar2 (orbitClosure L D.T ⊔ D.T)
          (L.map (MulAut.conj ((t : ↥(orbitClosure L D.T ⊔ D.T)) : G)).toMonoidHom) := by
      have h1 : imageBar2 (orbitClosure L D.T ⊔ D.T)
          (L.map (MulAut.conj ((t : ↥(orbitClosure L D.T ⊔ D.T)) : G)).toMonoidHom) =
          ((L.subgroupOf (orbitClosure L D.T ⊔ D.T)).map
            (MulAut.conj (⟨((t : ↥(orbitClosure L D.T ⊔ D.T)) : G), hTH htT⟩ :
              ↥(orbitClosure L D.T ⊔ D.T))).toMonoidHom).map π := by
        rw [imageBar2, subgroupOf_map_conj_of_le (K := L) hLH (hTH htT)]
      rw [h1, imageBar2, Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hconj]
    exact Subgroup.map_mono (Subgroup.comap_mono (hLtY _ htT))
  have htop : imageBar2 (orbitClosure L D.T ⊔ D.T) (orbitClosure L D.T) ⊔
      imageBar2 (orbitClosure L D.T ⊔ D.T) D.T = ⊤ := by
    show ((orbitClosure L D.T).subgroupOf (orbitClosure L D.T ⊔ D.T)).map π ⊔
      ((D.T.subgroupOf (orbitClosure L D.T ⊔ D.T)).map π) = ⊤
    rw [← Subgroup.map_sup]
    have hsup : (orbitClosure L D.T).subgroupOf (orbitClosure L D.T ⊔ D.T) ⊔
        D.T.subgroupOf (orbitClosure L D.T ⊔ D.T) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hYH hTH, Subgroup.subgroupOf_self]
    rw [hsup, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  rw [← htop]
  exact le_antisymm (sup_le_sup horb_le le_rfl) (sup_le_sup hXle le_rfl)

theorem shape_of_two_components {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q} {m : ℕ}
    (hAc : CFSG.IsComponent A) (hBc : CFSG.IsComponent B)
    (hAs : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A)
    (hBs : IsSimpleGroup ↥B) (hBn : ¬ IsMulCommutative ↥B)
    (hAnb : A ≠ ⊥) (hBnb : B ≠ ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hFnorm : (A ⊔ B).Normal)
    (hFmin : ∀ N : Subgroup Q, N.Normal → N ≤ A ⊔ B → N = ⊥ ∨ N = A ⊔ B)
    (hC : Subgroup.centralizer ((A ⊔ B : Subgroup Q) : Set Q) = ⊥)
    (hquot : IsPGroup 2 (Q ⧸ (A ⊔ B)))
    (hshapeA : IsL2 ↥A m ∨ IsSz ↥A m) (hshapeB : IsL2 ↥B m ∨ IsSz ↥B m) :
    ∀ (Y : Subgroup Q) (hY : Y.Normal) (X : Subgroup (Q ⧸ Y)) (hXn : X.Normal)
      (hXne : X ≠ ⊥)
      (hXmin : ∀ N : Subgroup (Q ⧸ Y), N.Normal → N ≤ X → N = ⊥ ∨ N = X)
      (hXnc : ¬ IsMulCommutative X),
      ∀ L : Subgroup (Q ⧸ Y), CFSG.Open.IsComponentOf L X → IsL2 ↥L m ∨ IsSz ↥L m := by
  intro Y hY X hXn hXne hXmin hXnc L hL
  classical
  haveI := hY
  have hYtrich : Y = ⊥ ∨ A ⊔ B ≤ Y := by
    by_cases hYbot : Y = ⊥
    · exact Or.inl hYbot
    · right
      haveI : (A ⊔ B).Normal := hFnorm
      rcases hFmin (Y ⊓ (A ⊔ B)) (Subgroup.normal_inf_normal Y (A ⊔ B))
        inf_le_right with h0 | htop
      · exfalso
        have hYA : Y ≤ Subgroup.centralizer (A : Set Q) := by
          rcases CFSG.LocalCores.component_normal_subgroup hAc hY with hle | hc
          · exfalso
            have h1 : A ≤ Y ⊓ (A ⊔ B) := le_inf hle le_sup_left
            rw [h0] at h1
            exact hAnb (le_bot_iff.mp h1)
          · rw [Subgroup.commutator_comm] at hc
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
        have hYB : Y ≤ Subgroup.centralizer (B : Set Q) := by
          rcases CFSG.LocalCores.component_normal_subgroup hBc hY with hle | hc
          · exfalso
            have h1 : B ≤ Y ⊓ (A ⊔ B) := le_inf hle le_sup_right
            rw [h0] at h1
            exact hBnb (le_bot_iff.mp h1)
          · rw [Subgroup.commutator_comm] at hc
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
        have hYzero : Y ≤ Subgroup.centralizer ((A ⊔ B : Subgroup Q) : Set Q) := by
          rw [Subgroup.le_centralizer_iff] at hYA hYB ⊢
          exact sup_le hYA hYB
        rw [hC] at hYzero
        exact hYbot (le_bot_iff.mp hYzero)
      · exact (le_of_eq htop.symm).trans inf_le_left
  rcases hYtrich with hYbot | hFY
  ·
    subst hYbot
    let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
    let X₀ : Subgroup Q := X.map e.toMonoidHom
    have hX₀map : X₀.map e.symm.toMonoidHom = X := by
      simp [X₀, Subgroup.map_map]
    have hX₀n : X₀.Normal := hXn.map e.toMonoidHom e.surjective
    have hX₀ne : X₀ ≠ ⊥ := by
      intro h
      apply hXne
      have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) h
      rw [hX₀map, Subgroup.map_bot] at h1
      exact h1
    have hX₀min : ∀ N : Subgroup Q, N.Normal → N ≤ X₀ → N = ⊥ ∨ N = X₀ := by
      intro N hNn hNle
      have hN'n : (N.map e.symm.toMonoidHom).Normal :=
        hNn.map e.symm.toMonoidHom e.symm.surjective
      have hN'le : N.map e.symm.toMonoidHom ≤ X := by
        rw [← hX₀map]
        exact Subgroup.map_mono hNle
      rcases hXmin (N.map e.symm.toMonoidHom) hN'n hN'le with h0 | htop
      · left
        have h1 : N.map e.symm.toMonoidHom = (⊥ : Subgroup Q).map e.symm.toMonoidHom := by
          rw [h0, Subgroup.map_bot]
        exact Subgroup.map_injective e.symm.injective h1
      · right
        have h1 : N.map e.symm.toMonoidHom = X₀.map e.symm.toMonoidHom := by
          rw [htop, hX₀map]
        exact Subgroup.map_injective e.symm.injective h1
    have hX₀nc : ¬ IsMulCommutative X₀ := by
      intro h
      apply hXnc
      have e' : ↥X ≃* ↥X₀ := X.equivMapOfInjective e.toMonoidHom e.injective
      refine ⟨⟨fun a b => ?_⟩⟩
      apply e'.injective
      rw [map_mul, map_mul]
      exact IsMulCommutative.is_comm.comm _ _
    haveI : (A ⊔ B).Normal := hFnorm
    have hFX₀n : (X₀ ⊓ (A ⊔ B)).Normal := Subgroup.normal_inf_normal X₀ (A ⊔ B)
    rcases hFmin (X₀ ⊓ (A ⊔ B)) hFX₀n inf_le_right with h0 | htop
    · exfalso
      have hX₀A : X₀ ≤ Subgroup.centralizer (A : Set Q) := by
        rcases CFSG.LocalCores.component_normal_subgroup hAc hX₀n with hle | hc
        · exfalso
          have h1 : A ≤ X₀ ⊓ (A ⊔ B) := le_inf hle le_sup_left
          rw [h0] at h1
          exact hAnb (le_bot_iff.mp h1)
        · rw [Subgroup.commutator_comm] at hc
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
      have hX₀B : X₀ ≤ Subgroup.centralizer (B : Set Q) := by
        rcases CFSG.LocalCores.component_normal_subgroup hBc hX₀n with hle | hc
        · exfalso
          have h1 : B ≤ X₀ ⊓ (A ⊔ B) := le_inf hle le_sup_right
          rw [h0] at h1
          exact hBnb (le_bot_iff.mp h1)
        · rw [Subgroup.commutator_comm] at hc
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
      have hX₀zero : X₀ ≤ Subgroup.centralizer ((A ⊔ B : Subgroup Q) : Set Q) := by
        rw [Subgroup.le_centralizer_iff] at hX₀A hX₀B ⊢
        exact sup_le hX₀A hX₀B
      rw [hC] at hX₀zero
      exact hX₀ne (le_bot_iff.mp hX₀zero)
    · have hX₀eq : X₀ = A ⊔ B := by
        rcases hX₀min (A ⊔ B) hFnorm ((le_of_eq htop.symm).trans inf_le_left) with h | h
        · exfalso
          exact hAnb ((le_bot_iff).mp (le_sup_left.trans (le_of_eq h)))
        · exact h.symm
      have hL₀ : CFSG.Open.IsComponentOf (L.map e.toMonoidHom) X₀ :=
        CFSG.Goldschmidt.G310.isComponentOf_map_mulEquiv e hL
      have hL₀sub : (L.map e.toMonoidHom).IsSubnormal :=
        CFSG.Quasithin.A3.isSubnormal_of_subnormal hL₀.2.1
          (by rw [hX₀eq]; exact hFnorm.isSubnormal)
      have hcases := CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.a10_subnormal_direct
        hAs hAn hBs hBn hcomm hinf (hL₀.1.trans (le_of_eq hX₀eq)) hL₀sub
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL₀.2.2)
      have hLshape : IsL2 ↥(L.map e.toMonoidHom) m ∨
          IsSz ↥(L.map e.toMonoidHom) m := by
        rcases hcases with h | h
        · rw [h]; exact hshapeA
        · rw [h]; exact hshapeB
      have eL : ↥L ≃* ↥(L.map e.toMonoidHom) :=
        L.equivMapOfInjective e.toMonoidHom e.injective
      rcases hLshape with h | h
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eL.symm h)
      · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eL.symm h)
  ·
    exfalso
    have hquotY : IsPGroup 2 (Q ⧸ Y) := by
      have hker : A ⊔ B ≤ (QuotientGroup.mk' Y).ker := by
        rw [QuotientGroup.ker_mk']
        exact hFY
      have hsurj : Function.Surjective
          (QuotientGroup.lift (A ⊔ B) (QuotientGroup.mk' Y) hker) := by
        intro x
        obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Y x
        exact ⟨QuotientGroup.mk q, rfl⟩
      exact IsPGroup.of_surjective hquot (QuotientGroup.lift (A ⊔ B)
        (QuotientGroup.mk' Y) hker) hsurj
    have hX2 : IsPGroup 2 ↥X := IsPGroup.of_injective hquotY X.subtype X.subtype_injective
    have hcm := CFSG.Timmesfeld.Bridge.RootClosure.commute_of_minimal hX2 hXne hXmin
    exact hXnc ⟨⟨fun a b => Subtype.ext (hcm a a.2 b b.2)⟩⟩

theorem exists_mem_sylow_map_conj_eq_conjSubgroup {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : UC22.conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : UC22.conjClosure D.M L ≠ L) :
    ∃ t ∈ D.T, L.map (MulAut.conj t).toMonoidHom = CFSG.Quasithin.conjSubgroup L x :=
  (p42_swap_data hL hxM hXsup hne).2

theorem exists_bar2_map_of_le {H X : Subgroup G} (hXH : X ≤ H)
    (hpCore : pCoreOf 2 X = X ⊓ pCoreOf 2 H) :
    ∃ ψ : Bar2 X →* Bar2 H, Function.Injective ψ ∧
      ∀ (K : Subgroup G), K ≤ X → (imageBar2 X K).map ψ = imageBar2 H K := by
  classical
  let ψ₀ : ↥X →* Bar2 H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hXH)
  have hker : CFSG.pCore 2 ↥X ≤ ψ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (QuotientGroup.mk (Subgroup.inclusion hXH x) : Bar2 H) = 1
    rw [QuotientGroup.eq_one_iff, ← CFSG.openPCoreOf_subgroupOf 2 H]
    have hx' : ((x : ↥X) : G) ∈ pCoreOf 2 X := by
      have h1 : (x : ↥X) ∈ (pCoreOf 2 X).subgroupOf X := by
        rw [CFSG.openPCoreOf_subgroupOf]
        exact hx
      exact Subgroup.mem_subgroupOf.mp h1
    rw [hpCore] at hx'
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hx'.2)
  let ψ : Bar2 X →* Bar2 H := QuotientGroup.lift (CFSG.pCore 2 ↥X) ψ₀ hker
  have hψ_apply : ∀ x : ↥X, ψ (QuotientGroup.mk x) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.inclusion hXH x) := fun x => rfl
  have hψker : ψ.ker = ⊥ := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hz
      induction z using QuotientGroup.induction_on with
      | H x =>
        have hz' : ψ₀ x = 1 := hz
        change (QuotientGroup.mk (Subgroup.inclusion hXH x) : Bar2 H) = 1 at hz'
        rw [QuotientGroup.eq_one_iff, ← CFSG.openPCoreOf_subgroupOf 2 H] at hz'
        change (QuotientGroup.mk x : Bar2 X) = 1
        rw [QuotientGroup.eq_one_iff, ← CFSG.openPCoreOf_subgroupOf 2 X, hpCore]
        exact ⟨x.2, hz'⟩
    · intro hz
      rw [hz]
      exact map_one ψ
  refine ⟨ψ, (MonoidHom.ker_eq_bot_iff ψ).mp hψker, ?_⟩
  intro K hKX
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
    have hkK : ((k : ↥X) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    refine Subgroup.mem_map.mpr ⟨⟨(k : ↥X), hXH k.2⟩,
      Subgroup.mem_subgroupOf.mpr hkK, ?_⟩
    rw [← hky]
    change (QuotientGroup.mk (Subgroup.inclusion hXH k) : Bar2 H) =
      ψ (QuotientGroup.mk (k : ↥X))
    rw [hψ_apply]
    rfl
  · intro hz
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hz
    have hKX : (h : G) ∈ X := hKX (Subgroup.mem_subgroupOf.mp hh)
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk ⟨(h : G), hKX⟩, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨⟨(h : G), hKX⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hh), rfl⟩
    · rw [hψ_apply]
      rfl

theorem center_sup_eq_bot_of_simple {Q : Type} [Group Q] {A B : Subgroup Q}
    (hAs : IsSimpleGroup ↥A) (hAn : ¬ IsMulCommutative ↥A)
    (hBs : IsSimpleGroup ↥B) (hBn : ¬ IsMulCommutative ↥B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Subgroup.center ↥(A ⊔ B) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro z hz
  have hzc : ∀ n ∈ A ⊔ B, n * (z : Q) = (z : Q) * n := fun n hn =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨n, hn⟩)
  exact Subtype.ext
    (CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.a10t1_sub_center_sup
      hAs hAn hBs hBn hcomm z.2 hzc)

theorem hasComponentShapes_bar2_sup {D : Data G} {L : Subgroup G} {x : G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : UC22.conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : UC22.conjClosure D.M L ≠ L) {H : Subgroup G}
    (hH : H = UC22.conjClosure D.M L ⊔ D.T)
    (hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L)) :
    HasComponentShapes (Bar2 H) (S17.nOf L) := by
  classical
  subst hH
  set X : Subgroup G := UC22.conjClosure D.M L with hXdef
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hKdef
  have hXsup' : X = L ⊔ K := hXsup
  have hLX : L ≤ X := le_sup_left.trans (le_of_eq hXsup'.symm)
  have hKX : K ≤ X := le_sup_right.trans (le_of_eq hXsup'.symm)
  have hLH : L ≤ X ⊔ D.T := hLX.trans le_sup_left
  have hKH : K ≤ X ⊔ D.T := hKX.trans le_sup_left
  have hXM : X ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hL.1.le
  have hXnormM : D.M ≤ Subgroup.normalizer (X : Set G) :=
    (conjSetOf_subset_calC_conjClosure hL).2.1
  have hHnorm : X ⊔ D.T ≤ Subgroup.normalizer (X : Set G) :=
    (sup_le hXM D.sylowM.le).trans hXnormM
  have hXnH : (X.subgroupOf (X ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHnorm
  have hXsubH : CFSG.Open.IsSubnormal X (X ⊔ D.T) :=
    CFSG.Open.IsSubnormal.step le_sup_left hXnH (CFSG.Open.IsSubnormal.refl _)
  have hLXnorm : (L.subgroupOf X).Normal :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.component_normal_in_conjClosure hL
  have hLsubH : CFSG.Open.IsSubnormal L (X ⊔ D.T) :=
    CFSG.Open.IsSubnormal.step hLX hLXnorm hXsubH
  have hpCoreX : pCoreOf 2 X = X ⊓ pCoreOf 2 (X ⊔ D.T) :=
    pCoreOf_eq_inf_pCoreOf_of_isSubnormal hXsubH
  let A : Subgroup (Bar2 (X ⊔ D.T)) := imageBar2 (X ⊔ D.T) L
  let B : Subgroup (Bar2 (X ⊔ D.T)) := imageBar2 (X ⊔ D.T) K
  obtain ⟨eA⟩ := nonempty_bar2_image_mulEquiv_of_isSubnormal hLH hLsubH
  have hAsimple : IsSimpleGroup ↥A :=
    eA.isSimpleGroup_congr.mp (isSimpleGroup_of_isL2_or_isSz hL2)
  haveI := hAsimple
  have hAq : CFSG.Open.IsQuasisimple ↥A := CFSG.Open.IsQuasisimple.of_mulEquiv eA.symm hL.2.2
  have hAno : ¬ IsMulCommutative ↥A :=
    (show Group.IsPerfect ↥A from ⟨hAq.1⟩).not_isMulCommutative
  have hAne : A ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot A).mp inferInstance
  have hAsub : A.IsSubnormal := by
    have h1 : CFSG.Open.IsSubnormal (L.subgroupOf (X ⊔ D.T)) ⊤ :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hLH).mpr hLsubH
    have h2 : CFSG.Open.IsSubnormal ((L.subgroupOf (X ⊔ D.T)).map
        (piBar2 (X ⊔ D.T))) ⊤ :=
      CFSG.Quasithin.A3.subnormal_top_map (QuotientGroup.mk'_surjective _) h1
    exact CFSG.Open.IsSubnormal.top_iff.mp h2
  have hAcomp : CFSG.IsComponent A :=
    ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hAq, hAsub⟩
  obtain ⟨t, htT, htK⟩ := exists_mem_sylow_map_conj_eq_conjSubgroup hL hxM hXsup hne
  have htK' : L.map (MulAut.conj t).toMonoidHom = K := by
    rw [hKdef]; exact htK
  have htH : t ∈ X ⊔ D.T := le_sup_right (a := X) htT
  let q : Bar2 (X ⊔ D.T) := piBar2 (X ⊔ D.T) ⟨t, htH⟩
  have hBconj : B = A.map (MulAut.conj q).toMonoidHom := by
    have h := imageBar2_map_conj (H := X ⊔ D.T) (K := L) hLH htH
    show imageBar2 (X ⊔ D.T) K = (imageBar2 (X ⊔ D.T) L).map
      (MulAut.conj q).toMonoidHom
    rw [← htK']
    exact h.symm
  have eB : ↥A ≃* ↥B :=
    (A.equivMapOfInjective (MulAut.conj q).toMonoidHom
      (MulAut.conj q).injective).trans (MulEquiv.subgroupCongr hBconj.symm)
  have hBsimp : IsSimpleGroup ↥B := eB.symm.isSimpleGroup_congr.mpr hAsimple
  haveI := hBsimp
  have hBq : CFSG.Open.IsQuasisimple ↥B := CFSG.Open.IsQuasisimple.of_mulEquiv eB.symm hAq
  have hBno : ¬ IsMulCommutative ↥B :=
    (show Group.IsPerfect ↥B from ⟨hBq.1⟩).not_isMulCommutative
  have hBne : B ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot B).mp inferInstance
  have hBsub : B.IsSubnormal := by
    rw [hBconj]
    exact Subgroup.IsSubnormal.map (f := (MulAut.conj q).toMonoidHom)
      (MulAut.conj q).surjective hAsub
  have hBcomp : CFSG.IsComponent B :=
    ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hBq, hBsub⟩
  have hshapeA : IsL2 ↥A (S17.nOf L) ∨ IsSz ↥A (S17.nOf L) := by
    rcases hL2 with h | h
    · exact Or.inl (LieModel.of_mulEquiv eA h)
    · exact Or.inr (LieModel.of_mulEquiv eA h)
  have hshapeB : IsL2 ↥B (S17.nOf L) ∨ IsSz ↥B (S17.nOf L) := by
    rcases hshapeA with h | h
    · exact Or.inl (LieModel.of_mulEquiv eB h)
    · exact Or.inr (LieModel.of_mulEquiv eB h)
  set A' : Subgroup (Bar2 X) := imageBar2 X L with hA'def
  set B' : Subgroup (Bar2 X) := imageBar2 X K with hB'def
  have hLcX : L ∈ calC X :=
    (conjSetOf_subset_calC_conjClosure hL).2.2 L (self_mem_conjSetOf D.M L)
  have hKcX : K ∈ calC X :=
    (conjSetOf_subset_calC_conjClosure hL).2.2 K ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  obtain ⟨eA'⟩ := nonempty_bar2_image_mulEquiv_of_isSubnormal hLX hLcX.1
  have hA'simple : IsSimpleGroup ↥A' :=
    eA'.isSimpleGroup_congr.mp (isSimpleGroup_of_isL2_or_isSz hL2)
  have hA'q : CFSG.Open.IsQuasisimple ↥A' := CFSG.Open.IsQuasisimple.of_mulEquiv eA'.symm hL.2.2
  have hA'no : ¬ IsMulCommutative ↥A' :=
    (show Group.IsPerfect ↥A' from ⟨hA'q.1⟩).not_isMulCommutative
  have hLKne : L ≠ K := by
    rw [hKdef]
    exact ((conjSubgroup_mem_calC_and_ne hL hxM hXsup hne).2).symm
  have hcomm' : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a :=
    uc22p22l_barImage_commute hLcX hKcX hLKne
  have hcommut' : ⁅A', B'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb => (hcomm' a ha b hb).symm)
  have hinf' : A' ⊓ B' = ⊥ := by
    haveI : IsSimpleGroup ↥A' := hA'simple
    have hnorm : A' ≤ Subgroup.normalizer ((A' ⊓ B' : Subgroup (Bar2 X)) : Set (Bar2 X)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.mp hz
        refine Subgroup.mem_inf.mpr ⟨A'.mul_mem (A'.mul_mem ha hzA) (A'.inv_mem ha), ?_⟩
        have h1 : a * z * a⁻¹ = z := by rw [hcomm' a ha z hzB]; group
        rwa [h1]
      · intro hz
        obtain ⟨hyA, hyB⟩ := Subgroup.mem_inf.mp hz
        have h1 : z = a⁻¹ * (a * z * a⁻¹) * a := by group
        rw [h1]
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact A'.mul_mem (A'.mul_mem (A'.inv_mem ha) hyA) ha
        · have h2 : a⁻¹ * (a * z * a⁻¹) = (a * z * a⁻¹) * a⁻¹ :=
            hcomm' a⁻¹ (A'.inv_mem ha) _ hyB
          have h3 : a⁻¹ * (a * z * a⁻¹) * a = a * z * a⁻¹ := by
            rw [h2]; group
          rw [h3]; exact hyB
    have hNsub : ((A' ⊓ B').subgroupOf A').Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
    haveI := hNsub
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A' ⊓ B').subgroupOf A') with h0 | htop
    · have hd : (A' ⊓ B') ⊓ A' = ⊥ :=
        disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp h0)
      rwa [inf_eq_left.mpr inf_le_left] at hd
    · exfalso
      have hAle : A' ≤ B' := ((Subgroup.subgroupOf_eq_top).mp htop).trans inf_le_right
      haveI : IsMulCommutative ↥A' := by
        refine ⟨⟨fun u v => ?_⟩⟩
        exact Subtype.ext (hcomm' (u : Bar2 X) u.2 (v : Bar2 X) (hAle v.2))
      exact hA'no this
  obtain ⟨ψ, hψinj, hψimg⟩ := exists_bar2_map_of_le (H := X ⊔ D.T) (X := X) le_sup_left hpCoreX
  have hAψ : A = A'.map ψ := (hψimg L hLX).symm
  have hBψ : B = B'.map ψ := (hψimg K hKX).symm
  have hinfAB : A ⊓ B = ⊥ := by
    rw [hAψ, hBψ, ← Subgroup.map_inf A' B' ψ hψinj, hinf', Subgroup.map_bot]
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    rw [hAψ] at ha
    rw [hBψ] at hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hcomm' a' ha' b' hb']
  have hF_eq : A ⊔ B = imageBar2 (X ⊔ D.T) X := by
    show imageBar2 (X ⊔ D.T) L ⊔ imageBar2 (X ⊔ D.T) K = imageBar2 (X ⊔ D.T) X
    rw [imageBar2, imageBar2, imageBar2, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup hLH hKH, ← hXsup']
  have hFnorm : (A ⊔ B).Normal := by
    rw [hF_eq, imageBar2]
    exact hXnH.map (piBar2 (X ⊔ D.T)) (QuotientGroup.mk'_surjective _)
  have hcenter : Subgroup.center ↥(A ⊔ B) = ⊥ :=
    center_sup_eq_bot_of_simple hAsimple hAno hBsimp hBno hcommAB
  have hT2 : IsPGroup 2 (imageBar2 (X ⊔ D.T) D.T) := by
    have h1 : IsPGroup 2 (D.T.subgroupOf (X ⊔ D.T)) :=
      D.sylowM.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
    exact IsPGroup.map h1 (piBar2 (X ⊔ D.T))
  have hsupFT : A ⊔ B ⊔ imageBar2 (X ⊔ D.T) D.T = ⊤ := by
    rw [hF_eq, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hquotF : IsPGroup 2 (Bar2 (X ⊔ D.T) ⧸ (A ⊔ B)) := by
    haveI : (A ⊔ B).Normal := hFnorm
    haveI : ((A ⊔ B).subgroupOf (⊤ : Subgroup (Bar2 (X ⊔ D.T)))).Normal :=
      hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 ((⊤ : Subgroup (Bar2 (X ⊔ D.T))) ⧸
        (A ⊔ B).subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2)
        (G := Bar2 (X ⊔ D.T)) (L := (A ⊔ B)) (Q := imageBar2 (X ⊔ D.T) D.T) (K := ⊤)
        hT2 le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hsupFT
    have he : ((A ⊔ B).subgroupOf (⊤ : Subgroup (Bar2 (X ⊔ D.T)))).map
        (Subgroup.topEquiv (G := Bar2 (X ⊔ D.T))).toMonoidHom = A ⊔ B := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr ((A ⊔ B).subgroupOf ⊤) (A ⊔ B) Subgroup.topEquiv he)
  have hC : Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
      Set (Bar2 (X ⊔ D.T))) = ⊥ := by
    have hCnormal : (Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
        Set (Bar2 (X ⊔ D.T)))).Normal := Subgroup.normal_centralizer
    have hCinf : Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
        Set (Bar2 (X ⊔ D.T))) ⊓ (A ⊔ B) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro z hz
      obtain ⟨hzC, hzF⟩ := Subgroup.mem_inf.mp hz
      have hzZ : (⟨z, hzF⟩ : ↥(A ⊔ B)) ∈ Subgroup.center ↥(A ⊔ B) := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hzC (y : Bar2 (X ⊔ D.T)) y.2
      rw [hcenter] at hzZ
      have hzbot : (⟨z, hzF⟩ : ↥(A ⊔ B)) = 1 := by simpa using hzZ
      simpa using congrArg Subtype.val hzbot
    have hC2 : IsPGroup 2 (Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
        Set (Bar2 (X ⊔ D.T)))) := by
      have hinj : Function.Injective ((QuotientGroup.mk' (A ⊔ B)).comp
          (Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
            Set (Bar2 (X ⊔ D.T)))).subtype) := by
        intro u v huv
        have h1 : ((u : Bar2 (X ⊔ D.T))⁻¹ * (v : Bar2 (X ⊔ D.T))) ∈ (A ⊔ B) := by
          have h2 : QuotientGroup.mk' (A ⊔ B)
              ((u : Bar2 (X ⊔ D.T))⁻¹ * (v : Bar2 (X ⊔ D.T))) = 1 := by
            rw [map_mul, map_inv]
            have huv' : (QuotientGroup.mk' (A ⊔ B) (u : Bar2 (X ⊔ D.T))) =
                QuotientGroup.mk' (A ⊔ B) (v : Bar2 (X ⊔ D.T)) := huv
            rw [huv', inv_mul_cancel]
          exact (QuotientGroup.eq_one_iff _).mp h2
        have h3 : ((u : Bar2 (X ⊔ D.T))⁻¹ * (v : Bar2 (X ⊔ D.T))) ∈
            Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
              Set (Bar2 (X ⊔ D.T))) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ u.2) v.2
        have h4 : ((u : Bar2 (X ⊔ D.T))⁻¹ * (v : Bar2 (X ⊔ D.T))) = 1 := by
          have h5 : ((u : Bar2 (X ⊔ D.T))⁻¹ * (v : Bar2 (X ⊔ D.T))) ∈
              (⊥ : Subgroup (Bar2 (X ⊔ D.T))) := by
            rw [← hCinf]; exact Subgroup.mem_inf.mpr ⟨h3, h1⟩
          simpa using h5
        exact Subtype.ext (inv_mul_eq_one.mp h4)
      exact IsPGroup.of_injective hquotF _ hinj
    have hCO2 : Subgroup.centralizer ((A ⊔ B : Subgroup (Bar2 (X ⊔ D.T))) :
        Set (Bar2 (X ⊔ D.T))) ≤ pCoreOf 2 (⊤ : Subgroup (Bar2 (X ⊔ D.T))) :=
      CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.le_pCoreOf_of_normalized le_top
        (fun k _ a ha => hCnormal.conj_mem a ha k) hC2
    have hO2 : pCoreOf 2 (⊤ : Subgroup (Bar2 (X ⊔ D.T))) = ⊥ := by
      rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot (X ⊔ D.T)]
    rw [hO2] at hCO2
    exact le_bot_iff.mp hCO2
  have hFmin : ∀ N : Subgroup (Bar2 (X ⊔ D.T)), N.Normal → N ≤ A ⊔ B → N = ⊥ ∨ N = A ⊔ B := by
    intro N hNn hNle
    rcases CFSG.LocalCores.component_normal_subgroup hAcomp hNn with hAN | hAcN
    · right
      have hBN : B ≤ N := by
        rw [hBconj]
        calc (A.map (MulAut.conj q).toMonoidHom) ≤ N.map (MulAut.conj q).toMonoidHom :=
              Subgroup.map_mono hAN
          _ = N := CFSG.Goldschmidt.G310.map_conj_eq_of_normal hNn q
      exact le_antisymm hNle (sup_le hAN hBN)
    · rcases CFSG.LocalCores.component_normal_subgroup hBcomp hNn with hBN | hBcN
      · right
        have hAN : A ≤ N := by
          have h1 : B.map (MulAut.conj q⁻¹).toMonoidHom ≤ N.map
              (MulAut.conj q⁻¹).toMonoidHom := Subgroup.map_mono hBN
          rw [show B.map (MulAut.conj q⁻¹).toMonoidHom = A by
            calc B.map (MulAut.conj q⁻¹).toMonoidHom
                = (A.map (MulAut.conj q).toMonoidHom).map
                    (MulAut.conj q⁻¹).toMonoidHom := by rw [hBconj]
              _ = A := by
                  rw [uc22p22d_map_conj_map_conj, inv_mul_cancel]
                  ext y
                  simp [MulAut.conj_apply],
            CFSG.Goldschmidt.G310.map_conj_eq_of_normal hNn q⁻¹] at h1
          exact h1
        exact le_antisymm hNle (sup_le hAN hBN)
      · left
        have h1 : N ≤ Subgroup.centralizer (A : Set (Bar2 (X ⊔ D.T))) := by
          rw [Subgroup.commutator_comm] at hAcN
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAcN
        have h2 : N ≤ Subgroup.centralizer (B : Set (Bar2 (X ⊔ D.T))) := by
          rw [Subgroup.commutator_comm] at hBcN
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcN
        have h3 : N ≤ Subgroup.centralizer ((A ⊔ B :
            Subgroup (Bar2 (X ⊔ D.T))) : Set (Bar2 (X ⊔ D.T))) := by
          rw [Subgroup.le_centralizer_iff] at h1 h2 ⊢
          exact sup_le h1 h2
        rw [hC] at h3
        exact le_bot_iff.mp h3
  exact shape_of_two_components hAcomp hBcomp hAsimple hAno hBsimp hBno hAne hBne hcommAB
    hinfAB hFnorm hFmin hC hquotF hshapeA hshapeB

theorem r18_7b_of_ne_bot_XT_diag'
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (hV₀ : V₀ ≠ ⊥) (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h43c : W3Lem45_2Chief) (hK : K_L2SzAutRank) (h1742 : S17.R17_42At D V₀ V)
    (hXne : UC22.conjClosure D.M L ≠ L) :
    R18_7bAt D V₀ V p L h := by
  obtain ⟨n, x, hxM, hXsup, -, hshapen, -⟩ :=
    S17.p42_alt2_of_ne h1742 h.hp h.hL.1 hXne
  have hL2 : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L) := by
    rcases hshapen with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact Or.inl (by rwa [S17.nOf_eq_of_isL2 h2])
    · exact Or.inr (by rwa [S17.nOf_eq_of_isSz h2])
  have hgen := orbitClosure_imageBar2_sup_imageBar2_eq_top
    (H := UC22.conjClosure D.M L ⊔ D.T) h.hL.1 hxM hXsup hXne rfl
  have hshapes := hasComponentShapes_bar2_sup h.hL.1 hxM hXsup hXne rfl hL2
  have hshapesTop : HasComponentShapes (↥(⊤ : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T))))
      (S17.nOf L) :=
    hasComponentShapes_of_mulEquiv Subgroup.topEquiv.symm hshapes
  have hcf : ∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T' := by
    intro T' hT'
    exact compFactorAutInF_of_hasComponentShapes hT'.isPGroup hshapesTop hK
  exact r18_7b_of_ne_bot_XT_diag_of_inputs h hx h61 h127 h1114 h162 hTor h1482 h126 hSg hV₀ hX1
    h17_66_1 h18_4 h43c (H := UC22.conjClosure D.M L ⊔ D.T) rfl hL2 hgen hcf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
