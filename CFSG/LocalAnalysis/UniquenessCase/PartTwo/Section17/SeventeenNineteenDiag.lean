module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J1A5GenHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiagR42
public import CFSG.GroupTheory.ComponentDirectProduct
public import CFSG.Quasithin.Background.GoldschmidtE23Blocks
public import CFSG.GroupTheory.OrbitClosureSubgroupOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement
open CFSG.GroupTheory (orbitClosure_subgroupOf_of_le eq_of_isComponentOf_sup_of_direct)

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_19_A5Members (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G), Ctx17_17 D V₀ V L → IsJ1 (Bar2 L) →
    ∀ (A : Subgroup (Bar2 L)),
      IsAlt ↥A 5 →
        (∀ s ∈ (CFSG.GroupTheory.conjModPCore 2 L
            (D.T ⊓ Subgroup.normalizer (L : Set G)) inf_le_right).range,
          A.map s.toMonoidHom = A) →
        ¬ D.T ≤ Subgroup.normalizer (L : Set G) →
        ∃ K : Subgroup (Bar2 (memberDelta D L A)),
          CFSG.IsComponent K ∧
            (orbitClosure K (imageBar2 (memberDelta D L A) D.T) ⊔
              imageBar2 (memberDelta D L A) D.T = ⊤) ∧
            HasComponentShapes (Bar2 (memberDelta D L A)) 2

theorem pCoreOf_eq_inf_pCoreOf_of_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) :
    CFSG.Open.pCoreOf 2 L = L ⊓ CFSG.Open.pCoreOf 2 M :=
  pCoreOf_eq_inf_pCoreOf_of_isSubnormal hL.1

theorem le_normalizer_perfDelta_of_le_normalizer {L M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (L : Set G)) (A : Subgroup (Bar2 L))
    (hA : ∀ s ∈ (CFSG.GroupTheory.conjModPCore 2 L M hM).range, A.map s.toMonoidHom = A) :
    M ≤ Subgroup.normalizer (perfDelta L A : Set G) := by
  intro m hm
  have hP : m ∈ Subgroup.normalizer (preDelta L A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact preDelta_conj_eq L M hM A (fun m => hA _ ⟨m, rfl⟩) ⟨m, hm⟩
  exact CFSG.BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
    (preDelta L A) (CFSG.perfectResidual ↥(preDelta L A)) hP

theorem eq_iSup_perfDelta_sup_pCore (L : Subgroup G) {ι : Type*} (Δ : Finset ι)
    (A : ι → Subgroup (Bar2 L)) (hAlt : ∀ i ∈ Δ, IsAlt ↥(A i) 5)
    (hgen : (⨆ i ∈ Δ, A i) = ⊤) :
    (⨆ i ∈ Δ, perfDelta L (A i)) ⊔ CFSG.Open.pCoreOf 2 L = L := by
  have hmap := perfDelta_map_iSup_eq_top L Δ A hAlt hgen
  have hle : (⨆ i ∈ Δ, perfDelta L (A i)) ≤ L :=
    iSup₂_le fun i _ => perfDelta_le L (A i)
  have hsup : ((⨆ i ∈ Δ, perfDelta L (A i)).subgroupOf L) ⊔ CFSG.pCore 2 ↥L = ⊤ := by
    have h := Subgroup.comap_map_eq (S18.piBar2 L)
      ((⨆ i ∈ Δ, perfDelta L (A i)).subgroupOf L)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have := congrArg (Subgroup.map L.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top,
    Subgroup.range_subtype, ← CFSG.openPCoreOf_eq_map_pCore] at this
  exact this

theorem L_le_iSup_perfDelta_sup_T (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    {ι : Type*} (Δ : Finset ι) (A : ι → Subgroup (Bar2 L))
    (hAlt : ∀ i ∈ Δ, IsAlt ↥(A i) 5) (hgen : (⨆ i ∈ Δ, A i) = ⊤) :
    L ≤ (⨆ i ∈ Δ, perfDelta L (A i)) ⊔ D.T := by
  have hTsyl : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hO2M : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsyl
  have hO2L : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 D.M := by
    rw [pCoreOf_eq_inf_pCoreOf_of_mem_calC hL]
    exact inf_le_right
  calc L = (⨆ i ∈ Δ, perfDelta L (A i)) ⊔ CFSG.Open.pCoreOf 2 L :=
        (eq_iSup_perfDelta_sup_pCore L Δ A hAlt hgen).symm
    _ ≤ (⨆ i ∈ Δ, perfDelta L (A i)) ⊔ D.T := sup_le_sup_left (hO2L.trans hO2M) _

theorem imageBar2_orbitClosure_sup_eq_top {H Q T : Subgroup G} (hQH : Q ≤ H) (hTH : T ≤ H)
    (hH : H = Q ⊔ T) :
    orbitClosure (imageBar2 H Q) (imageBar2 H T) ⊔ imageBar2 H T = ⊤ := by
  have hQt : ∀ t ∈ T, Q.map (MulAut.conj t).toMonoidHom ≤ H := by
    intro t ht x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    exact H.mul_mem (H.mul_mem (hTH ht) (hQH hq)) (H.inv_mem (hTH ht))
  have hFH : orbitClosure Q T ≤ H := orbitClosure_le hQt
  have hmap : imageBar2 H (orbitClosure Q T) =
      orbitClosure (imageBar2 H Q) (imageBar2 H T) := by
    rw [imageBar2, orbitClosure_subgroupOf_of_le hTH hQt]
    exact (map_orbitClosure (piBar2 H) (Q.subgroupOf H) (T.subgroupOf H)).symm
  have hH' : H = orbitClosure Q T ⊔ T := by
    refine le_antisymm ?_ ?_
    · rw [hH]
      exact sup_le ((le_orbitClosure Q T).trans le_sup_left) le_sup_right
    · exact sup_le hFH hTH
  have hsup : imageBar2 H (orbitClosure Q T ⊔ T) =
      imageBar2 H (orbitClosure Q T) ⊔ imageBar2 H T :=
    imageBar2_sup hFH hTH
  calc orbitClosure (imageBar2 H Q) (imageBar2 H T) ⊔ imageBar2 H T
      = imageBar2 H (orbitClosure Q T) ⊔ imageBar2 H T := by rw [hmap]
    _ = imageBar2 H (orbitClosure Q T ⊔ T) := hsup.symm
    _ = imageBar2 H H := by rw [hH']
    _ = ⊤ := imageBar2_self H

theorem orbitClosure_imageBar2_perfDelta_sup_eq_top (D : Data G) {L : Subgroup G}
    (A : Subgroup (Bar2 L)) :
    orbitClosure (imageBar2 (memberDelta D L A) (perfDelta L A))
        (imageBar2 (memberDelta D L A) D.T) ⊔ imageBar2 (memberDelta D L A) D.T = ⊤ :=
  imageBar2_orbitClosure_sup_eq_top le_sup_left le_sup_right rfl


theorem hasComponentShapes_of_normal_direct {Q : Type} [Group Q] [Finite Q]
    {N : Subgroup Q} (hN : N.Normal) (hquot : IsPGroup 2 (Q ⧸ N))
    (𝒜 : Finset (Subgroup Q)) (hAle : ∀ A ∈ 𝒜, A ≤ N)
    (hAn : ∀ A ∈ 𝒜, (A.subgroupOf N).Normal)
    (hAs : ∀ A ∈ 𝒜, IsSimpleGroup ↥A)
    (hAnab : ∀ A ∈ 𝒜, ¬ IsMulCommutative ↥A)
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hsup : 𝒜.sup id = N)
    (hshape : ∀ A ∈ 𝒜, IsL2 ↥A 2 ∨ IsSz ↥A 2) :
    HasComponentShapes Q 2 := by
  classical
  intro Y hY X hXn hXne hXmin hXnc L hL
  have := hY
  let π : Q →* Q ⧸ Y := QuotientGroup.mk' Y
  let Nbar : Subgroup (Q ⧸ Y) := N.map π
  have hNbar : Nbar.Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have := hNbar
  have hXcomm : ⁅X, X⁆ = X := by
    have : X.Normal := hXn
    have hle : ⁅X, X⁆ ≤ X := Subgroup.commutator_le_left X X
    have hnorm : (⁅X, X⁆).Normal := Subgroup.commutator_normal X X
    rcases hXmin ⁅X, X⁆ hnorm hle with h | h
    · exfalso
      apply hXnc
      rw [isMulCommutative_iff]
      intro u v
      have hcent : X ≤ Subgroup.centralizer (X : Set (Q ⧸ Y)) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h
      have huv : v * (u : Q ⧸ Y) = (u : Q ⧸ Y) * v :=
        Subgroup.mem_centralizer_iff.mp (hcent u.2) v v.2
      exact Subtype.ext huv.symm
    · exact h
  have hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXcomm
  have hYbot : Subgroup.map π Y = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro y hy
    change (QuotientGroup.mk' Y) y = 1
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have hquot2 : IsPGroup 2 ((Q ⧸ Y) ⧸ Nbar) := by
    have hmapM : Subgroup.map π (N ⊔ Y) = Nbar := by
      rw [Subgroup.map_sup, hYbot, sup_bot_eq]
    let hle : N ≤ Subgroup.comap (MonoidHom.id Q) (N ⊔ Y) := fun x hx =>
      Subgroup.mem_comap.mpr (Subgroup.mem_sup_left hx)
    let hproj : Q ⧸ N →* Q ⧸ (N ⊔ Y) :=
      QuotientGroup.map N (N ⊔ Y) (MonoidHom.id Q) hle
    have hproj_apply : ∀ x : Q, hproj (QuotientGroup.mk' N x) =
        QuotientGroup.mk' (N ⊔ Y) x := by
      intro x
      show QuotientGroup.map N (N ⊔ Y) (MonoidHom.id Q) hle
        (QuotientGroup.mk' N x) = QuotientGroup.mk' (N ⊔ Y) x
      rw [QuotientGroup.map_mk']
      rfl
    have hproj_surj : Function.Surjective hproj := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N ⊔ Y) z
      exact ⟨QuotientGroup.mk' N x, hproj_apply x⟩
    have h2 : IsPGroup 2 (Q ⧸ (N ⊔ Y)) := IsPGroup.of_surjective hquot hproj hproj_surj
    have e := QuotientGroup.quotientQuotientEquivQuotient (G := Q) Y (N ⊔ Y) le_sup_right
    have e2 : ((Q ⧸ Y) ⧸ Nbar) ≃* Q ⧸ (N ⊔ Y) :=
      (QuotientGroup.quotientMulEquivOfEq hmapM).symm.trans e
    exact IsPGroup.of_equiv h2 e2.symm
  have hXle : X ≤ Nbar := by
    let ψ : ↥X →* ((Q ⧸ Y) ⧸ Nbar) := (QuotientGroup.mk' Nbar).comp X.subtype
    have hψrange : ψ.range = X.map (QuotientGroup.mk' Nbar) := by
      rw [show ψ = (QuotientGroup.mk' Nbar).comp X.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype]
    have h2top : IsPGroup 2 ↥(⊤ : Subgroup ((Q ⧸ Y) ⧸ Nbar)) :=
      IsPGroup.of_equiv hquot2
        (Subgroup.topEquiv (G := (Q ⧸ Y) ⧸ Nbar)).symm
    have h2range : IsPGroup 2 ↥ψ.range := h2top.to_le le_top
    have hperf : Group.IsPerfect ↥ψ.range := by
      rw [hψrange]
      exact Group.IsPerfect.map (H := X) (QuotientGroup.mk' Nbar)
    have : Group.IsPerfect ↥ψ.range := hperf
    have : Group.IsNilpotent ↥ψ.range := h2range.isNilpotent
    have hbot : ψ.range = ⊥ := by
      by_contra hne
      have : Nontrivial ↥ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable ↥ψ.range inferInstance
    have hmapbot : X.map (QuotientGroup.mk' Nbar) = ⊥ := by
      rw [← hψrange]
      exact hbot
    have hker : X ≤ (QuotientGroup.mk' Nbar).ker := (Subgroup.map_eq_bot_iff X).mp hmapbot
    rwa [QuotientGroup.ker_mk'] at hker
  have hLcomp : CFSG.Open.IsComponentOf L Nbar := by
    refine ⟨hL.1.trans hXle, ?_, hL.2.2⟩
    exact CFSG.Open.IsSubnormal.trans hL.2.1
      (CFSG.Open.IsSubnormal.step hXle (hXn.subgroupOf Nbar)
        (CFSG.Open.IsSubnormal.refl Nbar))
  let 𝒜' : Finset (Subgroup Q) := 𝒜.filter (fun A => ¬ A ≤ Y)
  let ℬ : Finset (Subgroup (Q ⧸ Y)) := 𝒜'.image (fun A => A.map π)
  have hBmem : ∀ B ∈ ℬ, ∃ A ∈ 𝒜, ¬ A ≤ Y ∧ B = A.map π := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    rw [Finset.mem_filter] at hA
    exact ⟨A, hA.1, hA.2, rfl⟩
  have hAleB : ∀ B ∈ ℬ, B ≤ Nbar := by
    intro B hB
    obtain ⟨A, hA, -, rfl⟩ := hBmem B hB
    exact Subgroup.map_mono (f := π) (hAle A hA)
  have hAnB : ∀ B ∈ ℬ, (B.subgroupOf Nbar).Normal := by
    intro B hB
    obtain ⟨A, hA, -, rfl⟩ := hBmem B hB
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (f := π) (hAle A hA))]
    intro h k hh hk
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨m * a * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.normal_subgroupOf_iff (hAle A hA)).mp (hAn A hA) a m ha hm
  have hinf_bot : ∀ A ∈ 𝒜, ¬ A ≤ Y → A ⊓ Y = ⊥ := by
    intro A hA hAY
    have : IsSimpleGroup ↥A := hAs A hA
    have hnorm : ((A ⊓ Y).subgroupOf A).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro h k hh hk
      exact Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hk hh.1) (A.inv_mem hk),
        hY.conj_mem h hh.2 k⟩
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ Y).subgroupOf A) with h | h
    · have hd : Disjoint (A ⊓ Y) A := Subgroup.subgroupOf_eq_bot.mp h
      have h1 := disjoint_iff.mp hd
      rwa [inf_of_le_left inf_le_left] at h1
    · exact absurd ((Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right) hAY
  have hiso : ∀ B ∈ ℬ, ∃ A ∈ 𝒜, ¬ A ≤ Y ∧ B = A.map π ∧ Nonempty (↥A ≃* ↥B) := by
    intro B hB
    obtain ⟨A, hA, hAY, rfl⟩ := hBmem B hB
    refine ⟨A, hA, hAY, rfl, ?_⟩
    have hinf : A ⊓ Y = ⊥ := hinf_bot A hA hAY
    let f : ↥A →* ↥(A.map π) :=
      (π.comp A.subtype).codRestrict _ fun a => Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩
    have hfinj : Function.Injective f := by
      intro x y hxy
      have h3 : π (x : Q) = π (y : Q) := congrArg Subtype.val hxy
      have h1 : π ((x : Q)⁻¹ * (y : Q)) = 1 := by
        rw [map_mul, map_inv, h3, inv_mul_cancel]
      have h2 : (x : Q)⁻¹ * (y : Q) ∈ Y := (QuotientGroup.eq_one_iff _).mp h1
      have h4 : (x : Q)⁻¹ * (y : Q) ∈ A := A.mul_mem (A.inv_mem x.2) y.2
      have h5 : (x : Q)⁻¹ * (y : Q) = 1 := by
        have h6 := Subgroup.mem_inf.mpr ⟨h4, h2⟩
        rw [hinf] at h6
        exact Subgroup.mem_bot.mp h6
      refine Subtype.ext ?_
      have h7 : (y : Q) = (x : Q) := by
        calc (y : Q) = ((x : Q) * (x : Q)⁻¹) * (y : Q) := by group
          _ = (x : Q) * ((x : Q)⁻¹ * (y : Q)) := by group
          _ = (x : Q) * 1 := by rw [h5]
          _ = (x : Q) := mul_one _
      exact h7.symm
    have hfsurj : Function.Surjective f := by
      intro b
      obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp b.2
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
    exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩⟩
  have hAsB : ∀ B ∈ ℬ, IsSimpleGroup ↥B := by
    intro B hB
    obtain ⟨A, hA, -, -, ⟨e⟩⟩ := hiso B hB
    exact e.isSimpleGroup_congr.mp (hAs A hA)
  have hAnabB : ∀ B ∈ ℬ, ¬ IsMulCommutative ↥B := by
    intro B hB
    obtain ⟨A, hA, -, -, ⟨e⟩⟩ := hiso B hB
    exact fun h => hAnab A hA ((isMulCommutative_congr e).mpr h)
  have hBshape : ∀ B ∈ ℬ, IsL2 ↥B 2 ∨ IsSz ↥B 2 := by
    intro B hB
    obtain ⟨A, hA, -, -, ⟨e⟩⟩ := hiso B hB
    rcases hshape A hA with h | h
    · exact Or.inl (LieModel.of_mulEquiv e h)
    · exact Or.inr (LieModel.of_mulEquiv e h)
  have hcommB : ∀ B ∈ ℬ, ∀ C ∈ ℬ, B ≠ C →
      ∀ a ∈ B, ∀ b ∈ C, Commute a b := by
    intro B hB C hC hne a ha b hb
    obtain ⟨A, hA, -, rfl⟩ := hBmem B hB
    obtain ⟨A₂, hA₂, -, rfl⟩ := hBmem C hC
    have hne' : A ≠ A₂ := by
      rintro rfl
      exact hne rfl
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    show π a' * π b' = π b' * π a'
    rw [← map_mul, ← map_mul]
    exact congrArg π (hcomm A hA A₂ hA₂ hne' a' ha' b' hb').eq
  have hmap_sup : 𝒜'.sup (fun A => A.map π) = Subgroup.map π (𝒜'.sup id) := by
    rw [Finset.sup_eq_iSup, Finset.sup_eq_iSup]
    rw [Subgroup.map_iSup]
    simp only [Subgroup.map_iSup]
    rfl
  have hsupB : ℬ.sup id = Nbar := by
    have hNbar_eq : Nbar = Subgroup.map π (𝒜'.sup id) := by
      refine le_antisymm ?_ ?_
      ·
        have hle : N ≤ Y ⊔ 𝒜'.sup id := by
          rw [← hsup]
          refine Finset.sup_le fun A hA => ?_
          by_cases hAY : A ≤ Y
          · exact hAY.trans le_sup_left
          · exact (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hA, hAY⟩)).trans
              le_sup_right
        have hmap := Subgroup.map_mono (f := π) hle
        rw [Subgroup.map_sup, hYbot, bot_sup_eq] at hmap
        exact hmap
      · exact Subgroup.map_mono (f := π) (Finset.sup_le fun A hA =>
          hAle A (Finset.mem_filter.mp hA).1)
    rw [hNbar_eq, ← hmap_sup]
    rw [show ℬ = 𝒜'.image (fun A => A.map π) from rfl, Finset.sup_image]
    rfl
  obtain ⟨B, hB, hLB⟩ := eq_of_isComponentOf_sup_of_direct ℬ hAleB hAnB hAsB hAnabB hcommB
    hsupB L hLcomp
  exact hLB ▸ hBshape B hB


theorem preDeltaMap_ker_eq_pCore (L : Subgroup G) (A : Subgroup (Bar2 L)) :
    (preDeltaMap L A).ker =
      (CFSG.Open.pCoreOf 2 L).subgroupOf (preDelta L A) := by
  rw [preDeltaMap_ker L A]
  ext z
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact (CFSG.mem_openPCoreOf_iff (Subgroup.inclusion (preDelta_le L A) z)).symm

theorem preDelta_eq_perfDelta_sup_pCore (L : Subgroup G) (A : Subgroup (Bar2 L))
    (hAlt : IsAlt ↥A 5) :
    preDelta L A = perfDelta L A ⊔ CFSG.Open.pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperfA : Group.IsPerfect ↥A := by
    obtain ⟨eA⟩ := hAlt
    have : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
      ⟨CFSG.GroupTheory.AlternatingFive.commutator_eq_top⟩
    exact Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  have : Group.IsPerfect ↥A := hperfA
  set P := preDelta L A with hPdef
  set Q := perfDelta L A with hQdef
  set O := CFSG.Open.pCoreOf 2 L with hOdef
  have hOleP : O ≤ P := preDelta_contains_pCore L A
  have hQleP : Q ≤ P := perfDelta_le_pre L A
  let f : ↥P →* ↥A := (preDeltaMap L A).codRestrict A fun z => by
    have h : preDeltaMap L A z ∈ (preDeltaMap L A).range := ⟨z, rfl⟩
    rwa [preDeltaMap_range L A] at h
  have hfsurj : Function.Surjective f := by
    intro a
    have ha : (a : Bar2 L) ∈ (preDeltaMap L A).range := by
      rw [preDeltaMap_range L A]
      exact a.2
    obtain ⟨z, hz⟩ := ha
    exact ⟨z, Subtype.ext hz⟩
  have hkerO : ∀ z : ↥P, f z = 1 ↔ z ∈ O.subgroupOf P := by
    intro z
    constructor
    · intro hz
      have hz1 : preDeltaMap L A z = 1 := congrArg Subtype.val hz
      have hz2 : z ∈ (preDeltaMap L A).ker := MonoidHom.mem_ker.mpr hz1
      rw [preDeltaMap_ker_eq_pCore L A] at hz2
      exact hz2
    · intro hz
      apply Subtype.ext
      change preDeltaMap L A z = 1
      rw [← MonoidHom.mem_ker, preDeltaMap_ker_eq_pCore L A]
      exact hz
  have hres' :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
      f hfsurj
  have hres : Subgroup.map f (CFSG.perfectResidual ↥P) = ⊤ := hres'
  refine le_antisymm ?_ (sup_le hQleP hOleP)
  intro x hxP
  have hxbar : f ⟨x, hxP⟩ ∈ Subgroup.map f (CFSG.perfectResidual ↥P) := by
    rw [hres]
    exact Subgroup.mem_top _
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxbar
  have hqQ : ((q : ↥P) : G) ∈ Q := ⟨q, hq, rfl⟩
  have hqx1 : f (q⁻¹ * ⟨x, hxP⟩) = 1 := by
    rw [map_mul, map_inv, hqx, inv_mul_cancel]
  have hmemO : (q⁻¹ * ⟨x, hxP⟩ : ↥P) ∈ O.subgroupOf P := (hkerO _).mp hqx1
  have hxO : (((q⁻¹ * ⟨x, hxP⟩ : ↥P)) : G) ∈ O := Subgroup.mem_subgroupOf.mp hmemO
  have hxeq : x = ((q * (q⁻¹ * ⟨x, hxP⟩) : ↥P) : G) := by simp
  rw [hxeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqQ) (Subgroup.mem_sup_right hxO)

theorem pCoreOf_le_pCoreOf_memberDelta (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (A : Subgroup (Bar2 L)) :
    CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 (memberDelta D L A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hO2M_le_T : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsyl
  have hO2L_le_O2M : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 D.M := by
    rw [pCoreOf_eq_inf_pCoreOf_of_mem_calC hL]
    exact inf_le_right
  have hHM : memberDelta D L A ≤ D.M := member_le_M D hL.1.le A
  have hO2M_H : CFSG.Open.pCoreOf 2 D.M ≤ memberDelta D L A :=
    hO2M_le_T.trans le_sup_right
  have hO2M_le_O2H : CFSG.Open.pCoreOf 2 D.M ≤
      CFSG.Open.pCoreOf 2 (memberDelta D L A) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 hO2M_H ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hO2M_H).mpr
      (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
  exact hO2L_le_O2M.trans hO2M_le_O2H


theorem isAlt_imageBar2_perfDelta (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (A : Subgroup (Bar2 L)) (hAlt : IsAlt ↥A 5) :
    IsAlt ↥(imageBar2 (memberDelta D L A) (perfDelta L A)) 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := preDelta L A with hPdef
  set Q := perfDelta L A with hQdef
  set H := memberDelta D L A with hHdef
  set K := imageBar2 H Q with hKdef
  have hAsimp : IsSimpleGroup ↥A := by
    obtain ⟨eA⟩ := hAlt
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    exact eA.isSimpleGroup_congr.mpr inferInstance
  have : IsSimpleGroup ↥A := hAsimp
  have hQH : Q ≤ H := le_sup_left
  have hOleO2H : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    pCoreOf_le_pCoreOf_memberDelta D hL A
  have hO2HleH : CFSG.Open.pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hOleP : CFSG.Open.pCoreOf 2 L ≤ P := preDelta_contains_pCore L A
  have hPH : P ≤ H := by
    rw [hPdef, preDelta_eq_perfDelta_sup_pCore L A hAlt]
    exact sup_le hQH (hOleO2H.trans hO2HleH)
  have hO2Lnorm : ((CFSG.Open.pCoreOf 2 L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hOnorm : ((CFSG.Open.pCoreOf 2 L).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOleP]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).mp hO2Lnorm h k hh
      (preDelta_le L A (hPdef ▸ hk))
  have hO2image : imageBar2 H (CFSG.Open.pCoreOf 2 L) = ⊥ := by
    rw [imageBar2, Subgroup.map_eq_bot_iff]
    intro z hz
    exact (QuotientGroup.eq_one_iff z).mpr
      ((CFSG.mem_openPCoreOf_iff z).mp (hOleO2H (Subgroup.mem_subgroupOf.mp hz)))
  have himageP : imageBar2 H P = K := by
    rw [hPdef, preDelta_eq_perfDelta_sup_pCore L A hAlt,
      imageBar2_sup hQH (hOleO2H.trans hO2HleH), hO2image, sup_bot_eq]
  let fP : ↥P →* ↥K := (bar2Incl hPH).codRestrict K fun z => by
    have h : bar2Incl hPH z ∈ imageBar2 H P :=
      Subgroup.mem_map.mpr ⟨⟨(z : G), hPH z.2⟩, Subgroup.mem_subgroupOf.mpr z.2, rfl⟩
    rwa [himageP] at h
  have hfPsurj : Function.Surjective fP := by
    intro k
    have hk : (k : Bar2 H) ∈ (bar2Incl hPH).range := by
      rw [bar2Incl_range hPH, himageP]
      exact k.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hk
    exact ⟨z, Subtype.ext (by simpa [fP] using hz)⟩
  have hker : ∀ z : ↥P, fP z = 1 ↔ z ∈ (CFSG.Open.pCoreOf 2 H).subgroupOf P := by
    intro z
    constructor
    · intro hz
      have hz1 : bar2Incl hPH z = 1 := congrArg Subtype.val hz
      have hz2 : Subgroup.inclusion hPH z ∈ CFSG.pCore 2 ↥H :=
        (QuotientGroup.eq_one_iff _).mp hz1
      rw [Subgroup.mem_subgroupOf]
      exact (CFSG.mem_openPCoreOf_iff (Subgroup.inclusion hPH z)).mpr hz2
    · intro hz
      apply Subtype.ext
      show bar2Incl hPH z = 1
      rw [bar2Incl, MonoidHom.comp_apply]
      exact (QuotientGroup.eq_one_iff _).mpr
        ((CFSG.mem_openPCoreOf_iff (Subgroup.inclusion hPH z)).mp
          (Subgroup.mem_subgroupOf.mp hz))
  have hOleKer : (CFSG.Open.pCoreOf 2 L).subgroupOf P ≤ fP.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    exact (hker z).mpr (Subgroup.mem_subgroupOf.mpr
      (hOleO2H (Subgroup.mem_subgroupOf.mp hz)))
  have ePA : (↥P ⧸ (CFSG.Open.pCoreOf 2 L).subgroupOf P) ≃* ↥A :=
    ((QuotientGroup.quotientMulEquivOfEq (preDeltaMap_ker_eq_pCore L A)).symm.trans
      (QuotientGroup.quotientKerEquivRange (preDeltaMap L A))).trans
      (MulEquiv.subgroupCongr (preDeltaMap_range L A))
  have : IsSimpleGroup (↥P ⧸ (CFSG.Open.pCoreOf 2 L).subgroupOf P) :=
    ePA.isSimpleGroup_congr.mpr hAsimp
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have : Subsingleton ↥K := by rw [hKbot]; infer_instance
    have hPle : P ≤ CFSG.Open.pCoreOf 2 H := by
      intro p hp
      have h1 : fP ⟨p, hp⟩ = 1 := Subsingleton.elim _ _
      exact Subgroup.mem_subgroupOf.mp ((hker ⟨p, hp⟩).mp h1)
    have hP2 : IsPGroup 2 ↥P :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hPle
    have hquot2 : IsPGroup 2 (↥P ⧸ (CFSG.Open.pCoreOf 2 L).subgroupOf P) :=
      IsPGroup.of_surjective hP2 (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hcard : Nat.card (↥P ⧸ (CFSG.Open.pCoreOf 2 L).subgroupOf P) = 60 := by
      rw [Nat.card_congr ePA.toEquiv]
      obtain ⟨eA⟩ := hAlt
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    obtain ⟨n, hn⟩ := hquot2.exists_card_eq
    rw [hcard] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  let ψ : (↥P ⧸ (CFSG.Open.pCoreOf 2 L).subgroupOf P) →* ↥K :=
    QuotientGroup.lift _ fP hOleKer
  have hψsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨z, rfl⟩ := hfPsurj k
    exact ⟨QuotientGroup.mk z, QuotientGroup.lift_mk _ hOleKer z⟩
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      apply hKne
      rw [eq_bot_iff]
      intro k hk
      obtain ⟨z, hz⟩ := hfPsurj ⟨k, hk⟩
      have hz1 : QuotientGroup.mk z ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hz1
      have hz2 : (⟨k, hk⟩ : ↥K) = 1 := hz ▸ hz1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz2)
  obtain ⟨eA5⟩ := hAlt
  exact ⟨(MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).symm.trans (ePA.trans eA5)⟩


theorem pCoreOf_M_le_pCoreOf_memberDelta (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (A : Subgroup (Bar2 L)) :
    CFSG.Open.pCoreOf 2 D.M ≤ CFSG.Open.pCoreOf 2 (memberDelta D L A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hO2M_le_T : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsyl
  have hHM : memberDelta D L A ≤ D.M := member_le_M D hL.1.le A
  have hO2M_H : CFSG.Open.pCoreOf 2 D.M ≤ memberDelta D L A :=
    hO2M_le_T.trans le_sup_right
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 hO2M_H ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hO2M_H).mpr
    (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))

theorem isQuasisimple_imageBar2_perfDelta (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (A : Subgroup (Bar2 L)) (hAlt : IsAlt ↥A 5) :
    CFSG.IsQuasisimple ↥(imageBar2 (memberDelta D L A) (perfDelta L A)) := by
  obtain ⟨eK⟩ := isAlt_imageBar2_perfDelta D hL A hAlt
  have hq5 : CFSG.Open.IsQuasisimple ↥(alternatingGroup (Fin 5)) :=
    CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup (by norm_num)
  exact (CFSG.Quasithin.A3.isQuasisimple_iff_open).mpr (hq5.of_mulEquiv eK)


theorem commute_imageBar2_perfDelta_conj (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (A : Subgroup (Bar2 L)) (hAlt : IsAlt ↥A 5)
    (hInv : ∀ s ∈ (CFSG.GroupTheory.conjModPCore 2 L
        (D.T ⊓ Subgroup.normalizer (L : Set G)) inf_le_right).range,
      A.map s.toMonoidHom = A)
    {s t : G} (hs : s ∈ D.T) (ht : t ∈ D.T)
    (hne : imageBar2 (memberDelta D L A)
        ((perfDelta L A).map (MulAut.conj s).toMonoidHom) ≠
      imageBar2 (memberDelta D L A)
        ((perfDelta L A).map (MulAut.conj t).toMonoidHom)) :
    ∀ x ∈ imageBar2 (memberDelta D L A) ((perfDelta L A).map (MulAut.conj s).toMonoidHom),
      ∀ y ∈ imageBar2 (memberDelta D L A) ((perfDelta L A).map (MulAut.conj t).toMonoidHom),
        Commute x y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := memberDelta D L A
  set Q := perfDelta L A
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hsM : s ∈ D.M := hTM hs
  have htM : t ∈ D.M := hTM ht
  have hMMs : D.M.map (MulAut.conj s).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsM)
  have hMMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htM)
  have hLs : L.map (MulAut.conj s).toMonoidHom ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj s) hMMs hL
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMMt hL
  have hLne : L.map (MulAut.conj s).toMonoidHom ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro heq
    apply hne
    have huN : s⁻¹ * t ∈ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change Subgroup.map (MulAut.conj (s⁻¹ * t)).toMonoidHom L = L
      have hcomp1 : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          (MulAut.conj (s⁻¹ * t)).toMonoidHom := by
        ext x
        change (MulAut.conj s⁻¹) ((MulAut.conj t) x) = (MulAut.conj (s⁻¹ * t)) x
        rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
        group
      have h1 : L.map (MulAut.conj (s⁻¹ * t)).toMonoidHom =
          (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by
        rw [Subgroup.map_map, hcomp1]
      rw [h1, ← heq, Subgroup.map_map]
      have h2 : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          (MulAut.conj (s⁻¹ * s)).toMonoidHom := by
        ext x
        change (MulAut.conj s⁻¹) ((MulAut.conj s) x) = (MulAut.conj (s⁻¹ * s)) x
        rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [h2, inv_mul_cancel, map_one]
      exact Subgroup.map_id L
    have huM : s⁻¹ * t ∈ D.T ⊓ Subgroup.normalizer (L : Set G) :=
      ⟨D.T.mul_mem (D.T.inv_mem hs) ht, huN⟩
    have hQinv : Q.map (MulAut.conj (s⁻¹ * t)).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((le_normalizer_perfDelta_of_le_normalizer
          (M := D.T ⊓ Subgroup.normalizer (L : Set G)) inf_le_right A hInv) huM)
    have hcomp : (MulAut.conj s).toMonoidHom.comp (MulAut.conj (s⁻¹ * t)).toMonoidHom =
        (MulAut.conj t).toMonoidHom := by
      ext x
      change (MulAut.conj s) ((MulAut.conj (s⁻¹ * t)) x) = (MulAut.conj t) x
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group
    have hQst : Q.map (MulAut.conj t).toMonoidHom = Q.map (MulAut.conj s).toMonoidHom := by
      rw [← hcomp, ← Subgroup.map_map, hQinv]
    rw [hQst]
  have hO2M_H : CFSG.Open.pCoreOf 2 D.M ≤ CFSG.Open.pCoreOf 2 H :=
    pCoreOf_M_le_pCoreOf_memberDelta D hL A
  have hHs : H.map (MulAut.conj s).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (le_sup_right (a := Q) (by exact hs : s ∈ D.T)))
  have hHt : H.map (MulAut.conj t).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (le_sup_right (a := Q) (by exact ht : t ∈ D.T)))
  have hQsH : (Q.map (MulAut.conj s).toMonoidHom) ≤ H := by
    rw [← hHs]
    exact Subgroup.map_mono (f := (MulAut.conj s).toMonoidHom) le_sup_left
  have hQtH : (Q.map (MulAut.conj t).toMonoidHom) ≤ H := by
    rw [← hHt]
    exact Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) le_sup_left
  intro x hx y hy
  have hxr : x ∈ (bar2Incl hQsH).range := by
    rw [bar2Incl_range hQsH]
    exact hx
  have hyr : y ∈ (bar2Incl hQtH).range := by
    rw [bar2Incl_range hQtH]
    exact hy
  obtain ⟨xs, rfl⟩ := MonoidHom.mem_range.mp hxr
  obtain ⟨ys, rfl⟩ := MonoidHom.mem_range.mp hyr
  let xsH : ↥H := ⟨(xs : G), hQsH xs.2⟩
  let ysH : ↥H := ⟨(ys : G), hQtH ys.2⟩
  have hQsL : Q.map (MulAut.conj s).toMonoidHom ≤ L.map (MulAut.conj s).toMonoidHom :=
    Subgroup.map_mono (f := (MulAut.conj s).toMonoidHom) (perfDelta_le L A)
  have hQtL : Q.map (MulAut.conj t).toMonoidHom ≤ L.map (MulAut.conj t).toMonoidHom :=
    Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) (perfDelta_le L A)
  have hxsG : (xs : G) ∈ L.map (MulAut.conj s).toMonoidHom := hQsL xs.2
  have hysG : (ys : G) ∈ L.map (MulAut.conj t).toMonoidHom := hQtL ys.2
  have hmemM : ⁅(xs : G), (ys : G)⁆ ∈ CFSG.Open.pCoreOf 2 D.M :=
    commutator_mem_pCoreOf_of_ne hLs hLt hLne hxsG hysG
  have hmemH : ⁅xsH, ysH⁆ ∈ CFSG.pCore 2 ↥H := by
    have hmemG : ((⁅xsH, ysH⁆ : ↥H) : G) ∈ CFSG.Open.pCoreOf 2 H := by
      rw [show ((⁅xsH, ysH⁆ : ↥H) : G) = ⁅(xs : G), (ys : G)⁆ from
        map_commutatorElement H.subtype xsH ysH]
      exact hO2M_H hmemM
    exact (CFSG.mem_openPCoreOf_iff (⁅xsH, ysH⁆)).mp hmemG
  have hmain : ⁅bar2Incl hQsH xs, bar2Incl hQtH ys⁆ = 1 := by
    have h1 : bar2Incl hQsH xs = (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) xsH := rfl
    have h2 : bar2Incl hQtH ys = (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ysH := rfl
    rw [h1, h2]
    exact (QuotientGroup.eq_one_iff _).mpr hmemH
  exact commutatorElement_eq_one_iff_mul_comm.mp hmain


theorem normal_imageBar2_perfDelta_conj_in_orbitClosure (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (A : Subgroup (Bar2 L)) (hAlt : IsAlt ↥A 5)
    (hInv : ∀ s ∈ (CFSG.GroupTheory.conjModPCore 2 L
        (D.T ⊓ Subgroup.normalizer (L : Set G)) inf_le_right).range,
      A.map s.toMonoidHom = A)
    {s : G} (hs : s ∈ D.T) :
    ((imageBar2 (memberDelta D L A) ((perfDelta L A).map (MulAut.conj s).toMonoidHom)).subgroupOf
      (orbitClosure (imageBar2 (memberDelta D L A) (perfDelta L A))
        (imageBar2 (memberDelta D L A) D.T))).Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := memberDelta D L A
  set Q := perfDelta L A
  set B := imageBar2 H (Q.map (MulAut.conj s).toMonoidHom)
  set K := imageBar2 H Q
  set T1 := imageBar2 H D.T
  set N := orbitClosure K T1
  have hTH : D.T ≤ H := le_sup_right
  have hQsH : (Q.map (MulAut.conj s).toMonoidHom) ≤ H := by
    have hHs : H.map (MulAut.conj s).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (le_sup_right (a := Q) (by exact hs : s ∈ D.T)))
    rw [← hHs]
    exact Subgroup.map_mono (f := (MulAut.conj s).toMonoidHom) le_sup_left
  have hQH : Q ≤ H := le_sup_left
  have hBN : B ≤ N := by
    have hmap : B = K.map (MulAut.conj (bar2Incl hTH ⟨s, hs⟩)).toMonoidHom := by
      rw [bar2Incl, MonoidHom.comp_apply]
      exact (imageBar2_map_conj hQH (hTH hs)).symm
    rw [hmap]
    exact map_conj_le_orbitClosure K (Subgroup.mem_map_of_mem (QuotientGroup.mk' _)
      (Subgroup.mem_subgroupOf.mpr hs))
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hBN).mpr ?_
  refine orbitClosure_le fun a ha => ?_
  have har : a ∈ (bar2Incl hTH).range := by
    rw [bar2Incl_range hTH]
    exact ha
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp har
  have hKa : K.map (MulAut.conj (bar2Incl hTH r)).toMonoidHom =
      imageBar2 H (Q.map (MulAut.conj (r : G)).toMonoidHom) := by
    rw [bar2Incl, MonoidHom.comp_apply]
    exact imageBar2_map_conj hQH (hTH r.2)
  by_cases hEq : K.map (MulAut.conj (bar2Incl hTH r)).toMonoidHom = B
  · rw [hEq]
    exact Subgroup.le_normalizer
  · have hne : imageBar2 H (Q.map (MulAut.conj (r : G)).toMonoidHom) ≠
        imageBar2 H (Q.map (MulAut.conj s).toMonoidHom) := by
      intro hcontra
      apply hEq
      rw [hKa]
      exact hcontra
    have hcomm := commute_imageBar2_perfDelta_conj D hL A hAlt hInv r.2 hs hne
    rw [hKa]
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hzy : ∀ z ∈ B, (MulAut.conj y) z = z := by
      intro z hz
      rw [MulAut.conj_apply]
      calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [(hcomm y hy z hz).eq]
        _ = z := by group
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      change (MulAut.conj y) z ∈ B
      rwa [hzy z hz]
    · intro z hz
      exact ⟨z, hz, hzy z hz⟩

theorem gap17_19_A5Members (D : Data G) (V₀ V : Subgroup G) :
    Gap17_19_A5Members D V₀ V := by
  classical
  intro L c hJ A hAlt hInv hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : L ∈ calC D.M := c.mem_calC
  set Q := perfDelta L A with hQdef
  set H := memberDelta D L A with hHdef
  set K := imageBar2 H Q with hKdef
  set T1 := imageBar2 H D.T with hT1def
  set N := orbitClosure K T1 with hNdef
  have hTH : D.T ≤ H := le_sup_right
  have hgen : N ⊔ T1 = ⊤ := orbitClosure_imageBar2_perfDelta_sup_eq_top D A
  have hNnormal : N.Normal := orbitClosure_normal hgen
  have : N.Normal := hNnormal
  have hKq : CFSG.IsQuasisimple ↥K := isQuasisimple_imageBar2_perfDelta D hL A hAlt
  have hId : Q.map (MulAut.conj (1 : G)).toMonoidHom = Q := by
    rw [map_one]
    exact Subgroup.map_id Q
  have hKnormal : (K.subgroupOf N).Normal := by
    have h := normal_imageBar2_perfDelta_conj_in_orbitClosure D hL A hAlt hInv
      (s := 1) (one_mem D.T)
    rw [hId] at h
    simpa [Q, H, K, T1, N] using h
  have hKsub : K.IsSubnormal :=
    Subgroup.IsSubnormal.step K N (le_orbitClosure K T1)
      (Subgroup.Normal.isSubnormal hNnormal) hKnormal
  have hKcomp : CFSG.IsComponent K := ⟨hKq, hKsub⟩
  have hKsimp : IsSimpleGroup ↥K := by
    obtain ⟨eK⟩ := isAlt_imageBar2_perfDelta D hL A hAlt
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    exact eK.isSimpleGroup_congr.mpr inferInstance
  have hKnc : ¬ IsMulCommutative ↥K := by
    obtain ⟨eK⟩ := isAlt_imageBar2_perfDelta D hL A hAlt
    intro h
    have h5 : IsMulCommutative ↥(alternatingGroup (Fin 5)) :=
      (isMulCommutative_congr eK).mp h
    rw [alternatingGroup.isMulCommutative_iff_card_le_three] at h5
    simpa using h5
  have hKL2 : IsL2 ↥K 2 := by
    obtain ⟨eK⟩ := isAlt_imageBar2_perfDelta D hL A hAlt
    exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five eK
  have hT12 : IsPGroup 2 T1 := by
    have hT2H : IsPGroup 2 ↥(D.T.subgroupOf H) :=
      IsPGroup.of_equiv D.sylowM.isPGroup
        (Subgroup.subgroupOfEquivOfLe hTH).symm
    have h1 : IsPGroup 2 (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        (D.T.subgroupOf H)) :=
      IsPGroup.map (H := D.T.subgroupOf H) hT2H (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    exact h1
  have hquotN : IsPGroup 2 (Bar2 H ⧸ N) := by
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp T1.subtype) := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      have hx : x ∈ T1 ⊔ N := by
        rw [sup_comm, hgen]
        exact Subgroup.mem_top x
      obtain ⟨a, ha, n, hn, hxeq⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := T1) (t := N)).mp hx
      refine ⟨⟨a, ha⟩, ?_⟩
      change (QuotientGroup.mk' N) a = (QuotientGroup.mk' N) x
      rw [← hxeq, map_mul]
      have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [hn1, mul_one]
    exact IsPGroup.of_surjective hT12 _ hsurj
  have : Fintype ↥D.T := Fintype.ofFinite _
  let fam : Finset (Subgroup (Bar2 H)) := Finset.univ.image
    (fun t : ↥D.T => imageBar2 H (Q.map (MulAut.conj (t : G)).toMonoidHom))
  have hmemfam : ∀ B ∈ fam, ∃ t : ↥D.T,
      B = imageBar2 H (Q.map (MulAut.conj (t : G)).toMonoidHom) := by
    intro B hB
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨t, rfl⟩
  have hBt : ∀ t : ↥D.T, imageBar2 H (Q.map (MulAut.conj (t : G)).toMonoidHom) =
      K.map (MulAut.conj (bar2Incl hTH t)).toMonoidHom := by
    intro t
    rw [bar2Incl, MonoidHom.comp_apply]
    exact (imageBar2_map_conj (le_sup_left : Q ≤ H) (hTH t.2)).symm
  have hBiso : ∀ t : ↥D.T,
      Nonempty (↥K ≃* ↥(imageBar2 H (Q.map (MulAut.conj (t : G)).toMonoidHom))) := by
    intro t
    refine ⟨?_⟩
    rw [hBt t]
    exact Subgroup.equivMapOfInjective K (MulAut.conj (bar2Incl hTH t)).toMonoidHom
      (MulAut.conj (bar2Incl hTH t)).injective
  have hAle : ∀ B ∈ fam, B ≤ N := by
    intro B hB
    obtain ⟨t, rfl⟩ := hmemfam B hB
    rw [hBt t]
    exact map_conj_le_orbitClosure K (Subgroup.mem_map_of_mem
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.mem_subgroupOf.mpr t.2))
  have hAn : ∀ B ∈ fam, (B.subgroupOf N).Normal := by
    intro B hB
    obtain ⟨t, rfl⟩ := hmemfam B hB
    have h := normal_imageBar2_perfDelta_conj_in_orbitClosure D hL A hAlt hInv
      (s := (t : G)) t.2
    simpa [Q, H, K, T1, N] using h
  have hAs : ∀ B ∈ fam, IsSimpleGroup ↥B := by
    intro B hB
    obtain ⟨t, rfl⟩ := hmemfam B hB
    obtain ⟨e⟩ := hBiso t
    exact e.isSimpleGroup_congr.mp hKsimp
  have hAnabB : ∀ B ∈ fam, ¬ IsMulCommutative ↥B := by
    intro B hB
    obtain ⟨t, rfl⟩ := hmemfam B hB
    obtain ⟨e⟩ := hBiso t
    exact fun h => hKnc ((isMulCommutative_congr e).mpr h)
  have hcommB : ∀ B ∈ fam, ∀ C ∈ fam, B ≠ C →
      ∀ x ∈ B, ∀ y ∈ C, Commute x y := by
    intro B hB C hC hne x hx y hy
    obtain ⟨s, rfl⟩ := hmemfam B hB
    obtain ⟨t, rfl⟩ := hmemfam C hC
    exact commute_imageBar2_perfDelta_conj D hL A hAlt hInv s.2 t.2 hne x hx y hy
  have hsupB : fam.sup id = N := by
    refine le_antisymm (Finset.sup_le hAle) ?_
    change orbitClosure K T1 ≤ fam.sup id
    refine orbitClosure_le fun a ha => ?_
    have har : a ∈ (bar2Incl hTH).range := by
      rw [bar2Incl_range hTH]
      exact ha
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp har
    have hmem : imageBar2 H (Q.map (MulAut.conj (t : G)).toMonoidHom) ∈ fam :=
      Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    rw [← hBt t]
    exact Finset.le_sup (f := id) hmem
  have hshapeB : ∀ B ∈ fam, IsL2 ↥B 2 ∨ IsSz ↥B 2 := by
    intro B hB
    obtain ⟨t, rfl⟩ := hmemfam B hB
    obtain ⟨e⟩ := hBiso t
    exact Or.inl (LieModel.of_mulEquiv e hKL2)
  refine ⟨K, hKcomp, hgen, ?_⟩
  exact hasComponentShapes_of_normal_direct hNnormal hquotN fam hAle hAn hAs hAnabB hcommB
    hsupB hshapeB

theorem memberDelta_inFSq_of_gap (D : Data G)
    {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L) (hJ : IsJ1 (Bar2 L))
    {A : Subgroup (Bar2 L)} (hAlt : IsAlt ↥A 5)
    (hInv : ∀ s ∈ (CFSG.GroupTheory.conjModPCore 2 L
        (D.T ⊓ Subgroup.normalizer (L : Set G)) inf_le_right).range,
      A.map s.toMonoidHom = A)
    (hT : ¬ D.T ≤ Subgroup.normalizer (L : Set G))
    (hGap : Gap17_19_A5Members D V₀ V) (hKc : K_L2SzAutRank) (h43c : W3Lem45_2Chief) :
    InFSq 2 (memberDelta D L A) := by
  obtain ⟨K, hK, hgen, hshape⟩ := hGap L c hJ A hAlt hInv hT
  have hTsyl : IsSylowIn 2 (imageBar2 (memberDelta D L A) D.T) ⊤ :=
    isSylowIn_imageBar2 (TwelveShort.isSylowIn_of_le D le_sup_right)
  have hshapeTop : HasComponentShapes (↥(⊤ : Subgroup (Bar2 (memberDelta D L A)))) 2 :=
    hasComponentShapes_of_mulEquiv (Subgroup.topEquiv (G := Bar2 (memberDelta D L A))).symm
      hshape
  refine inFSq_of_components h43c (by norm_num) hK hTsyl hgen ?_
  intro T' hT'
  exact compFactorAutInF_of_hasComponentShapes hT'.isPGroup hshapeTop hKc

theorem exists_delta_of_nonnormal (D : Data G)
    {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L) (hJ : IsJ1 (Bar2 L))
    (h3' : ∀ g : G, g ∉ D.M → ¬ 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g))
    (hU : UniqueMax D.M L) (hT : ¬ D.T ≤ Subgroup.normalizer (L : Set G))
    (hKJ1 : K_J1A5Gen) (hKc : K_L2SzAutRank)
    (h43c : W3Lem45_2Chief) (hGap : Gap17_19_A5Members D V₀ V) :
    ∃ Δ : Finset (Subgroup G),
      (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
        (∀ H ∈ Δ, InFSq 2 H) ∧
          (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g) := by
  classical
  let M : Subgroup G := D.T ⊓ Subgroup.normalizer (L : Set G)
  have hMle : M ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  let φ := CFSG.GroupTheory.conjModPCore 2 L M hMle
  have hS : IsPGroup 2 φ.range := by
    have h2 : IsPGroup 2 ↥M := D.sylowM.isPGroup.to_le inf_le_left
    have htop : IsPGroup 2 ↥(⊤ : Subgroup ↥M) :=
      h2.of_equiv (Subgroup.topEquiv (G := ↥M)).symm
    have h := IsPGroup.map htop φ
    rwa [Subgroup.map_top] at h
  obtain ⟨Δbar, hΔbar_ne, hΔbar, hgen⟩ := hKJ1 (Bar2 L) hJ φ.range hS
  let toH : Subgroup (Bar2 L) → Subgroup G := fun A => memberDelta D L A
  have hΔmem : ∀ H ∈ Δbar.image toH, D.T ≤ H ∧ H ≤ D.M := by
    intro H hH
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hH
    exact ⟨le_member D L A, member_le_M D c.mem_calC.1.le A⟩
  have hΔInFSq : ∀ H ∈ Δbar.image toH, InFSq 2 H := by
    intro H hH
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hH
    exact memberDelta_inFSq_of_gap D c hJ (hΔbar A hA).1 (hΔbar A hA).2 hT hGap hKc h43c
  have hΔres : ∀ H ∈ Δbar.image toH, ∀ g : G, g ∉ D.M →
      ¬ twoResidual H ≤ conjSubgroup D.M g := by
    intro H hH g hg hle
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hH
    have h3Q : 3 ∣ Nat.card ↥(perfDelta L A) := three_dvd_perfDelta L A (hΔbar A hA).1
    have hQres : perfDelta L A ≤ twoResidual (memberDelta D L A) :=
      CFSG.Quasithin.GE23.le_twoResidual_of_perfect le_sup_left (perfDelta_perfect L A)
    have hQle : perfDelta L A ≤ L ⊓ conjSubgroup D.M g :=
      le_inf (perfDelta_le L A) (hQres.trans hle)
    have hdvd : 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) := by
      have h1 := Subgroup.card_subgroup_dvd_card
        ((perfDelta L A).subgroupOf (L ⊓ conjSubgroup D.M g))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv] at h1
      exact h3Q.trans h1
    exact h3' g hg hdvd
  have hTsup : D.T ≤ ⨆ H ∈ Δbar.image toH, H := by
    obtain ⟨i0, hi0⟩ := hΔbar_ne
    have hmem : toH i0 ∈ Δbar.image toH := Finset.mem_image.mpr ⟨i0, hi0, rfl⟩
    exact (le_member D L i0).trans (le_iSup₂_of_le (toH i0) hmem le_rfl)
  have hLsup : L ≤ ⨆ H ∈ Δbar.image toH, H := by
    have hgenL : L ≤ (⨆ A ∈ Δbar, perfDelta L A) ⊔ D.T :=
      L_le_iSup_perfDelta_sup_T D c.mem_calC Δbar (fun A => A)
        (fun i hi => (hΔbar i hi).1) hgen
    have h1 : (⨆ A ∈ Δbar, perfDelta L A) ≤ ⨆ H ∈ Δbar.image toH, H := by
      refine iSup₂_le fun A hA => ?_
      have hmem : toH A ∈ Δbar.image toH := Finset.mem_image.mpr ⟨A, hA, rfl⟩
      exact (le_sup_left : perfDelta L A ≤ toH A).trans
        (le_iSup₂_of_le (toH A) hmem le_rfl)
    exact hgenL.trans (sup_le h1 hTsup)
  have hU' : UniqueMax D.M (⨆ H ∈ Δbar.image toH, H) := by
    unfold UniqueMax at hU ⊢
    ext N
    constructor
    · intro hN
      have hLN : L ≤ N := hLsup.trans hN.2
      have hmem : N ∈ calMOf L := ⟨hN.1, hLN⟩
      rw [hU] at hmem
      simpa using hmem
    · intro hN
      have hNM : N = D.M := by simpa using hN
      subst hNM
      exact ⟨D.maxLocal, iSup₂_le fun H hH => (hΔmem H hH).2⟩
  exact ⟨Δbar.image toH, hΔmem, hU', hΔInFSq, hΔres⟩

section Certified


theorem gap17_19Delta_of (D : Data G) (V₀ V : Subgroup G)
    (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D)
    (hU3 : K_U3FourPowThreeRankOne)
    (hKJ1 : K_J1A5Gen) (hKc : K_L2SzAutRank)
    (h43c : W3Lem45_2Chief) :
    Gap17_19Delta D V₀ V := by
  intro L c hJ h3' hV0 hT
  have hAuniq : ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 → A ∈ uniqueSet D.M :=
    mem_uniqueSet_of_card_three_of_isJ1 D c hJ h8107 hU3
  have hU : UniqueMax D.M L := uniqueMax_of_isJ1 D c hJ h920 hAuniq
  by_cases hTN : D.T ≤ Subgroup.normalizer (L : Set G)
  · exact exists_delta_of_normal D c hJ hTN h3' hU hKJ1 hKc
  · exact exists_delta_of_nonnormal D c hJ h3' hU hT hKJ1 hKc h43c
      (gap17_19_A5Members D V₀ V)


theorem seventeen_nineteen_of (D : Data G) (V₀ V : Subgroup G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (h111 : W3Thm111 G) (h117 : C117 D V₀ V)
    (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1 D)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) (h77 : Inputs1719.W4Lem7_7)
    (hrow : Inputs1719.W4Thm11_1Row .J1)
    (h43c : W3Lem45_2Chief) :
    R17_19At D V₀ V := by
  have hU3 : Inputs1719.K_U3FourPowThreeRankOne := Inputs1719.k_U3FourPowThreeRankOne_holds
  exact seventeen_nineteen D V₀ V hx h61 h127 h1114 h162 hTor h1482 h126 h111 h117 h8107 h920
    hU3
    (b17_19Bound_holds D V₀ V hx h61 h127 h1214 h4128 h117 h77 hrow)
    (gap17_19Delta_of D V₀ V h8107 h920 hU3 Inputs1719.k_J1A5Gen_holds
      Inputs1719.k_L2SzAutRank_holds h43c)
    Inputs1719.k_J1A5Gen_holds Inputs1719.k_L2SzAutRank_holds

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
