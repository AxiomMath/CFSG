module

public import CFSG.Quasithin.Recognition.Stroth.SliceSzUReduction
public import CFSG.Quasithin.Recognition.Stroth.Y9Transport
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Quasithin.Recognition.Stroth.U54VertexFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNst
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.Quasithin.Vol2.E2NinePullback
public import CFSG.Quasithin.H13.A7Nat1238Setup
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin.H13.F431.Un.OL5 CFSG.Quasithin.H13.Sec53F CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.RankThree.PartOne.U5K.Hyp CFSG.AGLEmbedding
  CFSG.GH74.QTGen4.DSGen4

variable {K : Type} [Field K]

private theorem card_u5LnP (h : UnitaryFieldData 2 2 K) :
    Nat.card (u5LnP h) = 802160640 := by
  have hfin : Finite K := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiso : ∀ x ∈ hypFlag h 2 1 2, ∀ y ∈ hypFlag h 2 1 2, hypForm h 2 1 x y = 0 :=
    (isIsotropicChain_hypFlag h (r := 2) (ε := 1) le_rfl).2.2 2 le_rfl
  have hidxLn : (u5LnP h).index = 66625 := by
    have hfr : Module.finrank K (hypFlag h 2 1 2) = 2 :=
      (isIsotropicChain_hypFlag h (r := 2) (ε := 1) le_rfl).1 2 le_rfl
    have hiso' := isotropic_stabilizer_index h (W := hypFlag h 2 1 2) hiso
    rw [hfr] at hiso'
    have hq : ((isoStabilizer h 2 1 (hypFlag h 2 1 2)).index : ℚ) = 66625 := by
      have hI2 : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hiso'.2.1, hiso'.2.2.2.2.2.2 2, hI2]
      norm_num
    have hidx : (isoStabilizer h 2 1 (hypFlag h 2 1 2)).index = 66625 := by
      exact_mod_cast hq
    rw [u5LnP, hiso'.1, hidx]
  have hSUcard : Nat.card (hypSU h 2 1) = 267219763200000 := by
    have hformula :=
      (unitary_order_and_Sylow h (r := 2) (ε := 1) (by norm_num) (by norm_num)).2.2.2.2.2.1
    have hI : Finset.Icc 2 (2 * 2 + 1) = {2, 3, 4, 5} := by decide
    rw [hI] at hformula
    norm_num at hformula ⊢
    exact_mod_cast hformula
  have hPSUcard : Nat.card (hypPSU h 2 1) = 53443952640000 := by
    have h := (unitary_order_and_Sylow h (r := 2) (ε := 1) (by norm_num) (by norm_num)).2.2.2.2.2.2
    rw [hSUcard] at h
    norm_num at h
    exact h
  have hmul := Subgroup.index_mul_card (u5LnP h)
  rw [hidxLn, hPSUcard] at hmul
  omega

private theorem not_dvd_card_u5LnP (h : UnitaryFieldData 2 2 K) :
    ¬ 13 ∣ Nat.card (u5LnP h) := by
  rw [card_u5LnP h]
  norm_num

private theorem centerOf_perfectCore_u5PtP_eq_centerOf_U (h : UnitaryFieldData 2 2 K) :
    centerOf (perfectCore (u5PtP h)) = centerOf (hypProjUnitriangular h 2 1) := by
  have hfin : Finite K := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hf : 2 ≤ 2 := le_rfl
  have hZPt : centerOf (perfectCore (u5PtP h)) = (ZPsub h).map (hypProj h 2 1) :=
    centerOf_perfectCore_u5PtP (h := h) hf
  have hZU : centerOf (hypProjUnitriangular h 2 1) = (ZPsub h).map (hypProj h 2 1) := by
    apply le_antisymm
    · calc centerOf (hypProjUnitriangular h 2 1)
          ≤ Subgroup.centralizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) :=
            inf_le_right
        _ ≤ (ZPsub h).map (hypProj h 2 1) := centralizer_le_map_ZPsub (h := h)
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨Subgroup.mem_map_of_mem _ (ZPsub_le_U hw),
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_mul, ZPsub_commute hw hu]
  exact hZPt.trans hZU.symm

private theorem exists_unitaryFieldData_of_psu5 {Y : Type} [Group Y]
    (hY : IsLieOverTwo .PSU 5 2 Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (h : UnitaryFieldData 2 2 F),
      Nonempty (Y ≃* hypPSU h 2 1) := by
  rcases hY with ⟨-, hc⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  · obtain ⟨-, F, hField, hFinite, hF, ⟨eS⟩⟩ := hc
    letI := hField
    letI := hFinite
    have hcard : Nat.card F = 2 ^ (2 * 2) := by rw [hF]; norm_num
    have h : UnitaryFieldData 2 2 F := ⟨Nat.prime_two, by norm_num, hcard⟩
    haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    exact ⟨F, hField, hFinite, h,
      ⟨eS.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm⟩⟩
  all_goals exact absurd hn0 (by norm_num)

private theorem thirteen_dvd_card_of_statedSU {G : Type} [Group G] {L : Subgroup G}
    (hSU : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L ≃* StatedSU 3 4 F)) :
    13 ∣ Nat.card ↥L := by
  obtain ⟨F, hField, hFinite, hcard4, ⟨eSU⟩⟩ := hSU
  letI := hField
  letI := hFinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 2)
      (by rw [hcard4]; norm_num)
  have hcardQuot : Nat.card (oTwoQuot ↥L) = 62400 := by
    rw [Nat.card_congr eSU.toEquiv, show (4 : ℕ) = 2 ^ 2 by norm_num,
      CFSG.SectionRank.OddCover.card_statedSU_three (p := 2) (f := 2)
        (by rw [hcard4]; norm_num)]
    norm_num
  have h1 : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  rw [h1, hcardQuot]
  exact (show (13 : ℕ) ∣ 62400 by norm_num).mul_right _

private theorem u54_orientation {G : Type} [Group G] {Y : Type} [Group Y]
    {K : Type} [Field K] {h : UnitaryFieldData 2 2 K}
    {L1 L2 S : Subgroup G} {M1 M2 : Subgroup Y}
    (ε : Y ≃* hypPSU h 2 1)
    (hPε : (M1.map ε.toMonoidHom = u5PtP h ∧ M2.map ε.toMonoidHom = u5LnP h) ∨
      (M1.map ε.toMonoidHom = u5LnP h ∧ M2.map ε.toMonoidHom = u5PtP h))
    (h13P : 13 ∣ Nat.card ↥(L1 ⊔ bigB L1 L2 S))
    (hcard : Nat.card ↥M1 = Nat.card ↥(L1 ⊔ bigB L1 L2 S)) :
    M1.map ε.toMonoidHom = u5PtP h ∧ M2.map ε.toMonoidHom = u5LnP h := by
  have h13Ln : ¬ 13 ∣ Nat.card (u5LnP h) := not_dvd_card_u5LnP h
  have hM1ε : M1.map ε.toMonoidHom = u5PtP h := by
    rcases hPε with hcase | hcase
    · exact hcase.1
    · exfalso
      have hcardP : Nat.card ↥(L1 ⊔ bigB L1 L2 S) = Nat.card (u5LnP h) := by
        have hM1_Ln : Nat.card ↥M1 = Nat.card (u5LnP h) := by
          rw [← Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective, hcase.1]
        exact hcard.symm.trans hM1_Ln
      exact h13Ln (hcardP ▸ h13P)
  refine ⟨hM1ε, ?_⟩
  rcases hPε with hcase | hcase
  · exact hcase.2
  · exact absurd (hcase.1.symm.trans hM1ε) (u5PtP_ne_u5LnP (h := h)).symm

private structure U54Data (G : Type) [Group G] (L1 L2 S : Subgroup G) where
  K : Type
  [fieldK : Field K]
  h : UnitaryFieldData 2 2 K
  ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(u5PtP h)
  ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(u5LnP h)
  hBimg1 : ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
    (u5PtP h ⊓ u5LnP h).subgroupOf (u5PtP h)
  hBimg2 : ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
    (u5PtP h ⊓ u5LnP h).subgroupOf (u5LnP h)

private theorem u54_vertices {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hSU : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 4 F))
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 5 2)) :
    Nonempty (U54Data G L1 L2 S) := by
  classical
  obtain ⟨Y, _, hY, T, M1, M2, hpair, ⟨iso0⟩⟩ := hA
  obtain ⟨F, hField, hFinite, h, ⟨eY⟩⟩ := exists_unitaryFieldData_of_psu5 hY
  letI := hField
  letI := hFinite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  obtain ⟨c, -, hPc⟩ := (u5_yamStd (h := h)).pair eY hpair
  let ε : Y ≃* hypPSU h 2 1 := eY.trans (MulAut.conj c⁻¹)
  have hε : ∀ S : Subgroup Y, S.map ε.toMonoidHom =
      (S.map eY.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  have hPε : (M1.map ε.toMonoidHom = u5PtP h ∧
        M2.map ε.toMonoidHom = u5LnP h) ∨
      (M1.map ε.toMonoidHom = u5LnP h ∧
        M2.map ε.toMonoidHom = u5PtP h) := by
    rcases hPc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [hε, hε, h1, h2, Walter.map_conj_map_conj_inv, Walter.map_conj_map_conj_inv]
      exact ⟨rfl, rfl⟩
    · right
      rw [hε, hε, h1, h2, Walter.map_conj_map_conj_inv, Walter.map_conj_map_conj_inv]
      exact ⟨rfl, rfl⟩
  have hcard : Nat.card ↥M1 = Nat.card ↥(L1 ⊔ bigB L1 L2 S) :=
    (Nat.card_congr iso0.φ1.toEquiv).symm
  obtain ⟨hM1ε, hM2ε⟩ := u54_orientation ε hPε
    ((thirteen_dvd_card_of_statedSU hSU).trans (Subgroup.card_dvd_of_le le_sup_left)) hcard
  have hεinj : Function.Injective ε.toMonoidHom := ε.injective
  let e1 : (RankTwoAmalgam.ofSubgroups M1 M2).G1 ≃* ↥(u5PtP h) :=
    (M1.equivMapOfInjective ε.toMonoidHom hεinj).trans (MulEquiv.subgroupCongr hM1ε)
  let e2 : (RankTwoAmalgam.ofSubgroups M1 M2).G2 ≃* ↥(u5LnP h) :=
    (M2.equivMapOfInjective ε.toMonoidHom hεinj).trans (MulEquiv.subgroupCongr hM2ε)
  let ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(u5PtP h) := iso0.φ1.trans e1
  let ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(u5LnP h) := iso0.φ2.trans e2
  have hQ1 : (M1 ⊓ M2).map ε.toMonoidHom = u5PtP h ⊓ u5LnP h := by
    rw [Subgroup.map_inf_eq _ _ _ hεinj, hM1ε, hM2ε]
  have hP1P2 : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
    (CFSG.Quasithin.prop_F19_of_hyp111 (G := G) (L1 := L1) (L2 := L2) (S := S)
      hF.1).1
  have hBimg1 : ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (u5PtP h ⊓ u5LnP h).subgroupOf (u5PtP h) := by
    have h := iso_map_inter_of_equiv iso0 ε e1 hQ1 (fun x => rfl)
    rwa [show (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S from hP1P2]
      at h
  have hBimg2 : ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
      (u5PtP h ⊓ u5LnP h).subgroupOf (u5LnP h) := by
    have h := iso_map_inter_of_equiv_right iso0 ε e2 hQ1 (fun x => rfl)
    rwa [show (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S from hP1P2]
      at h
  exact ⟨⟨F, h, ψ1, ψ2, hBimg1, hBimg2⟩⟩

private theorem u54_model_data {K : Type} [Field K] (h : UnitaryFieldData 2 2 K) :
    hypProjUnitriangular h 2 1 ≤ u5PtP h ∧
      hypProjUnitriangular h 2 1 ≤ u5LnP h ∧
      IsSylowTwoOf (hypProjUnitriangular h 2 1) (u5PtP h) ∧
      IsSylowTwoOf (hypProjUnitriangular h 2 1) (u5LnP h) := by
  have hUB : hypProjUnitriangular h 2 1 ≤ hypProjBorel h 2 1 := by
    rw [← normalizer_hypProjUnitriangular_five (h := h)]
    exact Subgroup.le_normalizer
  have hUPt : hypProjUnitriangular h 2 1 ≤ u5PtP h :=
    hUB.trans (hypProjBorel_le_projIsoStabilizer h le_rfl (by norm_num))
  have hULn : hypProjUnitriangular h 2 1 ≤ u5LnP h :=
    hUB.trans (hypProjBorel_le_projIsoStabilizer h (by norm_num) le_rfl)
  exact ⟨hUPt, hULn, F7.isSylowTwoOf_mono_right (u5_sylow h) hUPt le_top,
    F7.isSylowTwoOf_mono_right (u5_sylow h) hULn le_top⟩

private theorem u54_S_image_of {G : Type} [Group G] [Finite G]
    {L B S : Subgroup G} {K : Type} [Field K] {h : UnitaryFieldData 2 2 K}
    {P : Subgroup (hypPSU h 2 1)}
    (ψ : ↥(L ⊔ B) ≃* ↥P)
    (hBimgN : ((B.subgroupOf (L ⊔ B)).map ψ.toMonoidHom).map P.subtype =
      u5PtP h ⊓ u5LnP h)
    (hSyl : IsSylowTwoOf S (L ⊔ B)) (hSleB : S ≤ B)
    (hUsyl : IsSylowTwoOf (hypProjUnitriangular h 2 1) P) :
    (S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom =
        (hypProjUnitriangular h 2 1).subgroupOf P := by
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hinfN : u5PtP h ⊓ u5LnP h =
      Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := by
    rw [u5PtP_inf_u5LnP, normalizer_hypProjUnitriangular_five]
  have hUsylN : IsSylowTwoOf (hypProjUnitriangular h 2 1)
      (Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1))) :=
    F7.isSylowTwoOf_mono_right (u5_sylow h) Subgroup.le_normalizer le_top
  have hUn : ((hypProjUnitriangular h 2 1).subgroupOf
      (Subgroup.normalizer (hypProjUnitriangular h 2 1 :
        Set (hypPSU h 2 1)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hSimgTop : IsSylowTwoOf ((S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom) ⊤ := by
    have hSsub : IsSylowTwoOf (S.subgroupOf (L ⊔ B)) ⊤ := by
      refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
      · exact hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
      · simpa using hSyl.2.2
    exact CFSG.Quasithin.E2.isSylowTwoOf_map_mulEquiv ψ hSsub
  have hUsubTop : IsSylowTwoOf ((hypProjUnitriangular h 2 1).subgroupOf P) ⊤ := by
    refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hUsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUsyl.1).symm
    · simpa using hUsyl.2.2
  have hSimg_le : (S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom ≤
      (hypProjUnitriangular h 2 1).subgroupOf P := by
    intro x hx
    have hxT : (x : hypPSU h 2 1) ∈
        (((S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom).map P.subtype) := ⟨x, hx, rfl⟩
    have hleT : (((S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom).map P.subtype) ≤
        Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := by
      have hSleB' : S.subgroupOf (L ⊔ B) ≤ B.subgroupOf (L ⊔ B) :=
        Subgroup.subgroupOf_mono _ hSleB
      calc (((S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom).map P.subtype)
          ≤ (((B.subgroupOf (L ⊔ B)).map ψ.toMonoidHom).map P.subtype) :=
            Subgroup.map_mono (Subgroup.map_mono hSleB')
        _ = u5PtP h ⊓ u5LnP h := hBimgN
        _ = Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := hinfN
    have hSsub2 : IsPGroup 2 (S.subgroupOf (L ⊔ B)) :=
      hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
    have hTp : IsPGroup 2 (((S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom).map P.subtype) :=
      (hSsub2.map ψ.toMonoidHom).map P.subtype
    exact le_of_isSylowTwoOf_normal hUsylN hUn hleT hTp hxT
  refine Subgroup.eq_of_le_of_card_ge hSimg_le ?_
  rw [hSimgTop.card_eq, hUsubTop.card_eq]

private theorem u54_perfectCore_of {G : Type} [Group G] [Finite G]
    {L B S : Subgroup G} {K : Type} [Field K] {h : UnitaryFieldData 2 2 K}
    {P : Subgroup (hypPSU h 2 1)}
    (ψ : ↥(L ⊔ B) ≃* ↥P)
    (hSUsub : (S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom =
      (hypProjUnitriangular h 2 1).subgroupOf P)
    (hSle : S ≤ L ⊔ B)
    (hUcore : hypProjUnitriangular h 2 1 ≤ perfectCore P) :
    ((perfectCore (L ⊔ B)).subgroupOf (L ⊔ B)).map ψ.toMonoidHom =
        (perfectCore P).subgroupOf P ∧
      S ≤ perfectCore (L ⊔ B) := by
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hperf : ((perfectCore (L ⊔ B)).subgroupOf (L ⊔ B)).map ψ.toMonoidHom =
      (perfectCore P).subgroupOf P := by
    have hpc := CFSG.Quasithin.F112R.perfectCore_map_inj ψ.toMonoidHom ψ.injective
      (⊤ : Subgroup ↥(L ⊔ B))
    rw [Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective] at hpc
    rw [← Subgroup.subgroupOf_self P] at hpc
    rw [← Subgroup.subgroupOf_self (L ⊔ B)] at hpc
    rw [← CFSG.Quasithin.H13.A7.perfectCore_subgroupOf_of_le (le_refl P)] at hpc
    rw [← CFSG.Quasithin.H13.A7.perfectCore_subgroupOf_of_le (le_refl (L ⊔ B))] at hpc
    exact hpc.symm
  have hUleCore : (hypProjUnitriangular h 2 1).subgroupOf P ≤
      (perfectCore P).subgroupOf P := by
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hUcore (Subgroup.mem_subgroupOf.1 hx))
  refine ⟨hperf, ?_⟩
  have h1 : (S.subgroupOf (L ⊔ B)).map ψ.toMonoidHom ≤
      ((perfectCore (L ⊔ B)).subgroupOf (L ⊔ B)).map ψ.toMonoidHom := by
    rw [hSUsub, hperf]
    exact hUleCore
  have h2 : S.subgroupOf (L ⊔ B) ≤
      (perfectCore (L ⊔ B)).subgroupOf (L ⊔ B) :=
    (Subgroup.map_le_map_iff_of_injective ψ.injective).1 h1
  intro s hs
  let sP : ↥(L ⊔ B) := ⟨s, hSle hs⟩
  exact Subgroup.mem_subgroupOf.1
    (h2 (Subgroup.mem_subgroupOf.2 (show (sP : G) ∈ S from hs)))

private theorem u54_perfect_left {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hSU : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 4 F))
    (hSleCore : S ≤ perfectCore (L1 ⊔ bigB L1 L2 S)) :
    perfectCore (L1 ⊔ bigB L1 L2 S) = L1 ∧ ⁅L1, L1⁆ = L1 := by
  have hR111 : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (CFSG.Quasithin.F112R.bigB_le_normalizer hF.1).1
  have hBsolv : Group.IsSolvable ↥(bigB L1 L2 S) := F1.isSolvable_bigB hR111
  have hcoreP1leL1 : perfectCore (L1 ⊔ bigB L1 L2 S) ≤ L1 := by
    have hn : (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hB1)
    exact CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left hn rfl hBsolv
  have hperfL1quot : Group.IsPerfect (oTwoQuot ↥L1) := by
    obtain ⟨F, hField, hFinite, hcard4, ⟨eSU⟩⟩ := hSU
    letI := hField
    letI := hFinite
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 :=
      CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 2)
        (by rw [hcard4]; norm_num)
    have hperf : Group.IsPerfect (StatedSU 3 (2 ^ 2) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 2)
        (by rw [hcard4]; norm_num) (by norm_num) (by norm_num)
    exact Group.IsPerfect.ofSurjective (f := eSU.symm.toMonoidHom) eSU.symm.surjective
  have hO1 : pCoreOf 2 L1 ≤ ⁅L1, L1⁆ := by
    calc pCoreOf 2 L1 ≤ S ⊓ L1 :=
          CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow
      _ ≤ S := inf_le_left
      _ ≤ perfectCore (L1 ⊔ bigB L1 L2 S) := hSleCore
      _ = ⁅perfectCore (L1 ⊔ bigB L1 L2 S), perfectCore (L1 ⊔ bigB L1 L2 S)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅L1, L1⁆ := Subgroup.commutator_mono hcoreP1leL1 hcoreP1leL1
  have hL1perf : ⁅L1, L1⁆ = L1 := perfect_of_isPerfect_oTwoQuot hperfL1quot hO1
  have hL1leCore1 : L1 ≤ perfectCore (L1 ⊔ bigB L1 L2 S) :=
    CFSG.Quasithin.le_perfectCore_of_perfect le_sup_left hL1perf
  exact ⟨le_antisymm hcoreP1leL1 hL1leCore1, hL1perf⟩

private theorem u54_perfect_right {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S)
    (hL2 : IsL2Quot 4 (oTwoQuot ↥L2))
    (hSleCore : S ≤ perfectCore (L2 ⊔ bigB L1 L2 S)) :
    perfectCore (L2 ⊔ bigB L1 L2 S) = L2 ∧ ⁅L2, L2⁆ = L2 := by
  have hR111 : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hB2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (CFSG.Quasithin.F112R.bigB_le_normalizer hF.1).2
  have hBsolv : Group.IsSolvable ↥(bigB L1 L2 S) := F1.isSolvable_bigB hR111
  have hcoreP2leL2 : perfectCore (L2 ⊔ bigB L1 L2 S) ≤ L2 := by
    have hn : (L2.subgroupOf (L2 ⊔ bigB L1 L2 S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hB2)
    exact CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left hn rfl hBsolv
  have hperfL2quot : Group.IsPerfect (oTwoQuot ↥L2) := by
    obtain ⟨eL2⟩ := hL2
    have h4 : ∃ s : Finset (GaloisField 2 4), s.card = 4 := by
      have h4c : 4 ≤ Nat.card (GaloisField 2 4) := by
        rw [GaloisField.card 2 4 (by norm_num)]
        norm_num
      have : Fintype (GaloisField 2 4) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (GaloisField 2 4))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4c)
      exact ⟨s, hs⟩
    have hPSL : Group.IsPerfect
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
      CFSG.LinearGroups.linear_projective_perfect (K := GaloisField 2 4)
        (by norm_num) (Or.inr h4)
    exact Group.IsPerfect.ofSurjective (f := eL2.symm.toMonoidHom) eL2.symm.surjective
  have hO2 : pCoreOf 2 L2 ≤ ⁅L2, L2⁆ := by
    calc pCoreOf 2 L2 ≤ S ⊓ L2 :=
          CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow
      _ ≤ S := inf_le_left
      _ ≤ perfectCore (L2 ⊔ bigB L1 L2 S) := hSleCore
      _ = ⁅perfectCore (L2 ⊔ bigB L1 L2 S), perfectCore (L2 ⊔ bigB L1 L2 S)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅L2, L2⁆ := Subgroup.commutator_mono hcoreP2leL2 hcoreP2leL2
  have hL2perf : ⁅L2, L2⁆ = L2 := perfect_of_isPerfect_oTwoQuot hperfL2quot hO2
  have hL2leCore2 : L2 ≤ perfectCore (L2 ⊔ bigB L1 L2 S) :=
    CFSG.Quasithin.le_perfectCore_of_perfect le_sup_left hL2perf
  exact ⟨le_antisymm hcoreP2leL2 hL2leCore2, hL2perf⟩

private theorem u54_special {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    {K : Type} [Field K] {h : UnitaryFieldData 2 2 K}
    (hF : F112Hyp L1 L2 S)
    (hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S))
    (hSle : S ≤ L1)
    (ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(u5PtP h))
    (hperfPt1 : ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (perfectCore (u5PtP h)).subgroupOf (u5PtP h))
    (hcoreP1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1) :
    IsSpecialPow 2 4 3 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
  have hB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (CFSG.Quasithin.F112R.bigB_le_normalizer hF.1).1
  have hPC1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 :=
    pCoreOf_sup_eq_of_sylow_le hB1 hSylP1 hSle
  let eP1 : ↥(perfectCore (L1 ⊔ bigB L1 L2 S)) ≃* ↥(perfectCore (u5PtP h)) :=
    (Subgroup.subgroupOfEquivOfLe (perfectCore_le (L1 ⊔ bigB L1 L2 S))).symm.trans
      ((MulEquiv.subgroupMap ψ1 ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
          (L1 ⊔ bigB L1 L2 S))).trans
        ((MulEquiv.subgroupCongr hperfPt1).trans
          (Subgroup.subgroupOfEquivOfLe (perfectCore_le (u5PtP h)))))
  rw [hPC1, ← hcoreP1]
  exact IsSpecialPow.of_mulEquiv (pCoreOfMulEquiv eP1 2).symm
    (isSpecialPow_pCoreOf_perfectCore_u5PtP (h := h) (by norm_num))

private theorem u54_card {G : Type} [Group G] {L1 L2 S : Subgroup G}
    {K : Type} [Field K] {h : UnitaryFieldData 2 2 K}
    (ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(u5LnP h)) :
    Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 16 := by
  calc Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
      = Nat.card (pCoreOf 2 (u5LnP h)) :=
        CFSG.Quasithin.F112R.card_pCoreOf_of_mulEquiv ψ2 2
    _ = Nat.card ((Ssub h).map (hypProj h 2 1)) := by rw [pCoreOf_u5LnP_eq]
    _ = Nat.card (Ssub h) := by rw [Un.card_map_hypProj (Ssub_le_Usub)]
    _ = (2 ^ 2) ^ 8 := card_Ssub (h := h)
    _ = 2 ^ 16 := by norm_num

private theorem u54_center {G : Type} [Group G] {L1 L2 S : Subgroup G}
    {K : Type} [Field K] {h : UnitaryFieldData 2 2 K}
    (ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(u5PtP h))
    (hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S))
    (hSUsub1 : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (hypProjUnitriangular h 2 1).subgroupOf (u5PtP h))
    (hperfPt1 : ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (perfectCore (u5PtP h)).subgroupOf (u5PtP h))
    (hcoreP1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1)
    (hUPt : hypProjUnitriangular h 2 1 ≤ u5PtP h) :
    centerOf S ≤ Subgroup.centralizer (L1 : Set G) := by
  have hcentPt : centerOf (perfectCore (u5PtP h)) = centerOf (hypProjUnitriangular h 2 1) :=
    centerOf_perfectCore_u5PtP_eq_centerOf_U h
  have hcenterS : centerOf (S.subgroupOf (L1 ⊔ bigB L1 L2 S)) =
      (centerOf S).subgroupOf (L1 ⊔ bigB L1 L2 S) := by
    apply Subgroup.map_injective (f := (L1 ⊔ bigB L1 L2 S).subtype)
      (L1 ⊔ bigB L1 L2 S).subtype_injective
    rw [map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hSylP1.1]
    exact (Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hSylP1.1)).symm
  have hcenterU : centerOf ((hypProjUnitriangular h 2 1).subgroupOf (u5PtP h)) =
      (centerOf (hypProjUnitriangular h 2 1)).subgroupOf (u5PtP h) := by
    apply Subgroup.map_injective (f := (u5PtP h).subtype) (u5PtP h).subtype_injective
    rw [map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hUPt]
    exact (Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hUPt)).symm
  have hcenterMap : ((centerOf S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (centerOf (hypProjUnitriangular h 2 1)).subgroupOf (u5PtP h) := by
    have h := CFSG.Quasithin.H13.Sec53F.Yam.centerOf_map_equiv ψ1
      (S.subgroupOf (L1 ⊔ bigB L1 L2 S))
    rw [hSUsub1, hcenterS, hcenterU] at h
    exact h.symm
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hzP1 : z ∈ L1 ⊔ bigB L1 L2 S := hSylP1.1 hz.1
  have hlP1 : l ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_left hl
  let z' : ↥(L1 ⊔ bigB L1 L2 S) := ⟨z, hzP1⟩
  let l' : ↥(L1 ⊔ bigB L1 L2 S) := ⟨l, hlP1⟩
  have hzCenter : ψ1 z' ∈ (centerOf (hypProjUnitriangular h 2 1)).subgroupOf (u5PtP h) := by
    have hmem : ψ1 z' ∈ ((centerOf S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom :=
      (Subgroup.mem_map (f := ψ1.toMonoidHom)).2
        ⟨z', (Subgroup.mem_subgroupOf (h := z')).2 (by simpa using hz), rfl⟩
    rwa [hcenterMap] at hmem
  have hlPerf : ψ1 l' ∈ (perfectCore (u5PtP h)).subgroupOf (u5PtP h) := by
    have hlPerf1 : l ∈ perfectCore (L1 ⊔ bigB L1 L2 S) := by rw [hcoreP1]; exact hl
    have hmem : ψ1 l' ∈ ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom :=
      (Subgroup.mem_map (f := ψ1.toMonoidHom)).2
        ⟨l', (Subgroup.mem_subgroupOf (h := l')).2 (by simpa using hlPerf1), rfl⟩
    rwa [hperfPt1] at hmem
  have hzC : ((ψ1 z' : ↥(u5PtP h)) : hypPSU h 2 1) ∈
      Subgroup.centralizer (perfectCore (u5PtP h) : Set (hypPSU h 2 1)) := by
    have h1 : ψ1 z' ∈ (centerOf (perfectCore (u5PtP h))).subgroupOf (u5PtP h) := by
      rw [hcentPt]
      exact hzCenter
    exact (Subgroup.mem_subgroupOf.1 h1).2
  have hlPerf' : ((ψ1 l' : ↥(u5PtP h)) : hypPSU h 2 1) ∈ perfectCore (u5PtP h) :=
    Subgroup.mem_subgroupOf.1 hlPerf
  have hcomm := Subgroup.mem_centralizer_iff.1 hzC _ hlPerf'
  have hpsi : ψ1 (l' * z') = ψ1 (z' * l') := by
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact hcomm
  have hcomm' : l' * z' = z' * l' := ψ1.injective hpsi
  simpa using congrArg Subtype.val hcomm'

theorem y9U54 : Y9U54 := by
  intro G _ _ L1 L2 S hF hSU hL2 hA
  classical
  obtain ⟨D⟩ := u54_vertices hF hSU hA
  letI := D.fieldK
  have hR111 : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hmdl := u54_model_data D.h
  have hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := (leafSylowS (G := G) hR111).2.1
  have hSylP2 : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) := by
    have h := (leafSylowS (G := G) hR111.symm).2.1
    rwa [bigB_comm] at h
  have hBimgN1 : (((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map
      D.ψ1.toMonoidHom).map (u5PtP D.h).subtype = u5PtP D.h ⊓ u5LnP D.h := by
    rw [D.hBimg1, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hBimgN2 : (((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map
      D.ψ2.toMonoidHom).map (u5LnP D.h).subtype = u5PtP D.h ⊓ u5LnP D.h := by
    rw [D.hBimg2, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hSUsub1 := u54_S_image_of D.ψ1 hBimgN1 hSylP1
    (le_sup_right : S ≤ bigB L1 L2 S) hmdl.2.2.1
  obtain ⟨hperfPt1, hSleCore1⟩ := u54_perfectCore_of D.ψ1 hSUsub1 hSylP1.1
    (U_le_perfectCore_u5PtP (h := D.h) (by norm_num))
  have hSUsub2 := u54_S_image_of D.ψ2 hBimgN2 hSylP2
    (le_sup_right : S ≤ bigB L1 L2 S) hmdl.2.2.2
  obtain ⟨-, hSleCore2⟩ := u54_perfectCore_of D.ψ2 hSUsub2 hSylP2.1
    (U_le_perfectCore_u5LnP (h := D.h) (by norm_num))
  obtain ⟨hcoreP1, hL1perf⟩ := u54_perfect_left hF hSU hSleCore1
  obtain ⟨hcoreP2, hL2perf⟩ := u54_perfect_right hF hL2 hSleCore2
  have hPO : PerfectOver L1 L2 S :=
    ⟨perfectCore_eq_self_of_perfect hL1perf, perfectCore_eq_self_of_perfect hL2perf,
      hcoreP1 ▸ hSleCore1, hcoreP2 ▸ hSleCore2⟩
  exact ⟨u54_center D.ψ1 hSylP1 hSUsub1 hperfPt1 hcoreP1 hmdl.1,
    u54_special hF hSylP1 hPO.2.2.1 D.ψ1 hperfPt1 hcoreP1,
    u54_card D.ψ2, hPO⟩

end CFSG.Quasithin.Stroth
