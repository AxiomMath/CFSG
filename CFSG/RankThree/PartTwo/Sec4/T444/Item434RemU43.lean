module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43K3
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Cover
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import Certificates.Certificate9574
public import Certificates.Certificate9575
public import Certificates.Certificate9576
public import Certificates.Certificate9577
public import Certificates.Certificate9578
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverGen

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Item434Kit Item434Alt

namespace Item434RemU43

theorem uSylCheck_true : uSylCheck = true :=
  Certificates.certificate9574

theorem uClassCheck_true : uClassCheck = true :=
  Certificates.certificate9575

theorem uPairCheck_true : uPairCheck = true :=
  Certificates.certificate9576

theorem uBadCheck_true : uBadCheck = true :=
  Certificates.certificate9578

theorem uCoverAll_true : uCoverAll = true :=
  Certificates.certificate9577

noncomputable def projSUEquivUX : projSU 4 3 1 ≃* UX :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (projSUEquivStatedProj 4 3 1).trans
    (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 4)
        (CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (K := GaloisField 3 (2 * 1))
          (L := CFSG.LieType.Multipliers.U43.F9) (by
            rw [GaloisField.card 3 (2 * 1) (by norm_num), Nat.card_eq_fintype_card,
              CFSG.LieType.Multipliers.U43.F9.card_eq]
            norm_num)))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU _ 4 (3 ^ 1))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars _))

open Item434RemU43

attribute [local irreducible] sAt

theorem card_map_piU_of_elemAbelian {E : Subgroup SUg} (hE : IsElemAbelian 3 E) :
    Nat.card (E.map piU) = Nat.card E := by
  have hinj : Function.Injective (piU.comp E.subtype) := fun a b hab =>
    Subtype.ext (piU_injOn_order3 (hE.2 a a.2) (hE.2 b b.2) hab)
  have hmap : E.map piU = (piU.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

@[expose] def K2Data (P : Subgroup UX) : Prop :=
  ∃ B E : Subgroup UX, B ≤ P ∧ 9 ≤ Nat.card B ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
    ∀ b ∈ B, ∀ d ∈ E, b * d = d * b

theorem k2Data_of_pull {P : Subgroup UX} {g : UX} {Pt : Subgroup SUg}
    (hmap : P.map (MulAut.conj g).toMonoidHom = Pt.map piU) {B' E' : Subgroup SUg}
    (hB'e : IsElemAbelian 3 B') (hB'Pt : B' ≤ Pt) (hB'9 : 9 ≤ Nat.card B')
    (hE'e : IsElemAbelian 3 E') (hE'81 : 81 ≤ Nat.card E')
    (hcomm : ∀ b ∈ B', ∀ d ∈ E', b * d = d * b) : K2Data P := by
  refine ⟨(B'.map piU).map (MulAut.conj g⁻¹).toMonoidHom,
    (E'.map piU).map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : B'.map piU ≤ P.map (MulAut.conj g).toMonoidHom := hmap ▸ Subgroup.map_mono hB'Pt
    have h2 := Item434AltPerm.map_conj_map_conj_inv P g⁻¹
    rw [inv_inv] at h2
    calc (B'.map piU).map (MulAut.conj g⁻¹).toMonoidHom
        ≤ (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
          Subgroup.map_mono h1
      _ = P := h2
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      card_map_piU_of_elemAbelian hB'e]
    exact hB'9
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hE'e)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      card_map_piU_of_elemAbelian hE'e]
    exact hE'81
  · rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩ _ ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩
    change MulAut.conj g⁻¹ (piU β) * MulAut.conj g⁻¹ (piU δ) =
      MulAut.conj g⁻¹ (piU δ) * MulAut.conj g⁻¹ (piU β)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm β hβ δ hδ]

theorem conj_closure_pair_le {g0 g1 w : SUg} {R : Subgroup SUg} (h0 : w * g0 * w⁻¹ ∈ R)
    (h1 : w * g1 * w⁻¹ ∈ R) :
    ∀ y ∈ Subgroup.closure ({g0, g1} : Set SUg), w * y * w⁻¹ ∈ R := by
  have hle : Subgroup.closure ({g0, g1} : Set SUg) ≤ R.comap (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact h0
    · rw [hx]; exact h1
  exact fun y hy => hle hy

theorem k2Data_good (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {P : Subgroup UX}
    {g : UX} {Pt : Subgroup SUg} (hPte : IsElemAbelian 3 Pt)
    (hmap : P.map (MulAut.conj g).toMonoidHom = Pt.map piU) {h u v : SUg} (hu : u ∈ Pt)
    (hv : v ∈ Pt) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvu : v ≠ u) (hvu2 : v ≠ u * u)
    (hhu : h * u * h⁻¹ ∈ rtS) (hhv : h * v * h⁻¹ ∈ rtS) : K2Data P := by
  have hPab : ∀ a ∈ Pt, ∀ b ∈ Pt, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPte.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hu3 := hPte.2 u hu
  have hv3 := hPte.2 v hv
  have hnot : v ∉ Subgroup.zpowers u :=
    Asc83Table.not_mem_zpowers_of_ne hu3 hv1 hvu (by rw [pow_two]; exact hvu2)
  have hB9 : Nat.card (Subgroup.closure ({u, v} : Set SUg)) = 9 :=
    Asc83Table.card_closure_pair_eq_nine hu3 hv3 (hPab u hu v hv) hu1 hnot
  have hBPt : Subgroup.closure ({u, v} : Set SUg) ≤ Pt := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hv
  have hBe : IsElemAbelian 3 (Subgroup.closure ({u, v} : Set SUg)) :=
    Sec5.isElemAbelian_of_le hPte hBPt
  have hEe : IsElemAbelian 3 (rtS.map (MulAut.conj h⁻¹).toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
      (rtS_isElemAbelian hsyl hrt)
  have hE81 : 81 ≤ Nat.card (rtS.map (MulAut.conj h⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact card_rtS hsyl hrt
  refine k2Data_of_pull hmap hBe hBPt (by rw [hB9]) hEe hE81 ?_
  rintro b hb _ ⟨r, hr, rfl⟩
  have hbr : h * b * h⁻¹ ∈ rtS := conj_closure_pair_le hhu hhv b hb
  have hcm : (h * b * h⁻¹) * r = r * (h * b * h⁻¹) :=
    congrArg Subtype.val ((rtS_isElemAbelian hsyl hrt).1.is_comm.comm ⟨_, hbr⟩ ⟨r, hr⟩)
  change b * (h⁻¹ * r * h⁻¹⁻¹) = (h⁻¹ * r * h⁻¹⁻¹) * b
  calc b * (h⁻¹ * r * h⁻¹⁻¹) = h⁻¹ * ((h * b * h⁻¹) * r) * h := by group
    _ = h⁻¹ * (r * (h * b * h⁻¹)) * h := by rw [hcm]
    _ = (h⁻¹ * r * h⁻¹⁻¹) * b := by group

theorem isElemAbelian_closure_union {P : Subgroup SUg} {z : SUg} (hP : IsElemAbelian 3 P)
    (hz3 : z ^ 3 = 1) (hzc : ∀ x ∈ P, x * z = z * x) :
    IsElemAbelian 3 (Subgroup.closure ((P : Set SUg) ∪ {z})) := by
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine Item434SporE81.isElemAbelian_closure_of_comm ?_ ?_
  · intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hPab x hx y hy
    · have hy' : y = z := hy
      rw [hy']
      exact hzc x hx
    · have hx' : x = z := hx
      rw [hx']
      exact (hzc y hy).symm
    · have hx' : x = z := hx
      have hy' : y = z := hy
      rw [hx', hy']
      exact Commute.refl _
  · rintro x (hx | hx)
    · exact hP.2 x hx
    · have hx' : x = z := hx
      rw [hx']
      exact hz3

theorem le_card_closure_union {P : Subgroup SUg} {z : SUg} (hP27 : Nat.card P = 27)
    (hE : IsElemAbelian 3 (Subgroup.closure ((P : Set SUg) ∪ {z}))) (hz : z ∉ P) :
    81 ≤ Nat.card (Subgroup.closure ((P : Set SUg) ∪ {z})) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPE : P ≤ Subgroup.closure ((P : Set SUg) ∪ {z}) := fun x hx =>
    Subgroup.subset_closure (Or.inl hx)
  have hzE : z ∈ Subgroup.closure ((P : Set SUg) ∪ {z}) := Subgroup.subset_closure (Or.inr rfl)
  have hEp : IsPGroup 3 (Subgroup.closure ((P : Set SUg) ∪ {z})) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hdvd : 27 ∣ Nat.card (Subgroup.closure ((P : Set SUg) ∪ {z})) :=
    hP27 ▸ Subgroup.card_dvd_of_le hPE
  have hne : Nat.card (Subgroup.closure ((P : Set SUg) ∪ {z})) ≠ 27 := by
    intro h27
    have := Subgroup.eq_of_le_of_card_ge hPE (by rw [h27, hP27])
    exact hz (this ▸ hzE)
  rw [hk] at hdvd hne ⊢
  have h3k : 3 ^ 3 ∣ 3 ^ k := by simpa using hdvd
  have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3k
  have hk4 : 4 ≤ k := by
    by_contra hlt
    exact hne (by rw [show k = 3 by omega]; norm_num)
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4

theorem k2Data_notin (hsyl : uSylCheck = true) (hz : uZCheck = true) {P : Subgroup UX}
    {g : UX} {Pt : Subgroup SUg} (hPt : Pt ≤ sylS) (hPte : IsElemAbelian 3 Pt)
    (hPt27 : Nat.card Pt = 27) (hmap : P.map (MulAut.conj g).toMonoidHom = Pt.map piU)
    (hnot : sAt uZ ∉ Pt) : K2Data P := by
  obtain ⟨hzlt, hz1, hz3, hzcen⟩ := uZ_spec hsyl hz
  have hEe := isElemAbelian_closure_union hPte hz3 (fun x hx => hzcen x (hPt hx))
  have hE81 := le_card_closure_union hPt27 hEe hnot
  have hPE : Pt ≤ Subgroup.closure ((Pt : Set SUg) ∪ {sAt uZ}) := fun x hx =>
    Subgroup.subset_closure (Or.inl hx)
  exact k2Data_of_pull hmap hPte le_rfl (by rw [hPt27]; norm_num) hEe hE81
    (fun b hb d hd => congrArg Subtype.val (hEe.1.is_comm.comm ⟨b, hPE hb⟩ ⟨d, hd⟩))

theorem e27_cases (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hpair : uPairCheck = true) (hbad : uBadCheck = true) (hZ : Subgroup.center UX = ⊥)
    {P : Subgroup UX} (hPe : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    K2Data P ∨ Item434SporGen.NoSignalizer P := by
  obtain ⟨g, Pt, hPt, hPte, hPt27, hmap⟩ := exists_conj_elemAbelian hsyl hPe hP27
  obtain ⟨hrt, -, -, -, hzc⟩ := uClassCheck_parts hcls
  by_cases hz : sAt uZ ∈ Pt
  · rcases pair_dichotomy hsyl hcls hpair hbad hPt hPte hPt27 hz with
      ⟨h, u, hu, v, hv, hu1, hv1, hvu, hvu2, hhu, hhv⟩ | ⟨k, hk, ha, hb⟩
    · exact Or.inl (k2Data_good hsyl hrt hPte hmap hu hv hu1 hv1 hvu hvu2 hhu hhv)
    · right
      have hN := noSignalizer_bad hsyl hcls hbad hZ hk
      have hle : (Subgroup.closure ({sAt uZ, sAt ((badTriple k).getD 1 0),
          sAt ((badTriple k).getD 2 0)} : Set SUg)).map piU ≤ Pt.map piU := by
        apply Subgroup.map_mono
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx
        · rw [hx]; exact hz
        · rw [hx]; exact ha
        · rw [hx]; exact hb
      have hN' := (NoSignalizer.mono hle hN).map_conj g⁻¹
      have e : (Pt.map piU).map (MulAut.conj g⁻¹).toMonoidHom = P := by
        rw [← hmap]
        have := Item434AltPerm.map_conj_map_conj_inv P g⁻¹
        rwa [inv_inv] at this
      rwa [e] at hN'
  · exact Or.inl (k2Data_notin hsyl hzc hPt hPte hPt27 hmap hz)

theorem false_of_card_27 {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434Core G A M Q) (e : layer G ⧸ Subgroup.center (layer G) ≃* UX)
    (hcen : Subgroup.center UX = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer UX))
    (hE : ∀ P : Subgroup UX, IsElemAbelian 3 P → Nat.card P = 27 →
      K2Data P ∨ Item434SporGen.NoSignalizer P)
    (hZ : Subgroup.center (layer G) = ⊥) (h27 : Nat.card h.layerStar = 27) : False := by
  have h27' : Nat.card (A.map (quotConj e)) = 27 := by
    rw [Item434Spor.card_map_quotConj h e]
    exact h27
  set P := (A.map (quotConj e)).comap (MulAut.conj : UX →* MulAut UX) with hPdef
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h27']
  have hPe : IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e)
  rcases hE P hPe hP27 with ⟨B, E, hBP, hB9, hEe, hE81, hBE⟩ | hN
  · exact Item434SporE81.false_of_e81 h hZ e hcen hPmap hBP hB9 hEe hE81 hBE
  · exact false_of_normalizer h e fun Y hY3 hAY => hN Y hY3 (hPmap ▸ hAY)

theorem exists_E27 {Y : Type*} [Group Y] [Finite Y] {W : Subgroup Y}
    (hW : IsElemAbelian 3 W) (h27 : 27 ≤ Nat.card W) :
    ∃ D : Subgroup Y, D ≤ W ∧ IsElemAbelian 3 D ∧ Nat.card D = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hW).exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := W) (n := 3)
    (by rw [hk]; exact pow_dvd_pow 3 hk3)
  refine ⟨K.map W.subtype, Subgroup.map_subtype_le K,
    Sec5.isElemAbelian_of_le hW (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective W.subtype_injective, hK]
  norm_num

theorem exists_E27_UX (hsyl : uSylCheck = true) (hrt : uRtCheck = true) :
    ∃ D : Subgroup UX, IsElemAbelian 3 D ∧ Nat.card D = 27 := by
  have hRe : IsElemAbelian 3 (rtS.map piU) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ (rtS_isElemAbelian hsyl hrt)
  have h81 : 81 ≤ Nat.card (rtS.map piU) := by
    rw [card_map_piU_of_le hsyl (rtS_le_sylS hsyl hrt)]
    exact card_rtS hsyl hrt
  obtain ⟨D, -, hD, hD27⟩ := exists_E27 hRe (by omega)
  exact ⟨D, hD, hD27⟩

theorem not_three_dvd_outer_UX : ¬ 3 ∣ Nat.card (Outer UX) := by
  have h := outU43_holds
  rwa [Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence projSUEquivUX).toEquiv] at h

theorem false_of_projSU_four_three
    {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 4 3 1) : False := by
  have hsyl := uSylCheck_true
  have hcls := uClassCheck_true
  have hpair := uPairCheck_true
  have hbad := uBadCheck_true
  have hcover := uCoverAll_true
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* UX := e₀.trans projSUEquivUX with hθ
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := h.isQuasisimple.2.1
  have : IsSimpleGroup UX := θ.symm.isSimpleGroup
  have hcen : Subgroup.center UX = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [card_UX]; norm_num)
  have hout := not_three_dvd_outer_UX
  obtain ⟨hrt, -, -, -, -⟩ := uClassCheck_parts hcls
  by_cases hZ : Subgroup.center (layer G) = ⊥
  · rcases h.card_layerStar with h9 | ⟨h27, -⟩
    · obtain ⟨D, hD, hD27⟩ := exists_E27_UX hsyl hrt
      exact Item434Spor.false_of_card_nine h hZ θ hD hD27 h9
    · exact false_of_card_27 h θ hcen hout
        (fun P hPe hP27 => e27_cases hsyl hcls hpair hbad hcen hPe hP27) hZ h27
  · exact Item434Cover.false_of_cover_gen h θ hcen hout hZ (hX_UX hsyl hcls hcover)

end Item434RemU43

section Families


theorem item434CharThreeU4 :
    Item434CharThreeU4 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (Item434RemU43.false_of_projSU_four_three hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
