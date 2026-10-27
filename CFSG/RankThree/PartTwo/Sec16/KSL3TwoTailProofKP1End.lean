module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofKS
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Class
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Rad
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofBlock
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1624KP1

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open ProofKS1623Parab

variable {F : Type} [Field F]

theorem card_galoisField_two_zero' : Nat.card (GaloisField 2 0) = 2 :=
  CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_galoisField_two_zero

theorem card_radV : Nat.card (radV F) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (radUEquiv F).toEquiv]
  have e : radU F (flagSpace 3 F 2) ≃ (Fin 2 → F) :=
    { toFun := fun u => radCoord u.1
      invFun := fun w => ⟨uVec w, uVec_mem_radU w⟩
      left_inv := fun u => Subtype.ext (uVec_radCoord u.2)
      right_inv := fun w => radCoord_uVec w }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

theorem inSubgroup_perfectResidual_stabilizer_le :
    inSubgroup perfectResidual ((stabilizer (flagSpace 3 F 2)).map (proj 3 F)) ≤ parB F := by
  set P := (stabilizer (flagSpace 3 F 2)).map (proj 3 F) with hP
  have h1 : perfectResidual P ≤ commutator P := by
    rw [← derivedSeries_one]
    exact iInf_le _ 1
  have h2 : (commutator P).map P.subtype = ⁅P, P⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  calc inSubgroup perfectResidual P = (perfectResidual P).map P.subtype := rfl
    _ ≤ (commutator P).map P.subtype := Subgroup.map_mono h1
    _ = ⁅P, P⁆ := h2
    _ = (⁅stabilizer (flagSpace 3 F 2), stabilizer (flagSpace 3 F 2)⁆).map (proj 3 F) := by
        rw [hP, Subgroup.map_commutator]
    _ ≤ (parK F).map (proj 3 F) := Subgroup.map_mono commutator_stabilizer_le_parK

theorem eq_of_le_of_isPGroup {G : Type} [Group G] [Finite G] {L V X P : Subgroup G} {b : G}
    {m p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hD : Data1623 L b m p P V X) {R : Subgroup G}
    (hR : IsPGroup 2 R) (hVR : V ≤ R) (hRK : R ≤ kPara1623 L V)
    (hKR : kPara1623 L V ≤ Subgroup.normalizer (R : Set G)) : R = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kPara1623 L V with hKdef
  obtain ⟨hVn, ⟨e⟩⟩ := hD.quot
  set V' := V.subgroupOf K with hV'
  set R' := R.subgroupOf K with hR'
  have hR'n : R'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mpr hKR
  have hF4 : 4 ≤ Nat.card (GaloisField 2 m) := Proof1624KS.four_le_card_galoisField hp hp3 hD
  have hsimp : IsSimpleGroup (↥K ⧸ V') := by
    have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
    exact (e.trans (Sec4.projSLEquivPSL (GaloisField 2 m))).isSimpleGroup
  have hmapn : (R'.map (QuotientGroup.mk' V')).Normal :=
    hR'n.map _ (QuotientGroup.mk'_surjective V')
  rcases hmapn.eq_bot_or_eq_top with h1 | h1
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    refine le_antisymm (fun x hx => ?_) hVR
    have hx' : (⟨x, hRK hx⟩ : K) ∈ R' := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (h1 hx')
  · exfalso
    have hR'2 : IsPGroup 2 R' := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
    have hQ2 : IsPGroup 2 (↥K ⧸ V') := by
      intro z
      have hz : z ∈ R'.map (QuotientGroup.mk' V') := h1 ▸ Subgroup.mem_top z
      obtain ⟨r, hr, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hR'2 ⟨r, hr⟩
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have hk' : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [hk', map_one]
    have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2 * m) hD.card
    have hV'2 : IsPGroup 2 V' := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hD.le_V).symm
    have hpX : p ∣ Nat.card X := by rw [hD.card_X]
    have hpK : p ∣ Nat.card K := hpX.trans (Subgroup.card_dvd_of_le hD.le_K)
    have hpV : ¬ p ∣ Nat.card V' := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV'2
      rw [hk]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
      omega
    have hpQ : p ∣ Nat.card (↥K ⧸ V') := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V'
      rw [h1] at hpK
      exact (Nat.Prime.dvd_mul hp).mp hpK |>.resolve_right hpV
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
    rw [hk] at hpQ
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpQ)
    omega

theorem map_eq_map_map_symm {Y G : Type*} [Group Y] [Group G] (ι₀ : Y →* G) (α : Y ≃* Y)
    (H : Subgroup Y) : H.map ι₀ = (H.map α.toMonoidHom).map (ι₀.comp α.symm.toMonoidHom) := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp

end ProofKS1624KP1

open ProofKS1624KP1 ProofKS1623Parab Proof1623Para
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open CFSG.Assembly.RankThreeEven (projSL)

theorem ks1624ParaKP1 : KS1624ParaKP1 := by
  intro G _ _ L m' hm' hL b m p P V X hp hp3 hD
  obtain ⟨eL⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 m' with hFdef
  have hFc : Nat.card F = 2 ^ m' := GaloisField.card 2 m' (by omega)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2 * m) hD.card
  have hF4m := Proof1624KS.four_le_card_galoisField hp hp3 hD
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, card_galoisField_two_zero'] at hF4m
    omega
  have hVbot : V ≠ ⊥ := by
    intro h
    have hc := hD.card
    rw [h, Subgroup.card_bot] at hc
    have : 2 ^ 1 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set e0 : projectiveSL 3 F ≃* L :=
    (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 F).symm.trans eL.symm with he0
  set ι₀ : projectiveSL 3 F →* G := L.subtype.comp e0.toMonoidHom with hι₀
  have hι₀i : Function.Injective ι₀ := Subtype.val_injective.comp e0.injective
  have hι₀r : ι₀.range = L := by
    rw [hι₀, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e0.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨V0, rfl⟩ : ∃ V0 : Subgroup (projectiveSL 3 F), V0.map ι₀ = V :=
    ⟨V.comap ι₀, Subgroup.map_comap_eq_self (hι₀r ▸ hD.le_L)⟩
  have hKK0 : kPara1623 L (V0.map ι₀) =
      (inSubgroup perfectResidual (Subgroup.normalizer (V0 : Set (projectiveSL 3 F)))).map ι₀ := by
    rw [kPara1623, inf_normalizer_map_eq hι₀i hι₀r V0, inSubgroup_perfectResidual_map hι₀i]
  have hV0p : IsPGroup 2 V0 := hV2.of_equiv (V0.equivMapOfInjective ι₀ hι₀i).symm
  have hV0b : V0 ≠ ⊥ := by
    intro h
    apply hVbot
    rw [h, Subgroup.map_bot]
  obtain ⟨α, hα⟩ := exists_mulEquiv_normalizer_le hV0p hV0b
  set ι : projectiveSL 3 F →* G := ι₀.comp α.symm.toMonoidHom with hι
  have hιi : Function.Injective ι := hι₀i.comp α.symm.injective
  have hιr : ι.range = L := by
    rw [hι, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr α.symm.surjective,
      ← MonoidHom.range_eq_map, hι₀r]
  set R := V0.map α.toMonoidHom with hRdef
  have hNR : (Subgroup.normalizer (V0 : Set (projectiveSL 3 F))).map α.toMonoidHom =
      Subgroup.normalizer (R : Set (projectiveSL 3 F)) :=
    Subgroup.map_equiv_normalizer_eq V0 α
  set K1 := inSubgroup perfectResidual (Subgroup.normalizer (R : Set (projectiveSL 3 F)))
    with hK1def
  have hVR : V0.map ι₀ = R.map ι := map_eq_map_map_symm ι₀ α V0
  have hKK1 : kPara1623 L (V0.map ι₀) = K1.map ι := by
    rw [hKK0, map_eq_map_map_symm ι₀ α, ← inSubgroup_perfectResidual_map α.injective, hNR]
  have hperf : ⁅K1, K1⁆ = K1 := Sec18.commutator_inSubgroup_perfectResidual _
  have hK1N : K1 ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F)) := Subgroup.map_subtype_le _
  have hK1B : K1 ≤ parB F := by
    refine (Sec18.le_inSubgroup_perfectResidual hperf (hK1N.trans ?_)).trans
      inSubgroup_perfectResidual_stabilizer_le
    rw [← hNR]
    exact hα
  have hRK1 : R ≤ K1 := by
    have h1 := hD.le_V
    rw [hKK1, hVR] at h1
    exact (Subgroup.map_le_map_iff_of_injective hιi).mp h1
  have hRp : IsPGroup 2 R := hV0p.map α.toMonoidHom
  obtain ⟨x1, hx1, hx14⟩ : ∃ x1 ∈ K1, x1 ^ 4 ≠ 1 := by
    have hXb : X ≠ ⊥ := by
      intro h
      have hc := hD.card_X
      rw [h, Subgroup.card_bot] at hc
      have := hp.two_le
      omega
    obtain ⟨⟨x0, hx0X⟩, hx01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXb
    have hx0K : x0 ∈ K1.map ι := hKK1 ▸ hD.le_K hx0X
    obtain ⟨x1, hx1, rfl⟩ := hx0K
    refine ⟨x1, hx1, fun h4 => ?_⟩
    have hord : orderOf (⟨ι x1, hx0X⟩ : X) ∣ p := by
      rw [← hD.card_X]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp hord with h1 | h1
    · exact hx01 (orderOf_eq_one_iff.mp h1)
    · have h4' : (⟨ι x1, hx0X⟩ : X) ^ 4 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← map_pow, h4, map_one]; rfl)
      have := orderOf_dvd_of_pow_eq_one h4'
      rw [h1] at this
      have := Nat.le_of_dvd (by norm_num) this
      obtain rfl : p = 4 := by omega
      norm_num at hp
  have hRV : R ≤ radV F := le_radV_of_normalized hK1B hperf hx1 hx14 hRp (hRK1.trans hK1B) hK1N
  have hVK1 : radV F ≤ K1 := radV_le_of_le hRV hK1B hx1 hx14
  have hReq : R = radV F := by
    have h2 : IsPGroup 2 ((radV F).map ι) := by
      refine IsPGroup.map (fun u => ⟨1, Subtype.ext ?_⟩) ι
      rw [pow_one, Subgroup.coe_pow]
      exact sq_eq_one_of_mem_radV u.2
    have h3 := eq_of_le_of_isPGroup hp hp3 hD h2 (by rw [hVR]; exact Subgroup.map_mono hRV)
      (by rw [hKK1]; exact Subgroup.map_mono hVK1)
      (by
        rw [hKK1]
        exact (Subgroup.map_mono (hK1B.trans parB_le_normalizer_radV)).trans
          (Subgroup.le_normalizer_map ι))
    rw [hVR] at h3
    exact ((Subgroup.map_injective hιi) h3).symm
  have hF4 : 4 ≤ Nat.card F := by
    have h1 : Nat.card R = Nat.card (V0.map ι₀) := by
      rw [hVR]
      exact (Subgroup.card_map_of_injective hιi).symm
    rw [hReq, card_radV, hD.card] at h1
    have h2 : 4 ≤ 2 ^ m := by
      rw [← GaloisField.card 2 m hm0]
      exact hF4m
    have h3 : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h3] at h1
    have h4 : 4 ^ 2 ≤ Nat.card F ^ 2 := by
      rw [h1]
      exact Nat.pow_le_pow_left h2 2
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h4
  have hK1eq : K1 = parB F := by
    rw [hK1def, hReq, radV, normalizer_radU]
    exact perfectResidual_stabilizer_eq hF4
  rw [hKK1, hVR, hK1eq, hReq]
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one (F := F) (by omega)
  refine ⟨Sec15.Proof153Block.isShort_map_of_injective ι hιi
      (IsShort2.isShort (isShort2_parB hF4)),
    Sec15.Proof153Block.isTypeScriptL_map_of_injective ι hιi
      (Or.inl ⟨m', isLin2Type_parB hFc hF4⟩), ?_, ?_, ?_⟩
  · intro T hTL hT2 hKT
    obtain ⟨T0, rfl⟩ : ∃ T0 : Subgroup (projectiveSL 3 F), T0.map ι = T :=
      ⟨T.comap ι, Subgroup.map_comap_eq_self (hιr ▸ hTL)⟩
    have hT02 : IsPGroup 2 T0 := hT2.of_equiv (T0.equivMapOfInjective ι hιi).symm
    have hNT0 : parB F ≤ Subgroup.normalizer (T0 : Set (projectiveSL 3 F)) := by
      intro y hy
      have hyN := hKT ⟨y, hy, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      have h1 : ι (y * t * y⁻¹) ∈ T0.map ι := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hyN (ι t)).mp ⟨t, ht, rfl⟩
      obtain ⟨t', ht', hteq⟩ := h1
      rwa [← hιi hteq]
    exact Subgroup.map_mono (le_radV_of_isPGroup hT02 hNT0)
  · intro Y hKY hYL hYne
    obtain ⟨Y0, rfl⟩ : ∃ Y0 : Subgroup (projectiveSL 3 F), Y0.map ι = Y :=
      ⟨Y.comap ι, Subgroup.map_comap_eq_self (hιr ▸ hYL)⟩
    have hKY0 : parB F ≤ Y0 := (Subgroup.map_le_map_iff_of_injective hιi).mp hKY
    have hY0 : Y0 ≠ ⊤ := by
      rintro rfl
      apply hYne
      rw [← MonoidHom.range_eq_map, hιr]
    rw [inSubgroup_perfectResidual_map hιi, perfectResidual_eq_of_le hF4 hKY0 hY0]
  · rw [← Subgroup.map_commutator, commutator_radV_parB ht0 ht1]

end CFSG.RankThree.PartTwo.Sec16
