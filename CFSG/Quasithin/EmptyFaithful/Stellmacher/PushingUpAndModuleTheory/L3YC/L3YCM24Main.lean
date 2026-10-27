module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCM24Trio
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCM24Z4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCClassIIRows
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.G64SymCase
public import CFSG.Quasithin.EmptyFaithful.Insp9Basic
public import CFSG.Quasithin.EmptyFaithful.Insp9Case
public import CFSG.Quasithin.EmptyFaithful.Insp9Ord
public import CFSG.Quasithin.EmptyFaithful.LRed6Real
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y20
public import CFSG.Quasithin.EmptyFaithful.S152Y21
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D54
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.S153F18C
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.S153IClose
public import CFSG.Quasithin.EmptyFaithful.SBd4B1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRows
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.MS93.ASC132
public import CFSG.Quasithin.MS93.ASC134C5
public import CFSG.Quasithin.MS93.ASC134Ord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecBFacts
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.Stellmacher.PU.L3YC.M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.Quasithin.A312M24
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section Kernel


@[expose] noncomputable def Kg : Subgroup G24 := rho2.ker.map Z2.subtype

theorem mem_Kg_iff {g : G24} : g ∈ Kg ↔ ∃ h : g ∈ Z2, rho2 ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem Kg_le_Z2 : Kg ≤ Z2 := fun _ hg => (mem_Kg_iff.mp hg).1

theorem card_Kg [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : Nat.card Kg = 10752 := by
  rw [Kg, ← card_rho2.2]
  exact (Nat.card_congr (rho2.ker.equivMapOfInjective Z2.subtype Z2.subtype_injective).toEquiv).symm

theorem Z2_le_normalizer_Kg : Z2 ≤ Subgroup.normalizer (Kg : Set G24) := by
  have h : Kg.subgroupOf Z2 = rho2.ker :=
    Subgroup.comap_map_eq_self_of_injective Z2.subtype_injective rho2.ker
  have hn : (Kg.subgroupOf Z2).Normal := by
    rw [h]
    exact rho2.normal_ker
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer Kg_le_Z2).mp hn

end Kernel

section Octads

@[expose] def oct0 : Finset ℕ := [0, 2, 3, 7, 10, 15, 17, 21].toFinset

@[expose] def oct1 : Finset ℕ := [1, 4, 5, 6, 8, 9, 12, 18].toFinset

@[expose] def oct2 : Finset ℕ := [11, 13, 14, 16, 19, 20, 22, 23].toFinset

theorem T2_eq : T2 = [oct0, oct1, oct2] := rfl

theorem omega_oct0 : omega • oct0 = oct1 ∨ omega • oct0 = oct2 := by
  rw [hact_set, tab_omega]
  decide +kernel

theorem V6_witness :
    ∃ v ∈ V6, (∀ p ∈ oct0, v • p = p) ∧ (∃ p ∈ oct1, v • p ≠ p) ∧ (∃ p ∈ oct2, v • p ≠ p) := by
  obtain ⟨-, -, hreach⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective
    (wordG m24Sg V6w) enumV6
  have hw : ∃ t ∈ V6L, (∀ p ∈ [0, 2, 3, 7, 10, 15, 17, 21], t.getD p p = p) ∧
      (∃ p ∈ [1, 4, 5, 6, 8, 9, 12, 18], t.getD p p ≠ p) ∧
      (∃ p ∈ [11, 13, 14, 16, 19, 20, 22, 23], t.getD p p ≠ p) := by
    decide +kernel
  obtain ⟨t, ht, h0, ⟨p1, hp1, hp1'⟩, ⟨p2, hp2, hp2'⟩⟩ := hw
  obtain ⟨v, hv, hvt⟩ := hreach t ht
  refine ⟨v, hv, fun p hp => ?_, ⟨p1, ?_, ?_⟩, ⟨p2, ?_, ?_⟩⟩
  · rw [oct0, List.mem_toFinset] at hp
    rw [smul_nat, hvt]
    exact h0 p hp
  · rw [oct1, List.mem_toFinset]; exact hp1
  · rw [smul_nat, hvt]; exact hp1'
  · rw [oct2, List.mem_toFinset]; exact hp2
  · rw [smul_nat, hvt]; exact hp2'

end Octads

section Main


theorem eq_Kg [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup G24} (hperf : ⁅B, B⁆ = B)
    (hN : m24CtxE.S ≤ Subgroup.normalizer (B : Set G24)) (hcard : Nat.card B = 10752) :
    B = Kg := by
  have hBZ6 : B ≤ Z6 := (sup_S_eq_Z6 hperf hN hcard) ▸ le_sup_left
  have hBZ2 : B ≤ Z2 := hBZ6.trans Z6_le_Z2
  have hBA : B ≤ perfectCore Z2 := le_perfectCore_of_perfect hBZ2 hperf
  have : Group.IsSolvable (Equiv.Perm (Fin T2.length)) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  have hle : B ≤ Kg := fun b hb =>
    mem_Kg_iff.mpr ⟨hBZ2 hb, map_eq_one_of_mem_perfectCore rho2 (hBZ2 hb) (hBA hb)⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Kg, hcard])

theorem octad_fixed {b : G24} (hb : b ∈ Kg) : ∀ x ∈ T2, b • x = x := by
  intro x hx
  obtain ⟨hbZ, hb1⟩ := mem_Kg_iff.mp hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have := listHom_spec Z2 T2 T2_nodup Z2_inv ⟨b, hbZ⟩ ⟨i, hi⟩
  rw [show listHom Z2 T2 T2_nodup Z2_inv ⟨b, hbZ⟩ = 1 from hb1] at this
  exact this.symm

theorem no_b_acts_as_omega {b : G24} (hb : b ∈ Kg)
    (h : ∀ v ∈ V6, omega * v * omega⁻¹ = b * v * b⁻¹) : False := by
  obtain ⟨v, hvV, hv0, ⟨p1, hp1, hp1'⟩, ⟨p2, hp2, hp2'⟩⟩ := V6_witness
  have hv := h v hvV
  have hcomm : (b⁻¹ * omega) * v = v * (b⁻¹ * omega) := by
    calc (b⁻¹ * omega) * v = b⁻¹ * (omega * v * omega⁻¹) * omega := by group
      _ = b⁻¹ * (b * v * b⁻¹) * omega := by rw [hv]
      _ = v * (b⁻¹ * omega) := by group
  have hbinv : ∀ x ∈ T2, b⁻¹ • x = x := fun x hx => by
    rw [inv_smul_eq_iff]
    exact (octad_fixed hb x hx).symm
  have hfix : ∀ p ∈ (b⁻¹ * omega) • oct0, v • p = p := by
    intro p hp
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_smul_finset.mp hp
    calc v • ((b⁻¹ * omega) • p0) = (v * (b⁻¹ * omega)) • p0 := (mul_smul _ _ _).symm
      _ = ((b⁻¹ * omega) * v) • p0 := by rw [hcomm]
      _ = (b⁻¹ * omega) • (v • p0) := mul_smul _ _ _
      _ = (b⁻¹ * omega) • p0 := by rw [hv0 p0 hp0]
  have hy : (b⁻¹ * omega) • oct0 = omega • oct0 := by
    rw [mul_smul]
    have hmem : omega • oct0 ∈ T2 := by
      rcases omega_oct0 with h1 | h1 <;> rw [h1] <;> simp [T2_eq]
    exact hbinv _ hmem
  rw [hy] at hfix
  rcases omega_oct0 with h1 | h1
  · rw [h1] at hfix
    exact hp1' (hfix p1 hp1)
  · rw [h1] at hfix
    exact hp2' (hfix p2 hp2)

end Main

section PCore


theorem V6_fix_oct : ∀ v ∈ V6, ∀ x ∈ T2, v • x = x := by
  refine fix_of_gens _ T2 (fun g hg x hx => ?_)
  have hgT : tab 24 g ∈ V6T := by rw [← V6g_tab]; exact List.mem_map_of_mem hg
  rw [hact_set]
  have : ∀ t ∈ V6T, ∀ x ∈ T2, actSet t x = x := by decide +kernel
  exact this _ hgT x hx

theorem V6_le_Kg [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : V6 ≤ Kg := fun v hv =>
  mem_Kg_iff.mpr ⟨V6_le_Z6.trans Z6_le_Z2 hv,
    listHom_eq_one_of_fix Z2 T2 T2_nodup Z2_inv _ (V6_fix_oct v hv)⟩

theorem y6_mem_Kg [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : y6 ∈ Kg := by
  have hz : y6 ∈ Z2 := Z6_le_Z2 y6_mem
  refine mem_Kg_iff.mpr ⟨hz, ?_⟩
  have h7 : (rho2 ⟨y6, hz⟩) ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨y6, hz⟩ : ↥Z2) ^ 7 = 1 := Subtype.ext (by simpa using y6_pow)
    rw [this, map_one]
  have hperm : Nat.card (Equiv.Perm (Fin T2.length)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hd6 : orderOf (rho2 ⟨y6, hz⟩) ∣ 6 := hperm ▸ orderOf_dvd_natCard _
  have hd7 : orderOf (rho2 ⟨y6, hz⟩) ∣ 7 := orderOf_dvd_of_pow_eq_one h7
  have : orderOf (rho2 ⟨y6, hz⟩) ∣ Nat.gcd 6 7 := Nat.dvd_gcd hd6 hd7
  have h1 : orderOf (rho2 ⟨y6, hz⟩) = 1 := by
    have : Nat.gcd 6 7 = 1 := by norm_num
    rw [this] at *
    exact Nat.dvd_one.mp ‹_›
  exact orderOf_eq_one_iff.mp h1

theorem isPGroup_V6 : IsPGroup 2 V6 := IsPGroup.of_card (by rw [card_V6])

theorem V6_le_pCore {B : Subgroup G24} (hBZ6 : B ≤ Z6) (hVB : V6 ≤ B) :
    V6.subgroupOf B ≤ CFSG.pCore 2 ↥B := by
  have hnorm : (V6.subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hBZ6.trans Z6_normalizes_V6)
  have hp : IsPGroup 2 ↥(V6.subgroupOf B) :=
    isPGroup_V6.of_equiv (Subgroup.subgroupOfEquivOfLe hVB).symm
  exact le_sSup ⟨hnorm, hp⟩

end PCore

section Final

theorem pCore_le_of_simple_quot {B : Type} [Group B] [Finite B] (V : Subgroup B) [V.Normal]
    (hS : IsSimpleGroup (B ⧸ V)) (hQ : Nat.card (B ⧸ V) = 168) : CFSG.pCore 2 B ≤ V := by
  have hN : ((CFSG.pCore 2 B).map (QuotientGroup.mk' V)).Normal :=
    (CFSG.pCore_normal (p := 2) (G := B)).map _ (QuotientGroup.mk'_surjective V)
  have hp : IsPGroup 2 ↥((CFSG.pCore 2 B).map (QuotientGroup.mk' V)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := B)).map _
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS _ hN with h | h
  · intro x hx
    have : QuotientGroup.mk' V x ∈ (CFSG.pCore 2 B).map (QuotientGroup.mk' V) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    rw [h] at hp
    have hpq : IsPGroup 2 (B ⧸ V) := hp.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hpq
    rw [hQ] at hk
    have : (168 : ℕ) = 2 ^ k := hk
    have h8 : k < 8 := by
      by_contra hk8
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> omega

end Final

section Native


theorem m24_row14_native [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup G24} (hperf : ⁅B, B⁆ = B)
    (hN : m24CtxE.S ≤ Subgroup.normalizer (B : Set G24))
    (hext : IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y)) :
    ∃ ω : G24, ω ∈ Subgroup.normalizer (B : Set G24) ∧ ω ^ 3 = 1 ∧
      (∀ b ∈ B, ∃ q ∈ (CFSG.pCore 2 ↥B).map B.subtype, ω * q * ω⁻¹ ≠ b * q * b⁻¹) ∧
      ⁅CFSG.pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆ = CFSG.pCore 2 ↥B := by
  obtain ⟨V, hVn, hVE, hVQ⟩ := hext
  have hVcard : Nat.card V = 64 := by
    obtain ⟨e⟩ := hVE
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hcardB : Nat.card B = 10752 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hVcard,
      Stellmacher.PU.L3YC.card_L32 hVQ]
  have hBK : B = Kg := eq_Kg hperf hN hcardB
  have hBZ6 : B ≤ Z6 := (sup_S_eq_Z6 hperf hN hcardB) ▸ le_sup_left
  have hVB : V6 ≤ B := hBK ▸ V6_le_Kg
  have hP1 := V6_le_pCore hBZ6 hVB
  refine ⟨omega, hBK ▸ Z2_le_normalizer_Kg omega_mem, omega_pow_three, ?_, ?_⟩
  · intro b hb
    by_contra hcon
    push Not at hcon
    refine no_b_acts_as_omega (hBK ▸ hb) fun v hv => hcon v ?_
    exact ⟨⟨v, hVB hv⟩, hP1 (by simpa [Subgroup.mem_subgroupOf] using hv), rfl⟩
  ·
    have hsimple : IsSimpleGroup (↥B ⧸ V) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hVQ).2
    have hQ : Nat.card (↥B ⧸ V) = 168 := Stellmacher.PU.L3YC.card_L32 hVQ
    have hle : CFSG.pCore 2 ↥B ≤ V := pCore_le_of_simple_quot V hsimple hQ
    have hV6card : Nat.card (V6.subgroupOf B) = 64 := by
      have h64 : Nat.card V6 = 64 := by rw [card_V6]; norm_num
      rw [← h64]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVB).toEquiv)
    have hPcard : Nat.card (CFSG.pCore 2 ↥B) ≤ 64 :=
      hVcard ▸ Subgroup.card_le_of_le hle
    have hPeq : V6.subgroupOf B = CFSG.pCore 2 ↥B :=
      Subgroup.eq_of_le_of_card_ge hP1 (by rw [hV6card]; exact hPcard)
    have hy6 : y6 ∈ B := hBK ▸ y6_mem_Kg
    refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
    rw [← hPeq]
    intro p hp
    have hpV : (p : G24) ∈ V6 := by simpa [Subgroup.mem_subgroupOf] using hp
    obtain ⟨x, hxV, hx⟩ := V6_comm _ hpV
    have hxB : x ∈ B := hVB hxV
    have hxP : (⟨x, hxB⟩ : ↥B) ∈ V6.subgroupOf B := by simpa [Subgroup.mem_subgroupOf] using hxV
    have hc := Subgroup.commutator_mem_commutator hxP (Subgroup.mem_top (⟨y6, hy6⟩ : ↥B))
    have : (⁅(⟨x, hxB⟩ : ↥B), ⟨y6, hy6⟩⁆ : ↥B) = p := by
      apply Subtype.ext
      simp [commutatorElement_def]
      simpa [commutatorElement_def] using hx
    rwa [this] at hc

end Native

end CFSG.Quasithin.Stellmacher.PU.L3YC.M24
