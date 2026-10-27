module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RJ2Lat
public import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Recognition.CertTwoLocal
public import CFSG.Quasithin.Recognition.F112J2Act
public import CFSG.Quasithin.Background.Q8D8Recognition
public import CFSG.Quasithin.EmptyFaithful.SzF53A2
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.Sporadic.J2.Setup
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotJ2
public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.C1PackSolvP
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.F112F53Res
public import CFSG.Quasithin.EmptyFaithful.F112RE
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152He9Y1
public import CFSG.Quasithin.Recognition.F112J2Reduce
public import CFSG.Quasithin.Recognition.F112RGold
public import CFSG.Quasithin.Recognition.F112TitsB2
public import CFSG.Quasithin.Recognition.F112TitsFrob
public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.Recognition.F112WKernel
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.Quasithin.Recognition.F112WValency
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312J2

section Abstract

variable {G : Type} [Group G]

theorem le_centralizer_of_card_le_two [Finite G] {L Z : Subgroup G}
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (hZ : Nat.card Z ≤ 2) :
    L ≤ Subgroup.centralizer (Z : Set G) := by
  intro ℓ hℓ
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  by_contra hne
  have hw : ℓ * z * ℓ⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hLZ hℓ) z).mp hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hne (by group)
  have hwz : ℓ * z * ℓ⁻¹ ≠ z := fun h => hne (by
    calc z * ℓ = ℓ * z * ℓ⁻¹ * ℓ := by rw [h]
      _ = ℓ * z := by group)
  have hw1 : ℓ * z * ℓ⁻¹ ≠ 1 := fun h => hz1 (by
    have : ℓ * z = ℓ := by
      calc ℓ * z = ℓ * z * ℓ⁻¹ * ℓ := by group
        _ = ℓ := by rw [h, one_mul]
    simpa using this)
  let f : Fin 3 → ↥Z := ![1, ⟨z, hz⟩, ⟨ℓ * z * ℓ⁻¹, hw⟩]
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab' ⊢
    all_goals first
      | exact absurd hab'.symm hz1 | exact absurd hab' hz1 | exact absurd hab'.symm hw1
      | exact absurd hab' hw1 | exact absurd hab'.symm hwz | exact absurd hab' hwz
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

theorem centerOf_le_centralizer_two [Finite G] {L P S : Subgroup G} (hLP : L ≤ P)
    (hct : CharTwo P) (hSP : S ≤ P) (hQS : pCoreOf 2 P ≤ S)
    (hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 P)) ≤ 2) :
    centerOf S ≤ Subgroup.centralizer (L : Set G) := by
  set Q := pCoreOf 2 P with hQ
  have hLZ : L ≤ Subgroup.normalizer (centerOf Q : Set G) := fun ℓ hℓ =>
    CFSG.Quasithin.H13.NQCat.G2Rad.mem_normalizer_centerOf
      (le_normalizer_pCoreOf 2 P (hLP hℓ))
  have hcard : Nat.card (centerOf Q) ≤ 2 := by
    rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective]
    exact hZ
  have hLC := le_centralizer_of_card_le_two hLZ hcard
  rintro z ⟨hzS, hzc⟩
  have hzQ : z ∈ Q := hct ⟨hSP hzS, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp hzc q (hQS hq)⟩
  have hzZ : z ∈ centerOf Q := ⟨hzQ, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp hzc q (hQS hq)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro ℓ hℓ
  exact (Subgroup.mem_centralizer_iff.mp (hLC hℓ) z hzZ).symm

theorem isQ8D8_of_mulEquiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P') (h : IsQ8D8 P) :
    IsQ8D8 P' := by
  obtain ⟨hc, A, B, ⟨hAB, hsup⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans hc, A.map e.toMonoidHom, B.map e.toMonoidHom,
    ⟨?_, ?_⟩, ⟨(A.equivMapOfInjective _ e.injective).symm.trans eA⟩,
    ⟨(B.equivMapOfInjective _ e.injective).symm.trans eB⟩⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hAB ha) b hb
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  · rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr e.surjective

theorem isQ8D8_pCoreOf_of_mulEquiv {H : Type*} [Group H] {A : Subgroup G} {B : Subgroup H}
    (e : ↥A ≃* ↥B) (h : IsQ8D8 ↥(pCoreOf 2 B)) : IsQ8D8 ↥(pCoreOf 2 A) :=
  isQ8D8_of_mulEquiv (pCoreOfMulEquiv e 2).symm h

theorem commutator_eq_top_of_perfect {K : Subgroup G} (h : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ := by
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, htop, h]

end Abstract

section Model


theorem isQ8D8_pCoreOf_normal {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (hext : IsExt ↥Y (fun V _ => IsExtraspecial2 2 V) (fun Z _ => IsAlt 5 Z))
    (hperf : ⁅Y, Y⁆ = Y) (hc : Nat.card (pCoreOf 2 Y) = 2 ^ 5) :
    IsQ8D8 ↥(pCoreOf 2 Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVn, hV, hA⟩ := hext
  have hq := Q8D8Rec.isQ8D8_of_perfect_alt5 V hV hA (commutator_eq_top_of_perfect hperf)
  have hWY : V.map Y.subtype ≤ Y := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hYW : Y ≤ Subgroup.normalizer ((V.map Y.subtype : Subgroup X) : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨y, hy⟩ * v * ⟨y, hy⟩⁻¹, hVn.conj_mem v hv _, rfl⟩
    · rintro ⟨v, hv, hx⟩
      have hx' : x = y⁻¹ * (v : X) * y := by
        rw [show (v : X) = y * x * y⁻¹ from hx]
        group
      refine ⟨⟨y, hy⟩⁻¹ * v * (⟨y, hy⟩⁻¹)⁻¹, hVn.conj_mem v hv _, ?_⟩
      rw [hx']
      simp
  have hW2 : IsPGroup 2 (V.map Y.subtype) :=
    (CFSG.isExtraspecialPGroup_iff_isExtraspecial.mpr hV.1).1.map _
  have hWO : V.map Y.subtype ≤ pCoreOf 2 Y := le_pCoreOf_of_le_normalizer hWY hYW hW2
  have hWc : Nat.card (V.map Y.subtype) = 2 ^ 5 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hV.2]
  have hWeq : V.map Y.subtype = pCoreOf 2 Y :=
    Subgroup.eq_of_le_of_card_ge hWO (by rw [hWc, hc])
  rw [← hWeq]
  exact isQ8D8_of_mulEquiv (V.equivMapOfInjective _ Y.subtype_injective) hq

theorem isQ8D8_pCoreOf_Y3 : IsQ8D8 ↥(pCoreOf 2 (j2CtxA.Y 3)) :=
  isQ8D8_pCoreOf_normal j2_Y3_ext.1 j2_Y3_ext.2 J2L.card_pCoreOf_Y3

end Model

section Main

theorem exists_yPair_conj {Y H : Type*} [Group Y] [Group H] [Finite H] (E0 : Y ≃* H)
    {S₀ : Subgroup H} (hS₀ : IsSylowTwoOf S₀ ⊤) {T M₁ M₂ : Subgroup Y}
    (hp : IsYAmalgamPair T M₁ M₂) :
    ∃ E : Y ≃* H, IsYAmalgamPair S₀ (M₁.map E.toMonoidHom) (M₂.map E.toMonoidHom) := by
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj (hp.map E0).1 hS₀
  refine ⟨E0.trans (MulAut.conj h), ?_⟩
  have hy2 := hp.map (E0.trans (MulAut.conj h))
  have hTD : T.map (E0.trans (MulAut.conj h)).toMonoidHom = S₀ := by
    rw [hh, Subgroup.map_map]
    rfl
  rwa [hTD] at hy2


theorem y9J2 : Y9J2 := by
  intro G _ _ L1 L2 S hF h1 h2 hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, _, ⟨e⟩, T, M₁, M₂, hp, ⟨ψ1⟩, -, ⟨ψ2⟩⟩ := hA
  obtain ⟨E0⟩ : Nonempty (Y ≃* ↥CFSG.Sporadic.J2.J) :=
    ⟨(e.trans quasithinJ2MulEquivNative).trans CFSG.Sporadic.Bridge.J2.nativeEquiv⟩
  obtain ⟨E, hy2⟩ := @exists_yPair_conj Y ↥CFSG.Sporadic.J2.J inferInstance inferInstance
    inferInstance E0 j2CtxA.S j2A_sylow T M₁ M₂ hp
  have hL1 : 5 ∣ Nat.card ↥(L1 ⊔ bigB L1 L2 S) := by
    have h60 : Nat.card (oTwoQuot ↥L1) = 60 := by
      rw [IsL2Quot.card (by norm_num) h1]
      norm_num
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L1)
    have h5 : 5 ∣ Nat.card L1 := by
      rw [hq]
      exact Dvd.dvd.mul_right (h60 ▸ (by norm_num : 5 ∣ 60)) _
    exact h5.trans (Subgroup.card_dvd_of_le le_sup_left)
  have φ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(M₁.map E.toMonoidHom) :=
    ψ1.trans (M₁.equivMapOfInjective E.toMonoidHom E.injective)
  have φ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(M₂.map E.toMonoidHom) :=
    ψ2.trans (M₂.equivMapOfInjective E.toMonoidHom E.injective)
  obtain ⟨hM1, hM2⟩ : M₁.map E.toMonoidHom = j2CtxA.Y 3 ∧ M₂.map E.toMonoidHom = j2CtxA.Y 2 := by
    rcases J2L.yPair_eq hy2 with h' | ⟨hM1, -⟩
    · exact h'
    · exfalso
      rw [Nat.card_congr φ1.toEquiv, hM1, J2L.card_Y2] at hL1
      norm_num at hL1
  let P1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(j2CtxA.Y 3) := φ1.trans (MulEquiv.subgroupCongr hM1)
  let P2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(j2CtxA.Y 2) := φ2.trans (MulEquiv.subgroupCongr hM2)
  have hq8 : IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) :=
    isQ8D8_pCoreOf_of_mulEquiv P1 isQ8D8_pCoreOf_Y3
  have hR : Hyp111R L1 L2 S := by
    obtain ⟨e1⟩ := h1
    obtain ⟨e2⟩ := F112J2.nonempty_psl_four_equiv_alt5
    exact (CFSG.Quasithin.hyp111R_of_perm_three_alt_five hF.1.symm h2 ⟨e1.trans e2⟩).symm
  obtain ⟨-, -, hQS⟩ := CFSG.GH74.QTGen4.DSGen4.leafSylowS hR
  have hct : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hF.1.h1.charTwo
  have hSP : S ≤ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S).trans le_sup_right
  have hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) ≤ 2 := by
    obtain ⟨z, -, -, hzz, hc, -⟩ := CFSG.Quasithin.H13.isQ8D8_central_facts hq8
    have hle : Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤ Subgroup.zpowers z :=
      fun c hc' => by
        rcases hc c hc' with rfl | rfl
        · exact one_mem _
        · exact Subgroup.mem_zpowers _
    calc Nat.card (Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)))
        ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hzz)
  refine ⟨fun _ => centerOf_le_centralizer_two le_sup_left hct hSP hQS hZ, hq8, ?_⟩
  rw [card_pCoreOf_of_mulEquiv P2 2, J2L.card_pCoreOf_Y2]

end Main

end CFSG.Quasithin.F112R
