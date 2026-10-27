module

public import CFSG.Quasithin.H13.NQS1312I
public import CFSG.Quasithin.Background.C134L32CorrM
public import CFSG.Quasithin.MS93.Burnside.C134Big
public import CFSG.Quasithin.H13.NQS1312AW
public import CFSG.Quasithin.H13.NQS1312OW
public import Certificates.Kernel.ThCent.Leaves

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_c27_lineW
    (h1332 : Stmt13_3_2) (h27 : ASC27Statement G) (h134 : C134L32CorrM)
    (hcorr : MS93.burnsideC134w_AS_C_1_34_corrBig) (hU33 : U33CommDimFact) (hF318 : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hA3 : A3Orbits G) (hKF : KnownFacts15122Types) (hE : Vol2.Ch11.SecA.FactA318Excl)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦL : ∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G)) : K ≤ normalizer (L : Set G) := by
  by_contra hKL
  have hyp : HypC23 (lineH Φ) (pCoreOf 2 (L ⊔ T)) (lineH Φ ⊓ normalizer (L : Set G)) :=
    hypC23_line h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  have hKM : ¬ K ≤ lineH Φ ⊓ normalizer (L : Set G) := fun h => hKL (h.trans inf_le_right)
  have hC1 := (h27 _ _ _ K _ hyp hK hq hKc hKM hQK rfl).1.2.1
  rcases SBc17.asc27_cases h27 hyp hK hq hKc hKM hQK rfl with
    h | h | h | h | h | h | h | h | h | h | h
  · exact false_of_c27L2_line h1332 hA3 h38 hH hU3 hF hΦLs hΦN hΦT hK hq hQK hC1 h
  · exact false_of_c27A5_line hA3 h38 hH hU3 hF hΦLs hΦT hK hQK h
  · exact false_of_c27A7a_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq h
  · exact false_of_c27A7b_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq h
  ·
    obtain ⟨⟨n, α, hn5, hn8, -, hαb, t, htQ, htV, hautR, hord, σ, hσ, hσα⟩, hMK⟩ := h
    obtain ⟨S, hS, -, -, hSL, -, hidx⟩ := exists_sylow_lineH h1332 hH hF hΦN
    have hSK : IsSylowTwoOf (S ⊓ K) K :=
      S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hK) hS
    have hSM : S ⊓ K ≤ (lineH Φ ⊓ normalizer (L : Set G)) ⊓ K := fun x hx =>
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hS.1 (Subgroup.mem_inf.1 hx).1,
        hSL (Subgroup.mem_inf.1 hx).1⟩, (Subgroup.mem_inf.1 hx).2⟩
    obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    · exact false_of_c27Alt_five hQK hSK hSM hC1 hαb htQ htV hautR hσ hσα hMK
    · exact false_of_c27Alt_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq (Or.inl rfl) hαb
    · exact false_of_c27Alt_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq (Or.inr rfl) hαb
    · exact false_of_c27Alt_eight hSK hidx hC1 hαb htV hautR hord
  · exact false_of_c27Hat6_line hF318 h36 h38 hH hU3 hF hΦLs hK hq h
  · exact false_of_c27ExcA7_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq h
  · exact false_of_c27A6Sp4_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq hE h
  · exact false_of_c27G2_line hF318 h36 h38 hKF hH hU3 hF hΦLs hK hq h
  ·
    obtain ⟨⟨n, F, _, _, hn1, hcard, ⟨e⟩⟩, hmax, hMS⟩ := h
    rcases Nat.even_or_odd n with hn | hn
    · exact false_of_c27SL3_even_lineW h1332 hF318 h36 h38 hA3 hcorr hH hU3
        hF hΦLs hΦN hΦT hK hq
        hQK hC1 hn hn1 hcard e hMS
    · by_cases hn1' : n = 1
      · subst hn1'
        exact false_of_c27SL3_two_lineW h1332 h36 h38 hA3 h134 hU33 hH hU3 hF hΦL
          hΦLs hΦN hΦT hK
          hq hQK hC1 (hcard.trans (pow_one 2)) e hmax hMS
      · exact false_of_c27SL3_odd_line h1332 h38 hA3 hH hU3 hF hΦLs hΦN hΦT hK hq hQK hn hn1'
          hcard e hmax
  · exact false_of_c27L45_line h1332 hF318 h36 h38 hA3 hKF hH hU3 hF hΦLs hΦN hΦT hK hq hQK hC1 h

end CFSG.Quasithin.H13.U3.NLine

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB NLine
open scoped IsMulCommutative

theorem u3LineComponentExclusionQ_of_inputsW
    (h1332 : Stmt13_3_2) (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h134 : C134L32CorrM) (hcorr : MS93.burnsideC134w_AS_C_1_34_corrBig) (hU33 : U33CommDimFact) :
    U3LineComponentExclusionQ := by
  intro G _ _ T L V z _ hH hU3 hF b hbn hba hbi u v hu hv huv K hK hq hQK
  obtain ⟨hA37, hA38, -⟩ := a3ForSQTK_holds
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  obtain ⟨Φ, hΦL, hΦLs, hΦN, hΦT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  have huv0 : b0 (Φ (Additive.ofMul ⟨u, hu⟩)) (Φ (Additive.ofMul ⟨v, hv⟩)) ≠ 0 := by
    rwa [← form_eq_b0 hLV hΦLs hV1 hbn hbi]
  obtain ⟨l, hl, hlu, hlv⟩ := exists_conj_line hLV hΦLs hu hv huv0
  have hinv15 : (ptOf Φ (vecOf 15))⁻¹ = ptOf Φ (vecOf 15) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) _ (ptOf_mem _)
  have h15 : l⁻¹ * u * l⁻¹⁻¹ = ptOf Φ (vecOf 15) := by rw [← hlu]; group
  have h52 : l⁻¹ * v * l⁻¹⁻¹ = ptOf Φ (vecOf 52) ∨
      l⁻¹ * v * l⁻¹⁻¹ = ptOf Φ (vecOf 52) * ptOf Φ (vecOf 15) := by
    rcases hlv with h | h
    · left
      rw [← h]
      group
    · right
      have hv' : v = l * ptOf Φ (vecOf 52) * l⁻¹ * u⁻¹ := by rw [h]; group
      rw [hv', ← hlu]
      group
      rw [zpow_neg_one, hinv15]
  have hC : (centralizer ({u, v} : Set G)).map (MulAut.conj l⁻¹).toMonoidHom = lineH Φ := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h1 := conj_mem_centralizer_pair hlu hlv hc
      rw [lineH]
      simpa [MulAut.conj_apply, mul_assoc] using h1
    · intro hx
      refine ⟨l * x * l⁻¹, ?_, ?_⟩
      · have h1 := conj_mem_centralizer_pair h15 h52 hx
        simpa [mul_assoc] using h1
      · simp [mul_assoc]
  set K' := K.map (MulAut.conj l⁻¹).toMonoidHom with hK'
  have hK'c : K' ∈ cComp (lineH Φ) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj l⁻¹) hK
    rwa [hC] at h1
  have hq' : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') := by
    let e : ↥K ≃* ↥K' := K.equivMapOfInjective (MulAut.conj l⁻¹).toMonoidHom
      (MulAut.conj l⁻¹).injective
    have he : (CFSG.pCore 2 ↥K).map e.toMonoidHom = CFSG.pCore 2 ↥K' := CFSG.pCore_map_iso 2 e
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K') e he) hq
  have hlQ : l ∈ normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hl)
  have hQK' : pCoreOf 2 (L ⊔ T) ≤ normalizer (K' : Set G) := by
    intro q hq
    have hq' : l * q * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) := (mem_normalizer_iff.1 hlQ q).1 hq
    rw [mem_normalizer_iff]
    intro x
    have key : ∀ y : G, y ∈ K' ↔ l * y * l⁻¹ ∈ K := fun y => by
      rw [hK', Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hk
      · intro hy
        exact ⟨l * y * l⁻¹, hy, by simp [mul_assoc]⟩
    rw [key, key]
    have e1 : l * (q * x * q⁻¹) * l⁻¹ = (l * q * l⁻¹) * (l * x * l⁻¹) * (l * q * l⁻¹)⁻¹ := by
      group
    rw [e1]
    exact mem_normalizer_iff.1 (hQK hq') _
  have hK'M := le_normalizer_of_c27_lineW h1332 (h27 G) h134 hcorr hU33 hF318
    VolI.a36ForSQTK_holds hA38 hA3 knownFacts15122Types_final factA318Excl_holds hH hU3 hF hΦL
    hΦLs hΦN hΦT hK'c hq' hQK'
  have hlM : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
  intro k hk
  have h1 : l⁻¹ * k * l ∈ normalizer (L : Set G) :=
    hK'M ⟨k, hk, by simp⟩
  have h2 : l * (l⁻¹ * k * l) * l⁻¹ ∈ normalizer (L : Set G) :=
    mul_mem (mul_mem hlM h1) (inv_mem hlM)
  rwa [show l * (l⁻¹ * k * l) * l⁻¹ = k by group] at h2

end CFSG.Quasithin.H13.U3
