module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem conjSubgroup_inv_le_iff (B M : Subgroup G) (g : G) :
    conjSubgroup B g⁻¹ ≤ M ↔ B ≤ conjSubgroup M g :=
  (E3.le_conjSubgroup_iff_inv_le g).symm

private theorem conjSub_eq_conjSubgroup_inv (h : G) (A : Subgroup G) :
    CFSG.Quasithin.A1b.conjSub h A = conjSubgroup A h⁻¹ := by
  rw [CFSG.Quasithin.A1b.conjSub, conjSubgroup, inv_inv]

private theorem twoFirst_conj {n : ℕ} {M V : Subgroup G} (y g : G) :
    TwoFirst n (conjSubgroup M y) (conjSubgroup V y) (y⁻¹ * g * y) ↔ TwoFirst n M V g := by
  have hgy : y * (y⁻¹ * g * y) = g * y := by group
  have hVg : conjSubgroup (conjSubgroup V y) (y⁻¹ * g * y) =
      conjSubgroup (conjSubgroup V g) y := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hgy]
  have hMg : conjSubgroup (conjSubgroup M y) (y⁻¹ * g * y) =
      conjSubgroup (conjSubgroup M g) y := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hgy]
  have hinf : conjSubgroup V y ⊓ conjSubgroup (conjSubgroup M g) y =
      conjSubgroup (V ⊓ conjSubgroup M g) y := (E3.conjSubgroup_inf V (conjSubgroup M g) y).symm
  have hcancel : conjSubgroup (conjSubgroup (V ⊓ conjSubgroup M g) y) y⁻¹ =
      V ⊓ conjSubgroup M g := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  unfold TwoFirst
  constructor
  · rintro ⟨I, hI, hle⟩
    rw [hMg, hinf, E3.gammaSet_conjV] at hI
    refine ⟨conjSubgroup I y⁻¹, ?_, ?_⟩
    · have h1 := E3.conj_mem_gammaSet (V := V) (i := n)
        (X := conjSubgroup (V ⊓ conjSubgroup M g) y) y⁻¹ hI
      rwa [hcancel] at h1
    · rw [hVg] at hle
      intro h
      apply hle
      have hI' : conjSubgroup (conjSubgroup I y⁻¹) y = I := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      rw [← E3.conjSubgroup_centralizer]
      rw [← hI', ← E3.conjSubgroup_centralizer]
      rw [← E3.conjSubgroup_inf, ← E3.conjSubgroup_inf]
      rw [E3.conjSubgroup_le_conjSubgroup_iff]
      exact h
  · rintro ⟨I, hI, hle⟩
    refine ⟨conjSubgroup I y, ?_, ?_⟩
    · have h1 := E3.conj_mem_gammaSet (V := V) (i := n) (X := V ⊓ conjSubgroup M g) y hI
      rw [← hinf] at h1
      rw [hMg, E3.gammaSet_conjV]
      exact h1
    · rw [hVg]
      intro h
      apply hle
      have h' : conjSubgroup (conjSubgroup V g ⊓ M ⊓ centralizer (I : Set G)) y ≤
          conjSubgroup (centralizer (V : Set G)) y := by
        have hL : conjSubgroup (conjSubgroup V g ⊓ M ⊓ centralizer (I : Set G)) y =
            conjSubgroup (conjSubgroup V g) y ⊓ conjSubgroup M y ⊓
              centralizer (conjSubgroup I y : Set G) := by
          rw [E3.conjSubgroup_inf, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
        have hR : conjSubgroup (centralizer (V : Set G)) y =
            centralizer (conjSubgroup V y : Set G) := E3.conjSubgroup_centralizer V y
        rw [hL, hR]
        exact h
      exact (E3.conjSubgroup_le_conjSubgroup_iff y).1 h'

private theorem inCalO2_conj {n : ℕ} {M V₀ V : Subgroup G} (y g : G) :
    InCalO2 n (conjSubgroup M y) (conjSubgroup V₀ y) (conjSubgroup V y) (y⁻¹ * g * y) ↔
      InCalO2 n M V₀ V g := by
  have hgy : y * (y⁻¹ * g * y) = g * y := by group
  have hVg : conjSubgroup (conjSubgroup V y) (y⁻¹ * g * y) =
      conjSubgroup (conjSubgroup V g) y := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hgy]
  have hMg : conjSubgroup (conjSubgroup M y) (y⁻¹ * g * y) =
      conjSubgroup (conjSubgroup M g) y := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hgy]
  have hTwoDual : TwoDual n (conjSubgroup M y) (conjSubgroup V y) (y⁻¹ * g * y) ↔
      TwoDual n M V g := by
    rw [← twoFirst_swap n (conjSubgroup M y) (conjSubgroup V y) (y⁻¹ * g * y)]
    rw [hMg, hVg]
    rw [show (y⁻¹ * g * y)⁻¹ = y⁻¹ * g⁻¹ * y by group]
    rw [twoFirst_conj y g⁻¹]
    rw [twoFirst_swap n M V g]
  have hIsP : ¬ IsPGroup 2 (conjSubgroup V y ⊔
        conjSubgroup (conjSubgroup V y) (y⁻¹ * g * y) : Subgroup G) ↔
      ¬ IsPGroup 2 (V ⊔ conjSubgroup V g : Subgroup G) := by
    have hsup : conjSubgroup V y ⊔ conjSubgroup (conjSubgroup V y) (y⁻¹ * g * y) =
        conjSubgroup (V ⊔ conjSubgroup V g) y := by
      rw [hVg, conjSubgroup_sup]
    rw [hsup]
    constructor
    · intro h hP
      exact h (E3.isPGroup_conjSubgroup hP y)
    · intro h hP
      refine h ?_
      have h2 := E3.isPGroup_conjSubgroup hP y⁻¹
      rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
  unfold InCalO2
  rw [inCalO_conj y g, twoFirst_conj y g, hTwoDual, hIsP]

theorem s15_Thirteen_exists_A_K (D : Data G) (h126 : R126 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M)
    (hC : centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M) :
    ∃ H A K : Subgroup G, IsSylowIn 2 D.T H ∧ A ∈ E3.gammaSet V 0 D.T ∧
      E1.IsE D.k H D.T A K ∧ ⁅twoResidual K, E3.cClos V D.k D.T⁆ ≠ ⊥ := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
  have hTH₀ : D.T ≤ H₀ := hmin.1.1
  have hH₀M : ¬ H₀ ≤ D.M := hmin.1.2.1
  have hS : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hTH₀
  have hEF : E1.InEFor D.k H₀ D.T := (E1.inE_iff_inEFor hS).1 (h126 H₀ hmin)
  let Ω : Set (Subgroup G) := {A | ∃ g : G, A = conjSubgroup V g ∧ A ≤ H₀}
  have hΩ : E1.IsInvColl H₀ Ω := by
    refine ⟨fun A hA => by obtain ⟨g, -, hAH⟩ := hA; exact hAH, fun A hA => ?_,
      fun A hA h hh => ?_⟩
    · obtain ⟨g, rfl, -⟩ := hA
      exact E3.isElemAbelian_conjSubgroup hV g
    · obtain ⟨g, hAg, hAH⟩ := hA
      refine ⟨g * h⁻¹, ?_, ?_⟩
      · rw [conjSub_eq_conjSubgroup_inv, hAg, conjSubgroup_conjSubgroup]
      · rw [conjSub_eq_conjSubgroup_inv, hAg]
        intro x hx
        rw [mem_conjSubgroup_iff] at hx
        rw [inv_inv, ← hAg] at hx
        have hxH : h⁻¹ * x * h ∈ H₀ := hAH hx
        have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
        rw [← e]
        exact H₀.mul_mem (H₀.mul_mem hh hxH) (H₀.inv_mem hh)
  have hweak : E1.weakClosure D.T Ω = E3.wClos V 0 D.T := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
      obtain ⟨g, rfl, -⟩ := hA
      exact E3.le_wClos ⟨hAT, g, le_rfl, E3.mQuot_self (conjSubgroup V g)⟩
    · refine E3.wClos_le_of_forall fun A hA => ?_
      obtain ⟨hAT, g, hAg, hmg⟩ := hA
      have hVg2 : IsPGroup 2 (conjSubgroup V g) :=
        E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g
      have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg2 hAg).1 hmg
      rw [hAeq]
      refine le_iSup₂_of_le (conjSubgroup V g) ⟨g, rfl, (hAeq ▸ hAT).trans hTH₀⟩ ?_
      exact le_iSup_of_le (hAeq ▸ hAT) le_rfl
  have hgen := hEF Ω hΩ
  rw [hweak] at hgen
  have hN' : H₀ ⊓ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := inf_le_right.trans hN
  have hgen_not : ¬ E1.eGen D.k H₀ D.T Ω ≤ D.M := by
    intro hle
    apply hH₀M
    rw [← hgen]
    exact sup_le hle hN'
  have hex : ∃ A K : Subgroup G, A ∈ Ω ∧ A ≤ D.T ∧ E1.IsE D.k H₀ D.T A K ∧ ¬ K ≤ D.M := by
    by_contra hcon
    apply hgen_not
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    by_contra hKM
    exact hcon ⟨A, K, hA, hAT, hK, hKM⟩
  obtain ⟨A, K, hAΩ, hAT, hK, hKM⟩ := hex
  obtain ⟨g, hAg, -⟩ := hAΩ
  refine ⟨H₀, A, K, hS, ⟨hAT, g, le_of_eq hAg, by rw [hAg, E3.mQuot_self]⟩, hK, ?_⟩
  intro hbot
  have h2 : twoResidual K ≤ D.M :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot).trans hC
  have hKle : K ≤ D.M := by
    rw [← sup_twoResidual_eq hK.2.2.1]
    exact sup_le (inf_le_left.trans D.sylowM.le) h2
  exact hKM hKle

private theorem six_nine_two_core_of_isE {M V H S A K : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hMnorm : normalizer (V : Set G) = M)
    (hS : IsSylowIn 2 S H) {i k n : ℕ} (hn : n = k + i)
    (hA : A ∈ E3.gammaSet V i S) (hAV : A ≤ V) (hK : E1.IsE k H S A K)
    (hkV : n < rk ↥V)
    (hr : (n : ℕ∞) < E3.rParam V)
    (hne : ⁅twoResidual K, E3.cClos V n S⁆ ≠ ⊥)
    (hbeta : (n : ℕ∞) < betaN i M V) :
    ∃ g ∈ K, InCalO2 n M ⊥ V g := by
  obtain ⟨hAS, x, hAx, hmx⟩ := hA
  have hAi : E3.mQuot V A ≤ i := (E3.mQuot_conj_eq hV hAV hAx).trans_le hmx.le
  have hAab : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAV hV
  have hAK : A ≤ K := (E3.card_le_of_isE hS hAS hAab hK).1
  have hijk : i + k ≤ n := by omega
  set Q := E3.cClos V n (pCoreOf 2 K) with hQ
  set W := E3.wClos V n (pCoreOf 2 K) with hW
  set B := A ⊓ pCoreOf 2 K with hB
  have hBW : B ≤ W := E3.e3_17_B_le hV hS hijk hkV hAS hAV hAi hK
  have hmB : E3.mQuot V B ≤ n := by
    have h := E3.e3_17_mQuot hV hS hAS hAV hAi hK
    rw [hB]; omega
  have hcentle : Subgroup.centralizer (W : Set G) ≤ M := by
    rw [← hMnorm]
    exact E3.e3_17_cent_le hV hS hijk hr hkV hAS hAV hAi hK
  have hQM : Q ≤ M := (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans hcentle
  have hQW : Q ≤ centralizer (B : Set G) :=
    (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans (Subgroup.centralizer_le hBW)
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left
  have hcomm := E3.e3_17_comm_ne hV hS hijk hr hkV hAS hAV hAi hK hne
  have hEne : ⁅A, Q⁆ ≠ ⊥ := hcomm.2
  have hAne : ¬ A ≤ pCoreOf 2 K := by
    intro hAle
    have hAB : B = A := inf_eq_left.2 hAle
    have hAW : A ≤ W := hAB ▸ hBW
    have hQA : Q ≤ centralizer (A : Set G) :=
      (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans (Subgroup.centralizer_le hAW)
    apply hEne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hQA
  have hBab : IsElemAbelian 2 B := B2F.isElemAbelian_mono inf_le_left hAab
  have hB2 : IsPGroup 2 B := B2F.isPGroup_of_isElemAbelian hBab
  have hBAm : E3.mQuot A B ≤ k := by
    obtain ⟨-, hcard⟩ := E3.card_le_of_isE hS hAS hAab hK
    have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAab
    have e := E3.card_eq_two_pow_mul hA2 (inf_le_left : B ≤ A)
    rw [e] at hcard
    have := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  have hCGE : centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) ≤ M := by
    by_contra hCGE
    obtain ⟨t, htQ, htAt⟩ := exists_commElt_ne_bot_of_commutator_ne_bot hEne
    have hcommE : commElt A t ≤ ⁅A, Q⁆ :=
      (commElt_le_commutator A t).trans
        (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 htQ))
    have hPropB : PropB M (commElt A t) := fun hle =>
      hCGE ((Subgroup.centralizer_le hcommE).trans hle)
    exact (betaN_le_of_cent_ne hAV hAi (inf_le_left : B ≤ A) hBAm hn hQM hQW hQ2 htQ htAt
      hPropB) hbeta
  have hE_le_V : ⁅A, Q⁆ ≤ V := by
    refine (Subgroup.commutator_mono hAV le_rfl).trans ?_
    refine Subgroup.commutator_le.2 ?_
    intro v hv q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := hMnorm.symm ▸ hQM hq
    have h1 : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hqN v).1 hv
    have h2 : q * v⁻¹ * q⁻¹ ∈ V := by
      have := V.inv_mem h1
      convert this using 1
      group
    have e : ⁅v, q⁆ = v * (q * v⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv h2
  have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAab
  obtain ⟨g, hgK, hgnon2⟩ := exists_not_isPGroup_sup_conj_of_not_le_pCore hAK hA2 hAne
  have hWnorm : K ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := n) (pCoreOf 2 K))
  have hQnorm : K ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_cClos (V := V) (i := n) (pCoreOf 2 K))
  have hE_le_Q : ⁅A, Q⁆ ≤ Q := by
    refine Subgroup.commutator_le.2 ?_
    intro a ha q hq
    have haN : a ∈ Subgroup.normalizer (Q : Set G) := hQnorm (hAK ha)
    have h1 : a * q * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 haN q).1 hq
    have e : ⁅a, q⁆ = (a * q * a⁻¹) * q⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hQg : conjSubgroup Q g = Q := conjSubgroup_eq_iff_mem_normalizer.2 (hQnorm hgK)
  have hQg_inv : conjSubgroup Q g⁻¹ = Q :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hQnorm (K.inv_mem hgK))
  have hWg : conjSubgroup W g = W := conjSubgroup_eq_iff_mem_normalizer.2 (hWnorm hgK)
  have hWg_inv : conjSubgroup W g⁻¹ = W :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hWnorm (K.inv_mem hgK))
  have hEg_le_Q : conjSubgroup (⁅A, Q⁆) g ≤ Q :=
    (E3.conjSubgroup_mono_left g hE_le_Q).trans (le_of_eq hQg)
  have hEginv_le_Q : conjSubgroup (⁅A, Q⁆) g⁻¹ ≤ Q :=
    (E3.conjSubgroup_mono_left g⁻¹ hE_le_Q).trans (le_of_eq hQg_inv)
  have hEg_le_M : conjSubgroup (⁅A, Q⁆) g ≤ M := hEg_le_Q.trans hQM
  have hEginv_le_M : conjSubgroup (⁅A, Q⁆) g⁻¹ ≤ M := hEginv_le_Q.trans hQM
  have hBg_le_W : conjSubgroup B g ≤ W := (E3.conjSubgroup_mono_left g hBW).trans (le_of_eq hWg)
  have hBginv_le_W : conjSubgroup B g⁻¹ ≤ W :=
    (E3.conjSubgroup_mono_left g⁻¹ hBW).trans (le_of_eq hWg_inv)
  have heC_of_Q : ∀ {e : G}, e ∈ Q → e ∈ centralizer (W : Set G) := by
    intro e he
    exact (Subgroup.mem_inf.1 (hQ ▸ he)).2
  have hBg_le_CGE : conjSubgroup B g ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (heC_of_Q (hE_le_Q he)) b (hBg_le_W hb))).symm
  have hBginv_le_CGE : conjSubgroup B g⁻¹ ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (heC_of_Q (hE_le_Q he)) b (hBginv_le_W hb))).symm
  have hBg_le_M : conjSubgroup B g ≤ M := hBg_le_CGE.trans hCGE
  have hBginv_le_M : conjSubgroup B g⁻¹ ≤ M := hBginv_le_CGE.trans hCGE
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hnotVg : ¬ conjSubgroup V g ≤ M :=
    not_conjSubgroup_le_normalizer_of_not_isPGroup hV2 hAV hM hgnon2
  have hnotVMg : ¬ V ≤ conjSubgroup M g :=
    not_le_conjSubgroup_of_not_isPGroup hV2 hAV hMnorm hgnon2
  have hB_le_Mg : B ≤ conjSubgroup M g := (conjSubgroup_inv_le_iff B M g).1 hBginv_le_M
  have hE_le_Mg : ⁅A, Q⁆ ≤ conjSubgroup M g :=
    (conjSubgroup_inv_le_iff (⁅A, Q⁆) M g).1 hEginv_le_M
  have hmVg : E3.mQuot V (conjSubgroup M g) ≤ n :=
    (le_of_eq (mQuot_inf_left V (conjSubgroup M g)).symm).trans
      ((E3.mQuot_mono (le_inf (inf_le_left.trans hAV) hB_le_Mg)).trans hmB)
  have hmVg2 : E3.mQuot (conjSubgroup V g) M ≤ n := by
    have hBg_le_M' : conjSubgroup B g ≤ conjSubgroup V g ⊓ M :=
      le_inf (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV)) hBg_le_M
    have h1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M) ≤ E3.mQuot V B :=
      (E3.mQuot_mono hBg_le_M').trans_eq (E3.mQuot_conjSubgroup V B g)
    exact (le_of_eq (mQuot_inf_left (conjSubgroup V g) M).symm).trans (h1.trans hmB)
  have hInCalO : InCalO n M ⊥ V g := by
    refine ⟨⟨hnotVg, hmVg, ?_⟩, hnotVMg, hmVg2, ?_⟩
    · intro h; exact absurd rfl h
    · intro h; exact absurd rfl h
  have hrkB : rk ↥V = E3.mQuot V B + rk ↥B := by
    have h := E3.card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian hV)
      (inf_le_left.trans hAV : B ≤ V)
    rw [card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV),
      card_eq_two_pow_of_isPGroup hB2, ← pow_add] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hTwoFirst : TwoFirst n M V g := by
    have hc : n - E3.mQuot V B ≤ rk ↥B := by omega
    obtain ⟨I, hIB, hI⟩ := exists_le_mQuot_eq hBab hc
    have hIV : E3.mQuot V I = n := by
      have h := E3.mQuot_add (V := V) (U := I) (U' := B) hIB (inf_le_left.trans hAV)
      rw [hI] at h
      omega
    refine ⟨I, ?_, ?_⟩
    · refine ⟨le_inf (hIB.trans (inf_le_left.trans hAV)) (hIB.trans hB_le_Mg), 1, ?_, ?_⟩
      · simpa [conjSubgroup_one] using hIB.trans (inf_le_left.trans hAV)
      · simpa [conjSubgroup_one] using hIV
    · intro hle
      have hEg_le_CV : conjSubgroup (⁅A, Q⁆) g ≤ centralizer (V : Set G) := by
        refine (le_inf (le_inf (E3.conjSubgroup_mono_left g hE_le_V) hEg_le_M) ?_).trans hle
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro i hi
        exact (Subgroup.mem_centralizer_iff.1 (heC_of_Q (hEg_le_Q he)) i
          (hIB.trans hBW hi))
      have hV_le_C : V ≤ centralizer ((conjSubgroup (⁅A, Q⁆) g : Subgroup G) : Set G) :=
        (Subgroup.le_centralizer_iff).2 hEg_le_CV
      have hCg : centralizer ((conjSubgroup (⁅A, Q⁆) g : Subgroup G) : Set G) ≤
          conjSubgroup M g := by
        rw [← E3.conjSubgroup_centralizer]
        exact E3.conjSubgroup_mono_left g hCGE
      exact hnotVMg (hV_le_C.trans hCg)
  have hTwoDual : TwoDual n M V g := by
    have hBg2 : IsPGroup 2 (conjSubgroup B g) := E3.isPGroup_conjSubgroup hB2 g
    have hc : n - E3.mQuot (conjSubgroup V g) (conjSubgroup B g) ≤ rk ↥(conjSubgroup B g) := by
      have hB' : E3.mQuot (conjSubgroup V g) (conjSubgroup B g) = E3.mQuot V B :=
        E3.mQuot_conjSubgroup V B g
      have h1 : rk ↥(conjSubgroup V g) = E3.mQuot (conjSubgroup V g) (conjSubgroup B g) +
          rk ↥(conjSubgroup B g) := by
        have h := E3.card_eq_two_pow_mul
          (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g)
          (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV) :
            conjSubgroup B g ≤ conjSubgroup V g)
        rw [card_eq_two_pow_of_isPGroup
          (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g),
          card_eq_two_pow_of_isPGroup hBg2, ← pow_add] at h
        exact Nat.pow_right_injective (le_refl 2) h
      rw [E3.rk_conjSubgroup] at h1
      omega
    obtain ⟨I, hIB, hI⟩ := exists_le_mQuot_eq (E3.isElemAbelian_conjSubgroup hBab g) hc
    have hIVg : E3.mQuot (conjSubgroup V g) I = n := by
      have h := E3.mQuot_add (V := conjSubgroup V g) (U := I) (U' := conjSubgroup B g) hIB
        (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV))
      rw [hI] at h
      have hB' : E3.mQuot (conjSubgroup V g) (conjSubgroup B g) = E3.mQuot V B :=
        E3.mQuot_conjSubgroup V B g
      rw [hB'] at h
      omega
    refine ⟨I, ?_, ?_⟩
    · refine ⟨le_inf (hIB.trans (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV)))
          (hIB.trans hBg_le_M), 1, ?_, ?_⟩
      · simpa [conjSubgroup_one] using
          hIB.trans (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV))
      · simpa [conjSubgroup_one] using hIVg
    · intro hle
      have hE_le_CVg : ⁅A, Q⁆ ≤ centralizer (conjSubgroup V g : Set G) := by
        refine (le_inf (le_inf hE_le_V hE_le_Mg) ?_).trans hle
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro i hi
        exact (Subgroup.mem_centralizer_iff.1 (heC_of_Q (hE_le_Q he)) i
          (hIB.trans hBg_le_W hi))
      have hVg_le_C : conjSubgroup V g ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) :=
        (Subgroup.le_centralizer_iff).2 hE_le_CVg
      exact hnotVg (hVg_le_C.trans hCGE)
  have hnon2 : ¬ IsPGroup 2 (V ⊔ conjSubgroup V g : Subgroup G) := fun h =>
    hgnon2 (h.to_le (sup_le_sup hAV (E3.conjSubgroup_mono_left g hAV)))
  exact ⟨g, hgK, hInCalO, hTwoFirst, hTwoDual, hnon2⟩

private theorem inf_centralizer_ne_bot_of_isPGroup {E Y : Subgroup G} (hE : IsPGroup 2 E)
    (hY : IsPGroup 2 Y) (hY0 : Y ≠ ⊥) (hEY : E ≤ normalizer (Y : Set G)) :
    Y ⊓ centralizer (E : Set G) ≠ ⊥ := by
  have hmod := CFSG.SignalizerFunctor.Helpers.centralizer_card_modEq 2 Nat.prime_two E Y hE hEY
  have hdvd : 2 ∣ Nat.card Y := by
    rcases hY.card_eq_or_dvd with h1 | h1
    · exact absurd ((Subgroup.eq_bot_iff_card Y).mpr h1) hY0
    · exact h1
  have hdvd' : 2 ∣ Nat.card (Y ⊓ centralizer (E : Set G) : Subgroup G) :=
    (hmod.dvd_iff dvd_rfl).mp hdvd
  intro hbot
  rw [hbot, Subgroup.card_bot] at hdvd'
  exact Nat.prime_two.not_dvd_one hdvd'

theorem inf_conjSubgroup_ne_bot_of_mQuot_le {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hMnorm : normalizer (V : Set G) = M)
    (hV₀M : M ≤ normalizer (V₀ : Set G)) (hV₀ : IsPGroup 2 V₀) (hV₀ne : V₀ ≠ ⊥)
    (hr : (n : ℕ∞) < E3.rParam V) (hm : E3.mQuot (conjSubgroup V g) M ≤ n) :
    V₀ ⊓ conjSubgroup M g ≠ ⊥ := by
  have hB2 : IsPGroup 2 (conjSubgroup V g ⊓ M : Subgroup G) :=
    (E3.isPGroup_conjSubgroup hV g).to_le inf_le_left
  set Y : Subgroup G := V₀ ⊓ centralizer (conjSubgroup V g ⊓ M : Subgroup G) with hY
  have hYne : Y ≠ ⊥ := by
    rw [hY]
    exact inf_centralizer_ne_bot_of_isPGroup hB2 hV₀ hV₀ne (inf_le_right.trans hV₀M)
  have hYle : Y ≤ centralizer (conjSubgroup V g ⊓ M : Subgroup G) := by
    rw [hY]
    exact inf_le_right
  set U : Subgroup G := conjSubgroup V g ⊓ centralizer (Y : Set G) with hU
  have hBU : conjSubgroup V g ⊓ M ≤ U := by
    rw [hU]
    exact le_inf inf_le_left (Subgroup.le_centralizer_iff.1 hYle)
  have hmU : E3.mQuot (conjSubgroup V g) U ≤ n := by
    rw [hU]
    refine (E3.mQuot_mono hBU).trans ?_
    rw [mQuot_inf_left]
    exact hm
  have hCU : centralizer (U : Set G) ≤ conjSubgroup M g := by
    by_contra hC
    have hnorm : normalizer (conjSubgroup V g : Set G) = conjSubgroup M g := by
      rw [← E3.conjSubgroup_normalizer, hMnorm]
    have hC' : ¬ centralizer (U : Set G) ≤ normalizer (conjSubgroup V g : Set G) := by
      rwa [hnorm]
    have h1 : E3.rParam (conjSubgroup V g) ≤ E3.mQuot (conjSubgroup V g) U :=
      E3.rParam_le_mQuot (show U ≤ conjSubgroup V g from inf_le_left) hC'
    rw [E3.rParam_conj] at h1
    exact (not_le.2 hr) (h1.trans (by exact_mod_cast hmU))
  have hYU : Y ≤ centralizer (U : Set G) := by
    rw [hU]
    exact Subgroup.le_centralizer_iff.1 inf_le_right
  intro hbot
  apply hYne
  rw [eq_bot_iff, ← hbot]
  exact le_inf (hY.le.trans inf_le_left) (hYU.trans hCU)

theorem conjSubgroup_inf_ne_bot_of_mQuot_le {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hMnorm : normalizer (V : Set G) = M)
    (hV₀M : M ≤ normalizer (V₀ : Set G)) (hV₀ : IsPGroup 2 V₀) (hV₀ne : V₀ ≠ ⊥)
    (hr : (n : ℕ∞) < E3.rParam V) (hm : E3.mQuot V (conjSubgroup M g) ≤ n) :
    conjSubgroup V₀ g ⊓ M ≠ ⊥ := by
  have h := inf_conjSubgroup_ne_bot_of_mQuot_le (n := n) (M := conjSubgroup M g)
    (V₀ := conjSubgroup V₀ g) (V := conjSubgroup V g) (g := g⁻¹)
    (E3.isPGroup_conjSubgroup hV g) (by rw [← E3.conjSubgroup_normalizer, hMnorm])
    (by rw [← E3.conjSubgroup_normalizer]; exact E3.conjSubgroup_mono_left g hV₀M)
    (E3.isPGroup_conjSubgroup hV₀ g) (fun h0 => hV₀ne (conjSubgroup_eq_bot_iff.1 h0))
    (by rwa [E3.rParam_conj]) (by rwa [conjSubgroup_conjSubgroup_inv])
  rwa [conjSubgroup_conjSubgroup_inv] at h

theorem inCalO_iff_inCalO_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hMnorm : normalizer (V : Set G) = M)
    (hV₀M : M ≤ normalizer (V₀ : Set G)) (hV₀ : IsPGroup 2 V₀)
    (hr : (n : ℕ∞) < E3.rParam V) :
    InCalO n M V₀ V g ↔ InCalO n M ⊥ V g := by
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h4, h5, -⟩
    exact ⟨⟨h1, h2, fun h => absurd rfl h⟩, h4, h5, fun h => absurd rfl h⟩
  · rintro ⟨⟨h1, h2, -⟩, h4, h5, -⟩
    exact ⟨⟨h1, h2, fun hne => inf_conjSubgroup_ne_bot_of_mQuot_le hV hMnorm hV₀M hV₀ hne hr h5⟩,
      h4, h5, fun hne => conjSubgroup_inf_ne_bot_of_mQuot_le hV hMnorm hV₀M hV₀ hne hr h2⟩

theorem inCalO2_iff_inCalO2_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (hV : IsPGroup 2 V) (hMnorm : normalizer (V : Set G) = M)
    (hV₀M : M ≤ normalizer (V₀ : Set G)) (hV₀ : IsPGroup 2 V₀)
    (hr : (n : ℕ∞) < E3.rParam V) :
    InCalO2 n M V₀ V g ↔ InCalO2 n M ⊥ V g := by
  unfold InCalO2
  exact and_congr_left' (inCalO_iff_inCalO_bot hV hMnorm hV₀M hV₀ hr)

theorem s15_Thirteen_six_nine (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {H S A K : Subgroup G} (hS : IsSylowIn 2 S H) (hA : A ∈ E3.gammaSet V 0 S)
    (hK : E1.IsE D.k H S A K) (hr : (D.k : ℕ∞) < E3.rParam V)
    (hbeta : (D.k : ℕ∞) < betaN 0 D.M V)
    (hne : ⁅twoResidual K, E3.cClos V D.k S⁆ ≠ ⊥) :
    (calO2 D.k D.M V₀ V).Nonempty := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  obtain ⟨hAS, x, hAx, hmx⟩ := hA
  have hVx : IsElemAbelian 2 (conjSubgroup V x) := E3.isElemAbelian_conjSubgroup hV x
  have hAeq : A = conjSubgroup V x := by
    have hVx2 : IsPGroup 2 (conjSubgroup V x) := B2F.isPGroup_of_isElemAbelian hVx
    exact (E3.mQuot_eq_zero_iff hVx2 hAx).1 hmx
  have hMne : D.M ≠ ⊤ := by
    obtain ⟨H₀, hH₀, -⟩ := h.2
    exact fun htop => hH₀.2.1 (htop ▸ le_top)
  have hcentbot : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.2 (by
      intro z hz
      have hz1 : z = 1 := by simpa using hz
      rw [hz1]
      exact Subgroup.one_mem _)
  have hrkV : E3.rParam V ≤ (rk ↥V : ℕ∞) := by
    rw [← CFSG.LocalAnalysis.WeakClosure81.mQuot_bot V]
    refine E3.rParam_le_mQuot (bot_le : (⊥ : Subgroup G) ≤ V) ?_
    rw [hcentbot, Hyp125.normalizer_eq h]
    exact fun htop => hMne (top_le_iff.1 htop)
  have hbot : (calO2 D.k D.M ⊥ V).Nonempty := by
    have hMnormA : normalizer (A : Set G) = conjSubgroup D.M x := by
      rw [hAeq, ← E3.conjSubgroup_normalizer, Hyp125.normalizer_eq h]
    have hAgamma : A ∈ E3.gammaSet A 0 S :=
      ⟨hAS, 1, le_of_eq (conjSubgroup_one A).symm, by rw [conjSubgroup_one, E3.mQuot_self]⟩
    have hkV : D.k < rk ↥A := by
      rw [hAeq, E3.rk_conjSubgroup]
      exact_mod_cast lt_of_lt_of_le hr hrkV
    have hrA : (D.k : ℕ∞) < E3.rParam A := by
      rw [hAeq, E3.rParam_conj]
      exact hr
    have hneA : ⁅twoResidual K, E3.cClos A D.k S⁆ ≠ ⊥ := by
      rw [hAeq, E3.cClos_conjV]
      exact hne
    have hbetaA : (D.k : ℕ∞) < betaN 0 (normalizer (A : Set G)) A := by
      rw [hMnormA, hAeq, CFSG.LocalAnalysis.WeakClosure81.betaN_conj]
      exact hbeta
    have hVA : IsElemAbelian 2 A := hAeq.symm ▸ hVx
    obtain ⟨g, -, hg⟩ := six_nine_two_core_of_isE (M := normalizer (A : Set G)) (V := A)
      hVA le_rfl rfl hS rfl hAgamma le_rfl hK hkV hrA hneA hbetaA
    refine ⟨conjSubgroup V (x * g * x⁻¹), x * g * x⁻¹, rfl, ?_⟩
    have hg' : InCalO2 D.k (conjSubgroup D.M x) (conjSubgroup (⊥ : Subgroup G) x)
        (conjSubgroup V x) (x⁻¹ * (x * g * x⁻¹) * x) := by
      rw [show x⁻¹ * (x * g * x⁻¹) * x = g by group, ← hMnormA, ← hAeq,
        E3.conjSubgroup_bot]
      exact hg
    exact (inCalO2_conj x (x * g * x⁻¹)).1 hg'
  obtain ⟨X, g, hX, hg⟩ := hbot
  exact ⟨X, g, hX, (inCalO2_iff_inCalO2_bot (B2F.isPGroup_of_isElemAbelian hV)
    (Hyp125.normalizer_eq h) h.pairFacts.le_normalizer₀
    (B2F.isPGroup_of_isElemAbelian h.pairFacts.elemAbelian₀) hr).2 hg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
