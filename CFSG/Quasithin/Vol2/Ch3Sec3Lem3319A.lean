module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318E

public section

namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem pCoreOf_ne_bot (h : Hyp331 G T M L D) {Y : Subgroup G}
    (hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ := by
  set Z := quasithinOmegaOneCenter T with hZ
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZ2 : IsPGroup 2 Z := h.sylow.1.to_le hZT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot h.sylow.1 h.toSetup331.T_ne_bot
  have hN : Y ⊔ T ⊔ D ≤ Subgroup.normalizer (Z : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hYZ.trans (Subgroup.centralizer_le_normalizer _)
    · exact (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact h.DN.trans (Hyp331.normalizer_le_normalizer_of_characteristic hZT
        (CFSG.QuasithinUnique.L246C127.characteristic_omegaOneCenter T))
  have hle : Z ≤ pCoreOf 2 (Y ⊔ T ⊔ D) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hZT.trans (le_sup_right.trans le_sup_left)) hN hZ2
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact hZ1 hle

theorem le_normalizer_of_hom (h : Hyp331 G T M L D) (h12 : Step3_3_12R) {Y : Subgroup G}
    (hYL : Y ≤ L) (hY : ⁅Y, Y⁆ = Y) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.pCore 2 ↥Y) :
    Y ∈ lFamilyOf L T ∧ D ≤ Subgroup.normalizer (Y : Set G) := by
  have : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) le_rfl
  have hk : IsPGroup 2 ψ.ker := by
    rw [hψk]
    exact CFSG.pCore_isPGroup
  have hmem : Y ∈ lFamilyOf L T :=
    L3316.mem_lFamilyOf_of_hom h.sylow h.toSetup331.pCoreOf_ne_bot hYL hY hTY ψ hψs hk
  have ht : L3312.Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Or.inr (Or.inl (L3318.isPSL_of_hom le_rfl hψs hψk))
  refine ⟨hmem, ?_⟩
  obtain ⟨-, -, -, -, hDN | ⟨hpsl, -⟩⟩ := h12 G T M L D Y h hmem (pCoreOf_ne_bot h hYZ) ht
  · exact hDN
  · exact (L3318.not_isPSL_two_two le_rfl (by norm_num) hψs hψk hpsl).elim

omit [Finite G] in
theorem thompsonJ_le (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup₂_le fun _ hA => hA.1

theorem false_of_thompsonJ_le
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {Y : Subgroup G}
    (hYL : Y ≤ L) (hDY : D ≤ Subgroup.normalizer (Y : Set G))
    (hJ : thompsonJ (pCoreOf 2 (Y ⊔ T)) ≤ Subgroup.centralizer (vPlus L T : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := pCoreOf 2 (Y ⊔ T) with hS
  set R := pCoreOf 2 (L ⊔ T) with hR
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := h.toSetup331.isSylowTwoOf
  have hRT : R ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylLT
  have hYTLT : Y ⊔ T ≤ L ⊔ T := sup_le_sup_right hYL T
  have hRS : R ≤ S := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hRT.trans le_sup_right) (hYTLT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hsylYT : IsSylowTwoOf T (Y ⊔ T) := ⟨le_sup_right, h.sylow.1, fun h2 =>
    h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hST : S ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylYT
  have hJR : thompsonJ S ≤ R := by
    rw [hR, ← (Hyp331.centralizer_vPlus h h38 h39).2.1]
    exact le_inf ((thompsonJ_le S).trans hST) hJ
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVR : vPlus L T ≤ R := hred.1.trans inf_le_left
  have hV1 : vPlus L T ≠ ⊥ := by
    intro hbot
    have hZV : quasithinOmegaOneCenter T ≤ vPlus L T := le_conjClosure _ _
    rw [hbot, le_bot_iff] at hZV
    exact Setup.omegaOneCenterOf_ne_bot h.sylow.1 h.toSetup331.T_ne_bot hZV
  have hpos : 0 < CFSG.Open.pRank 2 S := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
    have hc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    rw [pow_zero, mul_one] at hc
    have hVA : Nat.card (vPlus L T) ≤ Nat.card A := hA.2.2 _ (hVR.trans hRS) hred.2.1
    have hV2 : 2 ≤ Nat.card (vPlus L T) := by
      rcases Nat.lt_or_ge (Nat.card (vPlus L T)) 2 with hlt | hge
      · exfalso
        apply hV1
        rw [← Subgroup.card_le_one_iff_eq_bot]
        omega
      · exact hge
    by_contra h0
    rw [Nat.not_lt, Nat.le_zero] at h0
    rw [h0, pow_zero] at hc
    omega
  have hJeq : thompsonJ S = thompsonJ R := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le hpos (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJR) hRS
  have hDS : D ≤ Subgroup.normalizer (S : Set G) :=
    (CFSG.LieType.Steinberg.le_normalizer_sup hDY h.DN).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hDJ : D ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
    rw [← hJeq]
    exact hDS.trans (Hyp331.normalizer_le_normalizer_of_characteristic (thompsonJ_le S)
      (S1414.characteristic_thompsonJ S))
  have hLJ : L ⊔ T ≤ Subgroup.normalizer (thompsonJ R : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (Hyp331.normalizer_le_normalizer_of_characteristic (thompsonJ_le R)
        (S1414.characteristic_thompsonJ R))
  have hJ1 : thompsonJ R ≠ ⊥ := by
    intro hbot
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian R
    have hAJ : A ≤ thompsonJ R := le_iSup₂_of_le (f := fun (B : Subgroup G)
      (_ : IsMaxElemAbelian R B) => B) A hA le_rfl
    rw [hbot, le_bot_iff] at hAJ
    have hVA : Nat.card (vPlus L T) ≤ Nat.card A := hA.2.2 _ hVR hred.2.1
    rw [hAJ, Subgroup.card_bot, Subgroup.card_le_one_iff_eq_bot] at hVA
    exact hV1 hVA
  exact h.not_le_normalizer h38 h39 hJ1
    ((thompsonJ_le R).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) hLJ hDJ

theorem thompsonJ_le_of_offender (h : Hyp331 G T M L D) [IsMulCommutative ↥(vPlus L T)]
    {S : Subgroup G} (hSLT : S ≤ L ⊔ T) (hVS : vPlus L T ≤ S)
    (hoff : ∀ B : Subgroup (MulAut ↥(vPlus L T)),
      IsFFStarOffender (autOn (L ⊔ T) (vPlus L T)) B → B ≤ autOn S (vPlus L T) → False) :
    thompsonJ S ≤ Subgroup.centralizer (vPlus L T : Set G) := by
  set V := vPlus L T with hVdef
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hV : CFSG.Open.IsElemAbelian 2 V := hred.2.1
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  refine iSup₂_le fun A hA => ?_
  by_contra hAC
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans (hSLT.trans hHV)
  have hcard := card_le_relIndex_mul_card hV hVS hA
  rw [← card_autOn_eq_relIndex hAn, ← card_fixV_autOn_eq hV hAn] at hcard
  have hA2 : IsA2 (autOn (L ⊔ T) V) (autOn A V) :=
    ⟨autOn_le_autOn V (hA.1.trans hSLT), autOn_ne_bot_of_not_le_centralizer hAn hAC,
      isElemAbelian2_autOn hV hA.2.1 hAn⟩
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 (by simpa using hcard)
  exact hoff B hB (hBA.trans (autOn_le_autOn V hA.1))

theorem false_of_offender
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h12 : Step3_3_12R)
    [IsMulCommutative ↥(vPlus L T)] {Y : Subgroup G} (hYL : Y ≤ L) (hY : ⁅Y, Y⁆ = Y)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.pCore 2 ↥Y)
    (hoff : ∀ B : Subgroup (MulAut ↥(vPlus L T)),
      IsFFStarOffender (autOn (L ⊔ T) (vPlus L T)) B →
        B ≤ autOn (pCoreOf 2 (Y ⊔ T)) (vPlus L T) → False) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hDY⟩ := le_normalizer_of_hom h h12 hYL hY hTY hYZ hψs hψk
  have hred := Hyp331.vPlus_reduced h.toSetup331
  set S := pCoreOf 2 (Y ⊔ T) with hS
  have hYTLT : Y ⊔ T ≤ L ⊔ T := sup_le_sup_right hYL T
  have hSLT : S ≤ L ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hYTLT
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := h.toSetup331.isSylowTwoOf
  have hRT : pCoreOf 2 (L ⊔ T) ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylLT
  have hRS : pCoreOf 2 (L ⊔ T) ≤ S := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hRT.trans le_sup_right) (hYTLT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hVS : vPlus L T ≤ S := (hred.1.trans inf_le_left).trans hRS
  exact false_of_thompsonJ_le h h38 h39 hYL hDY
    (thompsonJ_le_of_offender h hSLT hVS hoff)

end CFSG.Quasithin.H13.L3319
