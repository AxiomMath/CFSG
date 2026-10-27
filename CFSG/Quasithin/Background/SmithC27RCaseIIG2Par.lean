module

public import CFSG.Quasithin.Background.SmithC27RCaseIOrd
public import CFSG.Quasithin.Background.SmithC27RMS
public import CFSG.Quasithin.Background.SmithC27RTypeGen
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem isMaxParabolic2_inf_normalizer_of_radical {Γ : Type} [Group Γ] {L U : Subgroup Γ}
    (hBT : IsRadicalParabolic L) (hMax : MaxParabolicMaximal L) (hL : pCoreOf 2 L = ⊥)
    (hUL : U ≤ L) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hrad : pCoreOf 2 (L ⊓ Subgroup.normalizer (U : Set Γ)) = U) (hnS : ¬ IsSylowTwoOf U L) :
    IsMaxParabolic2 L (L ⊓ Subgroup.normalizer (U : Set Γ)) ∧
      ∀ Y : Subgroup Γ, L ⊓ Subgroup.normalizer (U : Set Γ) ≤ Y → Y ≠ L → Y ≤ L →
        Y = L ⊓ Subgroup.normalizer (U : Set Γ) := by
  have hne : L ⊓ Subgroup.normalizer (U : Set Γ) ≠ L := fun heq => hU1 (by rw [← hrad, heq, hL])
  refine hMax _ (hBT U hUL hU1 hU2 hrad) ?_ hne
  rintro ⟨S, hS, hB⟩
  have hSU : S ≤ U := by
    rw [← hrad, hB]
    exact le_pCoreOf_of_le_normalizer 2 (le_inf hS.1 Subgroup.le_normalizer) inf_le_right hS.2.1
  exact hnS ⟨hUL, hU2, fun h2 => hS.2.2 (h2.trans (Subgroup.index_dvd_of_le fun x hx => hSU hx))⟩

section Data

variable {G : Type} [Group G]

structure G2StarData (R K V : Subgroup G) : Prop where
  psu : IsPSU 3 3 1 ↥(autOn K V)
  g2Two : IsG2Two ↥(autOn (K ⊔ R) V)
  radPar : IsRadicalParabolic (autOn (K ⊔ R) V)
  maxPar : MaxParabolicMaximal (autOn (K ⊔ R) V)

end Data

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

private theorem sl3_ne_6048_mul {m c : ℕ} (hc : Odd c) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 6048 * c := by
  obtain ⟨k, rfl⟩ := hc
  rcases m with _ | _ | m
  · norm_num
  · norm_num
    omega
  · intro h
    have h64 : 2 ^ 6 ∣ (2 ^ (m + 2)) ^ 3 * (((2 ^ (m + 2)) ^ 2 - 1) * ((2 ^ (m + 2)) ^ 3 - 1)) := by
      refine Dvd.dvd.mul_right ?_ _
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    rw [h] at h64
    omega

theorem isG2Block_of_card_autOn (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hK : Nat.card ↥(autOn K V) = 6048)
    (hc : IsG2Block K ∨ IsAltBlockType K 6 ∨ IsSp4Block K ∨ IsHatA6Block K ∨
      ∃ (m : ℕ) (F' : Type) (_ : Field F') (_ : Fintype F')
        (α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F')),
        Fintype.card F' = 2 ^ m ∧ IsModO2Surj K α) :
    IsG2Block K := by
  obtain ⟨c, hco, -, hN⟩ := hs.exists_card_quot_eq
  rw [hK] at hN
  rcases hc with hb | ⟨-, α, hα, hker, -⟩ | ⟨-, F, _, _, hF4, α, hα, hker, -⟩ | hb |
      ⟨m, F', _, _, α, hF', hα⟩
  · exact hb
  · let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(alternatingGroup (Fin 6)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, Setup.X3.card_alt6] at hN
    omega
  · let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, card_statedSp_two', Nat.card_eq_fintype_card, hF4] at hN
    omega
  · have := card_autOn_of_hatA6 h hs hb
    omega
  · exact absurd ((card_quot_of_isModO2Surj hF' hα).1.symm.trans hN) (sl3_ne_6048_mul hco)

namespace G2StarData

variable (hd : G2StarData R K V)
include hd

omit [Finite G] in
theorem card_K : Nat.card ↥(autOn K V) = 6048 := SBc11.card_of_isPSU_three_three hd.psu

omit [Finite G] in
theorem center_K : Subgroup.center ↥(autOn K V) = ⊥ :=
  SBc11.center_eq_bot_of_list (Or.inr (Or.inr hd.psu))

omit [Finite G] in
theorem not_le (hs : StarHyp R K V) : ¬ autOn R V ≤ autOn K V := by
  intro hle
  have h1 : autOn (K ⊔ R) V = autOn K V := by rw [hs.autOn_sup, sup_eq_left.2 hle]
  have h2 := hd.g2Two.1
  rw [h1, hd.card_K] at h2
  omega

theorem maxParabolic (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V) :
    autOn (M ⊓ K) V ⊔ autOn R V =
        autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) ∧
      IsMaxParabolic2 (autOn (K ⊔ R) V) (autOn (M ⊓ K) V ⊔ autOn R V) := by
  set P := autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) with hP
  have hRX : autOn R V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_right
  have hR1 : autOn R V ≠ ⊥ := fun hb => hd.not_le hs (hb ▸ bot_le)
  have hnS' : ¬ IsSylowTwoOf (autOn R V) (autOn (K ⊔ R) V) := fun h' =>
    hnS (hs.isSylowTwoOf_iff.2 h')
  obtain ⟨hmax, hY⟩ := isMaxParabolic2_inf_normalizer_of_radical hd.radPar hd.maxPar
    hs.pCore_eq_bot hRX hR1 (isPGroup_autOn hs.pgroup) hrad hnS'
  have hsyl : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) := hs.pCore_eq_inf ▸ hs.centralizer_isSylow
  have hPM : P ≤ autOn (M ⊓ (K ⊔ R)) V :=
    (autOn_inf_normalizer_le hs.le_normalizer_V le_sup_right hs.pgroup hsyl).trans
      (autOn_mono' (le_inf (sup_inf_normalizer_R_le h) inf_le_left))
  have hMne : autOn (M ⊓ (K ⊔ R)) V ≠ autOn (K ⊔ R) V := by
    intro heq
    apply autOn_MK_ne h hs
    rw [hs.autOn_inf_M h.R_le_M, heq]
    exact inf_eq_right.2 (autOn_mono' le_sup_left)
  have hMP : autOn (M ⊓ (K ⊔ R)) V = P := hY _ hPM hMne (autOn_mono' inf_le_right)
  have hRP : autOn R V ≤ P := le_inf hRX Subgroup.le_normalizer
  have hsup : autOn (M ⊓ K) V ⊔ autOn R V = P := by
    rw [hs.autOn_inf_M h.R_le_M, hMP]
    refine le_antisymm (sup_le inf_le_left hRP) fun φ hφ => ?_
    obtain ⟨x, hx, rfl⟩ := mem_autOn_iff'.1 hφ.1
    obtain ⟨k, hk, r, hr, hkr⟩ := hs.mem_sup.1 hx
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hs.K_le_normalizer_V hk
    have hrN : r ∈ Subgroup.normalizer (V : Set G) := hs.R_le_normalizer_V hr
    have e : x = ⟨k, hkN⟩ * ⟨r, hrN⟩ := Subtype.ext hkr
    have hr' : conjAct V ⟨r, hrN⟩ ∈ autOn R V := mem_autOn_iff'.2 ⟨_, hr, rfl⟩
    have hk' : conjAct V ⟨k, hkN⟩ ∈ autOn K V := mem_autOn_iff'.2 ⟨_, hk, rfl⟩
    have hkP : conjAct V ⟨k, hkN⟩ ∈ P := by
      have e' : conjAct V ⟨k, hkN⟩ = conjAct V x * (conjAct V ⟨r, hrN⟩)⁻¹ := by
        rw [e, map_mul, mul_inv_cancel_right]
      rw [e']
      exact P.mul_mem hφ (P.inv_mem (hRP hr'))
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hkP, hk'⟩) (Subgroup.mem_sup_right hr')
  exact ⟨hsup, by rw [hsup]; exact hmax⟩

theorem isRankTwoLie2Derived (hs : StarHyp R K V) :
    IsRankTwoLie2Derived ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  obtain ⟨e⟩ := hs.nonempty_quotCenterEquiv
  let e' := e.trans ((QuotientGroup.quotientMulEquivOfEq hd.center_K).trans
    QuotientGroup.quotientBot)
  obtain ⟨hadm, F, hF, hFf, hFc, ⟨φ⟩⟩ := hd.psu
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hadm, F, hF, hFf, hFc, ⟨e'.trans φ⟩⟩))))))

theorem isMSPair (h : Hyp27 H R M K) (hs : StarHyp R K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V) :
    IsMSPair (K ⊔ R) R := by
  obtain ⟨heq, ⟨-, S, hS, hSP⟩, -⟩ := hd.maxParabolic h hs hnS hrad
  rw [heq] at hSP
  have hSR : S ≤ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) := fun s hsS =>
    (hSP ⟨hS.1 hsS, Subgroup.le_normalizer hsS⟩).2
  exact isMSPair_of h (hd.isRankTwoLie2Derived hs) (exists_sylow_le_normalizer_of_star hs hS hSR)

theorem three (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V) :
    C27Three H R M K V := by
  have hB : IsG2Block K := isG2Block_of_card_autOn h hs hd.card_K
    (hC132 G (K ⊔ R) R K (hd.isMSPair h hs hnS hrad) h.mem_cComp_sup h.coe_sup)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hB, hd.g2Two, (hd.maxParabolic h hs hnS hrad).2⟩)))))

end G2StarData

end CFSG.Quasithin.SmithC27
