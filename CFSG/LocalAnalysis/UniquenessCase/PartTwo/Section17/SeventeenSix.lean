module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Models.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
public import CFSG.Alternating.Multipliers.Small
public import CFSG.GH74.KGroups.A5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixteen
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.Quasithin.H13.A5W1618f
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Defs
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_isLieOverOdd17_of_isChev {X : Type} [Group X] {r : ℕ} (hr : r ≠ 2)
    (h : IsChev X r) : ∃ q : ℕ, IsLieOverOdd17 X r q := by
  obtain ⟨t, n, f, hadm, hlie⟩ := h
  exact ⟨r ^ f, hadm.1, hr, t, n, f, hadm, rfl, hlie⟩

theorem alt_five_of_odd_central_extension
    {E : Type} [Group E] [Finite E] (Z : Subgroup E) [Z.Normal]
    (hZ : Z ≤ Subgroup.center E) (hperf : commutator E = ⊤) (hodd : Odd (Nat.card Z))
    (e : E ⧸ Z ≃* alternatingGroup (Fin 5)) :
    Nonempty (E ≃* alternatingGroup (Fin 5)) := by
  classical
  haveI : Group.IsPerfect E := Group.isPerfect_def.mpr hperf
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by norm_num)
  have hc5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    CFSG.Walter.center_eq_bot_of_isSimpleGroup
      ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩,
        ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by decide⟩, by decide⟩
  have hcenter : Subgroup.center E = Z := by
    refine le_antisymm ?_ hZ
    intro x hx
    have hmem : (QuotientGroup.mk' Z x : E ⧸ Z) ∈ Subgroup.center (E ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g]
    have hc : e (QuotientGroup.mk' Z x) ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hmem g]
    have hc1 : e (QuotientGroup.mk' Z x) = 1 := by
      have hmem' : e (QuotientGroup.mk' Z x) ∈ (⊥ : Subgroup (alternatingGroup (Fin 5))) :=
        hc5 ▸ hc
      exact Subgroup.mem_bot.mp hmem'
    have h1 : (QuotientGroup.mk' Z x : E ⧸ Z) = 1 :=
      e.injective (by rw [hc1, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hdvd : Nat.card (Subgroup.center E) ∣ 2 := by
    have h := uc22p20r_card_center_dvd_hopf (K := E) (X := alternatingGroup (Fin 5))
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans e)
    have h2 := CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five.2
    rw [h2] at h
    exact h
  have hoddE : Odd (Nat.card (Subgroup.center E)) := by rw [hcenter]; exact hodd
  have hcard1 : Nat.card Z = 1 := by
    rw [← hcenter, hcenter] at *
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd hoddE (by rw [h]; norm_num)
  have hZbot : Z = ⊥ := Subgroup.card_eq_one.mp hcard1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem lieModel_psl_two_five_of_odd_central_extension
    {E : Type} [Group E] [Finite E] (Z : Subgroup E) [Z.Normal]
    (hZ : Z ≤ Subgroup.center E) (hperf : commutator E = ⊤) (hodd : Odd (Nat.card Z))
    (h : LieModel (E ⧸ Z) .PSL 2 5 1) : LieModel E .PSL 2 5 1 := by
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.A5.equiv_of_lieModel25 h
  obtain ⟨e2⟩ := alt_five_of_odd_central_extension Z hZ hperf hodd
    (e1.trans (MulEquiv.subgroupCongr CFSG.GH74.KGroups.A5.QP_eq_alt))
  exact Or.inl ⟨by decide,
    CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five E
      ⟨e2⟩⟩

theorem concl17_6_of_isL2Over17_five
    {D : Data G} {L : Subgroup G} {r : ℕ}
    (hK2 : CFSG.ComponentClassification.GS82PumpInputs.OddLieCharUnique)
    (hL : L ∈ calC D.M) (hr : r ≠ 2) (hchev : IsChev (BarInf L) r)
    (h5 : IsL2Over17 (BarInf L) 5) : Concl17_6 D L r := by
  obtain ⟨r', f, hr'p, hr'2, h5eq, hf, hlie⟩ := h5
  have hf1 : f = 1 := by
    rcases Nat.lt_or_ge f 2 with h | h
    · omega
    · exfalso
      have hdvd : r' ^ 2 ∣ r' ^ f := pow_dvd_pow r' h
      rw [← h5eq] at hdvd
      have hle : r' ^ 2 ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
      have h2 : 2 ≤ r' := hr'p.two_le
      have h3 : r' = 2 := by
        rcases (by omega : r' = 2 ∨ 3 ≤ r') with h | h
        · exact h
        · exfalso
          have h9 : 9 ≤ r' ^ 2 := by
            have h' : 3 * 3 ≤ r' * r' := Nat.mul_le_mul h h
            simpa [pow_two] using h'
          omega
      exact hr'2 h3
  subst hf1
  have hr'5 : r' = 5 := by
    rw [pow_one] at h5eq
    omega
  subst hr'5
  obtain ⟨t, n, fq, -, hchevLie⟩ := hchev
  have hr5 : r = 5 :=
    hK2 (BarInf L) t n r fq .PSL 2 5 1 hr (by norm_num) hchevLie hlie
  subst hr5
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hlieZ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 2 5 1 :=
    LieModel.of_mulEquiv e hlie
  have hperf : commutator (Bar2 L) = ⊤ :=
    Group.isPerfect_def.mp ((CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hL.2.2).1
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using UC22.uc22p20p_odd_center_bar2 ↥L
  have hlie2 : LieModel (Bar2 L) .PSL 2 5 1 :=
    lieModel_psl_two_five_of_odd_central_extension (Subgroup.center (Bar2 L)) le_rfl hperf hodd
      hlieZ
  exact ⟨⟨5, 1, Nat.prime_five, by decide, by norm_num, le_rfl, hlie2⟩,
    fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩

private theorem not_lt_add_of_le_add {m b k : ℕ} {i : ℕ∞} (h1 : m ≤ b + k) :
    ¬ ((k : ℕ∞) + i + (b : ℕ∞) < (m : ℕ∞)) := by
  have hA : (m : ℕ∞) ≤ (b : ℕ∞) + (k : ℕ∞) := by
    have h' : ((m : ℕ) : ℕ∞) ≤ ((b + k : ℕ) : ℕ∞) := by exact_mod_cast h1
    simpa using h'
  have hB : (b : ℕ∞) + (k : ℕ∞) ≤ (k : ℕ∞) + i + (b : ℕ∞) := by
    have h : (k : ℕ∞) ≤ (k : ℕ∞) + i := le_add_of_nonneg_right zero_le
    calc (b : ℕ∞) + (k : ℕ∞) = (k : ℕ∞) + (b : ℕ∞) := add_comm _ _
      _ ≤ ((k : ℕ∞) + i) + (b : ℕ∞) := add_le_add_left h _
      _ = (k : ℕ∞) + i + (b : ℕ∞) := rfl
  exact not_lt_of_ge (hA.trans hB)

theorem barSub_ne_bot_of_bot (D : Data G) (h127 : R127 D) {V L : Subgroup G}
    (hV : Hyp125 D ⊥ V) (hL : L ∈ calC D.M) (h7 : UniqueMax D.M L) :
    barSub ⊥ V hV.isElemAbelian L ≠ ⊥ := by
  intro hbot
  have hP := hV.pairFacts
  have hLct : L ≤ F11.CTilde D.M ⊥ V :=
    (WeakClosure81.barSub_eq_bot_iff (M := D.M) (V₀ := ⊥) (V := V) (B := L)
      hP.elemAbelian hP.le_normalizer hP.le_normalizer₀ hL.1.le).1 hbot
  rw [uc22p22u_cTilde_bot] at hLct
  exact (twelve_nine D h127 hV).1
    (uc22p22u_isTI_of_uniqueMax D hP.elemAbelian hP.le_normalizer (hLct.trans inf_le_right) h7)

theorem exists_ctx17_6 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hL2five : ∀ L ∈ calC D.M, ∀ r : ℕ, r ≠ 2 → IsChev (BarInf L) r →
      IsL2Over17 (BarInf L) 5 → Concl17_6 D L r)
    {L₀ : Subgroup G} {r₀ : ℕ} (hc₀ : IsCounterexample17_6 D L₀ r₀) :
    ∃ (L : Subgroup G) (r q : ℕ), Ctx17_6 D V₀ V L r q := by
  classical
  obtain ⟨hc₀₁, hc₀₂, hc₀₃, hc₀₄⟩ := hc₀
  by_cases hA : ∃ (L : Subgroup G) (r : ℕ), IsCounterexample17_6 D L r ∧ ¬ IsL2Over17 (Bar2 L) r
  ·
    obtain ⟨L, r, hc, hNL⟩ := hA
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
    obtain ⟨q, hq⟩ := exists_isLieOverOdd17_of_isChev hc2 hc3
    exact ⟨L, r, q, hV, hc1, hq, fun h5 => hc4 (hL2five L hc1 r hc2 hc3 h5), hc4,
      fun hL2 => absurd hL2 hNL, fun hL2 => absurd hL2 hNL⟩
  ·
    have hall : ∀ (L : Subgroup G) (r : ℕ), IsCounterexample17_6 D L r → IsL2Over17 (Bar2 L) r := by
      intro L r hc
      by_contra h
      exact hA ⟨L, r, hc, h⟩
    by_cases h7 : ∃ (L : Subgroup G) (r : ℕ), IsCounterexample17_6 D L r ∧ r = 7
    · obtain ⟨L, r, hc, hr7⟩ := h7
      obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
      obtain ⟨q, hq⟩ := exists_isLieOverOdd17_of_isChev hc2 hc3
      exact ⟨L, r, q, hV, hc1, hq, fun h5 => hc4 (hL2five L hc1 r hc2 hc3 h5), hc4,
        fun _ => hall, fun _ _ => hr7⟩
    ·
      obtain ⟨q, hq⟩ := exists_isLieOverOdd17_of_isChev hc₀₂ hc₀₃
      exact ⟨L₀, r₀, q, hV, hc₀₁, hq, fun h5 => hc₀₄ (hL2five L₀ hc₀₁ r₀ hc₀₂ hc₀₃ h5), hc₀₄,
        fun _ => hall, fun _ h => absurd h h7⟩

theorem seventeen_six_reductio_bot (D : Data G) (V₀ V : Subgroup G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h7 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q), R17_7At D V₀ V L r q hC)
    (h127 : R127 D)
    (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h15 : R17_15At D 𝔉 V₀ V L r q hC) (hV₀ : V₀ = ⊥) : False := by
  have hLM : CFSG.Open.IsSubnormal L D.M := hC.memL.1
  have hU : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le hLM.le) (h7 L r q hC).1
  have hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ := by
    subst hV₀
    exact barSub_ne_bot_of_bot D h127 hC.hyp125 hC.memL (h7 L r q hC).1
  have h1 : mBar D.M V₀ V hC.hyp125.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian + D.k :=
    twelve_twentyThree_one D hx h61 h126 h111 hC.hyp125 hV₀ hLM hC.memL.2.2 hL1 hU
  exact not_lt_add_of_le_add h1 h15

theorem O2_case_one (D : Data G) (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h1 : P17_12_1 r q L) (h7 : R17_7At D V₀ V L r q hC) :
    ∀ H ∈ Delta17_12 D 𝔉 r q L, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
  intro H hH g hg
  unfold Delta17_12 at hH
  rw [dif_pos h1] at hH
  obtain ⟨x, hx, rfl⟩ := hH
  have hperf : ⁅L.map (MulAut.conj x).toMonoidHom, L.map (MulAut.conj x).toMonoidHom⁆ =
      L.map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_commutator, hC.memL.2.1]
  have hres : L.map (MulAut.conj x).toMonoidHom ≤
      twoResidual (D.T ⊔ L.map (MulAut.conj x).toMonoidHom) :=
    CFSG.Quasithin.H13.A5.le_twoResidual_of_perfect hperf le_sup_right
  have hMx : conjSubgroup D.M x⁻¹ = D.M := by
    ext a
    rw [CFSG.Quasithin.mem_conjSubgroup_iff, inv_inv]
    constructor
    · intro h
      have h' := D.M.mul_mem (D.M.mul_mem hx h) (D.M.inv_mem hx)
      simpa [mul_assoc] using h'
    · intro h
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hx) h) hx
  have hLx : conjSubgroup L x⁻¹ = L.map (MulAut.conj x).toMonoidHom := by
    simp [CFSG.Quasithin.conjSubgroup]
  have hU : UniqueMax D.M (L.map (MulAut.conj x).toMonoidHom) := by
    have h := uniqueMax_conjSubgroup h7.1 x⁻¹
    rwa [hMx, hLx] at h
  exact twoResidual_not_le_conjSubgroup_of_uniqueMax D.maxLocal hU hres hg

section Certificates

theorem reductio_of_O2 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) (hV₀ : V₀ ≠ ⊥)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥)
    (h15 : R17_15At D 𝔉 V₀ V L r q hC) (h16 : R17_16At D 𝔉 V₀ V L r q hC)
    (hO2 : ∀ H ∈ Delta17_12 D 𝔉 r q L, ∀ g : G, g ∉ D.M →
      ¬ twoResidual H ≤ conjSubgroup D.M g) : False := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hfin : (Delta17_12 D 𝔉 r q L).Finite := Set.toFinite _
  set Δ : Finset (Subgroup G) := hfin.toFinset with hΔdef
  have hmem : ∀ H, H ∈ Δ ↔ H ∈ Delta17_12 D 𝔉 r q L := fun H => hfin.mem_toFinset
  have hle : ∀ H ∈ Delta17_12 D 𝔉 r q L, fIndex H ≤ iL17_12 D 𝔉 r q L := fun H hH => by
    unfold iL17_12 fIndexMax
    exact le_iSup₂ (f := fun H (_ : H ∈ Delta17_12 D 𝔉 r q L) => fIndex H) H hH
  have hiL : iL17_12 D 𝔉 r q L ≠ ⊤ := by
    intro htop
    have h := h15
    unfold R17_15At at h
    rw [htop] at h
    simp at h
  have hfi : ∀ H ∈ Delta17_12 D 𝔉 r q L, fIndex H ≠ ⊤ := fun H hH htop =>
    hiL (top_le_iff.mp (by rw [← htop]; exact hle H hH))
  have hT : ∀ H ∈ Delta17_12 D 𝔉 r q L, D.T ≤ H := by
    intro H hH
    unfold Delta17_12 at hH
    by_cases h1 : P17_12_1 r q L
    · rw [dif_pos h1] at hH
      obtain ⟨x, -, rfl⟩ := hH
      exact le_sup_left
    · by_cases h2 : P17_12_2 q L
      · rw [dif_neg h1, dif_pos h2] at hH
        obtain ⟨X, -, -, -, rfl⟩ := hH
        exact le_sup_left
      · rw [dif_neg h1, dif_neg h2] at hH
        obtain ⟨x, -, X, hX⟩ := hH
        obtain ⟨-, -, hHX, -⟩ := hX
        rw [hHX]
        exact le_sup_left
  have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := fun H hH =>
    ⟨hT H ((hmem H).1 hH),
      (le_iSup₂ (f := fun H (_ : H ∈ Delta17_12 D 𝔉 r q L) => H) H ((hmem H).1 hH)).trans
        (SeventeenSixteen.delta_le_M D 𝔉 V₀ V L r q hC)⟩
  have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
    have heq : (⨆ H ∈ Δ, H) = ⨆ H ∈ Delta17_12 D 𝔉 r q L, H :=
      iSup_congr fun H => iSup_congr_Prop (hmem H) fun _ => rfl
    rw [heq]
    exact h16
  have hι : ∀ H ∈ Δ, WeakClosure81.InFSq ((fun H => (fIndex H).toNat) H) H := fun H hH =>
    inFSq_toNat_fIndex (hfi H ((hmem H).1 hH))
  have h3 := twelve_twentyThree_three D hx h61 h127 h1114 h162 hTor h1482 h126 hC.hyp125 hV₀
    hC.memL.1 hC.memL.2.2 hL1 hΔ hΔU (fun H => (fIndex H).toNat) hι
    (fun H hH => hO2 H ((hmem H).1 hH))
  have hsup : Δ.sup (fun H => (fIndex H).toNat) ≤ (iL17_12 D 𝔉 r q L).toNat :=
    Finset.sup_le fun H hH => ENat.toNat_le_toNat (hle H ((hmem H).1 hH)) hiL
  have h15' : D.k + (iL17_12 D 𝔉 r q L).toNat +
      bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian <
      mBar D.M V₀ V hC.hyp125.isElemAbelian := by
    have h := h15
    unfold R17_15At at h
    rw [← ENat.coe_toNat hiL] at h
    exact_mod_cast h
  omega

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
