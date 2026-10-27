module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddRee
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeSevenTools
import CFSG.Walter.ReeOrder.JT.Section2
import CFSG.Walter.ReeOrder.JT.Section7C
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement MatrixGroups

@[expose] def UC2_10_7OddReeSevenInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ∀ f : ℕ,
    CFSG.Blueprint.LieModel X .twistedG2 0 3 f →
    ∀ (T B M : Subgroup X), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      B ≤ normalizer (T : Set X) → Nat.card B = 7 → T ≤ M → B ≤ M →
      (∀ g : X, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) → M = ⊤

@[expose] def UC2_10_7OddReeSevenInnerPhi6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ∀ f : ℕ,
    CFSG.Blueprint.LieModel X .twistedG2 0 3 f → ¬ 7 ∣ 3 ^ f + 1 →
    ∀ (T B M : Subgroup X), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      B ≤ normalizer (T : Set X) → Nat.card B = 7 → T ≤ M → B ≤ M →
      (∀ g : X, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) → M = ⊤

@[expose] def UC2_10_7OddReeSevenOuter : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), L.Normal → IsSimpleGroup ↥L →
    centralizer (L : Set A) = ⊥ → ∀ f : ℕ, CFSG.Blueprint.LieModel ↥L .twistedG2 0 3 f →
    ∀ (T B M : Subgroup A), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      B ≤ normalizer (T : Set A) → Nat.card B = 7 → ¬ B ≤ L →
      L ⊔ T ⊔ B = ⊤ → T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
      L ≤ M ∨ ⁅T, B⁆ = ⊥

theorem ree_exists_jtHyp
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {f : ℕ} (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 f) {v : X} (hv : orderOf v = 2) :
    ∃ J : CFSG.Walter.JT.JTHyp X, J.p = 3 ∧ J.f = f ∧ J.t = v := by
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  have hk : 1 ≤ k := by omega
  have hree : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * k + 1) :=
    (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, -, hcen, -, -⟩ :=
    CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
      k hk X hree
  obtain ⟨F, hFC, hinf, hsup, ⟨e⟩, -⟩ := hcen v hv
  have hgen := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_ReeSylowGeneration_holds
    X (3 ^ (2 * k + 1)) k ⟨k, rfl, hmod⟩ rfl hk
  refine ⟨{ p := 3
            f := 2 * k + 1
            five_lt := ?_
            abelian_sylow := fun P => (hgen.2.2 P).1.1
            index_ne_two := ?_
            t := v
            orderOf_t := hv
            F := F
            le_centralizer := hFC
            t_not_mem := ?_
            centralizer_eq := hsup.symm
            iso := e }, rfl, rfl, rfl⟩
  · calc 5 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro H hH
    have hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
    rcases (haveI := hHn; hXs.eq_bot_or_eq_top_of_normal H) with h | h
    · rw [h, Subgroup.index_bot] at hH
      obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := X)
      have h8 := (hgen.2.2 P).2.1
      have hcard := Subgroup.index_mul_card (H := (P : Subgroup X))
      rw [h8] at hcard
      omega
    · rw [h, Subgroup.index_top] at hH
      omega
  · intro hmem
    have hbot : v ∈ (⊥ : Subgroup X) := by
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers v, hmem⟩
    have hv1 : v = 1 := Subgroup.mem_bot.1 hbot
    rw [hv1, orderOf_one] at hv
    omega

theorem ree_sylow_two_facts
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {f : ℕ} (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 f) {T : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    Nat.card T = 8 ∧ centralizer (T : Set X) = T ∧
      (T.subgroupOf (normalizer (T : Set X))).index = 21 := by
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  have hk : 1 ≤ k := by omega
  have hree : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * k + 1) :=
    (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, ⟨⟨x, hx⟩, -⟩, -⟩ :=
    CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
      k hk X hree
  obtain ⟨J, hJp, -, -⟩ := ree_exists_jtHyp hXs hmod hx
  have hp : J.p ≠ 2 := by rw [hJp]; norm_num
  have h21 := CFSG.Walter.JT.lemma_2_1 J hp
  have hdvd : ¬ 2 ∣ T.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    rwa [Subgroup.relIndex_top_right] at h
  let S : Sylow 2 X := hT.isPGroup.toSylow hdvd
  have hSco : (S : Subgroup X) = T := IsPGroup.toSylow_coe hT.isPGroup hdvd
  rw [← hSco]
  exact ⟨(h21.2.1 S).2, h21.2.2.2.1 S, (h21.2.2.2.2.1 S).1⟩

theorem reeSevenInner_eq_top_of_dvd_add_one
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {f : ℕ} (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 f) (h7 : 7 ∣ 3 ^ f + 1)
    {T B M : Subgroup X} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hBT : B ≤ normalizer (T : Set X)) (hB7 : Nat.card B = 7) (hTM : T ≤ M) (hBM : B ≤ M)
    (hstar : ∀ g : X, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) : M = ⊤ := by
  obtain ⟨hT8, hCT, hidx⟩ := ree_sylow_two_facts hXs hmod hT
  have hBC : ¬ B ≤ centralizer (T : Set X) := by
    intro h
    have h78 := Subgroup.card_dvd_of_le (hCT ▸ h)
    rw [hB7, hT8] at h78
    norm_num at h78
  have hNM : normalizer (T : Set X) ≤ M :=
    normalizer_le_of_index_eq_twentyOne hT8 hidx hBT hB7 hTM hBM hstar
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  have hk : 1 ≤ k := by omega
  have hree : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * k + 1) :=
    (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨v, hv, hvB⟩ : ∃ v : X, orderOf v = 2 ∧ ∀ b ∈ B, b * v = v * b := by
    obtain ⟨-, ⟨⟨v₀, hv₀⟩, -⟩, -⟩ :=
      CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
        k hk X hree
    obtain ⟨J₀, hJ₀p, hJ₀f, hJ₀t⟩ := ree_exists_jtHyp hXs hmod hv₀
    have hp₀ : J₀.p ≠ 2 := by rw [hJ₀p]; norm_num
    have hcardC : Nat.card (centralizer ({v₀} : Set X)) = J₀.q * (J₀.q ^ 2 - 1) :=
      J₀.card_centralizer_of_orderOf_eq_two hp₀ hv₀
    have hcardX : Nat.card X = CFSG.Open.ordRee (3 ^ (2 * k + 1)) := by
      obtain ⟨-, -, -, -, hcard⟩ :=
        CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hree
      exact hcard
    have hq : J₀.q = 3 ^ (2 * k + 1) := by
      rw [CFSG.Walter.JT.JTHyp.q_eq, hJ₀p, hJ₀f]
    have hq2 : 2 ≤ J₀.q := by
      rw [hq]
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) (by omega : 3 ≤ 2 * k + 1)
      norm_num at h ⊢
      omega
    have h7q : 7 ∣ J₀.q + 1 := by rw [hq]; exact h7
    have hidxq : (centralizer ({v₀} : Set X)).index * (J₀.q * (J₀.q ^ 2 - 1)) =
        J₀.q ^ 3 * (J₀.q ^ 3 + 1) * (J₀.q - 1) := by
      have h1 := Subgroup.index_mul_card (H := centralizer ({v₀} : Set X))
      rw [hcardC, hcardX] at h1
      rw [hq] at h1 ⊢
      simpa [CFSG.Open.ordRee] using h1
    have hi : ¬ 7 ∣ (centralizer ({v₀} : Set X)).index :=
      not_seven_dvd_of_mul_eq hq2 h7q hidxq
    have hBp : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by rw [hB7, pow_one])
    obtain ⟨g, hg⟩ := CFSG.Monster.B.GSide.exists_conj_mem_of_not_dvd_index
      (centralizer ({v₀} : Set X)) hi hBp
    refine ⟨g⁻¹ * v₀ * g, ?_, ?_⟩
    · rw [show g⁻¹ * v₀ * g = MulAut.conj g⁻¹ v₀ by rw [MulAut.conj_apply, inv_inv]]
      rw [MulEquiv.orderOf_eq, hv₀]
    · intro b hb
      have hcomm : (g * b * g⁻¹) * v₀ = v₀ * (g * b * g⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hg b hb)
      calc b * (g⁻¹ * v₀ * g) = g⁻¹ * ((g * b * g⁻¹) * v₀) * g := by group
        _ = g⁻¹ * (v₀ * (g * b * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * v₀ * g) * b := by group
  have hvM : v ∈ M := hstar v fun b hb => by
    have hvb : v⁻¹ * b * v = b := by
      rw [mul_assoc, hvB b hb, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hvb]
    exact hBM hb
  obtain ⟨J, hJp, hJf, hJt⟩ := ree_exists_jtHyp hXs hmod hv
  have hp : J.p ≠ 2 := by rw [hJp]; norm_num
  have hBF : B ≤ J.F := by
    refine J.le_F_of_odd ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff, hJt]
      exact hvB b hb
    · rw [hB7]; exact ⟨3, rfl⟩
  obtain ⟨S, hvS, hSM⟩ : ∃ S : Sylow 2 X, v ∈ (S : Subgroup X) ∧
      normalizer ((S : Subgroup X) : Set X) ≤ M := by
    have hdvd : ¬ 2 ∣ T.index := by
      have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
      rwa [Subgroup.relIndex_top_right] at h
    have hrel : T.relIndex M * M.index = T.index := Subgroup.relIndex_mul_index hTM
    have hdvdM : ¬ 2 ∣ (T.subgroupOf M).index := by
      have hEq : (T.subgroupOf M).index = T.relIndex M := rfl
      rw [hEq]
      intro h2
      exact hdvd (hrel ▸ dvd_mul_of_dvd_left h2 M.index)
    have hvM' : orderOf (⟨v, hvM⟩ : ↥M) = 2 := by
      rw [← Subgroup.orderOf_coe, hv]
    have hP : IsPGroup 2 (Subgroup.zpowers (⟨v, hvM⟩ : ↥M)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvM', pow_one])
    obtain ⟨m, hm⟩ := CFSG.Monster.B.GSide.exists_conj_mem_of_not_dvd_index
      (T.subgroupOf M) hdvdM hP
    have hvT : (m : X) * v * (m : X)⁻¹ ∈ T := by
      have h := hm ⟨v, hvM⟩ (Subgroup.mem_zpowers _)
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    let Ssub : Subgroup X := T.map (MulAut.conj (m : X)⁻¹).toMonoidHom
    have hSsubcard : Nat.card Ssub = 8 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (m : X)⁻¹).injective, hT8]
    have hSsubP : IsPGroup 2 Ssub := IsPGroup.of_card (n := 3) (by rw [hSsubcard]; norm_num)
    have hSsubidx : ¬ 2 ∣ Ssub.index := by
      have h1 := Subgroup.index_mul_card T
      have h2 := Subgroup.index_mul_card Ssub
      rw [hT8] at h1
      rw [hSsubcard] at h2
      have hidxeq : T.index = Ssub.index := by omega
      rw [← hidxeq]
      exact hdvd
    let S : Sylow 2 X := hSsubP.toSylow hSsubidx
    have hScoe : (S : Subgroup X) = Ssub := IsPGroup.toSylow_coe hSsubP hSsubidx
    refine ⟨S, ?_, ?_⟩
    · rw [hScoe]
      have hf : (MulAut.conj (m : X)⁻¹) ((m : X) * v * (m : X)⁻¹) = v := by
        rw [MulAut.conj_apply]; group
      rw [← hf]
      exact Subgroup.mem_map_of_mem _ hvT
    · intro n hn
      rw [hScoe, ← Subgroup.map_equiv_normalizer_eq] at hn
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hn
      have hyM : y ∈ M := hNM hy
      have hmM : (m : X) ∈ M := m.2
      rw [← hyeq]
      change (MulAut.conj (m : X)⁻¹) y ∈ M
      rw [MulAut.conj_apply]
      simpa using M.mul_mem (M.mul_mem (M.inv_mem hmM) hyM) hmM
  obtain ⟨z, hzF, hz3, hzM⟩ : ∃ z ∈ J.F, orderOf z = 3 ∧ z ∈ M := by
    have htS : J.t ∈ (S : Subgroup X) := by rw [hJt]; exact hvS
    obtain ⟨z, hzF, hz3, hzN, -⟩ := (J.facts hp).exists_orderOf_eq_three (J.mod_eight hp)
      inf_le_right (J.isKleinFour_inf_F hp S htS)
    exact ⟨z, hzF, hz3, hSM (J.mem_normalizer_sylow_of_mem_F S htS hzF hzN)⟩
  have hFM : J.F ≤ M := by
    let R : Subgroup (PSL(2, GaloisField J.p J.f)) :=
      (B.subgroupOf J.F).map J.iso.toMonoidHom
    let H : Subgroup (PSL(2, GaloisField J.p J.f)) :=
      (M.subgroupOf J.F).map J.iso.toMonoidHom
    have hR : Nat.card R = 7 := by
      rw [Subgroup.card_map_of_injective J.iso.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBF).toEquiv, hB7]
    have hq5 : 5 ≤ J.p ^ J.f := by
      rw [hJp, hJf]
      calc 5 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq7 : J.p ^ J.f ≠ 7 := by
      rw [hJp, hJf]
      have h : 3 ^ 3 ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h
      omega
    have hq9 : J.p ^ J.f ≠ 9 := by
      rw [hJp, hJf]
      have h : 3 ^ 3 ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h
      omega
    have hrq : ¬ 7 ∣ J.p ^ J.f - 1 := by
      rw [hJp, hJf]
      intro hd
      have h7' : 7 ∣ 3 ^ (2 * k + 1) + 1 := h7
      have h2 : 7 ∣ (3 ^ (2 * k + 1) + 1) - (3 ^ (2 * k + 1) - 1) :=
        Nat.dvd_sub h7' hd
      have hsub : (3 ^ (2 * k + 1) + 1) - (3 ^ (2 * k + 1) - 1) = 2 := by
        have hpos : 0 < 3 ^ (2 * k + 1) := pow_pos (by norm_num) _
        omega
      rw [hsub] at h2
      norm_num at h2
    have hRH : normalizer (R : Set (PSL(2, GaloisField J.p J.f))) ≤ H := by
      intro y hy
      let xF : ↥J.F := J.iso.symm y
      have hxF : (xF : X) ∈ J.F := xF.2
      have hxy : J.iso xF = y := MulEquiv.apply_symm_apply J.iso y
      have hxM : (xF : X) ∈ M := by
        apply hstar (xF : X)
        intro b hb
        have hbF : b ∈ J.F := hBF hb
        have hbR : J.iso ⟨b, hbF⟩ ∈ R :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
        have h1 : y⁻¹ * (J.iso ⟨b, hbF⟩) * y ∈ R := by
          have hmem : y⁻¹ ∈ Subgroup.normalizer (R : Set (PSL(2, GaloisField J.p J.f))) :=
            (Subgroup.normalizer (R : Set (PSL(2, GaloisField J.p J.f)))).inv_mem hy
          have h := (Subgroup.mem_normalizer_iff.mp hmem (J.iso ⟨b, hbF⟩)).mp hbR
          simpa using h
        obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp h1
        have hc' : xF⁻¹ * (⟨b, hbF⟩ : ↥J.F) * xF = c := by
          refine J.iso.injective ?_
          rw [map_mul, map_mul, map_inv, hxy]
          exact hceq.symm
        have hcb : (xF : X)⁻¹ * b * (xF : X) = (c : X) := by
          have h := congrArg (fun t : ↥J.F => (t : X)) hc'
          simpa using h
        rw [hcb]
        exact hBM (Subgroup.mem_subgroupOf.mp hc)
      have hyH : y ∈ H := by
        have hsub : xF ∈ M.subgroupOf J.F := Subgroup.mem_subgroupOf.mpr hxM
        have hmem : J.iso xF ∈ H := Subgroup.mem_map_of_mem J.iso.toMonoidHom hsub
        rw [hxy] at hmem
        exact hmem
      exact hyH
    have hwH : J.iso ⟨z, hzF⟩ ∈ H :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzM)
    have hw3 : orderOf (J.iso ⟨z, hzF⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hz3]
    have hw : ¬ orderOf (J.iso ⟨z, hzF⟩) ∣ J.p ^ J.f + 1 := by
      rw [hw3, hJp, hJf]
      intro hd
      have h3dvd : 3 ∣ 3 ^ (2 * k + 1) := pow_dvd_pow 3 (by omega : 1 ≤ 2 * k + 1)
      have h1 : 3 ∣ 1 := (Nat.dvd_add_right h3dvd).mp hd
      norm_num at h1
    have hHtop : H = ⊤ :=
      psl2_eq_top_of_normalizer_le (p := J.p) (n := J.f) hp hq5 hq7 hq9
        (by norm_num) (by norm_num) (by rw [hJp]; norm_num) hrq hR hRH hwH hw
    intro x hx
    have hsub : (⟨x, hx⟩ : ↥J.F) ∈ M.subgroupOf J.F := by
      rw [Subgroup.mem_subgroupOf]
      have hmem : J.iso ⟨x, hx⟩ ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
      have : y = ⟨x, hx⟩ := J.iso.injective hyeq
      rwa [this] at hy
    exact Subgroup.mem_subgroupOf.mp hsub
  have hCM : centralizer ({v} : Set X) ≤ M := by
    have hce : centralizer ({v} : Set X) = zpowers v ⊔ J.F := by
      rw [← hJt]
      exact J.centralizer_eq
    rw [hce]
    exact sup_le (Subgroup.zpowers_le.mpr hvM) hFM
  have hcoatom : IsCoatom (centralizer ({v} : Set X)) := by
    obtain ⟨-, -, -, hcoat, -⟩ :=
      CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
        k hk X hree
    exact hcoat v hv
  rcases hcoatom.le_iff.mp hCM with h | h
  · exact h
  · exfalso
    have hvT : v ∈ T := by
      rw [← hCT]
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have htM : t ∈ M := hTM ht
      rw [h] at htM
      exact Subgroup.mem_centralizer_singleton_iff.mp htM
    have hv1 : v = 1 := eq_one_of_commute_of_card_eight hT8 hBT hB7 hBC hvT hvB
    rw [hv1, orderOf_one] at hv
    omega

theorem le_of_isSylowOf_two_of_ree
    {A : Type} [Group A] [Finite A] {L : Subgroup A}
    (hLn : L.Normal) (hCL : centralizer (L : Set A) = ⊥) {f : ℕ}
    (hmod : CFSG.Blueprint.LieModel ↥L .twistedG2 0 3 f) {T : Subgroup A}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : T ≤ L := by
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  obtain ⟨-, hout, -⟩ :=
    k_ReeSylowGeneration_holds ↥L (3 ^ (2 * k + 1)) k ⟨k, rfl, hmod⟩ rfl (by omega)
  intro t ht
  obtain ⟨n, hn⟩ := hT.isPGroup ⟨t, ht⟩
  have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hN : t ∈ normalizer (L : Set A) := by
    rw [normalizer_eq_top_iff.mpr hLn]
    exact mem_top t
  have h := CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_two
    hout.not_two_dvd_nat hN htn
  rwa [hCL, sup_bot_eq] at h

theorem uc2_10_7OddReeSeven_of_inner_outer
    (hI : UC2_10_7OddReeSevenInner)
    (hO : UC2_10_7OddReeSevenOuter) : UC2_10_7OddReeSeven := by
  intro A _ _ L hLn hLs hCL f hmod T B M hT hBT hB7 hsup hTM hBM hstar
  by_cases hBL : B ≤ L
  · left
    have hTL : T ≤ L := le_of_isSylowOf_two_of_ree hLn hCL hmod hT
    have hLtop : L = ⊤ := by
      rw [← hsup]
      exact le_antisymm (le_sup_left.trans le_sup_left) (sup_le (sup_le le_rfl hTL) hBL)
    have e : ↥L ≃* A := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
    have hAs : IsSimpleGroup A := (MulEquiv.isSimpleGroup_congr e).mp hLs
    rw [hI A hAs f (hmod.of_mulEquiv e) T B M hT hBT hB7 hTM hBM hstar]
    exact le_top
  · exact hO A L hLn hLs hCL f hmod T B M hT hBT hB7 hBL hsup hTM hBM hstar

theorem uc2_10_7OddReeSevenInner_of_phi6
    (h6 : UC2_10_7OddReeSevenInnerPhi6) :
    UC2_10_7OddReeSevenInner := by
  intro X _ _ hXs f hmod T B M hT hBT hB7 hTM hBM hstar
  by_cases h7 : 7 ∣ 3 ^ f + 1
  · exact reeSevenInner_eq_top_of_dvd_add_one hXs hmod h7 hT hBT hB7 hTM hBM hstar
  · exact h6 X hXs f hmod h7 T B M hT hBT hB7 hTM hBM hstar

theorem uc2_10_7OddReeSeven_of_phi6_outer
    (h6 : UC2_10_7OddReeSevenInnerPhi6)
    (hO : UC2_10_7OddReeSevenOuter) : UC2_10_7OddReeSeven :=
  uc2_10_7OddReeSeven_of_inner_outer (uc2_10_7OddReeSevenInner_of_phi6 h6) hO

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
