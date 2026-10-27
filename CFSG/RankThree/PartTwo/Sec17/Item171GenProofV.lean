module

public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Gen

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_closure_le {V N : Subgroup G} {S : Set G}
    (hS : ∀ s ∈ S, ∀ v ∈ V, ⁅v, s⁆ ∈ N)
    (hN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G)) :
    ⁅V, Subgroup.closure S⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro v hv b hb
  induction hb using Subgroup.closure_induction with
  | mem s hs => exact hS s hs v hv
  | one =>
    rw [commutatorElement_one_right]
    exact one_mem N
  | mul b₁ b₂ hb₁ _ ih₁ ih₂ =>
    have h : ⁅v, b₁ * b₂⁆ = ⁅v, b₁⁆ * (b₁ * ⁅v, b₂⁆ * b₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact mul_mem ih₁ ((Subgroup.mem_normalizer_iff.mp (hN hb₁) _).mp ih₂)
  | inv b hb ih =>
    have h : ⁅v, b⁻¹⁆ = b⁻¹ * ⁅v, b⁆⁻¹ * b⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem (hN hb)) _).mp (inv_mem ih)

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem centralizer_le_normalizer_L (h : Sec17Std G A c L Y₀) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro v hv
  have hD := h.toSec13Data
  obtain ⟨htypes, huniq⟩ := h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA
  have hLv := Sec6.map_conj_mem_thetaComponentsAt hv hD.mem_thetaComponentsAt
  have h3Lv : 3 ∣ Nat.card (L.map (MulAut.conj v).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]
    exact three_dvd_card_of_types148 htypes
  exact Proof171Steps.mem_normalizer_of_map_conj_eq'' (huniq _ hLv h3Lv)

theorem le_iSup_of_le_sup_pCoreOf (h : Sec17Std G A c L Y₀)
    (hcov : Y₀ ≤ (⨆ (w : G) (_ : w ∈ Subgroup.normalizer (A : Set G)),
        L.map (MulAut.conj w).toMonoidHom) ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    Y₀ ≤ ⨆ (w : G) (_ : w ∈ Subgroup.normalizer (A : Set G)),
        (L ⊔ ⁅CFSG.Open.pCoreOf 2 Y₀, Subgroup.zpowers c⁆).map (MulAut.conj w).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set W := Subgroup.normalizer (A : Set G) with hW
  set V := CFSG.Open.pCoreOf 2 Y₀ with hV
  set K := L ⊔ ⁅V, Subgroup.zpowers c⁆ with hK
  set X := ⨆ (w : G) (_ : w ∈ W), K.map (MulAut.conj w).toMonoidHom with hX
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hWV : W ≤ Subgroup.normalizer (V : Set G) :=
    h.normalizer_le.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hAW : A ≤ W := Subgroup.le_normalizer
  have hKX : ∀ w ∈ W, K.map (MulAut.conj w).toMonoidHom ≤ X := fun w hw =>
    le_iSup_of_le w (le_iSup_of_le hw le_rfl)
  have hWX : W ≤ Subgroup.normalizer (X : Set G) := by
    intro a ha
    have hle : X.map (MulAut.conj a).toMonoidHom ≤ X := by
      rw [hX, Subgroup.map_iSup]
      refine iSup_le fun w => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hw => ?_
      rw [Late.map_conj_map_conj]
      exact hKX _ (mul_mem ha hw)
    exact Subgroup.mem_normalizer_fintype fun n hn => hle ⟨n, hn, rfl⟩
  set S : Set G := {g | ∃ w ∈ W, g = w * c * w⁻¹} with hS
  set B := Subgroup.closure S with hB
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hw c).mp hD.mem_A
  have hB3 : IsPGroup 3 B := (HeadProof.isE27_of_std h).isPGroup.to_le hBA
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := hBA.trans (hAW.trans hWV)
  have hV3 : ¬ 3 ∣ Nat.card V := Proof171.not_three_dvd_of_isPGroup_two hV2
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three B V hB3 hV3 hBV
  have hVBX : ⁅V, B⁆ ≤ X := by
    refine commutator_closure_le ?_ (hBA.trans (hAW.trans hWX))
    rintro _ ⟨w, hw, rfl⟩ v hv
    refine hKX w hw (Subgroup.map_mono (le_sup_right : ⁅V, Subgroup.zpowers c⁆ ≤ K) ?_)
    have hmap : ⁅V, Subgroup.zpowers c⁆.map (MulAut.conj w).toMonoidHom =
        ⁅V, Subgroup.zpowers (w * c * w⁻¹)⁆ := by
      rw [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hWV hw),
        MonoidHom.map_zpowers]
      rfl
    rw [hmap]
    exact Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers _)
  set C := V ⊓ Subgroup.centralizer (B : Set G) with hC
  have hCL := centralizer_le_normalizer_L h
  have hCX : C ≤ Subgroup.normalizer (X : Set G) := by
    intro u hu
    have hle : X.map (MulAut.conj u).toMonoidHom ≤ X := by
      rw [hX, Subgroup.map_iSup]
      refine iSup_le fun w => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hw => ?_
      set u' := w⁻¹ * u * w with hu'
      have hu'V : u' ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hWV hw)) u).mp hu.1
        simpa [hu', mul_assoc] using this
      have hu'c : u' ∈ Subgroup.centralizer ({c} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : (w * c * w⁻¹) * u = u * (w * c * w⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hu.2 _ (Subgroup.subset_closure ⟨w, hw, rfl⟩)
        calc u' * c = w⁻¹ * (u * (w * c * w⁻¹)) * w := by rw [hu']; group
          _ = w⁻¹ * ((w * c * w⁻¹) * u) * w := by rw [hcomm]
          _ = c * u' := by rw [hu']; group
      have hu'K : u' ∈ Subgroup.normalizer (K : Set G) := by
        refine Proof171Steps.mem_normalizer_of_map_conj_eq'' ?_
        rw [hK, Subgroup.map_sup, Late.map_conj_eq_of_mem_normalizer (hCL hu'c),
          Late.map_conj_eq_of_mem_normalizer
            (Subgroup.normalizer_commutator_ge_left V (Subgroup.zpowers c) hu'V)]
      calc (K.map (MulAut.conj w).toMonoidHom).map (MulAut.conj u).toMonoidHom
          = K.map (MulAut.conj (u * w)).toMonoidHom := Late.map_conj_map_conj K u w
        _ = K.map (MulAut.conj (w * u')).toMonoidHom := by rw [hu']; congr 2; group
        _ = (K.map (MulAut.conj u').toMonoidHom).map (MulAut.conj w).toMonoidHom :=
          (Late.map_conj_map_conj K w u').symm
        _ = K.map (MulAut.conj w).toMonoidHom := by
          rw [Late.map_conj_eq_of_mem_normalizer hu'K]
        _ ≤ X := hKX w hw
    exact Subgroup.mem_normalizer_fintype fun n hn => hle ⟨n, hn, rfl⟩
  have hX0 : (⨆ (w : G) (_ : w ∈ W), L.map (MulAut.conj w).toMonoidHom) ≤ X :=
    iSup_le fun w => iSup_le fun hw => (Subgroup.map_mono le_sup_left).trans (hKX w hw)
  have hVXC : V ≤ X ⊔ C := hfac.le.trans (sup_le_sup hVBX le_rfl)
  have hYXC : Y₀ ≤ X ⊔ C := hcov.trans (sup_le (hX0.trans le_sup_left) hVXC)
  have hY3 : Y₀ = oPrimeResidualOf 3 Y₀ := h.mem_y0Star.prop.1.2.1
  refine hY3.le.trans ?_
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hyY, k, hk⟩
  have hy : y ∈ ((X ⊔ C : Subgroup G) : Set G) := hYXC hyY
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X C hCX] at hy
  obtain ⟨x, hx, u, hu, rfl⟩ := hy
  obtain ⟨m, hm⟩ := hV2 ⟨u, hu.1⟩
  have hm' : u ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  exact mul_mem hx (Proof171.mem_of_mul_pow_eq_one hx (hCX hu)
    (Nat.Coprime.pow k m (by norm_num)) hk hm')

end CFSG.RankThree.PartTwo.Sec17.Proof171Gen
