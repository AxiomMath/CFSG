module

public import CFSG.RankThree.PartTwo.Sec17.Item172Proof
public import CFSG.RankThree.PartTwo.Sec17.Item171ProofKFact
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def yb171 (A : Subgroup G) (b : G) : Subgroup G :=
  ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)), A⁆ ⊔
    oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

@[expose] noncomputable def yB171 (A B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), yb171 A b

end Defs

@[expose] noncomputable def Step171GenA10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) →
      Y₀ ≤ ⨆ (w : G) (_ : w ∈ Subgroup.normalizer (A : Set G)),
        (L ⊔ ⁅CFSG.Open.pCoreOf 2 Y₀, Subgroup.zpowers c⁆).map (MulAut.conj w).toMonoidHom

@[expose] noncomputable def Step171Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 →
      ¬ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ⁅CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤
        yb171 A b

@[expose] noncomputable def KFact171 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) →
      L ≤ delta A (lB A) L

@[expose] noncomputable def Step171Delta0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 →
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≠
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      deltaZero A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ yb171 A b

namespace Proof171

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_centralizer_singleton (w b : G) :
    (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer ({w * b * w⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    change w * y * w⁻¹ * (w * b * w⁻¹) = w * b * w⁻¹ * (w * y * w⁻¹)
    calc w * y * w⁻¹ * (w * b * w⁻¹) = w * (y * b) * w⁻¹ := by group
      _ = w * (b * y) * w⁻¹ := by rw [hy']
      _ = w * b * w⁻¹ * (w * y * w⁻¹) := by group
  · intro hx
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨w⁻¹ * x * w, ?_, ?_⟩
    · show w⁻¹ * x * w ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w⁻¹ * x * w * b = w⁻¹ * (x * (w * b * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * b * w⁻¹) * x) * w := by rw [hx']
        _ = b * (w⁻¹ * x * w) := by group
    · change w * (w⁻¹ * x * w) * w⁻¹ = x
      group

theorem map_conj_yb171_le {A : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (b : G) : (yb171 A b).map (MulAut.conj w).toMonoidHom ≤ yb171 A (w * b * w⁻¹) := by
  unfold yb171
  rw [Subgroup.map_sup, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer hw,
    map_pPrimeCoreOf 3 (MulAut.conj w), HeadProof.map_oPrimeResidualOf,
    HeadProof.map_conj_delta hw, map_conj_centralizer_singleton]

theorem map_conj_yB171_le {A B : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    (yB171 A B).map (MulAut.conj w).toMonoidHom ≤
      yB171 A (B.map (MulAut.conj w).toMonoidHom) := by
  unfold yB171
  simp only [Subgroup.map_iSup]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
  refine (map_conj_yb171_le hw b).trans ?_
  have hwb1 : w * b * w⁻¹ ≠ 1 := fun h1 => hb1 (by
    have hb : b = w⁻¹ * (w * b * w⁻¹) * w := by group
    rw [hb, h1]
    group)
  exact le_iSup_of_le (w * b * w⁻¹) (le_iSup_of_le ⟨b, hb, rfl⟩ (le_iSup_of_le hwb1 le_rfl))

theorem le_yB171_of_gen {A B Y X : Subgroup G} (hB : IsHyperplane A B)
    (hgen : Y ≤ ⨆ (w : G) (_ : w ∈ Subgroup.normalizer (A : Set G)),
      X.map (MulAut.conj w).toMonoidHom)
    (hX : ∀ B' : Subgroup G, IsHyperplane A B' → X ≤ yB171 A B') : Y ≤ yB171 A B := by
  refine hgen.trans (iSup_le fun w => iSup_le fun hw => ?_)
  set B' := B.map (MulAut.conj w⁻¹).toMonoidHom with hB'
  have hB'h : IsHyperplane A B' := hB.map_conj (inv_mem hw)
  calc X.map (MulAut.conj w).toMonoidHom
      ≤ (yB171 A B').map (MulAut.conj w).toMonoidHom := Subgroup.map_mono (hX B' hB'h)
    _ ≤ yB171 A (B'.map (MulAut.conj w).toMonoidHom) := map_conj_yB171_le hw
    _ = yB171 A B := by rw [hB', Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]

theorem deltaZero_le_of_eq {A : Subgroup G} {b : G} (hb : b ∈ A)
    (hK : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    deltaZero A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤
      ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)), A⁆ := by
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hO'N : O' ≤ Subgroup.normalizer (O : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))).trans
      (le_normalizer_pPrimeCoreOf 3 _)
  refine sSup_le fun Q hQ => ?_
  obtain ⟨⟨hQQ, hQA⟩, hQb⟩ := hQ
  have hQK : Q ≤ O ⊔ O' := hK ▸ le_delta hQQ hQb
  rw [hQA, Subgroup.commutator_le]
  intro x hx α hα
  have hx' : x ∈ ((O : Set G) * (O' : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O O' hO'N]
    exact hQK hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  have hzα : z * α = α * z :=
    (Subgroup.mem_centralizer_iff.mp (pPrimeCoreOf_le 3 _ hz) α hα).symm
  have hkey : ⁅y * z, α⁆ = ⁅y, α⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc y * z * α * (y * z)⁻¹ * α⁻¹ = y * (z * α) * z⁻¹ * y⁻¹ * α⁻¹ := by group
      _ = y * (α * z) * z⁻¹ * y⁻¹ * α⁻¹ := by rw [hzα]
      _ = y * α * y⁻¹ * α⁻¹ := by group
  rw [hkey]
  exact Subgroup.commutator_mem_commutator hy hα

variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem deltaZero_le_yb171 (h : Sec17Std G A c L Y₀) (hD0 : Step171Delta0) {b : G} (hb : b ∈ A)
    (hb1 : b ≠ 1) : deltaZero A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ yb171 A b := by
  by_cases hK : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  · exact (deltaZero_le_of_eq hb hK).trans le_sup_left
  · exact hD0 G A c L Y₀ h b hb hb1 hK

theorem le_yB171_L (h : Sec17Std G A c L Y₀) (h142 : Concl142 A (lB A)) (hD0 : Step171Delta0)
    (hLΔ : L ≤ delta A (lB A) L) {B : Subgroup G} (hB : IsHyperplane A B) : L ≤ yB171 A B := by
  refine (le_iSup_gen171 h.toSec13Data hLΔ hB).trans (iSup_le fun b => iSup_le fun hb =>
    iSup_le fun hb1 => ?_)
  exact ((gen171_le_deltaZero h.toSec13Data h142 b).trans
    (deltaZero_le_yb171 h hD0 (hB.1 hb) hb1)).trans
    (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))

theorem commutator_inf_le_of_le_M (h : Sec17Std G A c L Y₀) {b : G}
    (hbM : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ⁅CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤
      yb171 A b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVb : CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({b} : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    refine le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf
      (hbM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀))
      Subgroup.le_normalizer) ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_of_isPGroup_two
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀).to_le inf_le_left))
  exact le_sup_of_le_left (Subgroup.commutator_mono hVb
    (Subgroup.zpowers_le.mpr h.toSec13Data.mem_A))

theorem commutator_le_yB171 (h : Sec17Std G A c L Y₀) (hComm : Step171Comm) {B : Subgroup G}
    (hB : IsHyperplane A B) :
    ⁅CFSG.Open.pCoreOf 2 Y₀, Subgroup.zpowers c⁆ ≤ yB171 A B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have hcA : c ∈ A := hD.mem_A
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hA.2] at this
    omega
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from hD.commute (hB.1 x.2) (hB.1 y.2))⟩⟩,
      fun x hx => hA.1.2 x (hB.1 hx)⟩
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    h.le_normalizer_y0.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  refine (commutator_le_iSup_commutator hBe (by rw [hB9]; norm_num)
    (HeadProof.pow_three_of_std h hcA) (fun b hb => hD.commute (hB.1 hb) hcA) (hB.1.trans hAV)
    (hAV hcA) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)).trans ?_
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
  refine le_trans ?_ (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))
  by_cases hbM : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G)
  · exact commutator_inf_le_of_le_M h hbM
  · exact hComm G A c L Y₀ h b (hB.1 hb) hb1 hbM

theorem cover_of_omega (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) :
    Y₀ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  rcases h1514 Y₀ h.mem_y0Star hMeets with ⟨h1, -⟩ | ⟨-, -, hT3, -⟩ | ⟨-, -, -, -, hnot, -⟩
  · exact h1.le.trans (sup_le_sup_right inf_le_right _)
  · exfalso
    have h3 := hT3.1
    rw [hΩ, Set.ncard_singleton] at h3
    omega
  · exact absurd h.le_y0 (hnot Y₀ h.mem_y0Star)

theorem le_yc_of_cover (h : Sec17Std G A c L Y₀) (hcov : Y₀ ≤ L ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    Y₀ ≤ L ⊔ ⁅CFSG.Open.pCoreOf 2 Y₀, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hCL : CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    intro v hv
    obtain ⟨htypes, huniq⟩ := h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA
    have hLv := Sec6.map_conj_mem_thetaComponentsAt hv.2 hD.mem_thetaComponentsAt
    have h3Lv : 3 ∣ Nat.card (L.map (MulAut.conj v).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]
      exact three_dvd_card_of_types148 htypes
    exact mem_normalizer_of_map_conj_eq (huniq _ hLv h3Lv)
  exact le_sup_commutator_of_cover h.mem_y0Star.prop.1.2.1 hcov
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)
    (h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)) hD.le_centralizer
    (HeadProof.pow_three_of_std h hD.mem_A)
    ((h.le_normalizer_y0.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀))
      hD.mem_A) hCL

end Proof171

section Item171

variable {G : Type} [Group G] [Finite G]

open Proof171 in
theorem rank3II_17_1_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514 A (lB A) c L) (hMeets : Claim1715Meets) (h142 : Concl142 A (lB A))
    (hGen : Step171GenA10) (hK : KFact171) (hComm : Step171Comm) (hD0 : Step171Delta0) :
    Item171 A (lB A) := by
  intro Y₀' hY₀' B hB
  obtain rfl : Y₀' = Y₀ := h.eq_of_mem_y0Star hY₀'
  change Y₀' ≤ yB171 A B
  set X := L ⊔ ⁅CFSG.Open.pCoreOf 2 Y₀', Subgroup.zpowers c⁆ with hX
  have hcase : Y₀' ≤ (⨆ (w : G) (_ : w ∈ Subgroup.normalizer (A : Set G)),
      X.map (MulAut.conj w).toMonoidHom) ∧ L ≤ delta A (lB A) L := by
    rcases h.a10_or_omega with hA10 | hΩ
    · exact ⟨hGen G A c L Y₀' h hA10, hK G A c L Y₀' h hA10⟩
    · have hcov := cover_of_omega h h1514 (hMeets G A c L Y₀' h) hΩ
      refine ⟨(le_yc_of_cover h hcov).trans (le_iSup_of_le 1 (le_iSup_of_le (one_mem _) ?_)),
        le_delta_of_cover h.toSec13Data h142 h.mem_y0Star.prop.1 h.le_y0 hcov⟩
      rw [Late.map_conj_one]
  have hXB : ∀ B' : Subgroup G, IsHyperplane A B' → X ≤ yB171 A B' := fun B' hB' =>
    sup_le (le_yB171_L h h142 hD0 hcase.2 hB') (commutator_le_yB171 h hComm hB')
  exact le_yB171_of_gen hB hcase.1 hXB

theorem item171S17_of (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h142 : Concl142S14)
    (hGen : Step171GenA10) (hK : KFact171) (hComm : Step171Comm) (hD0 : Step171Delta0) :
    Item171S17 :=
  fun G _ _ A c L Y₀ h => rank3II_17_1_of h (h1514 G A c L Y₀ h) hMeets
    (h142 G A c L h.toSec14Std) hGen hK hComm hD0

end Item171

end CFSG.RankThree.PartTwo.Sec17
