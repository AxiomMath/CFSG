module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdField

public section

namespace CFSG.StandardType

namespace TableBUD

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] [Finite K] {d n p : ℕ}

theorem card_le_mul_card_eq {W : Subgroup (Fin d → Kˣ)} (hp : p.Prime)
    (hWp : ∀ σ ∈ W, ∀ k, σ k ^ p = 1) (i j : Fin d) {T : Subgroup (Fin d → Kˣ)}
    (hT : ∀ σ ∈ W, σ i = σ j → σ ∈ T) : Nat.card W ≤ p * Nat.card (T ⊓ W : Subgroup _) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set χ : W →* Kˣ := (Pi.evalMonoidHom (fun _ : Fin d => Kˣ) i).comp W.subtype *
    ((Pi.evalMonoidHom (fun _ : Fin d => Kˣ) j).comp W.subtype)⁻¹ with hχ
  have hker : Nat.card χ.ker ≤ Nat.card (T ⊓ W : Subgroup _) := by
    refine Nat.card_le_card_of_injective (fun σ => ⟨σ.1.1, hT σ.1.1 σ.1.2 ?_, σ.1.2⟩) ?_
    · have h1 : (σ.1 : Fin d → Kˣ) i * ((σ.1 : Fin d → Kˣ) j)⁻¹ = 1 := σ.2
      exact mul_inv_eq_one.mp h1
    · intro a b hab
      have h1 := congrArg (fun x : ↥(T ⊓ W) => (x : Fin d → Kˣ)) hab
      simp only at h1
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card χ.range ≤ p := by
    have hle : χ.range ≤ rootsOfUnity p K := by
      rintro _ ⟨σ, rfl⟩
      rw [mem_rootsOfUnity]
      change ((σ : Fin d → Kˣ) i * ((σ : Fin d → Kˣ) j)⁻¹) ^ p = 1
      rw [mul_pow, inv_pow, hWp σ.1 σ.2 i, hWp σ.1 σ.2 j, inv_one, mul_one]
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity K p)
  calc Nat.card W = Nat.card χ.ker * Nat.card χ.range := (Subgroup.card_ker_mul_card_range χ).symm
    _ ≤ Nat.card (T ⊓ W : Subgroup _) * p := Nat.mul_le_mul hker hrange
    _ = p * Nat.card (T ⊓ W : Subgroup _) := mul_comm _ _

theorem ggBstarBoundInnR_unitary_dvd (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd5 : 5 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    GGBstarBoundInnR p (d - 3) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  intro Eb Eh hEbI hEb hr h3 hV hle hEh hcard
  set h := TableBU.unitaryFieldData_of_card hK hn with hh
  have hd : 3 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have : CharP K 2 := h.charP
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hEbD : Eb ≤ inndiagU h hd1 := fun e he => congr_mem_primeFormD h hd1 hK (hEbI he)
  set E₀ := Eh ⊓ inndiagU h hd1 with hE₀
  have hE₀ab : IsElemAbelian p E₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hEh a.2.1 b.2.1)⟩⟩,
      fun a ha => hEh.2 a ha.1⟩
  have hEhE₀ := card_le_mul_card_inf_inndiagU h hd hq hp hEh
  have hEbE₀ : Eb ≤ E₀ := le_inf hle hEbD
  have hEb1 : 0 < Nat.card Eb := Nat.card_pos
  have hE₀ge : p * Nat.card Eb ≤ Nat.card E₀ := by
    have h1 : p * (p * Nat.card Eb) ≤ p * Nat.card E₀ := by
      calc p * (p * Nat.card Eb) = p ^ 2 * Nat.card Eb := by ring
        _ ≤ Nat.card Eh := hcard
        _ ≤ p * Nat.card E₀ := hEhE₀
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hE₀ge' : p ^ (d - 2) ≤ Nat.card E₀ := by
    have e1 : p ^ (d - 2) = p * p ^ (d - 3) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e1]
    exact (Nat.mul_le_mul_left _ hr).trans hE₀ge
  have hbig : p ^ (d / p + 1) < Nat.card E₀ := by
    have h1 : d / p ≤ d / 3 := Nat.div_le_div_left hp3 (by norm_num)
    have h2 : d / p + 1 < d - 2 := by omega
    exact (Nat.pow_lt_pow_right hp.one_lt h2).trans_le hE₀ge'
  obtain ⟨Q, hQ, hfr⟩ := exists_frame_inndiag hK hd hdq hq hp hpq hE₀ab inf_le_right hbig
  set Wh := frameWeights h Q hQ hd1 p E₀ with hWh
  set Wb := frameWeights h Q hQ hd1 p Eb with hWb
  have hWhc : Nat.card Wh = Nat.card E₀ := card_frameWeights hK hd hdq hp hpq hfr
  have hWbc : Nat.card Wb = Nat.card Eb :=
    card_frameWeights hK hd hdq hp hpq fun e he => hfr e (hEbE₀ he)
  have hWbWh : Wb ≤ Wh := fun σ ⟨h0, hp', hn', e, he, hfrσ⟩ => ⟨h0, hp', hn', e, hEbE₀ he, hfrσ⟩
  obtain ⟨V, hV1, hV2, hEbV⟩ := hV
  have hcinj := mulAut_conj_injective (TableBUE.center_proj_eq_bot hK hd hdq)
  set φ₀ := (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut _).comp
    (frameMk h Q hQ) with hφ₀
  have hkerφ₀ : φ₀.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
    intro u hu
    apply ker_frameMk_le_center h Q hQ
    exact hcinj (by rw [map_one]; exact hu)
  set V' := V.map (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut _)
    with hV'
  have hV'1 : V' ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hcinj]
    exact hV1
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hV'φ : V' ≤ φ₀.range := by
    rintro _ ⟨v, -, rfl⟩
    obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ v
    exact ⟨u, rfl⟩
  have hconjE : ∀ (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
      (v : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))),
      α * MulAut.conj v * α⁻¹ = MulAut.conj (α v) := by
    intro α v
    ext y
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  have hBV : Eb ≤ Subgroup.normalizer (V' : Set (MulAut _)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hconjE]
      exact ⟨e v, hEbV e he v hv, rfl⟩
    · rintro ⟨v, hv, hve⟩
      have hy : y = MulAut.conj (e⁻¹ v) := by
        rw [← hconjE, hve]
        group
      rw [hy]
      exact ⟨e⁻¹ v, hEbV _ (Eb.inv_mem he) v hv, rfl⟩
  obtain ⟨i, j, hij, hpair⟩ :=
    SURepair.exists_framePair_of_twoSubgroup h hkerφ₀ hV'1 hV'2 hV'φ hBV
  have hacts : ∀ (e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) σ,
      FrameAct h Q hQ e σ → (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) →
        SURep.GGFrameActs φ₀ e σ := by
    intro e σ hfrσ hσn
    refine ⟨hσn, fun s s' hss' => ?_⟩
    change e * MulAut.conj (frameMk h Q hQ s) * e⁻¹ = MulAut.conj (frameMk h Q hQ s')
    rw [hconjE, hfrσ.apply s s' hss']
  have hWbij : ∀ σ ∈ Wb, σ i = σ j := by
    rintro σ ⟨-, -, hσn, e, he, hfrσ⟩
    exact hpair e he σ (hacts e σ hfrσ hσn)
  have hEbact : ∀ e ∈ Eb, ∃ σ : Fin d → Kˣ, σ i = σ j ∧ FrameAct h Q hQ e σ := by
    intro e he
    obtain ⟨σ, h0, hσp, hσn, hfrσ⟩ := hfr e (hEbE₀ he)
    exact ⟨σ, hWbij σ ⟨h0, hσp, hσn, e, he, hfrσ⟩, hfrσ⟩
  have hc1 : (1 : Kˣ) ^ (2 ^ n + 1) = 1 := one_pow _
  set m := frameMk h Q hQ ⟨TableBUM.monoSwap i j 1, TableBUM.monoSwap_mem h hij hc1⟩ with hm
  have hfixm : ∀ (e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) σ,
      FrameAct h Q hQ e σ → σ i = σ j → e m = m := by
    intro e σ hfrσ hσij
    refine hfrσ.apply _ _ ?_
    change TableBUM.monoSwap i j 1 = diagHom d σ * TableBUM.monoSwap i j 1 * (diagHom d σ)⁻¹
    rw [TableBUM.commute_monoSwap hσij, mul_inv_cancel_right]
  have hEbF : Eb ≤ fixerSub m := fun e he => by
    obtain ⟨σ, hσij, hfrσ⟩ := hEbact e he
    exact hfixm e σ hfrσ hσij
  by_cases hI : ∃ σ ∈ Wh, σ i = σ j ∧ σ ∉ Wb
  ·
    obtain ⟨σ, ⟨h0, hσp, hσn, e, he, hfrσ⟩, hσij, hσWb⟩ := hI
    have heb : e ∉ Eb := fun heb => hσWb ⟨h0, hσp, hσn, e, heb, hfrσ⟩
    have hE'F : Eb ⊔ Subgroup.zpowers e ≤ fixerSub m :=
      sup_le hEbF ((Subgroup.zpowers_le).mpr (hfixm e σ hfrσ hσij))
    obtain ⟨V₁, hV₁1, hV₁2, hV₁⟩ := exists_two_subgroup_of_fix
      (frameMk_monoSwap_ne_one (h := h) (Q := Q) (hQ := hQ) hij hc1)
      (frameMk_monoSwap_sq (h := h) (Q := Q) (hQ := hQ) hij hc1) fun α hα => hE'F hα
    refine ⟨Eb ⊔ Subgroup.zpowers e, lt_of_le_of_ne le_sup_left fun hEq => ?_,
      sup_le hle ((Subgroup.zpowers_le).mpr he.1), V₁, hV₁1, hV₁2, hV₁⟩
    have h1 : e ∈ Eb ⊔ Subgroup.zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    rw [← hEq] at h1
    exact heb h1
  push Not at hI
  have hWh_le : Nat.card Wh ≤ p * Nat.card Wb := by
    have h1 := card_le_mul_card_eq hp (W := Wh) (fun σ hσ => hσ.2.1) i j (T := Wb) hI
    rwa [inf_eq_left.mpr hWbWh] at h1
  have hE₀le : Nat.card E₀ ≤ p * Nat.card Eb := by
    rw [← hWhc, ← hWbc]
    exact hWh_le
  obtain ⟨f, hfEh, hfD⟩ : ∃ f ∈ Eh, f ∉ inndiagU h hd1 := by
    by_contra hcon
    push Not at hcon
    have hEE : E₀ = Eh := inf_eq_left.mpr fun e he => hcon e he
    have h1 : p ^ 2 * Nat.card Eb ≤ p * Nat.card Eb := by
      rw [← hEE] at hcard
      exact hcard.trans hE₀le
    have h2 : p * Nat.card Eb < p ^ 2 * Nat.card Eb := by
      rw [sq, mul_assoc]
      exact lt_mul_of_one_lt_left (Nat.mul_pos hp.pos hEb1) hp.one_lt
    omega
  by_cases hII : ∃ k l : Fin d, k ≠ l ∧ ∀ σ ∈ Wh, σ k = σ l
  ·
    obtain ⟨k, l, hkl, hWkl⟩ := hII
    refine ⟨E₀, lt_of_le_of_ne hEbE₀ fun hEq => ?_, inf_le_left,
      exists_two_subgroup_of_pair (h := h) (Q := Q) (hQ := hQ) hkl fun e he => ?_⟩
    · have h1 : Nat.card Eb = Nat.card E₀ := by rw [hEq]
      have h2 : Nat.card Eb < p * Nat.card Eb := lt_mul_of_one_lt_left hEb1 hp.one_lt
      omega
    · obtain ⟨σ, h0, hσp, hσn, hfrσ⟩ := hfr e he
      exact ⟨σ, hWkl σ ⟨h0, hσp, hσn, e, he, hfrσ⟩, hfrσ⟩
  push Not at hII
  have hfp : f ^ p = 1 := hEh.2 f hfEh
  obtain ⟨B, hB, hsl⟩ := exists_isSemilin h hd hq f
  set φ := fieldFactorU h hd hq f with hφ
  have hφp : φ ^ p = 1 := by rw [hφ, ← map_pow, hfp, map_one]
  have hsl' := hsl.frame h Q hQ
  set B' := Q⁻¹ * B * glAut φ Q with hB'
  have hB'u : B' ∈ primeFormUnitary h (idGram K d) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hQ) hB)
      (glAut_mem_primeFormUnitary h (isPrimeFormGram_one (K := K) (n := d)) φ hQ)
  have hconj : ∀ σ ∈ Wh, ∃ c : Kˣ,
      B' * diagHom d σ = Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ * B' := by
    rintro σ ⟨-, hσp, hσn, e, he, hfrσ⟩
    exact exists_conj_eq_smul_of_commute h hK hd hdq hp hpq hQ hB'u hφp hsl' hσp hσn hfrσ
      (TableB.IsElemAbelian.comm hEh hfEh he.1)
  have hWhge : p ^ (d - 2) ≤ Nat.card Wh := by
    rw [hWhc]
    exact hE₀ge'
  have hcomm := TableBUM.commute_of_conj_eq_smul hp hp2 (by omega) (W := Wh)
    (fun σ hσ => hσ.1) (fun σ hσ => hσ.2.1) hII hWhge hconj
  obtain ⟨β, hβ⟩ := TableBUM.exists_diagHom_of_commute (W := (Wh : Set (Fin d → Kˣ))) hII hcomm
  exact exists_bstar_of_field h hK hn hd hdq hq hp hpq hQ hle hEbD hij hEbact hfEh hfD hfp
    (hβ ▸ hB'u) (hβ ▸ hsl')

theorem ggBstarBoundInn_unitary_dvd (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd5 : 5 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) :
    GGBstarBoundInn p (ggUnitaryTorusRank p d) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  exact ggBstarBoundInn_of_R hp (TableBUE.center_proj_eq_bot hK (by omega) hdq)
    (ggBstarBoundInnR_unitary_dvd hK hn hd5 hp hpq)

end TableBUD

end CFSG.StandardType
