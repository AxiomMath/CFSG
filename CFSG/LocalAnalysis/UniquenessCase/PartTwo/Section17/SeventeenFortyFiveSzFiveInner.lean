module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35Frame
import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Linear
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Unitary
import CFSG.Quasithin.H13.U3S1348J
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open scoped Pointwise

private theorem exists_frame_dim {n : ℕ} (hn : 4 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ (n = 2 * m + 1 + 1 ∨ n = 2 * m + 1 + 1 + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k - 1, by omega, Or.inl (by omega)⟩
  · exact ⟨k - 1, by omega, Or.inr (by omega)⟩

private theorem not_five_dvd_of_mod_five {q : ℕ} (hq5 : q % 5 = 2 ∨ q % 5 = 3) :
    ¬ 5 ∣ q * (q ^ 2 - 1) := by
  have hsq : q ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hq5 with h | h <;> rw [h]
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h with h1 | h1 <;>
    generalize q ^ 2 = Q at * <;> omega

private theorem exists_elemAbelian_sq_statedProj_statedSL_of_dvd_add_one
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hK : Nat.card K = p ^ f) (hq : 5 ∣ p ^ f + 1) {n : ℕ} (hn5 : 5 ≤ n) :
    ∃ E : Subgroup (StatedProj (StatedSL n K)), IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5SL2 : 5 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK]
    have hfac : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      simpa using sq_tsub_sq (p ^ f) 1
    exact dvd_mul_of_dvd_right (hq.trans ⟨p ^ f - 1, hfac⟩) (p ^ f)
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) K) 5 h5SL2
  let A : Matrix.SpecialLinearGroup (Fin 4) K :=
    CFSG.SeitzReduction.LinearPilot.pairEmbed (K := K) (n := 4) (a := 0) (b := 1) (by decide) x
  let B : Matrix.SpecialLinearGroup (Fin 4) K :=
    CFSG.SeitzReduction.LinearPilot.pairEmbed (K := K) (n := 4) (a := 2) (b := 3) (by decide) x
  have hAord : orderOf A = 5 :=
    (orderOf_injective _ (CFSG.SeitzReduction.LinearPilot.pairEmbed_injective (by decide)) x).trans
      hx
  have hBord : orderOf B = 5 :=
    (orderOf_injective _ (CFSG.SeitzReduction.LinearPilot.pairEmbed_injective (by decide)) x).trans
      hx
  have hA5 : A ^ 5 = 1 := by rw [← hAord]; exact pow_orderOf_eq_one A
  have hB5 : B ^ 5 = 1 := by rw [← hBord]; exact pow_orderOf_eq_one B
  have hAmem : A ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K)
      ({0, 1} : Finset (Fin 4)) := by
    rw [← CFSG.SeitzReduction.LinearPilot.range_pairEmbed (K := K) (n := 4)
      (a := 0) (b := 1) (by decide)]
    exact ⟨x, rfl⟩
  have hBmem : B ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K)
      ({2, 3} : Finset (Fin 4)) := by
    rw [← CFSG.SeitzReduction.LinearPilot.range_pairEmbed (K := K) (n := 4)
      (a := 2) (b := 3) (by decide)]
    exact ⟨x, rfl⟩
  have hcomm : A * B = B * A :=
    CFSG.SeitzReduction.LinearPilot.commute_blockSpecialLinear_of_disjoint
      (K := K) (n := 4) (by decide) hAmem hBmem
  have hBnot : B ∉ Subgroup.zpowers A := by
    intro hmem
    have hzle : Subgroup.zpowers A ≤ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        (K := K) ({0, 1} : Finset (Fin 4)) := Subgroup.zpowers_le.mpr hAmem
    have hbot : B ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) K)) := by
      rw [← CFSG.SeitzReduction.F4Pilot.blockSpecialLinear_inf_eq_bot_of_disjoint
        (F := K) (n := 4) (by decide : Disjoint ({0, 1} : Finset (Fin 4)) {2, 3})]
      exact ⟨hzle hmem, hBmem⟩
    rw [Subgroup.mem_bot] at hbot
    have := hBord
    rw [hbot, orderOf_one] at this
    omega
  obtain ⟨hEel, hEcard⟩ := CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers
    (p := 5) (A := Subgroup.zpowers A) (CFSG.Open.isElemAbelian_zpowers hA5) hBnot hB5
    (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left hcomm k).eq)
  let I : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb (by omega : 4 ≤ n))
  have hIcard : I.card = 4 := by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hIlt : I.card < n := by omega
  let eI : I ≃ Fin 4 := I.equivFin.trans (finCongr hIcard)
  let ψ : Matrix.SpecialLinearGroup (Fin 4) K →* StatedProj (StatedSL n K) :=
    ((CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n K).toMonoidHom).comp
      (((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K).comp
        (CFSG.SeitzReduction.LinearPilot.blockEmbed I)).comp
          (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear eI).symm.toMonoidHom)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have hab' : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K)
        (CFSG.SeitzReduction.LinearPilot.blockEmbed I
          ((CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear eI).symm a)) =
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K)
          (CFSG.SeitzReduction.LinearPilot.blockEmbed I
            ((CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear eI).symm b)) :=
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n K).injective hab
    have h2 := CFSG.SeitzReduction.LinearPilot.proj_comp_blockEmbed_injective
      (K := K) (n := n) (I := I) hIlt hab'
    exact (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear eI).symm.injective h2
  refine ⟨(Subgroup.zpowers A ⊔ Subgroup.zpowers B).map ψ, hEel.map ψ, ?_⟩
  rw [Subgroup.card_map_of_injective hψ, hEcard, Nat.card_zpowers, hAord]
  norm_num

private theorem exists_elemAbelian_sq_statedProj_statedSU_of_dvd_sub_one
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card K = (p ^ f) ^ 2) (hq : 5 ∣ p ^ f - 1) {n : ℕ} (hn5 : 5 ≤ n) :
    ∃ E : Subgroup (StatedProj (StatedSU n (p ^ f) K)), IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = p ^ (2 * f) := by
    rw [hF, ← pow_mul, Nat.mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK'
  have hSU2card : Nat.card (CFSG.ClassicalInvolution.Phan.Su K p f 2) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    obtain ⟨Pw, hPw⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF 2
    rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv Pw hPw).toEquiv]
    exact CFSG.LieType.Steinberg.card_SU_two hF
  have hfac : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    simpa using sq_tsub_sq (p ^ f) 1
  have h5SU2 : 5 ∣ Nat.card (CFSG.ClassicalInvolution.Phan.Su K p f 2) := by
    rw [hSU2card]
    exact dvd_mul_of_dvd_right (hq.trans ⟨p ^ f + 1, by rw [hfac]; ring⟩) (p ^ f)
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := CFSG.ClassicalInvolution.Phan.Su K p f 2) 5 h5SU2
  let A : CFSG.ClassicalInvolution.Phan.Su K p f 4 :=
    CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 3 0 x
  let B : CFSG.ClassicalInvolution.Phan.Su K p f 4 :=
    CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 3 2 x
  have hAord : orderOf A = 5 :=
    (orderOf_injective _ (CFSG.ClassicalInvolution.Phan.blockEmb_injective (by omega)) x).trans hx
  have hBord : orderOf B = 5 :=
    (orderOf_injective _ (CFSG.ClassicalInvolution.Phan.blockEmb_injective (by omega)) x).trans hx
  have hA5 : A ^ 5 = 1 := by rw [← hAord]; exact pow_orderOf_eq_one A
  have hB5 : B ^ 5 = 1 := by rw [← hBord]; exact pow_orderOf_eq_one B
  have hcomm : A * B = B * A :=
    CFSG.ClassicalInvolution.Phan.blockEmb2_comm (K := K) (p := p) (f := f) (n := 3)
      (i := 0) (j := 2) (by norm_num) x x
  have hBnot : B ∉ Subgroup.zpowers A := by
    intro hmem
    have hzle : Subgroup.zpowers A ≤
        (CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 3 0).range :=
      Subgroup.zpowers_le.mpr ⟨x, rfl⟩
    have hBmem : B ∈ (CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 3 2).range := ⟨x, rfl⟩
    have hbot : B ∈ (⊥ : Subgroup (CFSG.ClassicalInvolution.Phan.Su K p f 4)) := by
      rw [← CFSG.ClassicalInvolution.Phan.range_blockEmb2_inf_far
        (K := K) (p := p) (f := f) (n := 3) (a := 0) (b := 2) (by norm_num)]
      exact ⟨hzle hmem, hBmem⟩
    rw [Subgroup.mem_bot] at hbot
    have := hBord
    rw [hbot, orderOf_one] at this
    omega
  obtain ⟨hEel, hEcard⟩ := CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers
    (p := 5) (A := Subgroup.zpowers A) (CFSG.Open.isElemAbelian_zpowers hA5) hBnot hB5
    (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left hcomm k).eq)
  let σ : CFSG.ClassicalInvolution.Phan.Su K p f n ≃* StatedSU n (p ^ f) K :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
  let θ : CFSG.ClassicalInvolution.Phan.Su K p f n →* StatedProj (StatedSU n (p ^ f) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).comp
      σ.toMonoidHom
  have hθ : θ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f n) := by
    rw [CFSG.ClassicalInvolution.Phan.center_SUid_eq
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF) (by omega)]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [Subgroup.mem_subgroupOf]
    have h1 : (σ z : StatedSU n (p ^ f) K) ∈
        (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) :=
      (QuotientGroup.eq_one_iff (σ z)).1 hz
    rw [Subgroup.mem_subgroupOf] at h1
    simpa [σ] using h1
  let ψ : CFSG.ClassicalInvolution.Phan.Su K p f 4 →* StatedProj (StatedSU n (p ^ f) K) :=
    θ.comp (CFSG.ClassicalInvolution.Phan.blockEmb K p f n 4 0 (by omega))
  have hψ : Function.Injective ψ :=
    CFSG.ClassicalInvolution.Phan.comp_blockEmb_injective (K := K) (p := p) (f := f)
      (m := n) (k := 4) (i := 0) hF hθ (by omega) (by omega) (by omega)
  refine ⟨(Subgroup.zpowers A ⊔ Subgroup.zpowers B).map ψ, hEel.map ψ, ?_⟩
  rw [Subgroup.card_map_of_injective hψ, hEcard, Nat.card_zpowers, hAord]
  norm_num

open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
  (exists_isElemAbelian_cube_of_statedClassicalModel_PSU) in
theorem pmod_five_of_pRank_five_le_one
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hn5 : 5 ≤ n) (hp : p.Prime) (hp5 : p ≠ 5)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (h5rank : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 1) :
    p ^ f % 5 = 2 ∨ p ^ f % 5 = 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hf : 1 ≤ f := hadm.2.1
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hM : StatedClassicalModel X t n p f :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hX
  have hq0 : p ^ f % 5 ≠ 0 := by
    intro h
    have hdvd : 5 ∣ p ^ f := Nat.dvd_of_mod_eq_zero h
    have h5p : 5 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h5p).symm
  have hlt : p ^ f % 5 < 5 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : p ^ f % 5 = 1
  · rcases ht with rfl | rfl
    ·
      obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := hM
      have h5K : 5 ∣ Nat.card K - 1 := by rw [hK]; omega
      obtain ⟨E, hE, hEcard⟩ :=
        CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.exists_elemAbelian_diagThree_psl
          (K := K) (n := n) (p := 5) Nat.prime_five (by omega) h5K
      let φ : Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* X :=
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).trans e.symm
      have hE' : IsElemAbelian 5 (E.map φ.toMonoidHom) := hE.map φ.toMonoidHom
      have hcard : Nat.card (E.map φ.toMonoidHom) = 5 ^ 3 := by
        rw [Subgroup.card_map_of_injective φ.injective, hEcard]
      have := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_ge_of_elemAbelian_card
        (p := 5) (k := 3) (by norm_num) (H := ⊤) (E := E.map φ.toMonoidHom) le_top hE' hcard
      omega
    ·
      obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := hM
      have h5q : 5 ∣ p ^ f - 1 := by omega
      obtain ⟨E, hE, hEcard⟩ :=
        exists_elemAbelian_sq_statedProj_statedSU_of_dvd_sub_one (K := K) hp hf hK h5q (n := n) hn5
      have hE' : IsElemAbelian 5 (E.map e.symm.toMonoidHom) := hE.map e.symm.toMonoidHom
      have hcard : Nat.card (E.map e.symm.toMonoidHom) = 5 ^ 2 := by
        rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]
      have := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_ge_of_elemAbelian_card
        (p := 5) (k := 2) (by norm_num) (H := ⊤) (E := E.map e.symm.toMonoidHom) le_top hE' hcard
      omega
  · by_cases h4 : p ^ f % 5 = 4
    · rcases ht with rfl | rfl
      ·
        obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := hM
        have h5q : 5 ∣ p ^ f + 1 := by omega
        obtain ⟨E, hE, hEcard⟩ :=
          exists_elemAbelian_sq_statedProj_statedSL_of_dvd_add_one (K := K) hK h5q (n := n) hn5
        have hE' : IsElemAbelian 5 (E.map e.symm.toMonoidHom) := hE.map e.symm.toMonoidHom
        have hcard : Nat.card (E.map e.symm.toMonoidHom) = 5 ^ 2 := by
          rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]
        have := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_ge_of_elemAbelian_card
          (p := 5) (k := 2) (by norm_num) (H := ⊤) (E := E.map e.symm.toMonoidHom) le_top hE'
          hcard
        omega
      ·
        have hpq : 5 ∣ p ^ f + 1 := by omega
        have hq2 : p ^ f ≠ 2 := by omega
        obtain ⟨E, hE, hEcard⟩ :=
          exists_isElemAbelian_cube_of_statedClassicalModel_PSU
            hM Nat.prime_five (by norm_num) (by omega) hpq (Or.inl hq2)
        have := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_ge_of_elemAbelian_card
          (p := 5) (k := 3) (by norm_num) (H := ⊤) (E := E) le_top hE hEcard
        omega
    · omega

theorem centralizes_fundamental_of_card_five
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X]
    (t : StatedLieTag) (n p f : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2)
    (hp5 : p ≠ 5) (h5rank : pRank 5 (⊤ : Subgroup X) ≤ 3)
    (P : Sylow 2 X) (B : Subgroup X) (hBcard : Nat.card B = 5)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (K : Subgroup X) (hK : K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h5K : ¬ 5 ∣ Nat.card K) :
    B ≤ centralizer (K : Set X) := by
  have h5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨h5⟩
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hBcard
    omega
  have : IsCyclic B := isCyclic_of_prime_card hBcard
  have hBodd : Odd (Nat.card B) := by
    rw [hBcard]
    decide
  have hB3 : ¬ 3 ∣ Nat.card B := by
    rw [hBcard]
    decide
  have hBp : ¬ p ∣ Nat.card B := by
    rw [hBcard]
    exact fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp h5).mp h)
  have hrank : ∀ s : ℕ, s.Prime → s ∣ Nat.card B →
      pRank s B ≤ 2 ∧ pRank s (⊤ : Subgroup X) ≤ 3 := by
    intro s hs hsB
    rw [hBcard] at hsB
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hs h5).mp hsB
    refine ⟨?_, h5rank⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ h5 ?_
    rw [Subgroup.card_top, hBcard]
    decide
  have hsplit := UC22.kFunSplit_holds X t n p f hp hp2 hadm hX hA1 hRee P B hB0 inferInstance
    hBodd hB3 hBp hperm hrank K hK
  have hBK : B ⊓ K = ⊥ := by
    have h1 : Nat.card (B ⊓ K : Subgroup X) ∣ 5 := hBcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime h5).mp h1 with h | h
    · exact Subgroup.card_eq_one.mp h
    · exact absurd (h ▸ Subgroup.card_dvd_of_le inf_le_right) h5K
  rw [hBK, bot_sup_eq] at hsplit
  exact hsplit.le.trans inf_le_right

theorem card_dvd_of_mem_funSet_psl
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (hadm : StatedLieAdmissible .PSL n p f) (hX : LieModel X .PSL n p f)
    (P : Sylow 2 X) {K : Subgroup X} (hK : K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    Nat.card K ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card (GaloisField p f) = p ^ f :=
    GaloisField.card p f (by have := hadm.2.1; omega)
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL n p f hp hp2 (by trivial) hadm X hX
  obtain ⟨m, hm, rfl | rfl⟩ := exists_frame_dim hn
  · let ψ : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1)) (GaloisField p f) →* X := ψ0
    obtain ⟨c, hfull⟩ := UC22.exists_full_coordinate_frame_funSet_psl_even hp2 hm hadm hX ψ hψ0
      hker0 P
    rw [hfull] at hK
    obtain ⟨k, rfl⟩ := hK
    refine (Subgroup.card_map_dvd _ _).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    refine (Subgroup.card_range_dvd _).trans ?_
    rw [CFSG.LieType.HighestRoot.card_SL2, hF]
  · let ψ : Matrix.SpecialLinearGroup (Fin (2 * m + 1 + 1 + 1)) (GaloisField p f) →* X := ψ0
    obtain ⟨c, hfull⟩ := UC22.exists_full_coordinate_frame_funSet_psl_odd hp2 hm hadm hX ψ hψ0
      hker0 P
    rw [hfull] at hK
    obtain ⟨k, rfl⟩ := hK
    refine (Subgroup.card_map_dvd _ _).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    refine (Subgroup.card_range_dvd _).trans ?_
    rw [CFSG.LieType.HighestRoot.card_SL2, hF]

theorem card_dvd_of_mem_funSet_psu
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (hadm : StatedLieAdmissible .PSU n p f) (hX : LieModel X .PSU n p f)
    (P : Sylow 2 X) {K : Subgroup X} (hK : K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    Nat.card K ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul]
  have hSU : Nat.card (CFSG.ClassicalInvolution.Phan.Su (GaloisField p (2 * f)) p f 2) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    obtain ⟨Pw, hPw⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF 2
    rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv Pw hPw).toEquiv]
    exact CFSG.LieType.Steinberg.card_SU_two hF
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU n p f hp hp2 (by trivial) hadm X hX
  let ψ := ψ0.comp eU.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hψ0.comp eU.symm.surjective
  have hker : ψ.ker ≤ center (CFSG.ClassicalInvolution.Phan.Su (GaloisField p (2 * f)) p f n) := by
    intro y hy
    have hy' : eU.symm y ∈ center (CFSG.ClassicalInvolution.Generic.modelUniv
        .PSU n p f hp).K := hker0 hy
    rw [Subgroup.mem_center_iff] at hy' ⊢
    intro z
    apply eU.symm.injective
    simpa only [map_mul] using hy' (eU.symm z)
  obtain ⟨m, hm, rfl | rfl⟩ := exists_frame_dim hn
  · obtain ⟨c, hfull⟩ := UC22.exists_full_coordinate_frame_funSet_psu_even hp2 hm hadm hX eU heU
      ψ hψ hker P
    rw [hfull] at hK
    obtain ⟨k, rfl⟩ := hK
    refine (Subgroup.card_map_dvd _ _).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    exact hSU ▸ Subgroup.card_range_dvd _
  · obtain ⟨c, hfull⟩ := UC22.exists_full_coordinate_frame_funSet_psu_odd hp2 hm hadm hX eU heU
      ψ hψ hker P
    rw [hfull] at hK
    obtain ⟨k, rfl⟩ := hK
    refine (Subgroup.card_map_dvd _ _).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    exact hSU ▸ Subgroup.card_range_dvd _

theorem no_permuting_five_of_linear_unitary
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X]
    (t : StatedLieTag) (n p f : ℕ)
    (ht : t = .PSL ∨ t = .PSU) (hn : 4 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hq5 : p ^ f % 5 = 2 ∨ p ^ f % 5 = 3)
    (h5rank : pRank 5 (⊤ : Subgroup X) ≤ 3)
    (P : Sylow 2 X) (B : Subgroup X) (hBcard : Nat.card B = 5)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X)) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : p ≠ 5 := by
    rintro rfl
    have : 5 ^ f % 5 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 5 (by have := hadm.2.1; omega))
    omega
  have hA1 : ¬ (t = .PSL ∧ n = 2) := fun h => by omega
  have hRee : t ≠ .twistedG2 := by
    rcases ht with rfl | rfl <;> decide
  have hcent : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      B ≤ centralizer (K : Set X) := by
    intro K hK
    refine centralizes_fundamental_of_card_five X t n p f hp hp2 hadm hX hA1 hRee hp5 h5rank P B
      hBcard hperm K hK fun h5 => not_five_dvd_of_mod_five hq5 (h5.trans ?_)
    rcases ht with rfl | rfl
    · exact card_dvd_of_mem_funSet_psl hp hp2 hn hadm hX P hK
    · exact card_dvd_of_mem_funSet_psu hp hp2 hn hadm hX P hK
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    have hB0 : B ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hBcard
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB0
    exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩
  have hb5 : b ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := B) (x := ⟨b, hbB⟩)
    rw [hBcard] at h
    simpa using congrArg Subtype.val h
  have hbK : ∀ K ∈ FunSet (fundPred (p ^ f)) X (P : Subgroup X), b ∈ centralizer (K : Set X) :=
    fun K hK => hcent K hK hbB
  obtain ⟨e, hbe, he5⟩ : ∃ e : ℕ, b ^ e = 1 ∧ ¬ 5 ∣ e := by
    obtain ⟨m, hm, rfl | rfl⟩ := exists_frame_dim hn
    · rcases ht with rfl | rfl
      · refine ⟨p ^ f - 1, UC22.pow_sub_one_eq_one_of_forall_funSet_psl_even hp2 hm hadm hX P hbK,
          ?_⟩
        generalize p ^ f = q at hq5 ⊢
        omega
      · refine ⟨(p ^ f) ^ 2 - 1,
          UC22.pow_sq_sub_one_eq_one_of_forall_funSet_psu_even hp2 hm hadm hX P hbK, ?_⟩
        have := not_five_dvd_of_mod_five hq5
        exact fun h => this (h.mul_left _)
    · rcases ht with rfl | rfl
      · refine ⟨p ^ f - 1, UC22.pow_sub_one_eq_one_of_forall_funSet_psl_odd hp2 hm hadm hX P hbK,
          ?_⟩
        generalize p ^ f = q at hq5 ⊢
        omega
      · refine ⟨(p ^ f) ^ 2 - 1,
          UC22.pow_sq_sub_one_eq_one_of_forall_funSet_psu_odd hp2 hm hadm hX P hbK, ?_⟩
        have := not_five_dvd_of_mod_five hq5
        exact fun h => this (h.mul_left _)
  have hord : orderOf b ∣ Nat.gcd 5 e :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb5) (orderOf_dvd_of_pow_eq_one hbe)
  rw [((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr he5 : Nat.gcd 5 e = 1),
    Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact hb1 hord

theorem false_of_nonabComponent_inner_linear_unitary
    (X : Type) [Group X] [Finite X] (L B T : Subgroup X) (hLs : IsSimpleGroup L)
    (hB5 : Nat.card B = 5)
    (hBT : (B : Set X) * (T : Set X) = (T : Set X) * (B : Set X))
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) (hBL : B ≤ L)
    (t : StatedLieTag) (n p f : ℕ) (ht : t = .PSL ∨ t = .PSU) (hn5 : 5 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hadm : StatedLieAdmissible t n p f)
    (hL : LieModel L t n p f) (h5rank : CFSG.Open.pRank 5 L ≤ 1) :
    False := by
  obtain ⟨Q, hQ⟩ := hTL
  have hB'card : Nat.card (B.subgroupOf L) = 5 := by
    rw [← hB5]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hperm : ((B.subgroupOf L : Subgroup L) : Set L) * ((Q : Subgroup L) : Set L) =
      ((Q : Subgroup L) : Set L) * ((B.subgroupOf L : Subgroup L) : Set L) := by
    have hBmap : (L.subtype : L →* X) '' ((B.subgroupOf L : Subgroup L) : Set L) = (B : Set X) := by
      rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBL]
    have hQmap : (L.subtype : L →* X) '' ((Q : Subgroup L) : Set L) =
        ((T ⊓ L : Subgroup X) : Set X) := by
      rw [← Subgroup.coe_map, hQ]
    apply Set.image_injective.mpr (Subgroup.subtype_injective L)
    rw [Set.image_mul, Set.image_mul, hBmap, hQmap]
    exact CFSG.GroupTheory.permutes_inf_of_le hBL hBT
  have h5rank1 : CFSG.Open.pRank 5 (⊤ : Subgroup L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact h5rank
  have hq5 := pmod_five_of_pRank_five_le_one ht hn5 hp hp5 hadm hL h5rank1
  have h5rank' : pRank 5 (⊤ : Subgroup L) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact h5rank1.trans (by norm_num)
  exact no_permuting_five_of_linear_unitary L t n p f ht (by omega) hp hp2 hadm hL hq5 h5rank'
    Q (B.subgroupOf L) hB'card hperm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
