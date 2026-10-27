module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.PCore.Construction
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Quasithin.H13.GoldschmidtG52Sec
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.QuasithinDefs
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits

private theorem exists_pow_of_card_eq_sq {K : Type*} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] {r : ℕ} (hK : Nat.card K = r ^ 2) :
    ∃ f : ℕ, 1 ≤ f ∧ r = p ^ f := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, hpprime, hcard⟩ := FiniteField.card K p
  have hpn : p ^ (e : ℕ) = r ^ 2 := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow
    (p := p) (a := r) (m := (e : ℕ)) (n := 2) hp (by norm_num) hpn
  have hr2 : 2 ≤ r := by
    by_contra h
    have hrle : r ≤ 1 := by omega
    have hcardle : Nat.card K ≤ 1 := by
      rw [hK, pow_two]
      nlinarith [Nat.zero_le r]
    have hgt : 1 < Nat.card K := Finite.one_lt_card
    omega
  refine ⟨k, ?_, hk⟩
  by_contra hk0
  have hkzero : k = 0 := by omega
  rw [hkzero, pow_zero] at hk
  omega

private theorem exists_norm_neg_one_pair {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) :
    ∃ u u' : K, σ u * u = -1 ∧ σ u' * u' = -1 ∧ u' ≠ u := by
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact (neg_ne_zero.mpr one_ne_zero) hu.symm
  refine ⟨u, ω * u, hu, ?_, ?_⟩
  · rw [map_mul]
    calc (σ ω * σ u) * (ω * u) = (σ ω * ω) * (σ u * u) := by ring
      _ = 1 * (-1) := by rw [hω, hu]
      _ = -1 := by ring
  · intro h
    have hzero : (ω - 1) * u = 0 := by
      calc (ω - 1) * u = ω * u - u := by ring
        _ = 0 := by rw [h, sub_self]
    exact (mul_ne_zero (sub_ne_zero.mpr hω1) hu0) hzero

private theorem single_mem_isotropic_span {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    (Pi.single j 1 : Fin d → K) ∈
      Submodule.span K {v : Fin d → K | herm σ v v = 0} := by
  classical
  obtain ⟨u, u', hu, hu'norm, hu'_ne⟩ := exists_norm_neg_one_pair hσ
  obtain ⟨i, hij⟩ : ∃ i : Fin d, i ≠ j := by
    obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin d)
      (by rw [Fintype.card_fin]; omega) j
    exact ⟨i, hi⟩
  set pvec : Fin d → K := Pi.single i 1 + Pi.single j u with hpvec
  set qvec : Fin d → K := Pi.single i 1 + Pi.single j u' with hqvec
  have hp_iso : herm σ pvec pvec = 0 := by
    rw [hpvec, herm_single_add_single hij, hu]
    ring
  have hq_iso : herm σ qvec qvec = 0 := by
    rw [hqvec, herm_single_add_single hij, hu'norm]
    ring
  have hdiff : pvec - qvec = Pi.single j (u - u') := by
    funext k
    by_cases hkj : k = j
    · subst hkj
      simp [hpvec, hqvec, Pi.single_eq_same]
    · by_cases hki : k = i
      · subst hki
        simp [hpvec, hqvec, Pi.single_eq_same, Pi.single_eq_of_ne hkj,
          Pi.single_eq_of_ne (Ne.symm hij)]
      · simp [hpvec, hqvec, Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hki]
  have hp_mem : pvec ∈ Submodule.span K {v : Fin d → K | herm σ v v = 0} :=
    Submodule.subset_span hp_iso
  have hq_mem : qvec ∈ Submodule.span K {v : Fin d → K | herm σ v v = 0} :=
    Submodule.subset_span hq_iso
  have hsingle : Pi.single j (u - u') ∈
      Submodule.span K {v : Fin d → K | herm σ v v = 0} := by
    have hmem := Submodule.sub_mem _ hp_mem hq_mem
    rwa [hdiff] at hmem
  have hune : u - u' ≠ 0 := sub_ne_zero.mpr (Ne.symm hu'_ne)
  have hsingle1 : Pi.single j (1 : K) ∈
      Submodule.span K {v : Fin d → K | herm σ v v = 0} := by
    have hsmul : (u - u')⁻¹ • Pi.single j (u - u') = Pi.single j 1 := by
      rw [show (u - u')⁻¹ • Pi.single j (u - u') =
          Pi.single j ((u - u')⁻¹ • (u - u')) by rw [Pi.single_smul]]
      simp [smul_eq_mul, inv_mul_cancel₀ hune]
    rw [← hsmul]
    exact Submodule.smul_mem _ _ hsingle
  exact hsingle1

private theorem isotropic_span_top {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ} (hd : 2 ≤ d) :
    Submodule.span K {v : Fin d → K | herm σ v v = 0} = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro v _
  have hv : v = ∑ j : Fin d, Pi.single j (v j) := (Finset.univ_sum_single v).symm
  rw [hv]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hsingle := single_mem_isotropic_span hσ hd j
  rw [show Pi.single j (v j) = v j • (Pi.single j (1 : K)) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ hsingle

private theorem exists_isotropic_herm_ne_zero {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ}
    (hspan : Submodule.span K {v : Fin d → K | herm σ v v = 0} = ⊤)
    {w : Fin d → K} (hw0 : w ≠ 0) :
    ∃ u : Fin d → K, herm σ u u = 0 ∧ herm σ u w ≠ 0 := by
  by_contra h
  push Not at h
  have hZ : Submodule.span K {v : Fin d → K | herm σ v v = 0} ≤ (hermL σ w).ker := by
    rw [Submodule.span_le]
    intro v hv
    exact LinearMap.mem_ker.mpr (by
      rw [hermL_apply, herm_eq_zero_comm σ hσ.invol (h v hv)])
  have hzero : ∀ y : Fin d → K, herm σ w y = 0 := by
    intro y
    have hy : y ∈ Submodule.span K {v : Fin d → K | herm σ v v = 0} := by
      rw [hspan]
      exact Submodule.mem_top
    have hyZ := LinearMap.mem_ker.mp (hZ hy)
    simpa [hermL_apply] using hyZ
  exact hw0 (eq_zero_of_herm σ hzero)

private theorem exists_isotropic_herm_eq_one {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ}
    (hspan : Submodule.span K {v : Fin d → K | herm σ v v = 0} = ⊤)
    {w : Fin d → K} (hw0 : w ≠ 0) :
    ∃ u : Fin d → K, herm σ u u = 0 ∧ herm σ u w = 1 := by
  obtain ⟨u, hu, huw⟩ := exists_isotropic_herm_ne_zero hσ hspan hw0
  set s : K := herm σ u w with hs
  have hs0 : s ≠ 0 := huw
  refine ⟨(σ s)⁻¹ • u, ?_, ?_⟩
  · rw [herm_smul_left, herm_smul_right, hu]
    ring
  · rw [herm_smul_left, ← hs, map_inv₀, hσ.invol]
    exact inv_mul_cancel₀ hs0

private theorem mem_of_herm_eq_one {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ} {W : Submodule K (Fin d → K)}
    (hW : ∀ g ∈ T σ d, ∀ v ∈ W, g • v ∈ W)
    {u w : Fin d → K} (hu : herm σ u u = 0) (huw : herm σ u w = 1) (hw : w ∈ W) :
    u ∈ W := by
  obtain ⟨c, hc0, hc⟩ := hσ.exists_traceZero
  have htv : tv hσ.invol hu hc ∈ T σ d := tv_mem_T hσ.invol hu hc
  have hmem : tv hσ.invol hu hc • w ∈ W := hW _ htv w hw
  rw [tv_smul hσ.invol hu hc w, huw, mul_one] at hmem
  have hcu : c • u ∈ W := by
    have := W.sub_mem hmem hw
    simpa using this
  have hu_eq : u = c⁻¹ • (c • u) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hu_eq]
  exact W.smul_mem _ hcu

private theorem T_submodule_eq_bot_or_top {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ} (hd : 3 ≤ d)
    (hspan : Submodule.span K {v : Fin d → K | herm σ v v = 0} = ⊤)
    (W : Submodule K (Fin d → K))
    (hW : ∀ g ∈ T σ d, ∀ v ∈ W, g • v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨u, hu, huw⟩ := exists_isotropic_herm_eq_one hσ hspan hw0
  have huW : u ∈ W := mem_of_herm_eq_one hσ hW hu huw hw
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, herm_zero_left] at huw
    exact zero_ne_one huw
  have hall : ∀ b : Fin d → K, b ≠ 0 → herm σ b b = 0 → b ∈ W := by
    intro b hb0 hb
    obtain ⟨t, ht, htb⟩ := exists_mem_T_smul_eq_of_iso hσ hd hu0 hu hb0 hb
    rw [← htb]
    exact hW t ht u huW
  have hle : Submodule.span K {v : Fin d → K | herm σ v v = 0} ≤ W := by
    rw [Submodule.span_le]
    intro b hb
    by_cases hb0 : b = 0
    · rw [hb0]
      exact W.zero_mem
    · exact hall b hb0 hb
  rw [hspan] at hle
  exact eq_top_iff.mpr hle

private theorem T_submodule_eq_bot_or_top_two {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ)
    (hspan : Submodule.span K {v : Fin 2 → K | herm σ v v = 0} = ⊤)
    (W : Submodule K (Fin 2 → K))
    (hW : ∀ g ∈ T σ 2, ∀ v ∈ W, g • v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨u, hu, huw⟩ := exists_isotropic_herm_eq_one hσ hspan hw0
  have huW : u ∈ W := mem_of_herm_eq_one hσ hW hu huw hw
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, herm_zero_left] at huw
    exact zero_ne_one huw
  obtain ⟨u', hu', hu'u⟩ := exists_isotropic_herm_eq_one hσ hspan hu0
  have hu'W : u' ∈ W := mem_of_herm_eq_one hσ hW hu' hu'u huW
  have huu' : herm σ u u' = 1 := by
    rw [herm_conj σ hσ.invol u' u, hu'u, map_one]
  have hli : LinearIndependent K ![u, u'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    constructor
    · have h1 : herm σ (s • u + t • u') u' = 0 := by rw [hst]; simp
      simp only [herm_add_left, herm_smul_left, herm_smul_left, huu', hu', mul_one, mul_zero,
        add_zero] at h1
      exact (map_eq_zero_iff σ σ.injective).mp h1
    · have h1 : herm σ (s • u + t • u') u = 0 := by rw [hst]; simp
      simp only [herm_add_left, herm_smul_left, herm_smul_left, hu, hu'u, mul_zero, mul_one,
        zero_add] at h1
      exact (map_eq_zero_iff σ σ.injective).mp h1
  have hspan_top : Submodule.span K (Set.range ![u, u']) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank ?_
    simp [Module.finrank_fin_fun]
  have hle : Submodule.span K (Set.range ![u, u']) ≤ W := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using huW
    · simpa using hu'W
  rw [eq_top_iff]
  intro v _
  exact hle (by rw [hspan_top]; trivial)

private theorem SUid_submodule_eq_bot_or_top {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ} (hd : 2 ≤ d) :
    ∀ W : Submodule K (Fin d → K), (∀ g : SUid σ d, ∀ v ∈ W, g • v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hspan := isotropic_span_top hσ hd
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · have hd2 : d = 2 := by omega
    subst hd2
    exact T_submodule_eq_bot_or_top_two hσ hspan W (fun g hg v hv => hW g v hv)
  · exact T_submodule_eq_bot_or_top hσ hge hspan W (fun g hg v hv => hW g v hv)

private theorem natRep_SUid_isIrreducible {K : Type*} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {d : ℕ} (hd : 2 ≤ d) :
    Representation.IsIrreducible (natRep (SUid σ d)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin d → K) := Function.nontrivial
  refine CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule
    (natRep (SUid σ d)) ?_
  intro U hU
  refine SUid_submodule_eq_bot_or_top hσ hd U ?_
  intro g v hv
  have := hU g v hv
  simpa [natRep_apply, smul_def] using this

private theorem subsingleton_SUid_of_le_one {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hn : n ≤ 1) : Subsingleton (SUid σ n) := by
  constructor
  intro g g'
  refine Subtype.ext (Units.ext ?_)
  ext i j
  interval_cases n
  · exact i.elim0
  · fin_cases i
    fin_cases j
    have hg := ((mem_SUid_iff σ).mp g.2).1
    have hg' := ((mem_SUid_iff σ).mp g'.2).1
    rw [Matrix.det_fin_one] at hg hg'
    exact hg.trans hg'.symm

theorem pCore_statedSU_eq_bot {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {r : ℕ} (hK : Nat.card K = r ^ 2) (d : ℕ) :
    CFSG.pCore p ↥(StatedSU d r K) = ⊥ := by
  classical
  obtain ⟨f, hf1, hrf⟩ := exists_pow_of_card_eq_sq p hK
  have hcard : Nat.card K = (p ^ f) ^ 2 := by
    rw [← hrf]
    exact hK
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hcard
  have hEq : StatedSU d r K = SUid (unitaryInvolution K p f) d := by
    rw [hrf]
    exact (SUid_eq_statedSU (p := p) (f := f) hcard d).symm
  by_cases hd : d ≤ 1
  · have hsub : Subsingleton ↥(StatedSU d r K) := by
      rw [hEq]
      exact subsingleton_SUid_of_le_one (σ := unitaryInvolution K p f) hd
    rw [eq_bot_iff]
    intro x hx
    exact Subsingleton.elim x 1
  · have hd2 : 2 ≤ d := by omega
    rw [hEq]
    refine CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible
      p (natRep (SUid (unitaryInvolution K p f) d)) (natRep_injective _) ?_
    exact natRep_SUid_isIrreducible hσ hd2

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat
