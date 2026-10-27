module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GAbs
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.RankThree.PartOne.S12.Sec15Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier
open CFSG.Quasithin.H13.KG4413 (not_dvd_index_of_isPSL3)
open CFSG.Quasithin.H13.L32A.C.SkPf (isSylowTwoOf_sylow)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_card_center_bar2_dvd_three (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hX : IsL3 (BarInf L) f) (hf1 : f ≠ 1) (hf2 : f ≠ 2) :
    Nat.card (center (Bar2 L)) ∣ 3 := by
  have hex : exceptionalOrders .PSL 3 2 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSL 3 2 f = (Nat.gcd 3 (2 ^ f - 1), 1) := rfl
  have h := card_center_bar2_dvd_of_row hL (t := .PSL) (n := 3) (p := 2) (f := f)
    (by rw [hg, hex]; simp) (griessRow_of_lieModel_classical hGA hX (by decide))
  rw [hg, hex] at h
  exact (by simpa using h : Nat.card (center (Bar2 L)) ∣ Nat.gcd 3 (2 ^ f - 1)).trans
    (Nat.gcd_dvd_left 3 _)

theorem uc22s2114_le_centralizer_of_sylow {Tor Out : ℕ → Prop} {L M R E : Subgroup G} {n r : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) (hr : r.Prime) (hr2 : r ≠ 2)
    (hY2 : ¬ r ∣ Nat.card (Sylow 2 (BarInf L))) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hML : M ≤ normalizer (L : Set G)) (hR : IsSylowOf r R M) (hER : E ≤ R) (hEL : E ≤ L)
    (hEr : ∀ e ∈ E, e ^ r = 1) : E ≤ centralizer (R : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup r R := hR.isPGroup
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hRp
    (hR.le.trans hML) (not_dvd_card_sylow_of_quotient (CFSG.solvableRadical ↥L) hr hrK hY2)
  obtain ⟨S, hS, hRS⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ R ≤ normalizer (S : Set G) :=
    ⟨_, ⟨S', rfl⟩, hS'⟩
  have hRSK : R ≤ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup_of_mem (hRS hx)
      ((hR.le.trans hML).trans (normalizer_le_normalizer_OInf L) hx)
  obtain ⟨b, hb⟩ := hRp.exists_card_eq
  have hdisj : Disjoint R (S ⊔ OInf L) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hb]
    exact Nat.Coprime.pow_left b
      ((Nat.Prime.coprime_iff_not_dvd hr).2 (not_dvd_card_sup_OInf hS hr hr2 hrK))
  refine fun e he => mem_centralizer_iff.2 fun x hx => ?_
  obtain ⟨a, ha⟩ := hRp ⟨x, hx⟩
  have hxa : x ^ r ^ a = 1 := congrArg Subtype.val ha
  obtain ⟨k, hk⟩ := exists_pow_conj_mem hS hF (hML (hR.le hx)) (hRSK hx)
    (hr.odd_of_ne_two hr2).pow hxa
  have hxE : ∀ f ∈ E, x * f * x⁻¹ = f ^ k := by
    intro f hf
    have h2 : x * f * x⁻¹ * (f ^ k)⁻¹ ∈ R :=
      mul_mem (mul_mem (mul_mem hx (hER hf)) (inv_mem hx)) (inv_mem (pow_mem (hER hf) k))
    exact mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 (hk f (hEL hf) (hRSK (hER hf))))
  exact mul_inv_eq_iff_eq_mul.1 (uc22p218s_conj_eq_self_of_pow hEr hxE hxa e he)

theorem uc22s2114_exists_pair_of_torus {L : Subgroup G} {f p r : ℕ} (hX : IsL3 (BarInf L) f)
    (hp : p.Prime) (hpf : p ∣ 2 ^ f - 1) (hp3 : p ≠ 3) (hr : r.Prime) (hrf : r ∣ 2 ^ f - 1)
    (hr3 : r ≠ 3) (hpr : p ≠ r) (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ L ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  obtain ⟨T, hTc, hTE⟩ := uc22s218_l3_torus hX
  obtain ⟨A, hAT, hAe, hAc⟩ := hTE r hr hrf hr3
  obtain ⟨Q₁, hQT, hQe, hQc⟩ := hTE p hp hpf hp3
  obtain ⟨E₂, Q₂, hE₂, hE₂c, hQ₂, hQ₂c, hpow₂⟩ :=
    exists_pair_lift (CFSG.solvableRadical ↥L) hp hr hpr hpK hrK hAe hAc hQe hQc
      fun x hx => ⟨1, fun e he => by
        rw [pow_one, mul_inv_eq_iff_eq_mul]
        exact hTc x (hQT hx) e (hAT he)⟩
  refine ⟨E₂.map L.subtype, Q₂.map L.subtype, Subgroup.map_subtype_le E₂, hE₂.map _, ?_,
    Subgroup.map_subtype_le Q₂, hQ₂.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE₂c]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hQ₂c]
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hpow₂ q hq
    refine ⟨k, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    simpa using congrArg (fun z : ↥L => (z : G)) (hk e he)

theorem uc22s2114_exists_pair_of_out {Tor Out : ℕ → Prop} {L M : Subgroup G} {n p r : ℕ}
    (hLM : L ≤ M) [(L.subgroupOf M).Normal] (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hp : p.Prime) (hp2 : p ≠ 2) (hOut : Out p) (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hr : r.Prime) (hr2 : r ≠ 2) (hY2 : ¬ r ∣ Nat.card (Sylow 2 (BarInf L)))
    (hrL : 2 ≤ CFSG.Open.pRank r L) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hpr : p ≠ r) (hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p M) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hMK : M ≤ normalizer (OInf L : Set G) := hML.trans (normalizer_le_normalizer_OInf L)
  obtain ⟨E₀, hE₀L, hE₀el, hE₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hE₀el.isPGroup
    (hE₀L.trans le_normalizer)
    (not_dvd_card_sylow_of_quotient (CFSG.solvableRadical ↥L) hr hrK hY2)
  obtain ⟨S, hS, hE₀S⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ E₀ ≤ normalizer (S : Set G) :=
    ⟨_, ⟨S', rfl⟩, hS'⟩
  have hE₀SK : E₀ ≤ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup_of_mem (hE₀S hx) (le_normalizer_OInf L (hE₀L hx))
  obtain ⟨Q, hQ, hQel, hQc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp
    (two_le_pRank_inf_of_frattini hp hLM (B := normalizer ((S ⊔ OInf L : Subgroup G) : Set G))
      (fun m hm => by
        obtain ⟨l, hlL, hl⟩ :=
          CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hS (hML hm)
        exact ⟨l, hlL, mem_normalizer_sup_of_mem hl
          (mul_mem (inv_mem (le_normalizer_OInf L hlL)) (hMK hm))⟩)
      (fun h hhL hhS hhp => eq_one_of_pow_eq_one_of_facts hS hF hp hp2 hOut hpK hhL hhS hhp)
      hrank)
  have hQM : Q ≤ M := hQ.trans inf_le_left
  have hQS : Q ≤ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) := hQ.trans inf_le_right
  have hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) →
      x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S ⊔ OInf L := fun x hx =>
    exists_pow_conj_mem hS hF (hML (hQM hx)) (hQS hx) (hp.odd_of_ne_two hp2) (hQel.2 x hx)
  obtain ⟨E, hEL, hEel, hEc, hEpow⟩ := exists_pow_conj_of_coprime (L := L)
    (S := S ⊔ OInf L) hp hr hpr (sup_le hS.le (OInf_le L))
    (not_dvd_card_sup_OInf hS hr hr2 hrK) (not_dvd_card_sup_OInf hS hp hp2 hpK) hE₀L hE₀SK hE₀el
    hE₀c hQel hQS hpow
  exact ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hEpow⟩

theorem uc22s2114_strongly_of_pair {Tor Out : ℕ → Prop} (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hML : D.M ≤ normalizer (L : Set G)) {n p r : ℕ} (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hp : p.Prime) (h76 : Conclusion76 D.M p) (hr : r.Prime) (hr2 : r ≠ 2)
    (hY2 : ¬ r ∣ Nat.card (Sylow 2 (BarInf L))) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hrσ : r ∉ D.sig) {E Q : Subgroup G} (hEL : E ≤ L) (hEel : IsElemAbelian r E)
    (hEc : Nat.card E = r ^ 2) (hQM : Q ≤ D.M) (hQel : IsElemAbelian p Q)
    (hQc : Nat.card Q = p ^ 2) (hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) :
    IsStronglyPEmbedded r D.M := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hEM : E ≤ D.M := hEL.trans hL.1.le
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [card_bot] at hEc
    exact (Nat.one_lt_pow two_ne_zero hr.one_lt).ne hEc
  obtain ⟨x, hxQ, hx1, hxC⟩ := uc22p218s_exists_mem_centralizer hp hr hQel hQc hEel hE1 hpow
  have hxle : zpowers x ≤ D.M ⊓ centralizer (E : Set G) := zpowers_le.2 ⟨hQM hxQ, hxC⟩
  have hpos : 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hp hxle (isElemAbelian_zpowers (hQel.2 x hxQ))
      (by rw [Nat.card_zpowers, orderOf_eq_prime (hQel.2 x hxQ) hx1, pow_one])
  have hXN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE _
    have hQX : Q ≤ normalizer (X : Set G) := le_normalizer_iff.2 fun x hx y hy => by
      obtain ⟨k, hk⟩ := hpow x hx
      rw [hk y (hXE hy)]
      exact pow_mem hy k
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) :=
      UC6S846.le_pRank' hp (le_inf hQM hQX) hQel hQc
    omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  have hEC : E ≤ centralizer (R : Set G) :=
    uc22s2114_le_centralizer_of_sylow hF hr hr2 hY2 hrK hML hR hER hEL hEel.2
  exact h614 (UC6S846.sig_subset_sig1 hSg (UC6S846.not_solvable_of_mem_calC hL)) r hr hr2 hrσ R
    hR E (le_inf hER hEC) hEel hEc (h76 r hr E hEM hEel hEc hpos hXN)

theorem uc22s2114_false_of_isL3_four (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsL3 (BarInf L) f) (hf : 4 ∣ f)
    (hn : 4 ∣ c.n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Nat.Prime 5 := by norm_num
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have h15 : 15 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 15 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h5n : 5 ∣ 2 ^ c.n - 1 := (by norm_num : 5 ∣ 15).trans h15
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h3σ : 3 ∉ D.sig :=
    uc22s2114_not_mem_sig hSg hns hH c Nat.prime_three ((by norm_num : 3 ∣ 15).trans h15)
  have h5σ : 5 ∉ D.sig := uc22s2114_not_mem_sig hSg hns hH c h5 h5n
  have hZ := uc22s2114_card_center_bar2_dvd_three hGA hL hX (by omega) (by omega)
  have hK : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → ¬ ℓ ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    fun ℓ hℓ hℓ2 hℓ3 => not_dvd_card_solvableRadical hL.2.2 hℓ hℓ2 fun h =>
      hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (h.trans hZ))
  have h5K := hK 5 h5 (by norm_num) (by norm_num)
  have h5L : 2 ≤ CFSG.Open.pRank 5 L := by
    obtain ⟨T, -, hTE⟩ := uc22s218_l3_torus hX
    obtain ⟨A, -, hAe, hAc⟩ := hTE 5 h5 h5f (by norm_num)
    rw [pRank_eq_pRank_barInf h5 h5K]
    exact CFSG.SectionRank.le_pRank h5.one_lt le_top hAe hAc
  have hML : D.M ≤ normalizer (L : Set G) := by
    by_contra hML
    obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank h5 h5L
    have := UC6S846.calCRankTwice D.M L hL hML 5 h5 (by norm_num)
      (fun h => absurd (h.trans hZ) (by norm_num)) E hEL hEel 2 hEc
    exact h5σ (hSg.four_mem 5 h5 (by norm_num) (by omega))
  have : (L.subgroupOf D.M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hML
  have hY2 : ¬ 5 ∣ Nat.card (Sylow 2 (BarInf L)) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (BarInf L)) := inferInstance
    rw [Sylow.card_eq_index_normalizer P]
    exact not_dvd_index_of_isPSL3 (LieModel.statedClassicalModel hX (by decide))
      (isSylowTwoOf_sylow P) h5 (by norm_num) h5f
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
  have hp5 : p ≠ 5 := fun h => h5σ (h ▸ hp)
  have hpK := hK p hpp hp2 hp3
  have hF := torusFacts218_L3 hX
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hpf : p ∣ 2 ^ f - 1
    · obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        uc22s2114_exists_pair_of_torus hX hpp hpf hp3 h5 h5f (by norm_num) hp5 hpK h5K
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · have h1 := uc22s218_l3_pRank_le_two hX hpp hp2
      rw [← pRank_eq_pRank_barInf hpp hpK] at h1
      exact uc22s2114_exists_pair_of_out hLM hF hpp hp2 hpf hpK h5 (by norm_num) hY2 h5L h5K
        hp5 (by have := h4 p hp; omega)
  exact uc22s217u3a_false_of_sp D Ch hH c h5 h5n
    (uc22s2114_strongly_of_pair D hSg h614 hL hML hF hpp
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) h5 (by norm_num) hY2 h5K h5σ hEL hEel
      hEc hQM hQel hQc hpow)

end CFSG.LocalAnalysis.UniquenessCase.UC22
