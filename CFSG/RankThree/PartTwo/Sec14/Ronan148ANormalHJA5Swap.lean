module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJGen
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJConj
import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofOrderTools
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec5.Items52
import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import TauCeti.GroupTheory.OrderOfElement.PPart
public import CFSG.RankThree.PartOne.S12.Sec12FusSyl
public import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148 Ronan148M

theorem pow_three_mem_centralizer_of_a5 {X : Type*} [Group X] {T : Subgroup X}
    (φ : ↥T ≃* alternatingGroup (Fin 5)) {g : X} (hgT : g ∈ Subgroup.normalizer (T : Set X))
    {k : ℕ} (hg : g ^ 3 ^ k = 1) : g ^ 3 ∈ Subgroup.centralizer (T : Set X) := by
  set gT : ↥(Subgroup.normalizer (T : Set X)) := ⟨g, hgT⟩ with hgTdef
  set τ : MulAut ↥T := T.normalizerMonoidHom gT with hτ
  have hτk : τ ^ 3 ^ k = 1 := by
    rw [hτ, ← map_pow]
    have : gT ^ 3 ^ k = 1 := Subtype.ext (by simpa using hg)
    rw [this, map_one]
  set σ : MulAut (alternatingGroup (Fin 5)) := MulAut.congr φ τ with hσ
  have hσk : σ ^ 3 ^ k = 1 := by rw [hσ, ← map_pow, hτk, map_one]
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 σ
  have hπk : π ^ 3 ^ k = 1 := hbij.1 (by rw [map_pow, hπ, hσk, map_one])
  have hπ3 : π ^ 3 = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hπk)
    have h120 : orderOf π ∣ 120 := by
      have := orderOf_dvd_natCard π
      rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    rw [hj] at h120
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have : 3 ^ 2 ∣ 120 := (pow_dvd_pow 3 (by omega)).trans h120
      norm_num at this
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    exact pow_dvd_pow 3 hj1
  have hσ3 : σ ^ 3 = 1 := by rw [← hπ, ← map_pow, hπ3, map_one]
  have hτ3 : τ ^ 3 = 1 := (MulAut.congr φ).injective (by rw [map_pow, ← hσ, hσ3, map_one])
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : ((τ ^ 3) ⟨t, ht⟩ : X) = t := by rw [hτ3]; rfl
  have h2 : ((τ ^ 3) ⟨t, ht⟩ : X) = g ^ 3 * t * (g ^ 3)⁻¹ := by
    rw [hτ, ← map_pow, Sec4.normalizerMonoidHom_apply_coe]
    rfl
  rw [h2] at h1
  calc t * g ^ 3 = g ^ 3 * t * (g ^ 3)⁻¹ * g ^ 3 := by rw [h1]
    _ = g ^ 3 * t := by group

theorem card_frame_eq_three {X : Type} [Group X] [Finite X] {E T K : Subgroup X}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE27 : Nat.card E = 27) (hTK : T ≤ Subgroup.centralizer (K : Set X)) {t k : X}
    (htE : t ∈ E) (htT : t ∈ T) (htC : t ∉ Subgroup.centralizer (T : Set X))
    (hkE : k ∈ E) (hkK : k ∈ K) (hkC : k ∉ Subgroup.centralizer (K : Set X))
    (hET : E ⊓ Subgroup.centralizer (T : Set X) ⊔ Subgroup.zpowers t = E)
    (hEK : E ⊓ Subgroup.centralizer (K : Set X) ⊔ Subgroup.zpowers k = E) :
    Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set X) ⊓
        (E ⊓ Subgroup.centralizer (K : Set X))) = 3 ∧
      E ≤ E ⊓ Subgroup.centralizer (T : Set X) ⊓ (E ⊓ Subgroup.centralizer (K : Set X)) ⊔
        (E ⊓ T) ⊔ (E ⊓ K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : ∀ {H₁ H₂ : Subgroup X}, H₁ ≤ E → H₂ ≤ E →
      H₁ ≤ Subgroup.normalizer (H₂ : Set X) := by
    intro H₁ H₂ h₁ h₂ x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hEab y (h₂ hy) x (h₁ hx)
  have hord : ∀ {u : X}, u ∈ E → u ≠ 1 → Nat.card (Subgroup.zpowers u) = 3 := fun hu hu1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 _ hu) hu1
  have hdisj : ∀ {H : Subgroup X} {u : X}, u ∈ E → u ≠ 1 → u ∉ H →
      H ⊓ Subgroup.zpowers u = ⊥ := by
    intro H u hu hu1 huH
    have hdvd : Nat.card ↥(H ⊓ Subgroup.zpowers u) ∣ 3 := by
      rw [← hord hu hu1]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : H ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hord hu hu1])
      have : u ∈ H ⊓ Subgroup.zpowers u := by rw [heq]; exact Subgroup.mem_zpowers u
      exact huH this.1
  have ht1 : t ≠ 1 := fun h => htC (h ▸ Subgroup.one_mem _)
  have hk1 : k ≠ 1 := fun h => hkC (h ▸ Subgroup.one_mem _)
  set CT := E ⊓ Subgroup.centralizer (T : Set X) with hCT
  set CK := E ⊓ Subgroup.centralizer (K : Set X) with hCK
  have hcard9 : ∀ {H : Subgroup X} {u : X}, H ≤ E → u ∈ E → u ≠ 1 → u ∉ H →
      H ⊔ Subgroup.zpowers u = E → Nat.card H = 9 := by
    intro H u hHE hu hu1 huH hsup
    have h := Sec6.card_sup_mul_card_inf (hnorm hHE (Subgroup.zpowers_le.mpr hu))
    rw [hsup, hdisj hu hu1 huH, Subgroup.card_bot, mul_one, hE27, hord hu hu1] at h
    omega
  have hCT9 : Nat.card CT = 9 := hcard9 inf_le_left htE ht1 (fun h => htC h.2) hET
  have hCK9 : Nat.card CK = 9 := hcard9 inf_le_left hkE hk1 (fun h => hkC h.2) hEK
  have htCK : t ∈ CK := ⟨htE, hTK htT⟩
  have hsup27 : Nat.card ↥(CT ⊔ CK) = 27 := by
    have hle : CT ⊔ CK ≤ E := sup_le inf_le_left inf_le_left
    have h1 : Nat.card ↥(CT ⊔ CK) ∣ 27 := hE27 ▸ Subgroup.card_dvd_of_le hle
    have h2 : 9 ∣ Nat.card ↥(CT ⊔ CK) := hCT9 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h3 : Nat.card ↥(CT ⊔ CK) ≠ 9 := by
      intro h9
      have heq : CT = CT ⊔ CK := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9, hCT9])
      exact htC ((heq ▸ (le_sup_right : CK ≤ CT ⊔ CK) htCK : t ∈ CT).2)
    obtain ⟨m, hm⟩ := h2
    rw [hm] at h1 h3 ⊢
    have hm3 : m ∣ 3 := by
      have h1' : 9 * m ∣ 9 * 3 := by simpa using h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1'
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h | h
    · subst h; norm_num at h3
    · subst h; norm_num
  set W := CT ⊓ CK with hW
  have hW3 : Nat.card W = 3 := by
    have h : Nat.card ↥(CT ⊔ CK) * Nat.card ↥(CT ⊓ CK) = Nat.card CT * Nat.card CK :=
      Sec6.card_sup_mul_card_inf (hnorm (inf_le_left : CT ≤ E) (inf_le_left : CK ≤ E))
    rw [hsup27, hCT9, hCK9] at h
    change 27 * Nat.card W = 9 * 9 at h
    omega
  have htW : t ∉ W := fun h => htC h.1.2
  have hWt : W ⊔ Subgroup.zpowers t = CK := by
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le (inf_le_right : W ≤ CK) (Subgroup.zpowers_le.mpr htCK)) ?_
    have h := Sec6.card_sup_mul_card_inf (hnorm (inf_le_left.trans inf_le_left : W ≤ E)
      (Subgroup.zpowers_le.mpr htE))
    rw [hdisj htE ht1 htW, Subgroup.card_bot, mul_one, hW3, hord htE ht1] at h
    rw [hCK9, h]
  have hE : E ≤ W ⊔ (E ⊓ T) ⊔ (E ⊓ K) := by
    have h1 : E = W ⊔ Subgroup.zpowers t ⊔ Subgroup.zpowers k := by rw [hWt, hEK]
    have h2 : W ⊔ Subgroup.zpowers t ⊔ Subgroup.zpowers k ≤ W ⊔ (E ⊓ T) ⊔ (E ⊓ K) :=
      sup_le_sup (sup_le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨htE, htT⟩)) _)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hkE, hkK⟩))
    exact h1.le.trans h2
  exact ⟨hW3, hE⟩

theorem le_centralizer_of_frame {X : Type} [Group X] [Finite X] {E T K Q : Subgroup X}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE27 : Nat.card E = 27) (hTK : T ≤ Subgroup.centralizer (K : Set X)) {t k : X}
    (htE : t ∈ E) (htT : t ∈ T) (htC : t ∉ Subgroup.centralizer (T : Set X))
    (hkE : k ∈ E) (hkK : k ∈ K) (hkC : k ∉ Subgroup.centralizer (K : Set X))
    (hET3 : Nat.card ↥(E ⊓ T) = 3) (hEK3 : Nat.card ↥(E ⊓ K) = 3)
    (hET : E ⊓ Subgroup.centralizer (T : Set X) ⊔ Subgroup.zpowers t = E)
    (hEK : E ⊓ Subgroup.centralizer (K : Set X) ⊔ Subgroup.zpowers k = E)
    (hQ : IsPGroup 3 Q) (hQE : Q ≤ Subgroup.normalizer (E : Set X))
    (hQT : Q ≤ Subgroup.normalizer (T : Set X)) (hQK : Q ≤ Subgroup.normalizer (K : Set X)) :
    Q ≤ Subgroup.centralizer (E : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hW3, hE⟩ := card_frame_eq_three hEab hE3 hE27 hTK htE htT htC hkE hkK hkC hET hEK
  set W := E ⊓ Subgroup.centralizer (T : Set X) ⊓ (E ⊓ Subgroup.centralizer (K : Set X)) with hW
  have hQW : Q ≤ Subgroup.centralizer (W : Set X) := by
    refine Res6Order.le_centralizer_of_card_three hQ hW3 ?_
    have hCTn := Late.le_normalizer_inf hQE
      (hQT.trans (Sec5.normalizer_le_normalizer_centralizer T))
    have hCKn := Late.le_normalizer_inf hQE
      (hQK.trans (Sec5.normalizer_le_normalizer_centralizer K))
    exact Late.le_normalizer_inf hCTn hCKn
  have hQT' : Q ≤ Subgroup.centralizer ((E ⊓ T : Subgroup X) : Set X) :=
    Res6Order.le_centralizer_of_card_three hQ hET3 (Late.le_normalizer_inf hQE hQT)
  have hQK' : Q ≤ Subgroup.centralizer ((E ⊓ K : Subgroup X) : Set X) :=
    Res6Order.le_centralizer_of_card_three hQ hEK3 (Late.le_normalizer_inf hQE hQK)
  intro q hq
  have hle : W ⊔ (E ⊓ T) ⊔ (E ⊓ K) ≤ Subgroup.centralizer ({q} : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro y hy <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (Subgroup.mem_centralizer_iff.mp (hQW hq) y hy)
    · exact (Subgroup.mem_centralizer_iff.mp (hQT' hq) y hy)
    · exact (Subgroup.mem_centralizer_iff.mp (hQK' hq) y hy)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hE hy))

theorem exists_order_nine_of_not_sylow {X : Type} [Group X] [Finite X] {E T K H : Subgroup X}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE27 : Nat.card E = 27)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (E : Set X) → w ^ 3 = 1 → w ∈ E)
    (φT : ↥T ≃* alternatingGroup (Fin 5)) (φK : ↥K ≃* alternatingGroup (Fin 5))
    (hTK : T ≤ Subgroup.centralizer (K : Set X)) (hEH : E ≤ H)
    (hHT : H ≤ Subgroup.normalizer (T : Set X)) (hHK : H ≤ Subgroup.normalizer (K : Set X))
    (hnat : ∀ s ∈ Subgroup.normalizer (E : Set X), T.map (MulAut.conj s).toMonoidHom ≠ K)
    {x : X} (hxT : T.map (MulAut.conj x).toMonoidHom = K)
    (hxH : E.map (MulAut.conj x).toMonoidHom ≤ H) :
    ∃ g ∈ H, g ∈ Subgroup.centralizer (E : Set X) ∧ ∃ m : ℕ, 2 ≤ m ∧ orderOf g = 3 ^ m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  have hET : E ≤ Subgroup.normalizer (T : Set X) := hEH.trans hHT
  have hEK : E ≤ Subgroup.normalizer (K : Set X) := hEH.trans hHK
  obtain ⟨t₀, ht₀T, ht₀E, ht₀1, -, hEt⟩ := exists_inner_a5_of_normalizer hEab hE3 hF3 hET φT
  obtain ⟨k₀, hk₀K, hk₀E, hk₀1, -, hEk⟩ := exists_inner_a5_of_normalizer hEab hE3 hF3 hEK φK
  have hcard3 : ∀ {S : Subgroup X} (φ : ↥S ≃* alternatingGroup (Fin 5)) {u : X}, u ∈ E → u ∈ S →
      u ≠ 1 → Nat.card ↥(E ⊓ S) = 3 := by
    intro S φ u huE huS hu1
    have h60 : Nat.card S = 60 := by
      rw [Nat.card_congr φ.toEquiv]
      exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    have h1 : Nat.card ↥(E ⊓ S) ∣ 60 := h60 ▸ Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥(E ⊓ S) ∣ 27 := hE27 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card ↥(E ⊓ S) ∣ 3 := by
      have : Nat.card ↥(E ⊓ S) ∣ Nat.gcd 60 27 := Nat.dvd_gcd h1 h2
      simpa using this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exfalso
      have := Subgroup.card_eq_one.mp h
      exact hu1 (Subgroup.mem_bot.mp (this ▸ Subgroup.mem_inf.mpr ⟨huE, huS⟩))
    · exact h
  set E' := E.map (MulAut.conj x).toMonoidHom with hE'
  obtain ⟨P, hP, hEP⟩ := Sec13.Item134SylowBarProof.exists_isSylowOf_le hEH hEp
  by_cases hPE : P = E
  ·
    exfalso
    rw [hPE] at hP
    have hE'card : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hP' : CFSG.ABGLocalTools.IsSylowOf 3 E' H :=
      CFSG.ABGLocalTools.isSylowOf_of_card hxH (by rw [hE'card]; exact hP.card_eq)
    obtain ⟨n, hnH, hn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hP hP'
    apply hnat (n⁻¹ * x)
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show E.map (MulAut.conj (n⁻¹ * x)).toMonoidHom = E
      rw [← Late.map_conj_map_conj, ← hE', hn, Late.map_conj_map_conj, inv_mul_cancel,
        Late.map_conj_one]
    · rw [← Late.map_conj_map_conj, hxT]
      exact Late.map_conj_eq_of_mem_normalizer (inv_mem (hHK hnH))
  obtain ⟨g, hgP, hgE, hgN⟩ := CFSG.RankThree.PartOne.Sec12Fus.exists_mem_normalizer_sdiff hEP
    hP.isPGroup (Ne.symm hPE)
  have hgH : g ∈ H := hP.le hgP
  have hQ : IsPGroup 3 (Subgroup.zpowers g) :=
    hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hgP)
  have hgC : g ∈ Subgroup.centralizer (E : Set X) :=
    le_centralizer_of_frame hEab hE3 hE27 hTK ht₀E ht₀T (not_mem_centralizer_of_a5 φT ht₀T ht₀1)
      hk₀E hk₀K (not_mem_centralizer_of_a5 φK hk₀K hk₀1) (hcard3 φT ht₀E ht₀T ht₀1)
      (hcard3 φK hk₀E hk₀K hk₀1) hEt hEk hQ (Subgroup.zpowers_le.mpr hgN)
      (Subgroup.zpowers_le.mpr (hHT hgH)) (Subgroup.zpowers_le.mpr (hHK hgH))
      (Subgroup.mem_zpowers g)
  obtain ⟨k, hk⟩ := hP.isPGroup ⟨g, hgP⟩
  have hgk : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hgk)
  have hg3 : g ^ 3 ≠ 1 := fun h => hgE (hF3 g hgC h)
  have hm2 : 2 ≤ m := by
    by_contra hm2
    apply hg3
    rw [← orderOf_dvd_iff_pow_eq_one, hm]
    exact (pow_dvd_pow 3 (show m ≤ 1 by omega)).trans (pow_one 3).dvd
  exact ⟨g, hgH, hgC, m, hm2, hm⟩

theorem pow_pred_mem_centralizer_of_a5 {X : Type} [Group X] {S : Subgroup X}
    (φ : ↥S ≃* alternatingGroup (Fin 5)) {g : X}
    (hgS : g ∈ Subgroup.normalizer (S : Set X)) {m : ℕ} (hm2 : 2 ≤ m) (hgm : orderOf g = 3 ^ m) :
    g ^ 3 ^ (m - 1) ∈ Subgroup.centralizer (S : Set X) := by
  have hgk : g ^ 3 ^ m = 1 := by rw [← hgm]; exact pow_orderOf_eq_one g
  have h3 := pow_three_mem_centralizer_of_a5 φ hgS hgk
  have : g ^ 3 ^ (m - 1) = (g ^ 3) ^ 3 ^ (m - 2) := by
    rw [← pow_mul, ← pow_succ']
    congr 2
    omega
  rw [this]
  exact Subgroup.pow_mem _ h3 _

theorem exists_order_nine_of_swap {X : Type} [Group X] [Finite X] {E T K : Subgroup X}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE27 : Nat.card E = 27)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (E : Set X) → w ^ 3 = 1 → w ∈ E)
    (φT : ↥T ≃* alternatingGroup (Fin 5)) (φK : ↥K ≃* alternatingGroup (Fin 5))
    (hTK : T ≤ Subgroup.centralizer (K : Set X)) (hET : E ≤ Subgroup.normalizer (T : Set X))
    (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hnat : ∀ s ∈ Subgroup.normalizer (E : Set X), T.map (MulAut.conj s).toMonoidHom ≠ K)
    {x : X} (hxT : T.map (MulAut.conj x).toMonoidHom = K)
    (hxK : K.map (MulAut.conj x).toMonoidHom = T) :
    ∃ g ∈ Subgroup.centralizer (E : Set X), ∃ m : ℕ, 2 ≤ m ∧ orderOf g = 3 ^ m ∧
      g ^ 3 ^ (m - 1) ∈ Subgroup.centralizer (K : Set X) := by
  have hE'H : E.map (MulAut.conj x).toMonoidHom ≤
      Subgroup.normalizer (T : Set X) ⊓ Subgroup.normalizer (K : Set X) := by
    refine le_inf ?_ ?_
    · have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hEK
      rwa [Subgroup.map_equiv_normalizer_eq, hxK] at h
    · have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hET
      rwa [Subgroup.map_equiv_normalizer_eq, hxT] at h
  obtain ⟨g, hgH, hgC, m, hm2, hm⟩ := exists_order_nine_of_not_sylow hEab hE3 hE27 hF3 φT φK hTK
    (le_inf hET hEK) inf_le_left inf_le_right hnat hxT hE'H
  exact ⟨g, hgC, m, hm2, hm, pow_pred_mem_centralizer_of_a5 φK hgH.2 hm2 hm⟩

section Quot

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_three_element148 {A Y : Subgroup G} (hA3 : IsPGroup 3 A) (hY : Y ∈ scriptY A)
    [(ker148 A Y).Normal] {g : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hgC : g ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) {m : ℕ}
    (hgm : orderOf g = 3 ^ m) :
    ∃ z : ↥(Y ⊔ A), QuotientGroup.mk' (ker148 A Y) z = g ∧ z ^ 3 ^ m = 1 ∧
      (z : G) ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) g
  have hk : ∀ a ∈ A, (k : G)⁻¹ * (a * k * a⁻¹) ∈ pPrimeCoreOf 3 Y := by
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp hgC _ (alpha148_mem_img148 (Y := Y) ha)
    rw [alpha148_eq_mk'] at h1
    have h2 : QuotientGroup.mk' (ker148 A Y) k =
        QuotientGroup.mk' (ker148 A Y) (⟨a, Subgroup.mem_sup_right ha⟩ * k *
          (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(Y ⊔ A))⁻¹) := by
      rw [map_mul, map_mul, map_inv, h1, mul_inv_cancel_right]
    have h3 := (QuotientGroup.eq (s := ker148 A Y)).mp h2
    exact Subgroup.mem_subgroupOf.mp h3
  have hAO : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    hY.2.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  obtain ⟨y, hky, hyA⟩ := exists_commute_mem_coset148 hA3 (coprime_card_pPrimeCoreOf 3 Y) hAO hk
  have hyM : y ∈ Y ⊔ A := by
    have : y = (k : G) * ((k : G)⁻¹ * y) := by group
    rw [this]
    exact (Y ⊔ A).mul_mem k.2 (Subgroup.mem_sup_left (pPrimeCoreOf_le 3 Y hky))
  set y' : ↥(Y ⊔ A) := ⟨y, hyM⟩ with hy'
  have hyk : QuotientGroup.mk' (ker148 A Y) y' = QuotientGroup.mk' (ker148 A Y) k := by
    refine (QuotientGroup.eq (s := ker148 A Y)).mpr ?_
    rw [ker148, Subgroup.mem_subgroupOf]
    have : ((y'⁻¹ * k : ↥(Y ⊔ A)) : G) = ((k : G)⁻¹ * y)⁻¹ := by simp [hy']
    rw [this]
    exact inv_mem hky
  set z := TauCeti.pPart 3 y' with hz
  have hy0 : orderOf y' ≠ 0 := (orderOf_pos y').ne'
  have hzo : orderOf z = 3 ^ (orderOf y').factorization 3 :=
    TauCeti.orderOf_pPart Nat.prime_three hy0
  have hfree : QuotientGroup.mk' (ker148 A Y) (TauCeti.pFreePart 3 y') = 1 := by
    set u := QuotientGroup.mk' (ker148 A Y) (TauCeti.pFreePart 3 y') with hu
    have h1 : orderOf u ∣ orderOf (TauCeti.pFreePart 3 y') := orderOf_map_dvd _ _
    have h2 : orderOf u ∣ 3 ^ m := by
      rw [← hgm, ← hyk]
      refine orderOf_dvd_of_mem_zpowers ?_
      rw [hu, ← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem _ (TauCeti.pFreePart_mem_zpowers 3 y')
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    have hj0 : j = 0 := by
      by_contra hj0
      exact TauCeti.not_dvd_orderOf_pFreePart Nat.prime_three hy0
        ((dvd_pow_self 3 hj0).trans (hj ▸ h1))
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  have hzk : QuotientGroup.mk' (ker148 A Y) z = QuotientGroup.mk' (ker148 A Y) k := by
    rw [← hyk, ← TauCeti.pFreePart_mul_pPart 3 y', map_mul, hfree, one_mul]
  refine ⟨z, hzk, ?_, ?_⟩
  ·
    have hker : z ^ 3 ^ m ∈ ker148 A Y := by
      rw [← QuotientGroup.eq_one_iff (N := ker148 A Y), ← QuotientGroup.mk'_apply, map_pow, hzk,
        ← hgm, pow_orderOf_eq_one]
    have h1 : orderOf (z ^ 3 ^ m) ∣ Nat.card ↥(ker148 A Y) :=
      Subgroup.orderOf_dvd_natCard _ hker
    have h2 : orderOf (z ^ 3 ^ m) ∣ 3 ^ (orderOf y').factorization 3 := by
      rw [← hzo]
      exact orderOf_pow_dvd _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    have hj0 : j = 0 := by
      by_contra hj0
      exact Main148.not_three_dvd_card_ker148 ((dvd_pow_self 3 hj0).trans (hj ▸ h1))
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  ·
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (TauCeti.pPart_mem_zpowers 3 y')
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hz, ← hn, Subgroup.coe_zpow]
    exact ((Commute.zpow_right (show Commute a y from hyA a ha) n)).eq

end Quot

section HJ

variable {G : Type} [Group G] [Finite G]

theorem pow_mem_zpowers_of_isLBConfig
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {z : G}
    (hzA : z ∈ Subgroup.centralizer (A : Set G)) {m : ℕ} (hm : 2 ≤ m) (hz : z ^ 3 ^ m = 1) :
    z ^ 3 ^ (m - 1) ∈ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hbA : b ∈ A := hB.1 hbB
  have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzA b hbA).symm
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  obtain ⟨φ⟩ := Item148HJ.j2_of_isLBConfig hc
  have h3Lb : 3 ∣ Nat.card Lb := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥Lb)
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
    rw [h1]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hzN : z ∈ Subgroup.normalizer (Lb : Set G) := by
    have huniq := (hS.chosen136.2 b hc.2.1 Lb hLb).2
    have hmem := Sec6.map_conj_mem_thetaComponentsAt hzb hLb.1
    have h3 : 3 ∣ Nat.card ↥(Lb.map (MulAut.conj z).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj z).injective]
      exact h3Lb
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hmem h3)
  set Q := ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb with hQ
  set zN : ↥(Subgroup.normalizer (Lb : Set G)) := ⟨z, hzN⟩ with hzN'
  set σ : MulAut Q := Sec4.thetaQuotMulAut ↥Lb (Lb.normalizerMonoidHom zN) with hσ
  have hσm : σ ^ 3 ^ m = 1 := by
    rw [hσ, ← map_pow, ← map_pow]
    have : zN ^ 3 ^ m = 1 := Subtype.ext (by simpa using hz)
    rw [this, map_one, map_one]
  obtain ⟨v, hv⟩ := Sec17.j2_mem_range_conj_of_pow_eq_one ⟨φ⟩ hσm
  set π : ↥Lb →* Q := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) with hπ
  set E : Subgroup Q := (A.subgroupOf Lb).map π with hE
  have hσe : ∀ e ∈ E, σ e = e := by
    rintro _ ⟨e, he, rfl⟩
    rw [hπ, QuotientGroup.mk'_apply, hσ, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    have hze := Subgroup.mem_centralizer_iff.mp hzA (e : G) (Subgroup.mem_subgroupOf.mp he)
    change z * e * z⁻¹ = e
    rw [← hze, mul_inv_cancel_right]
  have hvE : v ∈ Subgroup.centralizer (E : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := hσe e he
    rw [← hv, MulAut.conj_apply] at h1
    calc e * v = v * e * v⁻¹ * v := by rw [h1]
      _ = v * e := by group
  have hS' := Item148HJ.sec14Std_of_isLBConfig hS hc
  obtain ⟨-, hAL9, -⟩ := j2_point_facts hS'.toSec13Data ⟨φ⟩
  have hθ3 : ¬ 3 ∣ Nat.card ↥(aschbacherSolvableCore 3 ↥Lb) := by
    have h := (Sec6.theta_solvable_and_not_dvd Lb).2
    rwa [inSubgroup, Subgroup.card_map_of_injective Lb.subtype_injective] at h
  have hinj : Function.Injective (π.comp (A.subgroupOf Lb).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx3 : ((x : ↥Lb) : G) ^ 3 = 1 := hA.1.2 _ (Subgroup.mem_subgroupOf.mp x.2)
    have hxo : orderOf (x : ↥Lb) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx3))
    have hxθ : orderOf (x : ↥Lb) ∣ Nat.card ↥(aschbacherSolvableCore 3 ↥Lb) :=
      Subgroup.orderOf_dvd_natCard _ hx
    have h1 : orderOf (x : ↥Lb) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hxo with h | h
      · exact h
      · exact absurd (h ▸ hxθ) hθ3
    exact Subgroup.mem_bot.mpr (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hE9 : Nat.card E = 9 := by
    have hrange : (π.comp (A.subgroupOf Lb).subtype).range = E := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Nat.card E = Nat.card ↥(A.subgroupOf Lb) := by
      rw [← hrange]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1, ← Subgroup.inf_subgroupOf_left A Lb,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, inf_comm, hAL9]
  have hvE' : v ∈ E := KFacts.ks17J2CentralizerNine Q ⟨φ⟩ E hE9 hvE
  have hv3 : v ^ 3 = 1 := by
    obtain ⟨e, he, rfl⟩ := hvE'
    rw [← map_pow]
    have : e ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp he))
    rw [this, map_one]
  have hσ3 : σ ^ 3 = 1 := by rw [← hv, ← map_pow, hv3, map_one]
  have hexp : 3 ^ (m - 1) = 3 * 3 ^ (m - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hwσ : Sec4.thetaQuotMulAut ↥Lb (Lb.normalizerMonoidHom (zN ^ 3 ^ (m - 1))) = 1 := by
    rw [map_pow, map_pow, ← hσ, hexp, pow_mul, hσ3, one_pow]
  have hwA : z ^ 3 ^ (m - 1) ∈ A := by
    have hw3 : (z ^ 3 ^ (m - 1)) ^ 3 = 1 := by
      rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, hz]
    exact Sec4.mem_of_maximal_of_commute hS.maximal_isElemAbelian hw3 fun a ha =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hzA _) a ha
  have hwsc : z ^ 3 ^ (m - 1) ∈
      Late.sectionCentralizer A Lb ((aschbacherSolvableCore 3 ↥Lb).map Lb.subtype) := by
    refine ⟨hwA, fun x hx => ?_⟩
    have h1 := congrArg (fun f : MulAut Q => f (π ⟨x, hx⟩)) hwσ
    simp only [MulAut.one_apply] at h1
    rw [hπ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk] at h1
    have h2 : Lb.normalizerMonoidHom (zN ^ 3 ^ (m - 1)) ⟨x, hx⟩ * (⟨x, hx⟩ : ↥Lb)⁻¹ ∈
        aschbacherSolvableCore 3 ↥Lb := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
        mul_inv_cancel]
    refine ⟨_, h2, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
      Subgroup.coe_inv, Subgroup.coe_pow]
  have hzb' := hLb.2.2.1
  have hmem : z ^ 3 ^ (m - 1) ∈ (Subgroup.zpowers b : Set G) := hzb' ▸ hwsc
  exact hmem

end HJ


section Frame

variable {G : Type} [Group G] [Finite G]

theorem false_of_swap148
    {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {T K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (φT : ↥T ≃* alternatingGroup (Fin 5))
    (φK : ↥K ≃* alternatingGroup (Fin 5))
    (hTK : T ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAT : img148 A Y A ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAK : img148 A Y A ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hnat : ∀ s ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      T.map (MulAut.conj s).toMonoidHom ≠ K)
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hxT : T.map (MulAut.conj x).toMonoidHom = K)
    (hxK : K.map (MulAut.conj x).toMonoidHom = T)
    (hnoPt : ∀ (a : G) (ha : a ∈ A), Subgroup.zpowers a ∈ omegaA A →
      alpha148 A Y a ha ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  have hA3' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  obtain ⟨g, hgC, m, hm2, hgm, hgK⟩ :=
    exists_order_nine_of_swap hAab hA3 hAE.2 hF3 φT φK hTK hAT hAK hnat hxT hxK
  obtain ⟨z, hzg, hzm, hzA⟩ := exists_lift_three_element148 hA3' hY hgC hgm
  have hzm' : (z : G) ^ 3 ^ m = 1 := by
    rw [← Subgroup.coe_pow, hzm, Subgroup.coe_one]
  have hw := pow_mem_zpowers_of_isLBConfig hS hB hc hzA hm2 hzm'
  obtain ⟨hbB, -, hb1, -, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hg1 : alpha148 A Y b hbA ^ k = g ^ 3 ^ (m - 1) := by
    rw [alpha148_eq_mk', ← map_zpow, ← hzg, ← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_zpow, Subgroup.coe_pow]
    exact hk
  have hg1ne : g ^ 3 ^ (m - 1) ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hgm]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbα1 : alpha148 A Y b hbA ≠ 1 := by
    intro h
    exact hb1 (alpha148_injective (Y := Y) hA.1.2 hbA (Subgroup.one_mem A) (by rw [h]; rfl))
  have hob : orderOf (alpha148 A Y b hbA) = 3 :=
    orderOf_eq_prime (hA3 _ (alpha148_mem_img148 hbA)) hbα1
  have hog : orderOf (g ^ 3 ^ (m - 1)) = 3 := by
    refine orderOf_eq_prime ?_ hg1ne
    rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, ← hgm, pow_orderOf_eq_one]
  have hzz : Subgroup.zpowers (g ^ 3 ^ (m - 1)) = Subgroup.zpowers (alpha148 A Y b hbA) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨k, hg1⟩)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hog, hob])
  have hbK : alpha148 A Y b hbA ∈ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    (Subgroup.zpowers_le.mpr hgK) (hzz ▸ Subgroup.mem_zpowers _)
  exact hnoPt b hbA hc.2.1 hbK

theorem false_of_three_cycle148 {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {T K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (φT : ↥T ≃* alternatingGroup (Fin 5))
    (φK : ↥K ≃* alternatingGroup (Fin 5)) (hKc : IsComponent K)
    (hTK : T ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAT : img148 A Y A ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAK : img148 A Y A ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hnat : ∀ s ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      T.map (MulAut.conj s).toMonoidHom ≠ K)
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hxT : T.map (MulAut.conj x).toMonoidHom = K)
    (hxK : K.map (MulAut.conj x).toMonoidHom ≠ T) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hinj : ∀ (H₁ H₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)) (y : ↥(Y ⊔ A) ⧸ ker148 A Y),
      H₁.map (MulAut.conj y).toMonoidHom = H₂.map (MulAut.conj y).toMonoidHom → H₁ = H₂ :=
    fun H₁ H₂ y hy => Subgroup.map_injective (MulAut.conj y).injective hy
  have hcomm : ∀ {U V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}, IsComponent U → IsComponent V →
      U ≠ V → V ≤ Subgroup.centralizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun hU hV hUV _ hy => Res2LBal.mem_centralizer_of_mem_of_ne hU hV hUV hy
  have hiso : ∀ {S : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}, (↥S ≃* alternatingGroup (Fin 5)) →
      ∀ y : ↥(Y ⊔ A) ⧸ ker148 A Y,
        Nonempty (↥(S.map (MulAut.conj y).toMonoidHom) ≃* alternatingGroup (Fin 5)) :=
    fun φ y => ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj y).injective).symm.trans φ⟩
  have hTc : IsComponent T := by
    have h := Res2LBal.isComponent_conj hKc x⁻¹
    rwa [← hxT, Res2LBal.map_conj_map_conj, inv_mul_cancel, Res2LBal.map_conj_one] at h
  have hTK' : T ≠ K := by
    intro h
    obtain ⟨t, htT, -, -, htZ⟩ := exists_three_of_a5 φT
    apply htZ
    have := hTK htT
    rwa [← h] at this
  have hT₃c : IsComponent (K.map (MulAut.conj x).toMonoidHom) := Res2LBal.isComponent_conj hKc x
  obtain ⟨φ₃⟩ := hiso φK x
  have h3K : K.map (MulAut.conj x).toMonoidHom ≠ K := fun h =>
    hTK' (hinj T K x (hxT.trans h.symm))
  have h4 : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = T := by
    by_contra h4
    have hT₄c := Res2LBal.isComponent_conj hT₃c x
    obtain ⟨φ₄⟩ := hiso φ₃ x
    have h4K : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom ≠ K :=
      fun h => hxK (hinj _ T x (h.trans hxT.symm))
    have h43 : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom ≠
        K.map (MulAut.conj x).toMonoidHom := fun h => h3K (hinj _ K x h)
    obtain ⟨j, hjT, hj1, hj3, hjZ⟩ := exists_three_of_a5 φT
    obtain ⟨T0, hT0T, hT0, hT02, hjT0⟩ := exists_two_subgroup_of_a5 φT hjT hj3 hj1
    obtain ⟨k, hkK, -, hk3, hkZ⟩ := exists_three_of_a5 φK
    obtain ⟨u₃, hu₃, -, hu₃3, hu₃Z⟩ := exists_three_of_a5 φ₃
    obtain ⟨u₄, hu₄, -, hu₄3, hu₄Z⟩ := exists_three_of_a5 φ₄
    exact false_of_four_commuting148 hS (hcomm hTc hKc hTK') (hcomm hTc hT₃c (Ne.symm hxK))
      (hcomm hTc hT₄c (Ne.symm h4)) (hcomm hKc hT₃c (Ne.symm h3K))
      (hcomm hKc hT₄c (Ne.symm h4K)) (hcomm hT₃c hT₄c (Ne.symm h43)) hjT hkK hu₃ hu₄ hj3 hk3
      hu₃3 hu₄3 hjZ hkZ hu₃Z hu₄Z hT0 hT02 hT0T hjT0
  have hAT₃ : img148 A Y A ≤ Subgroup.normalizer
      ((K.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_normalizer_of_a5_component148 hS hTc hT₃c hxK hAT hA3 φT φ₃
  have hxH : (img148 A Y A).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊓
        Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊓
        Subgroup.normalizer
          ((K.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine le_inf (le_inf ?_ ?_) ?_
    · have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hAT₃
      rwa [Subgroup.map_equiv_normalizer_eq, h4] at h
    · have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hAT
      rwa [Subgroup.map_equiv_normalizer_eq, hxT] at h
    · have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hAK
      rwa [Subgroup.map_equiv_normalizer_eq] at h
  obtain ⟨g, hgH, hgC, m, hm2, hgm⟩ := exists_order_nine_of_not_sylow hAab hA3 hAE.2 hF3 φT φK
    hTK (le_inf (le_inf hAT hAK) hAT₃) (fun _ h => h.1.1) (fun _ h => h.1.2) hnat hxT hxH
  have hg₁T := pow_pred_mem_centralizer_of_a5 φT hgH.1.1 hm2 hgm
  have hg₁K := pow_pred_mem_centralizer_of_a5 φK hgH.1.2 hm2 hgm
  have hg₁3 := pow_pred_mem_centralizer_of_a5 φ₃ hgH.2 hm2 hgm
  have hg₁E : g ^ 3 ^ (m - 1) ∈ img148 A Y A := by
    refine hF3 _ (Subgroup.pow_mem _ hgC _) ?_
    rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, ← hgm, pow_orderOf_eq_one]
  have hg₁1 : g ^ 3 ^ (m - 1) ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hgm]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨t₀, ht₀T, ht₀E, ht₀1, -, hEt⟩ := exists_inner_a5_of_normalizer hAab hA3 hF3 hAT φT
  obtain ⟨k₀, hk₀K, hk₀E, hk₀1, -, hEk⟩ := exists_inner_a5_of_normalizer hAab hA3 hF3 hAK φK
  obtain ⟨t₃, ht₃T, ht₃E, ht₃1, ht₃3, -⟩ := exists_inner_a5_of_normalizer hAab hA3 hF3 hAT₃ φ₃
  obtain ⟨hW3, -⟩ := card_frame_eq_three hAab hA3 hAE.2 hTK ht₀E ht₀T
    (not_mem_centralizer_of_a5 φT ht₀T ht₀1) hk₀E hk₀K (not_mem_centralizer_of_a5 φK hk₀K hk₀1)
    hEt hEk
  have ht₃W : t₃ ∈ img148 A Y A ⊓ Subgroup.centralizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊓
      (img148 A Y A ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :=
    ⟨⟨ht₃E, hcomm hTc hT₃c (Ne.symm hxK) ht₃T⟩, ⟨ht₃E, hcomm hKc hT₃c (Ne.symm h3K) ht₃T⟩⟩
  have hWeq : Subgroup.zpowers t₃ =
      img148 A Y A ⊓ Subgroup.centralizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊓
        (img148 A Y A ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht₃W)
      (by rw [hW3, Nat.card_zpowers, orderOf_eq_prime ht₃3 ht₃1])
  have hg₁t : g ^ 3 ^ (m - 1) ∈ Subgroup.zpowers t₃ := by
    rw [hWeq]
    exact ⟨⟨hg₁E, hg₁T⟩, ⟨hg₁E, hg₁K⟩⟩
  exact hg₁1 (eq_one_of_mem_zpowers_centralizer ht₃3 (not_mem_centralizer_of_a5 φ₃ ht₃T ht₃1)
    hg₁t hg₁3)

end Frame

section Certificates


theorem step148NormalHJA5Three_holds :
    Step148NormalHJA5Three := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hXeq hZ15 h12 K hKc hK5 x hxY hKx hgen hKX hAK k₀
    hk₀K hk₀A hk₀1 hAeqK hnoPt
  let := ker148_normal hY.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hS.isE27.2]; norm_num)
  obtain ⟨φK⟩ := hK5
  obtain ⟨T, hT, hxT⟩ : ∃ T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      (T = img148 A Y J ∨ T = img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ∧
        T.map (MulAut.conj x).toMonoidHom = K := by
    rcases hKx with h | h
    · exact ⟨_, Or.inl rfl, h.symm⟩
    · exact ⟨_, Or.inr rfl, h.symm⟩
  have hTX : T ≤ img148 A Y (deltaZero A (lB A) Y) := by
    rcases hT with rfl | rfl
    · exact hXeq ▸ le_sup_left
    · exact hXeq ▸ le_sup_right
  have hTK : T ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hTX.trans (Subgroup.le_centralizer_iff.mp hKX)
  have hAT : img148 A Y A ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rcases hT with rfl | rfl
    · exact img148_le_normalizer hAJ
    · exact img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  have hT5 : Nonempty (↥T ≃* alternatingGroup (Fin 5)) := by
    rcases hT with rfl | rfl
    · exact hJ5
    · rcases hZ15 with h0 | h5
      · exfalso
        have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKc.1
        rw [← hxT, h0, Subgroup.map_bot] at this
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
      · exact h5
  obtain ⟨φT⟩ := hT5
  have hnat : ∀ s ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      T.map (MulAut.conj s).toMonoidHom ≠ K := fun s hs hsK =>
    false_of_map_conj_normalizer148 hA3 hY hs hTX hKc hsK.symm hKX
  by_cases hxK : K.map (MulAut.conj x).toMonoidHom = T
  · exact false_of_swap148 hS hY hB hc φT φK hTK hAT hAK hnat hxT hxK hnoPt
  · exact false_of_three_cycle148 hS hY φT φK hKc hTK hAT hAK hnat hxT hxK

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
