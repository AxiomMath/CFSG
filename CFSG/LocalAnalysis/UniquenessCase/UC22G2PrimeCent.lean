module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofLongCent
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

variable {K : Type} [Field K]

private theorem uc22g2_factorization_prime_sl2 [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) :
    (Nat.card (SL2 K)).factorization r = (Nat.card K - 1).factorization r := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hsq : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have h0 : Nat.card K ≠ 0 := by omega
  have h1 : Nat.card K - 1 ≠ 0 := by omega
  have h2 : Nat.card K + 1 ≠ 0 := by omega
  rw [hsq, Nat.factorization_mul h0 (mul_ne_zero h1 h2), Nat.factorization_mul h1 h2]
  have hn0 : ¬ r ∣ Nat.card K := by
    intro hdvd
    have h1' : r ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hdvd hrq
    have h4 : Nat.card K - (Nat.card K - 1) = 1 :=
      Nat.sub_sub_self (by omega : 1 ≤ Nat.card K)
    rw [h4] at h1'
    exact hr.not_dvd_one h1'
  have hn2 : ¬ r ∣ Nat.card K + 1 := by
    intro hdvd
    have h2' : r ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hdvd hrq
    have h4 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [hm, show m + 1 - 1 = m from Nat.add_sub_cancel m 1]
      exact Nat.add_sub_cancel_left m 2
    rw [h4] at h2'
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2'
    have hr2le : 2 ≤ r := hr.two_le
    omega
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hn0,
    Nat.factorization_eq_zero_of_not_dvd hn2, zero_add, add_zero]

theorem uc22g2_exists_conj_HSL_of_prime [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) (A : SL2 K) (hA : ∃ k : ℕ, A ^ r ^ k = 1) :
    ∃ (P : SL2 K) (t : Kˣ), P * A * P⁻¹ = HSL t := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  set D := (HSLHom K).range with hD
  have hDcard : Nat.card D = Nat.card K - 1 := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective (f := HSLHom K) HSLHom_injective).toEquiv,
      Nat.card_units]
  obtain ⟨P₀⟩ : Nonempty (Sylow r D) := inferInstance
  let Q : Sylow r (SL2 K) := Sylow.ofCard ((P₀ : Subgroup D).map D.subtype) (by
    rw [Subgroup.card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity P₀,
      hDcard, uc22g2_factorization_prime_sl2 hr hr2 hrq])
  have hE : IsPGroup r (Subgroup.zpowers A) := by
    obtain ⟨k, hk⟩ := hA
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨y, hy⟩ := exists_conj_le_sylow' Q _ hE
  have hmem : y * A * y⁻¹ ∈ D := by
    have h1' : y * A * y⁻¹ ∈ (Subgroup.zpowers A).map (MulAut.conj y).toMonoidHom :=
      ⟨A, Subgroup.mem_zpowers A, rfl⟩
    have h2' := hy h1'
    rw [Sylow.coe_ofCard] at h2'
    obtain ⟨d, -, hd⟩ := h2'
    rw [← hd]
    exact d.2
  obtain ⟨t, ht⟩ := hmem
  exact ⟨y, t, ht.symm⟩

private theorem uc22g2_prime_dvd_sq_sub_one [Finite K] {r : ℕ} (hr : r.Prime)
    (hrK : r ≠ ringChar K) {A : SL2 K} (hAr : A ^ r = 1) (hA1 : A ≠ 1) :
    r ∣ Nat.card K ^ 2 - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hord : orderOf A = r := orderOf_eq_prime hAr hA1
  have hdvd : r ∣ Nat.card (SL2 K) := by
    have h := orderOf_dvd_natCard A
    rwa [hord] at h
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at hdvd
  have hnot : ¬ r ∣ Nat.card K := by
    intro hdvdK
    let := Fintype.ofFinite K
    have : CharP K (ringChar K) := ringChar.charP K
    have hprime : (ringChar K).Prime :=
      (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
        (CharP.ringChar_ne_zero_of_finite K)
    obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hcard] at hdvdK
    exact hrK ((Nat.prime_dvd_prime_iff_eq hr hprime).mp (hr.dvd_of_dvd_pow hdvdK))
  exact ((hr.dvd_mul).mp hdvd).resolve_left hnot

section Cent


theorem uc22g2_long_prime_comm_split [Finite K] {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ Nat.card K - 1) {y : adjointGroup .G2 K} (hyM : y ∈ g2LongSL2 K)
    (hyr : y ^ r = 1) (hy1 : y ≠ 1) :
    ∀ x ∈ centralizer ({y} : Set (adjointGroup .G2 K)),
      ∀ w ∈ centralizer ({y} : Set (adjointGroup .G2 K)), x * w * x⁻¹ * w⁻¹ ∈ g2ShortSL2 K := by
  obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp hyM
  have hinj := simpleRootSL2_injective_g2 (K := K) g2ia
  have hAr : A ^ r = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hyr)
  obtain ⟨P, t, hPt⟩ :=
    uc22g2_exists_conj_HSL_of_prime hr (by omega) hrq A ⟨1, by simpa using hAr⟩
  have : Fact r.Prime := ⟨hr⟩
  have htr : orderOf t = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := K)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hAr, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hy1
      have h1 : A = 1 := by
        have h1' : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom K))
        simpa using h1'
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  have h5t : 5 ≤ orderOf t := by omega
  set m : adjointGroup .G2 K :=
    ⟨simpleRootSL2 .G2 K g2ia P, simpleRootSL2_mem_adjointGroup _ P⟩
  have hmM : m ∈ g2LongSL2 K := mem_g2LongSL2_iff.mpr ⟨P, rfl⟩
  have hmz : ((m * y * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (fun j => t ^ Tag.G2.cartan g2ia j) := by
    rw [coe_conj, ← hA, ← rhoA_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  have hcen : ∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
        torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
    intro x hx
    rw [← toralCentralizer_torusA_of_five_le (ζ := t) h5t, ← mem_centralizer_iff_toral hmz]
    exact conj_mem_centralizer hx
  have hmS : ∀ s ∈ g2ShortSL2 K, m * s = s * m := fun s hs =>
    (g2Short_commute_g2Long hs hmM).symm
  intro x hx w hw
  have h := commutator_mem_of_mem_sup torus_comm
    (torusGroup_le_normalizer_rootPair (K := K) isRoot_g2δ) (hcen x hx) (hcen w hw)
  refine mem_of_conj_mem hmS ?_
  change ((m * (x * w * x⁻¹ * w⁻¹) * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
    rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)
  convert h using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem uc22g2_short_prime_comm_split [Finite K] {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ Nat.card K - 1) {y : adjointGroup .G2 K} (hyS : y ∈ g2ShortSL2 K)
    (hyr : y ^ r = 1) (hy1 : y ≠ 1) :
    ∀ x ∈ centralizer ({y} : Set (adjointGroup .G2 K)),
      ∀ w ∈ centralizer ({y} : Set (adjointGroup .G2 K)), x * w * x⁻¹ * w⁻¹ ∈ g2LongSL2 K := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hyS
  have hinj := rhoV_injective (K := K)
  have hAr : A ^ r = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hyr)
  have hA1 : A ≠ 1 := fun h => hy1 (by
    apply Subtype.ext
    rw [← hA, h, map_one]
    rfl)
  obtain ⟨P, t, hPt⟩ :=
    uc22g2_exists_conj_HSL_of_prime hr (by omega) hrq A ⟨1, by simpa using hAr⟩
  have hHSLr : HSL t ^ r = 1 := by
    rw [← hPt, conj_pow, hAr, mul_one, mul_inv_cancel]
  have hHSL1 : HSL t ≠ 1 := by
    intro h1
    apply hA1
    have h1' : P * A * P⁻¹ = 1 := by rw [hPt, h1]
    simpa using h1'
  have : Fact r.Prime := ⟨hr⟩
  have htr : orderOf t = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := K)
      rw [map_pow, map_one, HSLHom_apply, hHSLr]
    · rintro rfl
      exact hHSL1 (map_one (HSLHom K))
  have h5t : 5 ≤ orderOf t := by omega
  set m : adjointGroup .G2 K := ⟨rhoV K P, by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _)
      (simpleRootSL2_mem_adjointGroup _ P)) (inv_mem (canonicalRep_mem_adjointGroup _ K _))⟩
  have hmS : m ∈ g2ShortSL2 K := mem_g2ShortSL2_iff.mpr ⟨P, rfl⟩
  have hmy : ((m * y * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [coe_conj, ← hA, ← rhoV_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  have hcen : ∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      ((m * x * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
        torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) := by
    intro x hx
    rw [← toralCentralizer_shortNine (le_trans (by norm_num) h5t),
      ← mem_centralizer_iff_toral hmy]
    exact conj_mem_centralizer hx
  have hmM : ∀ s ∈ g2LongSL2 K, m * s = s * m := fun s hs => g2Short_commute_g2Long hmS hs
  intro x hx w hw
  have h := commutator_mem_of_mem_sup torus_comm
    (torusGroup_le_normalizer_rootPair (K := K) (isRoot_single .G2 g2l)) (hcen x hx) (hcen w hw)
  refine mem_of_conj_mem hmM ?_
  change ((m * (x * w * x⁻¹ * w⁻¹) * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
    rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)
  convert h using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem uc22g2_long_prime_comm [Finite K] {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrK : r ≠ ringChar K) {y : adjointGroup .G2 K} (hyM : y ∈ g2LongSL2 K) (hyr : y ^ r = 1)
    (hy1 : y ≠ 1) :
    ∀ x ∈ centralizer ({y} : Set (adjointGroup .G2 K)),
      ∀ w ∈ centralizer ({y} : Set (adjointGroup .G2 K)), x * w * x⁻¹ * w⁻¹ ∈ g2ShortSL2 K := by
  obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp hyM
  have hinj := simpleRootSL2_injective_g2 (K := K) g2ia
  have hAr : A ^ r = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hyr)
  have hA1 : A ≠ 1 := by
    rintro rfl
    apply hy1
    apply Subtype.ext
    rw [← hA, map_one]
    rfl
  have hrq : r ∣ Nat.card K ^ 2 - 1 := uc22g2_prime_dvd_sq_sub_one hr hrK hAr hA1
  obtain ⟨K₂, _, _, _, σ, hdeg, hσ⟩ := exists_quadratic_ext' K
  obtain ⟨-, -, hfix⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have hcard := natCard_quadratic (K := K) (K₂ := K₂) hdeg
  have hrq₂ : r ∣ Nat.card K₂ - 1 := by rw [hcard]; exact hrq
  set ι := bcG2 K K₂
  have hιyr : ι y ^ r = 1 := by rw [← map_pow, hyr, map_one]
  have hιy1 : ι y ≠ 1 := fun h => hy1 (bcG2_injective (h.trans (map_one ι).symm))
  have hsplit :=
    uc22g2_long_prime_comm_split hr hr5 hrq₂ (bcG2_mem_g2LongSL2 hyM) hιyr hιy1
  intro x hx w hw
  refine mem_g2ShortSL2_of_bcG2 σ hfix ?_
  have := hsplit _ (map_mem_centralizer ι hx) _ (map_mem_centralizer ι hw)
  simpa only [map_mul, map_inv] using this

theorem uc22g2_short_prime_comm [Finite K] {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrK : r ≠ ringChar K) {y : adjointGroup .G2 K} (hyS : y ∈ g2ShortSL2 K) (hyr : y ^ r = 1)
    (hy1 : y ≠ 1) :
    ∀ x ∈ centralizer ({y} : Set (adjointGroup .G2 K)),
      ∀ w ∈ centralizer ({y} : Set (adjointGroup .G2 K)), x * w * x⁻¹ * w⁻¹ ∈ g2LongSL2 K := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hyS
  have hinj := rhoV_injective (K := K)
  have hAr : A ^ r = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hyr)
  have hA1 : A ≠ 1 := by
    rintro rfl
    apply hy1
    apply Subtype.ext
    rw [← hA, map_one]
    rfl
  have hrq : r ∣ Nat.card K ^ 2 - 1 := uc22g2_prime_dvd_sq_sub_one hr hrK hAr hA1
  obtain ⟨K₂, _, _, _, σ, hdeg, hσ⟩ := exists_quadratic_ext' K
  obtain ⟨-, -, hfix⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have hcard := natCard_quadratic (K := K) (K₂ := K₂) hdeg
  have hrq₂ : r ∣ Nat.card K₂ - 1 := by rw [hcard]; exact hrq
  set ι := bcG2 K K₂
  have hιyr : ι y ^ r = 1 := by rw [← map_pow, hyr, map_one]
  have hιy1 : ι y ≠ 1 := fun h => hy1 (bcG2_injective (h.trans (map_one ι).symm))
  have hsplit :=
    uc22g2_short_prime_comm_split hr hr5 hrq₂ (bcG2_mem_g2ShortSL2 hyS) hιyr hιy1
  intro x hx w hw
  refine mem_g2LongSL2_of_bcG2 σ hfix ?_
  have := hsplit _ (map_mem_centralizer ι hx) _ (map_mem_centralizer ι hw)
  simpa only [map_mul, map_inv] using this

theorem uc22g2_centralizer_commutator_long [Finite K] (hK6 : 6 ≤ Nat.card K) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrK : r ≠ ringChar K) {y : adjointGroup .G2 K}
    (hyM : y ∈ g2LongSL2 K) (hyr : y ^ r = 1) (hy1 : y ≠ 1) :
    centralizer ((⁅centralizer ({y} : Set (adjointGroup .G2 K)),
      centralizer ({y} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K)) = g2LongSL2 K := by
  have hK4 : 4 ≤ Nat.card K := by omega
  have hK5 : 5 ≤ Nat.card K := by omega
  have hScomm : ⁅g2ShortSL2 K, g2ShortSL2 K⁆ = g2ShortSL2 K :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_g2ShortSL2 hK4).1
  have hSC : g2ShortSL2 K ≤ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact g2Short_commute_g2Long hs hyM
  have hCcomm : ⁅Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      Subgroup.centralizer ({y} : Set (adjointGroup .G2 K))⁆ = g2ShortSL2 K := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx w hw
      exact uc22g2_long_prime_comm hr hr5 hrK hyM hyr hy1 x hx w hw
    · calc g2ShortSL2 K = ⁅g2ShortSL2 K, g2ShortSL2 K⁆ := hScomm.symm
        _ ≤ ⁅Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
              Subgroup.centralizer ({y} : Set (adjointGroup .G2 K))⁆ :=
            Subgroup.commutator_mono hSC hSC
  have hCentS : Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) =
      g2LongSL2 K := by
    apply le_antisymm
    · intro x hx
      exact mem_g2LongSL2_of_mem_centralizer hK5 hx
    · intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact g2Short_commute_g2Long hs hm
  rw [hCcomm, hCentS]

theorem uc22g2_centralizer_commutator_short [Finite K] (hK6 : 6 ≤ Nat.card K) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrK : r ≠ ringChar K) {y : adjointGroup .G2 K}
    (hyS : y ∈ g2ShortSL2 K) (hyr : y ^ r = 1) (hy1 : y ≠ 1) :
    centralizer ((⁅centralizer ({y} : Set (adjointGroup .G2 K)),
      centralizer ({y} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K)) = g2ShortSL2 K := by
  have hK4 : 4 ≤ Nat.card K := by omega
  have hMcomm : ⁅g2LongSL2 K, g2LongSL2 K⁆ = g2LongSL2 K :=
    Subgroup.isPerfect_iff.mp (isPerfect_g2LongSL2 hK4)
  have hMC : g2LongSL2 K ≤ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (g2Short_commute_g2Long hyS hm).symm
  have hCcomm : ⁅Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
      Subgroup.centralizer ({y} : Set (adjointGroup .G2 K))⁆ = g2LongSL2 K := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx w hw
      exact uc22g2_short_prime_comm hr hr5 hrK hyS hyr hy1 x hx w hw
    · calc g2LongSL2 K = ⁅g2LongSL2 K, g2LongSL2 K⁆ := hMcomm.symm
        _ ≤ ⁅Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
              Subgroup.centralizer ({y} : Set (adjointGroup .G2 K))⁆ :=
            Subgroup.commutator_mono hMC hMC
  have hCentM : Subgroup.centralizer (g2LongSL2 K : Set (adjointGroup .G2 K)) =
      g2ShortSL2 K := by
    apply le_antisymm
    · intro x hx
      exact mem_g2ShortSL2_of_mem_centralizer hK6 hx
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (g2Short_commute_g2Long hs hm).symm
  rw [hCcomm, hCentM]

end Cent

end CFSG.LocalAnalysis.UniquenessCase.UC22
