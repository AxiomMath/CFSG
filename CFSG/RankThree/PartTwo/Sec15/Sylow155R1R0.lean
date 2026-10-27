module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_inner_aux {A M C : Subgroup G}
    {Y : Subgroup (↥C ⧸ CFSG.pPrimeCore 3 ↥C)} [hYn : Y.Normal] (hA : Late.IsE27 A)
    (h142 : Concl142 A (lB A)) (hAM : A ≤ M) {c : G} (hc : Subgroup.zpowers c ∈ omegaA A)
    (hcY : c ∈ (Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).map C.subtype)
    {g : G} (hgC : g ∈ C)
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G))
    (hno : ¬ ∃ w : ↥C, (w : G) ∈ CFSG.Open.pCoreOf 2 M ∧ ∃ y ∈ Y, y ≠ 1 ∧ ∀ z ∈ Y,
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) w * z *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) w)⁻¹ = y * z * y⁻¹) :
    ⁅CFSG.Open.pCoreOf 2 M ⊓ C, Subgroup.zpowers g⁆ ≤
      (CFSG.pPrimeCore 3 ↥C).map C.subtype := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hc).1
  have hcM : c ∈ M := hAM hcA
  obtain ⟨c', hc'Y, hc'⟩ := hcY
  have hc'val : (c' : G) = c := hc'
  have hcC : c ∈ C := hc'val ▸ c'.2
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  set W : Subgroup G := CFSG.Open.pCoreOf 2 M ⊓ C
  have hW2 : IsPGroup 2 W := hO2.to_le inf_le_left
  have hWconj : ∀ m : G, m ∈ M → m ∈ C → ∀ q ∈ W, m * q * m⁻¹ ∈ W := by
    intro m hm hmC q hq
    obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.mp hq
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) q).mp hq1,
        C.mul_mem (C.mul_mem hmC hq2) (C.inv_mem hmC)⟩
  have hcomm : ∀ w : ↥C, (w : G) ∈ CFSG.Open.pCoreOf 2 M → π w * π c' = π c' * π w := by
    intro w hw
    set w₁ : ↥C := w * c' * w⁻¹ * c'⁻¹ with hw₁
    have hw₁M : (w₁ : G) ∈ CFSG.Open.pCoreOf 2 M := by
      have e : (w₁ : G) = (w : G) * (c * (w : G)⁻¹ * c⁻¹) := by
        simp [hw₁, hc'val, mul_assoc]
      rw [e]
      exact (CFSG.Open.pCoreOf 2 M).mul_mem hw
        ((Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hcM) _).mp
          ((CFSG.Open.pCoreOf 2 M).inv_mem hw))
    have hπw₁ : π w₁ ∈ Y := by
      have e : π w₁ = (π w * π c' * (π w)⁻¹) * (π c')⁻¹ := by
        simp [hw₁, mul_assoc]
      rw [e]
      exact Y.mul_mem (hYn.conj_mem _ hc'Y _) (Y.inv_mem hc'Y)
    have h1 : π w₁ = 1 := by
      by_contra hne
      exact hno ⟨w₁, hw₁M, π w₁, hπw₁, hne, fun z _ => rfl⟩
    have e : π w₁ = ⁅π w, π c'⁆ := by
      simp [hw₁, commutatorElement_def]
    rw [e, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  let φ : ↥W →* ↥C ⧸ CFSG.pPrimeCore 3 ↥C := π.comp (Subgroup.inclusion inf_le_right)
  have hnorm : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.mem_normalizer_fintype fun n hn => hWconj c hcM hcC n hn)
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    intro h3
    have h := h3.trans (Subgroup.card_subgroup_dvd_card φ.ker)
    rw [hk] at h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have hpgroup : IsPGroup 3 (Subgroup.zpowers c) :=
    hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA)
  have hkey : ∀ (u : ↥C), (u : G) ∈ CFSG.Open.pCoreOf 2 M → ∀ k : ℤ,
      π (c' ^ k * u * (c' ^ k)⁻¹) = π u := by
    intro u hu k
    have hc : Commute (π c' ^ k) (π u) := Commute.zpow_left (hcomm u hu).symm k
    rw [map_mul, map_mul, map_inv, map_zpow]
    exact mul_inv_eq_iff_eq_mul.mpr hc.eq
  have htriv : ∀ (a : ↥(Subgroup.zpowers c)) (x : ↥W),
      φ ⟨(a : G) * x * (a : G)⁻¹, Subgroup.le_normalizer_iff.mp hnorm a a.2 x x.2⟩ = φ x := by
    rintro ⟨a, ha⟩ ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h := hkey ⟨x, hx.2⟩ hx.1 k
    refine Eq.trans (congrArg π (Subtype.ext ?_)) h
    simp [hc'val]
  open CFSG.RankThreeEvenClassification.Helpers in
  have hfix := fun w : ↥W =>
    exists_centralizer_with_same_image_of_trivial_quotient_action 3 Nat.prime_three
      (Subgroup.zpowers c) W hpgroup hnorm φ hker htriv w
  have hV3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    intro h3
    rw [hk] at h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hQ : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) :=
    Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 hc
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hV3) hAV
  have hQg : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G) ≤
      delta A (lB A) (CFSG.Open.pCoreOf 2 M) := le_delta hQ inf_le_left
  rw [Subgroup.commutator_le]
  intro h hh x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨hhV, hhC⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨w₀, hw₀c, hw₀⟩ := hfix ⟨h, hh⟩
  let g' : ↥C := ⟨g, hgC⟩
  let h' : ↥C := ⟨h, hhC⟩
  let w₀' : ↥C := ⟨(w₀ : G), w₀.2.2⟩
  have hw₀Q : (w₀ : G) ∈ CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨w₀.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subgroup.mem_centralizer_iff.mp hw₀c z (Subgroup.mem_zpowers z)
  have hw₀g : (w₀ : G) * g = g * (w₀ : G) :=
    Subgroup.mem_centralizer_iff.mp hgZ (w₀ : G) (hQg hw₀Q)
  have hw₀g' : w₀' * g' = g' * w₀' := Subtype.ext hw₀g
  have hπh : π h' = π w₀' := hw₀.symm
  have h1 : π ⁅h', g' ^ k⁆ = 1 := by
    rw [map_commutatorElement, hπh, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (Commute.zpow_right hw₀g' k).eq, map_one]
  exact ⟨⁅h', g' ^ k⁆, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem res1_exists_inner {A : Subgroup G} {c : G} {L M : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hAM : A ≤ M)
    (h142 : Concl142 A (lB A)) (hY : Res1AtOf A c L M Yc) :
    ∃ w : ↥(Res1C A L), (w : G) ∈ CFSG.Open.pCoreOf 2 M ∧ ∃ y ∈ Yc, y ≠ 1 ∧ ∀ z ∈ Yc,
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w * z *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w)⁻¹ = y * z * y⁻¹ := by
  by_contra hno
  obtain ⟨hhyp, -, -, ⟨hYcomp, hcY, -⟩, g, hg, hgZ, -, hgnot⟩ := hY
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ (Subgroup.mem_inf.mp hg).1
  have hgC : g ∈ Res1C A L := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp hgA b (Subgroup.mem_inf.mp hb).1
  exact hgnot (exists_inner_aux (Late.isE27_of_mem_partTwoE hS.toSec13Data.mem_partTwoE) h142 hAM
    hS.zpowers_mem_omegaA hcY hgC hgZ hno)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
