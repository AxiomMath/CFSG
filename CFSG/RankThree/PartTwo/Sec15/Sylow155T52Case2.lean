module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155T51
public import CFSG.RankThree.PartTwo.Sec13.Item133Mono
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import Certificates.Certificate8171
public import Certificates.Certificate8172
import CFSG.RankThree.PartTwo.Sec15.Sylow155T52
import CFSG.RankThree.PartTwo.Sec15.Sylow155T52Coord
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStd
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec14.Concl143HJ
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Center
public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Con
public import CFSG.RankThree.PartTwo.Sec15.Sylow155NO
public import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinB
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sylow155T52

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_of_conj_mem {E : Subgroup G} {g : G}
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective
    (MulAut.conj g).injective).ge
  rintro _ ⟨e, he, rfl⟩
  exact hg e he

theorem exists_coords_of_case2
    {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hirrW : Sec21.IsIrreducibleOn (wStar A))
    {φ : wStar A →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)} (hφ : Function.Injective φ)
    (ψ : Sec4.autIn L A ≃* Multiplicative (ZMod 4)) :
    Nat.card (wStar A) ∣ 48 ∧ ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (wStar A).map (KFacts.glHom f) ≤ linePermuting Lstd ∧
      monomialDetOne Lstd ≤ (wStar A).map (KFacts.glHom f) ∧
      ∀ j : Fin 3, Subgroup.zpowers (coordPt f j) ∈ omegaA A := by
  have hAe := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_equiv ψ
    (m := Multiplicative.ofAdd (1 : ZMod 4)) (by decide) (by decide)
  have hτW : τ ∈ wStar A := autIn_mono le_top hτ
  have hW48 : Nat.card (wStar A) ∣ 48 := by
    have h1 := Subgroup.card_subgroup_dvd_card φ.range
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_prod,
      Sec13.card_multiplicative_zmod, Nat.card_perm, Nat.card_fin] at h1
    exact h1
  have hord : orderOf (⟨τ, hτW⟩ : wStar A) = 4 := by
    have h4' : (⟨τ, hτW⟩ : wStar A) ^ 4 = 1 := Subtype.ext h4
    have h2' : (⟨τ, hτW⟩ : wStar A) ^ 2 ≠ 1 := fun h => h2 (congrArg Subtype.val h)
    have hdvd := orderOf_dvd_of_pow_eq_one h4'
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf (⟨τ, hτW⟩ : wStar A)
    · exact absurd (orderOf_eq_zero_iff'.mp h 4 (by norm_num)) (by simpa using h4')
    · exact absurd (by rw [← orderOf_dvd_iff_pow_eq_one, h]; norm_num) h2'
    · exact absurd (by rw [← orderOf_dvd_iff_pow_eq_one, h]) h2'
    · norm_num at hdvd
    · rfl
  have hW4 : 4 ∣ Nat.card (wStar A) := hord ▸ orderOf_dvd_natCard _
  have hW13 : ¬ 13 ∣ Nat.card (wStar A) := fun h => absurd (h.trans hW48) (by norm_num)
  obtain ⟨f, hle, hG0⟩ := exists_std_coords hAe h27 hirrW hW4 hW13
  set M := KFacts.glHom f τ with hMdef
  have hMG : M ∈ (wStar A).map (KFacts.glHom f) := ⟨τ, hτW, rfl⟩
  have hM4 : M ^ 4 = 1 := by rw [hMdef, ← map_pow, h4, map_one]
  have hM2 : M ^ 2 ≠ 1 := fun h =>
    h2 (KFacts.glHom_injective f (by rw [map_pow, ← hMdef, h, map_one]))
  set vc := Sec12.coordVec f ⟨c, hcA⟩ with hvcdef
  have hvc0 : vc ≠ 0 := Sec12.coordVec_ne_zero f (fun h => hD.ne_one (congrArg Subtype.val h))
  have hMvc : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ vc = vc := by
    rw [hMdef, hvcdef, glHom_mulVec_coordVec, autIn_fix hD.le_centralizer hcA hτ]
  obtain ⟨i, hi⟩ := mem_Lstd_of_order_four (hle hMG) hM4 hM2 hvc0
    (by rw [hMvc]; exact Submodule.mem_span_singleton_self _)
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hi
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact hvc0 hμ.symm
  have hMi : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = Pi.single i 1 := by
    have h := hMvc
    rw [← hμ, Matrix.mulVec_smul] at h
    exact smul_right_injective _ hμ0 h
  have hN0 : monomialDetOne Lstd ≤ (wStar A).map (KFacts.glHom f) :=
    N0std_le_of hle hG0 hMG hM4 hM2 hMi
  refine ⟨hW48, f, hle, hN0, fun j => ?_⟩
  obtain ⟨r, hr, hrij⟩ := exists_mem_N0std_mulVec i j
  obtain ⟨σ, hσ, hσr⟩ := hN0 hr
  obtain ⟨w, hw, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  have hne : A.normalizerMonoidHom ⟨w, hw⟩ ⟨c, hcA⟩ ≠ 1 := by
    intro h
    apply hD.ne_one
    have := congrArg Subtype.val h
    rw [normalizerMonoidHom_apply_val] at this
    have h1 : c = w⁻¹ * (w * c * w⁻¹) * w := by group
    rw [h1]
    change w⁻¹ * (w * c * w⁻¹) * w = 1
    rw [show w * c * w⁻¹ = 1 from this]
    group
  have hx := zpowers_eq_coordPt f hne (j := j) (by
    rw [← glHom_mulVec_coordVec, hσr, ← hvcdef, ← hμ, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ hrij)
  rw [← hx]
  have hmem := (map_conj_mem_omegaA_iff hw).mpr hD.zpowers_mem_omegaA
  rw [MonoidHom.map_zpowers] at hmem
  exact hmem

theorem isPConstrained_of_monomial (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (hT : TheoremFourHyp G) (hS : partTwoS G = ∅) {A : Subgroup G} (hA : A ∈ partTwoF G)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (hle : (wStar A).map (KFacts.glHom f) ≤ linePermuting Lstd)
    (hN0 : monomialDetOne Lstd ≤ (wStar A).map (KFacts.glHom f))
    (hW48 : Nat.card (wStar A) ∣ 48)
    (hΩ : ∀ j : Fin 3, Subgroup.zpowers (coordPt f j) ∈ omegaA A)
    {B : Subgroup G} (hB : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) :
    CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  have hFE := (hT.partTwoF_eq_partTwoE hS).1
  have hAE : A ∈ partTwoE G := hFE ▸ hA
  have hA27 : Nat.card A = 27 := hAE.2.1
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hB9 : Nat.card B = 9 := by
    have h := hB.2
    rw [hA27] at h
    omega
  obtain ⟨K, hKA, -, hBK, hKinv, hKB⟩ :=
    exists_invariant_component_point h1 h2 h43 hin hT hS hA hB.1 hB9 hcon
  have hpt : ∀ j : Fin 3, (f (Multiplicative.ofAdd (Pi.single j 1)) : G) ∉ B := by
    intro j hj
    refine hfree _ hj (fun h => ?_) (hΩ j)
    have h' := congrArg (Sec12.coordVec f)
      (Subtype.ext h : f (Multiplicative.ofAdd (Pi.single j 1)) = 1)
    simp [Sec12.coordVec] at h'
  obtain ⟨b₁, b₂, hb₁B, hb₂B, hb₁1, hb₂b₁, R, hR, hR₁, hR₂, hall⟩ :=
    exists_raw_plane hAab hA27 f hB.1 hB9 hpt
  have hb₁1' : (b₁ : G) ≠ 1 := fun h => hb₁1 (Subtype.ext h)
  have hb₁3 : (b₁ : G) ^ 3 = 1 := hAab.2 _ b₁.2
  have hb₂3 : (b₂ : G) ^ 3 = 1 := hAab.2 _ b₂.2
  have hb₂b₁' : (b₂ : G) ∉ Subgroup.zpowers (b₁ : G) := by
    intro h
    apply hb₂b₁
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  have hE1 : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (b₁ : G)) :=
    hAab.mono (Subgroup.zpowers_le.mpr b₁.2)
  obtain ⟨-, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE1 hb₂b₁' hb₂3
    (fun x hx => congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨x, Subgroup.zpowers_le.mpr b₁.2 hx⟩ b₂))
  have hBsup : Subgroup.zpowers (b₁ : G) ⊔ Subgroup.zpowers (b₂ : G) = B := by
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hb₁B) (Subgroup.zpowers_le.mpr hb₂B)) ?_
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime hb₁3 hb₁1', hB9]
  obtain ⟨r, hr, hrR⟩ := exists_mem_N0std_of_raw hR
  obtain ⟨σ, hσ, hσr⟩ := hN0 hr
  obtain ⟨w, hw, -, hσw⟩ := Sec4.mem_autIn_iff.mp hσ
  have hσv : ∀ x : A, ofVec (Sec12.coordVec f (σ x)) = rmv R (ofVec (Sec12.coordVec f x)) := by
    intro x
    rw [← glHom_mulVec_coordVec f σ x, hσr, ofVec_mulVec, hrR]
  have hσG : ∀ x : A, ((σ x : A) : G) = w * x * w⁻¹ := by
    intro x
    rw [← hσw, normalizerMonoidHom_apply_val]
  have hσb₁ : ((σ b₁ : A) : G) ∈ B := by
    obtain ⟨α, β, hαβ⟩ := exists_of_inSpanTwo hR₁
    exact mem_of_coordVec_eq_two f hb₁B hb₂B (by rw [hσv]; exact hαβ)
  have hσb₂ : ((σ b₂ : A) : G) ∈ B := by
    obtain ⟨α, β, hαβ⟩ := exists_of_inSpanTwo hR₂
    exact mem_of_coordVec_eq_two f hb₁B hb₂B (by rw [hσv]; exact hαβ)
  have hwB : w ∈ Subgroup.normalizer (B : Set G) := by
    have hle' : Subgroup.zpowers (b₁ : G) ⊔ Subgroup.zpowers (b₂ : G) ≤
        B.comap (MulAut.conj w).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · show w * (b₁ : G) * w⁻¹ ∈ B
        rw [← hσG]
        exact hσb₁
      · show w * (b₂ : G) * w⁻¹ ∈ B
        rw [← hσG]
        exact hσb₂
    rw [hBsup] at hle'
    exact mem_normalizer_of_conj_mem fun e he => hle' he
  have hwK : ∀ x ∈ K, w * x * w⁻¹ ∈ K := fun x hx => by
    rw [← hKinv w hw hwB]
    exact ⟨x, hx, rfl⟩
  have hKB' : K ≤ B := by
    intro k hk
    by_contra hkB
    set κ : A := ⟨k, hKA hk⟩
    rcases hall (ofVec (Sec12.coordVec f κ)) (mem_allV3 _) with h | ⟨h₁, h₂⟩
    · obtain ⟨α, β, hαβ⟩ := exists_of_inSpanTwo h
      exact hkB (mem_of_coordVec_eq_two f hb₁B hb₂B hαβ)
    · apply hBK
      have hκ1 : ((σ κ : A) : G) ∈ K := by
        rw [hσG]
        exact hwK k hk
      have hκ2 : ((σ (σ κ) : A) : G) ∈ K := by
        rw [hσG]
        exact hwK _ hκ1
      rw [← hBsup]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · obtain ⟨α, β, γ, h⟩ := exists_of_inSpanThree h₁
        exact mem_of_coordVec_eq_three f (show (κ : G) ∈ K from hk) hκ1 hκ2
          (by rw [hσv (σ κ), hσv κ]; exact h)
      · obtain ⟨α, β, γ, h⟩ := exists_of_inSpanThree h₂
        exact mem_of_coordVec_eq_three f (show (κ : G) ∈ K from hk) hκ1 hκ2
          (by rw [hσv (σ κ), hσv κ]; exact h)
  obtain ⟨d, hdB, hdA, ⟨k, hk⟩, a, haA, hda⟩ := hKB hKB'
  set τ : MulAut A := A.normalizerMonoidHom ⟨d, hdA⟩ with hτdef
  have hτW : τ ∈ wStar A := Sec4.mem_autIn_iff.mpr ⟨d, hdA, Subgroup.mem_top d, rfl⟩
  have hτ3 : τ ^ 3 = 1 := by
    have hτk : τ ^ 3 ^ k = 1 := by
      have hd : (⟨d, hdA⟩ : Subgroup.normalizer (A : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hk)
      rw [hτdef, ← map_pow, hd, map_one]
    have hk' : (⟨τ, hτW⟩ : wStar A) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hτk)
    have hdvd : orderOf (⟨τ, hτW⟩ : wStar A) ∣ 3 := by
      obtain ⟨j, -, hjeq⟩ :=
        (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
      have h48 := (orderOf_dvd_natCard (⟨τ, hτW⟩ : wStar A)).trans hW48
      rw [hjeq] at h48 ⊢
      have hj1 : j ≤ 1 := by
        by_contra hj1
        push Not at hj1
        have h9 : 3 ^ 2 ∣ 48 := (pow_dvd_pow 3 hj1).trans h48
        norm_num at h9
      simpa using pow_dvd_pow 3 hj1
    have h3 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa using congrArg Subtype.val h3
  set g : GL (Fin 3) (ZMod 3) := KFacts.glHom f τ with hg
  have hgL : g ∈ linePermuting Lstd := hle ⟨τ, hτW, rfl⟩
  have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, hτ3, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    apply hda
    have hτ1 : τ = 1 := KFacts.glHom_injective f (by rw [← hg, h, map_one])
    have h' := congrArg (fun φ : MulAut A => ((φ ⟨a, haA⟩ : A) : G)) hτ1
    simp only [MulAut.one_apply] at h'
    rw [hτdef, normalizerMonoidHom_apply_val] at h'
    exact h'
  have hfix : ∀ x : A, (x : G) ∈ B →
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Sec12.coordVec f x = Sec12.coordVec f x := by
    intro x hx
    rw [hg, glHom_mulVec_coordVec]
    congr 1
    apply Subtype.ext
    rw [hτdef, normalizerMonoidHom_apply_val]
    have hc := Subgroup.mem_centralizer_iff.mp hdB (x : G) hx
    calc d * (x : G) * d⁻¹ = (x : G) * d * d⁻¹ := by rw [hc]
      _ = x := by group
  have hspan := mem_span_of_order_three hgL hg3 hg1 (Sec12.coordVec_ne_zero f hb₁1)
    (hfix b₁ hb₁B) (hfix b₂ hb₂B)
  exact hb₂b₁ ((KFacts.coordVec_mem_span_iff f).mp hspan)

end Sylow155T52

variable {G : Type} [Group G] [Finite G]

theorem step155BalCompW_of_not_le_normalizer
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46) (h131 : Item131) (h132 : Item132)
    (hspor : SporadicModels131) (hSLC : SLTwoCenter) (hSLT : NotSLTwoOfHypT)
    {A L : Subgroup G} {c : G}
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hpgl : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hm12 : IsEmpty (lBarA c L A ≃*
      Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12))
    (hj2 : IsEmpty (lBarA c L A ≃*
      Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) :
    Step155BalCompW A c L := by
  intro h X K Y M T P _ _ _ _ _ _ _ g _ _ _ B hB hfree hcon
  exfalso
  apply hcon
  have hD : Sec13Data G A c L := h.toSec13Data
  have hST := h.hypS_or_hypT
  have hcL := not_mem_of_hyp h131 hspor hSLC hSLT hD hST hW
  rcases cases131 h131 hspor hSLC hD with ⟨-, h9, -, hcase⟩ | ⟨-, -, hMJ, -⟩ |
      ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · have hAe := hD.isElemAbelian
    have hcB : c ∉ A ⊓ L := fun h => hcL h.2
    have hAa := eq_sup_of_card_nine hD h9 hcB
    obtain ⟨τ, hτ, h4, h2'⟩ := exists_order_four_of_cases hcase
    obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2'
    have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
    have hirrL := isIrreducibleOn_of_order_four hBe h9 hρ hρ4 hρ2
    rcases h132 G A c L hD hST c hD.mem_A hD.ne_one L hD.mem_thetaComponentsAt hAa hcB hirrL with
      ⟨hWB, -, -, -, hΩc, -, hΩ9, -, -⟩ | hWc | ⟨hirrW, -, φ, hφ⟩
    ·
      exact Sylow155T51.isPConstrained_of_case3 h1 h2 h43 hin h.toTheoremFourHyp h.partTwoS_eq
        h.mem_partTwoF h.zpowers_mem_omegaA hirrL hWB hΩc hΩ9 h9 hB hfree
    · exact absurd hWc hW
    · have hLW : Sec4.autIn L A ≤ wStar A := autIn_mono le_top
      rcases h131 G A c L hD with ⟨-, he | he⟩ | ⟨hPGL, -, -⟩ | ⟨-, hψ⟩ | ⟨-, he⟩ |
          ⟨hM, -⟩ | ⟨hJ, -⟩ | ⟨h7, -, -⟩
      · obtain ⟨e⟩ := he
        exact (false_of_quaternion hφ (Q := (Sec4.autIn L A).subgroupOf (wStar A))
          ((Subgroup.subgroupOfEquivOfLe hLW).trans e)).elim
      · obtain ⟨e⟩ := he
        exact (false_of_SL23 hφ (Q := (Sec4.autIn L A).subgroupOf (wStar A))
          ((Subgroup.subgroupOfEquivOfLe hLW).trans e)).elim
      · exact absurd hPGL hpgl
      ·
        obtain ⟨ψ⟩ := hψ
        obtain ⟨hW48, f, hle, hN0, hΩ⟩ := Sylow155T52.exists_coords_of_case2 hD hirrW hφ ψ
        exact Sylow155T52.isPConstrained_of_monomial h1 h2 h43 hin h.toTheoremFourHyp
          h.partTwoS_eq h.mem_partTwoF f hle hN0 hW48 hΩ hB hfree
      · obtain ⟨e⟩ := he
        exact (false_of_quaternion hφ (Q := (Sec4.autIn L A).subgroupOf (wStar A))
          ((Subgroup.subgroupOfEquivOfLe hLW).trans e)).elim
      · exact (hm12.false hM.some).elim
      · exact (hj2.false hJ.some).elim
      · exfalso
        rcases h7 with hSL | ⟨hHeis, -⟩
        · exact hcL (mem_of_isSLThreePiTwo hSLC hD hSL)
        · exact hcL (mem_of_isHeisCentral hD hHeis)
  · rcases hMJ with hM | hJ
    · exact (hm12.false hM.some).elim
    · exact (hj2.false hJ.some).elim
  · exact absurd hPGL hpgl
  · exact absurd hcL' hcL

end CFSG.RankThree.PartTwo.Sec15
