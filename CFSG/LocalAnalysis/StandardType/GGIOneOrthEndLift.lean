module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperElt
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndElt
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp

theorem ggEndNodeIOneNonSmall_of_elt {p r : ℕ} {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    (hC : GGCenterPrime p R)
    (hinn : ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ (MulAut.conj : R →* MulAut R).range)
    (h : GGEndNodeIOneElt p r R) : GGEndNodeIOneNonSmall p r R (LargeEvenInnSet R) := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcard hAI hr h3 hcase hnone
  rcases hcase with hα | hδ
  swap
  · exact absurd hδ (not_ggDeltaAdm_of_prime (fun φ hφ _ => hφ) hC hψ hker hperf hA hAI)
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker hZ
  have hex : ∀ a : As, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    have hap : TableBUR.indAut ψ hψ hkc (a : MulAut L') ^ p = 1 := by
      rw [← map_pow, hAs.2 a a.2, map_one]
    obtain ⟨t, ht⟩ := hinn _ hap
    refine ⟨t, fun l => ?_⟩
    rw [← TableBUR.indAut_apply ψ hψ hkc, ← ht]
    rfl
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : As, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : As) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : As →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : As, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : As) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  let χA : A →* R := χ.comp (Subgroup.inclusion hAAs.le)
  have hχAinj : Function.Injective χA := hχinj.comp (Subgroup.inclusion_injective hAAs.le)
  have hAbA : IsElemAbelian p χA.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χA
  have hAbsA : IsElemAbelian p χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hAs a.2 b.2))
    (fun a => Subtype.ext (by simpa using hAs.2 a a.2)) χ
  have hle : χA.range ≤ χ.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨Subgroup.inclusion hAAs.le a, rfl⟩
  have hcardAb : Nat.card χA.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχAinj).toEquiv).symm
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      χA.range ≤ Subgroup.normalizer (U : Set R) := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    have e : ψ ((a : MulAut L') l) = χA a * ψ l * (χA a)⁻¹ :=
      hχ (Subgroup.inclusion hAAs.le a) l
    rw [← e]
    exact hAU a a.2 l hu
  obtain ⟨t, htAb, hend, h7⟩ := h χA.range χ.range hAbA hle hAbsA (hcardAb ▸ hr) (hcardAb ▸ h3)
    hUAb
  obtain ⟨a₀, rfl⟩ := htAb
  obtain ⟨ht1, hcomp, hcent⟩ := hend.2
  set a₁ : As := Subgroup.inclusion hAAs.le a₀ with ha₁
  have hχa₁ : χ a₁ = χA a₀ := rfl
  obtain ⟨t', ht'⟩ := hψ (χA a₀)
  have ha₀ := hinner a₁ t' (ht'.trans hχa₁.symm)
  have hfix : ggFix (a₀ : MulAut L') = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix]
    change (a₁ : MulAut L') l = l ↔ _
    rw [ha₀, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  rw [← ht'] at hcomp hcent h7
  obtain ⟨hlayer, hcompL⟩ := layer_centralizer_lift hψ hker hcomp
  set Kb := LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)) with hKb
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
  have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
  have hmapK := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hKbperf
  have hCentEnd : GGCentEnd As (a₀ : MulAut L') := by
    intro a' ha'
    obtain ⟨s', hs'⟩ := hψ (χ ⟨a', ha'⟩)
    have hinn' := hinner ⟨a', ha'⟩ s' hs'
    have hcent' := hcent (χ ⟨a', ha'⟩) ⟨⟨a', ha'⟩, rfl⟩
    rw [hfix, hlayer]
    constructor
    · intro hj
      have h1 : ∀ j ∈ Kb, χ ⟨a', ha'⟩ * j = j * χ ⟨a', ha'⟩ := by
        intro j hj'
        rw [← hmapK] at hj'
        obtain ⟨k, hk, rfl⟩ := hj'
        have e := hj k hk
        rw [hinn'] at e
        rw [← hs', ← map_mul, ← map_mul]
        congr 1
        calc s' * k = s' * k * s'⁻¹ * s' := by group
          _ = k * s' := by rw [e]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcent'.mp h1)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 : a₁ ^ n = ⟨a', ha'⟩ := hχinj (by rw [map_zpow, hχa₁, ← ht', hn])
      exact congrArg Subtype.val h2
    · intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h2 : a₁ ^ n = ⟨a', ha'⟩ := Subtype.ext hn
      have h3 : χ ⟨a', ha'⟩ ∈ Subgroup.zpowers (ψ t') :=
        Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [ht', ← hχa₁, ← map_zpow, h2]⟩
      have h4 := hcent'.mpr h3
      intro j hj
      rw [hinn']
      have hcomm := commute_of_mem_commutator (x := s')
        (Y := Kb.comap ψ) (fun y hy => hker (by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs', h4 (ψ y) hy]
          group)) hj
      rw [hcomm]
      group
  refine ⟨(a₀ : MulAut L'), ⟨a₀.2, fun h1 => ht1 ?_, ?_, fun a' ha' => hCentEnd a' (hAAs.le ha')⟩,
    hCentEnd, fun hp3 => ?_⟩
  · have : a₀ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [hfix]
    exact hcompL
  · refine IOneOrthEnd.not_largeEvenSmall_of_map ψ _ ?_
    rw [hfix, hlayer, hmapK]
    exact h7 hp3

theorem ggEndNodeIOne_of_elt {p r : ℕ} {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    (hC : GGCenterPrime p R)
    (hinn : ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ (MulAut.conj : R →* MulAut R).range)
    (h : GGEndNodeIOneElt p r R) : GGEndNodeIOne p r R (LargeEvenInnSet R) :=
  (ggEndNodeIOneNonSmall_of_elt hZ hC hinn h).endNodeIOne

end CFSG.StandardType
