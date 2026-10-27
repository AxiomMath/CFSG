module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGAutRankLeTwo (p : ℕ) : LargeEvenRawCont :=
  fun R _ _ _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ E : Subgroup (MulAut R), IsElemAbelian p E → Nat.card E ≤ p ^ 2

@[expose] def GGLinearTwoLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2)

namespace NbrLangRest

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_large_elemAbelian {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) :
    ∃ E : Subgroup (MulAut R), IsElemAbelian p E ∧ p ^ 2 < Nat.card E := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have := Fact.mk hp
  have hB : IsElemAbelian p B := hC.1.2.2.2.2.2.2.1.1.1
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hC.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hC.1.2.2.2.2.2.1.2.2.2
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hC.2.1.1.trans hN
  have hS : LargeEvenSHat p B y K := hK.1
  set α : ↥B →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hBN) with hα
  have hE : IsElemAbelian p α.range :=
    isElemAbelian_range (fun a b => hB.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hB.2 a a.2)) α
  refine ⟨α.range, hE, ?_⟩
  have hker : α.ker ≤ (Subgroup.zpowers y).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_zpowers_of_sHat hS]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one K θ hperf (g := ⟨b, hBN b.2⟩) hb⟩
  have hyB : y ∈ B := hS.2.1
  have hy : Nat.card ((Subgroup.zpowers y).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hB.2 y hyB) hS.2.2.1]
  have hk : Nat.card α.ker ≤ p := hy ▸ Subgroup.card_le_of_le hker
  have h1 := Subgroup.card_ker_mul_card_range α
  have h2 : p ^ 4 ≤ Nat.card B := by
    rw [hBc]
    exact Nat.pow_le_pow_right hp.pos h4
  have h3 : p ^ 4 ≤ p * Nat.card α.range :=
    h2.trans (h1 ▸ Nat.mul_le_mul_right _ hk)
  have h5 : p * p ^ 2 < p * Nat.card α.range := by
    have : p * p ^ 2 < p ^ 4 := by
      rw [← pow_succ']
      exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  exact Nat.lt_of_mul_lt_mul_left h5

end Config

section LinearTwo

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hna : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem conj_injective_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hna : ∃ a b : Q, a * b ≠ b * a) : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hz : r ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun s => by
    have h1 : r * s * r⁻¹ = s := by
      have := congrArg (fun φ : MulAut Q => φ s) hr
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc s * r = r * s * r⁻¹ * r := by rw [h1]
      _ = r * s := by group
  rw [center_eq_bot_of_simple hs hna] at hz
  exact Subgroup.mem_bot.mp hz

theorem isElemAbelian_of_le' {M : Type*} [Group M] {p : ℕ} {E E₀ : Subgroup M}
    (hE : IsElemAbelian p E) (h : E₀ ≤ E) : IsElemAbelian p E₀ := CFSG.Open.IsElemAbelian.mono hE h

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem mem_range_conj_of_mem_conjImage_two
    {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ) :
    ∃ r, MulAut.conj r = φ := by
  obtain ⟨A, -, hA⟩ := hφ
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2)
    ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact (Matrix.GeneralLinearGroup.det A).ne_zero hs
  set u : Fˣ := Units.mk0 s hs0 with hu
  have hdet : Matrix.GeneralLinearGroup.det A = u * u := Units.ext (by rw [hs]; rfl)
  set A' : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * A with hA'def
  have hA' : A' ∈ LargeEvenSLGroup (Fin 2) F := by
    rw [LargeEvenSLGroup, MonoidHom.mem_ker, hA'def, map_mul,
      Matrix.GeneralLinearGroup.det_scalar, hdet, Fintype.card_fin]
    group
  have hconj : ∀ g : GL (Fin 2) F, A' * g * A'⁻¹ = A * g * A⁻¹ := by
    intro g
    rw [hA'def, mul_inv_rev, ← map_inv, inv_inv]
    calc Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * A * g *
          (A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)
        = Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * (A * g * A⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) u := by group
      _ = (A * g * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
        rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = A * g * A⁻¹ := by rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  refine ⟨LargeEvenProjMk _ ⟨A', hA'⟩, ?_⟩
  ext r
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ r
  rw [MulAut.conj_apply]
  have hmem : A' * (h : GL (Fin 2) F) * A'⁻¹ ∈ LargeEvenSLGroup (Fin 2) F :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hA' h.2) (Subgroup.inv_mem _ hA')
  rw [hA h ⟨_, hmem⟩ (hconj h)]
  rw [← map_mul, ← map_inv, ← map_mul]
  rfl

theorem card_le_of_forall_mem_conjImage_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 2) F), a * b ≠ b * a)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)))) (hE : IsElemAbelian p E)
    (hEI : ∀ φ ∈ E, φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F))
      Set.univ) :
    Nat.card E ≤ p := by
  have := Fact.mk hp
  have hinj := conj_injective_of_simple hs hna
  have hle : E ≤ (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin 2) F) →* _).range :=
    fun φ hφ => mem_range_conj_of_mem_conjImage_two (hEI φ hφ)
  set P : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := E.comap MulAut.conj with hP
  have hPE : Nat.card P = Nat.card E := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hle]
  have hPp : ∀ r ∈ P, r ^ p = 1 := fun r hr =>
    hinj (by rw [map_pow, map_one]; exact hE.2 _ hr)
  set e : LargeEvenProj (LargeEvenSLGroup (Fin 2) F) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (TypeA.recipeEquiv 2 F).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F) with he
  set P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := P.map e.toMonoidHom with hP'
  have hP'card : Nat.card P' = Nat.card P := Subgroup.card_map_of_injective e.injective
  have hP'p : ∀ g ∈ P', g ^ p = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hPp r hr, map_one]
  have hcyc : IsCyclic P' :=
    CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 P'
      (fun g => ⟨1, Subtype.ext (by simpa using hP'p g g.2)⟩)
  have h1 := TableB.card_le_of_isCyclic hp.pos hcyc hP'p
  omega

theorem ggAutRankLeTwo_linear_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGAutRankLeTwo p (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F))) := by
  intro hs hna E hE
  obtain ⟨J, S, hJ, -, hnorm, ⟨g, hgS, hg⟩, hpS⟩ :=
    RecipeFieldLinear.ggRawPCyclic_linear (K := F) le_rfl (hp.odd_of_ne_two hp2) hs hna
  have hES : E ≤ S := fun φ hφ => hpS φ ⟨1, by rw [pow_one]; exact hE.2 φ hφ⟩
  have hQ : IsCyclic (↥S ⧸ J.subgroupOf S) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgS⟩, fun q => ?_⟩⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hg s s.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgS⟩ ^ (-k)) : ↥S ⧸ J.subgroupOf S) = QuotientGroup.mk s
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [zpow_neg] using hk
  set χ : ↥E →* ↥S ⧸ J.subgroupOf S :=
    (QuotientGroup.mk' (J.subgroupOf S)).comp (Subgroup.inclusion hES) with hχ
  have hrange : Nat.card χ.range ≤ p := by
    refine TableB.card_le_of_isCyclic hp.pos inferInstance ?_
    rintro _ ⟨a, rfl⟩
    have ha : a ^ p = 1 := Subtype.ext (by simpa using hE.2 a a.2)
    rw [← map_pow, ha, map_one]
  set E₀ : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))) :=
    χ.ker.map E.subtype with hE₀
  have hE₀card : Nat.card E₀ = Nat.card χ.ker := Subgroup.card_map_of_injective E.subtype_injective
  have hE₀E : E₀ ≤ E := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hE₀I : ∀ φ ∈ E₀, φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : χ a = 1 := ha
    rw [hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha'
    rw [← hJ]
    exact ha'
  have hker : Nat.card χ.ker ≤ p :=
    hE₀card ▸ card_le_of_forall_mem_conjImage_two hp hp2 hs hna E₀ (isElemAbelian_of_le' hE hE₀E)
      hE₀I
  have h1 := Subgroup.card_ker_mul_card_range χ
  calc Nat.card E = Nat.card χ.ker * Nat.card χ.range := h1.symm
    _ ≤ p * p := Nat.mul_le_mul hker hrange
    _ = p ^ 2 := (sq p).symm

end LinearTwo

end NbrLangRest

open NbrLangRest

theorem ggNbrLangTorusAxisOn_of_autRankLeTwo {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGAutRankLeTwo p)) :
    GGNbrLangTorusAxisOn S := by
  intro G _ _ p B Bs x L D J hC y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : S p lab
  · refine largeEvenRawDatum_mono ?_
      (h p lab hC.1.2.2.2.2.2.1.1 hC.1.2.2.2.2.2.1.2.1 hlab hS _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hrk⟩
    obtain ⟨E, hE, hcard⟩ := exists_large_elemAbelian hC hK hN hperf θ
    exact absurd (hrk hs hna E hE) (not_le.mpr hcard)
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h' => absurd h' hS⟩) hraw

theorem ggNbrInnerWeylOn_of_autRankLeTwo {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGAutRankLeTwo p)) :
    GGNbrInnerWeylOn S := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : S p lab
  · refine largeEvenRawDatum_mono ?_
      (h p lab hC.1.2.2.2.2.2.1.1 hC.1.2.2.2.2.2.1.2.1 hlab hS _ hraw)
    rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hrk⟩
    obtain ⟨E, hE, hcard⟩ := exists_large_elemAbelian hC hK hN hperf θ
    exact absurd (hrk hs hna E hE) (not_le.mpr hcard)
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h' => absurd h' hS⟩) hraw

theorem largeEvenLabelAll_autRankLeTwo_linearTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : GGLinearTwoLabel lab) :
    LargeEvenLabelAll lab (GGAutRankLeTwo p) := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases h with ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht hl <;> subst ht hl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ hK => by
      have := charP_two_of_card hK
      exact ggAutRankLeTwo_linear_two hp hp2) hQ
  · simp only [LargeEvenRawDatum, ↓reduceIte] at hQ ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ hK => by
      have := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
      exact ggAutRankLeTwo_linear_two hp hp2) hQ

theorem ggNbrLangTorusAxisOn_linearTwo :
    GGNbrLangTorusAxisOn fun _ lab => GGLinearTwoLabel lab :=
  ggNbrLangTorusAxisOn_of_autRankLeTwo fun _ _ hp hp2 _ h =>
    largeEvenLabelAll_autRankLeTwo_linearTwo hp hp2 h

theorem ggNbrInnerWeylOn_linearTwo : GGNbrInnerWeylOn fun _ lab => GGLinearTwoLabel lab :=
  ggNbrInnerWeylOn_of_autRankLeTwo fun _ _ hp hp2 _ h =>
    largeEvenLabelAll_autRankLeTwo_linearTwo hp hp2 h

end CFSG.StandardType

end
