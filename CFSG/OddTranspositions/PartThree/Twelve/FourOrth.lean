module

public import CFSG.OddTranspositions.PartThree.Twelve.Four
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
public import CFSG.RankThree.GF2n.Stroth80.GriessProof
import CFSG.RankThree.GF2n.Stroth80.GriessSL34Proof
import CFSG.OddTranspositions.WidthSylow
import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec31
public import CFSG.RankThree.GF2n.Stroth80.Sec33A0
public import CFSG.RankThree.GF2n.Stroth80.Sec33Card
public import CFSG.RankThree.GF2n.Stroth80.Sec33Weyl
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix Module QuadraticMap CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.WeakClosure81 CFSG.OddTranspositions.PartFour CFSG.Open

section RootTriple

variable {X : Type} [Group X] {K : Type} [Field K] [CharP K 2] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)}

private theorem polar_self_eq_zero' {V : Type*} [AddCommGroup V] [Module K V]
    (R : QuadraticForm K V) (x : V) : polar R x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
private theorem ne_zero_of_map_eq_one' {V : Type*} [AddCommGroup V] [Module K V]
    {R : QuadraticForm K V} {x : V} (hx : R x = 1) : x ≠ 0 := fun h => by
  rw [h, QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

private theorem commute_symmetryGL_iff (hQ : Q.polarBilin.Nondegenerate) {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) :
    Commute (symmetryGL Q x) (symmetryGL Q y) ↔ polar Q x y = 0 := by
  have h1 : Commute (symmetryGL Q x) (symmetryGL Q y) ↔
      symmetryGL Q x ∈ Subgroup.centralizer {symmetryGL Q y} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  rw [h1, mem_centralizer_symmetryGL_iff hQ hy (symmetryGL_mem Q x),
    symmetryGL_mulVec_of_charTwo hx, add_eq_left, smul_eq_zero]
  simp [ne_zero_of_map_eq_one' hx]

private theorem commute_iff_of_symmetryGL (hQ : Q.polarBilin.Nondegenerate)
    {ψ : X →* GL (Fin m) K} (hψ : Function.Injective ψ) {t t' : X} {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) (ht : ψ t = symmetryGL Q x) (ht' : ψ t' = symmetryGL Q y) :
    Commute t t' ↔ polar Q x y = 0 := by
  rw [← commute_symmetryGL_iff hQ hx hy, ← ht, ← ht']
  exact ⟨fun h => h.map ψ, fun h => hψ (by rw [map_mul, map_mul]; exact h.eq)⟩

private theorem exists_singular_perp [Finite K] (hQ : Q.polarBilin.Nondegenerate) (hm : 4 ≤ m)
    {v : Fin m → K} (hv : Q v = 1) : ∃ w, w ≠ 0 ∧ Q w = 0 ∧ polar Q v w = 0 := by
  have hdim : 3 ≤ finrank K (Fin m → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have hv0 := ne_zero_of_map_eq_one' hv
  obtain ⟨z, hvz⟩ : ∃ z, polar Q v z ≠ 0 := by
    by_contra! h0
    exact hv0 (hQ.1 v fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
  obtain ⟨c, hcv, hcz, hc⟩ := exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hvz 0
    (polar Q v z + 1) 1
  have hne : c ≠ v := by
    intro h
    rw [h] at hcz
    exact one_ne_zero (by linear_combination -hcz)
  have hvc : polar Q v c = 0 := by rw [polar_comm]; exact hcv
  have hvv := polar_self_eq_zero' Q v
  refine ⟨v + c, ?_, ?_, ?_⟩
  · intro h
    apply hne
    have hvv2 : v + v = 0 := by
      rw [← two_smul K v, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
    exact add_left_cancel (h.trans hvv2.symm)
  · rw [QuadraticMap.map_add Q v c, hv, hc, hvc, ← two_mul,
      show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, add_zero]
  · rw [polar_add_right, hvv, hvc, add_zero]

omit [CharP K 2] in
private theorem exists_ne_zero_ne_one' [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
  by_contra! h
  have hsurj : Function.Surjective (![0, 1] : Fin 2 → K) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [h x hx]⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

omit [CharP K 2] in
private theorem map_add_smul_eq_one {v w : Fin m → K} (hv : Q v = 1) (hw : Q w = 0)
    (hvw : polar Q v w = 0) (t : K) : Q (v + t • w) = 1 := by
  rw [QuadraticMap.map_add Q v (t • w), QuadraticMap.map_smul, hv, hw, polar_smul_right, hvw]
  simp

private theorem polar_add_smul_add_smul_eq_zero {v w : Fin m → K} (hvw : polar Q v w = 0)
    (a b : K) : polar Q (v + a • w) (v + b • w) = 0 := by
  have hvv := polar_self_eq_zero' Q v
  have hww := polar_self_eq_zero' Q w
  have hwv : polar Q w v = 0 := by rw [polar_comm]; exact hvw
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul, hvv,
    hww, hvw, hwv]
  ring

private theorem mulVec_symmetryGL_mul_mul {a b c : Fin m → K} (ha : Q a = 1) (hb : Q b = 1)
    (hc : Q c = 1) (hab : polar Q a b = 0) (hac : polar Q a c = 0) (hbc : polar Q b c = 0)
    (x : Fin m → K) :
    ((symmetryGL Q a * symmetryGL Q b * symmetryGL Q c : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K) *ᵥ x =
      x + polar Q a x • a + polar Q b x • b + polar Q c x • c := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    symmetryGL_mulVec_of_charTwo hc, symmetryGL_mulVec_of_charTwo hb,
    symmetryGL_mulVec_of_charTwo ha]
  simp only [polar_add_right, polar_smul_right, hab, hac, hbc, smul_eq_mul, mul_zero, add_zero]
  module

private theorem symmetryGL_eq_mul_mul {v w : Fin m → K} (hv : Q v = 1) (hw : Q w = 0)
    (hvw : polar Q v w = 0) (l : K) :
    symmetryGL Q v = symmetryGL Q (v + l • w) * symmetryGL Q (v + w) *
      symmetryGL Q (v + (l + 1) • w) := by
  have h1 := map_add_smul_eq_one hv hw hvw l
  have h2 := map_add_smul_eq_one hv hw hvw 1
  have h3 := map_add_smul_eq_one hv hw hvw (l + 1)
  rw [one_smul] at h2
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [mulVec_symmetryGL_mul_mul h1 h2 h3 (by simpa using polar_add_smul_add_smul_eq_zero hvw l 1)
    (polar_add_smul_add_smul_eq_zero hvw l (l + 1))
    (by simpa using polar_add_smul_add_smul_eq_zero hvw 1 (l + 1)),
    symmetryGL_mulVec_of_charTwo hv]
  simp only [polar_add_left, polar_smul_left, smul_eq_mul]
  generalize polar Q v x = p
  generalize polar Q w x = q
  have key : x + (p + l * q) • (v + l • w) + (p + q) • (v + w) +
      (p + (l + 1) * q) • (v + (l + 1) • w) = x + p • v +
      (2 : K) • ((p + (l + 1) * q) • v + ((l + 1) * p + (l ^ 2 + l + 1) * q) • w) := by
    module
  rw [key, CharTwo.two_eq_zero, zero_smul, add_zero]

end RootTriple

theorem isRootTriple_of_isOrthReflection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 6 ≤ m) (hf : 2 ≤ f) (h : IsOrthReflection X m f s) :
    IsRootTriple E s := by
  classical
  have hm4 : 4 ≤ m := by omega
  have hroot := rootBlock_eq_singleton_of_isOrthReflection hcls hZ hs hm4 (Or.inr hf) h
  obtain ⟨K, _, _, _, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, hrefl⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ h
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  obtain ⟨w, hw0, hw, hvw⟩ := exists_singular_perp hQ hm4 hv
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one' (K := K) hf
    (by rw [Nat.card_eq_fintype_card]; exact hcard)
  have hl1' : l + 1 ≠ 0 := by
    intro h
    apply hl1
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hne : ∀ t : K, t ≠ 0 → v + t • w ≠ v := by
    intro t ht h
    rw [add_eq_left, smul_eq_zero] at h
    exact h.elim ht hw0
  have hmem : ∀ t : K, ∃ y ∈ E, ψ y = symmetryGL Q (v + t • w) := by
    intro t
    obtain ⟨y, hyc, hψy⟩ := hrefl _ (map_add_smul_eq_one hv hw hvw t)
    exact ⟨y, (hEs y).mpr hyc, hψy⟩
  have hout : ∀ t : K, t ≠ 0 → ∀ y, ψ y = symmetryGL Q (v + t • w) → y ∉ rootBlock E s := by
    intro t ht y hy hyr
    rw [hroot, Set.mem_singleton_iff] at hyr
    rw [hyr, hψs] at hy
    exact hne t ht (eq_of_symmetryGL_eq hQ (map_add_smul_eq_one hv hw hvw t) hv hy.symm)
  have hcomm : ∀ t t' : K, ∀ y y', ψ y = symmetryGL Q (v + t • w) →
      ψ y' = symmetryGL Q (v + t' • w) → Commute y y' := by
    intro t t' y y' hy hy'
    rw [commute_iff_of_symmetryGL hQ hψ (map_add_smul_eq_one hv hw hvw t)
      (map_add_smul_eq_one hv hw hvw t') hy hy']
    exact polar_add_smul_add_smul_eq_zero hvw t t'
  obtain ⟨y₁, hy₁, hψ₁⟩ := hmem l
  obtain ⟨y₂, hy₂, hψ₂⟩ := hmem 1
  obtain ⟨y₃, hy₃, hψ₃⟩ := hmem (l + 1)
  refine ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hout l hl0 y₁ hψ₁, hout 1 one_ne_zero y₂ hψ₂,
    hout (l + 1) hl1' y₃ hψ₃, hcomm l 1 y₁ y₂ hψ₁ hψ₂, hcomm l (l + 1) y₁ y₃ hψ₁ hψ₃,
    hcomm 1 (l + 1) y₂ y₃ hψ₂ hψ₃, ?_⟩
  apply hψ
  rw [one_smul] at hψ₂
  rw [map_mul, map_mul, hψ₁, hψ₂, hψ₃, hψs, symmetryGL_eq_mul_mul hv hw hvw l]

section Commutator

open CFSG.ClassicalGroups.Orthogonal

private theorem symmetryGL_notMem_commutator {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate) {v : Fin d → K}
    (hv : Q v = 1) : symmetryGL Q v ∉ ⁅matrixIsometries Q, matrixIsometries Q⁆ := by
  intro h
  have h1 := (CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff
    Q _).mp h
  rw [matrixLinearIso_symmetryGL, ← Subgroup.map_subtype_commutator] at h1
  obtain ⟨x, hx, hxe⟩ := h1
  refine CFSG.RankThree.PartOne.reflect_not_mem_commutator hQ (a := v)
    (by rw [hv]; exact one_ne_zero) ?_
  rwa [← show x = ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ from Subtype.ext hxe]

end Commutator

theorem notMem_commutator_of_isOrthReflection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ}
    (h : IsOrthReflection X m f s) : s ∉ commutator X := by
  obtain ⟨K, _, _, _, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, -⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ h
  intro hs
  have h1 := Subgroup.mem_map_of_mem ψ hs
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange, hψs] at h1
  exact symmetryGL_notMem_commutator hQ hv h1

section Multiplier

variable {X : Type} [Group X] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

private theorem commutator_subgroup_eq_self {G : Type*} [Group G] {Ω : Subgroup G}
    (h : commutator ↥Ω = ⊤) : ⁅Ω, Ω⁆ = Ω := by
  rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem exists_embedding {O : Subgroup (GL ι F)} (hZ : Subgroup.center X = ⊥)
    (e : X ⧸ Subgroup.center X ≃* ↥O) :
    ∃ π₀ : X →* GL ι F, Function.Injective π₀ ∧ π₀.range = O := by
  have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  refine ⟨O.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))),
    O.subtype_injective.comp (e.injective.comp hmk), ?_⟩
  ext A
  constructor
  · rintro ⟨g, rfl⟩
    exact (e _).2
  · intro hA
    obtain ⟨q, hq⟩ := e.surjective ⟨A, hA⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    exact ⟨g, congrArg Subtype.val hq⟩

private theorem commutator_commutator_eq {O Ω : Subgroup (GL ι F)} (hZ : Subgroup.center X = ⊥)
    (e : X ⧸ Subgroup.center X ≃* ↥O) (hΩ : ⁅O, O⁆ = Ω) (hperf : ⁅Ω, Ω⁆ = Ω) :
    ⁅commutator X, commutator X⁆ = commutator X := by
  obtain ⟨π₀, hinj, hrange⟩ := exists_embedding hZ e
  have hcomm : (commutator X).map π₀ = Ω := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange, hΩ]
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_commutator, hcomm, hperf]

private theorem odd_card_ker_of_model {O Ω : Subgroup (GL ι F)} (hZ : Subgroup.center X = ⊥)
    (e : X ⧸ Subgroup.center X ≃* ↥O) (hΩ : ⁅O, O⁆ = Ω) (hperf : ⁅Ω, Ω⁆ = Ω)
    (hG : ∀ (Γ : Type) [Group Γ] [Finite Γ] (π : Γ →* GL ι F), π.range = Ω →
      commutator Γ = ⊤ → π.ker ≤ Subgroup.center Γ → π.ker = ⊥)
    (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* ↥(commutator X)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcomm' : φ.ker ≤ commutator Γ) :
    Odd (Nat.card φ.ker) := by
  obtain ⟨π₀, hinj, hrange⟩ := exists_embedding hZ e
  have hcomm : (commutator X).map π₀ = Ω := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange, hΩ]
  have hperfX := commutator_commutator_eq hZ e hΩ hperf
  have htop : commutator ↥(commutator X) = ⊤ := by
    apply Subgroup.map_injective (commutator X).subtype_injective
    rw [Subgroup.map_subtype_commutator, hperfX, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hΓ : commutator Γ = ⊤ := by
    have h1 : (commutator Γ).map φ = ⊤ := by
      have h := Subgroup.map_commutator (⊤ : Subgroup Γ) ⊤ φ
      rw [Subgroup.map_top_of_surjective φ hφ] at h
      exact h.trans htop
    have h2 : commutator Γ ⊔ φ.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, h1, Subgroup.comap_top]
    rwa [sup_eq_left.mpr hcomm'] at h2
  set π : Γ →* GL ι F := π₀.comp ((commutator X).subtype.comp φ) with hπ
  have hπrange : π.range = Ω := by
    rw [hπ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, hcomm]
  have hπker : π.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MonoidHom.comp_apply,
      map_eq_one_iff π₀ hinj]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hker := hG Γ π hπrange hΓ (by rw [hπker]; exact hcen)
  rw [hπker] at hker
  rw [hker, Subgroup.card_bot]
  exact odd_one

end Multiplier

section Griess

open CFSG.RankThree.GF2n.Stroth80

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem ker_eq_bot_of_clause {Γ : Type} [Group Γ] (Y : Subgroup Γ) {b : ℕ}
    (h : ∀ A : Subgroup Γ, A ⊓ Y = ⊥ → CFSG.Open.IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup Γ) : Set Γ),
        e ∈ Subgroup.normalizer (A : Set Γ)) → Nat.card A < b) :
    1 < b := by
  have h1 := h ⊥ (bot_inf_eq _) ⟨inferInstance, fun x hx => by
    rw [Subgroup.mem_bot.mp hx, one_pow]⟩ (fun e _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp [mul_inv_eq_one])
  rwa [Subgroup.card_bot] at h1

private theorem ker_eq_bot_plus (hG : GriessCoverStatement) (h4 : 4 ≤ Nat.card F) {k : ℕ}
    (hk : 3 ≤ k) (Γ : Type) [Group Γ] [Finite Γ] (π : Γ →* GL (Fin k ⊕ Fin k) F)
    (hrange : π.range = CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus k F))
    (hperf : commutator Γ = ⊤) (hcen : π.ker ≤ Subgroup.center Γ) : π.ker = ⊥ := by
  rcases (hG F h4 Γ π.ker hcen hperf).2.2.1 k (by omega) π hrange rfl with hY | hA
  · exact hY
  · exfalso
    have h1 := ker_eq_bot_of_clause π.ker hA
    have hc : ¬ (Nat.card F = 4 ∧ k = 2) := fun h => by omega
    rw [if_neg hc] at h1
    omega

private theorem ker_eq_bot_minus (hG : GriessCoverStatement) (h4 : 4 ≤ Nat.card F) {k : ℕ}
    (hk : 1 ≤ k) {b c : F} (hirr : ∀ t : F, t ^ 2 + b * t + c ≠ 0) (Γ : Type) [Group Γ] [Finite Γ]
    (π : Γ →* GL (Fin k ⊕ Fin k ⊕ Fin 2) F)
    (hrange : π.range = CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (k + 1) F b c))
    (hperf : commutator Γ = ⊤) (hcen : π.ker ≤ Subgroup.center Γ) : π.ker = ⊥ :=
  (hG F h4 Γ π.ker hcen hperf).2.2.2 (k + 1) b c (by omega) hirr π hrange rfl

end Griess

section Model

open CFSG.ComponentClassification.RankTwoClassical CFSG.RankThree.GF2n.Stroth80

private theorem exists_matrix_model {X : Type} [Group X] {s : X} {m f : ℕ} (hm : 6 ≤ m)
    (hf : 2 ≤ f) (h : IsOrthReflection X m f s) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (F : Type) (_ : Field F) (_ : Finite F)
      (O Ω : Subgroup (GL ι F)), Nonempty (X ⧸ Subgroup.center X ≃* ↥O) ∧ ⁅O, O⁆ = Ω ∧
      ⁅Ω, Ω⁆ = Ω ∧ (GriessCoverStatement →
        ∀ (Γ : Type) [Group Γ] [Finite Γ] (π : Γ →* GL ι F), π.range = Ω → commutator Γ = ⊤ →
          π.ker ≤ Subgroup.center Γ → π.ker = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨k, hk, hmk, F, hF, hFin, hcard, e, -⟩ |
    ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc, e, -⟩
  · let _ : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
    have hk3 : 3 ≤ k := by omega
    have h4 : 4 ≤ Nat.card F := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact ⟨Fin k ⊕ Fin k, inferInstance, inferInstance, F, hF, hFin,
      CFSG.PGLModel.orthogonalPlus k F, StatedOmega (StatedQuadPlus k F), ⟨e⟩, rfl,
      commutator_subgroup_eq_self (Group.isPerfect_def.mp
        (CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := F) hk3)),
      fun hG Γ _ _ π hr hp hc => ker_eq_bot_plus hG h4 hk3 Γ π hr hp hc⟩
  · let _ : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
    have h4 : 4 ≤ Nat.card F := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact ⟨Fin k ⊕ Fin k ⊕ Fin 2, inferInstance, inferInstance, F, hF, hFin,
      CFSG.PGLModel.orthogonalMinus k F b c, StatedOmega (StatedQuadMinus (k + 1) F b c), ⟨e⟩,
      rfl, commutator_subgroup_eq_self
        (ORigid.commutator_statedOmega_quadMinus_eq_top (m := k + 1) (by omega) hbc),
      fun hG Γ _ _ π hr hp hc => ker_eq_bot_minus hG h4 (by omega) hbc Γ π hr hp hc⟩

end Model

theorem commutator_perfect_of_isOrthReflection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 6 ≤ m) (hf : 2 ≤ f)
    (h : IsOrthReflection X m f s) : ⁅commutator X, commutator X⁆ = commutator X := by
  obtain ⟨ι, _, _, F, _, _, O, Ω, ⟨e⟩, hΩ, hperf, -⟩ := exists_matrix_model hm hf h
  exact commutator_commutator_eq hZ e hΩ hperf

theorem odd_card_ker_of_isOrthReflection_of_griessCover
    (hG : CFSG.RankThree.GF2n.Stroth80.GriessCoverStatement) {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 6 ≤ m) (hf : 2 ≤ f)
    (h : IsOrthReflection X m f s) :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* ↥(commutator X)), Function.Surjective φ →
      φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → Odd (Nat.card φ.ker) := by
  intro Γ _ _ φ hφ hcen hcomm
  obtain ⟨ι, _, _, F, _, _, O, Ω, ⟨e⟩, hΩ, hperf, hker⟩ := exists_matrix_model hm hf h
  exact odd_card_ker_of_model hZ e hΩ hperf (hker hG) Γ φ hφ hcen hcomm

section Certs


theorem odd_card_ker_of_isOrthReflection {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    {s : X} {m f : ℕ} (hm : 6 ≤ m) (hf : 2 ≤ f) (h : IsOrthReflection X m f s) :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* ↥(commutator X)), Function.Surjective φ →
      φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → Odd (Nat.card φ.ker) :=
  odd_card_ker_of_isOrthReflection_of_griessCover
    (CFSG.RankThree.GF2n.Stroth80.griessCoverStatement_of_sl34
      CFSG.RankThree.GF2n.Stroth80.griessSL34Statement_holds) hZ hm hf h

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem false_of_isOrthReflection (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 6 ≤ m) (hf : 2 ≤ f)
    (h : IsOrthReflection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) : False := by
  have hZ : Subgroup.center
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ := by
    have h1 := center_le_solvableRadical
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    rw [solvableRadical_quotient_H hC] at h1
    exact le_bot_iff.mp h1
  obtain ⟨hb1, hne⟩ := subset_rootBlock_and_ne_of_isOrthReflection_of_four_le
    (imageClass_isClass hC) hZ hs (by omega) (Or.inr hf) h
  have htri := isRootTriple_of_isOrthReflection (imageClass_isClass hC) hZ hs hm hf h
  have hodd := odd_card_center_inf_commutator_of_multiplier hC hMZ
    (commutator_perfect_of_isOrthReflection hZ hm hf h)
    (odd_card_ker_of_isOrthReflection hZ hm hf h)
  exact false_of_isRootTriple_of_notMem_commutator hC hMZ hs hb1 hne htri hodd
    (notMem_commutator_of_isOrthReflection hZ h)

end Certs

end CFSG.OddTranspositions.PartThree
