module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.Universal

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.StandardType


private theorem excPayV6_raw_data {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f),
      2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ Nat.card K = (2 ^ f) ^ 2 ∧ commutator ↥X = ⊤ ∧
      MarkedModel ⟨.twE6, 0, f⟩ (TwE6Delta.RecipeR K f) ∧
      (∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G)) ∧
      (∀ b ∈ Bs, ∃ φ ∈ TwE6Delta.RecipeI K f,
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  have hraw_std : CFSG.StandardType.LargeEvenRawDatum lab _ :=
    (largeEvenRawDatum_legacy lab _).mpr hraw
  rcases lab with ⟨tag, rank, n⟩
  cases tag
  case twE6 =>
    simp only [LargeEvenRawDatum, LargeEvenRecipeTwisted] at hraw_std
    obtain ⟨K, hK_field, hK_finite, hK_card, hQ⟩ := hraw_std
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨⟨-, hp⟩, hn2⟩ := hP.1
    obtain ⟨hBsN, hBsInd⟩ := hP.2
    obtain ⟨hn1, hrank⟩ := hlab
    subst hrank
    have hm : MarkedModel ⟨.twE6, 0, n⟩ (TwE6Delta.RecipeR K n) := by
      have hK2 : Nat.card K = (2 ^ n) ^ TwistTag.E6.order := by
        rw [hK_card]
        rfl
      have hmod : TwistedChevalleyModel (TwE6Delta.RecipeR K n) TwistTag.E6 (2 ^ n) :=
        twistedChevalleyModel_largeEven (t := TwistTag.E6) (n := n) (K := K) hK2
      have hmem : StatedLieTag.twistedE6 ∈ chevalleyExceptionalTags := by decide
      exact Or.inr (Or.inl ⟨rfl, hmem, ⟨⟨Nat.prime_two, hn1, rfl⟩, hmod⟩⟩)
    exact ⟨n, K, hK_field, hK_finite, θ, hn2, hp, hK_card, hperf, hm, hBsN, hBsInd⟩
  all_goals
    obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw_std
    obtain ⟨-, -, θ, hP⟩ := hQ
    exact absurd hP.1.1.1 (by simp)

theorem exists_recipe_of_marking_twE6 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G}
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f),
      2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ Nat.card K = (2 ^ f) ^ 2 ∧ commutator ↥X = ⊤ ∧
      (∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G)) ∧
      (∀ b ∈ Bs, ∃ φ ∈ TwE6Delta.RecipeI K f,
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  obtain ⟨f, K, hK_field, hK_finite, θ, hf, hpf, hK_card, hcomm, -, hBsN, hBsInd⟩ :=
    excPayV6_raw_data hmark
  exact ⟨f, K, hK_field, hK_finite, θ, hf, hpf, hK_card, hcomm, hBsN, hBsInd⟩

theorem isCentralQuotientOf_of_presentsG0 {G : Type} [Group G] {X : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ₀ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 X (ggU t n f).D t n f ψ₀) :
    IsCentralQuotientOf (lieUniversal t n 2 f Nat.prime_two) ↥X := by
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hmem : ∀ x : (ggU t n f).K, ψ₀ x ∈ X := by
    intro x
    rw [← hrange]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  let θ : (ggU t n f).K →* ↥X := ψ₀.codRestrict X hmem
  refine ⟨θ, ?_, ?_⟩
  · intro y
    have hy : (y : G) ∈ ψ₀.range := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
    exact ⟨x, Subtype.ext hx⟩
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : ψ₀ x = 1 := congrArg Subtype.val hx
    exact hker (MonoidHom.mem_ker.2 hx')

private theorem excPayV6_psi_ker {L : Type} [Group L] {K : Type} [Field K] {f : ℕ}
    (θ : L ⧸ Subgroup.center L ≃* TwE6Delta.RecipeR K f) :
    (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (Subgroup.center L) x = 1 := by
      apply θ.injective
      simpa using h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  · intro hx
    have h1 : QuotientGroup.mk' (Subgroup.center L) x = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    rw [h1, map_one]

private theorem excPayV6_pow_apply {L R : Type} [Group L] [Group R] {ψ : L →* R}
    {φ : MulAut R} {c : MulAut L} (hφ : ∀ l, φ (ψ l) = ψ (c l)) (k : ℕ) (l : L) :
    (φ ^ k) (ψ l) = ψ ((c ^ k) l) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc (φ ^ (k + 1)) (ψ l)
        = φ ((φ ^ k) (ψ l)) := by rw [pow_succ', MulAut.mul_apply]
      _ = φ (ψ ((c ^ k) l)) := by rw [ih]
      _ = ψ (c ((c ^ k) l)) := hφ _
      _ = ψ ((c ^ (k + 1)) l) := by rw [pow_succ', MulAut.mul_apply]

private theorem excPayV6_conj_inner {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hperf : commutator ↥X = ⊤)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f)
    (hBsN : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G))
    (hBsInd : ∀ b ∈ Bs, ∃ φ ∈ TwE6Delta.RecipeI K f,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (b : G) (hb : b ∈ Bs) :
    ∃ x : ↥X, MulAut.conj x =
      Subgroup.normalizerMonoidHom (H := X) ⟨b⁻¹, Subgroup.inv_mem _ (hBsN b hb)⟩ := by
  let ψ : ↥X →* TwE6Delta.RecipeR K f :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center ↥X := (excPayV6_psi_ker θ).le
  have hbN' : b⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ (hBsN b hb)
  let c : MulAut ↥X := Subgroup.normalizerMonoidHom (H := X) ⟨b⁻¹, hbN'⟩
  have hc : ∀ y : ↥X, (c y : G) = b⁻¹ * (y : G) * b := by
    intro y
    show ((Subgroup.normalizerMonoidHom (H := X) ⟨b⁻¹, hbN'⟩) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  obtain ⟨φ, hφI, hφInd⟩ := hBsInd b hb
  have hφ : ∀ l : ↥X, φ (ψ l) = ψ (c l) := fun l => hφInd l (c l) (hc l)
  have hcp : c ^ p = 1 := by
    have h1 : (⟨b⁻¹, hbN'⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, inv_pow, hBs.2 b hb, inv_one]
      rfl
    calc c ^ p = Subgroup.normalizerMonoidHom (H := X)
          ((⟨b⁻¹, hbN'⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ p) :=
          (map_pow (Subgroup.normalizerMonoidHom (H := X)) ⟨b⁻¹, hbN'⟩ p).symm
      _ = 1 := by rw [h1, map_one]
  have hφp : φ ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [excPayV6_pow_apply hφ p l, hcp]
    rfl
  have hφinn : φ ∈ (MulAut.conj : TwE6Delta.RecipeR K f →*
      MulAut (TwE6Delta.RecipeR K f)).range :=
    TwE6Delta.ggOutdiagPrime_twE6 (by omega) hK hp hp3 φ hφI hφp
  obtain ⟨x, hx⟩ :=
    MonoidHom.mem_range.1 (mem_range_conj_of_induces_inn hψ hker hperf hφ hφinn)
  exact ⟨x, hx⟩

private theorem excPayV6_inner {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hperf : commutator ↥X = ⊤)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f)
    (hBsN : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G))
    (hBsInd : ∀ b ∈ Bs, ∃ φ ∈ TwE6Delta.RecipeI K f,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G) ∧
      ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := by
  intro b hb
  obtain ⟨x, hx⟩ := excPayV6_conj_inner hp hp3 hBs hf hK hperf θ hBsN hBsInd b hb
  refine ⟨hBsN b hb, x⁻¹, X.inv_mem x.2, fun y hy => ?_⟩
  have hy' : b * y * b⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.1 (hBsN b hb) y).1 hy
  have hkey : ∀ z ∈ X, b⁻¹ * z * b = (x : G) * z * (x : G)⁻¹ := by
    intro z hz
    have h1 : ((Subgroup.normalizerMonoidHom (H := X)
        ⟨b⁻¹, Subgroup.inv_mem _ (hBsN b hb)⟩) ⟨z, hz⟩ : G) = b⁻¹ * z * b := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp
    calc b⁻¹ * z * b
        = ((Subgroup.normalizerMonoidHom (H := X)
            ⟨b⁻¹, Subgroup.inv_mem _ (hBsN b hb)⟩) ⟨z, hz⟩ : G) := h1.symm
      _ = ((MulAut.conj x) ⟨z, hz⟩ : G) := by rw [hx]
      _ = (x : G) * z * (x : G)⁻¹ := by
          rw [MulAut.conj_apply]
          simp
  have h6 : y = (x : G) * (b * y * b⁻¹) * (x : G)⁻¹ := by
    rw [← hkey (b * y * b⁻¹) hy']
    group
  have hfin : (x : G)⁻¹ * y * (x : G) = b * y * b⁻¹ := by
    conv_lhs => rw [h6]
    group
  simpa [Subgroup.coe_inv, inv_inv] using hfin.symm

theorem exists_twE6Cover_of_marking {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    ∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      ∃ ψ₀ : (ggU .twistedE6 0 f).K →* G,
        GGPresentsG0 X (ggU .twistedE6 0 f).D .twistedE6 0 f ψ₀ ∧
        Nat.card ↥(Subgroup.center ↥X) ∣ 3 ∧
        ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G) ∧
          ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := by
  obtain ⟨f, K, hK_field, hK_finite, θ, hf, hpf, hK_card, hcomm, hm, hBsN, hBsInd⟩ :=
    excPayV6_raw_data hmark
  let ψ : ↥X →* TwE6Delta.RecipeR K f :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerψ : ψ.ker = Subgroup.center ↥X := excPayV6_psi_ker θ
  obtain ⟨π, φ, -, -, hφs, -, hφker, -⟩ :=
    exists_cover_phi_recipe_twE6 hf hK_card ↥X ψ hψ hkerψ.le hcomm
  let ψ₀ : (ggU .twistedE6 0 f).K →* G := X.subtype.comp φ
  have hrange : ψ₀.range = X := by
    change (X.subtype.comp φ).range = X
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφs, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hker₀ : ψ₀.ker ≤ Subgroup.center (ggU .twistedE6 0 f).K := by
    intro x hx
    have h1 : φ x = 1 := by
      apply Subtype.ext
      exact MonoidHom.mem_ker.1 hx
    exact hφker (MonoidHom.mem_ker.2 h1)
  have hlm : LieModel (↥X ⧸ Subgroup.center ↥X) .twistedE6 0 2 f :=
    lieModel_of_mulEquiv' θ.symm
      (show LieModel (TwE6Delta.RecipeR K f) .twistedE6 0 2 f from hm)
  have hpres : GGPresentsG0 X (ggU .twistedE6 0 f).D .twistedE6 0 f ψ₀ := by
    have hrk : 2 ≤ (ggU .twistedE6 0 f).D.rank := by
      rw [show (ggU .twistedE6 0 f).D.rank = 4 from rfl]
      decide
    have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, by omega, rfl⟩
    exact ⟨⟨hadm, hrk⟩, ⟨hrange, hker₀⟩, hcomm, hlm⟩
  have hZ3 : Nat.card ↥(Subgroup.center ↥X) ∣ 3 := by
    have hdvd := card_ker_dvd_gcd_recipe_twE6 hf hK_card ψ hψ hkerψ.le hcomm
    rw [hkerψ] at hdvd
    exact hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ f + 1))
  exact ⟨f, hf, hpf, ψ₀, hpres, hZ3, excPayV6_inner hp hp3 hBs hf hK_card hcomm θ hBsN hBsInd⟩

end CFSG.StandardType.ExcPay
