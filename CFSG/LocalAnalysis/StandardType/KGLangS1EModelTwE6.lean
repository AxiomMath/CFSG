module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EBridgeFix
public import CFSG.LocalAnalysis.StandardType.KGLangS1ECover
public import CFSG.LocalAnalysis.StandardType.KGLangS1ENormalFormTwE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.LocalAnalysis.StandardType.GGL45E67Center
import CFSG.LocalAnalysis.StandardType.GGL45NtRecTwE6
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc

private theorem kgLangS1EModelTwE6Aux_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private theorem kgLangS1EModelTwE6Aux_conj {R Γ : Type} [Group R] [Group Γ] (ρ : R →* Γ)
    (hρ : Function.Injective ρ) (g : Γ) (C : Subgroup R) (S : Subgroup Γ)
    (hiff : ∀ r : R, r ∈ C ↔ g⁻¹ * ρ r * g ∈ S)
    (honto : ∀ y ∈ S, ∃ r : R, r ∈ C ∧ g⁻¹ * ρ r * g = y) :
    ∃ e : ↥C ≃* ↥S, ∀ r : ↥C, (e r : Γ) = g⁻¹ * ρ (r : R) * g := by
  let φ : ↥C →* ↥S :=
    { toFun := fun r => ⟨g⁻¹ * ρ (r : R) * g, (hiff (r : R)).mp r.2⟩
      map_one' := Subtype.ext (by
        show g⁻¹ * ρ (1 : R) * g = 1
        simp)
      map_mul' := fun a b => Subtype.ext (by
        show g⁻¹ * ρ ((a : R) * (b : R)) * g = (g⁻¹ * ρ (a : R) * g) * (g⁻¹ * ρ (b : R) * g)
        rw [map_mul]
        group) }
  have hφ_apply : ∀ r : ↥C, (φ r : Γ) = g⁻¹ * ρ (r : R) * g := fun r => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply hρ
    have h : g⁻¹ * ρ (a : R) * g = g⁻¹ * ρ (b : R) * g := by
      rw [← hφ_apply a, ← hφ_apply b, hab]
    have h2 := congrArg (fun z => g * z * g⁻¹) h
    simpa [mul_assoc] using h2
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨r, hr, hy⟩ := honto (y : Γ) y.2
    exact ⟨⟨r, hr⟩, Subtype.ext hy⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun r => rfl⟩

private theorem kgLangS1EModelTwE6Aux_base
    {τ : Tag} {k L : Type} [Field k]
    [Field L] (ι : k →+* L) (H : Subgroup (ModGL τ k)) (S : Subgroup (ModGL τ L))
    (hfix : S = H.map (baseChangeGL ι)) :
    ∃ e : ↥H ≃* ↥S, ∀ y : ↥H, (e y : ModGL τ L) = baseChangeGL ι (y : ModGL τ k) := by
  subst hfix
  exact ⟨H.equivMapOfInjective (baseChangeGL ι) (baseChangeGL_injective ι),
    fun y => Subgroup.coe_equivMapOfInjective_apply _ _ _ y⟩

private theorem kgLangS1EModelTwE6Aux_quot {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (J₀ : Subgroup K) (C : Subgroup R)
    (h1 : ∀ j ∈ J₀, θ (QuotientGroup.mk j) ∈ C)
    (h2 : ∀ r ∈ C, ∃ j ∈ J₀, θ (QuotientGroup.mk j) = r)
    (h3 : ∀ j ∈ J₀, θ (QuotientGroup.mk j) = 1 ↔ ∀ j' ∈ J₀, j * j' = j' * j) :
    ∃ q : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥C,
      ∀ j : ↥J₀, (q (QuotientGroup.mk j) : R) = θ (QuotientGroup.mk (j : K)) := by
  let fbase : ↥J₀ →* ↥C :=
    { toFun := fun j => ⟨θ (QuotientGroup.mk (j : K)), h1 (j : K) j.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  have hsurj : Function.Surjective fbase := by
    intro c
    obtain ⟨j, hj, hjc⟩ := h2 (c : R) c.2
    exact ⟨⟨j, hj⟩, Subtype.ext hjc⟩
  have hker : fbase.ker = Subgroup.center ↥J₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx g
      have hx1 : θ (QuotientGroup.mk (x : K)) = 1 := congrArg Subtype.val hx
      exact Subtype.ext ((h3 (x : K) x.2).mp hx1 (g : K) g.2).symm
    · intro hx
      apply Subtype.ext
      show θ (QuotientGroup.mk (x : K)) = 1
      exact (h3 (x : K) x.2).mpr (fun j' hj' =>
        (congrArg Subtype.val (hx ⟨j', hj'⟩)).symm)
  let qhom : (↥J₀ ⧸ Subgroup.center ↥J₀) →* ↥C :=
    QuotientGroup.lift (Subgroup.center ↥J₀) fbase (le_of_eq hker.symm)
  have hqhom_mk : ∀ j : ↥J₀, qhom (QuotientGroup.mk j) = fbase j := by
    intro j
    rw [QuotientGroup.lift_mk]
  have hqker : qhom.ker = ⊥ := by
    ext a
    rw [Subgroup.mem_bot]
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective a
    rw [MonoidHom.mem_ker, hqhom_mk j, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    constructor
    · intro hfj g
      have hx1 : θ (QuotientGroup.mk (j : K)) = 1 := congrArg Subtype.val hfj
      exact Subtype.ext ((h3 (j : K) j.2).mp hx1 (g : K) g.2).symm
    · intro hj
      apply Subtype.ext
      show θ (QuotientGroup.mk (j : K)) = 1
      exact (h3 (j : K) j.2).mpr (fun j' hj' =>
        (congrArg Subtype.val (hj ⟨j', hj'⟩)).symm)
  have hqinj : Function.Injective qhom := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ qhom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    rw [hqker, Subgroup.mem_bot] at h1
    have h2 : b = a := by simpa using congrArg (fun x => a * x) h1
    exact h2.symm
  have hqsurj : Function.Surjective qhom := by
    intro c
    obtain ⟨j, hj⟩ := hsurj c
    exact ⟨QuotientGroup.mk j, by rw [hqhom_mk j, hj]⟩
  refine ⟨MulEquiv.ofBijective qhom ⟨hqinj, hqsurj⟩, fun j => ?_⟩
  have h := congrArg Subtype.val (hqhom_mk j)
  exact h

theorem kgLangS1E_J0_model_twE6
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n) {K₁ : Type} [Field K₁] [Finite K₁]
    (hK₁ : Nat.card K₁ = (2 ^ n) ^ 2)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (hen : e * 3 = n)
    (ρ : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) →*
      ModGL TwistTag.E6.tag L)
    (Θ : ratPts TwistTag.E6.tag L
        (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) →*
      MulAut (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)))
    (hρ : Function.Injective ρ)
    (hρG : ∀ r, ρ r ∈ ratPts TwistTag.E6.tag L
      (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3))
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL TwistTag.E6.tag L) * ρ r *
      (g : ModGL TwistTag.E6.tag L)⁻¹)
    (hFj : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n), orderOf f = 3 →
      ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) =
        (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) j) (ρ r))
    {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃*
      LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n))
    (hcomm : commutator K = ⊤) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ u ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)), kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A)
    (hξI : kgInducedAut θ ξ ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ : k ≃+* k) (ι : k →+* L)
      (g : ModGL TwistTag.E6.tag L),
      Nat.card k = (2 ^ e) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ e) ∧ g ∈ adjointGroup TwistTag.E6.tag L ∧
      ∃ ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom),
        ∀ x ∈ {x : ModGL TwistTag.E6.tag L | x ∈ ratPts TwistTag.E6.tag L
            (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) ∧
          ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
            (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ∧
          ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹},
          ∃ y ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom,
            baseChangeGL (τ := TwistTag.E6.tag) ι y = g⁻¹ * x * g ∧
            ∃ α ∈ A, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
              (ψ (QuotientGroup.mk j') : ModGL TwistTag.E6.tag k) =
                y * ψ (QuotientGroup.mk j) * y⁻¹ := by
  classical
  let R := LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
  letI : Group R := QuotientGroup.Quotient.group
    (Subgroup.center (↥(LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)))
  let I : Set (MulAut R) := LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
    (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
  let F : Set (MulAut R) := LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
    (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
  let F₀ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)
  haveI hcharK : CharP K₁ 2 := charP_two_of_card (m := n * 2) (by rw [hK₁, pow_mul])
  have hstab : ∀ g ∈ adjointGroup TwistTag.E6.tag L, F₀ g ∈ adjointGroup TwistTag.E6.tag L := by
    intro g hg
    show frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L) g ∈
      adjointGroup TwistTag.E6.tag L
    simpa [pow_one] using
      frobTwistGL_diagramMap_pow_mem_adjointGroup (k := L) (p := 2) (e := e) (ε := 1) hg
  obtain ⟨hRsimple, hRnab⟩ := TwE6Dvd.isSimpleGroup_recipeR hn hK₁
  have h3 : ¬ 3 ∣ 2 ^ n + 1 := by
    obtain ⟨j, hj⟩ := heven
    have hmod : 2 ^ n % 3 = 1 := by
      rw [hj, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (2 ^ n + 1)) := by
    have h1 : Nat.gcd 3 (2 ^ n + 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [h1]
    exact Nat.coprime_one_right 3
  have hinn : I ⊆ (MulAut.conj : R →* MulAut R).range := by
    intro φ hφ
    exact TwE6Delta.mem_inn_of_even hn heven hK₁ hφ
  have hconj : GGRawFieldConj 3 R I F :=
    RecipeExcLang.ggRawFieldConj_twE6 (K := K₁) hn hK₁ (p := 3) Nat.prime_three (by norm_num)
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    have hcp : GGCenterPrime 3 R :=
      ggCenterPrime_twE6_of_coprime hn hK₁ Nat.prime_three (by norm_num) hcop
    refine hcp K (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) ?_ ?_ hcomm
    · exact θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : QuotientGroup.mk' (Subgroup.center K) x = 1 := by
        apply θ.injective
        simpa using hx
      exact (QuotientGroup.eq_one_iff x).mp hx'
  obtain ⟨u, hu, f, hf, huf⟩ := hAI ξ hξ
  have hξp3 : ξ ^ 3 = 1 := hA.2 ξ hξ
  have hufI : u * f ∉ I := by rw [← huf]; exact hξI
  have hufp : (u * f) ^ 3 = 1 := by
    rw [← huf, ← map_pow (kgInducedAut θ) ξ 3, hξp3, map_one]
  obtain ⟨u', hu', f', hf'F, hord', heq⟩ :=
    kgLangFieldConj_root (p := 3) hconj hRsimple hRnab hu hf hufI hufp
  have hix : kgInducedAut θ ξ = u' * f' * u'⁻¹ := huf.trans heq
  have hρG' : ∀ r, ρ r ∈ ratPts TwistTag.E6.tag L (endPow F₀ 3) := hρG
  have hFj' : ∀ f ∈ F, orderOf f = 3 → ∃ j : ℕ, ¬ 3 ∣ j ∧
      ∀ r, ρ (f r) = (endPow F₀ j) (ρ r) := hFj
  obtain ⟨g, hgΘ, hiff, honto, hconj4⟩ :=
    kgLangS1E_bridge_fixed (p := 3) (by norm_num) hinn hstab ρ Θ hρ hρG' hΘ hI
      hconjΘ hFj' hu' hf'F hord'
  have hiff' : ∀ r : R, kgInducedAut θ ξ r = r ↔
      (g : ModGL TwistTag.E6.tag L)⁻¹ * ρ r * (g : ModGL TwistTag.E6.tag L) ∈
        ratPts TwistTag.E6.tag L F₀ := by
    intro r
    rw [hix]
    exact hiff r
  have heeven : Even e := by
    have h : Even (e * 3) := by rw [hen]; exact heven
    exact (Nat.even_mul.mp h).resolve_right (by decide)
  obtain ⟨k, hkfield, hkfin, σ, ι, hkcard, hσ, hfixRaw⟩ :=
    kgLangS1E_ratPts_frob_twE6 (L := L) he heeven
  have hfix : ratPts TwistTag.E6.tag L F₀ =
      (graphFixedRootGroup TwistTag.E6 k σ.toRingHom).map (baseChangeGL ι) := by
    change ratPts TwistTag.E6.tag L
      (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) =
      (graphFixedRootGroup TwistTag.E6 k σ.toRingHom).map (baseChangeGL ι)
    exact hfixRaw
  have hgadj : (g : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L := by
    show (g : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L
    exact (Subgroup.mem_inf.mp g.2).1
  let C : Subgroup R := ggFixSub (kgInducedAut θ ξ)
  obtain ⟨e₁, he₁⟩ := kgLangS1EModelTwE6Aux_conj ρ hρ (g : ModGL TwistTag.E6.tag L) C
    (ratPts TwistTag.E6.tag L F₀) (fun r => mem_ggFixSub.trans (hiff' r)) (fun y hy => by
      obtain ⟨r, hr, hry⟩ := honto y hy
      refine ⟨r, mem_ggFixSub.mpr ?_, hry⟩
      rw [hix]
      exact hr)
  obtain ⟨e₂, he₂⟩ := kgLangS1EModelTwE6Aux_base ι
    (graphFixedRootGroup TwistTag.E6 k σ.toRingHom) (ratPts TwistTag.E6.tag L F₀) hfix
  let eC : ↥C ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) := e₁.trans e₂.symm
  have hbase_φ : ∀ r : ↥C,
      baseChangeGL (τ := TwistTag.E6.tag) ι (eC r : ModGL TwistTag.E6.tag k) =
        (g : ModGL TwistTag.E6.tag L)⁻¹ * ρ (r : R) * (g : ModGL TwistTag.E6.tag L) := by
    intro r
    show baseChangeGL (τ := TwistTag.E6.tag) ι
        ((e₂.symm (e₁ r) : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) :
          ModGL TwistTag.E6.tag k) = _
    rw [← he₂ (e₂.symm (e₁ r)), MulEquiv.apply_symm_apply, he₁ r]
  obtain ⟨hperf, -, -, -, -⟩ :=
    finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two he k hkcard σ.toRingHom hσ
  obtain ⟨hsimple_graph, hna_graph⟩ :=
    isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.E6 k σ hperf
  have hCs : IsSimpleGroup ↥C := by
    haveI : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) := hsimple_graph
    exact eC.isSimpleGroup
  have hCna : ∃ a b : ↥C, a * b ≠ b * a :=
    kgLangS1EModelTwE6Aux_nonabelian eC.symm hna_graph
  obtain ⟨hcov1, hcov2, hcov3, hcov4⟩ :=
    kgLangS1E_component_cover (p := 3) (by norm_num) θ hZ hξp3 hCs hCna hJ₀
  obtain ⟨qiso, hqiso⟩ := kgLangS1EModelTwE6Aux_quot θ J₀ C hcov1 hcov2 hcov3
  let ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) := qiso.trans eC
  have hbase_ψ : ∀ j : ↥J₀,
      baseChangeGL (τ := TwistTag.E6.tag) ι (ψ (QuotientGroup.mk j) : ModGL TwistTag.E6.tag k) =
        (g : ModGL TwistTag.E6.tag L)⁻¹ * ρ (θ (QuotientGroup.mk (j : K))) *
          (g : ModGL TwistTag.E6.tag L) := by
    intro j
    show baseChangeGL (τ := TwistTag.E6.tag) ι (eC (qiso (QuotientGroup.mk j)) :
        ModGL TwistTag.E6.tag k) = _
    rw [hbase_φ, hqiso j]
  refine ⟨k, hkfield, hkfin, σ, ι, (g : ModGL TwistTag.E6.tag L), hkcard, hσ, hgadj, ψ, ?_⟩
  intro x hx
  obtain ⟨hxmem, α, hαA, hαI, hxconj⟩ := hx
  have hΘx : Θ ⟨x, hxmem⟩ = kgInducedAut θ α := by
    ext r
    apply hρ
    rw [hconjΘ ⟨x, hxmem⟩ r, hxconj r]
  have hcommαξ : α * ξ = ξ * α := by
    have h : (⟨α, hαA⟩ : ↥A) * ⟨ξ, hξ⟩ = ⟨ξ, hξ⟩ * ⟨α, hαA⟩ :=
      (isMulCommutative_iff.mp hA.1) _ _
    simpa using congrArg Subtype.val h
  have hcommΘ : Θ ⟨x, hxmem⟩ * (u' * f' * u'⁻¹) =
      (u' * f' * u'⁻¹) * Θ ⟨x, hxmem⟩ := by
    rw [hΘx, ← hix, ← map_mul, ← map_mul, hcommαξ]
  have hgx : (g : ModGL TwistTag.E6.tag L)⁻¹ * x * (g : ModGL TwistTag.E6.tag L) ∈
      ratPts TwistTag.E6.tag L F₀ :=
    hconj4 ⟨x, hxmem⟩ hcommΘ
  have hy : (g : ModGL TwistTag.E6.tag L)⁻¹ * x * (g : ModGL TwistTag.E6.tag L) ∈
      (graphFixedRootGroup TwistTag.E6 k σ.toRingHom).map
        (baseChangeGL (τ := TwistTag.E6.tag) ι) := hfix ▸ hgx
  obtain ⟨y, hy_mem, hy_eq⟩ := Subgroup.mem_map.mp hy
  refine ⟨y, hy_mem, hy_eq, ?_⟩
  refine ⟨α, hαA, fun j => ?_⟩
  let j' : ↥J₀ := ⟨α (j : K), hcov4 α hcommαξ (j : K) j.2⟩
  refine ⟨j', rfl, ?_⟩
  apply baseChangeGL_injective (τ := TwistTag.E6.tag) ι
  rw [hbase_ψ j', map_mul, map_mul, map_inv, hy_eq, hbase_ψ j]
  have hgroup : (g : ModGL TwistTag.E6.tag L)⁻¹ * x * (g : ModGL TwistTag.E6.tag L) *
        ((g : ModGL TwistTag.E6.tag L)⁻¹ * ρ (θ (QuotientGroup.mk (j : K))) *
          (g : ModGL TwistTag.E6.tag L)) *
        ((g : ModGL TwistTag.E6.tag L)⁻¹ * x * (g : ModGL TwistTag.E6.tag L))⁻¹ =
      (g : ModGL TwistTag.E6.tag L)⁻¹ * (x * ρ (θ (QuotientGroup.mk (j : K))) * x⁻¹) *
        (g : ModGL TwistTag.E6.tag L) := by group
  have hαapply : (kgInducedAut θ α) (θ (QuotientGroup.mk (j : K))) =
      θ (QuotientGroup.mk (α (j : K))) := by
    simp [kgInducedAut, MulAut.congr_apply, centerQuotAut_mk]
  have hxρ : x * ρ (θ (QuotientGroup.mk (j : K))) * x⁻¹ =
      ρ (θ (QuotientGroup.mk (α (j : K)))) :=
    (hxconj (θ (QuotientGroup.mk (j : K)))).symm.trans (congrArg ρ hαapply)
  rw [hgroup, hxρ]

end CFSG.StandardType
