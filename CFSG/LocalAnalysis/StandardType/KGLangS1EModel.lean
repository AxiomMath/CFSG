module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EBridgeFix
public import CFSG.LocalAnalysis.StandardType.KGLangS1ECover
public import CFSG.LocalAnalysis.StandardType.KGLangS1ENormalForm
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121

import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInner
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc

private theorem kgLangS1EModelAux_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

theorem kgLangS1E_J0_model_E7
    {n : ℕ} (hn : 1 ≤ n) {K₁ : Type} [Field K₁] [Finite K₁] (hK₁ : Nat.card K₁ = 2 ^ n)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) {Q : ModGL .E7 L}
    (hQ : IsDiagramTwistMatrix .E7 L Q)
    (ρ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false) →* ModGL .E7 L)
    (Θ : ratPts .E7 L (endPow (frobTwistGL .E7 L 2 e Q) 3) →*
      MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)))
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts .E7 L (endPow (frobTwistGL .E7 L 2 e Q) 3))
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 7) K₁
      (LargeEvenChevH (LargeEvenCartanE 7) K₁ false) ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL .E7 L) * ρ r * (g : ModGL .E7 L)⁻¹)
    (hFj : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 7) K₁
        (LargeEvenChevH (LargeEvenCartanE 7) K₁ false), orderOf f = 3 →
      ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) = (endPow (frobTwistGL .E7 L 2 e Q) j) (ρ r))
    {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false))
    (hcomm : commutator K = ⊤) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ u ∈ LargeEvenChevIDImage (LargeEvenCartanE 7) K₁
        (LargeEvenChevH (LargeEvenCartanE 7) K₁ false),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage (LargeEvenCartanE 7) K₁
        (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)), kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A)
    (hξI : kgInducedAut θ ξ ∉ LargeEvenChevIDImage (LargeEvenCartanE 7) K₁
      (LargeEvenChevH (LargeEvenCartanE 7) K₁ false))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* L) (g : ModGL .E7 L),
      Nat.card k = 2 ^ e ∧ g ∈ adjointGroup .E7 L ∧
      ∃ ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥(adjointGroup .E7 k),
        ∀ x ∈ {x : ModGL .E7 L | x ∈ ratPts .E7 L (endPow (frobTwistGL .E7 L 2 e Q) 3) ∧
            ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 7) K₁
              (LargeEvenChevH (LargeEvenCartanE 7) K₁ false) ∧
            ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹},
          ∃ y ∈ adjointGroup .E7 k, baseChangeGL (τ := .E7) ι y = g⁻¹ * x * g ∧
            ∃ α ∈ A, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
              (ψ (QuotientGroup.mk j') : ModGL .E7 k) = y * ψ (QuotientGroup.mk j) * y⁻¹ := by
  classical
  let R := LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)
  let I : Set (MulAut R) := LargeEvenChevIDImage (LargeEvenCartanE 7) K₁
    (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)
  let F : Set (MulAut R) := LargeEvenChevFieldImage (LargeEvenCartanE 7) K₁
    (LargeEvenChevH (LargeEvenCartanE 7) K₁ false)
  let F₀ : ModGL .E7 L →* ModGL .E7 L := frobTwistGL .E7 L 2 e Q
  haveI hcharK : CharP K₁ 2 := charP_two_of_card hK₁
  have hQ1 : Q = 1 := by
    rcases hQ with h | ⟨t, j, ht, h⟩
    · exact h
    · exact absurd ht (by cases t <;> decide)
  have hstab : ∀ g ∈ adjointGroup .E7 L, F₀ g ∈ adjointGroup .E7 L := by
    intro g hg
    show frobTwistGL .E7 L 2 e Q g ∈ adjointGroup .E7 L
    rw [frobTwistGL_apply, hQ1]
    simpa using (entrywiseFrobGL_mem (p := 2) (e := e) hg)
  have hq₁ : CFSG.IsQuasisimple ↥(adjointGroup .E7 K₁) :=
    chev_isQuasisimple (τ := .E7) (Or.inr (Or.inl rfl)) K₁
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K₁ .E7
  have hRsimple : IsSimpleGroup R := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E7 K₁) := hq₁.2.1
    exact eQ.isSimpleGroup
  have hRnab : ∃ a b : R, a * b ≠ b * a :=
    kgLangS1EModelAux_nonabelian eQ.symm hq₁.2.2
  have hT : TableB.torusSubgroup (LargeEvenCartanE 7) K₁ = ⊤ :=
    TableB.torusSubgroup_eq_top_of_mul_eq_smul (LargeEvenCartanE 7) K₁
      TableB.cartanE7_adj (TableB.exists_sq_eq_of_charTwo K₁)
  have hinn : I ⊆ (MulAut.conj : R →* MulAut R).range :=
    chevIDImage_subset_inn_of_top (K := K₁) (τ := .E7) hT
  have hinner : RecipeExcLang.InnerFieldTrivial .E7 K₁ :=
    RecipeExcLang.innerFieldTrivial_E7_E8 (f := n) hn hK₁ (Or.inl rfl)
  have hconj : GGRawFieldConj 3 R I F :=
    RecipeExcLang.ggRawFieldConj_chev_two (K := K₁) (n := n) (p := 3) hn hK₁
      (by norm_num) hinner
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    have hcp : GGCenterPrime 3 R :=
      ExcSplitL.ggCenterPrime_recipe_E7 (f := n) hn hK₁ (p := 3)
        (by norm_num) (by norm_num)
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
  have hρG' : ∀ r, ρ r ∈ ratPts .E7 L (endPow F₀ 3) := hρG
  have hFj' : ∀ f ∈ F, orderOf f = 3 → ∃ j : ℕ, ¬ 3 ∣ j ∧
      ∀ r, ρ (f r) = (endPow F₀ j) (ρ r) := hFj
  obtain ⟨g, hgΘ, hiff, honto, hconj4⟩ :=
    kgLangS1E_bridge_fixed (p := 3) (by norm_num) hinn hstab ρ Θ hρ hρG' hΘ hI
      hconjΘ hFj' hu' hf'F hord'
  have hiff' : ∀ r : R, kgInducedAut θ ξ r = r ↔
      (g : ModGL .E7 L)⁻¹ * ρ r * (g : ModGL .E7 L) ∈ ratPts .E7 L F₀ := by
    intro r
    rw [hix]
    exact hiff r
  obtain ⟨k, hkfield, hkfin, ι, hkcard, hfixRaw⟩ := kgLangS1E_ratPts_frob_E7 he hQ
  have hfix : ratPts .E7 L F₀ = (adjointGroup .E7 k).map (baseChangeGL ι) := by
    change ratPts .E7 L (frobTwistGL .E7 L 2 e Q) =
      (adjointGroup .E7 k).map (baseChangeGL ι)
    exact hfixRaw
  have hgadj : (g : ModGL .E7 L) ∈ adjointGroup .E7 L := by
    show (g : ModGL .E7 L) ∈ adjointGroup .E7 L
    exact (Subgroup.mem_inf.mp g.2).1
  let C : Subgroup R := ggFixSub (kgInducedAut θ ξ)
  let φh : ↥C →* ↥(ratPts .E7 L F₀) :=
    { toFun := fun r => ⟨(g : ModGL .E7 L)⁻¹ * ρ (r : R) * (g : ModGL .E7 L),
        (hiff' (r : R)).mp (mem_ggFixSub.mp r.2)⟩
      map_one' := Subtype.ext (by
        show (g : ModGL .E7 L)⁻¹ * ρ (1 : R) * (g : ModGL .E7 L) = 1
        simp)
      map_mul' := fun a b => Subtype.ext (by
        show (g : ModGL .E7 L)⁻¹ * ρ ((a : R) * (b : R)) * (g : ModGL .E7 L) =
          ((g : ModGL .E7 L)⁻¹ * ρ (a : R) * (g : ModGL .E7 L)) *
            ((g : ModGL .E7 L)⁻¹ * ρ (b : R) * (g : ModGL .E7 L))
        rw [map_mul]
        group) }
  have hφh_apply : ∀ r : ↥C, (φh r : ModGL .E7 L) =
      (g : ModGL .E7 L)⁻¹ * ρ (r : R) * (g : ModGL .E7 L) := fun r => rfl
  have hφh_inj : Function.Injective φh := by
    intro a b hab
    apply Subtype.ext
    apply hρ
    have h : (g : ModGL .E7 L)⁻¹ * ρ (a : R) * (g : ModGL .E7 L) =
        (g : ModGL .E7 L)⁻¹ * ρ (b : R) * (g : ModGL .E7 L) := by
      rw [← hφh_apply a, ← hφh_apply b, hab]
    have h2 := congrArg (fun z => (g : ModGL .E7 L) * z * (g : ModGL .E7 L)⁻¹) h
    simpa [mul_assoc] using h2
  have hφh_surj : Function.Surjective φh := by
    intro y
    obtain ⟨r, hr, hy⟩ := honto (y : ModGL .E7 L) y.2
    refine ⟨⟨r, mem_ggFixSub.mpr ?_⟩, Subtype.ext hy⟩
    rw [hix]
    exact hr
  let eBaseHom : ↥(adjointGroup .E7 k) →* ↥(ratPts .E7 L F₀) :=
    ((baseChangeGL (τ := .E7) ι).comp (adjointGroup .E7 k).subtype).codRestrict
      (ratPts .E7 L F₀) (by
        intro y
        show baseChangeGL (τ := .E7) ι (y : ModGL .E7 k) ∈ ratPts .E7 L F₀
        rw [hfix]
        exact Subgroup.mem_map.mpr ⟨(y : ModGL .E7 k), y.2, rfl⟩)
  have heBase_inj : Function.Injective eBaseHom := by
    intro a b hab
    apply Subtype.ext
    apply baseChangeGL_injective (τ := .E7) ι
    simpa [eBaseHom] using
      congrArg (fun z : ↥(ratPts .E7 L F₀) => (z : ModGL .E7 L)) hab
  have heBase_surj : Function.Surjective eBaseHom := by
    intro z
    have hz : (z : ModGL .E7 L) ∈ (adjointGroup .E7 k).map (baseChangeGL (τ := .E7) ι) := by
      rw [← hfix]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [eBaseHom] using hyz)⟩
  let eBase : ↥(adjointGroup .E7 k) ≃* ↥(ratPts .E7 L F₀) :=
    MulEquiv.ofBijective eBaseHom ⟨heBase_inj, heBase_surj⟩
  let eC : ↥C ≃* ↥(adjointGroup .E7 k) :=
    (MulEquiv.ofBijective φh ⟨hφh_inj, hφh_surj⟩).trans eBase.symm
  have hbase_φ : ∀ r : ↥C,
      baseChangeGL (τ := .E7) ι (eC r : ModGL .E7 k) =
        (g : ModGL .E7 L)⁻¹ * ρ (r : R) * (g : ModGL .E7 L) := by
    intro r
    have h1 : (eBaseHom (eBase.symm (φh r)) : ModGL .E7 L) = (φh r : ModGL .E7 L) :=
      congrArg Subtype.val (eBase.apply_symm_apply (φh r))
    exact h1.trans (hφh_apply r)
  let ebot : (↥(adjointGroup .E7 k) ⧸ Subgroup.center ↥(adjointGroup .E7 k)) ≃*
      ↥(adjointGroup .E7 k) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := k))).trans
      QuotientGroup.quotientBot
  have hq_k : CFSG.IsQuasisimple ↥(adjointGroup .E7 k) :=
    chev_isQuasisimple (τ := .E7) (Or.inr (Or.inl rfl)) k
  have hCs : IsSimpleGroup ↥C := by
    haveI : IsSimpleGroup (↥(adjointGroup .E7 k) ⧸
        Subgroup.center ↥(adjointGroup .E7 k)) := hq_k.2.1
    exact (eC.trans ebot.symm).isSimpleGroup
  have hCna : ∃ a b : ↥C, a * b ≠ b * a :=
    kgLangS1EModelAux_nonabelian (eC.trans ebot.symm).symm hq_k.2.2
  obtain ⟨hcov1, hcov2, hcov3, hcov4⟩ :=
    kgLangS1E_component_cover (p := 3) (by norm_num) θ hZ hξp3 hCs hCna hJ₀
  let fbase : ↥J₀ →* ↥C :=
    { toFun := fun j => ⟨θ (QuotientGroup.mk (j : K)), hcov1 (j : K) j.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  have hsurj : Function.Surjective fbase := by
    intro c
    obtain ⟨j, hj, hjc⟩ := hcov2 (c : R) c.2
    exact ⟨⟨j, hj⟩, Subtype.ext hjc⟩
  have hker : fbase.ker = Subgroup.center ↥J₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx g
      have hx1 : θ (QuotientGroup.mk (x : K)) = 1 := congrArg Subtype.val hx
      exact Subtype.ext ((hcov3 (x : K) x.2).mp hx1 (g : K) g.2).symm
    · intro hx
      apply Subtype.ext
      show θ (QuotientGroup.mk (x : K)) = 1
      exact (hcov3 (x : K) x.2).mpr (fun j' hj' =>
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
      exact Subtype.ext ((hcov3 (j : K) j.2).mp hx1 (g : K) g.2).symm
    · intro hj
      apply Subtype.ext
      show θ (QuotientGroup.mk (j : K)) = 1
      exact (hcov3 (j : K) j.2).mpr (fun j' hj' =>
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
  let qiso : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥C :=
    MulEquiv.ofBijective qhom ⟨hqinj, hqsurj⟩
  let ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥(adjointGroup .E7 k) := qiso.trans eC
  have hψ_mk : ∀ j : ↥J₀, ψ (QuotientGroup.mk j) = eC (fbase j) := by
    intro j
    show eC (qhom (QuotientGroup.mk j)) = eC (fbase j)
    rw [hqhom_mk j]
  have hbase_ψ : ∀ j : ↥J₀,
      baseChangeGL (τ := .E7) ι (ψ (QuotientGroup.mk j) : ModGL .E7 k) =
        (g : ModGL .E7 L)⁻¹ * ρ (θ (QuotientGroup.mk (j : K))) * (g : ModGL .E7 L) := by
    intro j
    rw [hψ_mk j, hbase_φ (fbase j)]
    rfl
  refine ⟨k, hkfield, hkfin, ι, (g : ModGL .E7 L), hkcard, hgadj, ψ, ?_⟩
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
  have hgx : (g : ModGL .E7 L)⁻¹ * x * (g : ModGL .E7 L) ∈ ratPts .E7 L F₀ :=
    hconj4 ⟨x, hxmem⟩ hcommΘ
  have hy : (g : ModGL .E7 L)⁻¹ * x * (g : ModGL .E7 L) ∈
      (adjointGroup .E7 k).map (baseChangeGL (τ := .E7) ι) := hfix ▸ hgx
  obtain ⟨y, hy_mem, hy_eq⟩ := Subgroup.mem_map.mp hy
  refine ⟨y, hy_mem, hy_eq, ?_⟩
  refine ⟨α, hαA, fun j => ?_⟩
  let j' : ↥J₀ := ⟨α (j : K), hcov4 α hcommαξ (j : K) j.2⟩
  refine ⟨j', rfl, ?_⟩
  apply baseChangeGL_injective (τ := .E7) ι
  rw [hbase_ψ j', map_mul, map_mul, map_inv, hy_eq, hbase_ψ j]
  have hgroup : (g : ModGL .E7 L)⁻¹ * x * (g : ModGL .E7 L) *
        ((g : ModGL .E7 L)⁻¹ * ρ (θ (QuotientGroup.mk (j : K))) * (g : ModGL .E7 L)) *
        ((g : ModGL .E7 L)⁻¹ * x * (g : ModGL .E7 L))⁻¹ =
      (g : ModGL .E7 L)⁻¹ * (x * ρ (θ (QuotientGroup.mk (j : K))) * x⁻¹) *
        (g : ModGL .E7 L) := by group
  have hαapply : (kgInducedAut θ α) (θ (QuotientGroup.mk (j : K))) =
      θ (QuotientGroup.mk (α (j : K))) := by
    simp [kgInducedAut, MulAut.congr_apply, centerQuotAut_mk]
  have hxρ : x * ρ (θ (QuotientGroup.mk (j : K))) * x⁻¹ =
      ρ (θ (QuotientGroup.mk (α (j : K)))) := by
    rw [← hαapply, hxconj (θ (QuotientGroup.mk (j : K)))]
  rw [hgroup, hxρ]

end CFSG.StandardType
