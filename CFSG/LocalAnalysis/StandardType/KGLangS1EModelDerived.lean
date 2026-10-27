module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EBridgeFix
public import CFSG.LocalAnalysis.StandardType.KGLangS1ECover
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagDiag
import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Cover
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Basic
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.C14Exc

theorem chevIDImage_commutator_mem_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type}
    [Field K] {H : Subgroup (LargeEvenChevGL A K)} {φ₁ φ₂ : MulAut (LargeEvenCenterQuot H)}
    (h₁ : φ₁ ∈ LargeEvenChevIDImage A K H) (h₂ : φ₂ ∈ LargeEvenChevIDImage A K H) :
    φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹ ∈
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
  set N := (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range with hN
  set π := QuotientGroup.mk' N with hπ
  set S : Set (MulAut (LargeEvenCenterQuot H) ⧸ N) :=
    π '' LargeEvenChevDiagImage A K H with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨φ₁, h₁, rfl⟩ _ ⟨φ₂, h₂, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    obtain ⟨b, hb⟩ := TableB.exists_isDiagOf h₂
    change π φ₁ * π φ₂ = π φ₂ * π φ₁
    rw [← map_mul, ← map_mul, TableBExc.isDiagOf_comm ha hb]
  have hcS : ∀ x ∈ Subgroup.closure S, ∀ s ∈ S, Commute x s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact fun s hs => hcomm y hy s hs
    | one => exact fun s _ => Commute.one_left s
    | mul y z _ _ hy hz => exact fun s hs => (hy s hs).mul_left (hz s hs)
    | inv y _ hy => exact fun s hs => (hy s hs).inv_left
  have hcC : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hcS x hx z hz
    | one => exact Commute.one_right x
    | mul z w _ _ hz hw => exact hz.mul_right hw
    | inv z _ hz => exact hz.inv_right
  have hle : Subgroup.closure (LargeEvenInnSet (LargeEvenCenterQuot H) ∪
      LargeEvenChevDiagImage A K H) ≤ (Subgroup.closure S).comap π := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · show π (MulAut.conj x) ∈ Subgroup.closure S
      have hx : MulAut.conj x ∈ N := ⟨x, rfl⟩
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hx]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨ψ, hψ, rfl⟩
  have h1 : π φ₁ ∈ Subgroup.closure S := hle h₁
  have h2 : π φ₂ ∈ Subgroup.closure S := hle h₂
  have hcomm12 := (hcC (π φ₁) h1 (π φ₂) h2).eq
  exact (QuotientGroup.eq_one_iff _).mp (by
    change π (φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm12]
    group)

theorem kgLangS1E_bridge_commutator_mem {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hcommI : ∀ φ₁ ∈ I, ∀ φ₂ ∈ I,
      φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹ ∈ (MulAut.conj : R →* MulAut R).range)
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    (ρ : R →* ModGL τ L) (Θ : ratPts τ L (endPow F₀ p) →* MulAut R)
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts τ L (endPow F₀ p))
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL τ L) * ρ r * (g : ModGL τ L)⁻¹)
    (x₁ x₂ : ratPts τ L (endPow F₀ p)) :
    ∃ r : R, ρ r = (x₁ : ModGL τ L) * (x₂ : ModGL τ L) * (x₁ : ModGL τ L)⁻¹ *
      (x₂ : ModGL τ L)⁻¹ := by
  have hI₁ : Θ x₁ ∈ I := (hI (Θ x₁)).2 ⟨x₁, rfl⟩
  have hI₂ : Θ x₂ ∈ I := (hI (Θ x₂)).2 ⟨x₂, rfl⟩
  obtain ⟨r, hr⟩ := hcommI (Θ x₁) hI₁ (Θ x₂) hI₂
  refine ⟨r, ?_⟩
  have heq : Θ ⟨ρ r, hρG r⟩ = Θ (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [absBridge_theta_rho hρ hρG hconjΘ r]
    exact hr
  simpa using congrArg Subtype.val (hΘ heq)

private theorem kgLangS1EModelDerivedAux_induced_mk {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (ξ : MulAut K) (q : K ⧸ Subgroup.center K) :
    kgInducedAut θ ξ (θ q) = θ (centerQuotAut K ξ q) := by
  simp [kgInducedAut, MulAut.congr_apply]

private theorem kgLangS1EModelDerivedAux_nonabelian {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private theorem kgLangS1EModelDerivedAux_isSimpleNonAbelian_impliesQuasisimple {D : Type*}
    [Group D] [IsSimpleGroup D] (hDna : ∃ a b : D, a * b ≠ b * a) :
    CFSG.IsQuasisimple D :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDna).1

theorem kgLangS1E_component_cover_derived {R : Type} [Group R]
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) {ξ : MulAut K}
    (hDs : IsSimpleGroup ↥⁅ggFixSub (kgInducedAut θ ξ), ggFixSub (kgInducedAut θ ξ)⁆)
    (hDna : ∃ a b : ↥⁅ggFixSub (kgInducedAut θ ξ), ggFixSub (kgInducedAut θ ξ)⁆,
      a * b ≠ b * a)
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    (∀ j ∈ J₀, θ (QuotientGroup.mk j) ∈
      ⁅ggFixSub (kgInducedAut θ ξ), ggFixSub (kgInducedAut θ ξ)⁆) ∧
    (∀ r ∈ ⁅ggFixSub (kgInducedAut θ ξ), ggFixSub (kgInducedAut θ ξ)⁆,
      ∃ j ∈ J₀, θ (QuotientGroup.mk j) = r) ∧
    (∀ j ∈ J₀, θ (QuotientGroup.mk j) = 1 ↔ ∀ j' ∈ J₀, j * j' = j' * j) ∧
    ∀ α : MulAut K, α * ξ = ξ * α → ∀ j ∈ J₀, α j ∈ J₀ := by
  classical
  let C : Subgroup R := ggFixSub (kgInducedAut θ ξ)
  let Cder : Subgroup R := ⁅C, C⁆
  let ψ' : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hψ'_apply : ∀ l, ψ' l = θ (QuotientGroup.mk l) := fun l => rfl
  have hψ'_surj : Function.Surjective ψ' := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, by rw [hψ'_apply l, hl, hq]⟩
  have hker : ψ'.ker ≤ Subgroup.center K := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : θ (QuotientGroup.mk l) = 1 := by
      rw [← hψ'_apply l]
      exact hl
    have h2 : QuotientGroup.mk l = 1 := θ.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff l).mp h2
  have hab : ∀ l, kgInducedAut θ ξ (ψ' l) = ψ' (ξ l) := by
    intro l
    change kgInducedAut θ ξ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (ξ l))
    rw [kgLangS1EModelDerivedAux_induced_mk θ ξ (QuotientGroup.mk l), centerQuotAut_mk]
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  have hDs' : IsSimpleGroup ↥Cder := hDs
  have : IsSimpleGroup ↥Cder := hDs'
  have hDna' : ∃ a b : ↥Cder, a * b ≠ b * a := hDna
  have hq : CFSG.IsQuasisimple ↥Cder :=
    kgLangS1EModelDerivedAux_isSimpleNonAbelian_impliesQuasisimple hDna'
  have hmap_eq : ∀ {J : Subgroup K}, IsComponentOf J (ggFixSub ξ) → J.map ψ' = Cder := by
    intro J hJ
    have hJ' : IsComponentOf J (ggFix ξ) := hJ
    have hJmap : IsComponentOf (J.map ψ') C :=
      E6ThreeModel.isComponentOf_map_ggFix_of_central hψ'_surj hker hab hJ'
    have hq' : CFSG.IsQuasisimple ↥⁅C, C⁆ := hq
    exact F4Nonsplit.eq_commutator_of_isComponentOf hq' hJmap
  have honto_of_comp : ∀ {J : Subgroup K}, IsComponentOf J (ggFixSub ξ) →
      ∀ r ∈ Cder, ∃ j ∈ J, θ (QuotientGroup.mk j) = r := by
    intro J hJ r hr
    have hmap := hmap_eq hJ
    have hr' : r ∈ J.map ψ' := by rwa [hmap]
    obtain ⟨j, hj, hjeq⟩ := hr'
    exact ⟨j, hj, hjeq⟩
  have hcov1 : ∀ j ∈ J₀, θ (QuotientGroup.mk j) ∈ Cder := by
    intro j hj
    have h : θ (QuotientGroup.mk j) ∈ J₀.map ψ' := ⟨j, hj, rfl⟩
    rwa [hmap_eq hJ₀] at h
  have hcov2 : ∀ r ∈ Cder, ∃ j ∈ J₀, θ (QuotientGroup.mk j) = r :=
    fun r hr => honto_of_comp hJ₀ r hr
  have hcenter_bot : Subgroup.center ↥Cder = ⊥ := by
    rcases hDs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Cder) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab'⟩ := hDna
      exact hab'
        (Subgroup.mem_center_iff.mp (by rw [h]; trivial : a ∈ Subgroup.center ↥Cder) b).symm
  have hcov3 : ∀ j ∈ J₀, θ (QuotientGroup.mk j) = 1 ↔ ∀ j' ∈ J₀, j * j' = j' * j := by
    intro j hj
    constructor
    · intro h1 j' hj'
      have hmk : QuotientGroup.mk j = 1 := θ.injective (by rw [h1, map_one])
      exact (Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff j).mp hmk) j').symm
    · intro hcomm
      have hcen : (⟨θ (QuotientGroup.mk j), hcov1 j hj⟩ : ↥Cder) ∈ Subgroup.center ↥Cder := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨j', hj', hj'eq⟩ := hcov2 (r : R) r.2
        apply Subtype.ext
        change (r : R) * θ (QuotientGroup.mk j) = θ (QuotientGroup.mk j) * (r : R)
        rw [← hj'eq, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rw [hcomm j' hj']
      rw [hcenter_bot, Subgroup.mem_bot] at hcen
      exact Subtype.ext_iff.mp hcen
  refine ⟨hcov1, hcov2, hcov3, ?_⟩
  intro α hα j hj
  have hfixα : (ggFixSub ξ).map α.toMonoidHom = ggFixSub ξ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : ξ y = y := by simpa using hy
      change ξ (α y) = α y
      calc ξ (α y) = (ξ * α) y := rfl
        _ = (α * ξ) y := by rw [hα]
        _ = α (ξ y) := rfl
        _ = α y := by rw [hy']
    · intro hx
      refine ⟨α.symm x, ?_, by simp⟩
      have hx' : ξ x = x := by simpa using hx
      change ξ (α.symm x) = α.symm x
      have hαsymm : α.symm * ξ = ξ * α.symm := by
        change α⁻¹ * ξ = ξ * α⁻¹
        calc α⁻¹ * ξ = α⁻¹ * (ξ * α) * α⁻¹ := by group
          _ = α⁻¹ * (α * ξ) * α⁻¹ := by rw [hα]
          _ = ξ * α⁻¹ := by group
      calc ξ (α.symm x) = (ξ * α.symm) x := rfl
        _ = (α.symm * ξ) x := by rw [hαsymm]
        _ = α.symm (ξ x) := rfl
        _ = α.symm x := by rw [hx']
  have hcomp : IsComponentOf (J₀.map α.toMonoidHom) (ggFixSub ξ) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hfixα]
      exact Subgroup.map_mono hJ₀.1
    · rw [← hfixα]
      exact Assembly.IsSubnormal.map α.toMonoidHom hJ₀.2.1
    · exact Assembly.IsQuasisimple.of_mulEquiv
        (J₀.equivMapOfInjective α.toMonoidHom α.injective).symm hJ₀.2.2
  by_cases heq : J₀.map α.toMonoidHom = J₀
  · have : α j ∈ J₀.map α.toMonoidHom := ⟨j, hj, rfl⟩
    rwa [heq] at this
  · exfalso
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ₀ hcomp with h | h
    · exact heq h.symm
    · have hcomm : ∀ a ∈ J₀, ∀ b ∈ J₀.map α.toMonoidHom, a * b = b * a := by
        intro a ha b hb
        have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅J₀, J₀.map α.toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator ha hb
        rw [h, Subgroup.mem_bot] at hmem
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [hmem, one_mul]
      have hDabel : ∀ r s : ↥Cder, r * s = s * r := by
        intro r s
        apply Subtype.ext
        obtain ⟨a, ha, haeq⟩ := honto_of_comp hJ₀ (r : R) r.2
        obtain ⟨b, hb, hbeq⟩ := honto_of_comp hcomp (s : R) s.2
        change (r : R) * (s : R) = (s : R) * (r : R)
        rw [← haeq, ← hbeq, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul]
        rw [hcomm a ha b hb]
      obtain ⟨a, b, hab'⟩ := hDna
      exact hab' (hDabel a b)

private theorem kgLangS1EModelDerivedAux_quot {K R : Type} [Group K] [Group R]
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

theorem kgLangS1E_J0_model_derived
    {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hcommI : ∀ φ₁ ∈ I, ∀ φ₂ ∈ I,
      φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹ ∈ (MulAut.conj : R →* MulAut R).range)
    (hconj : GGRawFieldConj p R I F) (hRs : IsSimpleGroup R) (hRna : ∃ a b : R, a * b ≠ b * a)
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    (hstab : ∀ g ∈ adjointGroup τ L, F₀ g ∈ adjointGroup τ L)
    (ρ : R →* ModGL τ L) (Θ : ratPts τ L (endPow F₀ p) →* MulAut R)
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts τ L (endPow F₀ p))
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL τ L) * ρ r * (g : ModGL τ L)⁻¹)
    (hFj : ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r))
    {k : Type} [Field k] (ι : k →+* L) (Γ T : Subgroup (ModGL τ k))
    (hfix : ratPts τ L F₀ = Γ.map (baseChangeGL ι)) (hTΓ : T ≤ Γ) (hΓT : ⁅Γ, Γ⁆ ≤ T)
    (hTperf : ⁅T, T⁆ = T) (hTs : IsSimpleGroup ↥T) (hTna : ∃ a b : ↥T, a * b ≠ b * a)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A)
    (hAI : ∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A) (hξI : kgInducedAut θ ξ ∉ I)
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    ∃ g : ModGL τ L, g ∈ adjointGroup τ L ∧
      ∃ ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥T,
        ∀ x ∈ {x : ModGL τ L | x ∈ ratPts τ L (endPow F₀ p) ∧
            ∃ α ∈ A, kgInducedAut θ α ∈ I ∧ ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹},
          ∃ y ∈ Γ, baseChangeGL (τ := τ) ι y = g⁻¹ * x * g ∧
            ∃ α ∈ A, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
              (ψ (QuotientGroup.mk j') : ModGL τ k) = y * ψ (QuotientGroup.mk j) * y⁻¹ := by
  classical
  obtain ⟨u, hu, f, hf, huf⟩ := hAI ξ hξ
  have hξp : ξ ^ p = 1 := hA.2 ξ hξ
  have hufI : u * f ∉ I := by rw [← huf]; exact hξI
  have hufp : (u * f) ^ p = 1 := by
    rw [← huf, ← map_pow (kgInducedAut θ) ξ p, hξp, map_one]
  obtain ⟨u', hu', f', hf'F, hord', heq⟩ :=
    kgLangFieldConj_root hconj hRs hRna hu hf hufI hufp
  have hix : kgInducedAut θ ξ = u' * f' * u'⁻¹ := huf.trans heq
  obtain ⟨g, hgΘ, hiff, hconj3⟩ :=
    kgLangS1E_bridge_fixed_inndiag hp hstab ρ Θ hρ hρG hΘ hI hconjΘ hFj hu' hf'F hord'
  have hiff' : ∀ r : R, kgInducedAut θ ξ r = r ↔
      (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) ∈ ratPts τ L F₀ := by
    intro r
    rw [hix]
    exact hiff r
  have hgadj : (g : ModGL τ L) ∈ adjointGroup τ L := (Subgroup.mem_inf.mp g.2).1
  let C : Subgroup R := ggFixSub (kgInducedAut θ ξ)
  let φ' : R →* ModGL τ L := (MulAut.conj (g : ModGL τ L)⁻¹).toMonoidHom.comp ρ
  have hφ'_apply : ∀ r, φ' r = (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) := by
    intro r
    simp [φ']
  have hφ'_inj : Function.Injective φ' := by
    intro a b hab
    apply hρ
    apply (MulAut.conj (g : ModGL τ L)⁻¹).injective
    simpa [φ'] using hab
  have hCΓ : C.map φ' ≤ Γ.map (baseChangeGL ι) := by
    rintro y ⟨r, hr, rfl⟩
    have hr' : kgInducedAut θ ξ r = r := mem_ggFixSub.mp hr
    have hmem : φ' r ∈ ratPts τ L F₀ := by
      rw [hφ'_apply r]
      exact (hiff' r).mp hr'
    rwa [hfix] at hmem
  have hcommC : ⁅Γ.map (baseChangeGL ι), Γ.map (baseChangeGL ι)⁆ ≤ C.map φ' := by
    rw [← hfix]
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    have hy₁p : y₁ ∈ ratPts τ L (endPow F₀ p) := by
      rw [ratPts, Subgroup.mem_inf] at hy₁ ⊢
      refine ⟨hy₁.1, ?_⟩
      show endPow F₀ p y₁ = y₁
      rw [endPow_apply]
      exact Function.iterate_fixed (ratPts_fix hy₁) p
    have hy₂p : y₂ ∈ ratPts τ L (endPow F₀ p) := by
      rw [ratPts, Subgroup.mem_inf] at hy₂ ⊢
      refine ⟨hy₂.1, ?_⟩
      show endPow F₀ p y₂ = y₂
      rw [endPow_apply]
      exact Function.iterate_fixed (ratPts_fix hy₂) p
    let x₁ : ratPts τ L (endPow F₀ p) :=
      ⟨(g : ModGL τ L) * y₁ * (g : ModGL τ L)⁻¹,
        mul_mem (mul_mem g.2 hy₁p) (inv_mem g.2)⟩
    let x₂ : ratPts τ L (endPow F₀ p) :=
      ⟨(g : ModGL τ L) * y₂ * (g : ModGL τ L)⁻¹,
        mul_mem (mul_mem g.2 hy₂p) (inv_mem g.2)⟩
    obtain ⟨r, hr⟩ := kgLangS1E_bridge_commutator_mem hcommI ρ Θ hρ hρG hΘ hI hconjΘ x₁ x₂
    have hφr : φ' r = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
      rw [hφ'_apply r, hr]
      simp only [x₁, x₂]
      group
    have hφr_mem : φ' r ∈ ratPts τ L F₀ := by
      rw [hφr]
      exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)
    have hrC : r ∈ C := by
      change kgInducedAut θ ξ r = r
      exact (hiff' r).mpr hφr_mem
    exact Subgroup.mem_map.mpr ⟨r, hrC, hφr⟩
  have hDT : (⁅C, C⁆).map φ' = T.map (baseChangeGL ι) := by
    rw [Subgroup.map_commutator]
    apply le_antisymm
    · calc ⁅C.map φ', C.map φ'⁆ ≤ ⁅Γ.map (baseChangeGL ι), Γ.map (baseChangeGL ι)⁆ :=
            Subgroup.commutator_mono hCΓ hCΓ
        _ = (⁅Γ, Γ⁆).map (baseChangeGL ι) :=
            (Subgroup.map_commutator Γ Γ (baseChangeGL ι)).symm
        _ ≤ T.map (baseChangeGL ι) := Subgroup.map_mono hΓT
    · have hTmap : T.map (baseChangeGL ι) =
          ⁅T.map (baseChangeGL ι), T.map (baseChangeGL ι)⁆ := by
        rw [← Subgroup.map_commutator, hTperf]
      have hTleC : T.map (baseChangeGL ι) ≤ C.map φ' := by
        rw [hTmap]
        calc ⁅T.map (baseChangeGL ι), T.map (baseChangeGL ι)⁆
            ≤ ⁅Γ.map (baseChangeGL ι), Γ.map (baseChangeGL ι)⁆ :=
              Subgroup.commutator_mono (Subgroup.map_mono hTΓ) (Subgroup.map_mono hTΓ)
          _ ≤ C.map φ' := hcommC
      rw [hTmap]
      exact Subgroup.commutator_mono hTleC hTleC
  obtain ⟨eD, heD⟩ : ∃ eD : ↥⁅C, C⁆ ≃* ↥T, ∀ r : ↥⁅C, C⁆,
      baseChangeGL (τ := τ) ι (eD r : ModGL τ k) =
        (g : ModGL τ L)⁻¹ * ρ (r : R) * (g : ModGL τ L) := by
    let e₁ : ↥⁅C, C⁆ ≃* ↥((⁅C, C⁆).map φ') :=
      (⁅C, C⁆).equivMapOfInjective φ' hφ'_inj
    let e₂ : ↥T ≃* ↥(T.map (baseChangeGL ι)) :=
      T.equivMapOfInjective (baseChangeGL ι) (baseChangeGL_injective ι)
    refine ⟨e₁.trans (MulEquiv.subgroupCongr hDT) |>.trans e₂.symm, ?_⟩
    intro r
    let z : ↥(T.map (baseChangeGL ι)) := MulEquiv.subgroupCongr hDT (e₁ r)
    have h₁ : ((e₁ r : ↥((⁅C, C⁆).map φ')) : ModGL τ L) = φ' (r : R) :=
      Subgroup.coe_equivMapOfInjective_apply _ _ _ r
    have hz : (z : ModGL τ L) = φ' (r : R) := by
      change ((e₁ r : ↥((⁅C, C⁆).map φ')) : ModGL τ L) = φ' (r : R)
      exact h₁
    have h₂ : baseChangeGL (τ := τ) ι (e₂.symm z : ModGL τ k) = (z : ModGL τ L) := by
      have h := Subgroup.coe_equivMapOfInjective_apply (H := T)
        (baseChangeGL (τ := τ) ι) (baseChangeGL_injective ι) (e₂.symm z)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    change baseChangeGL (τ := τ) ι (e₂.symm z : ModGL τ k) =
      (g : ModGL τ L)⁻¹ * ρ (r : R) * (g : ModGL τ L)
    rw [h₂, hz, hφ'_apply]
  have hDs : IsSimpleGroup ↥⁅C, C⁆ := by
    have : IsSimpleGroup ↥T := hTs
    exact eD.isSimpleGroup
  have hDna : ∃ a b : ↥⁅C, C⁆, a * b ≠ b * a :=
    kgLangS1EModelDerivedAux_nonabelian eD.symm hTna
  obtain ⟨hcov1, hcov2, hcov3, hcov4⟩ := kgLangS1E_component_cover_derived θ hDs hDna hJ₀
  obtain ⟨qiso, hqiso⟩ : ∃ q : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥⁅C, C⁆,
      ∀ j : ↥J₀, (q (QuotientGroup.mk j) : R) = θ (QuotientGroup.mk (j : K)) :=
    kgLangS1EModelDerivedAux_quot θ J₀ ⁅C, C⁆ hcov1 hcov2 hcov3
  let ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥T := qiso.trans eD
  have hbase_ψ : ∀ j : ↥J₀,
      baseChangeGL (τ := τ) ι (ψ (QuotientGroup.mk j) : ModGL τ k) =
        (g : ModGL τ L)⁻¹ * ρ (θ (QuotientGroup.mk (j : K))) * (g : ModGL τ L) := by
    intro j
    show baseChangeGL (τ := τ) ι (eD (qiso (QuotientGroup.mk j)) : ModGL τ k) = _
    rw [heD (qiso (QuotientGroup.mk j)), hqiso j]
  refine ⟨(g : ModGL τ L), hgadj, ψ, ?_⟩
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
  have hgx : (g : ModGL τ L)⁻¹ * x * (g : ModGL τ L) ∈ ratPts τ L F₀ :=
    hconj3 ⟨x, hxmem⟩ hcommΘ
  have hy : (g : ModGL τ L)⁻¹ * x * (g : ModGL τ L) ∈
      Γ.map (baseChangeGL (τ := τ) ι) := hfix ▸ hgx
  obtain ⟨y, hy_mem, hy_eq⟩ := Subgroup.mem_map.mp hy
  refine ⟨y, hy_mem, hy_eq, ?_⟩
  refine ⟨α, hαA, fun j => ?_⟩
  let j' : ↥J₀ := ⟨α (j : K), hcov4 α hcommαξ (j : K) j.2⟩
  refine ⟨j', rfl, ?_⟩
  apply baseChangeGL_injective (τ := τ) ι
  rw [hbase_ψ j', map_mul, map_mul, map_inv, hy_eq, hbase_ψ j]
  have hgroup : (g : ModGL τ L)⁻¹ * x * (g : ModGL τ L) *
        ((g : ModGL τ L)⁻¹ * ρ (θ (QuotientGroup.mk (j : K))) * (g : ModGL τ L)) *
        ((g : ModGL τ L)⁻¹ * x * (g : ModGL τ L))⁻¹ =
      (g : ModGL τ L)⁻¹ * (x * ρ (θ (QuotientGroup.mk (j : K))) * x⁻¹) *
        (g : ModGL τ L) := by group
  have hαapply : (kgInducedAut θ α) (θ (QuotientGroup.mk (j : K))) =
      θ (QuotientGroup.mk (α (j : K))) := by
    simp [kgInducedAut, MulAut.congr_apply, centerQuotAut_mk]
  have hxρ : x * ρ (θ (QuotientGroup.mk (j : K))) * x⁻¹ =
      ρ (θ (QuotientGroup.mk (α (j : K)))) :=
    (hxconj (θ (QuotientGroup.mk (j : K)))).symm.trans (congrArg ρ hαapply)
  rw [hgroup, hxρ]

end CFSG.StandardType
