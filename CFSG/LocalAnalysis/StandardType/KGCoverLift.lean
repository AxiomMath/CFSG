module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.StandardType.KGUniv

open CFSG.RankThree.PerfectCover
open scoped commutatorElement

private theorem eq_of_central_displacement_hom_aux {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] (f g : G →* H)
    (h : ∀ x, (g x)⁻¹ * f x ∈ Subgroup.center H) : f = g := by
  have hfg : ∀ x, f x = g x * ((g x)⁻¹ * f x) := fun x => by group
  have hle : commutator G ≤ MonoidHom.eqLocus f g := by
    rw [_root_.commutator_def G, Subgroup.commutator_le]
    intro a _ b _
    show f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hfg a, hfg b]
    exact CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (h a) (h b)
  rw [Group.IsPerfect.commutator_eq_top] at hle
  ext x
  exact hle (Subgroup.mem_top x)

private lemma kgInducedAut_apply_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) =
    θ (QuotientGroup.mk (α k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerQuotAut_mk]

theorem exists_universal_cover_lift {K R : Type} [Group K] [Finite K] [Group R]
    (hK : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* R) :
    Finite (HopfCover R) ∧ commutator (HopfCover R) = ⊤ ∧
      ∃ (θC : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R) (κ : HopfCover R →* K)
        (lift : MulAut K →* MulAut (HopfCover R)),
        Function.Surjective κ ∧ κ.ker ≤ Subgroup.center (HopfCover R) ∧
        (∀ x, θ (QuotientGroup.mk (κ x)) = hopfCoverMap R x) ∧
        (∀ α x, κ (lift α x) = α (κ x)) ∧ ∀ α, kgInducedAut θC (lift α) = kgInducedAut θ α := by
  classical
  haveI : Group.IsPerfect K := ⟨hK⟩
  let q : K →* R := centralQuotientMap θ
  have hq : Function.Surjective q := centralQuotientMap_surjective θ
  have hqker : q.ker = Subgroup.center K := centralQuotientMap_ker θ
  haveI : Finite R := finite_of_surjective_monoidHom q hq
  haveI hRperf : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := q) hq
  let C := HopfCover R
  haveI hCfin : Finite C := finite_hopfCover hRperf
  haveI hCperf : Group.IsPerfect C := hopfCover_isPerfect
  have hCcom : commutator C = ⊤ := Group.IsPerfect.commutator_eq_top (G := C)
  let π : C →* R := hopfCoverMap R
  have hπ : Function.Surjective π := hopfCoverMap_surjective (S := R)
  let κ : C →* K := hopfLift q hq (le_of_eq hqker)
  have hκ_surj : Function.Surjective κ := hopfLift_surjective q hq (le_of_eq hqker)
  have hκ_comp : q.comp κ = π := comp_hopfLift q hq (le_of_eq hqker)
  have hκ_mk : ∀ x : C, θ (QuotientGroup.mk (κ x)) = π x := by
    intro x
    rw [← centralQuotientMap_apply θ (κ x)]
    exact DFunLike.congr_fun hκ_comp x
  have hκ_le_center : κ.ker ≤ Subgroup.center C := by
    intro x hx
    apply hopfMultiplier_le_center (S := R)
    change π x = 1
    have hx1 : κ x = 1 := MonoidHom.mem_ker.mp hx
    rw [← hκ_mk x, hx1]
    simp
  have hπker : π.ker = Subgroup.center C := by
    apply le_antisymm
    · intro x hx
      exact hopfMultiplier_le_center (S := R) hx
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hkcenter : κ x ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨z, rfl⟩ := hκ_surj y
        calc κ z * κ x = κ (z * x) := (map_mul κ z x).symm
          _ = κ (x * z) := by rw [Subgroup.mem_center_iff.mp hx z]
          _ = κ x * κ z := map_mul κ x z
      have hq1 : QuotientGroup.mk (κ x) = 1 := (QuotientGroup.eq_one_iff (κ x)).mpr hkcenter
      rw [← hκ_mk x, hq1]
      simp
  let θC : C ⧸ Subgroup.center C ≃* R :=
    QuotientGroup.liftEquiv (Subgroup.center C) hπ hπker.symm
  have hθC_mk : ∀ x : C, θC (QuotientGroup.mk x) = π x :=
    fun x => QuotientGroup.liftEquiv_mk (Subgroup.center C) hπ hπker.symm x
  have exists_aut_lift : ∀ α : MulAut K, ∃ γ : MulAut C, ∀ x, κ (γ x) = α (κ x) := by
    intro α
    let ᾱ : MulAut R := kgInducedAut θ α
    have hqα : ∀ y : K, ᾱ (q y) = q (α y) := by
      intro y
      change kgInducedAut θ α (centralQuotientMap θ y) = centralQuotientMap θ (α y)
      rw [centralQuotientMap_apply θ y, centralQuotientMap_apply θ (α y)]
      exact kgInducedAut_apply_mk θ α y
    let q' : C →* R := (ᾱ⁻¹ : MulAut R).toMonoidHom.comp π
    have hq' : Function.Surjective q' := by
      intro r
      obtain ⟨x, hx⟩ := hπ (ᾱ r)
      exact ⟨x, by simp [q', hx]⟩
    have hq'ker : q'.ker ≤ Subgroup.center C := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : (ᾱ⁻¹ : MulAut R) (π x) = 1 := by
        simpa [q', MonoidHom.comp_apply] using hx
      have hπx : π x = 1 := (map_eq_one_iff (ᾱ⁻¹ : MulAut R) (ᾱ⁻¹).injective).mp hx1
      exact le_of_eq hπker (by rw [MonoidHom.mem_ker]; exact hπx)
    let γ₀ : C →* C := hopfLift q' hq' hq'ker
    have hγ₀_surj : Function.Surjective γ₀ := hopfLift_surjective q' hq' hq'ker
    have hγ₀_bij : Function.Bijective γ₀ :=
      ⟨(Finite.injective_iff_surjective (f := (γ₀ : C → C))).mpr hγ₀_surj, hγ₀_surj⟩
    let γ : MulAut C := MulEquiv.ofBijective γ₀ hγ₀_bij
    have hγ_apply : ∀ x, γ x = γ₀ x := fun x => MulEquiv.ofBijective_apply γ₀ hγ₀_bij x
    have hγπ : ∀ x, π (γ x) = ᾱ (π x) := by
      intro x
      rw [hγ_apply x]
      have hcomp : q' (γ₀ x) = π x := DFunLike.congr_fun (comp_hopfLift q' hq' hq'ker) x
      have h1 : (ᾱ⁻¹ : MulAut R) (π (γ₀ x)) = π x := by
        simpa [q', MonoidHom.comp_apply] using hcomp
      have h2 := congrArg (fun r => ᾱ r) h1
      simpa using h2
    have hmain : κ.comp γ.toMonoidHom = α.toMonoidHom.comp κ := by
      refine eq_of_central_displacement_hom_aux (κ.comp γ.toMonoidHom)
        (α.toMonoidHom.comp κ) ?_
      intro y
      apply le_of_eq hqker
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (q (α (κ y)))⁻¹ * q (κ (γ y)) = 1
      rw [← hqα (κ y)]
      have hκγ : q (κ (γ y)) = π (γ y) := DFunLike.congr_fun hκ_comp (γ y)
      have hκy : q (κ y) = π y := DFunLike.congr_fun hκ_comp y
      rw [hκγ, hκy, hγπ y, inv_mul_cancel]
    exact ⟨γ, fun x => DFunLike.congr_fun hmain x⟩
  have aut_lift_unique : ∀ (α : MulAut K) (γ₁ γ₂ : MulAut C),
      (∀ x, κ (γ₁ x) = α (κ x)) → (∀ x, κ (γ₂ x) = α (κ x)) → γ₁ = γ₂ := by
    intro α γ₁ γ₂ h₁ h₂
    refine MulEquiv.toMonoidHom_injective ?_
    refine eq_of_central_displacement_hom_aux γ₁.toMonoidHom γ₂.toMonoidHom ?_
    intro x
    apply hκ_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (κ (γ₂ x))⁻¹ * κ (γ₁ x) = 1
    rw [h₂ x, h₁ x, inv_mul_cancel]
  let liftFun : MulAut K → MulAut C := fun α => Classical.choose (exists_aut_lift α)
  have liftFun_spec : ∀ α x, κ (liftFun α x) = α (κ x) := fun α =>
    Classical.choose_spec (exists_aut_lift α)
  have liftFun_mul : ∀ α β, liftFun (α * β) = liftFun α * liftFun β := by
    intro α β
    refine aut_lift_unique (α * β) (liftFun (α * β)) (liftFun α * liftFun β)
      (liftFun_spec (α * β)) ?_
    intro x
    rw [MulAut.mul_apply, liftFun_spec α (liftFun β x), liftFun_spec β x, MulAut.mul_apply]
  let lift : MulAut K →* MulAut C := MonoidHom.mk' liftFun liftFun_mul
  refine ⟨hCfin, hCcom, θC, κ, lift, hκ_surj, hκ_le_center, hκ_mk, ?_, ?_⟩
  · intro α x
    exact liftFun_spec α x
  · intro α
    apply MulEquiv.ext
    intro r
    obtain ⟨y, rfl⟩ := θC.surjective r
    refine QuotientGroup.induction_on y ?_
    intro x
    have hκl : κ (lift α x) = α (κ x) := liftFun_spec α x
    rw [kgInducedAut_apply_mk θC (lift α) x, hθC_mk (lift α x), hθC_mk x, ← hκ_mk x,
      kgInducedAut_apply_mk θ α (κ x), ← hκ_mk (lift α x), hκl]

end CFSG.StandardType.KGUniv
