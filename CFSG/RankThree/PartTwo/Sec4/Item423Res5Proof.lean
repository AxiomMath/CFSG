module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res5ProofStd
public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofSLThree
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists

public section

namespace CFSG.RankThree.PartTwo.Sec4

namespace Res423Five

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

section Transport

variable {X : Type} [Group X] (hK : PiField π p f K)

theorem congr_eq_pglConj (e : X ≃* projImage (slPi π 3 (p ^ f) K)) {τ : MulAut X}
    (y : glPi π 3 (p ^ f) K)
    (h : ∀ z : X, ((e (τ z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (y : GL (Fin 3) K) * (e z : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk (y : GL (Fin 3) K))⁻¹) :
    MulAut.congr e τ = pglConj hK y := by
  ext w
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, coe_pglConj_apply, h,
    MulEquiv.apply_symm_apply]

theorem pglConj_inv_mul_mul (g y : glPi π 3 (p ^ f) K) :
    (pglConj hK g)⁻¹ * pglConj hK y * pglConj hK g = pglConj hK (g⁻¹ * y * g) := by
  rw [map_mul, map_mul, map_inv]

theorem pglConj_conj_eq_stdDiag (hq : ModThree π (p ^ f)) (g y : glPi π 3 (p ^ f) K)
    {l : Kˣ} {st : rootsOfUnity 3 K × rootsOfUnity 3 K}
    (h : (g : GL (Fin 3) K)⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l *
      diagUnits 1 (st.1 : Kˣ) (st.2 : Kˣ)) :
    pglConj hK (g⁻¹ * y * g) = pglConj hK (stdDiag hK hq st) := by
  apply pglConj_eq_of_mk_eq
  rw [coe_stdDiag]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h, map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨l, rfl⟩, one_mul]

end Transport

theorem k423TypeCAlpha_of_two_lt {X : Type} [Group X] [Finite X] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (e : X ≃* projImage (slPi π 3 (p ^ f) K))
    {D : Subgroup (GL (Fin 3) K)} (hD : IsTypeC π (p ^ f) K D) (B Y : Subgroup (MulAut X))
    (hInn : (MulAut.conj : X →* MulAut X).range ≤ Y) (hBY : B ≤ Y)
    (hB1 : ∀ τ ∈ B, ∃ y ∈ D, ∀ z : X, ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    (hB2 : ∀ y ∈ D, ∃ τ ∈ B, ∀ z : X, ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) :
    thetaAlpha 3 (B.subgroupOf Y) = ⊥ := by
  obtain ⟨g, hg, hdiag, hsurj⟩ := isTypeC_conj_std hK hq hD
  obtain ⟨Ψ, hΨapp⟩ : ∃ Ψ : MulAut X ≃* MulAut (projImage (slPi π 3 (p ^ f) K)),
      ∀ σ, Ψ σ = (pglConj hK ⟨g, hg⟩)⁻¹ * MulAut.congr e σ * pglConj hK ⟨g, hg⟩ :=
    ⟨(MulAut.congr e).trans (MulAut.conj (pglConj hK ⟨g, hg⟩)⁻¹), fun σ => by
      rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]⟩
  have hΨB : ∀ τ ∈ B, ∀ y ∈ D, (∀ z : X, ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) →
      ∀ (l : Kˣ) (st : rootsOfUnity 3 K × rootsOfUnity 3 K),
        g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 (st.1 : Kˣ) (st.2 : Kˣ) →
          Ψ τ = pglConj hK (stdDiag hK hq st) := by
    intro τ _ y hy hyz l st hl
    rw [hΨapp, congr_eq_pglConj hK e ⟨y, hD.1 hy⟩ hyz, pglConj_inv_mul_mul]
    exact pglConj_conj_eq_stdDiag hK hq ⟨g, hg⟩ ⟨y, hD.1 hy⟩ hl
  have hBmap : B.map Ψ.toMonoidHom = stdPlane hK hq := by
    apply le_antisymm
    · rintro _ ⟨τ, hτ, rfl⟩
      obtain ⟨y, hy, hyz⟩ := hB1 τ hτ
      obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag y hy
      rw [mem_stdPlane]
      exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), (hΨB τ hτ y hy hyz l (⟨s, hs⟩, ⟨t, ht⟩) hl).symm⟩
    · intro β hβ
      obtain ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, rfl⟩ := (mem_stdPlane hK hq).mp hβ
      obtain ⟨y, hy, l, hl⟩ := hsurj s hs t ht
      obtain ⟨τ, hτ, hτz⟩ := hB2 y hy
      exact ⟨τ, hτ, hΨB τ hτ y hy hτz l (⟨s, hs⟩, ⟨t, ht⟩) hl⟩
  have hInn' : (MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))).range ≤ Y.map Ψ.toMonoidHom := by
    rintro _ ⟨w, rfl⟩
    refine ⟨MulAut.conj (e.symm (pglConj hK ⟨g, hg⟩ w)), hInn ⟨_, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hΨapp, Res423Two.mulAut_congr_conj, MulEquiv.apply_symm_apply]
    have h1 := Res423Two.mulAut_mul_conj_mul_inv (pglConj hK ⟨g, hg⟩)⁻¹ (pglConj hK ⟨g, hg⟩ w)
    rw [inv_inv, MulAut.inv_apply_self] at h1
    exact h1
  have hBY' : stdPlane hK hq ≤ Y.map Ψ.toMonoidHom := hBmap ▸ Subgroup.map_mono hBY
  apply thetaAlpha_subgroupOf_eq_bot_of_map Ψ.toMonoidHom Ψ.injective B Y
  rw [hBmap]
  exact thetaAlpha_stdPlane hK hq hq2 hInn' hBY'

section SL

variable {X : Type} [Group X]

@[expose] noncomputable def quotientCenterEquivProj (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (e : X ≃* slPi π 3 (p ^ f) K) :
    X ⧸ Subgroup.center X ≃* projImage (slPi π 3 (p ^ f) K) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← Subtype.coe_inj,
      coe_projOf, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    constructor
    · intro hx
      have hc : e x ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨z, rfl⟩ := e.surjective w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
      exact CFSG.RankThree.PartTwo.Sec13.mem_statedScalars_of_mem_center hK hq hc
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro z
      apply e.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact commute_of_mem_statedScalars hx _ :
    Subgroup.center X = ((projOf (slPi π 3 (p ^ f) K)).comp e.toMonoidHom).ker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((projOf_surjective _).comp e.surjective))

theorem coe_quotientCenterEquivProj_mk (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : X ≃* slPi π 3 (p ^ f) K) (x : X) :
    ((quotientCenterEquivProj hK hq e (x : X ⧸ Subgroup.center X) :
      projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (e x : GL (Fin 3) K) :=
  rfl

theorem centerDescend_injective [Group.IsPerfect X] :
    Function.Injective (KFacts.centerDescend X) := by
  intro α β h
  apply mulAut_eq_of_inv_mul_mem_center
  intro s
  have h1 := congrArg (fun τ : MulAut (X ⧸ Subgroup.center X) =>
    τ (s : X ⧸ Subgroup.center X)) h
  simp only [KFacts.centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem centerDescend_conj' (x : X) :
    KFacts.centerDescend X (MulAut.conj x) = MulAut.conj (x : X ⧸ Subgroup.center X) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H z => rfl

end SL

end Res423Five

open Res423Five

theorem k423TypeCAlpha_holds : K423TypeCAlpha := by
  intro X _ _ hX π p f K _ hK hq e D hD B Y hInn hBY hB1 hB2
  exact k423TypeCAlpha_of_two_lt hK hq
    (CFSG.RankThree.PartTwo.Sec13.Item138Proof.two_lt_of_mulEquiv hX hK hq e) e hD B Y hInn hBY
    hB1 hB2

theorem k423TypeCAlphaSL_holds : K423TypeCAlphaSL := by
  intro X _ _ hX π p f K _ hK hq e D hD B Y hInn hBY hB1 hB2
  have : Group.IsPerfect X := hX.1
  have hq2 : 2 < p ^ f := by
    have h2 : 2 ≤ p ^ f :=
      le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
    by_contra hle
    have heq : p ^ f = 2 := by omega
    cases π
    · have : Group.IsSolvable (slPi false 3 (p ^ f) K) :=
        CFSG.RankThree.PartTwo.Sec13.isSolvable_slPi_two hK heq
      have hsol : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
      exact Group.IsPerfect.not_isSolvable (G := X) hsol
    · change p ^ f % 3 = 1 at hq
      omega
  set ρ := KFacts.centerDescend X with hρ
  set ē := quotientCenterEquivProj hK hq e with hē
  apply thetaAlpha_subgroupOf_eq_bot_of_map ρ centerDescend_injective B Y
  refine k423TypeCAlpha_of_two_lt hK hq hq2 ē hD (B.map ρ) (Y.map ρ) ?_
    (Subgroup.map_mono hBY) ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨MulAut.conj x, hInn ⟨x, rfl⟩, centerDescend_conj' x⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hB1 τ hτ
    refine ⟨y, hy, fun z => ?_⟩
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [hρ, KFacts.centerDescend_mk, coe_quotientCenterEquivProj_mk,
        coe_quotientCenterEquivProj_mk, hyz, map_mul, map_mul, map_inv]
  · intro y hy
    obtain ⟨τ, hτ, hτz⟩ := hB2 y hy
    refine ⟨ρ τ, ⟨τ, hτ, rfl⟩, fun z => ?_⟩
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [hρ, KFacts.centerDescend_mk, coe_quotientCenterEquivProj_mk,
        coe_quotientCenterEquivProj_mk, hτz, map_mul, map_mul, map_inv]

end CFSG.RankThree.PartTwo.Sec4
