module

public import CFSG.LocalAnalysis.WeakClosure81.GapTwoCard
public import CFSG.CGT.Timmesfeld75.MultPrime
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.LocalAnalysis.WeakClosure81.TransvectionCenterCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank

theorem quotient_center_injective {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : BarSituation X S) :
    Function.Injective
      (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center X)) := by
  have hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    le_bot_iff.1 (hS.pCore_eq_bot ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center hO2
  have hconj : ∀ (g x : X), CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (g * x * g⁻¹) := by
    intro g x hx
    refine ⟨fun h => hx.1 ?_, ?_⟩
    · have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [← this, h]
      group
    · have : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
      rw [this, hx.2]
      group
  haveI hnormal : (Subgroup.closure
      {x : X | CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hconj g x hx)
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  have hgen : Subgroup.closure
      {x : X | CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x} = ⊤ := by
    rw [eq_top_iff, ← hS.normalClosure_eq_top]
    refine Subgroup.normalClosure_le_normal fun s hs => ?_
    by_cases h1 : s = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨h1, by simpa [pow_two] using hS.elemAbelian.2 s hs⟩
  have hker :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull.characteristic_quotient_ker_eq_bot
      (Subgroup.center X) hodd le_rfl hgen
  exact (MonoidHom.ker_eq_bot_iff _).1 hker

private theorem specialLinearGroupEquivStatedSL_tvSL {m : ℕ} {F : Type} [Field F]
    {a f : Fin m → F} (hf : f ⬝ᵥ a = 0) :
    specialLinearGroupEquivStatedSL m F (tvSL a f hf) =
      transvectionCenterSL a f hf := by
  apply Subtype.ext
  apply Units.ext
  rw [specialLinearGroupEquivStatedSL_coe, transvectionCenterSL_coe, coe_tvSL]

private theorem projectiveSLMulEquivStatedProj_proj_tvSL {m : ℕ} {F : Type} [Field F]
    {a f : Fin m → F} (hf : f ⬝ᵥ a = 0) :
    projectiveSLMulEquivStatedProj m F (proj m F (tvSL a f hf)) =
      QuotientGroup.mk (transvectionCenterSL a f hf) := by
  have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        m F (QuotientGroup.mk (tvSL a f hf)) =
      proj m F (tvSL a f hf) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL,
      QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  rw [projectiveSLMulEquivStatedProj, MulEquiv.trans_apply, ← h1,
    MulEquiv.symm_apply_apply]
  rw [projectiveSpecialLinearGroupEquivStatedProj, QuotientGroup.congr_apply,
    specialLinearGroupEquivStatedSL_tvSL]
  rfl

theorem w3Lem85TwoGap2_holds : W3Lem85TwoGap2 := by
  intro X _ _ S hS hlin A hA hfix
  obtain ⟨m, n, hm3, hLie, hTCG, T, hST, hwc⟩ := hlin
  obtain ⟨F, hField, hFin, hcardF, e, a, ha, hiff⟩ := hTCG
  classical
  letI : Field F := hField
  letI : Finite F := hFin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  let A' : Subgroup (MulAut (X ⧸ Subgroup.center X)) :=
    A.map (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center X))
  let eAut : MulAut (X ⧸ Subgroup.center X) ≃*
      MulAut (StatedProj (StatedSL m F)) := MulAut.congr e
  let B : Subgroup (MulAut (StatedProj (StatedSL m F))) := A'.map eAut.toMonoidHom
  let e2 : projectiveSL m F ≃* StatedProj (StatedSL m F) := projectiveSLMulEquivStatedProj m F
  let C : Subgroup (MulAut (projectiveSL m F)) := B.map (MulAut.congr e2.symm).toMonoidHom

  have hA' : IsElemAbelian 2 A' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a1, ha1, hax⟩ := x.2
      obtain ⟨b1, hb1, hby⟩ := y.2
      apply Subtype.ext
      show (x : MulAut (X ⧸ Subgroup.center X)) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hA.1.is_comm.comm ⟨a1, ha1⟩ ⟨b1, hb1⟩))
    · obtain ⟨a1, ha1, hax⟩ := hx
      rw [← hax, ← map_pow, hA.2 a1 ha1, map_one]
  have hcardA' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (quotient_center_injective hS)
  have hfixA' : ∀ a' ∈ A', ∀ s' ∈ S.map q, a' s' = s' := by
    rintro a' ⟨a1, ha1, rfl⟩ s' ⟨s, hs, rfl⟩
    rw [CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk, hfix a1 ha1 s hs]

  have hB : IsElemAbelian 2 B := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a1, ha1, hax⟩ := x.2
      obtain ⟨b1, hb1, hby⟩ := y.2
      apply Subtype.ext
      show (x : MulAut (StatedProj (StatedSL m F))) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      exact congrArg eAut (congrArg Subtype.val (hA'.1.is_comm.comm ⟨a1, ha1⟩ ⟨b1, hb1⟩))
    · obtain ⟨a1, ha1, hax⟩ := hx
      rw [← hax, ← map_pow, hA'.2 a1 ha1, map_one]
  have hcardB : Nat.card B = Nat.card A' :=
    Subgroup.card_map_of_injective eAut.injective

  have hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    le_bot_iff.1 (hS.pCore_eq_bot ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center hO2
  have hZS : S ⊓ Subgroup.center X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    have hz2 : z ^ 2 = 1 := hS.elemAbelian.2 z hz.1
    have hord2 : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
    have hordne : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
    have hord : orderOf z = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact absurd h hordne
      · exact h
    have h2dvd : 2 ∣ Nat.card (Subgroup.center X) := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz.2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hinjS : Set.InjOn q (S : Set X) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ Subgroup.center X := QuotientGroup.eq.1 hxy
    have h2 : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
    have h3 : x⁻¹ * y ∈ S ⊓ Subgroup.center X := ⟨h2, h1⟩
    rw [hZS, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact h3
  have hcardS : Nat.card (S.map q) = Nat.card S := by
    change (S.map q : Set (X ⧸ Subgroup.center X)).ncard = (S : Set X).ncard
    rw [Subgroup.coe_map]
    exact hinjS.ncard_image
  have hpre : (S.map q : Set (X ⧸ Subgroup.center X)) =
      e ⁻¹' transvectionCenterSet m F a := by
    ext y
    rw [Subgroup.coe_map, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hiff (q s)).1 ⟨s, hs, rfl⟩
    · intro hy
      obtain ⟨s, hs, hsy⟩ := (hiff y).2 hy
      exact ⟨s, hs, hsy⟩
  have hcardImg : Nat.card (S.map q) = Nat.card F ^ (m - 1) := by
    change (S.map q : Set (X ⧸ Subgroup.center X)).ncard = Nat.card F ^ (m - 1)
    rw [hpre]
    rw [Set.ncard_preimage_of_injective_subset_range e.injective (by
      intro x _
      exact ⟨e.symm x, e.apply_symm_apply x⟩)]
    exact ncard_transvectionCenterSet m F (by omega) a ha

  have hfixB : ∀ b ∈ B, ∀ x ∈ transvectionCenterSet m F a, b x = x := by
    rintro b ⟨a1, ha1, rfl⟩ x hx
    have hx' : e.symm x ∈ S.map q := by
      have h1 : e.symm x ∈ (e ⁻¹' transvectionCenterSet m F a : Set (X ⧸ Subgroup.center X)) := by
        rw [Set.mem_preimage, e.apply_symm_apply]
        exact hx
      rw [← hpre] at h1
      exact h1
    change (MulAut.congr e a1) x = x
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    rw [hfixA' a1 ha1 (e.symm x) hx']
    exact e.apply_symm_apply x
  have hC : IsElemAbelian 2 C := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a1, ha1, hax⟩ := x.2
      obtain ⟨b1, hb1, hby⟩ := y.2
      apply Subtype.ext
      show (x : MulAut (projectiveSL m F)) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hB.1.is_comm.comm ⟨a1, ha1⟩ ⟨b1, hb1⟩))
    · obtain ⟨a1, ha1, hax⟩ := hx
      rw [← hax, ← map_pow, hB.2 a1 ha1, map_one]
  have hcardC : Nat.card C = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.congr e2.symm).injective
  have hfixC : ∀ c ∈ C, ∀ (f : Fin m → F) (hf : f ⬝ᵥ a = 0),
      c (proj m F (tvSL a f hf)) = proj m F (tvSL a f hf) := by
    rintro c ⟨b, hb, rfl⟩ f hf
    have hx : e2 (proj m F (tvSL a f hf)) ∈ transvectionCenterSet m F a := by
      rw [projectiveSLMulEquivStatedProj_proj_tvSL]
      exact ⟨transvectionCenterSL a f hf, rfl, f, hf, transvectionCenterSL_coe a f hf⟩
    change (MulAut.congr e2.symm b) (proj m F (tvSL a f hf)) = proj m F (tvSL a f hf)
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
    rw [hfixB b hb (e2 (proj m F (tvSL a f hf))) hx]
    exact e2.symm_apply_apply (proj m F (tvSL a f hf))
  have hbound : Nat.card C ≤ Nat.card F ^ (m - 1) :=
    card_elemAbelian_two_aut_projSU_fixes_tvCenter (K := F) hm3 ha C hC hfixC

  calc
    Nat.card A = Nat.card A' := hcardA'.symm
    _ = Nat.card B := hcardB.symm
    _ = Nat.card C := hcardC.symm
    _ ≤ Nat.card F ^ (m - 1) := hbound
    _ = Nat.card S := hcardImg.symm.trans hcardS

end CFSG.LocalAnalysis.WeakClosure81

end
