module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane

public noncomputable section

namespace CFSG.StandardType.LangRetype

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  (lang_familyGroup_of_mapsTo twFrob twFrob_apply twFrob_mem_familyGroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 (canonicalRep_rootReflection_mem)


theorem canonicalRep_mem_familyGroup_of_mem_closure
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {u : WeylGroup τ}
    (hu : u ∈ Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α}) :
    canonicalRep (coxeterSystem τ) L u ∈ familyGroup (K := L) a := by
  induction hu using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, rfl⟩ := hs
    have hneg : -α ∈ familyKernel a := ⟨IsRoot.neg hα.1, fun i => by
      rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2 i, inv_one, mul_one]⟩
    have hle : torusGroup τ L ⊔ rootSpan τ L {α, -α} ≤ familyGroup (K := L) a :=
      sup_le_sup_left (rootSpan_mono fun β hβ => by
        rcases hβ with rfl | rfl
        exacts [hα, hneg]) _
    exact hle (canonicalRep_rootReflection_mem hα.1)
  | one =>
    rw [canonicalRep_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) x y
    have e : canonicalRep (coxeterSystem τ) L (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) L x * canonicalRep (coxeterSystem τ) L y) := by
      rw [hkk]
      group
    rw [e]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem ihx ihy)
  | inv x hx ihx =>
    obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) x x⁻¹
    rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
    have e : canonicalRep (coxeterSystem τ) L x⁻¹ = (canonicalRep (coxeterSystem τ) L x)⁻¹ * k := by
      rw [← hkk]
      group
    rw [e]
    exact mul_mem (inv_mem ihx) (Subgroup.mem_sup_left hk)

variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {ι : Type}

theorem exists_lang_retype_twisted
    (t : TwistTag) (f : ℕ) (hf : 1 ≤ f)
    (a : ι → Fin t.tag.rank → Lˣ) {g₀ : ModGL t.tag L} {v w : WeylGroup t.tag}
    (hF : twistHom t L (iterateFrobenius L ℓ f) g₀ =
      g₀ * canonicalRep (coxeterSystem t.tag) L v)
    (hfix : ∀ s, canonicalRep (coxeterSystem t.tag) L v *
        twistHom t L (iterateFrobenius L ℓ f) (rootDiagUnit t.tag (a s)) *
        (canonicalRep (coxeterSystem t.tag) L v)⁻¹ = rootDiagUnit t.tag (a s))
    (hw : w * v⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α}) :
    ∃ z ∈ familyGroup (K := L) a,
      (g₀ * z)⁻¹ * twistHom t L (iterateFrobenius L ℓ f) (g₀ * z) =
        canonicalRep (coxeterSystem t.tag) L w := by
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : L →+* L, Fr = iterateFrobenius L ℓ f := ⟨_, rfl⟩
  rw [← hFrdef] at hF hfix ⊢
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFrdef, iterateFrobenius_def, hx]⟩
  have hFrinj : Function.Injective (Units.map Fr.toMonoidHom) := fun x y h =>
    Units.ext (Fr.injective (congrArg Units.val h))
  obtain ⟨F, hFdef⟩ : ∃ F : ModGL t.tag L →* ModGL t.tag L, F = twistHom t L Fr := ⟨_, rfl⟩
  rw [← hFdef] at hF hfix ⊢
  obtain ⟨a'', ha''⟩ : ∃ a'' : ι → Fin t.tag.rank → Lˣ,
      a'' = fun s i => Units.map Fr.toMonoidHom (a s (t.perm.symm i)) := ⟨_, rfl⟩
  have hFd : ∀ s, F (rootDiagUnit t.tag (a s)) = rootDiagUnit t.tag (a'' s) := fun s => by
    rw [hFdef, twistHom_rootDiagUnit_eq, ha'']
  have hwconj : ∀ s, rootDiagUnit t.tag (a s) =
      canonicalRep (coxeterSystem t.tag) L v * rootDiagUnit t.tag (a'' s) *
        (canonicalRep (coxeterSystem t.tag) L v)⁻¹ := fun s => by
    rw [← hFd]
    exact (hfix s).symm
  have hv : ∀ s x, rootChar (a s) (v • x) =
      Units.map Fr.toMonoidHom (rootChar (a s) (permLattice t.perm.symm x)) := by
    intro s x
    rw [(rootDiagUnit_eq_conj_canonicalRep_iff (K := L) (a s) (a'' s) v).1 (hwconj s) x, ha'']
    rw [rootChar_map_tuple Fr (fun i => a s (t.perm.symm i)) x,
      rootChar_permLattice (a s) t.perm.symm x]
  have himg : (fun α => v • permLattice t.perm α) '' familyKernel a = familyKernel a := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
      refine ⟨IsRoot.smul (hα.permLattice t.cartan_perm) v, fun s => ?_⟩
      rw [hv, CFSG.LieType.Chevalley.permLattice_symm_permLattice, hαa s, map_one]
    · rintro ⟨hβ, hβa⟩
      refine ⟨permLattice t.perm.symm (v⁻¹ • β), ⟨?_, fun s => ?_⟩, ?_⟩
      · have hr : IsRoot t.tag (v⁻¹ • β) := IsRoot.smul hβ v⁻¹
        have := hr.permLattice (π := t.perm.symm) (fun i j => by
          have h := t.cartan_perm (t.perm.symm i) (t.perm.symm j)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm)
        exact this
      · apply hFrinj
        rw [map_one, ← hv s (v⁻¹ • β), smul_inv_smul, hβa s]
      · simp only
        rw [CFSG.LieType.Chevalley.permLattice_permLattice_symm, smul_inv_smul]
  have hLang : ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (canonicalRep (coxeterSystem t.tag) L v * F z *
        (canonicalRep (coxeterSystem t.tag) L v)⁻¹) = c := by
    have hst : ∀ x ∈ familyGroup (K := L) a, frobTwistGL t.tag L ℓ f
        (canonicalRep (coxeterSystem t.tag) L v * diagramMap t L) x ∈
          familyGroup (K := L) a := by
      intro x hx
      have e : frobTwistGL t.tag L ℓ f
          (canonicalRep (coxeterSystem t.tag) L v * diagramMap t L) x =
            twFrob t (canonicalRep (coxeterSystem t.tag) L v) Fr x := by
        rw [frobTwistGL_apply, twFrob_apply, CFSG.LieType.Chevalley.twistHom_apply, hFrdef]
        group
      rw [e]
      exact twFrob_mem_familyGroup t hFrs v a himg hx
    intro c hc
    obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo ℓ a f hf _ hst c hc
    refine ⟨z, hz, ?_⟩
    rw [← hzc, hFdef, CFSG.LieType.Chevalley.twistHom_apply, hFrdef]
    group
  have hc : canonicalRep (coxeterSystem t.tag) L w * (canonicalRep (coxeterSystem t.tag) L v)⁻¹ ∈
      familyGroup (K := L) a := by
    have hu := canonicalRep_mem_familyGroup_of_mem_closure (L := L) a hw
    obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) (w * v⁻¹) v
    rw [inv_mul_cancel_right] at hkk
    have e : canonicalRep (coxeterSystem t.tag) L w *
        (canonicalRep (coxeterSystem t.tag) L v)⁻¹ =
          k⁻¹ * canonicalRep (coxeterSystem t.tag) L (w * v⁻¹) := by
      rw [← mul_inv_eq_iff_eq_mul.2 hkk.symm]
      group
    rw [e]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) hu
  obtain ⟨z, hz, hzF⟩ := hLang _ hc
  refine ⟨z, hz, ?_⟩
  calc (g₀ * z)⁻¹ * F (g₀ * z) = z⁻¹ * (g₀⁻¹ * F g₀) * F z := by rw [map_mul]; group
    _ = z⁻¹ * canonicalRep (coxeterSystem t.tag) L v * F z := by
        rw [hF]; group
    _ = (z⁻¹ * (canonicalRep (coxeterSystem t.tag) L v * F z *
          (canonicalRep (coxeterSystem t.tag) L v)⁻¹)) *
          canonicalRep (coxeterSystem t.tag) L v := by group
    _ = canonicalRep (coxeterSystem t.tag) L w := by
        rw [hzF]; group

end CFSG.StandardType.LangRetype
