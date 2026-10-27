module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplitTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F


theorem cochar_mem_torusGroup {L : Type} [Field L] [IsAlgClosed L]
    (F : Set (Fin TwistTag.E6.tag.rank → Lˣ)) (hF : famKernel F = ∅)
    (ν : Lˣ →* ModGL TwistTag.E6.tag L) (hadj : ∀ c, ν c ∈ adjointGroup TwistTag.E6.tag L)
    (hcomm : ∀ a ∈ F, ∀ c, rootDiagUnit TwistTag.E6.tag a * ν c *
      (rootDiagUnit TwistTag.E6.tag a)⁻¹ = ν c) (c : Lˣ) :
    ν c ∈ torusGroup TwistTag.E6.tag L := by
  have hbot : ∀ T : Set (Fin TwistTag.E6.tag.rank → ℤ),
      rootSpan TwistTag.E6.tag L (∅ ∩ T) = ⊥ := by
    intro T
    rw [Set.empty_inter]
    exact le_bot_iff.1 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  have hdec : ∀ c, ∃ h ∈ torusGroup TwistTag.E6.tag L, ∃ w,
      ν c = h * canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by
    intro c
    obtain ⟨w, -, h, hh, u, hu, v, hv, he⟩ := fam_factor F (hadj c) fun a ha => hcomm a ha c
    rw [hF, hbot, Subgroup.mem_bot] at hu hv
    subst hu hv
    exact ⟨h, hh, w, by simpa only [mul_one] using he⟩
  have hmono : ∀ c, ν c ∈ monomialSubgroup TwistTag.E6.tag L := fun c => by
    obtain ⟨h, hh, w, he⟩ := hdec c
    rw [he]
    exact mul_mem (torusGroup_le_monomialSubgroup hh) (canonicalRep_mem_monomialSubgroup L w)
  obtain ⟨φ, hφ⟩ : ∃ φ : Lˣ →* WeylGroup TwistTag.E6.tag,
      φ = (weylQuotientHom TwistTag.E6.tag L).comp (ν.codRestrict _ hmono) := ⟨_, rfl⟩
  have h1 : ∀ c, φ c = 1 := units_hom_eq_one_of_pow φ
    (N := Nat.card (WeylGroup TwistTag.E6.tag)) Nat.card_pos fun _ => pow_card_eq_one'
  obtain ⟨h, hh, w, he⟩ := hdec c
  have hm : MapsRootLines (ν c) w := by
    rw [he]
    exact mapsRootLines_mul_canonicalRep hh w
  have hw : φ c = w := by
    rw [hφ]
    exact weylQuotientHom_eq (g := ⟨ν c, hmono c⟩) hm
  rw [h1 c] at hw
  rw [he, ← hw, canonicalRep_one, mul_one]
  exact hh

theorem ennolaSplitStep_holds : EnnolaSplitStep := by
  intro K _ _ σ q hK hσ _ A D hv ⟨μ, hμ1, hμadj, hμF, hμA⟩
  by_contra hno
  refine hμ1 (MonoidHom.ext fun c₀ => ?_)
  have hq : 0 < q := Nat.pos_of_ne_zero fun h0 => by
    have h := Nat.card_pos (α := K)
    rw [hK, h0] at h
    norm_num at h
  obtain ⟨hcadj, hcF⟩ := baseChangeGL_mem_adjointGroup_twistHom_eq hσ D.hFr D.hcI
  obtain ⟨θ, hθ⟩ : ∃ θ : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      θ = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) D.c := ⟨_, rfl⟩
  have hθadj : θ ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [hθ]
    exact mul_mem (inv_mem D.hg0C) hcadj
  have hcoord : ∀ x ∈ A, ∃ a, rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (D.hc x hx)
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hy).1
    refine ⟨a, ?_⟩
    rw [← hyx]
    change _ = D.g0⁻¹ * (D.g0 * _ * D.g0⁻¹) * D.g0
    group
  have hker : famKernel {a | ∃ x ∈ A, rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun α ⟨hα, hk⟩ => hno ⟨α, hα, fun x hx => ?_⟩
    obtain ⟨a, ha⟩ := hcoord x hx
    exact ⟨a, ha, hk a ⟨x, hx, ha⟩⟩
  have hT := cochar_mem_torusGroup _ hker ((MulAut.conj θ).toMonoidHom.comp μ)
    (fun c => mul_mem (mul_mem hθadj (hμadj c)) (inv_mem hθadj)) (by
      rintro a ⟨x, hx, ha⟩ c
      have hda : rootDiagUnit TwistTag.E6.tag a =
          θ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * θ⁻¹ := by
        rw [ha, hθ]
        simp only [map_mul, map_inv]
        group
      have hx' : baseChangeGL (algebraMap K (AlgebraicClosure K)) x * μ c *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) x)⁻¹ = μ c := by
        rw [← hμA x hx c, mul_inv_cancel_right]
      change rootDiagUnit TwistTag.E6.tag a * (θ * μ c * θ⁻¹) *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹ = θ * μ c * θ⁻¹
      rw [hda]
      calc _ = θ * (baseChangeGL (algebraMap K (AlgebraicClosure K)) x * μ c *
            (baseChangeGL (algebraMap K (AlgebraicClosure K)) x)⁻¹) * θ⁻¹ := by group
        _ = θ * μ c * θ⁻¹ := by rw [hx'])
  have hFθ : twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr θ =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)⁻¹ * θ := by
    rw [hθ, map_mul, map_inv, D.hg0, hcF]
    group
  have hν := cochar_eq_one_of_isLongest hq D.hFr hv ((MulAut.conj θ).toMonoidHom.comp μ) hT
    fun c => by
      change θ * μ (c ^ q) * θ⁻¹ = _ * twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr
        (θ * μ c * θ⁻¹) * _
      rw [map_mul, map_mul, map_inv, hFθ, hμF c]
      group
  have h := DFunLike.congr_fun hν c₀
  change θ * μ c₀ * θ⁻¹ = 1 at h
  exact conj_eq_one_iff.1 h

end CFSG.StandardType.TwE6RootKill

end
