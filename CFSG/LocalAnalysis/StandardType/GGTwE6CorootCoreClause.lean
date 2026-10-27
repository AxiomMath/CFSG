module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreDiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.TableBExcTwo
  CFSG.StandardType.TableBExcTwoFusion
open CFSG.ClassicalInvolution.ModelFacts.Levi (thetaDiag)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight (rootTorusSL2_eq_thetaDiag_e6)

local instance twE6CorootCoreClauseNeZero : NeZero Tag.E6.rank := ⟨by decide⟩


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem mem_zpowers_of_commute_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {A : SL2 k}
    (hA : orderOf A = Nat.card k + 1) {m : ℕ} (hm : A ^ m ≠ 1) {s c : ModGL TwistTag.E6.tag K}
    (hc : c ∈ adjointGroup TwistTag.E6.tag K) (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hs : s = c * rootDiagUnit TwistTag.E6.tag b) (hF : twistHom TwistTag.E6 K σ s = s)
    (hx : s * (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) =
      (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) * s)
    (hD : ∀ d ∈ su6Levi σ, s * d = d * s) :
    s ∈ zpowers ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) A) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card hf hk)
  have : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρdef
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  obtain ⟨l, P, hl1, hlq, hP⟩ :=
    exists_inv_mul_map_mul_eq_HSL_of_finrank (finrank_eq_two hf hk hK) hA
  have hPm : P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m) * P = HSL (l ^ m) := by
    have e : (P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A * P⁻¹⁻¹) ^ m =
        P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A ^ m * P⁻¹⁻¹ := conj_pow
    rw [inv_inv] at e
    rw [← F4Pilot.HSL_pow, ← hP, map_pow, e]
  have hlm1 : l ^ m ≠ 1 := fun h => hm (hρinj (by
    have e1 : (HSL (1 : Kˣ) : SL2 K) = 1 := by rw [← pow_zero l, ← F4Pilot.HSL_pow, pow_zero]
    rw [h, e1] at hPm
    have e2 : Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m) = 1 := by
      calc _ = P * (P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m) * P) * P⁻¹ := by
            group
        _ = 1 := by rw [hPm, mul_one, mul_inv_cancel]
    rw [map_one, hρdef, MonoidHom.comp_apply, e2, map_one]))
  have hσl : Units.map σ.toMonoidHom l = l⁻¹ := by
    have e : Units.map σ.toMonoidHom l = l ^ 2 ^ f := Units.ext (by simp [hσ])
    rw [e, eq_inv_iff_mul_eq_one, ← pow_succ, ← hk, hlq]
  obtain ⟨-, -, -, -, hLΓ, -, -⟩ := su6Levi_facts hf hk hK hσ
  have hpair : ∀ {j j' : Fin Tag.E6.rank}, j ≠ 1 → j' ≠ 1 →
      @Eq (Fin Tag.E6.rank) (TwistTag.E6.perm j) j' →
      @Eq (Fin Tag.E6.rank) (TwistTag.E6.perm j') j →
      rootDiagUnit .E6 (pairDiag j j' l l⁻¹) ∈ su6Levi σ := by
    rintro j j' hj hj' rfl hjj
    rw [hLΓ]
    exact rootDiagUnit_pairDiag_mem_inf (t := TwistTag.E6) hj hj' hjj hσl
      (by rw [map_inv, hσl, inv_inv])
  have hpχ : ∀ {j j' : Fin Tag.E6.rank}, (∀ i, coPair .E6 j (corootFrameRoot i) =
      coPair .E6 j' (corootFrameRoot i)) →
      ∀ i, rootChar (pairDiag j j' l l⁻¹) (corootFrameRoot i) = 1 :=
    fun h i => by rw [rootChar_pairDiag_inv, h i, sub_self, zpow_zero]
  have hR : ∀ i, IsRoot .E6 (corootFrameRoot i) := fun i => mem_rootFinset.1 (corootFrameRoot_mem i)
  have hint : ∀ (i : Fin 4) (B : SL2 k) (x : Kˣ),
      P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) B * P = HSL x →
      (frameProd K corootFrame P : ModGL .E6 K) *
          rootDiagUnit .E6 (thetaDiag (corootFrameRoot i) x) =
        rootSL2 .E6 K (corootFrameRoot i) (Matrix.SpecialLinearGroup.map (algebraMap k K) B) *
          (frameProd K corootFrame P : ModGL .E6 K) := fun i B x hBx => by
    rw [← rootTorusSL2_eq_thetaDiag_e6 (hR i) x, rootTorusSL2, ← hBx]
    exact frameProd_mul_rootSL2 corootFrame i P _
  have hx0 : Commute s (rootSL2 .E6 K (corootFrameRoot 0)
      (Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m))) := hx
  have hDi : ∀ {i : Fin 4}, i ≠ 0 → ∀ B : SL2 k, Commute s
      (rootSL2 .E6 K (corootFrameRoot i) (Matrix.SpecialLinearGroup.map (algebraMap k K) B)) :=
    fun hi B => hD _ (rootSL2_frame_mem_su6Levi hf hk hK hσ hi B)
  obtain ⟨a, ha⟩ := exists_inv_conj_eq_rootDiagUnit hlm1 hl1 (frameProd K corootFrame P).2 hc b hs
    fun e he => by
    simp only [frameTori, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hint 0 (A ^ m) (l ^ m) hPm, hx0⟩
    · exact ⟨_, hint 1 A l hP, hDi (i := 1) (by decide) A⟩
    · exact ⟨_, hint 2 A l hP, hDi (i := 2) (by decide) A⟩
    · exact ⟨_, hint 3 A l hP, hDi (i := 3) (by decide) A⟩
    · exact ⟨_, (commute_frameProd_rootDiagUnit (hpχ fun i => (coPair_corootFrameRoot i).1) P).eq,
        hD _ (hpair (j := 0) (j' := 5) (by decide) (by decide) rfl rfl)⟩
    · exact ⟨_, (commute_frameProd_rootDiagUnit (hpχ fun i => (coPair_corootFrameRoot i).2) P).eq,
        hD _ (hpair (j := 2) (j' := 4) (by decide) (by decide) rfl rfl)⟩
  have hβ : ∀ i : Fin 4, i ≠ 0 → rootChar a (corootFrameRoot i) = 1 := by
    intro i hi
    have hB : ∀ B : SL2 k, rootDiagUnit .E6 a * rootSL2 .E6 K (corootFrameRoot i)
        (P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) B * P) =
        rootSL2 .E6 K (corootFrameRoot i)
          (P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) B * P) * rootDiagUnit .E6 a :=
      fun B => by
        rw [← ha]
        exact conj_commute_of_intertwine (frameProd_mul_rootSL2 corootFrame i P _) (hDi hi B)
    have hu := hB (uSL 1)
    have hv := hB (vSL 1)
    rw [E6GraphLevi.map_uSL, map_one] at hu
    rw [E6GraphLevi.map_vSL, map_one] at hv
    exact rootChar_eq_one_of_commute (hR i) P hu hv
  have hs3 : s = thetaSL2 K P * rootDiagUnit TwistTag.E6.tag a * (thetaSL2 K P)⁻¹ :=
    (inv_mul_eq_iff_eq_mul.1 (eq_mul_inv_of_mul_eq ha)).trans
      ((mul_assoc _ _ _).symm.trans (frameProd_conj_rootDiagUnit hβ P))
  have hDa : ∀ d ∈ su6Levi σ,
      rootDiagUnit TwistTag.E6.tag a * d = d * rootDiagUnit TwistTag.E6.tag a := by
    intro d hd
    have hn : Commute (thetaSL2 K P) d := mem_centralizer_iff.1
      (subsystemGroup_le_centralizer_thetaSL2 hK2 (su6Levi_le_subsystemGroup σ hd)) _ ⟨P, rfl⟩
    have e : rootDiagUnit TwistTag.E6.tag a = (thetaSL2 K P)⁻¹ * s * thetaSL2 K P := by
      rw [hs3]
      group
    rw [e]
    exact ((hn.inv_left.mul_left (hD d hd)).mul_left hn).eq
  have hσσ : ∀ x, σ (σ x) = x := TwistedE6Pilot.apply_apply_eq hK hσ
  have hy : ∀ {j j' : Fin Tag.E6.rank}, j ≠ 1 → j' ≠ 1 →
      @Eq (Fin Tag.E6.rank) (TwistTag.E6.perm j) j' →
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j' 1 → a j = 1 ∧ a j' = 1 := by
    intro j j' hj hj' hjj hne
    have hpl : @permLattice TwistTag.E6.tag TwistTag.E6.perm
        (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
          (Pi.single j' 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← hjj]
      exact permLattice_single _ _
    have hyD := twistedE6PairX_single_mem_inf (K := K) hσσ (A := E6GraphLevi.setA) (j := j) hj
      (by rw [hjj]; exact hj') 1
    rw [twistedE6PairX, hpl, map_one, ← hLΓ] at hyD
    refine eq_one_of_commute_pinnedX_mul hne (fun u v => ?_) (hDa _ hyD)
    have h := (commute_pinnedX_permLattice_twistedE6 (K := K)
      (isRoot_single TwistTag.E6.tag j) u v).eq
    rw [hpl] at h
    exact h
  have ha3 : a 3 = 1 := by
    have h := hβ 3 (by decide)
    rwa [show corootFrameRoot 3 = Pi.single 3 1 by decide, EPilot.rootChar_single_eq] at h
  obtain ⟨h0, h5⟩ := hy (j := 0) (j' := 5) (by decide) (by decide) rfl (by decide)
  obtain ⟨h2, h4⟩ := hy (j := 2) (j' := 4) (by decide) (by decide) rfl (by decide)
  have ha1 : ∀ j : Fin Tag.E6.rank, j ≠ 1 → a j = 1 := by
    intro j hj
    have : j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j hj; decide
    rcases this with rfl | rfl | rfl | rfl | rfl
    exacts [h0, h2, ha3, h4, h5]
  have hhigh : a = EPilot.highDiag .E6 (a 1) := by
    funext j
    rw [EPilot.highDiag, Pi.mulSingle_apply]
    split_ifs with hj
    · rw [hj]
      rfl
    · exact ha1 j hj
  have hda : rootDiagUnit TwistTag.E6.tag a = thetaSL2 K (HSL (a 1)) :=
    (congrArg (rootDiagUnit TwistTag.E6.tag) hhigh).trans (thetaSL2_HSL (a 1)).symm
  have hsB : s = thetaSL2 K (P * HSL (a 1) * P⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← hda]
    exact hs3
  have hσB : Matrix.SpecialLinearGroup.map σ (P * HSL (a 1) * P⁻¹) = P * HSL (a 1) * P⁻¹ :=
    thetaSL2_injective hK2 (by rw [← twistHom_thetaSL2 hK2, ← hsB, hF])
  obtain ⟨B₀, hB₀⟩ :=
    F4Pilot.exists_map_eq_of_map_eq (algebraMap k K) σ (sigma_eq_self_iff hk hσ) _ hσB
  have hsρ : s = ρ B₀ := by rw [hsB, ← hB₀, hρdef, MonoidHom.comp_apply]
  have hBA : B₀ * A ^ m = A ^ m * B₀ := hρinj (by rw [map_mul, map_mul, ← hsρ]; exact hx)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (mem_zpowers_of_commute_pow hA hm hBA)
  rw [hsρ]
  exact mem_zpowers_iff.2 ⟨i, (map_zpow ρ A i).symm⟩

end CFSG.StandardType.TwE6CorootCore

end
