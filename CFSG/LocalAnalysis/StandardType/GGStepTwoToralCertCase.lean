module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertPlane

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {p : ℕ}

theorem tcCaseOK_sound (hp : p.Prime) {L : List (Array ℤ)} {gens : Array (List ℕ)}
    (hL : tcLOK (tcEnv τ p L gens) = true) {π : Equiv.Perm (Fin τ.rank)}
    (hgens : ∀ gi, CommutesPi π (tcWordElt τ (gens.getD gi [])))
    {OT : Thunk (Option TcOrb)}
    (hOT : ∀ T, OT.get = some T → tcOrbOK (tcEnv τ p L gens) T = true)
    {alc : List (Array ℤ)} {cover : Bool}
    (hcover : cover = true → π = 1 ∧ alc = tcAlcove τ p) {b : Array ℤ} {O : List ℕ}
    {ag : List (Array ℤ)}
    (hag : ∀ a ∈ ag, tcVec p τ.rank a ∈
      latEigenCoroot p τ.symmetrizedCartan π (tcRootSet τ O))
    (hcase : tcCaseOK (tcEnv τ p L gens) OT alc cover b O ag = true)
    {D : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (hD : QualPlane p (tcKerSub p τ.rank L) D)
    (hcard : Nat.card ↥(tcKerSub p τ.rank L ⊓ annSub p (tcRootSet τ O)) ≤ p ^ 2) :
    CertConcl p π (tcKerSub p τ.rank L) (tcVec p τ.rank b) (tcRootSet τ O) D := by
  unfold tcCaseOK at hcase
  simp only [tcEnv_p, tcEnv_n, tcEnv_L, tcEnv_R] at hcase
  by_cases hk : 3 ≤ (tcKernel p τ.rank
      (L ++ O.map fun i => (tcRoots τ ()).getD i #[])).length
  · simp only [hk, ↓reduceIte] at hcase
    have h3 := tcKerOK_finrank_ge hp hcase
    rw [List.length_take, min_eq_left hk, tcKerSub_rows_eq] at h3
    have h4 := natCard_ge_pow hp _ h3
    have h5 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  · simp only [hk, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true] at hcase
    obtain ⟨⟨⟨hech, hinV⟩, hagV⟩, hcases⟩ := hcase
    have hfin : Module.finrank (ZMod p) D = 2 := finrank_eq_two_of_natCard hp D hD.2.1
    have hDV : D ≤ tcKerSub p τ.rank L := hD.1
    obtain ⟨hmemspan, hlenfin⟩ := tcEchOK_sound hp hech
    have hinV' : ∀ r ∈ tcEchelon p τ.rank (b :: ag),
        tcInV (tcEnv τ p L gens) r.vec = true := by
      simpa using hinV
    have hagV' : ∀ a ∈ ag, tcInV (tcEnv τ p L gens) a = true := by simpa using hagV
    have hSV : Submodule.span (ZMod p) {f | ∃ r ∈ tcEchelon p τ.rank (b :: ag),
        f = tcVec p τ.rank r.vec} ≤ tcKerSub p τ.rank L := by
      refine Submodule.span_le.mpr ?_
      rintro f ⟨r, hr, rfl⟩
      exact (tcInV_iff _ _).mp (hinV' r hr)
    have hSspan : Submodule.span (ZMod p) {f | ∃ r ∈ tcEchelon p τ.rank (b :: ag),
        f = tcVec p τ.rank r.vec} ≤ Submodule.span (ZMod p) (insert (tcVec p τ.rank b)
          ((tcKerSub p τ.rank L : Set (Fin τ.rank → ZMod p)) ∩
            latEigenCoroot p τ.symmetrizedCartan π (tcRootSet τ O))) := by
      refine Submodule.span_le.mpr ?_
      rintro f ⟨r, hr, rfl⟩
      refine (Submodule.span_le.mpr ?_ : Submodule.span (ZMod p)
        {f | ∃ g ∈ b :: ag, f = tcVec p τ.rank g} ≤ _) (hmemspan r hr)
      rintro f ⟨g, hg, rfl⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _
          ⟨(tcInV_iff _ _).mp (hagV' g hg), hag g hg⟩)
    have hlenS : (tcEchelon p τ.rank (b :: ag)).length ≤ Module.finrank (ZMod p)
        (Submodule.span (ZMod p) {f | ∃ r ∈ tcEchelon p τ.rank (b :: ag),
          f = tcVec p τ.rank r.vec}) :=
      hlenfin _ fun r hr => Submodule.subset_span ⟨r, hr, rfl⟩
    suffices hw : ∃ s ∈ Submodule.span (ZMod p) {f | ∃ r ∈ tcEchelon p τ.rank (b :: ag),
        f = tcVec p τ.rank r.vec}, s ≠ 0 ∧ ∃ u : WeylGroup τ, CommutesPi π u ∧
          cowAct u s ∈ D by
      obtain ⟨s, hsS, hs0, u, hu, hsu⟩ := hw
      exact ⟨s, hSspan hsS, hs0, u, hu, hsu⟩
    rcases hcases with (hidx | ⟨hcv, hcov⟩) | hplane
    · have hidx' : tcDimV (tcEnv τ p L gens) ≤
          (tcEchelon p τ.rank (b :: ag)).length + 1 := of_decide_eq_true hidx
      have hL' := hL
      simp only [tcLOK, Bool.and_eq_true, beq_iff_eq, tcEnv_p, tcEnv_n, tcEnv_L] at hL'
      have hVd := finrank_tcKerSub_le hp hL'
      have hlt : Module.finrank (ZMod p) (tcKerSub p τ.rank L) <
          Module.finrank (ZMod p) D + Module.finrank (ZMod p)
            (Submodule.span (ZMod p) {f | ∃ r ∈ tcEchelon p τ.rank (b :: ag),
              f = tcVec p τ.rank r.vec}) := by
        have h1 : tcDimV (tcEnv τ p L gens) = τ.rank - L.length := rfl
        omega
      have hne := inf_ne_bot_of_finrank_zmod hp hDV hSV hlt
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact ⟨s, hs.2, hs0, 1, commutesPi_one π, by rw [cowAct_one]; exact hs.1⟩
    · obtain ⟨hπ, halc⟩ := hcover hcv
      subst hπ halc
      obtain ⟨d1, hd1, hd10, -⟩ := tcExists_two_independent hp D hfin
      obtain ⟨s, hsS, hs0, u, hsu⟩ := tcCoverOK_sound hp hcov hd10
      refine ⟨s, ?_, hs0, u, commutesPi_perm_one u, by rw [hsu]; exact hd1⟩
      refine (Submodule.span_le.mpr ?_ : Submodule.span (ZMod p)
        {f | ∃ g ∈ (tcEchelon p τ.rank (b :: ag)).map (fun x => x.vec),
          f = tcVec p τ.rank g} ≤ _) hsS
      rintro f ⟨g, hg, rfl⟩
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
      exact Submodule.subset_span ⟨r, hr, rfl⟩
    · cases hOTg : OT.get with
      | none => simp [hOTg] at hplane
      | some T =>
        simp only [hOTg] at hplane
        have hbasis : ∀ g ∈ (tcEchelon p τ.rank (b :: ag)).map (fun x => x.vec),
            tcInV (tcEnv τ p L gens) g = true := by
          intro g hg
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
          exact hinV' r hr
        obtain ⟨d, hd, hd0, s, hsS, hs0, u, hu, hsu⟩ :=
          tcPlaneOK_sound hp (hOT T hOTg) hgens hbasis hplane hD
        refine ⟨s, ?_, hs0, u, hu, by rw [hsu]; exact hd⟩
        refine (Submodule.span_le.mpr ?_ : Submodule.span (ZMod p)
          {f | ∃ g ∈ (tcEchelon p τ.rank (b :: ag)).map (fun x => x.vec),
            f = tcVec p τ.rank g} ≤ _) hsS
        rintro f ⟨g, hg, rfl⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
        exact Submodule.subset_span ⟨r, hr, rfl⟩

end CFSG.StandardType.StepTwoToralCert
