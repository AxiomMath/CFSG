module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertCase

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {p : ℕ}

@[simp] theorem tcEnv_G (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).G = tcGramTab τ () := rfl

@[simp] theorem tcEnv_Cor (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).Cor = tcCoTab τ () := rfl

theorem latPerm_one_iterate {N : ℕ} (k : ℕ) (α : Fin N → ℤ) :
    (latPerm (1 : Equiv.Perm (Fin N)))^[k] α = α := by
  have h : latPerm (1 : Equiv.Perm (Fin N)) = id := by
    funext β
    funext i
    rfl
  rw [h, Function.iterate_id]
  rfl

theorem tcClassOK_subset {G : Array (Array ℤ)} {phi C : List ℕ}
    (h : tcClassOK G phi C = true) : ∀ i ∈ C, i ∈ phi := by
  simp only [tcClassOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.2

theorem tcClassesOK_cover {G : Array (Array ℤ)} {phi : List ℕ} {cls : List (List ℕ)}
    (h : tcClassesOK G phi cls = true) :
    (∀ C ∈ cls, tcClassOK G phi C = true) ∧ ∀ i ∈ phi, ∃ C ∈ cls, i ∈ C := by
  simp only [tcClassesOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem] at h
  exact ⟨h.1, fun i hi => by
    obtain ⟨C, hC, hiC⟩ := h.2 i hi
    exact ⟨C, hC, hiC⟩⟩

theorem tcOrbVerified_sound (L : List (Array ℤ)) (gens : Array (List ℕ)) {T : TcOrb}
    (h : tcOrbVerified (tcEnv τ p L gens) = some T) :
    tcOrbOK (tcEnv τ p L gens) T = true := by
  unfold tcOrbVerified at h
  by_cases hT : tcOrbOK (tcEnv τ p L gens) (tcOrbBuild (tcEnv τ p L gens)) = true
  · rw [if_pos hT] at h
    cases h
    exact hT
  · rw [if_neg hT] at h
    cases h

section Split

theorem tcCoroot_mem_eigen_one (O : List ℕ) {i : ℕ} (hi : i ∈ O)
    (hil : i < τ.rootCertificate.roots.length) :
    tcVec p τ.rank (((tcCoTab τ ()).getD i #[]).map (· % (p : ℤ))) ∈
      latEigenCoroot p τ.symmetrizedCartan (1 : Equiv.Perm (Fin τ.rank)) (tcRootSet τ O) := by
  refine ⟨latCorootZ τ.symmetrizedCartan (τ.rootCertificate.root i),
    Submodule.subset_span ⟨τ.rootCertificate.root i, ⟨i, hi, hil, rfl⟩, rfl⟩, fun k => ?_,
    0, Submodule.zero_mem _, ?_⟩
  · simp only [tcVec, tcEnt_map_mod, ZMod.intCast_mod]
    rw [tcCoTab_getD τ hil]
  · funext k
    have hk : (Equiv.symm (1 : Equiv.Perm (Fin τ.rank))) k = k := rfl
    simp [hk]

theorem tcSplitCore_sound (hp : p.Prime) (L : List (Array ℤ)) (h : tcSplitCore τ p L = true) :
    SplitCertSpec τ p (tcKerSub p τ.rank L) := by
  unfold tcSplitCore at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hL, hall⟩ := h
  intro μ hμ hμV hμ0 O hO hcard D hD
  have hmem : Array.ofFn μ ∈ tcAlcove τ p := mem_tcAlcove hμ
  have hvec : tcVec p τ.rank (Array.ofFn μ) = modP p μ := tcVec_ofFn μ
  have hinV : tcInV (tcEnv τ p L (tcSimpleGens τ.rank)) (Array.ofFn μ) = true := by
    rw [tcInV_iff]
    show tcVec p τ.rank _ ∈ tcKerSub p τ.rank L
    rw [hvec]
    exact hμV
  have hz : tcIsZero p τ.rank (Array.ofFn μ) = false := by
    by_contra hcon
    have h1 : tcIsZero p τ.rank (Array.ofFn μ) = true := by simpa using hcon
    rw [tcIsZero_iff, hvec] at h1
    exact hμ0 h1
  have h3 := hall _ hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', hz, hinV, tcEnv_n, tcEnv_R, tcEnv_G,
    Bool.and_eq_true, List.all_eq_true] at h3
  rcases h3 with (h3 | h3) | ⟨hcls, hcases⟩
  · exact absurd h3 (by simp)
  · exact absurd h3 (by simp)
  have hphi : ∀ i, i ∈ (List.range (tcRoots τ ()).size).filter (fun r =>
      tcDot τ.rank ((tcRoots τ ()).getD r #[]) (Array.ofFn μ) % (p : ℤ) == 0) ↔
      i < τ.rootCertificate.roots.length ∧
        latChar p (modP p μ) (τ.rootCertificate.root i) = 0 := fun i => by
    rw [mem_tcPhi_iff, hvec]
  obtain ⟨α, hα, hOeq⟩ := hO
  obtain ⟨i, hil, rfl⟩ := isRoot_iff_exists_index.mp hα.1
  have hiphi := (hphi i).mpr ⟨hil, hα.2⟩
  obtain ⟨hclsok, hcover⟩ := tcClassesOK_cover hcls
  obtain ⟨C, hC, hiC⟩ := hcover i hiphi
  have hCok := hclsok C hC
  have hcomp := tcClassOK_sound (modP p μ) _ hphi hCok hiC
  have hOC : O = tcRootSet τ C := by
    rw [hOeq, ← hcomp]
    ext β
    simp only [Set.mem_ofPred_eq, latPerm_one_iterate]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  subst hOC
  have key := tcCaseOK_sound hp hL (π := 1) (fun gi => commutesPi_perm_one _)
    (OT := Thunk.mk fun _ => tcOrbVerified (tcEnv τ p L (tcSimpleGens τ.rank)))
    (fun T hT => tcOrbVerified_sound L _ hT) (cover := true) (fun _ => ⟨rfl, rfl⟩)
    (b := Array.ofFn μ) (O := C) (ag := tcCoroots (tcEnv τ p L (tcSimpleGens τ.rank)) C)
    (fun a ha => by
      simp only [tcCoroots, List.mem_map] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact tcCoroot_mem_eigen_one C hj ((hphi j).mp (tcClassOK_subset hCok j hj)).1)
    (hcases C hC) hD hcard
  rw [hvec] at key
  exact key

end Split

section T0

theorem mem_tcCartanRows (τ : Tag) (g : Array ℤ) :
    g ∈ tcCartanRows τ () ↔ ∃ j : Fin τ.rank, g = Array.ofFn fun i => τ.cartan j i := by
  simp only [tcCartanRows, tcCartan, Array.toList_ofFn, List.mem_ofFn]
  exact exists_congr fun j => eq_comm

theorem t0Sub_eq_tcKerSub (hT0 : tcT0Check () = true)
    (hL : tcLOK (tcEnv Tag.E6 3 [tcT0Functional ()] (tcSimpleGens Tag.E6.rank)) = true) :
    t0Sub Tag.E6 3 = tcKerSub 3 Tag.E6.rank [tcT0Functional ()] := by
  have hp : Nat.Prime 3 := by norm_num
  simp only [tcT0Check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hT0
  obtain ⟨⟨hrows, hech⟩, hlen⟩ := hT0
  have hspan : Submodule.span (ZMod 3) {f | ∃ g ∈ tcCartanRows Tag.E6 (),
      f = tcVec 3 Tag.E6.rank g} = t0Sub Tag.E6 3 := by
    unfold t0Sub
    congr 1
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_range, mem_tcCartanRows]
    constructor
    · rintro ⟨g, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by rw [tcVec_ofFn]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, by rw [tcVec_ofFn]⟩
  have hle : t0Sub Tag.E6 3 ≤ tcKerSub 3 Tag.E6.rank [tcT0Functional ()] := by
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    rintro f ⟨g, hg, rfl⟩
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact (tcDot_mod_eq_zero_iff _ _).mp (hrows g hg)
  have hL' := hL
  simp only [tcLOK, Bool.and_eq_true, beq_iff_eq, tcEnv_p, tcEnv_n, tcEnv_L] at hL'
  have h1 := finrank_tcKerSub_le hp hL'
  obtain ⟨hmem, hfin⟩ := tcEchOK_sound hp hech
  have h2 := hfin (t0Sub Tag.E6 3) (fun r hr => by
    rw [← hspan]
    exact hmem r hr)
  rw [hlen] at h2
  refine eq_of_le_of_finrank_le_zmod hp hle ?_
  have h3 : Tag.E6.rank - [tcT0Functional ()].length = 5 := rfl
  rw [h3] at h1
  exact h1.trans h2

theorem splitCertSpecT0_of_check (h : splitT0OK = true) :
    SplitCertSpec Tag.E6 3 (t0Sub Tag.E6 3) := by
  simp only [splitT0OK, Bool.and_eq_true] at h
  obtain ⟨hT0, hcore⟩ := h
  have hL : tcLOK (tcEnv Tag.E6 3 [tcT0Functional ()] (tcSimpleGens Tag.E6.rank)) = true := by
    unfold tcSplitCore at hcore
    simp only [Bool.and_eq_true] at hcore
    exact hcore.1
  rw [t0Sub_eq_tcKerSub hT0 hL]
  exact tcSplitCore_sound (by norm_num) _ hcore

end T0

section Twist

theorem latPerm_e6Gamma_involutive (α : Fin Tag.E6.rank → ℤ) :
    latPerm e6Gamma (latPerm e6Gamma α) = α := by
  funext j
  have h1 : e6Gamma (e6Gamma j) = j :=
    (e6Gamma_symm (e6Gamma j)).symm.trans (Equiv.symm_apply_apply _ _)
  simp only [latPerm, e6Gamma_symm, h1]

theorem tcOrbit_eq_union {N : ℕ} {π : Equiv.Perm (Fin N)}
    (hπ : ∀ α, latPerm π (latPerm π α) = α) (R : (Fin N → ℤ) → (Fin N → ℤ) → Prop)
    (α : Fin N → ℤ) :
    {β | ∃ k : ℕ, R ((latPerm π)^[k] α) β} = {β | R α β} ∪ {β | R (latPerm π α) β} := by
  have hit : ∀ k : ℕ, (latPerm π)^[k] α = α ∨ (latPerm π)^[k] α = latPerm π α := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, hπ])
  ext β
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨k, hk⟩
    rcases hit k with h | h
    · exact Or.inl (h ▸ hk)
    · exact Or.inr (h ▸ hk)
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

end Twist

end CFSG.StandardType.StepTwoToralCert
