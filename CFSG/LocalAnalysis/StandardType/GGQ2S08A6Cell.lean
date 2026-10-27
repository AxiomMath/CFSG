module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Main
public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Coords
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixComponents
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly A6 Matrix

noncomputable def ggQ2a6PermHom : Equiv.Perm (Fin 6) →* (V6 ≃ₗ[ZMod 3] V6) where
  toFun := perm6
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    funext i
    rfl
  map_mul' := perm6_mul

theorem ggQ2a6_perm_mem {S : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (h : ∀ k : Fin 5, perm6 (Equiv.swap k.castSucc k.succ) ∈ S) (σ : Equiv.Perm (Fin 6)) :
    perm6 σ ∈ S := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨k, rfl⟩ := hτ
    exact h k
  | one =>
    rw [show perm6 1 = 1 from ggQ2a6PermHom.map_one]
    exact S.one_mem
  | mul τ ρ _ _ hτ hρ =>
    rw [perm6_mul]
    exact S.mul_mem hτ hρ

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

theorem ggQ2a6_map_automizer_L (M : GGQ2LDatum 3 Bs L x) (κ : M.V ≃ₗ[ZMod 3] V6)
    {e : Fin 5 ≃ M.Λ}
    (hκs : ∀ (k : Fin 5) (v : V6), κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) =
      perm6 (Equiv.swap k.castSucc k.succ) v) :
    (ggAutomizer L Bs).map (ggQ2CellLin M κ) = ggQ2a6PermHom.range := by
  have hs : ∀ k : Fin 5, ggQ2CellLin M κ (M.simple (e k)) = perm6 (Equiv.swap k.castSucc k.succ) :=
    fun k => LinearEquiv.ext fun v => hκs k v
  apply le_antisymm
  · rw [M.automizer_L, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨Equiv.swap (e.symm i).castSucc (e.symm i).succ, ?_⟩
    change perm6 _ = _
    rw [← hs, Equiv.apply_symm_apply]
  · rintro _ ⟨σ, rfl⟩
    refine ggQ2a6_perm_mem (fun k => ?_) σ
    refine ⟨M.simple (e k), ?_, hs k⟩
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨e k, rfl⟩

theorem ggQ2a6_hyp_of_test {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (h : TestLin.TestHyp ggQ2a6PermHom.range one6 A M) : A6Hyp A M where
  le := h.le
  perm_mem σ := h.W_le ⟨σ, rfl⟩
  noTransv := h.noTransv
  normW g hg hfix σ := by
    obtain ⟨τ, hτ⟩ := h.normW g hg hfix (perm6 σ) ⟨σ, rfl⟩
    exact ⟨τ, hτ.symm⟩
  stab_mem := h.stab_mem

variable [Finite G]

theorem ggQ2s08a6_refl
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    {labL : LargeEvenLabel} (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 5 ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter)
    (hTBN : GGQ2TableBNbr) (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ)
    (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hΓ : GGQ2GammaX 3 B Bs x L D J := hΓi hS rfl hI1 hCav
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hCav
    exact absurd (Nat.le_of_dvd one_pos hCav) (by norm_num)
  have hW5 : ∃ e : Fin 5 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 5).reindex e := by
    have hW : ∃ e : Fin labL.rank ≃ M.Λ, M.coxeter = (CoxeterMatrix.A labL.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, hLab.1] using hWeyl
    have key : ∀ n : ℕ, n = 5 → (∃ e : Fin n ≃ M.Λ, M.coxeter = (CoxeterMatrix.A n).reindex e) →
        ∃ e : Fin 5 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 5).reindex e := by
      rintro n rfl h
      exact h
    exact key _ hLab.2.1 hW
  obtain ⟨e, he⟩ := hW5
  obtain ⟨κ, hκx, hκs⟩ := ggQ2s08a6_coords M hShape he
  have hWimg := ggQ2a6_map_automizer_L M κ hκs
  have hH := ggQ2a6_hyp_of_test (ggQ2Cell_hyp hLB hP hS hΓ hAJ M κ hκx hWimg)
  have hφA : φ ∈ ggAutomizer ⊤ Bs :=
    mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top _, hInd.1, hInd.2⟩
  have hx' : ∀ (k : G) (ψ : MulAut ↥Bs), (∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = k * b * k⁻¹) →
      ψ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) → k * x * k⁻¹ ∈ Subgroup.zpowers x := by
    intro k ψ hk hψ
    have h1 := hk ⟨x, M.hx⟩
    rw [← h1]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hψ
    rw [← hm]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simp⟩
  by_cases hline : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)
  · exact hΓ g hInd.1 (hx' g φ hInd.2 hline)
  obtain ⟨ρ, hρM, hρR, hρx⟩ := ggQ2_exists_movesLine_refl_M hTBN hS hI1
  have hρline := ggQ2Cell_not_mem_zpowers_of_movesLine M.hx hρx
  have hmoves : ∀ ψ : MulAut ↥Bs, ψ ⟨x, M.hx⟩ ∉ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) →
      MovesLine6 (ggQ2CellLin M κ ψ) := fun ψ hψ =>
    ⟨fun h => hψ (ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx (Or.inl h)),
      fun h => hψ (ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx (Or.inr h))⟩
  rcases a6_main hH ⟨ρ, hρM, rfl⟩ (ggQ2Cell_isRefl M κ hρR) (hmoves ρ hρline) ⟨φ, hφA, rfl⟩
      (ggQ2Cell_isRefl M κ hRefl) (hmoves φ hline) with hin | hRO
  ·
    obtain ⟨φ', hφ'M, hφ'⟩ := hin
    obtain rfl := ggQ2CellLin_injective M κ hφ'
    exact ggQ2Cell_normalizes_of_mem hΓ M.hx hInd hφ'M
  ·
    obtain ⟨f, hfli, hfsum, hfperm, hfeven, hfmono⟩ := hRO
    have hΛ : Fintype.card M.Λ = 5 := (Fintype.card_congr e).symm.trans (Fintype.card_fin 5)
    have hdim : Module.finrank (ZMod 3) M.V = 6 := by rw [hShape.2.2.2.1, hΛ]
    haveI : Module.Finite (ZMod 3) M.V := Module.finite_of_finrank_eq_succ hdim
    have hli : LinearIndependent (ZMod 3) (fun j => κ.symm (f j)) :=
      hfli.map' κ.symm.toLinearMap κ.symm.ker
    refine ggQ2s08_roPrime_six hLB hP hRig hS hCav M hShape hMark hLab hWeyl
      (fun j => κ.symm (f j)) ⟨hli, ?_, ?_, ?_⟩ ?_ g φ hInd ?_
    · exact hli.span_eq_top_of_card_eq_finrank (by rw [hdim, Fintype.card_fin])
    · rw [← map_sum, hfsum, ← hκx, LinearEquiv.symm_apply_apply]
    · intro a ha
      obtain ⟨τ, hτ⟩ : ggQ2CellLin M κ a ∈ ggQ2a6PermHom.range := by
        rw [← hWimg]
        exact ⟨a, ha, rfl⟩
      obtain ⟨σ, hσ⟩ := hfperm τ
      refine ⟨σ, fun i => ?_⟩
      have h1 : ggQ2CellLin M κ a (f i) = f (σ i) := by
        rw [← hτ]
        exact hσ i
      rw [ggQ2CellLin_apply] at h1
      show ggLin (p := 3) M.model a (κ.symm (f i)) = κ.symm (f (σ i))
      rw [← h1, LinearEquiv.symm_apply_apply]
    · intro g' hg'
      obtain ⟨σ, ε, hε, hprod, hg'f⟩ := hg'
      have hmem := hfeven (ggLinConj κ g') ⟨σ, ε, hε, hprod, fun i => by
        change κ (g' (κ.symm (f i))) = ε i • f (σ i)
        rw [hg'f i, map_smul, LinearEquiv.apply_symm_apply]⟩
      obtain ⟨φ'', hφ''M, hφ''⟩ := hmem
      obtain ⟨k, hkG0, hkN, hk⟩ := mem_ggAutomizer_iff.mp hφ''M
      refine ⟨k, φ'', ⟨hkN, hk⟩, hkG0, ?_⟩
      refine LinearEquiv.ext fun v => ?_
      have := congrArg (fun T : V6 ≃ₗ[ZMod 3] V6 => κ.symm (T (κ v))) hφ''
      simpa [ggQ2CellLin_apply, ggLinConj] using this
    · obtain ⟨σ, ε, hε, hφf⟩ := hfmono
      refine ⟨σ, ε, hε, fun i => ?_⟩
      have h1 := hφf i
      rw [ggQ2CellLin_apply] at h1
      have h2 := congrArg κ.symm h1
      rw [LinearEquiv.symm_apply_apply, map_smul] at h2
      exact h2

end CFSG.StandardType

end
