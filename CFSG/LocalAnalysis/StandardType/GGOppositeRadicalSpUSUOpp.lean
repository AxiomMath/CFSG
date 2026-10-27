module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUStd
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUOpp

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary GGOppRad

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type*} [Group H] [Finite H] (ρ : H →* Module.End K V) {F : ReflForm K V}

theorem exists_isCompl_of_inf_eq_bot' [FiniteDimensional K V]
    (htv : ∀ x : V, F.β x x = 0 → ∃ h : H, ∀ v, ρ h v = v + F.β x v • x)
    (hsg : ∀ x y : V, F.β x x = 0 → F.β x y = 0 → ∃ (c : K) (h : H), (F.β y y = 0 → c = 0) ∧
      ∀ v, ρ h v = v + F.β x v • (y + c • x) + F.β y v • x)
    {A F' : ℕ → Submodule K V} {N N' : ℕ} (hA : IsSelfDual F A N) (hF' : IsSelfDual F F' N')
    (hbot : flagKernel ρ F' ⊓ flagStab ρ A = ⊥) (j : ℕ) : ∃ k, IsCompl (A k) (F' j) := by
  classical
  have h1 : ∀ g : H, g ∈ flagKernel ρ F' → (∀ i, ∀ v ∈ A i, ρ g v ∈ A i) → g = 1 := by
    intro g hg hgA
    have : g ∈ flagKernel ρ F' ⊓ flagStab ρ A :=
      ⟨hg, GGOppRad.mem_flagStab_of_forall ρ hgA⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have key : ∀ j, 2 * j ≤ N' → ∃ k, IsCompl (A k) (F' j) := by
    intro j hj
    by_cases hX : F' j = ⊥
    · exact ⟨N, by rw [hA.top N le_rfl, hX]; exact isCompl_top_bot⟩
    have hex : ∃ k, A (k + 1) ⊓ F' j ≠ ⊥ :=
      ⟨N, by rw [hA.top (N + 1) (by omega), top_inf_eq]; exact hX⟩
    set k := Nat.find hex with hk
    have hk1 : A (k + 1) ⊓ F' j ≠ ⊥ := Nat.find_spec hex
    have hk0 : A k ⊓ F' j = ⊥ := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, hA.zero, bot_inf_eq]
      · have := Nat.find_min hex (show k - 1 < k by omega)
        rwa [not_not, Nat.sub_add_cancel hpos] at this
    have hkN : k < N := by
      by_contra hkN
      rw [hA.top k (by omega), top_inf_eq] at hk0
      exact hX hk0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk1
    have hxA : x ∈ A (k + 1) := (Submodule.mem_inf.mp hx).1
    have hxF : x ∈ F' j := (Submodule.mem_inf.mp hx).2
    have hjN : j ≤ N' := by omega
    have hxF' : x ∈ F' (N' - j) := hF'.mono (by omega) hxF
    have hxx : F.β x x = 0 := hF'.mem_perp hjN hxF hxF'
    obtain ⟨t, ht⟩ := htv x hxx
    have ht' : ∀ v, ρ t v = v + F.β x v • x + F.β x v • (0 : V) := fun v => by
      rw [ht, smul_zero, add_zero]
    have htK : t ∈ flagKernel ρ F' :=
      mem_flagKernel_of_apply ρ hF' hjN hxF (zero_mem _) hxF' hxF' ht'
    obtain ⟨w, hw⟩ := exists_β_eq_one (F := F) hx0
    have ht1 : t ≠ 1 := ne_one_of_apply ρ ht' (v := w)
      (by rw [hw, one_smul, smul_zero, add_zero]; exact hx0)
    have htA : x ∈ A (N - k) → ∀ i, ∀ v ∈ A i, ρ t v ∈ A i := by
      intro hxk i v hv
      rw [ht]
      rcases Nat.lt_or_ge k i with hki | hik
      · exact add_mem hv (Submodule.smul_mem _ _ (hA.mono hki hxA))
      · rw [hA.mem_perp' hkN.le hxk (hA.mono hik hv), zero_smul, add_zero]
        exact hv
    by_cases hcase : 2 * (k + 1) ≤ N
    · exact absurd (h1 t htK (htA (hA.mono (by omega) hxA))) ht1
    refine ⟨k, disjoint_iff.mpr hk0, codisjoint_iff.mpr ?_⟩
    by_contra hne
    have hperp := perp_ne_bot F hne
    rw [F.perp_sup, hA.perp k hkN.le, hF'.perp j hjN] at hperp
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    have hyA : y ∈ A (N - k) := (Submodule.mem_inf.mp hy).1
    have hyF : y ∈ F' (N' - j) := (Submodule.mem_inf.mp hy).2
    by_cases hdep : ∃ c : K, y = c • x
    · obtain ⟨c, rfl⟩ := hdep
      have hc : c ≠ 0 := by
        rintro rfl
        exact hy0 (zero_smul K x)
      have hxk : x ∈ A (N - k) := by
        have := Submodule.smul_mem _ c⁻¹ hyA
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      exact ht1 (h1 t htK (htA hxk))
    have hxy : F.β x y = 0 := hF'.mem_perp hjN hxF hyF
    obtain ⟨c, s, hc0, hs⟩ := hsg x y hxx hxy
    have hyc : y + c • x ∈ F' (N' - j) := add_mem hyF (Submodule.smul_mem _ _ hxF')
    have hsK : s ∈ flagKernel ρ F' :=
      mem_flagKernel_of_apply ρ hF' hjN hxF hxF hyc hyF hs
    have hsA : ∀ i, ∀ v ∈ A i, ρ s v ∈ A i := by
      intro i v hv
      rw [hs]
      rcases Nat.lt_or_ge k i with hki | hik
      · refine add_mem (add_mem hv (Submodule.smul_mem _ _ (add_mem (hA.mono ?_ hyA)
          (Submodule.smul_mem _ _ (hA.mono hki hxA))))) (Submodule.smul_mem _ _ (hA.mono hki hxA))
        omega
      · rw [hA.mem_perp' hkN.le hyA (hA.mono hik hv), zero_smul, add_zero]
        rcases Nat.lt_or_ge i (N - k) with hi | hi
        · rw [hA.mem_perp (show k + 1 ≤ N by omega) hxA (hA.mono (by omega) hv), zero_smul,
            add_zero]
          exact hv
        · have hyy : F.β y y = 0 := hA.mem_perp' hkN.le hyA (hA.mono (by omega) hyA)
          rw [hc0 hyy, zero_smul, add_zero]
          exact add_mem hv (Submodule.smul_mem _ _ (hA.mono hi hyA))
    have hs1 := h1 s hsK hsA
    apply hdep
    refine ⟨-(c + F.β y w), ?_⟩
    have h2 := hs w
    rw [hs1, map_one, Module.End.one_apply, hw, one_smul, add_assoc, left_eq_add] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_smul, ← add_assoc]
    exact h2
  by_cases hj : 2 * j ≤ N'
  · exact key j hj
  by_cases hjN : N' ≤ j
  · exact ⟨0, by rw [hA.zero, hF'.top j hjN]; exact isCompl_bot_top⟩
  obtain ⟨k, hk⟩ := key (N' - j) (by omega)
  have hk' : IsCompl (A (min k N)) (F' (N' - j)) := by
    rcases le_total k N with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h, hA.top N le_rfl, ← hA.top k h]
  have := isCompl_perp F hk'
  rw [hA.perp _ (min_le_right k N), hF'.perp _ (Nat.sub_le N' j),
    Nat.sub_sub_self (by omega)] at this
  exact ⟨_, this⟩

end General

section Unitary

variable {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

theorem isSULevel_idx {n M N' : ℕ} {ℓ : Fin n → ℕ} (hℓ : IsSULevel M ℓ)
    {F' : ℕ → Submodule F (Fin n → F)} (hF' : IsSelfDual (suForm σ hσ n) F' N')
    (D : OppData ℓ F') : IsSULevel (N' - 1) D.idx := by
  have hdual : ∀ j ≤ N', stdFlag (K := F) ℓ (M + 1 - D.level j) = stdFlag ℓ (D.level (N' - j)) := by
    intro j hj
    have h1 := isCompl_perp (suForm σ hσ n) (D.isCompl_level j)
    rw [perp_stdFlag_su σ hσ hℓ, hF'.perp j hj] at h1
    exact stdFlag_eq_of_isCompl h1 (D.isCompl_level (N' - j))
  have key : ∀ a, ∀ j ≤ N', D.idx (Fin.rev a) < N' - j ↔ ¬ D.idx a < j := by
    intro a j hj
    have h2 : ℓ (Fin.rev a) < D.level (N' - j) ↔ ℓ (Fin.rev a) < M + 1 - D.level j := by
      have e1 := single_mem_stdFlag (K := F) (ℓ := ℓ) (k := D.level (N' - j)) (a := Fin.rev a)
      have e2 := single_mem_stdFlag (K := F) (ℓ := ℓ) (k := M + 1 - D.level j) (a := Fin.rev a)
      rw [← e1, ← e2, hdual j hj]
    rw [D.idx_lt_iff, D.idx_lt_iff, ← not_lt, h2]
    have := hℓ a
    omega
  have hlt : ∀ a, D.idx a < N' := fun a => D.idx_lt_iff.mpr (by
    rw [D.level_eq_zero (hF'.top N' le_rfl)]
    exact Nat.zero_le _)
  intro t
  have k1 := (key t (D.idx t) (hlt _).le).mpr (lt_irrefl _)
  have k2 := mt (key t (D.idx t + 1) (hlt _)).mp (not_not.mpr (Nat.lt_succ_self _))
  have := hlt t
  omega

theorem suForm_mulVec₂ {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) (u v : Fin n → F) :
    (suForm σ hσ n).β (A *ᵥ u) (B *ᵥ v) =
      (σ ∘ u) ⬝ᵥ ((conjTr σ A * antidiag n * B) *ᵥ v) := by
  rw [suForm_β_eq]
  have h1 : (σ ∘ (A *ᵥ u)) = (A.map σ) *ᵥ (σ ∘ u) := by
    funext i
    exact RingHom.map_mulVec (σ : F →+* F) A u i
  rw [h1, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
    mulVec_mulVec, mulVec_mulVec, conjTr, Matrix.mul_assoc]

variable [CharP F 2]

variable (F) in
@[expose] def suJsl (n : ℕ) : Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨antidiag n, det_antidiag n⟩

theorem suJsl_inv {n : ℕ} : (suJsl F n)⁻¹ = suJsl F n :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact antidiag_mul_antidiag n))

@[expose] def adjSU {n : ℕ} (g : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  suJsl F n * tInv (Matrix.SpecialLinearGroup.map (σ : F →+* F) g) * suJsl F n

include hσ in
theorem conjTr_adjSU_mul {n : ℕ} (g : Matrix.SpecialLinearGroup (Fin n) F) :
    conjTr σ ((adjSU σ g : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        antidiag n * (g : Matrix (Fin n) (Fin n) F) = antidiag n := by
  have hinv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hJσ : (antidiag n : Matrix (Fin n) (Fin n) F).map σ = antidiag n := by
    ext a b
    simp only [map_apply, antidiag, of_apply]
    by_cases h : b = Fin.rev a
    · rw [ite_eq_left h, map_one]
    · rw [ite_eq_right h, map_zero]
  have hσσ : ∀ M : Matrix (Fin n) (Fin n) F, (M.map σ).map σ = M := fun M => by
    ext a b
    simp [hσ]
  have hJt : (antidiag n : Matrix (Fin n) (Fin n) F)ᵀ = antidiag n := by
    have := conjTr_antidiag (σ := σ) n
    rwa [conjTr, hJσ] at this
  have hcoe : ((adjSU σ g : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      antidiag n * (((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F).map σ)ᵀ * antidiag n := by
    rw [adjSU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    change antidiag n * (((Matrix.SpecialLinearGroup.map (σ : F →+* F) g)⁻¹ :
      Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * antidiag n = _
    rw [← map_inv, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rfl
  rw [hcoe, conjTr, Matrix.map_mul, Matrix.map_mul, hJσ, ← transpose_map, hσσ,
    transpose_mul, transpose_mul, transpose_transpose, hJt]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (antidiag n) (antidiag n), antidiag_mul_antidiag, Matrix.one_mul, hinv,
    Matrix.mul_one]

include hσ in
theorem suForm_adjSU {n : ℕ} (g : Matrix.SpecialLinearGroup (Fin n) F) (u v : Fin n → F) :
    (suForm σ hσ n).β (slRep (adjSU σ g) u) (slRep g v) = (suForm σ hσ n).β u v := by
  rw [slRep_apply, slRep_apply, suForm_mulVec₂, conjTr_adjSU_mul σ hσ, ← suForm_β_eq]

include hσ in
theorem perp_map_slRep_su {n : ℕ} (g : Matrix.SpecialLinearGroup (Fin n) F)
    (X : Submodule F (Fin n → F)) :
    (suForm σ hσ n).perp (X.map (slRep g)) =
      ((suForm σ hσ n).perp X).map (slRep (adjSU σ g)) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    apply (suForm σ hσ n).refl
    change (suForm σ hσ n).β (slRep (adjSU σ g) a) (slRep g x) = 0
    rw [suForm_adjSU σ hσ]
    exact (suForm σ hσ n).refl _ _ (ha x hx)
  · have h1 := (suForm σ hσ n).finrank_perp (X.map (slRep g))
    have h2 := (suForm σ hσ n).finrank_perp X
    have e1 : Module.finrank F (X.map (slRep g)) = Module.finrank F X :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (fun x y hxy => by
        simpa only [rep_inv_apply_rep] using congrArg (slRep g⁻¹) hxy) _)).symm
    have e2 : Module.finrank F (((suForm σ hσ n).perp X).map (slRep (adjSU σ g))) =
        Module.finrank F ((suForm σ hσ n).perp X) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (fun x y hxy => by
        simpa only [rep_inv_apply_rep] using congrArg (slRep (adjSU σ g)⁻¹) hxy) _)).symm
    omega

include hσ in
theorem flagMap_adjSU_of_isSelfDual {n N : ℕ} {E F' : ℕ → Submodule F (Fin n → F)}
    (hE : IsSelfDual (suForm σ hσ n) E N) (hF : IsSelfDual (suForm σ hσ n) F' N)
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : flagMap slRep g E = F') :
    flagMap slRep (adjSU σ g) E = F' := by
  have key : ∀ k ≤ N, flagMap slRep (adjSU σ g) E k = F' k := by
    intro k hk
    have h1 : E k = (suForm σ hσ n).perp (E (N - k)) := by
      rw [hE.perp _ (Nat.sub_le N k), Nat.sub_sub_self hk]
    have h2 : F' k = (suForm σ hσ n).perp (F' (N - k)) := by
      rw [hF.perp _ (Nat.sub_le N k), Nat.sub_sub_self hk]
    change (E k).map (slRep (adjSU σ g)) = F' k
    rw [h1, ← perp_map_slRep_su σ hσ, h2, ← hg]
    rfl
  funext k
  rcases le_total k N with hk | hk
  · exact key k hk
  · have := key N le_rfl
    change (E N).map (slRep (adjSU σ g)) = F' N at this
    rw [hE.top N le_rfl, hF.top N le_rfl] at this
    change (E k).map (slRep (adjSU σ g)) = F' k
    rw [hE.top k hk, hF.top k hk]
    exact this

theorem flagMap_suJsl {n : ℕ} (ℓ : Fin n → ℕ) :
    flagMap slRep (suJsl F n) (stdFlag ℓ) = stdFlag (ℓ ∘ Fin.rev) := by
  funext k
  have hle : flagMap slRep (suJsl F n) (stdFlag ℓ) k ≤ stdFlag (ℓ ∘ Fin.rev) k := by
    rintro _ ⟨w, hw, rfl⟩ a ha
    change (slRep (suJsl F n) w) a = 0
    rw [slRep_apply]
    change (antidiag n *ᵥ w) a = 0
    rw [antidiag_mulVec_apply]
    exact hw _ ha
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have e1 : Module.finrank F ((stdFlag (K := F) ℓ k).map (slRep (suJsl F n))) =
      Module.finrank F (stdFlag (K := F) ℓ k) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (fun x y hxy => by
      simpa only [rep_inv_apply_rep] using congrArg (slRep (suJsl F n)⁻¹) hxy) _)).symm
  change Module.finrank F ((stdFlag (K := F) ℓ k).map (slRep (suJsl F n))) = _
  rw [e1, finrank_stdFlag, finrank_stdFlag]
  exact Fintype.card_congr ((Fin.revPerm (n := n)).subtypeEquiv fun a => by
    simp [Function.comp_apply, Fin.revPerm_apply])

theorem adjSU_mem_stdUop [Finite F] {n C : ℕ} {i : Fin n → ℕ} (hi : IsSULevel C i)
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : g ∈ stdUop (K := F) i) :
    adjSU σ g ∈ stdUop (K := F) i := by
  have h0 : Matrix.SpecialLinearGroup.map (σ : F →+* F) g ∈ stdUop (K := F) i := by
    rw [mem_stdUop_iff] at hg ⊢
    intro c a hac
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
      hg c a hac]
    by_cases hca : c = a
    · subst hca
      simp
    · simp [Matrix.one_apply_ne hca]
  have h1 : tInv (Matrix.SpecialLinearGroup.map (σ : F →+* F) g) ∈ stdU (K := F) i := by
    obtain ⟨h, hh, hh'⟩ := h0
    have : tInv (tInv h) = h := tInv.symm_apply_apply h
    rw [← hh']
    change tInv (tInv h) ∈ _
    rw [this]
    exact hh
  have h2 : adjSU σ g ∈ stdU (K := F) (i ∘ Fin.rev) := by
    rw [stdU, ← flagMap_suJsl, flagKernel_flagMap]
    refine ⟨tInv (Matrix.SpecialLinearGroup.map (σ : F →+* F) g), h1, ?_⟩
    change suJsl F n * _ * (suJsl F n)⁻¹ = _
    rw [suJsl_inv]
    rfl
  rw [mem_stdUop_iff]
  rw [mem_stdU_iff] at h2
  intro c a hac
  refine h2 c a fun h => hac ?_
  have := hi c
  have := hi a
  simp only [Function.comp_apply] at h
  omega

theorem exists_eq_flagMap_of_isCompl_su [Finite F] {n M N' : ℕ} {ℓ : Fin n → ℕ}
    (hℓ : IsSULevel M ℓ) {F' : ℕ → Submodule F (Fin n → F)}
    (hF' : IsSelfDual (suForm σ hσ n) F' N') (hN' : 1 ≤ N')
    (hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j)) :
    ∃ (u : SU σ n) (i : Fin n → ℕ), IsSULevel (N' - 1) i ∧ u ∈ suU σ ℓ ∧
      GGOppRad.flagMap (natRep (SU σ n)) u (stdFlag i) = F' ∧
      suU σ (i ∘ Fin.rev) ≤ suU σ ℓ := by
  let D : OppData ℓ F' := ⟨hF'.mono, hF'.zero, ⟨N', hF'.top N' le_rfl⟩, hcompl⟩
  have hi : IsSULevel (N' - 1) D.idx := isSULevel_idx σ hσ hℓ hF' D
  have hE : IsSelfDual (suForm σ hσ n) (stdFlag D.idx) N' := by
    have := isSelfDual_stdFlag_su σ hσ hi
    rwa [Nat.sub_add_cancel hN'] at this
  have hg : D.elt ∈ stdUop (K := F) D.idx := D.elt_mem_stdUop
  have hgF : flagMap slRep D.elt (stdFlag D.idx) = F' := D.flagMap_elt
  have hα : adjSU σ D.elt = D.elt :=
    eq_of_flagMap_eq (adjSU_mem_stdUop σ hi hg) hg
      (by rw [flagMap_adjSU_of_isSelfDual σ hσ hE hF' hgF, hgF])
  have hsu : conjTr σ (D.elt : Matrix (Fin n) (Fin n) F) * antidiag n *
      (D.elt : Matrix (Fin n) (Fin n) F) = antidiag n := by
    have := conjTr_adjSU_mul σ hσ D.elt
    rwa [hα] at this
  let u : SU σ n := ⟨Matrix.SpecialLinearGroup.toGL D.elt, mem_SU.mpr ⟨D.elt.2, hsu⟩⟩
  have hcond : ∀ c a, D.idx a < D.idx c → ℓ c < ℓ a := fun c a h => by
    have h1 : ¬ D.level (D.idx a + 1) ≤ ℓ c := fun h' => by
      have := D.idx_lt_iff.mpr h'
      omega
    have h2 : D.level (D.idx a + 1) ≤ ℓ a := D.idx_lt_iff.mp (Nat.lt_succ_self _)
    omega
  refine ⟨u, D.idx, hi, ?_, ?_, ?_⟩
  · rw [mem_suU_iff]
    intro c a hca
    exact (mem_stdU_iff.mp (D.stdUop_idx_le hg)) c a hca
  · funext k
    have h1 := congrFun hgF k
    change (stdFlag D.idx k).map (slRep D.elt) = F' k at h1
    change (stdFlag D.idx k).map (natRep (SU σ n) u) = F' k
    rw [← h1]
    congr 1
  · intro g hgsw
    rw [mem_suU_comp_rev_iff hi] at hgsw
    rw [mem_suU_iff]
    intro c a hca
    exact hgsw c a fun h => hca (hcond c a h)

end Unitary

end GGOppRadSpU

end CFSG.StandardType
