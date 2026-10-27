module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph

public section

namespace CFSG.Quasithin

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Module Subgroup

namespace B69

variable {K : Type} [Field K]

@[expose] def TypePres (φ : MulAut (projectiveSL 3 K)) : Prop :=
  ∀ W : Submodule K (Fin 3 → K), finrank K W = 1 →
    ∃ W' : Submodule K (Fin 3 → K), finrank K W' = 1 ∧
      (projStabilizer W).map (φ : projectiveSL 3 K →* projectiveSL 3 K) = projStabilizer W'

section Geometry

variable [Finite K] [CharP K 2]

theorem TypePres.hyperplane {φ : MulAut (projectiveSL 3 K)} (hφ : TypePres φ)
    (H : Submodule K (Fin 3 → K)) (hH : finrank K H = 2) :
    ∃ H' : Submodule K (Fin 3 → K), finrank K H' = 2 ∧
      (projStabilizer H).map (φ : projectiveSL 3 K →* projectiveSL 3 K) = projStabilizer H' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, haut⟩ := incidence_graph (K := K) (n := 3) 2 le_rfl
  obtain ⟨hE, hdisjE, -, -, -⟩ := intrinsic_extremal_parabolics (K := K) (n := 3) 2 le_rfl
  have hmemL : ∀ L : Submodule K (Fin 3 → K), finrank K L = 1 →
      projStabilizer L ∈ extremalParabolics (projectiveSL 3 K) 2 := fun L hL => by
    rw [hE]
    exact Or.inl ⟨L, hL, rfl⟩
  have hmemH : ∀ H : Submodule K (Fin 3 → K), finrank K H = 3 - 1 →
      projStabilizer H ∈ extremalParabolics (projectiveSL 3 K) 2 := fun H hH => by
    rw [hE]
    exact Or.inr ⟨H, hH, rfl⟩
  obtain ⟨Φ, hΦ, hpres⟩ := haut φ
  have hF1 : finrank K (flagSpace 3 K 1) = 1 := finrank_flagSpace (by omega)
  have hnoswap : ¬((∀ M, M ∈ pointVertices 3 K 2 → Φ M ∈ hyperplaneVertices 3 K 2) ∧
      ∀ M, M ∈ hyperplaneVertices 3 K 2 → Φ M ∈ pointVertices 3 K 2) := by
    rintro ⟨h1, -⟩
    obtain ⟨H, hH, hMH⟩ := h1 ⟨_, hmemL _ hF1⟩ ⟨_, hF1, rfl⟩
    obtain ⟨L', hL', hL'eq⟩ := hφ _ hF1
    rw [hΦ] at hMH
    exact Set.disjoint_left.mp hdisjE ⟨L', hL', rfl⟩ ⟨H, hH, hMH.symm.trans hL'eq⟩
  obtain ⟨-, hhh⟩ := hpres.resolve_right hnoswap
  obtain ⟨H', hH', hH'eq⟩ := hhh ⟨_, hmemH H (by simpa using hH)⟩ ⟨H, by simpa using hH, rfl⟩
  rw [hΦ] at hH'eq
  exact ⟨H', by simpa using hH', hH'eq⟩

omit [Finite K] [CharP K 2] in
theorem finrank_map_flagSpace (g : Matrix.SpecialLinearGroup (Fin 3) K) {d : ℕ} (hd : d ≤ 3) :
    finrank K ((flagSpace 3 K d).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) = d := by
  rw [show finrank K ((flagSpace 3 K d).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K))) =
      finrank K (flagSpace 3 K d) from LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _,
    finrank_flagSpace hd]

theorem exists_two_parabolics (S₀ : Sylow 2 (projectiveSL 3 K)) :
    ∃ Q₁ Q₂ : Subgroup (projectiveSL 3 K), IsCoatom Q₁ ∧ IsCoatom Q₂ ∧ Q₁ ≠ Q₂ ∧
      (S₀ : Subgroup (projectiveSL 3 K)) ≤ Q₁ ∧ (S₀ : Subgroup (projectiveSL 3 K)) ≤ Q₂ ∧
      ∀ φ : MulAut (projectiveSL 3 K),
        (S₀ : Subgroup (projectiveSL 3 K)).map (φ : projectiveSL 3 K →* projectiveSL 3 K) = S₀ →
        TypePres φ →
          Q₁.map (φ : projectiveSL 3 K →* projectiveSL 3 K) = Q₁ ∧
            Q₂.map (φ : projectiveSL 3 K →* projectiveSL 3 K) = Q₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM, hinj, -⟩ := maximal_parabolics (K := K) (n := 3) 2 (by norm_num)
  have hB₀mem : normalizer ((S₀ : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) ∈
      sylowNormalizers (projectiveSL 3 K) 2 := ⟨S₀, rfl⟩
  rw [sylowNormalizers_eq (K := K) (n := 3) 2 (by norm_num)] at hB₀mem
  obtain ⟨x, hx⟩ := hB₀mem
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  set B₀ := normalizer ((S₀ : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) with hB₀
  set L₁ := (flagSpace 3 K 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) with hL₁def
  set L₂ := (flagSpace 3 K 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) with hL₂def
  have hL₁ : finrank K L₁ = 1 := finrank_map_flagSpace g (by norm_num)
  have hL₂ : finrank K L₂ = 2 := finrank_map_flagSpace g (by norm_num)
  have hL₁b := bot_lt_and_lt_top_of_finrank (K := K) (n := 3) (W := L₁) (by omega) (by omega)
  have hL₂b := bot_lt_and_lt_top_of_finrank (K := K) (n := 3) (W := L₂) (by omega) (by omega)
  have hB₁ : B₀ ≤ projStabilizer L₁ := by
    rw [hx, hL₁def, ← projStabilizer_map_conj]
    exact map_mono (projUpperTriangular_le_projStabilizer 1)
  have hB₂ : B₀ ≤ projStabilizer L₂ := by
    rw [hx, hL₂def, ← projStabilizer_map_conj]
    exact map_mono (projUpperTriangular_le_projStabilizer 2)
  have hS₀B : (S₀ : Subgroup (projectiveSL 3 K)) ≤ B₀ := Subgroup.le_normalizer
  refine ⟨projStabilizer L₁, projStabilizer L₂, isCoatom_projStabilizer hL₁b.1 hL₁b.2,
    isCoatom_projStabilizer hL₂b.1 hL₂b.2, fun h => ?_, hS₀B.trans hB₁, hS₀B.trans hB₂,
    fun φ hφS hφ => ?_⟩
  · have h12 := congrArg (fun W : Submodule K (Fin 3 → K) => finrank K W) (hinj hL₁b hL₂b h)
    omega
  · have hφB : B₀.map (φ : projectiveSL 3 K →* projectiveSL 3 K) = B₀ := by
      rw [hB₀]
      have h1 : ((normalizer ((S₀ : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K))).map
          φ.toMonoidHom) = normalizer (((S₀ : Subgroup (projectiveSL 3 K)).map φ.toMonoidHom :
            Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) :=
        Subgroup.map_equiv_normalizer_eq _ φ
      have h2 : (S₀ : Subgroup (projectiveSL 3 K)).map φ.toMonoidHom = S₀ := hφS
      rw [h2] at h1
      exact h1
    refine ⟨?_, ?_⟩
    · obtain ⟨L', hL', hL'eq⟩ := hφ L₁ hL₁
      have hle : B₀ ≤ projStabilizer L' := by
        rw [← hL'eq, ← hφB]
        exact map_mono hB₁
      rw [hL'eq]
      have hL'b := bot_lt_and_lt_top_of_finrank (K := K) (n := 3) (W := L') (by omega) (by omega)
      have h1 : L' = (flagSpace 3 K (finrank K L')).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) :=
        eq_map_flagSpace_of_le (by rw [← hx]; exact hle)
      rw [hL'] at h1
      rw [h1]
    · obtain ⟨L', hL', hL'eq⟩ := hφ.hyperplane L₂ hL₂
      have hle : B₀ ≤ projStabilizer L' := by
        rw [← hL'eq, ← hφB]
        exact map_mono hB₂
      rw [hL'eq]
      have h1 : L' = (flagSpace 3 K (finrank K L')).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) :=
        eq_map_flagSpace_of_le (by rw [← hx]; exact hle)
      rw [hL'] at h1
      rw [h1]

end Geometry

section Abstract

variable {Λ : Type} [Group Λ] [Finite Λ]

@[expose] def autStab (R : Subgroup Λ) : Subgroup (MulAut Λ) where
  carrier := {ψ | R.map (ψ : Λ →* Λ) = R}
  one_mem' := by
    show R.map ((1 : MulAut Λ) : Λ →* Λ) = R
    ext x
    simp
  mul_mem' {a b} ha hb := by
    have ha' : R.map (a : Λ →* Λ) = R := ha
    have hb' : R.map (b : Λ →* Λ) = R := hb
    show R.map ((a * b : MulAut Λ) : Λ →* Λ) = R
    have : ((a * b : MulAut Λ) : Λ →* Λ) = (a : Λ →* Λ).comp (b : Λ →* Λ) := rfl
    rw [this, ← Subgroup.map_map, hb', ha']
  inv_mem' {a} ha := by
    have ha' : R.map (a : Λ →* Λ) = R := ha
    show R.map ((a⁻¹ : MulAut Λ) : Λ →* Λ) = R
    conv_lhs => rw [← ha']
    rw [Subgroup.map_map]
    have : ((a⁻¹ : MulAut Λ) : Λ →* Λ).comp (a : Λ →* Λ) = MonoidHom.id Λ := by
      ext x
      simp
    rw [this, Subgroup.map_id]

omit [Finite Λ] in
theorem mem_autStab {R : Subgroup Λ} {ψ : MulAut Λ} :
    ψ ∈ autStab R ↔ R.map (ψ : Λ →* Λ) = R := Iff.rfl

end Abstract

section Abstract2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {Λ : Type} [Group Λ] [Finite Λ]

omit [Finite Λ] in
theorem map_map_congr {P : Type} [Group P] (ι : Λ ≃* P) (φ : MulAut Λ) (Q : Subgroup P) :
    (Q.map (ι.symm : P →* Λ)).map (φ : Λ →* Λ) =
      (Q.map ((MulAut.congr ι φ : MulAut P) : P →* P)).map (ι.symm : P →* Λ) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.congr_apply]

omit [Finite Λ] in
theorem conj_mem_autStab {R : Subgroup Λ} {x : Λ} (hx : x ∈ R) : MulAut.conj x ∈ autStab R := by
  rw [mem_autStab]
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa [MulAut.conj_apply] using R.mul_mem (R.mul_mem hx hr) (R.inv_mem hx)
  · intro hy
    refine ⟨x⁻¹ * y * x, R.mul_mem (R.mul_mem (R.inv_mem hx) hy) hx, ?_⟩
    show x * (x⁻¹ * y * x) * x⁻¹ = y
    group

omit [Finite Λ] in
theorem exists_not_typePres [IsSimpleGroup Λ] (ι : Λ ≃* projectiveSL 3 K) {S₀ : Subgroup Λ}
    (hS₀p : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index) (hS₀ne : S₀ ≠ ⊥)
    {Ybar Tbar Mbar : Subgroup (MulAut Λ)} (hInn : ∀ x : Λ, MulAut.conj x ∈ Ybar)
    (hTM : Tbar ≤ Mbar) (hMY : Mbar < Ybar)
    (hgen : ∀ V : Subgroup (MulAut Λ), Tbar ≤ V → (∀ x : Λ, MulAut.conj x ∈ V) → Ybar ≤ V)
    (hmax : ∀ V : Subgroup (MulAut Λ), Tbar ≤ V → V < Ybar → V ≤ Mbar)
    (hTS : ∀ φ ∈ Tbar, S₀.map (φ : Λ →* Λ) = S₀) :
    ∃ φ ∈ Tbar, ¬ TypePres (MulAut.congr ι φ) := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀'p : IsPGroup 2 ↥(S₀.map (ι : Λ →* projectiveSL 3 K)) :=
    hS₀p.of_equiv (S₀.equivMapOfInjective (ι : Λ →* projectiveSL 3 K) ι.injective)
  have hS₀'i : ¬ 2 ∣ (S₀.map (ι : Λ →* projectiveSL 3 K)).index := by
    rw [Subgroup.index_map_equiv]
    exact hS₀i
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQ12, hSQ₁, hSQ₂, hfix⟩ := exists_two_parabolics (K := K)
    (hS₀'p.toSylow hS₀'i)
  have hsyl : ((hS₀'p.toSylow hS₀'i : Sylow 2 (projectiveSL 3 K)) : Subgroup (projectiveSL 3 K)) =
      S₀.map (ι : Λ →* projectiveSL 3 K) := rfl
  rw [hsyl] at hSQ₁ hSQ₂ hfix
  set R₁ : Subgroup Λ := Q₁.map (ι.symm : projectiveSL 3 K →* Λ) with hR₁
  set R₂ : Subgroup Λ := Q₂.map (ι.symm : projectiveSL 3 K →* Λ) with hR₂
  have hmapι : ∀ Q : Subgroup (projectiveSL 3 K),
      (Q.map (ι.symm : projectiveSL 3 K →* Λ)).map (ι : Λ →* projectiveSL 3 K) = Q := by
    intro Q
    rw [Subgroup.map_map]
    have : (ι : Λ →* projectiveSL 3 K).comp (ι.symm : projectiveSL 3 K →* Λ) = MonoidHom.id _ := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  have hSR : ∀ Q : Subgroup (projectiveSL 3 K), S₀.map (ι : Λ →* projectiveSL 3 K) ≤ Q →
      S₀ ≤ Q.map (ι.symm : projectiveSL 3 K →* Λ) := by
    intro Q hQ x hx
    exact ⟨ι x, hQ ⟨x, hx, rfl⟩, by simp⟩
  have hR₁top : R₁ ≠ ⊤ := fun h => hQ₁.1 (by
    rw [← hmapι Q₁, ← hR₁, h, Subgroup.map_top_of_surjective _ ι.surjective])
  have hR₂top : R₂ ≠ ⊤ := fun h => hQ₂.1 (by
    rw [← hmapι Q₂, ← hR₂, h, Subgroup.map_top_of_surjective _ ι.surjective])
  have hR₁bot : R₁ ≠ ⊥ := fun h => hS₀ne (le_bot_iff.1 (h ▸ hSR Q₁ hSQ₁))
  have hR₂bot : R₂ ≠ ⊥ := fun h => hS₀ne (le_bot_iff.1 (h ▸ hSR Q₂ hSQ₂))
  have hsup : Q₁ ⊔ Q₂ = ⊤ := by
    rcases hQ₁.le_iff.1 (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂) with h | h
    · exact h
    · exfalso
      have hle : Q₂ ≤ Q₁ := h ▸ le_sup_right
      rcases hQ₂.le_iff.1 hle with h' | h'
      · exact hQ₁.1 h'
      · exact hQ12 h'
  have hR₁₂ : R₁ ⊔ R₂ = ⊤ := by
    rw [hR₁, hR₂, ← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ ι.symm.surjective]
  have hTR : ∀ φ ∈ Tbar, φ ∈ autStab R₁ ∧ φ ∈ autStab R₂ := by
    intro φ hφ
    have hS' : (S₀.map (ι : Λ →* projectiveSL 3 K)).map
        ((MulAut.congr ι φ : MulAut (projectiveSL 3 K)) : projectiveSL 3 K →* projectiveSL 3 K) =
          S₀.map (ι : Λ →* projectiveSL 3 K) := by
      rw [Subgroup.map_map]
      have : ((MulAut.congr ι φ : MulAut (projectiveSL 3 K)) :
          projectiveSL 3 K →* projectiveSL 3 K).comp (ι : Λ →* projectiveSL 3 K) =
          (ι : Λ →* projectiveSL 3 K).comp (φ : Λ →* Λ) := by
        ext x
        simp [MulAut.congr_apply]
      rw [this, ← Subgroup.map_map, hTS φ hφ]
    obtain ⟨h1, h2⟩ := hfix (MulAut.congr ι φ) hS' (hcon φ hφ)
    refine ⟨?_, ?_⟩
    · rw [mem_autStab, hR₁, map_map_congr, h1]
    · rw [mem_autStab, hR₂, map_map_congr, h2]
  have hprop : ∀ R : Subgroup Λ, R ≠ ⊤ → R ≠ ⊥ → (∀ φ ∈ Tbar, φ ∈ autStab R) →
      ∀ x ∈ R, MulAut.conj x ∈ Mbar := by
    intro R hRt hRb hTR' x hx
    have hlt : Ybar ⊓ autStab R < Ybar := by
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      have hY : Ybar ≤ autStab R := inf_eq_left.1 heq
      have hnorm : R.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have := hY (hInn g)
        rw [mem_autStab] at this
        rw [← this]
        exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
      rcases hnorm.eq_bot_or_eq_top with h | h
      · exact hRb h
      · exact hRt h
    have hTV : Tbar ≤ Ybar ⊓ autStab R := fun φ hφ => ⟨(hTM.trans hMY.le) hφ, hTR' φ hφ⟩
    exact hmax _ hTV hlt ⟨hInn x, conj_mem_autStab hx⟩
  have hInnM : ∀ x : Λ, MulAut.conj x ∈ Mbar := by
    have hH : Mbar.comap (MulAut.conj : Λ →* MulAut Λ) = ⊤ := by
      rw [eq_top_iff, ← hR₁₂]
      exact sup_le (fun x hx => hprop R₁ hR₁top hR₁bot (fun φ hφ => (hTR φ hφ).1) x hx)
        (fun x hx => hprop R₂ hR₂top hR₂bot (fun φ hφ => (hTR φ hφ).2) x hx)
    intro x
    have : x ∈ Mbar.comap (MulAut.conj : Λ →* MulAut Λ) := by rw [hH]; trivial
    exact this
  exact absurd (hgen Mbar hTM hInnM) (not_le_of_gt hMY)

end Abstract2

end B69

end CFSG.Quasithin
