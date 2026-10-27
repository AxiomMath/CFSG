module

public import CFSG.RankThree.GF2n.Stroth80.Sec312Quot

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

private def elat_stab {m : ℕ} {K : Type} [Field K] (W : Submodule K (Fin m → K)) :
    Subgroup (GL (Fin m) K) where
  carrier := {g | ∀ v : Fin m → K, (g : Matrix (Fin m) (Fin m) K) *ᵥ v - v ∈ W}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro g h hg hh v
    have hg0 : ∀ w : Fin m → K, (g : Matrix (Fin m) (Fin m) K) *ᵥ w - w ∈ W := hg
    have hh0 : ∀ w : Fin m → K, (h : Matrix (Fin m) (Fin m) K) *ᵥ w - w ∈ W := hh
    have hgW : ∀ w ∈ W, (g : Matrix (Fin m) (Fin m) K) *ᵥ w ∈ W := fun w hw => by
      have e : (g : Matrix (Fin m) (Fin m) K) *ᵥ w =
          (g : Matrix (Fin m) (Fin m) K) *ᵥ w - w + w := (sub_add_cancel _ _).symm
      rw [e]
      exact W.add_mem (hg0 w) hw
    have e : ((g * h : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v - v =
        (g : Matrix (Fin m) (Fin m) K) *ᵥ ((h : Matrix (Fin m) (Fin m) K) *ᵥ v - v) +
          ((g : Matrix (Fin m) (Fin m) K) *ᵥ v - v) := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      abel
    rw [e]
    exact W.add_mem (hgW _ (hh0 v)) (hg0 v)
  inv_mem' := by
    intro g hg v
    have hg0 : ∀ w : Fin m → K, (g : Matrix (Fin m) (Fin m) K) *ᵥ w - w ∈ W := hg
    have hgv : (g : Matrix (Fin m) (Fin m) K) *ᵥ
        (((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have h1 := hg0 (((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v)
    rw [hgv] at h1
    have h2 := W.neg_mem h1
    rw [neg_sub] at h2
    exact h2

private theorem mem_elat_stab_iff {m : ℕ} {K : Type} [Field K] (W : Submodule K (Fin m → K))
    (g : GL (Fin m) K) :
    g ∈ elat_stab W ↔ ∀ v : Fin m → K, (g : Matrix (Fin m) (Fin m) K) *ᵥ v - v ∈ W :=
  Iff.rfl

private theorem elat_mulVec_mem {m : ℕ} {K : Type} [Field K] {W : Submodule K (Fin m → K)}
    {g : GL (Fin m) K} (hg : ∀ v : Fin m → K, (g : Matrix (Fin m) (Fin m) K) *ᵥ v - v ∈ W)
    {w : Fin m → K} (hw : w ∈ W) : (g : Matrix (Fin m) (Fin m) K) *ᵥ w ∈ W := by
  have e : (g : Matrix (Fin m) (Fin m) K) *ᵥ w =
      (g : Matrix (Fin m) (Fin m) K) *ᵥ w - w + w := (sub_add_cancel _ _).symm
  rw [e]
  exact W.add_mem (hg w) hw

private theorem elat_add_self_eq_zero {m : ℕ} {K : Type} [Field K] [CharP K 2]
    (y : Fin m → K) : y + y = 0 := by
  rw [← two_smul K y, CharTwo.two_eq_zero, zero_smul]

private theorem elat_dot_sum_smul {ι : Type} [Fintype ι] {m : ℕ} {K : Type} [Field K]
    (f : Fin m → K) (c : ι → K) (v : ι → Fin m → K) :
    f ⬝ᵥ (∑ i, c i • v i) = ∑ i, c i * (f ⬝ᵥ v i) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
  ring

private theorem elat_row_of_dual {m : ℕ} {K : Type} [Field K] (φ : (Fin m → K) →ₗ[K] K) :
    ∃ r : Fin m → K, ∀ x : Fin m → K, r ⬝ᵥ x = φ x := by
  refine ⟨fun j => φ (Pi.single j 1), fun x => ?_⟩
  have hx : x = ∑ j, x j • (Pi.single j (1 : K) : Fin m → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem elat_det_one_add_vecMulVec {k : ℕ} {K : Type} [Field K] (u f : Fin k → K) :
    (1 + Matrix.vecMulVec u f).det = 1 + f ⬝ᵥ u := by
  have h : Matrix.vecMulVec u f = Matrix.replicateCol Unit u * Matrix.replicateRow Unit f := by
    ext a b
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]

private theorem elat_mem_of_iSup {G : Type} [Group G] {R : Subgroup G}
    {𝓛 : Finset (Subgroup G)} (hLR : ∀ L ∈ 𝓛, L ≤ R) (T : Subgroup ↥R)
    (hT : ∀ L (hL : L ∈ 𝓛) (l : G) (hl : l ∈ L), (⟨l, hLR L hL hl⟩ : ↥R) ∈ T)
    (g : G) (hg : g ∈ ⨆ L ∈ 𝓛, L) : ∃ hgR : g ∈ R, (⟨g, hgR⟩ : ↥R) ∈ T := by
  have hle : (⨆ L ∈ 𝓛, L) ≤ T.map R.subtype := by
    refine iSup₂_le (f := fun L (_ : L ∈ 𝓛) => L) fun L hL => ?_
    intro l hl
    exact Subgroup.mem_map.mpr ⟨⟨l, hLR L hL hl⟩, hT L hL l hl, rfl⟩
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (hle hg)
  subst hxg
  exact ⟨x.2, hx⟩

private theorem elat_transvection_entry {k : ℕ} {K : Type} [Field K] (i j a t : Fin k)
    (c : K) :
    (if t = a then (1 : K) else 0) + c * (if t = j then 1 else 0) * (if i = a then 1 else 0) =
      (if a = t then (1 : K) else 0) + (if i = a ∧ j = t then c else 0) := by
  by_cases h1 : t = a
  · subst h1
    by_cases h2 : t = j
    · subst h2
      by_cases h3 : i = t
      · subst h3
        simp
      · simp [h3]
    · simp [h2, Ne.symm h2]
  · by_cases h2 : t = j
    · subst h2
      by_cases h3 : i = a
      · subst h3
        simp [h1, Ne.symm h1]
      · simp [h3, h1, Ne.symm h1]
    · simp [h1, Ne.symm h1, h2, Ne.symm h2]

theorem elat_quotSat
    {G : Type} [Group G] [Finite G] (R : Subgroup G) (𝓛 : Finset (Subgroup G))
    (hLR : ∀ L ∈ 𝓛, L ≤ R)
    {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) {m : ℕ}
    (φ : ↥R →* GL (Fin m) K) (u : Subgroup G → (Fin m → K))
    (hu0 : ∀ L ∈ 𝓛, u L ≠ 0)
    (hel : ∀ L (hL : L ∈ 𝓛), ∀ (l : G) (hl : l ∈ L), ∃ f : Fin m → K, f ⬝ᵥ u L = 0 ∧
      (φ ⟨l, hLR L hL hl⟩ : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec (u L) f)
    (hfull : ∀ L (hL : L ∈ 𝓛), ∀ f : Fin m → K, f ⬝ᵥ u L = 0 → ∃ (l : G) (hl : l ∈ L),
      (φ ⟨l, hLR L hL hl⟩ : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec (u L) f)
    (hdist : ∃ L₁ ∈ 𝓛, ∃ L₂ ∈ 𝓛, ∀ c : K, u L₂ ≠ c • u L₁)
    (hker : ∀ s : ↥R, (s : G) ∈ ⨆ L ∈ 𝓛, L →
      ((φ s : Matrix (Fin m) (Fin m) K) * (φ s : Matrix (Fin m) (Fin m) K) = 1) →
      ∃ j : ℕ, (s : G) ^ 2 ^ j = 1) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ m ∧
      QuotSat (⨆ L ∈ 𝓛, L) (inSubgroup (pCore 2) (⨆ L ∈ 𝓛, L)) (IsSLModel k (Nat.card K)) := by
  set S : Subgroup G := ⨆ L ∈ 𝓛, L with hSdef
  have hLS : ∀ L ∈ 𝓛, L ≤ S := fun L hL => le_iSup₂ (f := fun L (_ : L ∈ 𝓛) => L) L hL
  have hSR : S ≤ R := iSup₂_le (f := fun L (_ : L ∈ 𝓛) => L) hLR
  set ψ : ↥S →* GL (Fin m) K := φ.comp (Subgroup.inclusion hSR) with hψdef
  set W : Submodule K (Fin m → K) := Submodule.span K (u '' (𝓛 : Set (Subgroup G))) with hWdef
  set k : ℕ := Module.finrank K W with hkdef
  set b : Module.Basis (Fin k) K W := Module.finBasis K W with hbdef
  have huW : ∀ L ∈ 𝓛, u L ∈ W := fun L hL =>
    Submodule.subset_span (Set.mem_image_of_mem u (Finset.mem_coe.mpr hL))
  have hT : ∀ L (hL : L ∈ 𝓛) (l : G) (hl : l ∈ L),
      (⟨l, hLR L hL hl⟩ : ↥R) ∈ (elat_stab W).comap φ := by
    intro L hL l hl
    obtain ⟨f, hf, hφ⟩ := hel L hL l hl
    rw [Subgroup.mem_comap, mem_elat_stab_iff]
    intro v
    rw [hφ, mulVec_one_add_vecMulVec]
    have e : v + (f ⬝ᵥ v) • u L - v = (f ⬝ᵥ v) • u L := by abel
    rw [e]
    exact W.smul_mem _ (huW L hL)
  have hψT : ∀ s : ↥S, ψ s ∈ elat_stab W := by
    intro s
    obtain ⟨_, hmem⟩ := elat_mem_of_iSup hLR ((elat_stab W).comap φ) hT s.1 s.2
    exact Subgroup.mem_comap.mp hmem
  set ρ : ↥S →* ((Fin m → K) ≃ₗ[K] (Fin m → K)) := matToLin.toMonoidHom.comp ψ with hρdef
  have hρ : ∀ (s : ↥S) (w : Fin m → K), ρ s w = (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ w :=
    fun s w => matToLin_apply (ψ s) w
  have hWρ : ∀ (s : ↥S), ∀ w ∈ W, ρ s w ∈ W := fun s w hw => by
    rw [hρ]
    exact elat_mulVec_mem ((mem_elat_stab_iff W (ψ s)).mp (hψT s)) hw
  have hk2 : 2 ≤ k := by
    obtain ⟨L₁, hL₁, L₂, hL₂, hd⟩ := hdist
    have hli : LinearIndependent K ![u L₁, u L₂] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right (hu0 L₁ hL₁), rfl⟩
      · exfalso
        apply hd (-(t⁻¹ * s))
        have h2 : t • u L₂ = -(s • u L₁) := eq_neg_of_add_eq_zero_right hst
        calc u L₂ = t⁻¹ • (t • u L₂) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • u L₁ := by rw [h2, smul_neg, neg_smul, mul_smul]
    have hmem : ∀ i : Fin 2, ![u L₁, u L₂] i ∈ W := by
      intro i
      fin_cases i
      · exact huW L₁ hL₁
      · exact huW L₂ hL₂
    have hli' : LinearIndependent K (fun i : Fin 2 => (⟨![u L₁, u L₂] i, hmem i⟩ : W)) :=
      LinearIndependent.of_comp W.subtype hli
    simpa using hli'.fintype_card_le_finrank
  have hkm : k ≤ m := by
    simpa using Submodule.finrank_le W
  set θ : ↥S →* GL (Fin k) K := b.toGL.toMonoidHom.comp (actionOnSubspace ρ W hWρ) with hθdef
  have hθe : ∀ s : ↥S, θ s = b.toGL (actionOnSubspace ρ W hWρ s) := fun s => rfl
  have hgen : ∀ (L : Subgroup G) (hL : L ∈ 𝓛) (l : G) (hl : l ∈ L),
      ((θ ⟨l, hLS L hL hl⟩ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K).det = 1 := by
    intro L hL l hl
    obtain ⟨f, hf, hφ⟩ := hel L hL l hl
    obtain ⟨uW, huWc⟩ : ∃ x : W, (x : Fin m → K) = u L := ⟨⟨u L, huW L hL⟩, rfl⟩
    have hψl : ((ψ ⟨l, hLS L hL hl⟩ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        1 + Matrix.vecMulVec (u L) f := hφ
    have hact : ∀ t : Fin k, actionOnSubspace ρ W hWρ ⟨l, hLS L hL hl⟩ (b t) =
        b t + (f ⬝ᵥ (b t : Fin m → K)) • uW := by
      intro t
      apply Subtype.ext
      rw [actionOnSubspace_apply, hρ, hψl, mulVec_one_add_vecMulVec, Submodule.coe_add,
        Submodule.coe_smul, huWc]
    have hmat : ((θ ⟨l, hLS L hL hl⟩ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        1 + Matrix.vecMulVec (fun i => b.repr uW i) (fun t => f ⬝ᵥ (b t : Fin m → K)) := by
      rw [hθe]
      ext i t
      rw [toGL_entry, hact t, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, smul_eq_mul, Matrix.add_apply, Matrix.vecMulVec_apply,
        Matrix.one_apply, Finsupp.single_apply]
      by_cases h : i = t
      · subst h
        simp [mul_comm]
      · simp [h, Ne.symm h, mul_comm]
    have hsum : ∑ t, b.repr uW t • (b t : Fin m → K) = u L := by
      have h := congrArg Subtype.val (Module.Basis.sum_repr b uW)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      rw [huWc] at h
      exact h
    have h1 : f ⬝ᵥ (∑ t, b.repr uW t • (b t : Fin m → K)) =
        ∑ t, b.repr uW t * (f ⬝ᵥ (b t : Fin m → K)) :=
      elat_dot_sum_smul f _ _
    rw [hsum, hf] at h1
    have hdot : (fun t => f ⬝ᵥ (b t : Fin m → K)) ⬝ᵥ (fun i => b.repr uW i) = 0 := by
      show ∑ t, (f ⬝ᵥ (b t : Fin m → K)) * b.repr uW t = 0
      have h2 : ∑ t, (f ⬝ᵥ (b t : Fin m → K)) * b.repr uW t =
          ∑ t, b.repr uW t * (f ⬝ᵥ (b t : Fin m → K)) :=
        Finset.sum_congr rfl fun t _ => mul_comm _ _
      rw [h2]
      exact h1.symm
    rw [hmat, elat_det_one_add_vecMulVec, hdot, add_zero]
  have hθS : ∀ s : ↥S, θ s ∈ StatedSL k K := by
    intro s
    have hT2 : ∀ (L : Subgroup G) (hL : L ∈ 𝓛) (l : G) (hl : l ∈ L),
        (⟨l, hLS L hL hl⟩ : ↥S) ∈ (StatedSL k K).comap θ := fun L hL l hl =>
      Subgroup.mem_comap.mpr (CFSG.Open.StatedAPI.mem_statedSL_of_det (hgen L hL l hl))
    obtain ⟨_, hmem⟩ := elat_mem_of_iSup hLS ((StatedSL k K).comap θ) hT2 s.1 s.2
    exact Subgroup.mem_comap.mp hmem
  have hdet : ∀ s : ↥S, ((b.toGL (actionOnSubspace ρ W hWρ s) : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K).det = 1 := fun s =>
    CFSG.Open.StatedAPI.det_of_mem_statedSL (hθS s)
  have htrans : ∀ (i j : Fin k), i ≠ j → ∀ c : K, ∃ s : ↥S,
      ((b.toGL (actionOnSubspace ρ W hWρ s) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        Matrix.transvection i j c := by
    intro i j hij c
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (c • b.coord j)
    obtain ⟨r, hr⟩ := elat_row_of_dual g
    have hgb : ∀ t : Fin k, g (b t : Fin m → K) = c * (if t = j then 1 else 0) := by
      intro t
      have h1 := LinearMap.congr_fun hg (b t)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        smul_eq_mul] at h1
      exact h1
    have hri : r ⬝ᵥ (b i : Fin m → K) = 0 := by
      rw [hr, hgb i, if_neg hij, mul_zero]
    have hrt : ∀ t : Fin k, r ⬝ᵥ (b t : Fin m → K) = c * (if t = j then 1 else 0) := by
      intro t
      rw [hr, hgb t]
    have hU : ∀ w' ∈ u '' (𝓛 : Set (Subgroup G)), ∀ f : Fin m → K, f ⬝ᵥ w' = 0 →
        ∃ γ ∈ ψ.range, (γ : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec w' f := by
      rintro _ ⟨L, hL, rfl⟩ f hf
      obtain ⟨l, hl, hφ⟩ := hfull L (Finset.mem_coe.mp hL) f hf
      exact ⟨ψ ⟨l, hLS L (Finset.mem_coe.mp hL) hl⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩, hφ⟩
    obtain ⟨γ, hγΓ, hγ⟩ := exists_elation_of_mem_span_centres ψ.range
      (u '' (𝓛 : Set (Subgroup G))) hU (b i : Fin m → K) (b i).2 r hri
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hγΓ
    refine ⟨s, ?_⟩
    have hact : ∀ t : Fin k, actionOnSubspace ρ W hWρ s (b t) =
        b t + (r ⬝ᵥ (b t : Fin m → K)) • b i := by
      intro t
      apply Subtype.ext
      rw [actionOnSubspace_apply, hρ, hγ, mulVec_one_add_vecMulVec, Submodule.coe_add,
        Submodule.coe_smul]
    ext a t
    rw [toGL_entry, hact t, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Module.Basis.repr_self, smul_eq_mul, hrt t]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Finsupp.single_apply]
    exact elat_transvection_entry i j a t c
  have hker' : ∀ s : ↥S, b.toGL (actionOnSubspace ρ W hWρ s) = 1 → ∃ j : ℕ, s ^ 2 ^ j = 1 := by
    intro s hs
    have hF : actionOnSubspace ρ W hWρ s = 1 := b.toGL.injective (by rw [hs, map_one])
    have hfix : ∀ w ∈ W, (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ w = w := by
      intro w hw
      have h1 := actionOnSubspace_apply ρ W hWρ s ⟨w, hw⟩
      rw [hF, hρ] at h1
      exact h1.symm
    have hsq : (ψ s : Matrix (Fin m) (Fin m) K) * (ψ s : Matrix (Fin m) (Fin m) K) = 1 := by
      apply matrix_eq_of_forall_mulVec
      intro x
      rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
      have hw : (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x - x ∈ W :=
        (mem_elat_stab_iff W (ψ s)).mp (hψT s) x
      have e : (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ ((ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x) =
          (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ ((ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x - x) +
            (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x := by
        rw [← Matrix.mulVec_add, sub_add_cancel]
      rw [e, hfix _ hw]
      have h4' : ((ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x - x) +
          (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x =
          ((ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x + (ψ s : Matrix (Fin m) (Fin m) K) *ᵥ x) + -x := by
        abel
      rw [h4', elat_add_self_eq_zero, zero_add]
      exact (eq_neg_of_add_eq_zero_left (elat_add_self_eq_zero x)).symm
    obtain ⟨j, hj⟩ := hker ⟨s.1, hSR s.2⟩ s.2 hsq
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  refine ⟨k, hk2, hkm, ?_⟩
  exact quotSat_isSLModel_of_restrict S h4 W hk2 b ρ hWρ hdet htrans hker'

end CFSG.RankThree.GF2n.Stroth80
