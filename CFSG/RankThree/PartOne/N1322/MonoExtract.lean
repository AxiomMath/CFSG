module

public import CFSG.RankThree.PartOne.N1322.MonoMain
public import CFSG.RankThree.SubgroupLists.CliffordPrime

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv CFSG.RankThree.SubgroupLists

variable {K : Type*} [Field K]

theorem exists_frame {X : Subgroup (GL (Fin 3) K)} (h : IsTransitiveMonomial X) :
    ∃ P : GL (Fin 3) K, MonoStd (X.map (cj P).toMonoidHom) := by
  classical
  obtain ⟨L, hint, hdim, hperm, htrans⟩ := h
  have hne : ∀ i, L i ≠ ⊥ := fun i hbot => by
    have := hdim i
    rw [hbot] at this
    simp at this
  have hinj : Function.Injective L := hint.submodule_iSupIndep.injective hne
  have hex : ∀ i, ∃ v : Fin 3 → K, v ∈ L i ∧ v ≠ 0 ∧ ∀ w ∈ L i, ∃ c : K, c • v = w := by
    intro i
    obtain ⟨v0, hv0ne, hv0⟩ := (finrank_eq_one_iff' (K := K) (V := L i)).mp (hdim i)
    refine ⟨v0, v0.2, fun h0 => hv0ne (Subtype.ext h0), fun w hw => ?_⟩
    obtain ⟨c, hc⟩ := hv0 ⟨w, hw⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose f hfL hf0 hfspan using hex
  have hli : LinearIndependent K f := hint.submodule_iSupIndep.linearIndependent L hfL hf0
  let P0 : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => f j i
  have hP0 : IsUnit P0 := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  let P : GL (Fin 3) K := hP0.unit
  have hPval : (P : Matrix (Fin 3) (Fin 3) K) = P0 := rfl
  have hPe : ∀ j, (P : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1 = f j := by
    intro j
    rw [hPval, Matrix.mulVec_single_one]
    rfl
  have hPinv : ∀ j, ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f j = Pi.single j 1 := by
    intro j
    rw [← hPe j, mulVec_inv_mulVec]
  choose! σf hσf using hperm
  have hmat : ∀ x ∈ X, ∃ (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ),
      P⁻¹ * x * P = mono σ a ∧ ∀ i, σ i = σf x i := by
    intro x hx
    have hxf : ∀ i, ∃ a : Kˣ, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ f i = (a : K) • f (σf x i) := by
      intro i
      have hmem : (x : Matrix (Fin 3) (Fin 3) K) *ᵥ f i ∈ L (σf x i) := by
        rw [← hσf x hx i, mem_translate]
        exact ⟨f i, hfL i, rfl⟩
      obtain ⟨c, hc⟩ := hfspan (σf x i) _ hmem
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        apply hf0 i
        have := congrArg (fun w => ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) hc.symm
        simpa [mulVec_inv_mulVec] using this
      exact ⟨Units.mk0 c hc0, by rw [Units.val_mk0]; exact hc.symm⟩
    choose a ha using hxf
    have hcol : ∀ j, ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1 =
        Pi.single (σf x j) (a j : K) := by
      intro j
      rw [mulVec_conj_symm, hPe, ha, Matrix.mulVec_smul, hPinv, single_eq_smul (σf x j) (a j : K)]
    have hσinj : Function.Injective (σf x) := by
      intro i j hij
      by_contra hne'
      have h1 := hcol i
      have h2 := hcol j
      rw [hij] at h1
      have h3 : ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((a j : K) • Pi.single i 1 - (a i : K) • Pi.single j 1) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2,
          single_eq_smul _ (a i : K), single_eq_smul _ (a j : K)]
        simp [smul_smul, mul_comm]
      have h4 : (a j : K) • (Pi.single i 1 : Fin 3 → K) - (a i : K) • Pi.single j 1 = 0 := by
        have := mulVec_inv_mulVec (P⁻¹ * x * P) ((a j : K) • Pi.single i 1 - (a i : K) • Pi.single j 1)
        rw [h3, Matrix.mulVec_zero] at this
        exact this.symm
      have h5 := congrFun h4 i
      simp [hne'] at h5
    have hσbij : Function.Bijective (σf x) := Finite.injective_iff_bijective.mp hσinj
    refine ⟨Equiv.ofBijective _ hσbij, a, ?_, fun i => rfl⟩
    apply Units.ext
    ext i j
    have := congrFun (hcol j) i
    rw [Matrix.mulVec_single_one] at this
    rw [mono_val, monoMat_apply]
    simpa [Pi.single_apply, Equiv.ofBijective_apply, eq_comm] using this
  refine ⟨P⁻¹, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨σ, a, hxa, -⟩ := hmat x hx
    refine ⟨σ, a, ?_⟩
    show P⁻¹ * x * P⁻¹⁻¹ = mono σ a
    rw [inv_inv]
    exact hxa
  · intro i j
    obtain ⟨g, hg, hgij⟩ := htrans i j
    obtain ⟨σ, a, hga, hσ⟩ := hmat g hg
    refine ⟨cj P⁻¹ g, Subgroup.mem_map_of_mem _ hg, σ, a, ?_, ?_⟩
    · show P⁻¹ * g * P⁻¹⁻¹ = mono σ a
      rw [inv_inv]
      exact hga
    · rw [hσ]
      exact hinj ((hσf g hg i).symm.trans hgij)

theorem core_of_monomial (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d)
    (hmono : IsTransitiveMonomial d.X) :
    d.n = 4 ∧ Nonempty (d.X ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  obtain ⟨P, hP⟩ := exists_frame hmono
  obtain ⟨hn, e⟩ := mono_main h2 (h.conj P) hP
  obtain ⟨e⟩ := e
  exact ⟨hn, ⟨((cj P).subgroupMap d.X).trans e⟩⟩

end CFSG.RankThree.PartOne.N1322
