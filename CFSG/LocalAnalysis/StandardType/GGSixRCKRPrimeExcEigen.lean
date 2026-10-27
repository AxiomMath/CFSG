module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcEigenTw

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)
open scoped Matrix

private theorem rckEig_entrywise_algebraMap {τ : Tag} {L : Type} [Field L] (σ : L →+* L) (c : L) :
    entrywise σ (algebraMap L (Module.End L (RootModule τ L)) c) =
      algebraMap L (Module.End L (RootModule τ L)) (σ c) := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp [entrywise, Module.algebraMap_end_apply, Finsupp.single_apply]

private noncomputable def rckEig_scal {τ : Tag} (c : GGLˣ) : ModGL τ GGL :=
  Units.map (algebraMap GGL (Module.End GGL (RootModule τ GGL))).toMonoidHom c

private theorem rckEig_scal_central {τ : Tag} (c : GGLˣ) (x : ModGL τ GGL) :
    x * rckEig_scal c = rckEig_scal c * x := by
  apply Units.ext
  have h := Algebra.commute_algebraMap_right (c : GGL) (x : Module.End GGL (RootModule τ GGL))
  exact h.eq

private theorem rckEig_conj_scal {τ : Tag} (c : GGLˣ) (P : ModGL τ GGL) :
    P * rckEig_scal c * P⁻¹ = rckEig_scal c := by
  rw [rckEig_scal_central c P, mul_assoc, mul_inv_cancel, mul_one]

private theorem rckEig_entrywise_scal {τ : Tag} (σ : GGL →+* GGL) (c : GGLˣ) :
    Units.map (entrywiseHom σ) (rckEig_scal c : ModGL τ GGL) =
      rckEig_scal (Units.map σ.toMonoidHom c) := by
  apply Units.ext
  exact rckEig_entrywise_algebraMap σ (c : GGL)

private theorem rckEig_scal_injective {τ : Tag} : Function.Injective (rckEig_scal (τ := τ)) := by
  intro c d h
  apply Units.ext
  have h' := congrArg (fun u : ModGL τ GGL => (u : Module.End GGL (RootModule τ GGL))) h
  exact (algebraMap GGL (Module.End GGL (RootModule τ GGL))).injective h'

private theorem rckEig_exists_unit_pow_ne_one {n : ℕ} (hn : 0 < n) : ∃ s : GGLˣ, s ^ n ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (0 : GGL) (Polynomial.nthRoots n (1 : GGL)).toFinset)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
  have h1 : c ^ n = 1 := by simpa using congrArg (fun u : GGLˣ => (u : GGL)) h
  exact Finset.mem_insert_of_mem (by simpa [Polynomial.mem_nthRoots hn] using h1)

theorem rckExc_langDatum_q_eq
    {t : StatedLieTag} {f : ℕ} (Dl : LangDatum (langTag t) GGL) (hΦ : Dl.Φ = ggPhi t f) : Dl.q = 2 ^ f := by
  obtain ⟨Fr, hFr, P, hP, hΦ_eq⟩ := Dl.steinberg
  have key : ∀ c : GGLˣ, c ^ Dl.q = c ^ 2 ^ f := by
    intro c
    have h1 : Dl.Φ (rckEig_scal c) = rckEig_scal (Units.map Fr.toMonoidHom c) := by
      rw [hΦ_eq, rckEig_entrywise_scal, rckEig_conj_scal]
    have h2 : Dl.Φ (rckEig_scal c) = rckEig_scal (Units.map (ggFrobT f).toMonoidHom c) := by
      rw [hΦ]
      cases t with
      | twistedE6 =>
        show twistHom TwistTag.E6 GGL (ggFrobT f) (rckEig_scal (τ := TwistTag.E6.tag) c) = _
        simp only [twistHom, MonoidHom.comp_apply]
        rw [rckEig_entrywise_scal]
        exact rckEig_conj_scal (τ := TwistTag.E6.tag) _ _
      | _ =>
        exact rckEig_entrywise_scal (ggFrobT f) c
    have h3 := rckEig_scal_injective (h1.symm.trans h2)
    have h4 : ((c : GGL)) ^ Dl.q = (c : GGL) ^ 2 ^ f := by
      have := congrArg (fun u : GGLˣ => (u : GGL)) h3
      simpa [hFr, ggFrobT_apply] using this
    exact Units.ext (by simpa using h4)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨c, hc⟩ := rckEig_exists_unit_pow_ne_one (n := 2 ^ f - Dl.q) (by omega)
    apply hc
    have h' : c ^ Dl.q * c ^ (2 ^ f - Dl.q) = c ^ Dl.q * 1 := by
      rw [← pow_add, show Dl.q + (2 ^ f - Dl.q) = 2 ^ f by omega, ← key c, mul_one]
    exact mul_left_cancel h'
  · obtain ⟨c, hc⟩ := rckEig_exists_unit_pow_ne_one (n := Dl.q - 2 ^ f) (by omega)
    apply hc
    have h' : c ^ 2 ^ f * c ^ (Dl.q - 2 ^ f) = c ^ 2 ^ f * 1 := by
      rw [← pow_add, show 2 ^ f + (Dl.q - 2 ^ f) = Dl.q by omega, key c, mul_one]
    exact mul_left_cancel h'

private theorem rckEig_step_pinnedX
    {t : StatedLieTag} (ht : t ≠ .twistedE6) {f : ℕ} (Dl : LangDatum (langTag t) GGL)
    (w : WeylGroup (langTag t)) (hn : Dl.n = canonicalRep (coxeterSystem (langTag t)) GGL w)
    (hΦ : Dl.Φ = ggPhi t f) {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) :
    ∃ ε : GGL, ε * ε = 1 ∧ ∀ c : GGL,
      Dl.step (pinnedX (langTag t) GGL γ c) =
        pinnedX (langTag t) GGL (w • γ) (ε * c ^ 2 ^ f) := by
  have hΦ' : Dl.Φ = Units.map (entrywiseHom (ggFrobT f)) := by
    rw [hΦ]
    cases t with
    | twistedE6 => exact absurd rfl ht
    | _ => rfl
  obtain ⟨ε, hε, h2⟩ := exists_canonicalRep_mul_pinnedX_mul_inv GGL w hγ
  refine ⟨ε, hε, fun c => ?_⟩
  rw [show Dl.step (pinnedX (langTag t) GGL γ c) =
      Dl.n * Dl.Φ (pinnedX (langTag t) GGL γ c) * Dl.n⁻¹ by
    simp [LangDatum.step, MulAut.conj_apply]]
  rw [hΦ', hn]
  show canonicalRep (coxeterSystem (langTag t)) GGL w *
      (Units.map (entrywiseHom (ggFrobT f))) (pinnedX (langTag t) GGL γ c) *
      (canonicalRep (coxeterSystem (langTag t)) GGL w)⁻¹ = _
  rw [CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, h2, ggFrobT_apply]

theorem rckExc_torus_eigen_untwisted
    {t : StatedLieTag} (ht : t ≠ .twistedE6) {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Dl : LangDatum (langTag t) GGL) (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ))
    (hΦ : Dl.Φ = ggPhi t f) (hρ : FrobRootMap Dl ρ)
    (A' : Subgroup (ModGL (langTag t) GGL)) (hA'el : IsElemAbelian p A')
    (hA' : ∀ x ∈ A', Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) :
    ∃ w : WeylGroup (langTag t), (∀ γ, IsRoot (langTag t) γ → ρ γ = w • γ) ∧
      Nat.card A' ≤ Nat.card {z : Fin (langTag t).rank → ZMod p //
        (modMat p (weylMatrix w))ᵀ *ᵥ z = ((2 ^ f : ℕ) : ZMod p) • z} := by
  obtain ⟨w, hn⟩ := Dl.n_weyl
  have hρw : ∀ γ, IsRoot (langTag t) γ → ρ γ = w • γ := by
    intro γ hγ
    obtain ⟨ε, hε, hstep⟩ := rckEig_step_pinnedX ht (f := f) Dl w hn hΦ hγ
    have hε0 : ε ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hε
      exact zero_ne_one hε
    have hsurj : Function.Surjective (fun c : GGL => ε * c ^ 2 ^ f) := by
      intro y
      obtain ⟨x, hx⟩ :=
        IsAlgClosed.exists_pow_nat_eq (y / ε) (pow_pos (by norm_num : (0 : ℕ) < 2) f)
      exact ⟨x, by show ε * x ^ 2 ^ f = y; rw [hx]; field_simp⟩
    have hmap : (rootSubgroup (langTag t) GGL γ).map Dl.step =
        rootSubgroup (langTag t) GGL (w • γ) :=
      map_rootSubgroup_eq_of_forall (f := Dl.step) (g := fun c : GGL => ε * c ^ 2 ^ f) hsurj hstep
    have hmapρ : (rootSubgroup (langTag t) GGL γ).map Dl.step =
        rootSubgroup (langTag t) GGL (ρ γ) := hρ.map_rootSubgroup γ hγ
    have hsub : rootSubgroup (langTag t) GGL (ρ γ) = rootSubgroup (langTag t) GGL (w • γ) := by
      rw [← hmapρ, hmap]
    exact CFSG.StandardType.LieCore.rootSubgroup_injective_of_isRoot
      ((hρ.isRoot_iff γ).2 hγ) (IsRoot.smul hγ w) hsub
  refine ⟨w, hρw, ?_⟩
  have hcard := rckExc_torus_eigen_of_rho hp hp2 Dl ρ hρ (weylMatrix w)
    (fun i => by rw [hρw _ (isRoot_single _ i), weylMatrix_mulVec]) A' hA'el hA'
  rw [rckExc_langDatum_q_eq Dl hΦ] at hcard
  simpa using hcard

end CFSG.StandardType.RCKRP
