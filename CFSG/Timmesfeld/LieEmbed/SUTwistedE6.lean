module

public import CFSG.Timmesfeld.LieEmbed.SLE6
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Steinberg.TwistedE6.Local

public noncomputable section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.BorelTits
open Minuscule

section SU

variable {F : Type*} [Field F] (σ : F ≃+* F) (n : ℕ)

@[expose] def suToSL : SU σ n →* Matrix.SpecialLinearGroup (Fin n) F where
  toFun g := ⟨((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), g.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {σ n}

theorem suToSL_rootHom (hσ : ∀ c, σ (σ c) = c) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : Multiplicative F) :
    suToSL σ n (rootHom σ hσ hij hi hj c) =
      Matrix.SpecialLinearGroup.transvection hij c.toAdd *
        Matrix.SpecialLinearGroup.transvection
          (fun h => hij (Fin.rev_injective h).symm : Fin.rev j ≠ Fin.rev i) (-σ c.toAdd) := by
  apply Subtype.ext
  change rootMatrix σ i j c.toAdd = _
  rw [rootMatrix_eq_mul σ hj, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rfl

theorem suToSL_longRootHom {i : Fin n} (hi : i ≠ Fin.rev i) (c : Multiplicative (traceZero σ)) :
    suToSL σ n (longRootHom σ hi c) =
      Matrix.SpecialLinearGroup.transvection hi (c.toAdd : F) := by
  apply Subtype.ext
  change longRootMatrix i (c.toAdd : F) = _
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  rfl

end SU

section Twisted

variable {k : Type} [Field k] [Finite k] [CharP k 2] {f : ℕ}
  (hk : Nat.card k = (2 ^ f) ^ 2) {θ : k →+* k} (hθσ : ∀ c, θ c = unitaryInvolution k 2 f c)
  {φ : Matrix.SpecialLinearGroup (Fin 6) k →* e6Data_valid.minGroup k}
  (hφ : ∀ (i j : Fin 6) (hij : i ≠ j) (c : k),
    φ (Matrix.SpecialLinearGroup.transvection hij c) = e6Data_valid.xm k (a5Root i j) c)

include hθσ hk in
theorem frob_involutive : ∀ c, θ (θ c) = c := fun c => by
  rw [hθσ, hθσ, unitaryInvolution_involutive hk]

omit [Finite k] in
theorem twistSign_cast (α : Fin (Tag.rank .E6) → ℤ) : ((twistSign α : ℤ) : k) = 1 := by
  rcases twistSign_eq_one_or α with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

include hθσ hφ in
theorem phi_rootHom {i j : Fin 6} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
    (hji : j ≠ Fin.rev i) (c : Multiplicative k) :
    φ (suToSL (unitaryInvolution k 2 f) 6
        (rootHom (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk) hij hi hj c)) =
      (xPair θ (frob_involutive hk hθσ) (isRoot_a5Root hij) (rho_a5Root_ne hij hji)
        c.toAdd : e6Data_valid.minGroup k) := by
  rw [suToSL_rootHom, map_mul, hφ, hφ, xPair_val, rho_a5Root, twistSign_cast, one_mul, hθσ,
    CharTwo.neg_eq]

include hθσ hφ in
theorem phi_longRootHom {i : Fin 6} (hi : i ≠ Fin.rev i)
    (c : Multiplicative (traceZero (unitaryInvolution k 2 f))) :
    φ (suToSL (unitaryInvolution k 2 f) 6 (longRootHom (unitaryInvolution k 2 f) hi c)) =
      (xFixed θ (isRoot_a5Root hi) (rho_a5Root_rev i) (c.toAdd : k) (by
        have h := (mem_traceZero (unitaryInvolution k 2 f)).1 c.toAdd.2
        rw [hθσ]
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
        exact h.symm) : e6Data_valid.minGroup k) := by
  rw [suToSL_longRootHom, hφ, xFixed_val]

theorem rev_ne_self_six (k' : Fin 6) : Fin.rev k' ≠ k' := by
  revert k'
  decide

include hθσ hφ in
theorem map_rootGroup_le_fixedGroup (γ : Fin (6 / 2) → ℤ) :
    ((Unitary.rootGroup (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk) 6 γ).map
      (φ.comp (suToSL (unitaryInvolution k 2 f) 6))) ≤ fixedGroup k θ := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, phi_rootHom hk hθσ hφ hij hi hj hji]
    exact (xPair _ _ _ _ _).2
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun _ => ?_
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, phi_longRootHom hθσ hφ hi]
    exact (xFixed _ _ _ _ _).2
  · exact iSup_le fun i => iSup_le fun k' => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hk' => absurd hk' (rev_ne_self_six k')

theorem c3Roots_index_check : ∀ γ ∈ c3Roots,
    (∃ i j : Fin 6, i ≠ j ∧ j ≠ Fin.rev i ∧ weight 6 i - weight 6 j = Unitary.toStd 6 γ) ∨
      ∃ i : Fin 6, 2 • weight 6 i = Unitary.toStd 6 γ := by
  decide +kernel

include hθσ hφ in
theorem map_rootGroup_eq {γ : Fin 3 → ℤ} (hγ : γ ∈ c3Roots) :
    (Unitary.rootGroup (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk) 6 γ).map
        (φ.comp (suToSL (unitaryInvolution k 2 f) 6)) =
      (twistedRootGroup k θ (c3ToF4 γ)).map (fixedGroup k θ).subtype := by
  have hθ := frob_involutive hk hθσ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
        iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_comap, MonoidHom.comp_apply, phi_rootHom hk hθσ hφ hij hi hj hji]
      have h := xPair_mem θ hθ (isRoot_a5Root hij) (rho_a5Root_ne hij hji) c.toAdd
      rw [proj_a5Root hij hji hw.symm] at h
      exact Subgroup.mem_map_of_mem (fixedGroup k θ).subtype h
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_comap, MonoidHom.comp_apply, phi_longRootHom hθσ hφ hi]
      have h := xFixed_mem θ (isRoot_a5Root hi) (rho_a5Root_rev i) (c.toAdd : k) (by
        have h := (mem_traceZero (unitaryInvolution k 2 f)).1 c.toAdd.2
        rw [hθσ]
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
        exact h.symm)
      rw [proj_a5Root_rev i hw.symm] at h
      exact Subgroup.mem_map_of_mem (fixedGroup k θ).subtype h
    · exact iSup_le fun i => iSup_le fun k' => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun hk' => absurd hk' (rev_ne_self_six k')
  · rintro _ ⟨g, hg, rfl⟩
    rcases c3Roots_index_check γ hγ with ⟨i, j, hij, hji, hw⟩ | ⟨i, hw⟩
    · have hi := (rev_ne_self_six i).symm
      have hj := (rev_ne_self_six j).symm
      obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_a5Root hij)
        (proj_a5Root hij hji hw.symm) (rho_a5Root_ne hij hji) g).1 hg
      refine ⟨rootHom (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk) hij hi hj
        (Multiplicative.ofAdd c), ?_, ?_⟩
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem i
          (Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hij (Subgroup.mem_iSup_of_mem hi
            (Subgroup.mem_iSup_of_mem hj (Subgroup.mem_iSup_of_mem hji
              (Subgroup.mem_iSup_of_mem hw (⟨_, rfl⟩)))))))))
      · rw [MonoidHom.comp_apply, phi_rootHom hk hθσ hφ hij hi hj hji, xPair_val, toAdd_ofAdd,
          Subgroup.coe_subtype, hc]
    · have hi := (rev_ne_self_six i).symm
      obtain ⟨c, hcθ, hc⟩ := (mem_twistedRootGroup_iff_of_fixed θ (isRoot_a5Root hi)
        (proj_a5Root_rev i hw.symm) (rho_a5Root_rev i) g).1 hg
      have htz : c ∈ traceZero (unitaryInvolution k 2 f) := by
        rw [mem_traceZero, ← hθσ, hcθ, CharTwo.add_self_eq_zero]
      refine ⟨longRootHom (unitaryInvolution k 2 f) hi (Multiplicative.ofAdd ⟨c, htz⟩), ?_, ?_⟩
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i
          (Subgroup.mem_iSup_of_mem hi (Subgroup.mem_iSup_of_mem hw
            (⟨_, rfl⟩)))))
      · rw [MonoidHom.comp_apply, phi_longRootHom hθσ hφ hi, xFixed_val, toAdd_ofAdd,
          Subgroup.coe_subtype, hc]

end Twisted

variable {k : Type} [Field k] [Finite k] [CharP k 2] {f : ℕ}
  (hk : Nat.card k = (2 ^ f) ^ 2) {θ : k →+* k} (hθσ : ∀ c, θ c = unitaryInvolution k 2 f c)

include hk hθσ in
theorem exists_suToTwistedE6 : ∃ ι : SU (unitaryInvolution k 2 f) 6 →* fixedGroup k θ,
    ι.ker ≤ Subgroup.center _ ∧ ∀ γ ∈ c3Roots,
      ((twistedRootGroup k θ (c3ToF4 γ) : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) =
        ι '' (Unitary.rootGroup (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk) 6 γ :
          Set (SU (unitaryInvolution k 2 f) 6)) := by
  obtain ⟨φ, hφ⟩ := exists_slToE6 (k := k)
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hk
  have htop := (isCTGroupDatum hk 6 (by norm_num) ζ hζ).iSup_eq_top
  have hfix : ∀ x, (φ.comp (suToSL (unitaryInvolution k 2 f) 6)) x ∈ fixedGroup k θ := by
    intro x
    have hle : (⨆ γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartan 6) (divisible 6),
        Unitary.rootGroup (unitaryInvolution k 2 f) (unitaryInvolution_involutive hk) 6 γ) ≤
          (fixedGroup k θ).comap (φ.comp (suToSL (unitaryInvolution k 2 f) 6)) :=
      iSup₂_le fun γ _ => (Subgroup.map_le_iff_le_comap).1
        (map_rootGroup_le_fixedGroup hk hθσ hφ γ)
    rw [htop] at hle
    exact hle (Subgroup.mem_top x)
  set ι := (φ.comp (suToSL (unitaryInvolution k 2 f) 6)).codRestrict (fixedGroup k θ) hfix with hι
  have hsub : (fixedGroup k θ).subtype.comp ι = φ.comp (suToSL (unitaryInvolution k 2 f) 6) :=
    MonoidHom.ext fun _ => rfl
  refine ⟨ι, ?_, fun γ hγ => ?_⟩
  · have h0 : (0 : Fin 6) ≠ Fin.rev 0 := by decide
    have h1 : (1 : k) ∈ traceZero (unitaryInvolution k 2 f) := by
      rw [mem_traceZero, map_one, CharTwo.add_self_eq_zero]
    have hnt : ∃ x, ι x ≠ 1 := by
      refine ⟨longRootHom (unitaryInvolution k 2 f) h0 (Multiplicative.ofAdd ⟨1, h1⟩), ?_⟩
      intro h
      have h' := congrArg (fixedGroup k θ).subtype h
      rw [← MonoidHom.comp_apply, hsub, map_one, MonoidHom.comp_apply,
        phi_longRootHom hθσ hφ h0, xFixed_val, toAdd_ofAdd,
        ← e6Data_valid.xm_zero k (a5Root 0 (Fin.rev 0))] at h'
      exact one_ne_zero (e6Data_valid.xm_injective k (isRoot_a5Root h0) h')
    have hq := isQuasisimple_SU hk (n := 6) (by norm_num) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
    exact CurtisTits.ker_le_center_of_isQuasisimple hq hnt
  · have h := map_rootGroup_eq hk hθσ hφ hγ
    rw [← hsub, ← Subgroup.map_map] at h
    rw [← Subgroup.coe_map, Subgroup.map_injective (fixedGroup k θ).subtype_injective h]

end CFSG.Timmesfeld.LieEmbed
