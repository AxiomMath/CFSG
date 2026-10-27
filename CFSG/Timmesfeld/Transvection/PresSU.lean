module

public import CFSG.Timmesfeld.Transvection.PresSUSL2
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

section Cone

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσ : ∀ c, σ (σ c) = c) {G : Type*} [Group G] (R : SURelations (m / 2) σ G) (he : Even m)

theorem SURelations.coneCompatible (hm : 4 ≤ m) (htr : ∀ c, σ c = c → ∃ s, s + σ s = c) :
    ConeCompatible (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m))
      (Unitary.rootGroup σ hσ m) (fun γ x => suPsi hσ R he γ x) := by
  refine coneCompatible_of_halfSpace (fun f => extendsToHom_halfSpace_su hσ R he f) fun i => ?_
  by_cases hk : i.val + 1 < m / 2
  · exact R.extendsToHom_short hσ he hk
  · exact R.extendsToHom_long hσ he hk hm htr

omit [Finite F] in
theorem SURelations.eq_suPsi_of {Ψ : SU σ m →* G}
    (h₁ : ∀ a b, idx a ≠ idx b → ∀ c, Ψ (suElt σ hσ a b c) = R.ξ a b c)
    (h₂ : ∀ a c, σ c = c → Ψ (suLong σ a c) = R.ξL a c) {γ : Fin (m / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan m) (divisible m)) (x : Unitary.rootGroup σ hσ m γ) :
    Ψ x = suPsi hσ R he γ x := by
  obtain ⟨a, b, c, hv, hγe, hx⟩ := exists_eval_eq hσ he hγ x
  have hx' : x = ⟨_, eval_mem_rootGroup hσ hv hγe⟩ := Subtype.ext hx.symm
  rw [hx', suPsi_eval hσ R he hv hγe]
  by_cases hba : b = a
  · subst hba
    simp only [SURelations.eval_long, suRelationsModel_ξL]
    exact h₂ b c (hv.2 rfl)
  · simp only [SURelations.eval_short _ hba, suRelationsModel_ξ]
    exact h₁ a b (idx_ne_of_ne hba hv.1) c

end Cone

@[expose] def SURelations.Generates {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*}
    [Group G] (R : SURelations r σ G) : Prop :=
  Subgroup.closure {g | (∃ a b, idx a ≠ idx b ∧ ∃ c, R.ξ a b c = g) ∨
    ∃ a c, σ c = c ∧ R.ξL a c = g} = ⊤

theorem unitaryLongRoot_eq {m : ℕ} (he : Even m) (hm : 2 ≤ m) :
    unitaryLongRoot m hm = Pi.single (⟨m / 2 - 1, by omega⟩ : Fin (m / 2)) 1 := by
  rw [unitaryLongRoot, ite_eq_left (Nat.even_iff.1 he), one_smul]

namespace SURelations

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {m : ℕ} (he : Even m) (hm : 4 ≤ m) {G : Type*} [Group G]
  (R : SURelations (m / 2) (unitaryInvolution F 2 f) G)

include hF hm in
theorem existsUnique_hom_suPsi :
    ∃! Ψ : SU (unitaryInvolution F 2 f) m →* G,
      ∀ γ ∈ roots (isFiniteType_cartan m) (divisible m),
        ∀ x : Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) m γ,
          Ψ x = suPsi (unitaryInvolution_involutive hF) R he γ x := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  exact existsUnique_hom_of_coneCompatible
    (presentationA_of (isCTGroupDatum hF m (by omega) ζ hζ)
      (steinbergExtras hF m (by omega) ζ hζ))
    (R.coneCompatible (unitaryInvolution_involutive hF) he hm
      fun _ hx => exists_add_unitaryInvolution_eq hF hx)

@[expose] noncomputable def toHom : SU (unitaryInvolution F 2 f) m →* G :=
  (R.existsUnique_hom_suPsi hF he hm).exists.choose

theorem toHom_eq_suPsi {γ : Fin (m / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan m) (divisible m))
    (x : Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) m γ) :
    R.toHom hF he hm x = suPsi (unitaryInvolution_involutive hF) R he γ x :=
  (R.existsUnique_hom_suPsi hF he hm).exists.choose_spec γ hγ x

theorem toHom_suElt {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) (c : F) :
    R.toHom hF he hm (suElt _ (unitaryInvolution_involutive hF) a b c) = R.ξ a b c := by
  obtain ⟨γ, hγ, hγe⟩ := exists_root_of_rt he (ne_swap_of_idx_ne hab)
  have hv := relValid_short (σ := unitaryInvolution F 2 f) hab c
  have h := R.toHom_eq_suPsi hF he hm hγ ⟨_, eval_mem_rootGroup _ hv hγe⟩
  rw [suPsi_eval _ R he hv hγe, R.eval_short (ne_of_idx_ne hab)] at h
  dsimp only at h
  rwa [SURelations.eval_short _ (ne_of_idx_ne hab), suRelationsModel_ξ] at h

theorem toHom_suLong (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F}
    (hc : unitaryInvolution F 2 f c = c) :
    R.toHom hF he hm (suLong (unitaryInvolution F 2 f) a c) = R.ξL a c := by
  obtain ⟨γ, hγ, hγe⟩ := exists_root_of_rt he (swap_ne_self a).symm
  have hv := relValid_long (σ := unitaryInvolution F 2 f) a hc
  have h := R.toHom_eq_suPsi hF he hm hγ ⟨_, eval_mem_rootGroup _ hv hγe⟩
  rw [suPsi_eval _ R he hv hγe, R.eval_long] at h
  dsimp only at h
  rwa [SURelations.eval_long, suRelationsModel_ξL] at h

include hF he hm in
theorem existsUnique_hom :
    ∃! Ψ : SU (unitaryInvolution F 2 f) m →* G,
      (∀ a b, idx a ≠ idx b → ∀ c, Ψ (suElt _ (unitaryInvolution_involutive hF) a b c) =
        R.ξ a b c) ∧
      ∀ a c, unitaryInvolution F 2 f c = c → Ψ (suLong _ a c) = R.ξL a c := by
  refine ⟨R.toHom hF he hm, ⟨fun a b hab c => R.toHom_suElt hF he hm hab c,
    fun a c hc => R.toHom_suLong hF he hm a hc⟩, fun Ψ hΨ => ?_⟩
  exact (R.existsUnique_hom_suPsi hF he hm).unique
    (fun γ hγ x => R.eq_suPsi_of _ he hΨ.1 hΨ.2 hγ x)
    (R.existsUnique_hom_suPsi hF he hm).exists.choose_spec

theorem toHom_surjective (hgen : R.Generates) : Function.Surjective (R.toHom hF he hm) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ (⟨a, b, hab, c, rfl⟩ | ⟨a, c, hc, rfl⟩)
  · exact ⟨_, R.toHom_suElt hF he hm hab c⟩
  · exact ⟨_, R.toHom_suLong hF he hm a hc⟩

theorem ker_toHom_le_center [Nontrivial G] (hgen : R.Generates) :
    (R.toHom hF he hm).ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) := by
  have hsurj := R.toHom_surjective hF he hm hgen
  have hK : IsQuasisimple (SU (unitaryInvolution F 2 f) m) :=
    isQuasisimple_SU hF (by omega) fun h => by
      simp only [Prod.mk.injEq] at h
      omega
  have hnt : ∃ k, R.toHom hF he hm k ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨k, rfl⟩ := hsurj g
    exact ⟨k, hg⟩
  exact CurtisTits.ker_le_center_of_isQuasisimple hK hnt

theorem ker_toHom_eq_center [Nontrivial G] (hgen : R.Generates)
    (hZ : Subgroup.center G = ⊥) :
    (R.toHom hF he hm).ker = Subgroup.center (SU (unitaryInvolution F 2 f) m) := by
  refine le_antisymm (R.ker_toHom_le_center hF he hm hgen) fun z hz => ?_
  have hsurj := R.toHom_surjective hF he hm hgen
  have hc : R.toHom hF he hm z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => by
    obtain ⟨k, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

include hF he hm in
theorem nonempty_mulEquiv [Nontrivial G] (hgen : R.Generates) (hZ : Subgroup.center G = ⊥) :
    Nonempty (SU (unitaryInvolution F 2 f) m ⧸ Subgroup.center (SU (unitaryInvolution F 2 f) m)
      ≃* G) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (R.ker_toHom_eq_center hF he hm hgen hZ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (R.toHom_surjective hF he hm hgen))⟩

theorem mem_map_rootGroup_unitaryLongRoot (g : G) :
    g ∈ ((Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m (by omega))).map
        (R.toHom hF he hm) ↔
      ∃ c, unitaryInvolution F 2 f c = c ∧
        R.ξL (Sum.inl (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) c = g := by
  have hk : ¬(⟨m / 2 - 1, by omega⟩ : Fin (m / 2)).val + 1 < m / 2 := by
    simp only
    omega
  have hαe := toStd_single_last_even (m := m) hk he
  rw [unitaryLongRoot_eq he (by omega), Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc0, rfl⟩ := (mem_rootGroup_iff_suLong (unitaryInvolution_involutive hF) he _
      hαe x).1 hx
    exact ⟨c, add_map_eq_zero_iff.1 hc0,
      (R.toHom_suLong hF he hm _ (add_map_eq_zero_iff.1 hc0)).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, suLong_mem (unitaryInvolution_involutive hF) _ hαe c,
      R.toHom_suLong hF he hm _ hc⟩

end SURelations

end CFSG.Timmesfeld.Transvection
