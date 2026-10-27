module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresProd

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
  {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

variable (D d) in
@[expose] def coordHom (b : Fin r) : (PiMat D d)ˣ →* GL (Fin (d b)) (D b) :=
  Units.map (Pi.evalMonoidHom (fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)) b)

theorem coe_coordHom (b : Fin r) (u : (PiMat D d)ˣ) :
    ((coordHom D d b u : GL (Fin (d b)) (D b)) : Matrix (Fin (d b)) (Fin (d b)) (D b)) =
      (u : PiMat D d) b :=
  rfl

theorem tau_apply_mul_eq_one (hτ : IsInvol τ) {u : (PiMat D d)ˣ} (hu : u ∈ unitaryOf hτ)
    (k : Fin r) : τ (u : PiMat D d) k * (u : PiMat D d) k = 1 := by
  have h := congrFun (mem_unitaryOf.mp hu) k
  simpa using h

theorem inv_apply_mul_apply (u : (PiMat D d)ˣ) (k : Fin r) :
    ((u⁻¹ : (PiMat D d)ˣ) : PiMat D d) k * (u : PiMat D d) k = 1 := by
  have h := congrFun (Units.inv_mul u) k
  simpa using h

theorem apply_mul_inv_apply (u : (PiMat D d)ˣ) (k : Fin r) :
    (u : PiMat D d) k * ((u⁻¹ : (PiMat D d)ˣ) : PiMat D d) k = 1 := by
  have h := congrFun (Units.mul_inv u) k
  simpa using h

theorem single_tau_single (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (i : Fin r) (m : Matrix (Fin (d i)) (Fin (d i)) (D i)) :
    (Pi.single (π i) (τ (Pi.single i m) (π i)) : PiMat D d) = τ (Pi.single i m) := by
  funext k
  by_cases hk : k = π i
  · subst hk
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk, tau_single_apply_of_ne hτ hπ i m hk]

theorem tau_piE_apply [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {j k : Fin r} (hjk : π k = j) :
    τ (piE D d j) k = 1 := by
  rw [hπ, ← hjk, perm_perm hτ hπ, piE, Pi.single_eq_same]

theorem eq_one_of_forall_le [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {u : (PiMat D d)ˣ} (hu : u ∈ unitaryOf hτ)
    (h : ∀ b, b ≤ π b → (u : PiMat D d) b = 1) : u = 1 := by
  apply Units.ext
  funext i
  rw [Units.val_one, Pi.one_apply]
  by_cases hi : i ≤ π i
  · exact h i hi
  · have hπi : π i ≤ π (π i) := by
      rw [perm_perm hτ hπ]
      exact le_of_lt (lt_of_not_ge hi)
    have h2 := tau_apply_mul_eq_one hτ hu i
    rw [apply_tau_eq hτ hπ _ rfl, h (π i) hπi,
      show (Pi.single (π i) (1 : Matrix (Fin (d (π i))) (Fin (d (π i))) (D (π i))) :
        PiMat D d) = piE D d (π i) from rfl, tau_piE_apply hτ hπ rfl, Matrix.one_mul] at h2
    exact h2

theorem coordHom_mem_matUnitary [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {b : Fin r} (hb : π b = b) {u : (PiMat D d)ˣ}
    (hu : u ∈ unitaryOf hτ) : coordHom D d b u ∈ matUnitary (isInvol_tauFix hτ hπ hb) := by
  rw [mem_matUnitary, coe_coordHom, ← apply_tau_eq_tauFix hτ hπ hb]
  exact tau_apply_mul_eq_one hτ hu b


variable (π) in
@[expose] def orbitGroup (hτ : IsInvol τ) (b : Fin r) : Subgroup (PiMat D d)ˣ where
  carrier := {u | u ∈ unitaryOf hτ ∧ ∀ k, k ≠ b → k ≠ π b → (u : PiMat D d) k = 1}
  one_mem' := ⟨Subgroup.one_mem _, fun _ _ _ => rfl⟩
  mul_mem' {u v} hu hv := ⟨Subgroup.mul_mem _ hu.1 hv.1, fun k hk hk' => by
    rw [Units.val_mul, Pi.mul_apply, hu.2 k hk hk', hv.2 k hk hk', Matrix.mul_one]⟩
  inv_mem' {u} hu := ⟨Subgroup.inv_mem _ hu.1, fun k hk hk' => by
    have h := inv_apply_mul_apply u k
    rwa [hu.2 k hk hk', Matrix.mul_one] at h⟩

theorem orbitGroup_le (hτ : IsInvol τ) (b : Fin r) : orbitGroup π hτ b ≤ unitaryOf hτ :=
  fun _ hu => hu.1

theorem conj_mem_orbitGroup (hτ : IsInvol τ) {b : Fin r} {u s : (PiMat D d)ˣ}
    (hu : u ∈ unitaryOf hτ) (hs : s ∈ orbitGroup π hτ b) : u * s * u⁻¹ ∈ orbitGroup π hτ b := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hs.1) (Subgroup.inv_mem _ hu),
    fun k hk hk' => ?_⟩
  rw [Units.val_mul, Units.val_mul, Pi.mul_apply, Pi.mul_apply, hs.2 k hk hk', Matrix.mul_one,
    apply_mul_inv_apply]

theorem eq_one_of_mem_orbitGroup [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {b : Fin r} {s : (PiMat D d)ˣ}
    (hs : s ∈ orbitGroup π hτ b) (h1 : (s : PiMat D d) b = 1) : s = 1 := by
  apply Units.ext
  funext k
  rw [Units.val_one, Pi.one_apply]
  by_cases hkb : k = b
  · subst hkb
    exact h1
  by_cases hkc : k = π b
  · subst hkc
    have h2 := tau_apply_mul_eq_one hτ hs.1 (π b)
    rw [apply_tau_eq hτ hπ _ (perm_perm hτ hπ b), h1,
      show (Pi.single b (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) : PiMat D d) = piE D d b from
        rfl, tau_piE_apply hτ hπ (perm_perm hτ hπ b), Matrix.one_mul] at h2
    exact h2
  · exact hs.2 k hkb hkc

theorem coordHom_injOn [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {b : Fin r} {s t : (PiMat D d)ˣ}
    (hs : s ∈ orbitGroup π hτ b) (ht : t ∈ orbitGroup π hτ b)
    (h : coordHom D d b s = coordHom D d b t) : s = t := by
  have h1 : s * t⁻¹ = 1 := by
    refine eq_one_of_mem_orbitGroup hτ hπ (Subgroup.mul_mem _ hs (Subgroup.inv_mem _ ht)) ?_
    have h2 := congrArg (fun g : GL (Fin (d b)) (D b) => (g : Matrix (Fin (d b)) (Fin (d b)) (D b)))
      (congrArg (· * (coordHom D d b t)⁻¹) h)
    simp only [mul_inv_cancel, Units.val_one, ← map_inv, ← map_mul, coe_coordHom] at h2
    exact h2
  exact mul_inv_eq_one.mp h1

section Image

variable (b : Fin r)

@[expose] noncomputable def unitAt (g : GL (Fin (d b)) (D b)) : (PiMat D d)ˣ where
  val := Function.update (1 : PiMat D d) b (g : Matrix (Fin (d b)) (Fin (d b)) (D b))
  inv := Function.update (1 : PiMat D d) b ((g⁻¹ : GL (Fin (d b)) (D b)) :
    Matrix (Fin (d b)) (Fin (d b)) (D b))
  val_inv := by
    funext k
    by_cases hk : k = b
    · subst hk
      simp
    · simp [Function.update_of_ne hk]
  inv_val := by
    funext k
    by_cases hk : k = b
    · subst hk
      simp
    · simp [Function.update_of_ne hk]

theorem coe_unitAt (g : GL (Fin (d b)) (D b)) :
    ((unitAt b g : (PiMat D d)ˣ) : PiMat D d) =
      Function.update (1 : PiMat D d) b (g : Matrix (Fin (d b)) (Fin (d b)) (D b)) :=
  rfl

theorem exists_mem_orbitGroup_fix [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {b : Fin r} (hb : π b = b)
    {g : GL (Fin (d b)) (D b)} (hg : g ∈ matUnitary (isInvol_tauFix hτ hπ hb)) :
    ∃ s ∈ orbitGroup π hτ b, coordHom D d b s = g := by
  refine ⟨unitAt b g, ⟨?_, fun k hk _ => ?_⟩, Units.ext ?_⟩
  · rw [mem_unitaryOf]
    funext k
    rw [Pi.mul_apply, Pi.one_apply, apply_tau_eq hτ hπ _ rfl]
    by_cases hk : k = b
    · subst hk
      rw [coe_unitAt, hb, Function.update_self]
      exact hg
    · have hπk : π k ≠ b := fun h => hk (by rw [← perm_perm hτ hπ k, h, hb])
      rw [coe_unitAt, Function.update_of_ne hπk, Function.update_of_ne hk, Pi.one_apply,
        Pi.one_apply, Matrix.mul_one,
        show (Pi.single (π k) (1 : Matrix (Fin (d (π k))) (Fin (d (π k))) (D (π k))) :
          PiMat D d) = piE D d (π k) from rfl, tau_piE_apply hτ hπ rfl]
  · rw [coe_unitAt, Function.update_of_ne hk, Pi.one_apply]
  · rw [coe_coordHom, coe_unitAt, Function.update_self]


theorem tau_single_mul_apply (hτ : IsInvol τ) (b : Fin r)
    (m m' : Matrix (Fin (d b)) (Fin (d b)) (D b)) :
    τ (Pi.single b m) (π b) * τ (Pi.single b m') (π b) = τ (Pi.single b (m' * m)) (π b) := by
  rw [← Pi.mul_apply, ← hτ.map_mul, ← Pi.single_mul]

variable {b} in
@[expose] noncomputable def unitPair [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) (hb : π b ≠ b) (g : GL (Fin (d b)) (D b)) :
    (PiMat D d)ˣ where
  val := Function.update (Function.update (1 : PiMat D d) b (g : Matrix (Fin (d b)) (Fin (d b))
    (D b))) (π b) (τ (Pi.single b ((g⁻¹ : GL (Fin (d b)) (D b)) :
      Matrix (Fin (d b)) (Fin (d b)) (D b))) (π b))
  inv := Function.update (Function.update (1 : PiMat D d) b ((g⁻¹ : GL (Fin (d b)) (D b)) :
    Matrix (Fin (d b)) (Fin (d b)) (D b))) (π b) (τ (Pi.single b (g : Matrix (Fin (d b))
      (Fin (d b)) (D b))) (π b))
  val_inv := by
    funext k
    by_cases hk : k = π b
    · subst hk
      rw [Pi.mul_apply, Function.update_self, Function.update_self, tau_single_mul_apply hτ,
        ← Units.val_mul, mul_inv_cancel, Units.val_one,
        show (Pi.single b (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) : PiMat D d) = piE D d b from
          rfl, tau_piE_apply hτ hπ (perm_perm hτ hπ b), Pi.one_apply]
    · rw [Pi.mul_apply, Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases hkb : k = b
      · subst hkb
        simp
      · simp [Function.update_of_ne hkb]
  inv_val := by
    funext k
    by_cases hk : k = π b
    · subst hk
      rw [Pi.mul_apply, Function.update_self, Function.update_self, tau_single_mul_apply hτ,
        ← Units.val_mul, inv_mul_cancel, Units.val_one,
        show (Pi.single b (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) : PiMat D d) = piE D d b from
          rfl, tau_piE_apply hτ hπ (perm_perm hτ hπ b), Pi.one_apply]
    · rw [Pi.mul_apply, Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases hkb : k = b
      · subst hkb
        simp
      · simp [Function.update_of_ne hkb]

theorem exists_mem_orbitGroup_pair [∀ i, NeZero (d i)] (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {b : Fin r} (hb : π b ≠ b)
    (g : GL (Fin (d b)) (D b)) :
    ∃ s ∈ orbitGroup π hτ b, coordHom D d b s = g := by
  have hbc : b ≠ π b := fun h => hb h.symm
  have hcoe : ((unitPair hτ hπ hb g : (PiMat D d)ˣ) : PiMat D d) =
      Function.update (Function.update (1 : PiMat D d) b (g : Matrix (Fin (d b)) (Fin (d b))
        (D b))) (π b) (τ (Pi.single b ((g⁻¹ : GL (Fin (d b)) (D b)) :
          Matrix (Fin (d b)) (Fin (d b)) (D b))) (π b)) := rfl
  refine ⟨unitPair hτ hπ hb g, ⟨?_, fun k hk hk' => ?_⟩, Units.ext ?_⟩
  · rw [mem_unitaryOf]
    funext k
    rw [Pi.mul_apply, Pi.one_apply]
    by_cases hkb : k = b
    · subst hkb
      rw [apply_tau_eq hτ hπ _ rfl, hcoe, Function.update_self, single_tau_single hτ hπ,
        hτ.invol, Pi.single_eq_same, Function.update_of_ne hbc, Function.update_self,
        ← Units.val_mul, inv_mul_cancel, Units.val_one]
    by_cases hkc : k = π b
    · subst hkc
      rw [apply_tau_eq hτ hπ _ (perm_perm hτ hπ b), hcoe, Function.update_of_ne hbc,
        Function.update_self, Function.update_self, tau_single_mul_apply hτ, ← Units.val_mul,
        inv_mul_cancel, Units.val_one,
        show (Pi.single b (1 : Matrix (Fin (d b)) (Fin (d b)) (D b)) : PiMat D d) = piE D d b from
          rfl, tau_piE_apply hτ hπ (perm_perm hτ hπ b)]
    · have hπk : π k ≠ b := fun h => hkc (by rw [← h, perm_perm hτ hπ])
      have hπk' : π k ≠ π b := fun h => hkb (by rw [← perm_perm hτ hπ k, h, perm_perm hτ hπ])
      rw [apply_tau_eq hτ hπ _ rfl, hcoe, Function.update_of_ne hπk', Function.update_of_ne hπk,
        Function.update_of_ne hkc, Function.update_of_ne hkb, Pi.one_apply, Pi.one_apply,
        Matrix.mul_one,
        show (Pi.single (π k) (1 : Matrix (Fin (d (π k))) (Fin (d (π k))) (D (π k))) :
          PiMat D d) = piE D d (π k) from rfl, tau_piE_apply hτ hπ rfl]
  · rw [hcoe, Function.update_of_ne hk', Function.update_of_ne hk, Pi.one_apply]
  · rw [coe_coordHom, hcoe, Function.update_of_ne hbc, Function.update_self]

end Image

end LayerCores

end CFSG.StandardType
