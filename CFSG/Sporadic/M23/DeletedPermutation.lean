module

public import CFSG.Sporadic.M23.IsotypicCount
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG

namespace M23.DeletedPermutation

abbrev X := Fin 23
abbrev V := Fin 22 → ℂ

variable {G : Type} [Group G] [MulAction G X]

@[expose] def extend (f : V) : X → ℂ :=
  Fin.lastCases 0 f

@[simp] theorem extend_castSucc (f : V) (i : Fin 22) :
    extend f i.castSucc = f i := by
  simp [extend]

@[simp] theorem extend_last (f : V) :
    extend f (Fin.last 22) = 0 := by
  exact Fin.lastCases_last

@[simp] theorem extend_add (f h : V) (x : X) :
    extend (f + h) x = extend f x + extend h x := by
  refine Fin.lastCases ?_ (fun i => ?_) x
  · rw [extend_last, extend_last, extend_last]
    simp
  · simp

@[simp] theorem extend_smul (c : ℂ) (f : V) (x : X) :
    extend (c • f) x = c • extend f x := by
  refine Fin.lastCases ?_ (fun i => ?_) x
  · rw [extend_last, extend_last]
    simp
  · simp

@[expose] def deletedLinear (g : G) : V →ₗ[ℂ] V where
  toFun f i := extend f (g⁻¹ • i.castSucc) - extend f (g⁻¹ • Fin.last 22)
  map_add' f h := by
    funext i
    simp only [Pi.add_apply, extend_add]
    abel
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, extend_smul, smul_eq_mul]
    simp only [RingHom.id_apply]
    ring

@[simp] theorem deletedLinear_apply (g : G) (f : V) (i : Fin 22) :
    deletedLinear g f i =
      extend f (g⁻¹ • i.castSucc) - extend f (g⁻¹ • Fin.last 22) :=
  rfl

private theorem extend_deletedLinear (g : G) (f : V) (x : X) :
    extend (deletedLinear g f) x =
      extend f (g⁻¹ • x) - extend f (g⁻¹ • Fin.last 22) := by
  refine Fin.lastCases ?_ (fun i => ?_) x
  · simp only [extend_last]
    ring
  · simp

@[expose] def deletedRep : Representation ℂ G V where
  toFun := deletedLinear
  map_one' := by
    apply LinearMap.ext
    intro f
    funext i
    change deletedLinear (1 : G) f i = f i
    simp only [deletedLinear_apply, inv_one, one_smul, extend_castSucc, extend_last, sub_zero]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    funext i
    change deletedLinear (g * h) f i = deletedLinear g (deletedLinear h f) i
    simp only [deletedLinear_apply, extend_deletedLinear]
    simp only [mul_inv_rev, mul_smul]
    ring

private def fixedCount (g : G) : ℕ :=
  Fintype.card (MulAction.fixedBy X g)

private theorem extend_single (i : Fin 22) (x : X) :
    extend (Pi.single i 1) x = if x = i.castSucc then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) x
  · change (0 : ℂ) = if Fin.last 22 = i.castSucc then 1 else 0
    rw [ite_eq_right (ne_of_gt (Fin.castSucc_lt_last i))]
  · simp only [extend_castSucc, Pi.single_apply]
    by_cases h : j = i
    · subst h
      simp
    · have hc : j.castSucc ≠ i.castSucc := by simpa
      simp [h, hc]

private theorem fixedCount_cast (g : G) :
    (fixedCount g : ℂ) = ∑ x : X, if g • x = x then 1 else 0 := by
  change (Fintype.card {x : X // g • x = x} : ℂ) = _
  rw [Fintype.card_subtype]
  let s : Finset X := Finset.univ.filter fun x => g • x = x
  calc
    (↑s.card : ℂ) = ∑ _x ∈ s, (1 : ℂ) := by simp
    _ = ∑ x : X, if g • x = x then 1 else 0 := by simp [s]

private theorem fixedCount_inv (g : G) : fixedCount g⁻¹ = fixedCount g := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl X) (by
    intro x
    change (g⁻¹ • x = x) ↔ (g • x = x)
    constructor
    · intro h
      have h' := congrArg (fun y => g • y) h
      simpa [smul_smul] using h'.symm
    · intro h
      have h' := congrArg (fun y => g⁻¹ • y) h
      simpa [smul_smul] using h'.symm)

private theorem sum_over_X_last (f : X → ℂ) :
    ∑ x : X, f x = f (Fin.last 22) + ∑ i : Fin 22, f i.castSucc := by
  have h := Equiv.sum_comp finSuccEquivLast.symm f
  rw [Fintype.sum_option] at h
  simpa using h.symm

private theorem sum_castSucc_indicator (x : X) :
    (∑ i : Fin 22, if x = i.castSucc then (1 : ℂ) else 0) =
      if x = Fin.last 22 then 0 else 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) x
  · have hne : ∀ i : Fin 22, Fin.last 22 ≠ i.castSucc :=
      fun i => ne_of_gt (Fin.castSucc_lt_last i)
    change (∑ i : Fin 22, if Fin.last 22 = i.castSucc then (1 : ℂ) else 0) = 0
    apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right (hne i)]
  · have hne : j.castSucc ≠ Fin.last 22 := ne_of_lt (Fin.castSucc_lt_last j)
    rw [ite_eq_right hne]
    simp

private theorem diagonal_deleted (g : G) (i : Fin 22) :
    ((LinearMap.toMatrix (Pi.basisFun ℂ (Fin 22)) (Pi.basisFun ℂ (Fin 22)))
      (deletedLinear g)) i i =
      (if g⁻¹ • i.castSucc = i.castSucc then 1 else 0) -
      (if g⁻¹ • Fin.last 22 = i.castSucc then 1 else 0) := by
  simp [extend_single]

private theorem character_deletedRep (g : G) :
    deletedRep.character g = (fixedCount g : ℂ) - 1 := by
  change (LinearMap.trace ℂ V) (deletedLinear g) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 22))]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [diagonal_deleted]
  rw [Finset.sum_sub_distrib]
  rw [sum_castSucc_indicator]
  have hc := fixedCount_cast (g := g⁻¹)
  rw [sum_over_X_last] at hc
  rw [fixedCount_inv] at hc
  by_cases h : g⁻¹ • Fin.last 22 = Fin.last 22
  · rw [ite_eq_left h]
    simp only [h, ite_eq_left] at hc
    rw [hc]
    ring
  · rw [ite_eq_right h]
    simp only [h, ite_false] at hc
    rw [hc]
    ring

private def fixedEmbeddingEquiv (k : ℕ) (g : G) :
    MulAction.fixedBy (Fin k ↪ X) g ≃ (Fin k ↪ MulAction.fixedBy X g) where
  toFun e :=
    { toFun := fun i => ⟨e.1 i, by
        change g • e.1 i = e.1 i
        have h := congrArg (fun q : Fin k ↪ X => q i) e.2
        simpa using h⟩
      inj' := fun _ _ h => e.1.injective (Subtype.ext_iff.mp h) }
  invFun e :=
    ⟨{ toFun := fun i => (e i).1
       inj' := fun _ _ h => e.injective (Subtype.ext h) }, by
      apply Function.Embedding.ext
      intro i
      rw [Function.Embedding.smul_apply]
      exact (e i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_descFactorial_fixedCount (k : ℕ) [Fintype G]
    [MulAction.IsMultiplyPretransitive G X k] (hk : k ≤ 23) :
    ∑ g : G, (fixedCount g).descFactorial k = Fintype.card G := by
  let : Fintype (Quotient (MulAction.orbitRel G (Fin k ↪ X))) :=
    Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    G (Fin k ↪ X)
  have hfixed : ∀ g : G,
      Fintype.card (MulAction.fixedBy (Fin k ↪ X) g) =
        (fixedCount g).descFactorial k := by
    intro g
    rw [Fintype.card_congr (fixedEmbeddingEquiv k g)]
    rw [Fintype.card_embedding_eq]
    simp [fixedCount]
  have : Nonempty (Fin k ↪ X) := ⟨
    { toFun := Fin.castLE hk
      inj' := fun _ _ h => Fin.castLE_inj.mp h }⟩
  have hquot : Fintype.card (Quotient (MulAction.orbitRel G (Fin k ↪ X))) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let e0 : Fin k ↪ X := Classical.choice inferInstance
    refine ⟨Quotient.mk'' e0, ?_⟩
    intro q
    refine Quotient.inductionOn q (fun e => ?_)
    apply Quotient.sound
    change e ∈ MulAction.orbit G e0
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G e0 e
    exact ⟨g, hg⟩
  simpa only [hfixed, hquot, one_mul] using h

private theorem sum_descFactorial_fixedCount_cast [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] (k : ℕ) (hk : k ≤ 4) :
    ∑ g : G, ((fixedCount g).descFactorial k : ℂ) = (Fintype.card G : ℂ) := by
  let : MulAction.IsMultiplyPretransitive G X k :=
    MulAction.isMultiplyPretransitive_of_le hk (by norm_num)
  have h := sum_descFactorial_fixedCount (G := G) k (by omega)
  exact_mod_cast h

private theorem sub_one_sq_descFactorial (n : ℕ) :
    ((n : ℂ) - 1) ^ 2 =
      (n.descFactorial 2 : ℂ) - (n.descFactorial 1 : ℂ) + 1 := by
  by_cases h : n < 2
  · interval_cases n <;> norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero]
  · have h1 : 1 ≤ n := by omega
    rw [show n.descFactorial 2 = (n - 1) * n.descFactorial 1 by
      simpa using Nat.descFactorial_succ n 1]
    rw [Nat.descFactorial_one, Nat.cast_mul, Nat.cast_sub h1]
    push_cast
    ring

private theorem sub_one_pow_four_descFactorial (n : ℕ) :
    ((n : ℂ) - 1) ^ 4 =
      (n.descFactorial 4 : ℂ) + 2 * (n.descFactorial 3 : ℂ) +
        (n.descFactorial 2 : ℂ) - (n.descFactorial 1 : ℂ) + 1 := by
  by_cases h : n < 3
  · interval_cases n <;> norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero]
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    rw [show n.descFactorial 4 = (n - 3) * n.descFactorial 3 by
      simpa using Nat.descFactorial_succ n 3]
    rw [show n.descFactorial 3 = (n - 2) * n.descFactorial 2 by
      simpa using Nat.descFactorial_succ n 2]
    rw [show n.descFactorial 2 = (n - 1) * n.descFactorial 1 by
      simpa using Nat.descFactorial_succ n 1]
    rw [Nat.descFactorial_one]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    ring

private theorem sum_character_mul_inv [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] :
    ∑ g : G, deletedRep.character g * deletedRep.character g⁻¹ =
      (Fintype.card G : ℂ) := by
  calc
    ∑ g : G, deletedRep.character g * deletedRep.character g⁻¹ =
        ∑ g : G, ((fixedCount g : ℂ) - 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [character_deletedRep, character_deletedRep, fixedCount_inv]
      ring
    _ = ∑ g : G, (((fixedCount g).descFactorial 2 : ℂ) -
          ((fixedCount g).descFactorial 1 : ℂ) + 1) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact sub_one_sq_descFactorial (fixedCount g)
    _ = (∑ g : G, ((fixedCount g).descFactorial 2 : ℂ)) -
          (∑ g : G, ((fixedCount g).descFactorial 1 : ℂ)) +
          ∑ _g : G, (1 : ℂ) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (Fintype.card G : ℂ) := by
      rw [sum_descFactorial_fixedCount_cast (G := G) 2 (by omega),
        sum_descFactorial_fixedCount_cast (G := G) 1 (by omega)]
      simp

theorem deletedRep_isIrreducible [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] :
    (deletedRep (G := G)).IsIrreducible := by
  have hs : CategoryTheory.Simple (FDRep.of (deletedRep (G := G))) :=
    (FDRep.simple_iff_char_is_norm_one (FDRep.of (deletedRep (G := G)))).2 (by
      change ∑ g : G, (deletedRep (G := G)).character g *
        (deletedRep (G := G)).character g⁻¹ = (Nat.card G : ℂ)
      simpa only [Nat.card_eq_fintype_card] using (sum_character_mul_inv (G := G)))
  let : CategoryTheory.Simple (FDRep.of (deletedRep (G := G))) := hs
  exact M23.simple_fdrep_isIrreducible (deletedRep (G := G))

private theorem sum_tensor_character_mul_inv [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] :
    ∑ g : G, (deletedRep.tprod deletedRep).character g *
      (deletedRep.tprod deletedRep).character g⁻¹ =
      4 * (Fintype.card G : ℂ) := by
  calc
    ∑ g : G, (deletedRep.tprod deletedRep).character g *
        (deletedRep.tprod deletedRep).character g⁻¹ =
        ∑ g : G, ((fixedCount g : ℂ) - 1) ^ 4 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [Representation.char_tensor]
      simp only [Pi.mul_apply]
      rw [character_deletedRep, character_deletedRep, fixedCount_inv]
      ring
    _ = ∑ g : G, (((fixedCount g).descFactorial 4 : ℂ) +
          2 * ((fixedCount g).descFactorial 3 : ℂ) +
          ((fixedCount g).descFactorial 2 : ℂ) -
          ((fixedCount g).descFactorial 1 : ℂ) + 1) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact sub_one_pow_four_descFactorial (fixedCount g)
    _ = 4 * (Fintype.card G : ℂ) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [sum_descFactorial_fixedCount_cast (G := G) 4 (by omega),
        sum_descFactorial_fixedCount_cast (G := G) 3 (by omega),
        sum_descFactorial_fixedCount_cast (G := G) 2 (by omega),
        sum_descFactorial_fixedCount_cast (G := G) 1 (by omega)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem tensor_intertwining_finrank [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] :
    Module.finrank ℂ ((deletedRep (G := G)).tprod deletedRep |>.IntertwiningMap
      ((deletedRep (G := G)).tprod deletedRep)) = 4 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    norm_cast
    exact Nat.ne_of_gt (Nat.card_pos (α := G)))
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    ((deletedRep (G := G)).tprod deletedRep)
    ((deletedRep (G := G)).tprod deletedRep)
  rw [sum_tensor_character_mul_inv (G := G)] at h
  rw [Nat.card_eq_fintype_card] at h
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    norm_cast
    exact Fintype.card_ne_zero
  have hsimp : (Fintype.card G : ℂ)⁻¹ * (4 * Fintype.card G) = 4 := by
    field_simp
  rw [hsimp] at h
  exact_mod_cast h.symm

private theorem sum_tensor_character [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] :
    ∑ g : G, ((deletedRep (G := G)).tprod deletedRep).character g =
      (Fintype.card G : ℂ) := by
  calc
    ∑ g : G, ((deletedRep (G := G)).tprod deletedRep).character g =
        ∑ g : G, ((fixedCount g : ℂ) - 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [Representation.char_tensor]
      simp only [Pi.mul_apply]
      rw [character_deletedRep]
      ring
    _ = ∑ g : G, (((fixedCount g).descFactorial 2 : ℂ) -
          ((fixedCount g).descFactorial 1 : ℂ) + 1) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact sub_one_sq_descFactorial (fixedCount g)
    _ = (∑ g : G, ((fixedCount g).descFactorial 2 : ℂ)) -
          (∑ g : G, ((fixedCount g).descFactorial 1 : ℂ)) +
          ∑ _g : G, (1 : ℂ) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (Fintype.card G : ℂ) := by
      rw [sum_descFactorial_fixedCount_cast (G := G) 2 (by omega),
        sum_descFactorial_fixedCount_cast (G := G) 1 (by omega)]
      simp

theorem tensor_invariants_finrank [Fintype G]
    [MulAction.IsMultiplyPretransitive G X 4] :
    Module.finrank ℂ ((deletedRep (G := G)).tprod deletedRep).invariants = 1 := by
  let rho := (deletedRep (G := G)).tprod deletedRep
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    norm_cast
    exact Nat.ne_of_gt (Nat.card_pos (α := G)))
  have h := Representation.card_inv_mul_sum_char_eq_finrank rho
  rw [show ∑ g : G, rho.character g = (Fintype.card G : ℂ) by
    simpa [rho] using (sum_tensor_character (G := G))] at h
  rw [Nat.card_eq_fintype_card] at h
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    norm_cast
    exact Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard] at h
  exact_mod_cast h.symm

end M23.DeletedPermutation

end CFSG
