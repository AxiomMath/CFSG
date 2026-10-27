module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace S1567

section Core

abbrev Mat3 := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def Inv3 (g : Mat3) : Prop := g * g = 1 ∧ g ≠ 1

instance : DecidablePred Inv3 := fun g => by unfold Inv3; infer_instance

@[expose] def Fx3 (g : Mat3) : Finset (Fin 3 → ZMod 2) := Finset.univ.filter (fun v => g.mulVec v = v)

theorem trans3 : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    v = w ∨ ∃ M : Mat3, M * M = 1 ∧ M.mulVec v = w := by
  decide +kernel

theorem fix3_card_one : ∀ g : Mat3, Inv3 g → (Fx3 g).card = 4 ∧ (Fx3 gᵀ).card = 4 := by
  decide +kernel

@[expose] def Pair2 (g h : Mat3) : Prop :=
  Inv3 h → g * h = h * g → g ≠ h → (Fx3 g ∩ Fx3 h).card * (Fx3 gᵀ ∩ Fx3 hᵀ).card ≤ 8

instance (g h : Mat3) : Decidable (Pair2 g h) := by unfold Pair2; infer_instance

theorem fix3_card_two : ∀ g : Mat3, Inv3 g → ∀ h : Mat3, Pair2 g h := by decide +kernel

@[expose] def Third3 (g h : Mat3) : Prop :=
  ∀ k : Mat3, Inv3 k → g * k = k * g → h * k = k * h → k ≠ g → k ≠ h → k = g * h

instance (g h : Mat3) : Decidable (Third3 g h) := by unfold Third3; infer_instance

@[expose] def Pair3 (g h : Mat3) : Prop := Inv3 h → g * h = h * g → g ≠ h → Third3 g h

instance (g h : Mat3) : Decidable (Pair3 g h) := by unfold Pair3; infer_instance

theorem third3 : ∀ g : Mat3, Inv3 g → ∀ h : Mat3, Pair3 g h := by decide +kernel

end Core

section I2

theorem moduleAct_false (g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
    moduleAct false g = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

theorem moduleAct_true_of_mul_self (g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (hg : g * g = 1) :
    moduleAct true g = (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  have : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  simp [moduleAct, this]

theorem inv3_of_mem {B : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))} (hB : IsElemAbelian 2 B)
    {g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)} (hg : g ∈ B) (hg1 : g ≠ 1) :
    Inv3 (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  refine ⟨?_, fun h => hg1 (Units.ext h)⟩
  have h2 := hB.2 g hg
  rw [pow_two] at h2
  exact congrArg Units.val h2

theorem card_subgroup_le_of_forall_mem {H : Type*} [Group H] [Finite H] (B : Subgroup H) (S : Finset H)
    (h : ∀ x ∈ B, x ∈ S) : Nat.card B ≤ S.card := by
  classical
  calc Nat.card B ≤ Nat.card (S : Set H) := Nat.card_mono (Set.toFinite _) (fun x hx => h x hx)
    _ = S.card := by simp

theorem fix_card_mul_le_Z (B : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
    (hB : IsElemAbelian 2 B) (hB1 : B ≠ ⊥) :
    Set.ncard {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct false b).mulVec v = v} *
      Set.ncard {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct true b).mulVec v = v} * Nat.card B ≤ 32 := by
  classical
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => by
    have := hB.1
    exact setLike_mul_comm hx hy
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => by
    have h2 := hB.2 x hx
    rwa [pow_two] at h2
  obtain ⟨g, hgB, hg1⟩ : ∃ g ∈ B, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hB1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  have hIg : Inv3 (g : Mat3) := inv3_of_mem hB hgB hg1
  obtain ⟨hF1, hF1t⟩ := fix3_card_one _ hIg
  have hfix1 : {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct false b).mulVec v = v} ⊆ ↑(Fx3 (g : Mat3)) := by
    intro v hv
    simpa [Fx3, moduleAct_false] using hv g hgB
  have hfix2 : {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct true b).mulVec v = v} ⊆ ↑(Fx3 (g : Mat3)ᵀ) := by
    intro v hv
    have := hv g hgB
    rw [moduleAct_true_of_mul_self g (hsq g hgB)] at this
    simpa [Fx3] using this
  by_cases hA : ∀ h ∈ B, h = 1 ∨ h = g
  · have hBc : Nat.card B ≤ 2 := by
      refine (card_subgroup_le_of_forall_mem B {1, g} fun h hh => ?_).trans (Finset.card_le_two)
      rcases hA h hh with rfl | rfl <;> simp
    have c1 : Set.ncard {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct false b).mulVec v = v} ≤ 4 := by
      calc _ ≤ Set.ncard (↑(Fx3 (g : Mat3)) : Set (Fin 3 → ZMod 2)) :=
            Set.ncard_le_ncard hfix1 (Finset.finite_toSet _)
        _ = 4 := by rw [Set.ncard_coe_finset, hF1]
    have c2 : Set.ncard {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct true b).mulVec v = v} ≤ 4 := by
      calc _ ≤ Set.ncard (↑(Fx3 (g : Mat3)ᵀ) : Set (Fin 3 → ZMod 2)) :=
            Set.ncard_le_ncard hfix2 (Finset.finite_toSet _)
        _ = 4 := by rw [Set.ncard_coe_finset, hF1t]
    calc _ ≤ 4 * 4 * 2 := Nat.mul_le_mul (Nat.mul_le_mul c1 c2) hBc
      _ = 32 := by norm_num
  · push Not at hA
    obtain ⟨h, hhB, hh1, hhg⟩ := hA
    have hIh : Inv3 (h : Mat3) := inv3_of_mem hB hhB hh1
    have hgh : (g : Mat3) * h = h * g := congrArg Units.val (hcomm g hgB h hhB)
    have hne : (g : Mat3) ≠ h := fun e => hhg (Units.ext e).symm
    have h2 := fix3_card_two _ hIg _ hIh hgh hne
    have hBc : Nat.card B ≤ 4 := by
      refine (card_subgroup_le_of_forall_mem B {1, g, h, g * h} fun k hkB => ?_).trans
        Finset.card_le_four
      by_contra hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      obtain ⟨hk1, hkg, hkh, hkgh⟩ := hk
      have hIk := inv3_of_mem hB hkB hk1
      have h3 := third3 _ hIg _ hIh hgh hne (k : Mat3) hIk
        (congrArg Units.val (hcomm g hgB k hkB)) (congrArg Units.val (hcomm h hhB k hkB))
        (fun e => hkg (Units.ext e)) (fun e => hkh (Units.ext e))
      exact hkgh (Units.ext (by simpa using h3))
    have c1 : Set.ncard {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct false b).mulVec v = v} ≤
        (Fx3 (g : Mat3) ∩ Fx3 (h : Mat3)).card := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun v hv => ?_) (Finset.finite_toSet _)
      have e1 := hv g hgB
      have e2 := hv h hhB
      simp only [moduleAct_false] at e1 e2
      simp [Fx3, e1, e2]
    have c2 : Set.ncard {v : Fin 3 → ZMod 2 | ∀ b ∈ B, (moduleAct true b).mulVec v = v} ≤
        (Fx3 (g : Mat3)ᵀ ∩ Fx3 (h : Mat3)ᵀ).card := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun v hv => ?_) (Finset.finite_toSet _)
      have e1 := hv g hgB
      have e2 := hv h hhB
      rw [moduleAct_true_of_mul_self g (hsq g hgB)] at e1
      rw [moduleAct_true_of_mul_self h (hsq h hhB)] at e2
      simp [Fx3, e1, e2]
    calc _ ≤ (Fx3 (g : Mat3) ∩ Fx3 (h : Mat3)).card * (Fx3 (g : Mat3)ᵀ ∩ Fx3 (h : Mat3)ᵀ).card * 4 :=
          Nat.mul_le_mul (Nat.mul_le_mul c1 c2) hBc
      _ ≤ 8 * 4 := Nat.mul_le_mul_right _ h2
      _ = 32 := by norm_num

end I2

section Transport

variable {F : Type} [Field F]

@[expose] noncomputable def toZMod2 [Fintype F] (hF : Fintype.card F = 2) : F ≃+* ZMod 2 :=
  (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm

@[expose] noncomputable def glMap {K : Type} [Field K] (ε : F ≃+* K) :
    Matrix.GeneralLinearGroup (Fin 3) F ≃* Matrix.GeneralLinearGroup (Fin 3) K :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 3) ε).toMulEquiv

theorem val_glMap {K : Type} [Field K] (ε : F ≃+* K) (g : Matrix.GeneralLinearGroup (Fin 3) F) :
    ((glMap ε g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) F).map ε := rfl

theorem moduleAct_glMap {K : Type} [Field K] (ε : F ≃+* K) (dual : Bool)
    (g : Matrix.GeneralLinearGroup (Fin 3) F) :
    moduleAct dual (glMap ε g) = (moduleAct dual g).map ε := by
  unfold moduleAct
  split_ifs
  · rw [← map_inv (glMap ε) g, val_glMap, Matrix.transpose_map]
  · rw [val_glMap]


theorem mulVec_map_ring {K : Type} [Field K] (ε : F ≃+* K) (M : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    (M.map ε).mulVec (fun i => ε (v i)) = fun i => ε ((M.mulVec v) i) := by
  funext i
  exact (RingHom.map_mulVec (ε : F →+* K) M v i).symm

theorem isElemAbelian_map {K : Type} [Field K] (ε : F ≃+* K) {B : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)}
    (hB : IsElemAbelian 2 B) : IsElemAbelian 2 (B.map (glMap ε).toMonoidHom) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x', hx', hx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y', hy', hy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    have hc := (by have := hB.1; exact setLike_mul_comm hx' hy' :
      x' * y' = y' * x')
    show (x : Matrix.GeneralLinearGroup (Fin 3) K) * y = y * x
    rw [← hx, ← hy]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc]
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow]
    simp [hB.2 x' hx']

theorem ncard_fix_map {K : Type} [Field K] (ε : F ≃+* K)
    (B : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)) (dual : Bool) :
    Set.ncard {v : Fin 3 → K | ∀ b ∈ B.map (glMap ε).toMonoidHom, (moduleAct dual b).mulVec v = v} =
      Set.ncard {v : Fin 3 → F | ∀ b ∈ B, (moduleAct dual b).mulVec v = v} := by
  have hinj : Function.Injective (fun v : Fin 3 → F => fun i => ε (v i)) := fun v w h =>
    funext fun i => ε.injective (congrFun h i)
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hw
    refine ⟨fun i => ε.symm (w i), fun b hb => ?_, funext fun i => by simp⟩
    have h1 := hw (glMap ε b) ⟨b, hb, rfl⟩
    rw [moduleAct_glMap] at h1
    have h2 : (fun i => ε ((moduleAct dual b).mulVec (fun j => ε.symm (w j)) i)) =
        fun i => ε (ε.symm (w i)) := by
      rw [← mulVec_map_ring]
      simpa using h1
    funext i
    exact ε.injective (congrFun h2 i)
  · rintro ⟨v, hv, rfl⟩ b' ⟨b, hb, rfl⟩
    rw [moduleAct_glMap, mulVec_map_ring]
    funext i
    rw [hv b hb]

theorem fix_card_mul_le [Fintype F] (hF : Fintype.card F = 2)
    (B : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)) (hB : IsElemAbelian 2 B) (hB1 : B ≠ ⊥) :
    Set.ncard {v : Fin 3 → F | ∀ b ∈ B, (moduleAct false b).mulVec v = v} *
      Set.ncard {v : Fin 3 → F | ∀ b ∈ B, (moduleAct true b).mulVec v = v} * Nat.card B ≤ 32 := by
  have hB1' : B.map (glMap (toZMod2 hF)).toMonoidHom ≠ ⊥ := by
    intro h
    apply hB1
    rw [eq_bot_iff]
    intro x hx
    have : (glMap (toZMod2 hF)) x ∈ B.map (glMap (toZMod2 hF)).toMonoidHom := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 ((glMap (toZMod2 hF)).injective (by simpa using this))
  have h := fix_card_mul_le_Z _ (isElemAbelian_map (toZMod2 hF) hB) hB1'
  have hc : Nat.card ↥(B.map (glMap (toZMod2 hF)).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (f := (glMap (toZMod2 hF)).toMonoidHom)
      (glMap (toZMod2 hF)).injective
  rwa [ncard_fix_map, ncard_fix_map, hc] at h

theorem eq_one_of_card_two [Fintype F] (hF : Fintype.card F = 2) {x : F} (hx : x ≠ 0) : x = 1 := by
  have h : toZMod2 hF x ≠ 0 := fun h => hx (by simpa using h)
  have h1 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact (toZMod2 hF).injective (by simpa using h1 _ h)

theorem mem_statedSL_of_card_two [Fintype F] (hF : Fintype.card F = 2)
    (g : Matrix.GeneralLinearGroup (Fin 3) F) : g ∈ StatedSL 3 F := by
  refine Subgroup.subset_closure ?_
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
  exact eq_one_of_card_two hF hdet

theorem exists_inv_mulVec [Fintype F] (hF : Fintype.card F = 2) (dual : Bool) (v w : Fin 3 → F)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) F, g * g = 1 ∧ (moduleAct dual g).mulVec v = w := by
  by_cases hvw : v = w
  · exact ⟨1, by simp, by subst hvw; cases dual <;> simp [moduleAct]⟩
  set ε := toZMod2 hF with hε
  have hv' : (fun i => ε (v i)) ≠ 0 := fun h => hv (funext fun i => ε.injective (by simpa using congrFun h i))
  have hw' : (fun i => ε (w i)) ≠ 0 := fun h => hw (funext fun i => ε.injective (by simpa using congrFun h i))
  rcases trans3 _ _ hv' hw' with h | ⟨M', hM'2, hM'v⟩
  · exact absurd (funext fun i => ε.injective (congrFun h i)) hvw
  · set M : Matrix (Fin 3) (Fin 3) F := M'.map ε.symm with hM
    have hMM : M * M = 1 := by
      rw [hM, ← Matrix.map_mul, hM'2]
      simp
    have hMv : M.mulVec v = w := by
      have h1 := mulVec_map_ring ε M v
      have hM' : M.map ε = M' := by
        rw [hM, Matrix.map_map]
        ext i j
        simp
      rw [hM'] at h1
      funext i
      apply ε.injective
      have := congrFun h1 i
      rw [hM'v] at h1
      simpa using (congrFun h1 i).symm
    cases dual
    · exact ⟨⟨M, M, hMM, hMM⟩, Units.ext hMM, by simpa [moduleAct] using hMv⟩
    · have hMtMt : Mᵀ * Mᵀ = 1 := by
        rw [← Matrix.transpose_mul, hMM, Matrix.transpose_one]
      refine ⟨⟨Mᵀ, Mᵀ, hMtMt, hMtMt⟩, Units.ext hMtMt, ?_⟩
      have hinv : (⟨Mᵀ, Mᵀ, hMtMt, hMtMt⟩ : Matrix.GeneralLinearGroup (Fin 3) F)⁻¹ =
          ⟨Mᵀ, Mᵀ, hMtMt, hMtMt⟩ := rfl
      simpa [moduleAct, hinv] using hMv

end Transport

end S1567

end CFSG.Quasithin
