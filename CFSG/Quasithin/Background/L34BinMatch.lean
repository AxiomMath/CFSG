module

public import CFSG.Quasithin.Background.L34BinPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.Quasithin.Background.HMathieuBits

public section

namespace CFSG.Quasithin.L34Bin

open CFSG.Fischer CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso)
open scoped MatrixGroups Matrix

section Descent

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem exists_zmod_intertwiner_rect {G : Type} [Group G] {n m : ℕ}
    (hF : Fintype.card F = 2 ^ f) (R₁ : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (R₂ : G →* Matrix (Fin m) (Fin m) (ZMod 2)) (M : Matrix (Fin m) (Fin n) F) (hM0 : M ≠ 0)
    (hM : ∀ g, M * (R₁ g).map (ZMod.castHom (dvd_refl 2) F) =
      (R₂ g).map (ZMod.castHom (dvd_refl 2) F) * M) :
    ∃ M₀ : Matrix (Fin m) (Fin n) (ZMod 2), M₀ ≠ 0 ∧ ∀ g, M₀ * R₁ g = R₂ g * M₀ := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  let S : Submodule F (Fin m × Fin n → F) :=
    { carrier := {v | ∀ g, Matrix.of (fun a b => v (a, b)) * (R₁ g).map φ =
        (R₂ g).map φ * Matrix.of (fun a b => v (a, b))}
      add_mem' := fun {v w} hv hw g => by
        have e : Matrix.of (fun a b => (v + w) (a, b)) =
            Matrix.of (fun a b => v (a, b)) + Matrix.of (fun a b => w (a, b)) := by
          ext a b
          rfl
        rw [e, Matrix.add_mul, Matrix.mul_add, hv g, hw g]
      zero_mem' := fun g => by
        have e : Matrix.of (fun a b => (0 : Fin m × Fin n → F) (a, b)) = 0 := by
          ext a b
          rfl
        rw [e, Matrix.zero_mul, Matrix.mul_zero]
      smul_mem' := fun c v hv g => by
        have e : Matrix.of (fun a b => (c • v) (a, b)) =
            c • Matrix.of (fun a b => v (a, b)) := by
          ext a b
          rfl
        rw [e, Matrix.smul_mul, Matrix.mul_smul, hv g] }
  let sq : F →+* F := frobeniusEquiv F 2
  have hsqφ : ⇑sq ∘ ⇑φ = ⇑φ := by
    rw [← RingHom.coe_comp, RingHom.ext_zmod (sq.comp φ) φ]
  have hΦ : ∀ v ∈ S, (fun i => v i ^ 2) ∈ S := by
    intro v hv g
    have h1 := congrArg (fun N : Matrix (Fin m) (Fin n) F => N.map sq) (hv g)
    simp only [Matrix.map_mul] at h1
    have h2 : ((R₁ g).map φ).map sq = (R₁ g).map φ := by
      rw [Matrix.map_map, hsqφ]
    have h3 : ((R₂ g).map φ).map sq = (R₂ g).map φ := by
      rw [Matrix.map_map, hsqφ]
    rw [h2, h3] at h1
    have e : Matrix.of (fun a b => (fun i => v i ^ 2) (a, b)) =
        (Matrix.of (fun a b => v (a, b))).map sq := by
      ext a b
      rfl
    rw [e]
    exact h1
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hmem : (fun p : Fin m × Fin n => M p.1 p.2) ∈ S := fun g => hM g
    rw [hbot] at hmem
    apply hM0
    ext a b
    exact congrFun (Submodule.mem_bot F |>.mp hmem) (a, b)
  obtain ⟨y, hy0, hyS⟩ := exists_fixed_mem hF S hΦ hSne
  refine ⟨Matrix.of fun a b => y (a, b), ?_, fun g => ?_⟩
  · intro h
    apply hy0
    funext p
    exact congrFun (congrFun h p.1) p.2
  · have h1 := hyS g
    have h2 : (Matrix.of fun a b => (fun i => φ (y i)) (a, b)) =
        (Matrix.of fun a b => y (a, b)).map φ := rfl
    rw [h2, ← Matrix.map_mul, ← Matrix.map_mul] at h1
    exact Matrix.map_injective φ.injective h1

end Descent

section Schur

variable {k G : Type} [Field k] [Group G]

theorem bijective_of_intertwiner {n m : ℕ} {R₁ : G →* Matrix (Fin n) (Fin n) k}
    {R₂ : G →* Matrix (Fin m) (Fin m) k}
    (h₁ : ∀ N : Submodule k (Fin n → k), (∀ g, ∀ v ∈ N, (R₁ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (h₂ : ∀ N : Submodule k (Fin m → k), (∀ g, ∀ v ∈ N, (R₂ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    {M : Matrix (Fin m) (Fin n) k} (hM0 : M ≠ 0) (hM : ∀ g, M * R₁ g = R₂ g * M) :
    Function.Bijective M.mulVec := by
  have hker : LinearMap.ker M.mulVecLin = ⊥ := by
    rcases h₁ (LinearMap.ker M.mulVecLin) (fun g v hv => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM g,
        ← Matrix.mulVec_mulVec]
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      rw [hv, Matrix.mulVec_zero]) with h | h
    · exact h
    · exfalso
      apply hM0
      ext i j
      have hj : (Pi.single j (1 : k) : Fin n → k) ∈ LinearMap.ker M.mulVecLin := by
        rw [h]
        exact Submodule.mem_top
      have h2 : M.mulVec (Pi.single j 1) = 0 := hj
      simpa [Matrix.mulVec_single_one] using congrFun h2 i
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    rcases h₂ (LinearMap.range M.mulVecLin) (fun g v hv => by
      obtain ⟨w, rfl⟩ := hv
      refine ⟨(R₁ g).mulVec w, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM g,
        ← Matrix.mulVec_mulVec]) with h | h
    · exfalso
      apply hM0
      ext i j
      have hj : M.mulVec (Pi.single j (1 : k)) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at hj
      simpa [Matrix.mulVec_single_one] using congrFun hj i
    · exact h
  exact ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩

end Schur

variable {n m : ℕ}

theorem exists_zmod_intertwiner_of_quot (ρ₁ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (ρ₂ : SL(3, F4) →* Matrix (Fin m) (Fin m) (ZMod 2)) {a b : Fin 2 → Bool}
    (π : Representation.IntertwiningMap (matRep (baseF ρ₁))
      (matRep (tensorRep (F := F4) F4 a b))) (hπ : Function.Surjective π)
    {Z : Subrepresentation (matRep (baseF ρ₂))}
    (eZ : Representation.Equiv Z.toRepresentation (matRep (tensorRep (F := F4) F4 a b))) :
    ∃ M₀ : Matrix (Fin m) (Fin n) (ZMod 2), M₀ ≠ 0 ∧ ∀ g, M₀ * ρ₁ g = ρ₂ g * M₀ := by
  classical
  have hirrT := ((tensorRep_absolutely_irreducible_and_distinct F4 card_F4 (by norm_num)).1 a b).1
  have hnt : Nontrivial (TIdx 2 a b → F4) :=
    ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hirrT).1
  let T : (Fin n → F4) →ₗ[F4] (Fin m → F4) :=
    Z.toSubmodule.subtype ∘ₗ eZ.symm.toLinearEquiv.toLinearMap ∘ₗ π.toLinearMap
  have hT0 : T ≠ 0 := by
    intro h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (TIdx 2 a b → F4)
    obtain ⟨v, hv⟩ := hπ (x - y)
    have h1 := LinearMap.congr_fun h v
    have h2 : ((eZ.symm (π v) : Z.toSubmodule) : Fin m → F4) = 0 := h1
    have h3 : eZ.symm (π v) = 0 := Subtype.ext h2
    have h4 : π v = 0 := by
      have := congrArg eZ h3
      rwa [Representation.Equiv.apply_symm_apply, map_zero] at this
    rw [hv] at h4
    exact hxy (sub_eq_zero.mp h4)
  have hTc : ∀ g v, T ((baseF ρ₁ g).mulVec v) = (baseF ρ₂ g).mulVec (T v) := by
    intro g v
    show ((eZ.symm (π ((matRep (baseF ρ₁)) g v)) : Z.toSubmodule) : Fin m → F4) =
      (matRep (baseF ρ₂)) g ((eZ.symm (π v) : Z.toSubmodule) : Fin m → F4)
    rw [Representation.IntertwiningMap.isIntertwining (matRep (baseF ρ₁)) _ π g v]
    exact congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining _ _ eZ.symm.toIntertwiningMap g (π v))
  obtain ⟨M, hM0, hM⟩ := exists_matrix_intertwiner (baseF ρ₁) (baseF ρ₂) T hT0 hTc
  exact exists_zmod_intertwiner_rect card_F4 ρ₁ ρ₂ M hM0 hM

theorem shiftBits_shiftBits (a : Fin 2 → Bool) : shiftBits 2 (shiftBits 2 a) = a := by
  revert a
  decide

theorem exists_iso_of_pair (ρ₁ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (ρ₂ : SL(3, F4) →* Matrix (Fin m) (Fin m) (ZMod 2)) (hn : 0 < n)
    (h₁ : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₁ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (h₂ : ∀ N : Submodule (ZMod 2) (Fin m → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₂ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) {a b c d : Fin 2 → Bool}
    {Y Y' : Subrepresentation (matRep (baseF ρ₁))} (hY : Y.toRepresentation.IsIrreducible)
    (hY' : Y'.toRepresentation.IsIrreducible)
    (eY : Representation.Equiv Y.toRepresentation (matRep (tensorRep (F := F4) F4 a b)))
    (eY' : Representation.Equiv Y'.toRepresentation
      (matRep (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b))))
    (htop : Y.toSubmodule ⊔ Y'.toSubmodule = ⊤) {Z Z' : Subrepresentation (matRep (baseF ρ₂))}
    (eZ : Representation.Equiv Z.toRepresentation (matRep (tensorRep (F := F4) F4 c d)))
    (eZ' : Representation.Equiv Z'.toRepresentation
      (matRep (tensorRep (F := F4) F4 (shiftBits 2 c) (shiftBits 2 d))))
    (hcd : (c = a ∧ d = b) ∨ (c = shiftBits 2 a ∧ d = shiftBits 2 b)) :
    ∃ M₀ : Matrix (Fin m) (Fin n) (ZMod 2), Function.Bijective M₀.mulVec ∧
      ∀ g, M₀ * ρ₁ g = ρ₂ g * M₀ := by
  classical
  obtain ⟨a₁, b₁, π, hπ⟩ := exists_simple_quotient card_F4 (by norm_num) (baseF ρ₁) hn
  have hirrT :=
    ((tensorRep_absolutely_irreducible_and_distinct F4 card_F4 (by norm_num)).1 a₁ b₁).1
  let Mj : ℕ → Subrepresentation (matRep (baseF ρ₁)) := fun j => if j = 0 then Y else Y'
  have hMj : ∀ j, (Mj j).toRepresentation.IsIrreducible := fun j => by
    by_cases hj : j = 0
    · rw [show Mj j = Y from ite_eq_left hj]
      exact hY
    · rw [show Mj j = Y' from ite_eq_right hj]
      exact hY'
  have hsup : ⨆ j, (Mj j).toSubmodule = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine sup_le ?_ ?_
    · exact le_iSup_of_le 0 (by rw [show Mj 0 = Y from ite_eq_left rfl])
    · exact le_iSup_of_le 1 (by rw [show Mj 1 = Y' from ite_eq_right one_ne_zero])
  obtain ⟨j, ⟨e⟩⟩ := exists_iso_of_surj_onto_irred hirrT π hπ Mj hMj hsup
  have key : ∀ Z : Subrepresentation (matRep (baseF ρ₁)), Mj j = Z →
      Nonempty (Representation.Equiv Z.toRepresentation
        (matRep (tensorRep (F := F4) F4 a₁ b₁))) := by
    rintro Z rfl
    exact ⟨e⟩
  have hdist := (tensorRep_absolutely_irreducible_and_distinct F4 card_F4 (by norm_num)).2
  have hab : (a₁ = a ∧ b₁ = b) ∨ (a₁ = shiftBits 2 a ∧ b₁ = shiftBits 2 b) := by
    by_cases hj : j = 0
    · obtain ⟨e'⟩ := key Y (ite_eq_left hj)
      obtain ⟨h1, h2⟩ := hdist _ _ _ _ ⟨eY.symm.trans e'⟩
      exact Or.inl ⟨h1.symm, h2.symm⟩
    · obtain ⟨e'⟩ := key Y' (ite_eq_right hj)
      obtain ⟨h1, h2⟩ := hdist _ _ _ _ ⟨eY'.symm.trans e'⟩
      exact Or.inr ⟨h1.symm, h2.symm⟩
  have hemb : ∃ W : Subrepresentation (matRep (baseF ρ₂)),
      Nonempty (Representation.Equiv W.toRepresentation
        (matRep (tensorRep (F := F4) F4 a₁ b₁))) := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Z, ⟨eZ⟩⟩
    · rw [shiftBits_shiftBits, shiftBits_shiftBits] at eZ'
      exact ⟨Z', ⟨eZ'⟩⟩
    · exact ⟨Z', ⟨eZ'⟩⟩
    · exact ⟨Z, ⟨eZ⟩⟩
  obtain ⟨W, ⟨eW⟩⟩ := hemb
  obtain ⟨M₀, hM0, hM⟩ := exists_zmod_intertwiner_of_quot ρ₁ ρ₂ π hπ eW
  exact ⟨M₀, bijective_of_intertwiner h₁ h₂ hM0 hM, hM⟩

@[expose] noncomputable def w0GLb : GL (Fin 3) F4 := Matrix.SpecialLinearGroup.toGL wJ

@[expose] noncomputable def gamSL : SL(3, F4) →* SL(3, F4) :=
  (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F4
    w0GLb).toMonoidHom.comp (tauSL F4)

theorem nonempty_equiv_tensorRep_gam (a b : Fin 2 → Bool) :
    Nonempty (Representation.Equiv (matRep ((tensorRep (F := F4) F4 a b).comp gamSL))
      (matRep (tensorRep (F := F4) F4 b a))) := by
  have h1 := (tensorRep_comp_conj (F := F4) F4 w0GLb a b).comp (tauSL F4)
  have h2 := tensorRep_comp_tau (F := F4) F4 a b
  rw [MonoidHom.comp_assoc] at h1
  exact (h1.trans h2).equiv

theorem pair_gam {ρ₀ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2)} {a b : Fin 2 → Bool}
    {Y Y' : Subrepresentation (matRep (baseF ρ₀))}
    (eY : Representation.Equiv Y.toRepresentation (matRep (tensorRep (F := F4) F4 a b)))
    (eY' : Representation.Equiv Y'.toRepresentation
      (matRep (tensorRep (F := F4) F4 (shiftBits 2 a) (shiftBits 2 b)))) :
    ∃ Z Z' : Subrepresentation (matRep (baseF (ρ₀.comp gamSL))),
      Nonempty (Representation.Equiv Z.toRepresentation
        (matRep (tensorRep (F := F4) F4 b a))) ∧
      Nonempty (Representation.Equiv Z'.toRepresentation
        (matRep (tensorRep (F := F4) F4 (shiftBits 2 b) (shiftBits 2 a)))) := by
  let ofY : Subrepresentation (matRep (baseF ρ₀)) →
      Subrepresentation (matRep (baseF (ρ₀.comp gamSL))) := fun Y =>
    ⟨Y.toSubmodule, fun g _ hv => Y.apply_mem_toSubmodule (gamSL g) hv⟩
  have hcomp : ∀ (Y : Subrepresentation (matRep (baseF ρ₀))) {c d : Fin 2 → Bool},
      Representation.Equiv Y.toRepresentation (matRep (tensorRep (F := F4) F4 c d)) →
      Nonempty (Representation.Equiv (ofY Y).toRepresentation
        (matRep (tensorRep (F := F4) F4 d c))) := by
    intro Y c d e
    obtain ⟨e₂⟩ := nonempty_equiv_tensorRep_gam c d
    refine ⟨(Representation.Equiv.mk e.toLinearEquiv (fun g => ?_)).trans e₂⟩
    exact e.isIntertwining' (gamSL g)
  exact ⟨ofY Y, ofY Y', hcomp Y eY, hcomp Y' eY'⟩

theorem hirr_comp {G : Type} [Group G] (ρ₀ : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) (α : G →* G)
    (hα : Function.Surjective α) :
    ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, ((ρ₀.comp α) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro N hN
  refine hirr N fun g v hv => ?_
  obtain ⟨h, rfl⟩ := hα g
  exact hN h v hv

theorem gamSL_surjective : Function.Surjective gamSL := by
  intro g
  obtain ⟨h, rfl⟩ := (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F4
    w0GLb).surjective g
  obtain ⟨h', rfl⟩ := tauSL_surjective (F := F4) h
  exact ⟨h', rfl⟩

theorem exists_ne_one_of_hirr {G : Type} [Group G] (ρ₀ : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hn : 2 ≤ n)
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) : ∃ g, ρ₀ g ≠ 1 := by
  by_contra h
  push Not at h
  let e : Fin n → ZMod 2 := Pi.single ⟨0, by omega⟩ 1
  rcases hirr (Submodule.span (ZMod 2) {e}) (fun g v hv => by
    rw [h g, Matrix.one_mulVec]
    exact hv) with h0 | h1
  · have he : e ∈ Submodule.span (ZMod 2) {e} := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at he
    have := congrFun he ⟨0, by omega⟩
    simp [e] at this
  · have he' : (Pi.single ⟨1, by omega⟩ 1 : Fin n → ZMod 2) ∈ Submodule.span (ZMod 2) {e} := by
      rw [h1]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he'
    have := congrFun ha ⟨1, by omega⟩
    simp [e] at this

section Wn

open CFSG.Quasithin.H.Mathieu

variable {k : ℕ}

@[expose] def autLin : MulAut (Wn k) →* Module.End (ZMod 2) (Fin k → ZMod 2) where
  toFun φ :=
    { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
      map_add' := fun v w => by rw [ofAdd_add, map_mul, toAdd_mul]
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul,
          Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow, toAdd_pow] }
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

@[expose] def autMat : MulAut (Wn k) →* Matrix (Fin k) (Fin k) (ZMod 2) where
  toFun φ := LinearMap.toMatrix' (autLin φ)
  map_one' := by rw [map_one, Module.End.one_eq_id, LinearMap.toMatrix'_id]
  map_mul' φ ψ := by rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]

theorem autMat_mulVec (φ : MulAut (Wn k)) (v : Fin k → ZMod 2) :
    (autMat φ).mulVec v = Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := by
  show (LinearMap.toMatrix' (autLin φ)).mulVec v = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem autMat_injective : Function.Injective (autMat (k := k)) := by
  intro φ ψ h
  refine MulEquiv.ext fun w => ?_
  have h1 := congrArg (fun M => M.mulVec (Multiplicative.toAdd w)) h
  simp only [autMat_mulVec, ofAdd_toAdd] at h1
  exact Multiplicative.toAdd.injective h1

theorem exists_fixed_mem_two {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (ρ : P →* Module.End (ZMod 2) (Fin k → ZMod 2)) (N : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hN : ∀ p, ∀ w ∈ N, ρ p w ∈ N) (hne : N ≠ ⊥) : ∃ w ∈ N, w ≠ 0 ∧ ∀ p, ρ p w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : AddSubgroup (Fin k → ZMod 2) := N.toAddSubgroup
  have hA : ∀ p, ∀ w ∈ A, ρ p w ∈ A := hN
  let φ : P →* Equiv.Perm A :=
    { toFun := fun p =>
        { toFun := fun x => ⟨ρ p x, hA p x x.2⟩
          invFun := fun x => ⟨ρ p⁻¹ x, hA p⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (by
            show ρ p⁻¹ (ρ p x) = x
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
          right_inv := fun x => Subtype.ext (by
            show ρ p (ρ p⁻¹ x) = x
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]) }
      map_one' := Equiv.ext fun x => Subtype.ext (by
        show ρ 1 x = x
        rw [map_one, Module.End.one_apply])
      map_mul' := fun p q => Equiv.ext fun x => Subtype.ext (by
        show ρ (p * q) x = ρ p (ρ q x)
        rw [map_mul, Module.End.mul_apply]) }
  let _ : MulAction P A := MulAction.compHom A φ
  obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvA : v ∈ A := hvN
  have h2 : 2 ∣ Nat.card A := by
    have hord : addOrderOf (⟨v, hvA⟩ : A) = 2 := by
      refine addOrderOf_eq_prime ?_ ?_
      · refine Subtype.ext ?_
        show (2 : ℕ) • v = 0
        funext i
        rw [Pi.smul_apply, two_nsmul, Pi.zero_apply]
        exact CharTwo.add_self_eq_zero (v i)
      · intro h
        exact hv0 (by simpa using congrArg Subtype.val h)
    have := addOrderOf_dvd_natCard (⟨v, hvA⟩ : A)
    rwa [hord] at this
  have hfix0 : (0 : A) ∈ MulAction.fixedPoints P A := by
    intro p
    exact Subtype.ext (map_zero (ρ p))
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point A h2 hfix0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun p => ?_⟩
  exact congrArg Subtype.val (hb p)

theorem hirr_of_fix {G : Type} [Group G] (σ : G →* MulAut (Wn k)) (P : Subgroup G) [Finite P]
    (hP : IsPGroup 2 P)
    (hgen : ∀ w : Wn k, w ≠ 1 → (∀ p ∈ P, σ p w = w) →
      Subgroup.closure {x | ∃ g, σ g w = x} = ⊤) :
    ∀ N : Submodule (ZMod 2) (Fin k → ZMod 2),
      (∀ g, ∀ v ∈ N, ((autMat.comp σ) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro N hN
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  right
  let ρ : P →* Module.End (ZMod 2) (Fin k → ZMod 2) := autLin.comp (σ.comp P.subtype)
  have hρN : ∀ p, ∀ w ∈ N, ρ p w ∈ N := fun p w hw => by
    have h1 := hN p w hw
    rw [MonoidHom.comp_apply, autMat_mulVec] at h1
    exact h1
  obtain ⟨w, hwN, hw0, hwfix⟩ := exists_fixed_mem_two hP ρ N hρN hN0
  have hw1 : Multiplicative.ofAdd w ≠ (1 : Wn k) := fun h =>
    hw0 (by simpa using congrArg Multiplicative.toAdd h)
  have hfix : ∀ p ∈ P, σ p (Multiplicative.ofAdd w) = Multiplicative.ofAdd w := fun p hp =>
    congrArg Multiplicative.ofAdd (hwfix ⟨p, hp⟩)
  have htop := hgen _ hw1 hfix
  let NS : Subgroup (Wn k) :=
    { carrier := {x | Multiplicative.toAdd x ∈ N}
      mul_mem' := fun {x y} hx hy => by
        show Multiplicative.toAdd (x * y) ∈ N
        rw [toAdd_mul]
        exact N.add_mem hx hy
      one_mem' := by
        show Multiplicative.toAdd (1 : Wn k) ∈ N
        rw [toAdd_one]
        exact N.zero_mem
      inv_mem' := fun {x} hx => by
        show Multiplicative.toAdd x⁻¹ ∈ N
        rw [toAdd_inv]
        exact N.neg_mem hx }
  have hle : Subgroup.closure {x | ∃ g, σ g (Multiplicative.ofAdd w) = x} ≤ NS := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    have h1 := hN g w hwN
    rw [MonoidHom.comp_apply, autMat_mulVec] at h1
    exact h1
  rw [htop] at hle
  rw [eq_top_iff]
  intro v _
  exact hle (Subgroup.mem_top (Multiplicative.ofAdd v))

end Wn

end CFSG.Quasithin.L34Bin
