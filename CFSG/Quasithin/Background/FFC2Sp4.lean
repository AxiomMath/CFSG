module

public import CFSG.Quasithin.Background.B4L3Coord

public section

open Matrix CFSG.Assembly.LowTwoRank

namespace CFSG.Quasithin.FFC

abbrev Jm (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := Matrix.fromBlocks 0 1 (-1) 0

def tvm {K : Type} [Field K] (v : Fin 2 ⊕ Fin 2 → K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  1 + Matrix.vecMulVec v ((Jm K).mulVec v)

def Msym (a b c d e f : ZMod 2) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Matrix.fromBlocks !![0, a; a, 0] !![b, c; d, e] !![b, d; c, e] !![0, f; f, 0]

set_option maxRecDepth 100000 in
theorem tvm_sq_zmod : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, tvm v * tvm v = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem tvm_symp_zmod :
    ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, (tvm v)ᵀ * Jm (ZMod 2) * tvm v = Jm (ZMod 2) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem forms_unique_msym : ∀ a b c d e f : ZMod 2,
    (∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, (tvm v)ᵀ * Msym a b c d e f * tvm v = Msym a b c d e f) →
    Msym a b c d e f = 0 ∨ Msym a b c d e f = Jm (ZMod 2) := by
  decide +kernel

theorem exists_msym (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) (hsym : Mᵀ = M)
    (hdiag : ∀ i, M i i = 0) : ∃ a b c d e f, M = Msym a b c d e f := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hsym i) j
    simpa [Matrix.transpose_apply] using this
  refine ⟨M (Sum.inl 0) (Sum.inl 1), M (Sum.inl 0) (Sum.inr 0), M (Sum.inl 0) (Sum.inr 1),
    M (Sum.inl 1) (Sum.inr 0), M (Sum.inl 1) (Sum.inr 1), M (Sum.inr 0) (Sum.inr 1), ?_⟩
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Msym, Matrix.fromBlocks, hdiag, hs]

theorem forms_unique_zmod : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2),
    Mᵀ = M → (∀ i, M i i = 0) →
    (∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, (tvm v)ᵀ * M * tvm v = M) → M = 0 ∨ M = Jm (ZMod 2) := by
  intro M hsym hdiag hinv
  obtain ⟨a, b, c, d, e, f, rfl⟩ := exists_msym M hsym hdiag
  exact forms_unique_msym a b c d e f hinv

section KLevel

variable {K : Type} [Field K] [Finite K]

noncomputable def ringEquivZMod2 (hK : Nat.card K = 2) : K ≃+* ZMod 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm

omit [Finite K] in
theorem map_Jm (c : K ≃+* ZMod 2) : (Jm K).map c = Jm (ZMod 2) := by
  have h : (-1 : Matrix (Fin 2) (Fin 2) K).map c = -1 := by
    have := map_neg (RingHom.mapMatrix (m := Fin 2) c.toRingHom) (1 : Matrix (Fin 2) (Fin 2) K)
    rw [map_one] at this
    exact this
  unfold Jm
  rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), Matrix.map_one _ (map_zero c) (map_one c), h]
  rfl

omit [Finite K] in
theorem map_tvm (c : K ≃+* ZMod 2) (v : Fin 2 ⊕ Fin 2 → K) :
    (tvm v).map c = tvm (fun i => c (v i)) := by
  have h1 : (fun i => c (((Jm K).mulVec v) i)) = (Jm (ZMod 2)).mulVec (fun i => c (v i)) := by
    funext i
    rw [← map_Jm c]
    exact RingHom.map_mulVec c.toRingHom (Jm K) v i
  have h2 : (Matrix.vecMulVec v ((Jm K).mulVec v)).map c =
      Matrix.vecMulVec (fun i => c (v i)) ((Jm (ZMod 2)).mulVec (fun i => c (v i))) := by
    rw [← h1]
    ext i j
    simp [Matrix.vecMulVec]
  unfold tvm
  rw [Matrix.map_add c (map_add c), Matrix.map_one _ (map_zero c) (map_one c), h2]


theorem tvm_sq (hK : Nat.card K = 2) (v : Fin 2 ⊕ Fin 2 → K) : tvm v * tvm v = 1 := by
  let c := ringEquivZMod2 hK
  have hφ : Function.Injective (RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom) :=
    Matrix.map_injective c.injective
  apply hφ
  rw [map_mul, map_one]
  have e : RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom (tvm v) = tvm (fun i => c (v i)) :=
    map_tvm c v
  rw [e]
  exact tvm_sq_zmod _

theorem tvm_symp (hK : Nat.card K = 2) (v : Fin 2 ⊕ Fin 2 → K) :
    (tvm v)ᵀ * Jm K * tvm v = Jm K := by
  let c := ringEquivZMod2 hK
  have hφ : Function.Injective (RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom) :=
    Matrix.map_injective c.injective
  apply hφ
  have e : RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom (tvm v) = tvm (fun i => c (v i)) :=
    map_tvm c v
  have eJ : RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom (Jm K) = Jm (ZMod 2) := map_Jm c
  have eT : RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom (tvm v)ᵀ =
      (tvm (fun i => c (v i)))ᵀ := by
    rw [← e]
    ext i j
    rfl
  rw [map_mul, map_mul, eT, eJ, e]
  exact tvm_symp_zmod _


theorem forms_unique (hK : Nat.card K = 2) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hsym : Mᵀ = M) (hdiag : ∀ i, M i i = 0)
    (hinv : ∀ v : Fin 2 ⊕ Fin 2 → K, (tvm v)ᵀ * M * tvm v = M) : M = 0 ∨ M = Jm K := by
  let c := ringEquivZMod2 hK
  let φ := RingHom.mapMatrix (m := Fin 2 ⊕ Fin 2) c.toRingHom
  have hφ : Function.Injective φ := Matrix.map_injective c.injective
  have hφT : ∀ N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, φ Nᵀ = (φ N)ᵀ := fun N => by
    ext i j
    rfl
  have h := forms_unique_zmod (φ M) (by rw [← hφT, hsym]) (fun i => by
    show c (M i i) = 0
    rw [hdiag, map_zero]) (fun v' => by
    have e : φ (tvm (fun i => c.symm (v' i))) = tvm v' := by
      have := map_tvm c (fun i => c.symm (v' i))
      simp only [RingEquiv.apply_symm_apply] at this
      exact this
    have := congrArg φ (hinv (fun i => c.symm (v' i)))
    rwa [map_mul, map_mul, hφT, e] at this)
  have hJ : φ (Jm K) = Jm (ZMod 2) := map_Jm c
  rcases h with h | h
  · left
    apply hφ
    rw [h, map_zero]
  · right
    apply hφ
    rw [h, hJ]

omit [Finite K] in
theorem mem_statedSp_iff' (A : GL (Fin 2 ⊕ Fin 2) K) :
    A ∈ StatedSp 2 K ↔ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * Jm K *
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Jm K :=
  CFSG.Open.StatedAPI.mem_statedSp_iff


theorem neg_eq_self_of_card_two (hK : Nat.card K = 2) (x : K) : -x = x := by
  let c := ringEquivZMod2 hK
  apply c.injective
  rw [map_neg]
  generalize c x = y
  revert y
  decide

theorem Jm_transpose (hK : Nat.card K = 2) : (Jm K)ᵀ = Jm K := by
  have h : (-1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    simp [Matrix.neg_apply, neg_eq_self_of_card_two hK]
  unfold Jm
  rw [Matrix.fromBlocks_transpose]
  simp [h]

omit [Finite K] in
theorem dotProduct_Jm_mulVec (x : Fin 2 ⊕ Fin 2 → K) : x ⬝ᵥ (Jm K *ᵥ x) = 0 := by
  have hx : x = Sum.elim (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) := by
    funext i
    cases i <;> rfl
  rw [hx, Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]
  ring


def tvGL (hK : Nat.card K = 2) (v : Fin 2 ⊕ Fin 2 → K) : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨tvm v, tvm v, tvm_sq hK v, tvm_sq hK v⟩

theorem tvGL_mem (hK : Nat.card K = 2) (v : Fin 2 ⊕ Fin 2 → K) : tvGL hK v ∈ StatedSp 2 K :=
  (mem_statedSp_iff' _).2 (tvm_symp hK v)

theorem mem_statedSp_of_normalizes (hK : Nat.card K = 2) (g : GL (Fin 2 ⊕ Fin 2) K)
    (hg : ∀ γ ∈ StatedSp 2 K, g * γ * g⁻¹ ∈ StatedSp 2 K) : g ∈ StatedSp 2 K := by
  set gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    with hgm
  set gi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hgi
  have h1 : gi * gm = 1 := Units.inv_mul g
  have h2 : gm * gi = 1 := Units.mul_inv g
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := gmᵀ * Jm K * gm with hM
  have hsym : Mᵀ = M := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Jm_transpose hK, Matrix.mul_assoc]
  have hdiag : ∀ i, M i i = 0 := by
    intro i
    have := dotProduct_Jm_mulVec (K := K) (fun k => gm k i)
    simp [hM, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at this ⊢
    linear_combination this
  have hinv : ∀ v : Fin 2 ⊕ Fin 2 → K, (tvm v)ᵀ * M * tvm v = M := by
    intro v
    have hmem := (mem_statedSp_iff' _).1 (hg _ (tvGL_mem hK v))
    rw [Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.transpose_mul] at hmem
    have e : (tvGL hK v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = tvm v := rfl
    rw [e, ← hgm, ← hgi] at hmem
    calc (tvm v)ᵀ * M * tvm v
        = gmᵀ * (giᵀ * (tvm v)ᵀ * gmᵀ * Jm K * gm * tvm v * gi) * gm := by
          have h3 : gmᵀ * giᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
          rw [hM]
          calc (tvm v)ᵀ * (gmᵀ * Jm K * gm) * tvm v
              = (gmᵀ * giᵀ) * (tvm v)ᵀ * gmᵀ * Jm K * gm * tvm v * (gi * gm) := by
                rw [h3, h1]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
            _ = gmᵀ * (giᵀ * (tvm v)ᵀ * gmᵀ * Jm K * gm * tvm v * gi) * gm := by
                simp only [Matrix.mul_assoc]
      _ = gmᵀ * ((gi)ᵀ * (tvm v)ᵀ * gmᵀ * Jm K * (gm * tvm v * gi)) * gm := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          have : giᵀ * (tvm v)ᵀ * gmᵀ * Jm K * (gm * tvm v * gi) = Jm K := by
            simpa only [Matrix.mul_assoc] using hmem
          rw [this, hM]
  rcases forms_unique hK M hsym hdiag hinv with h0 | hJ
  · exfalso
    have : Jm K = 0 := by
      calc Jm K = giᵀ * M * gi := by
            rw [hM]
            calc Jm K = (giᵀ * gmᵀ) * Jm K * (gm * gi) := by
                  rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]; simp
              _ = giᵀ * (gmᵀ * Jm K * gm) * gi := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [h0]; simp
    have h3 := congrFun (congrFun this (Sum.inl 0)) (Sum.inr 0)
    simp [Jm] at h3
  · exact (mem_statedSp_iff' g).2 hJ

end KLevel


section Assembly

variable {V : Type} [CommGroup V] {K : Type} [Field K] [Finite K]

@[expose] noncomputable def glLin : GL (Fin 2 ⊕ Fin 2) K ≃* ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 ⊕ Fin 2 → K))

omit [Finite K] in
theorem glLin_apply (A : GL (Fin 2 ⊕ Fin 2) K) (x : Fin 2 ⊕ Fin 2 → K) :
    glLin A x = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).mulVec x := rfl


theorem eq_zero_or_one_of_card_two' (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  let c := ringEquivZMod2 hK
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h (c x) with h0 | h1
  · left
    exact c.injective (by rw [h0, map_zero])
  · right
    exact c.injective (by rw [h1, map_one])

theorem le_of_binaryNaturalSp4_one {G H : Subgroup (MulAut V)}
    (hHn : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (h : BinaryNaturalSp4 H ⊤ ⊥ 1) : G ≤ H := by
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := h
  have hK : Nat.card K = 2 := by simpa using hKc
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSp 2 K)) rfl rfl hπ
  let cβ : V → (Fin 2 ⊕ Fin 2 → K) := fun u => Multiplicative.toAdd (β ⟨u, trivial⟩)
  have hcβ_mul : ∀ u w : V, cβ (u * w) = cβ u + cβ w := fun u w => by
    show Multiplicative.toAdd (β ⟨u * w, trivial⟩) = _
    have : (⟨u * w, trivial⟩ : ↥(⊤ : Subgroup V)) = ⟨u, trivial⟩ * ⟨w, trivial⟩ := rfl
    rw [this, map_mul]
    rfl
  have hcβ_inj : Function.Injective cβ := by
    intro u w huw
    have h1 : β ⟨u, trivial⟩ = β ⟨w, trivial⟩ := by
      apply Multiplicative.toAdd.injective
      exact huw
    have h2 : β (⟨u, trivial⟩ * ⟨w, trivial⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hβk _).1 h2
    rw [Subgroup.mem_bot] at h3
    have : u * w⁻¹ = 1 := h3
    exact mul_inv_eq_one.1 this
  have hcβ_surj : Function.Surjective cβ := by
    intro x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    refine ⟨u.1, ?_⟩
    show Multiplicative.toAdd (β ⟨u.1, trivial⟩) = x
    have h1 : β ⟨u.1, trivial⟩ = Multiplicative.ofAdd x := hu
    rw [h1]
    rfl
  have hcβ_eq : ∀ (γ : ↥(StatedSp 2 K)) (u : V),
      cβ ((π γ : MulAut V) u) = ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).mulVec (cβ u) := by
    intro γ u
    have := hβe γ ⟨u, trivial⟩ trivial
    exact congrArg Multiplicative.toAdd this
  intro g hg
  let eβ : V ≃ (Fin 2 ⊕ Fin 2 → K) := Equiv.ofBijective cβ ⟨hcβ_inj, hcβ_surj⟩
  have heβ : ∀ u, eβ u = cβ u := fun u => rfl
  have hs : ∀ u, eβ.symm (cβ u) = u := fun u => eβ.symm_apply_apply u
  let ê : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K) :=
    { toEquiv := eβ.symm.trans ((g : V ≃* V).toEquiv.trans eβ)
      map_add' := fun x y => by
        obtain ⟨u, rfl⟩ := hcβ_surj x
        obtain ⟨w, rfl⟩ := hcβ_surj y
        show eβ (g (eβ.symm (cβ u + cβ w))) = eβ (g (eβ.symm (cβ u))) + eβ (g (eβ.symm (cβ w)))
        rw [← hcβ_mul, hs, hs, hs, map_mul, heβ, heβ, heβ, hcβ_mul] }
  have hê : ∀ u, ê (cβ u) = cβ (g u) := fun u => by
    show eβ (g (eβ.symm (cβ u))) = cβ (g u)
    rw [hs]
    rfl
  have hlin : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), ê (c • x) = c • ê x := by
    intro c x
    rcases eq_zero_or_one_of_card_two' hK c with rfl | rfl
    · simp
    · simp
  let ĝ : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) := ê.toLinearEquiv hlin
  have hĝ : ∀ u, ĝ (cβ u) = cβ (g u) := hê
  let A : GL (Fin 2 ⊕ Fin 2) K := glLin.symm ĝ
  have hAĝ : ∀ x, glLin A x = ĝ x := fun x => by
    show (glLin (glLin.symm ĝ)) x = ĝ x
    rw [MulEquiv.apply_symm_apply]
  have hĝsymm : ∀ u, ĝ.symm (cβ u) = cβ (g⁻¹ u) := fun u => by
    rw [LinearEquiv.symm_apply_eq, hĝ]
    congr 1
    exact (by simp : g (g⁻¹ u) = u).symm
  have hnorm : ∀ γ ∈ StatedSp 2 K, A * γ * A⁻¹ ∈ StatedSp 2 K := by
    intro γ hγ
    have h1 : g * (π ⟨γ, hγ⟩ : MulAut V) * g⁻¹ ∈ H := hHn g hg _ (π ⟨γ, hγ⟩).2
    obtain ⟨γ'', hγ''⟩ := hπ.1 ⟨_, h1⟩
    have hγ''2 : ((π γ'' : ↥H) : MulAut V) = g * (π ⟨γ, hγ⟩ : MulAut V) * g⁻¹ :=
      congrArg Subtype.val hγ''
    have : A * γ * A⁻¹ = (show ↥(StatedSp 2 K) from γ'').1 := by
      apply glLin.injective
      apply LinearEquiv.ext
      intro x
      obtain ⟨u, rfl⟩ := hcβ_surj x
      have hAĝ' : glLin A = ĝ := LinearEquiv.ext hAĝ
      rw [map_mul, map_mul, map_inv, hAĝ']
      show ĝ (glLin γ (ĝ.symm (cβ u))) = glLin (show ↥(StatedSp 2 K) from γ'').1 (cβ u)
      rw [hĝsymm, glLin_apply, glLin_apply, ← hcβ_eq ⟨γ, hγ⟩ (g⁻¹ u), hĝ,
        ← hcβ_eq (show ↥(StatedSp 2 K) from γ'') u, hγ''2]
      rfl
    rw [this]
    exact (show ↥(StatedSp 2 K) from γ'').2
  have hAmem : A ∈ StatedSp 2 K := mem_statedSp_of_normalizes hK A hnorm
  have hgA : g = (π ⟨A, hAmem⟩ : MulAut V) := by
    apply MulEquiv.ext
    intro u
    apply hcβ_inj
    rw [hcβ_eq, ← hĝ, ← hAĝ]
    rfl
  rw [hgA]
  exact (π ⟨A, hAmem⟩).2

end Assembly

end CFSG.Quasithin.FFC
