module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.RankThree.PartTwo.Census.CommonUnipotent
public import CFSG.RankThree.Classical.SiegelRadical
import CFSG.RankThree.PartTwo.Census.QuotientWitness
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.RankThree.Classical
  Matrix

variable {K : Type} [Field K] {r : ℕ}

@[expose] def planeSign (r : ℕ) (K : Type) [Field K] : Fin r → Kˣ :=
  fun i => if i.val = 0 then -1 else 1

theorem planeSign_mul_self (i : Fin r) : planeSign r K i * planeSign r K i = 1 := by
  simp only [planeSign]
  split_ifs <;> simp

theorem planeSign_inv (i : Fin r) : (planeSign r K i)⁻¹ = planeSign r K i :=
  inv_eq_of_mul_eq_one_right (planeSign_mul_self i)

@[expose] noncomputable def planeInvolution (r : ℕ) (K : Type) [Field K] : StatedSp r K :=
  ⟨torusGL (planeSign r K), torusGL_mem_statedSp _⟩

theorem coe_planeInvolution :
    (((planeInvolution r K : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks (diagonal fun i => (planeSign r K i : K)) 0 0
        (diagonal fun i => (planeSign r K i : K)) := by
  rw [planeInvolution, coe_torusGL]
  simp only [planeSign_inv]

theorem planeInvolution_sq : planeInvolution r K ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_planeInvolution, fromBlocks_multiply,
    diagonal_mul_diagonal]
  simp only [← Units.val_mul, planeSign_mul_self, Units.val_one, diagonal_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  exact fromBlocks_one

theorem planeInvolution_not_mem (h2 : (2 : K) ≠ 0) (hr : 2 ≤ r) :
    planeInvolution r K ∉ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) := by
  rintro ⟨u, hu⟩
  have hu' := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
    (Fin r ⊕ Fin r) K)) hu
  change Matrix.scalar _ (u : K) = (((planeInvolution r K : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) at hu'
  rw [coe_planeInvolution] at hu'
  have e0 : (u : K) = -1 := by
    simpa [planeSign] using congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K =>
      M (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) hu'
  have e1 : (u : K) = 1 := by
    simpa [planeSign] using congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K =>
      M (Sum.inl ⟨1, by omega⟩) (Sum.inl ⟨1, by omega⟩)) hu'
  apply h2
  linear_combination e0 - e1

theorem le_localRank_PSp_of_symm [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (hr : 2 ≤ r) {W : Type} [AddCommGroup W]
    (S : W →+ Matrix (Fin r) (Fin r) K) (hS : Function.Injective S) (hsym : ∀ w, (S w)ᵀ = S w)
    (hsupp : ∀ w (i j : Fin r), S w i j ≠ 0 → (i.val = 0 ↔ j.val = 0)) {k : ℕ}
    (hW : Nat.card W = p ^ k) : k ≤ localRank p (StatedProj (StatedSp r K)) := by
  have hp : p.Prime := Fact.out
  let φ : Multiplicative W →* StatedSp r K :=
    { toFun := fun w => ⟨siegelGL (S w.toAdd), siegelGL_mem_statedSp (hsym _)⟩
      map_one' := Subtype.ext (by
        change siegelGL (S (Multiplicative.toAdd 1)) = 1
        rw [toAdd_one, map_zero, siegelGL_zero])
      map_mul' := fun a b => Subtype.ext (by
        change siegelGL (S (Multiplicative.toAdd (a * b))) =
          siegelGL (S (Multiplicative.toAdd a)) * siegelGL (S (Multiplicative.toAdd b))
        rw [toAdd_mul, map_add, siegelGL_add]) }
  have hφ : Function.Injective φ := by
    intro a b h
    have h' := congrArg (fun g : StatedSp r K => ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
    exact Multiplicative.toAdd.injective (hS (siegelMat_injective h'))
  have hWp : ∀ w : W, p • w = 0 := fun w => hS (by
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul])
  refine le_localRank_quotient_of_commute _ hp (isElemAbelian_range_of_nsmul hWp φ)
    (by rw [card_range_of_injective hφ, hW]) ?_ (planeInvolution_not_mem h2 hr)
    (by rw [planeInvolution_sq]; exact Subgroup.one_mem _) ?_
  · rw [eq_bot_iff]
    rintro x hx
    obtain ⟨⟨w, rfl⟩, ⟨u, hu⟩⟩ := Subgroup.mem_inf.mp hx
    have hu' := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K)) hu
    change Matrix.scalar _ (u : K) = siegelMat (S w.toAdd) at hu'
    have e0 := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K =>
      M (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) hu'
    simp [siegelMat] at e0
    rw [e0, Units.val_one, map_one, ← siegelMat_zero] at hu'
    have hw : w = 1 := Multiplicative.toAdd.injective
      (hS ((siegelMat_injective hu').symm.trans (map_zero S).symm))
    rw [hw, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨w, rfl⟩
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_planeInvolution]
    change siegelMat (S w.toAdd) * _ = _ * siegelMat (S w.toAdd)
    rw [siegelMat, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]
    congr 1
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases hij : S w.toAdd i j = 0
    · simp [hij]
    · have := hsupp w.toAdd i j hij
      simp only [planeSign]
      by_cases hi : i.val = 0
      · rw [ite_eq_left hi, ite_eq_left (this.mp hi)]
        ring
      · rw [ite_eq_right hi, ite_eq_right (fun h => hi (this.mpr h))]
        ring

@[expose] def siegelPlaneMap (r : ℕ) (K : Type) [Field K] (i j : Fin r) :
    (Fin r → K) × K →+ Matrix (Fin r) (Fin r) K where
  toFun w := Matrix.of fun k l =>
    if k = l then w.1 k else if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then w.2 else 0
  map_zero' := by
    ext k l
    simp
  map_add' a b := by
    ext k l
    simp only [of_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp

theorem siegelPlaneMap_apply (i j : Fin r) (w : (Fin r → K) × K) (k l : Fin r) :
    siegelPlaneMap r K i j w k l =
      if k = l then w.1 k else if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then w.2 else 0 :=
  rfl

theorem le_localRank_PSp [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hr : 3 ≤ r) :
    f * (r + 1) ≤ localRank p (StatedProj (StatedSp r K)) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set i : Fin r := ⟨1, by omega⟩
  set j : Fin r := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  refine le_localRank_PSp_of_symm h2 (by omega) (siegelPlaneMap r K i j) ?_ ?_ ?_ ?_
  · intro a b h
    have hd : ∀ k, a.1 k = b.1 k := fun k => by
      have := congrArg (fun M : Matrix (Fin r) (Fin r) K => M k k) h
      simpa [siegelPlaneMap_apply] using this
    have hb : a.2 = b.2 := by
      have := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j) h
      simpa [siegelPlaneMap_apply, hij] using this
    exact Prod.ext (funext hd) hb
  · intro w
    ext k l
    rw [transpose_apply, siegelPlaneMap_apply, siegelPlaneMap_apply]
    by_cases hkl : k = l
    · subst hkl
      rfl
    · rw [ite_eq_right (Ne.symm hkl), ite_eq_right hkl]
      congr 1
      apply propext
      tauto
  · intro w k l hkl
    rw [siegelPlaneMap_apply] at hkl
    by_cases h : k = l
    · rw [h]
    · rw [ite_eq_right h] at hkl
      have hc : (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
        by_contra hc
        exact hkl (ite_eq_right hc)
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [i, j]
  · rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hK, ← pow_mul, ← pow_add]
    ring_nf

theorem four_le_localRank_PSp [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (hr : 3 ≤ r) :
    4 ≤ localRank p (StatedProj (StatedSp r K)) := by
  have := le_localRank_PSp hp2 hK hr
  nlinarith

theorem excluded433_C (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    Excluded433 (.lie ⟨.C r q, hv⟩) := by
  intro G _ _ hG e
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_C r q
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C r q, hv⟩
  refine hG.false_of_four_le_localRank
    (p := TauCeti.ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩)
    (e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)) Fact.out
    (by rw [hc]; exact hrange.2)
    (four_le_localRank_PSp (f := q.exponent) (by rw [hc]; exact hrange.2) ?_ q.exponent_pos
      hrange.1)
  rw [TauCeti.ValidLieTypeIndex.card_fixedField, hc]
  simp [TauCeti.ValidLieTypeIndex.fieldOrder]

theorem le_localRank_PSp_two [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : 2 * f ≤ localRank p (StatedProj (StatedSp 2 K)) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  refine le_localRank_PSp_of_symm h2 le_rfl (diagonalAddMonoidHom (Fin 2) K)
    (fun a b h => diagonal_injective h) (fun w => diagonal_transpose w) ?_ ?_
  · intro w k l hkl
    by_cases h : k = l
    · rw [h]
    · exact absurd (diagonal_apply_ne _ h) hkl
  · rw [Nat.card_fun, Nat.card_fin, hK, ← pow_mul, mul_comm]

theorem excluded433_B2_odd_of_two_le (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) (hq : q.p ≠ 2) (hf : 2 ≤ q.exponent) :
    Excluded433 (.lie ⟨.B 2 q, hv⟩) := by
  intro G _ _ hG e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_B 2 q
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  refine hG.false_of_four_le_localRank
    (p := TauCeti.ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩)
    (e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)) Fact.out
    (by rw [hc]; exact hq) ?_
  have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_B 2 q
  have := le_localRank_PSp_two (p := TauCeti.ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩)
    (f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩)
    (K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)) (by rw [hc]; exact hq) (by
      rw [TauCeti.ValidLieTypeIndex.card_fixedField,
        TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow])
  rw [he] at this
  omega

end CFSG.RankThree.PartTwo.Census
