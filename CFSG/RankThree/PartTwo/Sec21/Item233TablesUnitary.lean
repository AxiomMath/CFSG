module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSymplectic
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Tables

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K] {e k n : ℕ} {f : Fin k → Fin n}

@[expose] def embedMatU (f : Fin k → Fin n) (g : Matrix (Fin k) (Fin k) K) :
    Matrix (Fin n) (Fin n) K :=
  1 + inclMat (K := K) f * (g - 1) * (inclMat (K := K) f)ᵀ

theorem embedMatU_one : embedMatU f (1 : Matrix (Fin k) (Fin k) K) = 1 := by
  simp [embedMatU]

theorem embedMatU_mul (hf : Function.Injective f) (g h : Matrix (Fin k) (Fin k) K) :
    embedMatU f (g * h) = embedMatU f g * embedMatU f h := by
  simp only [embedMatU]
  set P := inclMat (K := K) f
  have hPP : Pᵀ * P = 1 := inclMat_transpose_mul hf
  have e1 : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  have e2 : P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * ((g - 1) * (h - 1)) * Pᵀ := by
    calc P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * (g - 1) * (Pᵀ * P) * (h - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P * ((g - 1) * (h - 1)) * Pᵀ := by
          rw [hPP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : P * (g * h - 1) * Pᵀ = P * (g - 1) * Pᵀ + P * (h - 1) * Pᵀ +
      P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) := by
    rw [e2, e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [e3]
  noncomm_ring

theorem det_embedMatU (hf : Function.Injective f) (g : Matrix (Fin k) (Fin k) K) :
    (embedMatU f g).det = g.det := by
  rw [embedMatU, Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc,
    inclMat_transpose_mul hf, Matrix.mul_one, add_sub_cancel]

theorem embedMatU_transpose (g : Matrix (Fin k) (Fin k) K) :
    (embedMatU f g)ᵀ = embedMatU f gᵀ := by
  rw [embedMatU, embedMatU, transpose_add, transpose_one, transpose_mul, transpose_mul,
    transpose_transpose, transpose_sub, transpose_one, Matrix.mul_assoc]

@[expose] def embedGLU (hf : Function.Injective f) : GL (Fin k) K →* GL (Fin n) K where
  toFun g :=
    { val := embedMatU f (g : Matrix (Fin k) (Fin k) K)
      inv := embedMatU f ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
      val_inv := by rw [← embedMatU_mul hf, Units.mul_inv, embedMatU_one]
      inv_val := by rw [← embedMatU_mul hf, Units.inv_mul, embedMatU_one] }
  map_one' := Units.ext embedMatU_one
  map_mul' g h := Units.ext (embedMatU_mul hf (g : Matrix (Fin k) (Fin k) K) h)

theorem inclMat_apply (a : Fin n) (b : Fin k) :
    inclMat (K := K) f a b = if a = f b then 1 else 0 := rfl

theorem inclMat_mul_transpose_apply_of_mem (hf : Function.Injective f) {a : Fin n}
    (ha : a ∈ Set.range f) (b : Fin n) :
    (inclMat (K := K) f * (inclMat (K := K) f)ᵀ) a b = (1 : Matrix _ _ K) a b := by
  rw [Matrix.mul_apply]
  simp_rw [transpose_apply, inclMat_apply, ite_mul, one_mul, zero_mul]
  obtain ⟨c, rfl⟩ := ha
  rw [Finset.sum_eq_single c]
  · by_cases hb : f c = b
    · subst hb
      simp
    · simp [Ne.symm hb, Matrix.one_apply_ne hb]
  · intro d _ hdc
    have : f c ≠ f d := fun h => hdc (hf h).symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem inclMat_mul_transpose_apply_of_not_mem {a : Fin n} (ha : a ∉ Set.range f) (b : Fin n) :
    (inclMat (K := K) f * (inclMat (K := K) f)ᵀ) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have : a ≠ f c := fun h => ha ⟨c, h.symm⟩
  simp [inclMat_apply, this]

theorem inclMat_mul_transpose_apply_of_not_mem' {b : Fin n} (hb : b ∉ Set.range f) (a : Fin n) :
    (inclMat (K := K) f * (inclMat (K := K) f)ᵀ) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have : b ≠ f c := fun h => hb ⟨c, h.symm⟩
  simp [inclMat_apply, this]

theorem projQU_mul_of_supp (hf : Function.Injective f) {N : Matrix (Fin n) (Fin n) K}
    (hN : ∀ a b, (a ∉ Set.range f ∨ b ∉ Set.range f) → N a b = 0) :
    inclMat (K := K) f * (inclMat (K := K) f)ᵀ * N = N ∧
      N * (inclMat (K := K) f * (inclMat (K := K) f)ᵀ) = N := by
  constructor
  · ext a b
    by_cases ha : a ∈ Set.range f
    · rw [Matrix.mul_apply]
      simp_rw [inclMat_mul_transpose_apply_of_mem hf ha, Matrix.one_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    · rw [Matrix.mul_apply, hN a b (Or.inl ha)]
      exact Finset.sum_eq_zero fun c _ => by
        rw [inclMat_mul_transpose_apply_of_not_mem ha, zero_mul]
  · ext a b
    by_cases hb : b ∈ Set.range f
    · rw [Matrix.mul_apply]
      have hQ : ∀ c, (inclMat (K := K) f * (inclMat (K := K) f)ᵀ) c b =
          (1 : Matrix _ _ K) c b := by
        intro c
        by_cases hc : c ∈ Set.range f
        · exact inclMat_mul_transpose_apply_of_mem hf hc b
        · rw [inclMat_mul_transpose_apply_of_not_mem hc, Matrix.one_apply_ne]
          rintro rfl
          exact hc hb
      simp_rw [hQ, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    · rw [Matrix.mul_apply, hN a b (Or.inr hb)]
      exact Finset.sum_eq_zero fun c _ => by
        rw [inclMat_mul_transpose_apply_of_not_mem' hb, mul_zero]

theorem isIdOutside_embedMatU (g : Matrix (Fin k) (Fin k) K) :
    IsIdOutside (Set.range f) (embedMatU f g) := by
  intro a b hab
  have hP : ∀ z : Fin n, z ∉ Set.range f → ∀ c, inclMat (K := K) f z c = 0 := by
    intro z hz c
    have : z ≠ f c := fun h => hz ⟨c, h.symm⟩
    simp [inclMat_apply, this]
  rw [embedMatU, Matrix.add_apply, add_eq_left]
  rcases hab with ha | hb
  · rw [Matrix.mul_assoc, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [hP a ha c, zero_mul]
  · rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [transpose_apply, hP b hb c, mul_zero]

variable [CharP K 2]

theorem inclMat_map_frob :
    (inclMat (K := K) f).map (iterateFrobenius K 2 e) = inclMat (K := K) f := by
  ext a b
  simp only [inclMat, map_apply, of_apply]
  split_ifs <;> simp

theorem embedMatU_map (g : Matrix (Fin k) (Fin k) K) :
    (embedMatU f g).map (iterateFrobenius K 2 e) =
      embedMatU f (g.map (iterateFrobenius K 2 e)) := by
  rw [embedMatU, embedMatU, Matrix.map_add _ (map_add _),
    Matrix.map_one (iterateFrobenius K 2 e) (map_zero _) (map_one _), Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one (iterateFrobenius K 2 e) (map_zero _) (map_one _), inclMat_map_frob,
    transpose_map, inclMat_map_frob]

theorem embedMatU_unitary (hf : Function.Injective f) {g : Matrix (Fin k) (Fin k) K}
    (hg : (g.map (iterateFrobenius K 2 e))ᵀ * g = 1) :
    ((embedMatU f g).map (iterateFrobenius K 2 e))ᵀ * embedMatU f g = 1 := by
  rw [embedMatU_map, embedMatU_transpose, ← embedMatU_mul hf, hg, embedMatU_one]

variable (e) in
theorem mem_statedSU_iff' (hK : Nat.card K = (2 ^ e) ^ 2) {m : ℕ} (hm : 1 ≤ m)
    (A : GL (Fin m) K) : A ∈ StatedSU m (2 ^ e) K ↔ (A : Matrix (Fin m) (Fin m) K).det = 1 ∧
      ((A : Matrix (Fin m) (Fin m) K).map (iterateFrobenius K 2 e))ᵀ *
        (A : Matrix (Fin m) (Fin m) K) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hm).1
  exact Set.ext_iff.1 h A

@[expose] def embedSU (hf : Function.Injective f) (hK : Nat.card K = (2 ^ e) ^ 2) (hk : 1 ≤ k)
    (hn : 1 ≤ n) : StatedSU k (2 ^ e) K →* StatedSU n (2 ^ e) K :=
  ((embedGLU hf).comp (StatedSU k (2 ^ e) K).subtype).codRestrict (StatedSU n (2 ^ e) K)
    fun g => by
      have hg := (mem_statedSU_iff' e hK hk g).mp g.2
      refine (mem_statedSU_iff' e hK hn _).mpr ⟨?_, ?_⟩
      · change (embedMatU f _).det = 1
        rw [det_embedMatU hf]
        exact hg.1
      · exact embedMatU_unitary hf hg.2

theorem coe_embedSU (hf : Function.Injective f) (hK : Nat.card K = (2 ^ e) ^ 2) (hk : 1 ≤ k)
    (hn : 1 ≤ n) (g : StatedSU k (2 ^ e) K) :
    (((embedSU hf hK hk hn g : StatedSU n (2 ^ e) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = embedMatU f ((g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) :=
  rfl

theorem embedSU_injective (hf : Function.Injective f) (hK : Nat.card K = (2 ^ e) ^ 2)
    (hk : 1 ≤ k) (hn : 1 ≤ n) : Function.Injective (embedSU hf hK hk hn) := by
  intro g h hgh
  have key : ∀ g : Matrix (Fin k) (Fin k) K,
      (inclMat (K := K) f)ᵀ * embedMatU f g * inclMat (K := K) f = g := by
    intro g
    have hPP := inclMat_transpose_mul (K := K) hf
    rw [embedMatU, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP]
    calc 1 + (inclMat (K := K) f)ᵀ * (inclMat (K := K) f * (g - 1) * (inclMat (K := K) f)ᵀ) *
          inclMat (K := K) f =
        1 + ((inclMat (K := K) f)ᵀ * inclMat (K := K) f) * (g - 1) *
          ((inclMat (K := K) f)ᵀ * inclMat (K := K) f) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]
  apply Subtype.ext
  apply Units.ext
  have := congrArg (fun x : StatedSU n (2 ^ e) K =>
    (inclMat (K := K) f)ᵀ * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      inclMat (K := K) f) hgh
  simp only [coe_embedSU, key] at this
  exact this

theorem isIdOutside_map_frob {c : Set (Fin n)} {X : Matrix (Fin n) (Fin n) K}
    (hX : IsIdOutside c X) : IsIdOutside c ((X.map (iterateFrobenius K 2 e))ᵀ) := by
  intro a b hab
  rw [transpose_apply, map_apply, hX b a hab.symm]
  by_cases h : b = a
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]

theorem mem_range_embedSU_iff (hf : Function.Injective f) (hK : Nat.card K = (2 ^ e) ^ 2)
    (hk : 1 ≤ k) (hn : 1 ≤ n) (x : StatedSU n (2 ^ e) K) :
    x ∈ (embedSU hf hK hk hn).range ↔
      IsIdOutside (Set.range f) ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [coe_embedSU]
    exact isIdOutside_embedMatU _
  · intro hx
    set P := inclMat (K := K) f
    set X := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    set X' := (((x⁻¹ : StatedSU n (2 ^ e) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hPP : Pᵀ * P = 1 := inclMat_transpose_mul hf
    have hXX' : X * X' = 1 := by
      have h := congrArg (fun z : StatedSU n (2 ^ e) K =>
        ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (mul_inv_cancel x)
      simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h
    have hX'X : X' * X = 1 := by
      have h := congrArg (fun z : StatedSU n (2 ^ e) K =>
        ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (inv_mul_cancel x)
      simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h
    have hx' : IsIdOutside (Set.range f) X' := hx.of_mul_eq_one hXX' hX'X
    have hsupp : ∀ {Y : Matrix (Fin n) (Fin n) K}, IsIdOutside (Set.range f) Y →
        ∀ a b, (a ∉ Set.range f ∨ b ∉ Set.range f) → (Y - 1) a b = 0 := by
      intro Y hY a b hab
      rw [Matrix.sub_apply, hY a b hab, sub_self]
    have hQ : ∀ {Y : Matrix (Fin n) (Fin n) K}, IsIdOutside (Set.range f) Y →
        P * Pᵀ * Y = Y * (P * Pᵀ) ∧ P * Pᵀ * Y * (P * Pᵀ) = Y * (P * Pᵀ) := by
      intro Y hY
      obtain ⟨h1, h2⟩ := projQU_mul_of_supp hf (hsupp hY)
      have hQQ : P * Pᵀ * (P * Pᵀ) = P * Pᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hPP, Matrix.one_mul]
      have eY : Y = 1 + (Y - 1) := by abel
      constructor
      · rw [eY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]
      · rw [eY, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, h1, hQQ,
          Matrix.one_mul, h2]
    obtain ⟨hQX, hQXQ⟩ := hQ hx
    have hQP : P * Pᵀ * P = P := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    have hPQ : Pᵀ * (P * Pᵀ) = Pᵀ := by rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    set g := Pᵀ * X * P
    set g' := Pᵀ * X' * P
    have hgg' : g * g' = 1 := by
      calc g * g' = Pᵀ * (X * (P * Pᵀ)) * X' * P := by simp only [g, g', Matrix.mul_assoc]
        _ = Pᵀ * (P * Pᵀ) * (X * X') * P := by rw [← hQX]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hXX', Matrix.mul_one, ← Matrix.mul_assoc, hPP, Matrix.one_mul, hPP]
    have hg'g : g' * g = 1 := mul_eq_one_comm.mp hgg'
    have hemb : embedMatU f g = X := by
      rw [embedMatU]
      have e1 : P * (g - 1) * Pᵀ = P * Pᵀ * X * (P * Pᵀ) - P * Pᵀ := by
        simp only [g, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      rw [e1, hQXQ]
      obtain ⟨-, h2⟩ := projQU_mul_of_supp hf (hsupp hx)
      have e2 : X * (P * Pᵀ) = P * Pᵀ + (X - 1) := by
        have := h2
        rw [Matrix.sub_mul, Matrix.one_mul] at this
        rw [← this]
        abel
      rw [e2]
      abel
    have hxU : X.det = 1 ∧ (X.map (iterateFrobenius K 2 e))ᵀ * X = 1 :=
      (mem_statedSU_iff' e hK hn (x : GL (Fin n) K)).mp x.2
    have hdet : g.det = 1 := by rw [← det_embedMatU hf, hemb]; exact hxU.1
    have hunit : (g.map (iterateFrobenius K 2 e))ᵀ * g = 1 := by
      have hY : IsIdOutside (Set.range f) ((X.map (iterateFrobenius K 2 e))ᵀ) :=
        isIdOutside_map_frob hx
      obtain ⟨hQY, -⟩ := hQ hY
      have hPm : P.map (iterateFrobenius K 2 e) = P := inclMat_map_frob
      have hPtm : Pᵀ.map (iterateFrobenius K 2 e) = Pᵀ := by rw [transpose_map, hPm]
      have hgmap : (g.map (iterateFrobenius K 2 e))ᵀ =
          Pᵀ * (X.map (iterateFrobenius K 2 e))ᵀ * P := by
        simp only [g, Matrix.map_mul, hPm, hPtm, transpose_mul, transpose_transpose,
          Matrix.mul_assoc]
      rw [hgmap]
      calc Pᵀ * (X.map (iterateFrobenius K 2 e))ᵀ * P * (Pᵀ * X * P) =
            Pᵀ * ((X.map (iterateFrobenius K 2 e))ᵀ * (P * Pᵀ)) * X * P := by
            simp only [Matrix.mul_assoc]
        _ = Pᵀ * (P * Pᵀ) * ((X.map (iterateFrobenius K 2 e))ᵀ * X) * P := by
            rw [← hQY]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hxU.2, Matrix.mul_one, hPQ, hPP]
    let gGL : GL (Fin k) K := ⟨g, g', hgg', hg'g⟩
    have hgSU : gGL ∈ StatedSU k (2 ^ e) K := (mem_statedSU_iff' e hK hk gGL).mpr ⟨hdet, hunit⟩
    refine ⟨⟨gGL, hgSU⟩, Subtype.ext (Units.ext ?_)⟩
    rw [coe_embedSU]
    exact hemb

end CFSG.RankThree.PartTwo.Sec21.Tables
