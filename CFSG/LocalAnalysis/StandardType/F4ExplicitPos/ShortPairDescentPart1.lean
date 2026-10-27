module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6PairDescent

@[expose] public section

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal

open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix

open CFSG.SeitzReduction.F4Pilot

open CFSG.Timmesfeld.ARS.CaseM

open CFSG.Timmesfeld.Transvection.ModelRank

open CFSG.StandardType.F4ExplicitPos.Sp6PairDescent

namespace CFSG.StandardType.F4ExplicitPos.ShortPairDescent

abbrev altNil {n : ℕ} {F : Type} [Field F] (a b : Fin n ⊕ Fin n → F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.vecMulVec a (Matrix.mulVec (spGram n F) b) +
    Matrix.vecMulVec b (Matrix.mulVec (spGram n F) a)

theorem vecMul_spGram_mulVec_spGram {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (b : Fin n ⊕ Fin n → F) :
    (Matrix.mulVec (spGram n F) b) ᵥ* spGram n F = b := by
  rw [vecMul_spGram_eq_mulVec, Matrix.mulVec_mulVec, spGram_mul_self_eq_one,
    Matrix.one_mulVec]

theorem altNil_mul_spGram {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a b : Fin n ⊕ Fin n → F) :
    altNil a b * spGram n F = Matrix.vecMulVec a b + Matrix.vecMulVec b a := by
  rw [altNil, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    vecMul_spGram_mulVec_spGram, vecMul_spGram_mulVec_spGram]

theorem dotProduct_mulVec_spGram {n : ℕ} {F : Type} [Field F]
    (u v : Fin n ⊕ Fin n → F) :
    (Matrix.mulVec (spGram n F) v) ⬝ᵥ u = spForm u v := by
  rw [dotProduct_comm]

theorem altNil_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a b : Fin n ⊕ Fin n → F) :
    altNil a b * altNil a b =
      spForm a b • altNil a b + spForm a a • spNil b + spForm b b • spNil a := by
  have hPP := Matrix.vecMulVec_mul_vecMulVec a (Matrix.mulVec (spGram n F) b)
    a (Matrix.mulVec (spGram n F) b)
  have hPQ := Matrix.vecMulVec_mul_vecMulVec a (Matrix.mulVec (spGram n F) b)
    b (Matrix.mulVec (spGram n F) a)
  have hQP := Matrix.vecMulVec_mul_vecMulVec b (Matrix.mulVec (spGram n F) a)
    a (Matrix.mulVec (spGram n F) b)
  have hQQ := Matrix.vecMulVec_mul_vecMulVec b (Matrix.mulVec (spGram n F) a)
    b (Matrix.mulVec (spGram n F) a)
  rw [altNil, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hPP, hPQ, hQP, hQQ,
    dotProduct_mulVec_spGram a b, dotProduct_mulVec_spGram b b,
    dotProduct_mulVec_spGram a a, dotProduct_mulVec_spGram b a]
  rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul,
    ← spNil_eq_vecMulVec a, ← spNil_eq_vecMulVec b]
  rw [spForm_comm a b, CharTwo.neg_eq]
  module

theorem map_altNil {n : ℕ} {k Ω : Type} [Field k] [Field Ω] (φ : k →+* Ω)
    (u v : Fin n ⊕ Fin n → k) :
    (altNil u v).map φ = altNil (fun i => φ (u i)) (fun i => φ (v i)) := by
  ext i j
  simp only [altNil, Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    RingHom.map_add, RingHom.map_mul, RingHom.map_mulVec, map_symplecticGram]
  rfl

theorem map_smul_altNil {n : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (lam : k) (u v : Fin n ⊕ Fin n → k) :
    (lam • altNil u v).map (algebraMap k Ω) =
      (algebraMap k Ω lam) • (altNil u v).map (algebraMap k Ω) :=
  Matrix.map_smul' (algebraMap k Ω) lam (altNil u v) (fun a b => map_mul _ a b)

theorem map_spForm {n : ℕ} {k Ω : Type} [Field k] [Field Ω] (φ : k →+* Ω)
    (v w : Fin n ⊕ Fin n → k) :
    spForm (fun i => φ (v i)) (fun i => φ (w i)) = φ (spForm v w) := by
  rw [spForm, spForm, RingHom.map_dotProduct φ v (Matrix.mulVec (spGram n k) w)]
  congr 1
  funext i
  simp only [Function.comp_apply, RingHom.map_mulVec, map_symplecticGram]
  rfl

theorem short_support_descent {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [CharP k 2] [CharP Ω 2]
    {a b : Fin 3 ⊕ Fin 3 → Ω}
    (haa : spForm a a = 0) (hbb : spForm b b = 0) (hab : spForm a b = 0)
    {N₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k}
    {t : Ω} (_ht : t ≠ 0)
    (hN : N₀.map (algebraMap k Ω) = t • altNil a b)
    (hN₀ : N₀ ≠ 0) :
    ∃ (u v : Fin 3 ⊕ Fin 3 → k) (_ : u ≠ 0) (_ : v ≠ 0) (c : k) (_ : c ≠ 0),
      N₀ = c • altNil u v ∧ spForm u u = 0 ∧ spForm v v = 0 ∧ spForm u v = 0 := by
  classical
  have hba : spForm b a = 0 := by rw [spForm_comm a b, hab, neg_zero]
  let A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k := N₀ * spGram 3 k
  have hAmap : A.map (algebraMap k Ω) =
      t • (Matrix.vecMulVec a b + Matrix.vecMulVec b a) := by
    dsimp only [A]
    rw [Matrix.map_mul, hN, map_symplecticGram (algebraMap k Ω) 3, Matrix.smul_mul,
      altNil_mul_spGram]
  have hentry : ∀ i j, algebraMap k Ω (A i j) = t * (a i * b j + b i * a j) := by
    intro i j
    have h := congrFun (congrFun hAmap i) j
    simpa only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
      smul_eq_mul] using h
  have hA : A ≠ 0 := by
    intro h0
    apply hN₀
    calc N₀ = N₀ * 1 := (Matrix.mul_one N₀).symm
      _ = N₀ * (spGram 3 k * spGram 3 k) := by rw [spGram_mul_self_eq_one]
      _ = (N₀ * spGram 3 k) * spGram 3 k := by rw [Matrix.mul_assoc]
      _ = A * spGram 3 k := rfl
      _ = 0 := by rw [h0, Matrix.zero_mul]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hA
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  let u : Fin 3 ⊕ Fin 3 → k := fun p => A p i
  let v : Fin 3 ⊕ Fin 3 → k := fun p => A p j
  have hAij : A i j ≠ 0 := hij
  have hAii : A i i = 0 := by
    apply (algebraMap k Ω).injective
    rw [map_zero, hentry i i]
    linear_combination (t * (a i * b i)) * (CharTwo.two_eq_zero : (2 : Ω) = 0)
  have hAjj : A j j = 0 := by
    apply (algebraMap k Ω).injective
    rw [map_zero, hentry j j]
    linear_combination (t * (a j * b j)) * (CharTwo.two_eq_zero : (2 : Ω) = 0)
  have hsym : A j i = A i j := by
    apply (algebraMap k Ω).injective
    rw [hentry j i, hentry i j]
    ring
  have huj : u j = A i j := hsym
  have hvi : v i = A i j := rfl
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : u j = 0 := by simp [h0]
    rw [huj] at h1
    exact hAij h1
  have hv_ne : v ≠ 0 := by
    intro h0
    have h1 : v i = 0 := by simp [h0]
    rw [hvi] at h1
    exact hAij h1
  have hAid : A i j • A = Matrix.vecMulVec u v + Matrix.vecMulVec v u := by
    apply Matrix.map_injective (algebraMap k Ω).injective
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, map_mul, map_add]
    rw [hentry i j, hentry p q, hentry p i, hentry q j, hentry p j, hentry q i]
    linear_combination
      (-(t * t * (a p * a q * b i * b j + b p * b q * a i * a j))) *
        (CharTwo.two_eq_zero : (2 : Ω) = 0)
  have hu : (fun p => algebraMap k Ω (u p)) = t • (b i • a + a i • b) := by
    ext p
    have h := hentry p i
    change algebraMap k Ω (A p i) = (t • (b i • a + a i • b)) p
    rw [h]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hv : (fun p => algebraMap k Ω (v p)) = t • (b j • a + a j • b) := by
    ext p
    have h := hentry p j
    change algebraMap k Ω (A p j) = (t • (b j • a + a j • b)) p
    rw [h]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have huu : spForm u u = 0 := by
    apply (algebraMap k Ω).injective
    rw [map_zero, ← map_spForm, hu]
    simp only [spForm_self]
    try ring
  have hvv : spForm v v = 0 := by
    apply (algebraMap k Ω).injective
    rw [map_zero, ← map_spForm, hv]
    simp only [spForm_self]
    try ring
  have huv : spForm u v = 0 := by
    apply (algebraMap k Ω).injective
    rw [map_zero, ← map_spForm, hu, hv]
    simp only [spForm_smul_left', spForm_smul_right', spForm_add_left, spForm_add_right,
      haa, hbb, hab, hba]
    try ring
  have hAeq : A = (A i j)⁻¹ • (Matrix.vecMulVec u v + Matrix.vecMulVec v u) := by
    rw [← hAid, smul_smul, inv_mul_cancel₀ hAij, one_smul]
  have hN₀eq : N₀ = (A i j)⁻¹ • altNil u v := by
    calc N₀ = (N₀ * spGram 3 k) * spGram 3 k := by
          rw [Matrix.mul_assoc, spGram_mul_self_eq_one, Matrix.mul_one]
      _ = A * spGram 3 k := rfl
      _ = ((A i j)⁻¹ • (Matrix.vecMulVec u v + Matrix.vecMulVec v u)) * spGram 3 k := by
            conv_lhs => rw [hAeq]
      _ = (A i j)⁻¹ • ((Matrix.vecMulVec u v + Matrix.vecMulVec v u) * spGram 3 k) := by
            rw [Matrix.smul_mul]
      _ = (A i j)⁻¹ • altNil u v := by
            rw [← altNil_mul_spGram u v, Matrix.mul_assoc, spGram_mul_self_eq_one,
              Matrix.mul_one]
  exact ⟨u, v, hu_ne, hv_ne, (A i j)⁻¹, inv_ne_zero hAij, hN₀eq, huu, hvv, huv⟩

theorem one_add_smul_altNil_mul {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F} (hN : altNil a b * altNil a b = 0) (c d : F) :
    (1 + c • altNil a b) * (1 + d • altNil a b) = 1 + (c + d) • altNil a b := by
  have h : (1 + c • altNil a b) * (1 + d • altNil a b) =
      1 + c • altNil a b + d • altNil a b + (c * d) • (altNil a b * altNil a b) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    abel
  rw [h, hN, smul_zero, add_zero, add_smul]
  abel

def altSiegelSub {n : ℕ} {F : Type} [Field F] [CharP F 2] (a b : Fin n ⊕ Fin n → F)
    (hN : altNil a b * altNil a b = 0) : Subgroup (GL (Fin n ⊕ Fin n) F) where
  carrier := {g | ∃ c : F, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 + c • altNil a b}
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Units.val_mul, hc, hd, one_add_smul_altNil_mul hN c d]⟩
  one_mem' := ⟨0, by rw [zero_smul, add_zero, Units.val_one]⟩
  inv_mem' := by
    rintro x ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hxx : x * x = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one, hc, one_add_smul_altNil_mul hN c c,
        CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rw [inv_eq_of_mul_eq_one_right hxx, hc]

def spAltSiegelSub {n : ℕ} {F : Type} [Field F] [CharP F 2] (a b : Fin n ⊕ Fin n → F)
    (hN : altNil a b * altNil a b = 0) : Subgroup (StatedSp n F) :=
  (altSiegelSub a b hN).comap (StatedSp n F).subtype

theorem mem_spAltSiegelSub_iff {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F} (hN : altNil a b * altNil a b = 0) (x : StatedSp n F) :
    x ∈ spAltSiegelSub a b hN ↔ ∃ c : F, SpExtras.mat n F x = 1 + c • altNil a b := by
  rw [spAltSiegelSub, Subgroup.mem_comap]
  rfl

theorem altSiegelGroup_eq_altSiegelSub {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F}
    (haa : spForm a a = 0) (hbb : spForm b b = 0) (hab : spForm a b = 0) :
    altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b =
      altSiegelSub a b (by rw [altNil_mul_self, hab, haa, hbb]; simp) := by
  apply le_antisymm
  · rw [altSiegelGroup, Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    exact ⟨c, hc⟩
  · intro g hg
    obtain ⟨c, hc⟩ := hg
    rw [altSiegelGroup]
    exact Subgroup.subset_closure ⟨c, hc⟩

def IsAltSiegelGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a b : Fin n ⊕ Fin n → F) (X : Subgroup (StatedSp n F)) : Prop :=
  (∀ x, x ∈ X ↔ ∃ c : F, SpExtras.mat n F x = 1 + c • altNil a b) ∧
    (∀ c : F, ∃ x : StatedSp n F, SpExtras.mat n F x = 1 + c • altNil a b)

theorem exists_mat_eq_altNil {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F} (hab : spForm a b = 0) (c : F) :
    ∃ x : StatedSp n F, SpExtras.mat n F x = 1 + c • altNil a b := by
  have hab' : a ⬝ᵥ Matrix.mulVec (CFSG.LieType.BorelTits.spJ n F) b = 0 := hab
  obtain ⟨g, _hg, hact⟩ :=
    CFSG.StandardType.LieKnownR2.Short.exists_mem_spAltSiegel_mulVec hab' c
  refine ⟨g, ?_⟩
  have hsym : ∀ (w : Fin n ⊕ Fin n → F) (j : Fin n ⊕ Fin n),
      w ⬝ᵥ Matrix.mulVec (CFSG.LieType.BorelTits.spJ n F) (Pi.single j 1) =
        Matrix.mulVec (CFSG.LieType.BorelTits.spJ n F) w j := by
    intro w j
    rw [Matrix.dotProduct_mulVec,
      ← CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two (n := n) (F := F),
      Matrix.vecMul_transpose,
      CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two, dotProduct_single_one]
  ext i j
  have hj := congrFun (hact (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hj
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsym, Matrix.col_apply] at hj
  change ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j = _
  rw [hj]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Pi.single_apply]
  ring

theorem card_spAltSiegelSub {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin n ⊕ Fin n → F} (hab : spForm a b = 0)
    (hN : altNil a b * altNil a b = 0) (hE : altNil a b ≠ 0) :
    Nat.card (spAltSiegelSub a b hN) = Nat.card F := by
  classical
  let f : F → spAltSiegelSub a b hN := fun c =>
    ⟨Classical.choose (exists_mat_eq_altNil hab c),
      (mem_spAltSiegelSub_iff hN _).mpr ⟨c, Classical.choose_spec (exists_mat_eq_altNil hab c)⟩⟩
  have hf : ∀ c, SpExtras.mat n F (f c : StatedSp n F) = 1 + c • altNil a b :=
    fun c => Classical.choose_spec (exists_mat_eq_altNil hab c)
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro c d hcd
    have h1 : 1 + c • altNil a b = 1 + d • altNil a b := by rw [← hf c, hcd, hf d]
    have h2 : c • altNil a b = d • altNil a b := add_left_cancel h1
    have h3 : (c - d) • altNil a b = 0 := by rw [sub_smul, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hE)
  · intro x
    obtain ⟨c, hc⟩ := (mem_spAltSiegelSub_iff hN (x : StatedSp n F)).mp x.2
    exact ⟨c, Subtype.ext (SpExtras.mat_injective ((hf c).trans hc.symm))⟩

end CFSG.StandardType.F4ExplicitPos.ShortPairDescent
end

end
