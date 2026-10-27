module

public import CFSG.Quasithin.H13.L32NKGSp4
public import Certificates.Certificate7102

public section

namespace CFSG.Quasithin.H13.KGCert

@[expose] def vec6 (n : ℕ) : Fin 6 → ZMod 2 := fun i => b2z (n.testBit i)

@[expose] def code6 (v : Fin 6 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val + 32 * (v 5).val

theorem vec6_code6 (v : Fin 6 → ZMod 2) : vec6 (code6 v) = v := by
  have key : ∀ a b c d e f : ZMod 2, vec6 (code6 ![a, b, c, d, e, f]) = ![a, b, c, d, e, f] := by
    decide
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact key _ _ _ _ _ _

theorem code6_lt (v : Fin 6 → ZMod 2) : code6 v < 64 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  simp only [code6]
  omega

theorem testBit_eq_of_vec6 {m n : ℕ} (h : vec6 m = vec6 n) (i : ℕ) (hi : i < 6) :
    m.testBit i = n.testBit i :=
  b2z_inj (congrFun h ⟨i, hi⟩)

theorem vec6_inj {m n : ℕ} (hm : m < 64) (hn : n < 64) (h : vec6 m = vec6 n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact testBit_eq_of_vec6 h i hi
  · have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (h64 ▸ hm) (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (h64 ▸ hn) (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem vec6_xor (m n : ℕ) : vec6 (m ^^^ n) = vec6 m + vec6 n := by
  ext i
  simp only [vec6, Nat.testBit_xor, b2z_xor, Pi.add_apply]

theorem vec6_zero : vec6 0 = 0 := by
  ext i
  simp [vec6, b2z]

theorem vec6_ite (c : Bool) (a : ℕ) : vec6 (if c then a else 0) = b2z c • vec6 a := by
  cases c <;> simp [vec6_zero, b2z]

@[expose] def decodeC (A : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => vec6 (A.getD j 0) i

theorem decodeC_mulVec (A : List ℕ) (v : ℕ) :
    (decodeC A).mulVec (vec6 v) = vec6 (mulVecC A v) := by
  obtain ⟨-, -, -, -, f0, f1, f2, f3, f4, f5⟩ := fin_vals
  ext i
  simp only [mulVecC, vec6_xor, vec6_ite, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Fin.sum_univ_six, decodeC, Matrix.of_apply]
  simp only [vec6, bt, f0, f1, f2, f3, f4, f5]
  ring

theorem decodeC_mulC (A B : List ℕ) (hB : B.length = 6) :
    decodeC (mulC A B) = decodeC A * decodeC B := by
  ext i j
  have hj : (j : ℕ) < B.length := by rw [hB]; exact j.isLt
  have hget : (mulC A B).getD j 0 = mulVecC A (B.getD j 0) := by
    simp only [mulC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some]
  simp only [decodeC, Matrix.of_apply, Matrix.mul_apply]
  rw [hget, ← decodeC_mulVec]
  simp only [Matrix.mulVec, dotProduct, decodeC, Matrix.of_apply]

theorem decodeC_oneC : decodeC oneC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

@[expose] def ValidC (A : List ℕ) : Prop := A.length = 6 ∧ ∀ c ∈ A, c < 64

theorem decodeC_injOn {A A' : List ℕ} (hA : ValidC A) (hA' : ValidC A')
    (h : decodeC A = decodeC A') : A = A' := by
  apply List.ext_getElem (hA.1.trans hA'.1.symm)
  intro j hj hj'
  have hj6 : j < 6 := hA.1 ▸ hj
  have hcol : vec6 (A.getD j 0) = vec6 (A'.getD j 0) := by
    ext i
    have := congrFun (congrFun h i) ⟨j, hj6⟩
    simpa [decodeC] using this
  have h1 := vec6_inj (hA.2 _ (List.getD_eq_getElem _ _ hj ▸ List.getElem_mem hj))
    (hA'.2 _ (List.getD_eq_getElem _ _ hj' ▸ List.getElem_mem hj')) hcol
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h1

@[expose] def g22Mats : Submonoid (Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
  Submonoid.closure {decodeC gAc, decodeC gBc}

theorem length_mulC (A B : List ℕ) : (mulC A B).length = B.length := List.length_map _

theorem length_evalWord (w : List Bool) : (evalWord w).length = 6 := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    show (mulC (if g then gAc else gBc) (evalWord w)).length = 6
    rw [length_mulC, ih]

theorem evalWord_cons (g : Bool) (w : List Bool) :
    evalWord (g :: w) = mulC (if g then gAc else gBc) (evalWord w) := rfl

theorem decodeC_evalWord_mem (w : List Bool) : decodeC (evalWord w) ∈ g22Mats := by
  induction w with
  | nil => exact decodeC_oneC ▸ g22Mats.one_mem
  | cons g w ih =>
    rw [evalWord_cons, decodeC_mulC _ _ (length_evalWord w)]
    refine g22Mats.mul_mem (Submonoid.subset_closure ?_) ih
    cases g
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem mem_g22Elems {x : List ℕ} : x ∈ g22Elems ↔ ∃ w ∈ g22Words, evalWord w = x :=
  List.mem_map

theorem validC_of_mem {x : List ℕ} (hx : x ∈ g22Elems) :
    ValidC x := by
  have h := Certificates.certificate7102.2.2.1
  simp only [g22ValidCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact h x hx

theorem mulC_mem {x : List ℕ} (hx : x ∈ g22Elems) :
    mulC gAc x ∈ g22Elems ∧ mulC gBc x ∈ g22Elems := by
  have h := Certificates.certificate7102.2.2.2.1
  simp only [g22ClosedCheck, List.all_eq_true, Bool.and_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  exact h x hx

theorem mem_g22Mats_iff (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    M ∈ g22Mats ↔ ∃ x ∈ g22Elems, decodeC x = M := by
  constructor
  · intro hM
    refine Submonoid.closure_induction_left (motive := fun M _ => ∃ x ∈ g22Elems, decodeC x = M)
      ⟨oneC, Certificates.certificate7102.2.1, decodeC_oneC⟩ ?_ hM
    rintro g hg N - ⟨x, hx, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨mulC gAc x, (mulC_mem hx).1, decodeC_mulC _ _ (validC_of_mem hx).1⟩
    · exact ⟨mulC gBc x, (mulC_mem hx).2, decodeC_mulC _ _ (validC_of_mem hx).1⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, -, rfl⟩ := mem_g22Elems.mp hx
    exact decodeC_evalWord_mem w

theorem getD_lt_of_validC {A : List ℕ} (hA : ValidC A) (j : ℕ) : A.getD j 0 < 64 := by
  by_cases hj : j < A.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hA.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem mulVecC_lt {A : List ℕ} (hA : ValidC A) (v : ℕ) : mulVecC A v < 64 := by
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  have hite : ∀ (c : Bool) (n : ℕ), n < 2 ^ 6 → (if c then n else 0) < 2 ^ 6 := by
    intro c n hn
    cases c
    · simp
    · simpa using hn
  have hcol : ∀ j, A.getD j 0 < 2 ^ 6 := fun j => h64 ▸ getD_lt_of_validC hA j
  rw [h64]
  simp only [mulVecC]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (hite _ _ (hcol 0)) (hite _ _ (hcol 1))) (hite _ _ (hcol 2)))
    (hite _ _ (hcol 3))) (hite _ _ (hcol 4))) (hite _ _ (hcol 5))

theorem validC_mulC {A B : List ℕ} (hA : ValidC A) (hB : ValidC B) : ValidC (mulC A B) := by
  refine ⟨(length_mulC A B).trans hB.1, fun c hc => ?_⟩
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
  exact mulVecC_lt hA d

theorem validC_oneC : ValidC oneC := ⟨rfl, by decide⟩

@[expose] def KGG22PointStabModel : Prop :=
  ∀ v : Fin 6 → ZMod 2, v ≠ 0 → ∀ z ∈ g22Mats, z.mulVec v = v → z * z = 1 → z ≠ 1 →
    ∃ γ ∈ g22Mats, γ.mulVec v = v ∧ γ * z ≠ z * γ

theorem kgG22PointStabModel : KGG22PointStabModel := by
  intro v hv z hz hzv hzz hz1
  obtain ⟨zx, hzx, rfl⟩ := (mem_g22Mats_iff z).mp hz
  have hzxV := validC_of_mem hzx
  set n := code6 v with hn
  have hvn : vec6 n = v := vec6_code6 v
  have hn0 : n ≠ 0 := by
    intro h
    apply hv
    rw [← hvn, h, vec6_zero]
  have hfix : ∀ x : List ℕ, ValidC x → (decodeC x).mulVec v = v → mulVecC x n = n := by
    intro x hx h
    apply vec6_inj (mulVecC_lt hx n) (code6_lt v)
    rw [← decodeC_mulVec, hvn, h]
  have h := Certificates.certificate7102.2.2.2.2.1
  simp only [g22StabCheck, List.all_eq_true, List.mem_range, List.mem_filter, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    bne_eq_false_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true] at h
  have hn64 := code6_lt v
  have hn1 : n - 1 + 1 = n := by omega
  have h' := h (n - 1) (by omega) zx
  rw [hn1] at h'
  rcases h' ⟨hzx, hfix zx hzxV hzv⟩ with (hzz' | hz1') | ⟨γx, ⟨hγx, hγv⟩, hγz⟩
  · exfalso
    apply hzz'
    apply decodeC_injOn (validC_mulC hzxV hzxV) validC_oneC
    rw [decodeC_mulC _ _ hzxV.1, hzz, decodeC_oneC]
  · exact absurd hz1' (fun h1 => hz1 (by rw [h1, decodeC_oneC]))
  · refine ⟨decodeC γx, (mem_g22Mats_iff _).mpr ⟨γx, hγx, rfl⟩, ?_, ?_⟩
    · rw [← hvn, decodeC_mulVec, hγv]
    · intro hc
      apply hγz
      apply decodeC_injOn (validC_mulC (validC_of_mem hγx) hzxV)
        (validC_mulC hzxV (validC_of_mem hγx))
      rw [decodeC_mulC _ _ hzxV.1, decodeC_mulC _ _ (validC_of_mem hγx).1, hc]

@[expose] def g22Form : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0]

theorem g22Form_alternating : g22Form.transpose = g22Form ∧ ∀ i, g22Form i i = 0 := by
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · fin_cases i <;> rfl

theorem g22Form_mul_self : g22Form * g22Form = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem g22Mats_isometry : ∀ M ∈ g22Mats, M.transpose * g22Form * M = g22Form := by
  intro M hM
  refine Submonoid.closure_induction (motive := fun M _ => M.transpose * g22Form * M = g22Form)
    ?_ ?_ ?_ hM
  · rintro g (rfl | rfl)
    · ext i j
      fin_cases i <;> fin_cases j <;> decide
    · ext i j
      fin_cases i <;> fin_cases j <;> decide
  · simp
  · intro M N _ _ hM hN
    calc (M * N).transpose * g22Form * (M * N)
        = N.transpose * (M.transpose * g22Form * M) * N := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = g22Form := by rw [hM, hN]

theorem g22Elems_nodup : g22Elems.Nodup := by
  have h := Certificates.certificate7102.2.2.2.2.2
  simp only [g22NodupCheck, decide_eq_true_eq] at h
  exact List.Nodup.of_map code36
    ((List.mergeSort_perm _ _).nodup_iff.mp (List.isChain_iff_pairwise.mp h).nodup)

theorem card_g22Mats : Nat.card g22Mats = 12096 := by
  have hset : (g22Mats : Set (Matrix (Fin 6) (Fin 6) (ZMod 2))) =
      ↑((g22Elems.map decodeC).toFinset) := by
    ext M
    simp only [SetLike.mem_coe, mem_g22Mats_iff, List.mem_toFinset, List.mem_map]
  have hnd : (g22Elems.map decodeC).Nodup := g22Elems_nodup.map_on fun x hx y hy h =>
    decodeC_injOn (validC_of_mem hx) (validC_of_mem hy) h
  have h := Nat.card_coe_set_eq (g22Mats : Set (Matrix (Fin 6) (Fin 6) (ZMod 2)))
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map,
    Certificates.certificate7102.1, ← hset] at h
  exact h

@[expose] def KGSp6Order12096 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    Module.finrank (ZMod 2) V = 6 →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod 2] V), (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) →
    Nat.card Γ = 12096 →
    ∃ b : Module.Basis (Fin 6) (ZMod 2) V, ∀ M : Matrix (Fin 6) (Fin 6) (ZMod 2),
      M ∈ g22Mats ↔ ∃ γ ∈ Γ, LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) = M

theorem kgG22PointStab_of (hM : KGG22PointStabModel) (hO : KGSp6Order12096) :
    KGG22PointStab := by
  intro V _ _ _ B hBalt hBnd hdim Γ hΓB hcard v hv S Z₀ hS _ hZS hZ2 _ hle
  obtain ⟨b, hb⟩ := hO V B hBalt hBnd hdim Γ hΓB hcard
  set m : (V ≃ₗ[ZMod 2] V) → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    fun γ => LinearMap.toMatrix b b (γ : V →ₗ[ZMod 2] V) with hm
  have hmul : ∀ γ δ : V ≃ₗ[ZMod 2] V, m (γ * δ) = m γ * m δ := fun γ δ => by
    simp only [hm, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have hfix : ∀ γ : V ≃ₗ[ZMod 2] V, (m γ).mulVec (b.repr v) = b.repr v ↔ γ v = v := fun γ => by
    rw [hm, LinearMap.toMatrix_mulVec_repr, DFunLike.coe_fn_eq, LinearEquiv.coe_coe,
      EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨⟨z, hz⟩, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : Z₀)).mp hZ2
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have : Finite Z₀ := Nat.finite_of_card_ne_zero (by omega)
  have hzz : z * z = 1 := by
    have h := pow_card_eq_one' (G := Z₀) (x := ⟨z, hz⟩)
    rw [hZ2, pow_two] at h
    exact congrArg Subtype.val h
  have hzΓv := hS (hZS hz)
  have hv' : (b.repr v : Fin 6 → ZMod 2) ≠ 0 := by
    intro h
    exact hv ((LinearEquiv.map_eq_zero_iff b.repr).mp (Finsupp.coe_eq_zero.mp h))
  have hmz1 : m z ≠ 1 := by
    intro h
    apply hz1'
    apply LinearEquiv.toLinearMap_injective
    apply (LinearMap.toMatrix b b).injective
    rw [LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
    exact h
  have hmzz : m z * m z = 1 := by
    rw [← hmul, hzz, hm]
    simp only [LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
  obtain ⟨Mγ, hMγ, hMγv, hMγz⟩ := hM _ hv' (m z) ((hb _).mpr ⟨z, hzΓv.1, rfl⟩)
    ((hfix z).mpr hzΓv.2) hmzz hmz1
  obtain ⟨γ, hγΓ, rfl⟩ := (hb _).mp hMγ
  have hconj : γ * z * γ⁻¹ ∈ Z₀ :=
    (Subgroup.mem_set_normalizer_iff.mp (hle ⟨hγΓ, (hfix γ).mp hMγv⟩) z).mp hz
  have hne : (⟨γ * z * γ⁻¹, hconj⟩ : Z₀) ≠ 1 := by
    intro h
    apply hz1'
    have h' : γ * z * γ⁻¹ = 1 := congrArg Subtype.val h
    calc z = γ⁻¹ * (γ * z * γ⁻¹) * γ := by group
      _ = 1 := by rw [h']; group
  have heq : γ * z * γ⁻¹ = z := congrArg Subtype.val (huniq _ hne)
  apply hMγz
  change m γ * m z = m z * m γ
  rw [← hmul, ← hmul]
  congr 1
  calc γ * z = γ * z * γ⁻¹ * γ := by group
    _ = z * γ := by rw [heq]

theorem kgG22PointStab (hO : KGSp6Order12096) :
    KGG22PointStab :=
  kgG22PointStab_of kgG22PointStabModel hO

end CFSG.Quasithin.H13.KGCert
