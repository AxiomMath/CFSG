module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Refl

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

@[expose] def F2Vals (G₀ : Subgroup (antiSp k)) : Prop :=
  ∀ r ∈ normC G₀, ∀ s ∈ normC G₀, spBil r s = 0 ∨ spBil r s = 1

theorem exists_basis (hspan : Submodule.span k (normC G₀) = ⊤) :
    ∃ b : Fin 4 → Fin 4 → k, (∀ j, b j ∈ normC G₀) ∧ LinearIndependent k b := by
  obtain ⟨s, hsR, hspan', hli⟩ := exists_linearIndependent k (normC G₀)
  have hB := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan', hspan]))
  have : Finite s := hli.finite
  have : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = 4 := by
    rw [← Module.finrank_eq_card_basis hB, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  exact ⟨fun j => (e.symm j : Fin 4 → k), fun j => hsR (e.symm j).2,
    hli.comp _ e.symm.injective⟩

@[expose] def c2 : ZMod 2 →+* k :=
  ZMod.castHom (dvd_refl 2) k

theorem c2_injective : Function.Injective (c2 : ZMod 2 →+* k) :=
  ZMod.castHom_injective k

omit [CharP k 2] in
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem c2_eq_zero_or_one (a : ZMod 2) : c2 a = (0 : k) ∨ c2 a = (1 : k) := by
  rcases zmod2_cases a with rfl | rfl
  · exact Or.inl (map_zero (c2 : ZMod 2 →+* k))
  · exact Or.inr (map_one (c2 : ZMod 2 →+* k))

@[expose] noncomputable def toF2 (a : k) : ZMod 2 := by
  classical exact if a = 1 then 1 else 0

theorem c2_toF2 {a : k} (ha : a = 0 ∨ a = 1) : c2 (toF2 a) = a := by
  rcases ha with rfl | rfl
  · simp [toF2]
  · simp [toF2]

@[expose] def emb (b : Fin 4 → Fin 4 → k) (x : Fin 4 → ZMod 2) : Fin 4 → k :=
  ∑ j, (c2 (x j) : k) • b j

variable {b : Fin 4 → Fin 4 → k}

theorem emb_add (x y : Fin 4 → ZMod 2) : emb b (x + y) = emb b x + emb b y := by
  simp only [emb, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem emb_smul (c : ZMod 2) (x : Fin 4 → ZMod 2) : emb b (c • x) = (c2 c : k) • emb b x := by
  simp only [emb, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem emb_zero : emb b 0 = 0 := by
  simp [emb]

theorem emb_single (j : Fin 4) : emb b (Pi.single j 1) = b j := by
  rw [emb, Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_eq_of_ne hij])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

theorem emb_injective (hli : LinearIndependent k b) : Function.Injective (emb b) := by
  intro x y h
  have h' : ∑ j, ((c2 (x j) : k) - c2 (y j)) • b j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext j
  exact c2_injective (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h' j))

omit [CharP k 2] in
theorem span_range_eq_top (hli : LinearIndependent k b) :
    Submodule.span k (Set.range b) = ⊤ :=
  hli.span_eq_top_of_card_eq_finrank (by simp)

omit [CharP k 2] in
theorem eq_of_bil_basis (hli : LinearIndependent k b) {y z : Fin 4 → k}
    (h : ∀ j, spBil y (b j) = spBil z (b j)) : y = z := by
  rw [← sub_eq_zero]
  apply eq_zero_of_bil_eq_zero
  intro w
  have hw : w ∈ Submodule.span k (Set.range b) := by
    rw [span_range_eq_top hli]
    exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨j, rfl⟩ := hw
    rw [map_sub, bil_symm _ y, bil_symm _ z, h j, sub_self]
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, LinearMap.add_apply, ha, hc, add_zero]
  | smul a c _ hc => rw [map_smul, LinearMap.smul_apply, hc, smul_zero]

@[expose] noncomputable def gram (b : Fin 4 → Fin 4 → k) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => if i = j then 0 else toF2 (spBil (b i) (b j))

@[expose] noncomputable def f0 (b : Fin 4 → Fin 4 → k) :
    LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) :=
  Matrix.toBilin' (gram b)

omit [CharP k 2] in
theorem gram_symm (i j : Fin 4) : gram b i j = gram b j i := by
  by_cases h : i = j
  · subst h
    rfl
  · simp [gram, h, Ne.symm h, bil_symm (b i) (b j)]

omit [CharP k 2] in
theorem f0_symm (x y : Fin 4 → ZMod 2) : f0 b x y = f0 b y x := by
  simp only [f0, Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [gram_symm]
  ring

omit [CharP k 2] in
theorem f0_self (x : Fin 4 → ZMod 2) : f0 b x x = 0 := by
  have hd : ∀ i, gram b i i = 0 := fun i => by simp [gram]
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp only [f0, Matrix.toBilin'_apply, Fin.sum_univ_four, hd]
  rw [gram_symm 1 0, gram_symm 2 0, gram_symm 3 0, gram_symm 2 1, gram_symm 3 1, gram_symm 3 2]
  linear_combination (x 0 * x 1 * gram b 0 1 + x 0 * x 2 * gram b 0 2 + x 0 * x 3 * gram b 0 3 +
    x 1 * x 2 * gram b 1 2 + x 1 * x 3 * gram b 1 3 + x 2 * x 3 * gram b 2 3) * h2

theorem c2_gram (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (i j : Fin 4) :
    c2 (gram b i j) = spBil (b i) (b j) := by
  by_cases h : i = j
  · subst h
    simp [gram, bil_self]
  · simp only [gram, Matrix.of_apply, h, ↓reduceIte]
    exact c2_toF2 (hF _ (hb i) _ (hb j))

theorem bil_emb (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (x y : Fin 4 → ZMod 2) :
    spBil (emb b x) (emb b y) = c2 (f0 b x y) := by
  have hL : spBil (emb b x) (emb b y) = ∑ j, ∑ i, c2 (x i) * spBil (b i) (b j) * c2 (y j) := by
    simp only [emb, LinearMap.BilinForm.sum_left, LinearMap.BilinForm.sum_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hL, Finset.sum_comm, f0, Matrix.toBilin'_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, c2_gram hF hb]

theorem bil_emb_eq_zero_or_one (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (x y : Fin 4 → ZMod 2) : spBil (emb b x) (emb b y) = 0 ∨ spBil (emb b x) (emb b y) = 1 := by
  rw [bil_emb hF hb]
  exact c2_eq_zero_or_one _

theorem eq_zero_of_f0 (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {x : Fin 4 → ZMod 2} (h : ∀ y, f0 b x y = 0) : x = 0 := by
  apply emb_injective hli
  rw [emb_zero]
  apply eq_of_bil_basis hli
  intro j
  rw [← emb_single (b := b) j, bil_emb hF hb, h, map_zero, LinearMap.map_zero₂]

theorem exists_emb_eq (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {r : Fin 4 → k} (hr : r ∈ normC G₀) : ∃ x, emb b x = r := by
  have hval : ∀ x j, spBil (emb b x) (b j) = 0 ∨ spBil (emb b x) (b j) = 1 := fun x j => by
    rw [← emb_single (b := b) j]
    exact bil_emb_eq_zero_or_one hF hb x _
  let Φ : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) := fun x j => toF2 (spBil (emb b x) (b j))
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    refine emb_injective hli (eq_of_bil_basis hli fun j => ?_)
    rw [← c2_toF2 (hval x j), ← c2_toF2 (hval y j)]
    exact congrArg c2 (congrFun hxy j)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hΦ) fun j => toF2 (spBil r (b j))
  refine ⟨x, eq_of_bil_basis hli fun j => ?_⟩
  rw [← c2_toF2 (hval x j), ← c2_toF2 (hF r hr _ (hb j))]
  exact congrArg c2 (congrFun hx j)

@[expose] noncomputable def pre (b : Fin 4 → Fin 4 → k) (r : Fin 4 → k) : Fin 4 → ZMod 2 :=
  Function.invFun (emb b) r

theorem emb_pre (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {r : Fin 4 → k} (hr : r ∈ normC G₀) : emb b (pre b r) = r := by
  exact Function.invFun_eq (exists_emb_eq hF hb hli hr)

theorem pre_ne_zero (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {r : Fin 4 → k} (hr : r ∈ normC G₀) : pre b r ≠ 0 := by
  intro h
  apply hr.1
  rw [← emb_pre hF hb hli hr, h, emb_zero]

theorem pre_emb (hli : LinearIndependent k b) (x : Fin 4 → ZMod 2) : pre b (emb b x) = x := by
  exact Function.leftInverse_invFun (emb_injective hli) x

end CFSG.Quasithin.Ch3E213M.G41.Refl
