module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.KFacts

section Groups

variable {G : Type*} [Group G]

theorem card_closure_eq_nine [Finite G] {a b : G} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a)
    (hexp : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 3 = 1) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Subgroup.closure ({a, b} : Set G) with hD
  have haD : a ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbD : b ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hle : Nat.card D ≤ 9 := card_closure_pair_le_nine hab ha hb
  have hpD : IsPGroup 3 D := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hexp _ x.2)⟩
  obtain ⟨m, hm⟩ := hpD.exists_card_eq
  have hm2 : m ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m
  · exfalso
    have hbot : D = ⊥ := Subgroup.card_eq_one.1 (by rw [hm]; norm_num)
    rw [hbot, Subgroup.mem_bot] at haD
    exact ha1 haD
  · exfalso
    have hz3 : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime ha ha1
    have hzD : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 haD
    have heq := Subgroup.eq_of_le_of_card_ge hzD (by rw [hz3, hm]; norm_num)
    exact hba (heq ▸ hbD)
  · simpa using hm

theorem mem_of_pow_card_eq_one [Finite G] [IsCyclic G] (R : Subgroup G) {x : G}
    (hx : x ^ Nat.card R = 1) : x ∈ R := by
  classical
  have := Fintype.ofFinite G
  set n := Nat.card R with hn
  have hn0 : 0 < n := Nat.card_pos
  set T : Finset G := Finset.univ.filter (fun y : G => y ^ n = 1) with hT
  have hTle : T.card ≤ n := IsCyclic.card_pow_eq_one_le hn0
  set S : Finset G := Finset.univ.filter (fun y : G => y ∈ R) with hS
  have hSn : S.card = n := by
    rw [hn, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun y => by simp [hS]))
  have hST : S ⊆ T := by
    intro y hy
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (⟨y, hy⟩ : R) ^ n = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have heq : S = T := Finset.eq_of_subset_of_card_le hST (by rw [hSn]; exact hTle)
  have hxT : x ∈ T := by simp [hT, hx]
  rw [← heq] at hxT
  simpa [hS] using hxT

end Groups

section Twist

variable {K : Type} [Field K]

@[expose] noncomputable def twistHom (σ : K ≃+* K) : Kˣ →* Kˣ where
  toFun w := Units.map (σ : K →* K) w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem twistHom_apply (σ : K ≃+* K) (w : Kˣ) :
    twistHom σ w = Units.map (σ : K →* K) w * w⁻¹ := rfl

theorem mem_ker_twistHom {σ : K ≃+* K} {w : Kˣ} :
    w ∈ (twistHom σ).ker ↔ σ (w : K) = w := by
  rw [MonoidHom.mem_ker, twistHom_apply, mul_inv_eq_one]
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

variable [Finite K] {σ : K ≃+* K} {k : Subfield K}

omit [Finite K] in
theorem card_ker_twistHom (hk : ∀ x, x ∈ k ↔ σ x = x) :
    Nat.card (twistHom σ).ker = Nat.card k - 1 := by
  rw [← Nat.card_units k]
  refine Nat.card_congr
    { toFun := fun w => Units.mk0 ⟨((w : Kˣ) : K), (hk _).2 (mem_ker_twistHom.1 w.2)⟩
        (fun h => (w : Kˣ).ne_zero (congrArg Subtype.val h))
      invFun := fun u => ⟨Units.map k.subtype.toMonoidHom u, mem_ker_twistHom.2 ((hk _).1
        (by simp))⟩
      left_inv := fun w => by
        apply Subtype.ext
        apply Units.ext
        simp
      right_inv := fun u => by
        apply Units.ext
        apply Subtype.ext
        simp }

theorem card_range_twistHom (hk : ∀ x, x ∈ k ↔ σ x = x) (hkK : Nat.card K = Nat.card k ^ 3) :
    Nat.card (twistHom σ).range = Nat.card k ^ 2 + Nat.card k + 1 := by
  have h1 := (twistHom σ).ker.card_mul_index
  rw [Subgroup.index_ker, card_ker_twistHom hk, Nat.card_units, hkK] at h1
  have hq : 2 ≤ Nat.card k := by
    have := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  set q := Nat.card k with hqdef
  have h2 : (q - 1) * (q ^ 2 + q + 1) = q ^ 3 - 1 := by
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    have : (r + 1) ^ 3 = r * ((r + 1) ^ 2 + (r + 1) + 1) + 1 := by ring
    omega
  have h3 : (q - 1) * Nat.card (twistHom σ).range = (q - 1) * (q ^ 2 + q + 1) := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_left (by omega) h3

theorem exists_units_map_eq_mul (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hkK : Nat.card K = Nat.card k ^ 3) (hk3 : Nat.card k % 3 = 1) {c : Kˣ} (hc : c ^ 3 = 1) :
    ∃ μ : Kˣ, Units.map (σ : K →* K) μ = c * μ := by
  have hR := card_range_twistHom hk hkK
  have h3 : 3 ∣ Nat.card (twistHom σ).range := by
    rw [hR]
    have : (Nat.card k ^ 2 + Nat.card k + 1) % 3 = 0 := by
      rw [Nat.add_mod, Nat.add_mod (Nat.card k ^ 2), Nat.pow_mod, hk3]
    omega
  obtain ⟨m, hm⟩ := h3
  have hcR : c ∈ (twistHom σ).range :=
    mem_of_pow_card_eq_one _ (by rw [hm, pow_mul, hc, one_pow])
  obtain ⟨μ, hμ⟩ := hcR
  refine ⟨μ, ?_⟩
  rw [← hμ, twistHom_apply, inv_mul_cancel_right]

theorem exists_norm_one_not_mem (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hkK : Nat.card K = Nat.card k ^ 3) (hσ3 : ∀ x, σ (σ (σ x)) = x) :
    ∃ u : K, u ≠ 0 ∧ u * σ u * σ (σ u) = 1 ∧ u * (σ u)⁻¹ ∉ k := by
  classical
  have := Fintype.ofFinite K
  have hR := card_range_twistHom hk hkK
  have hq : 2 ≤ Nat.card k := by
    have := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨v, hvR, hv3⟩ : ∃ v ∈ (twistHom σ).range, v ^ 3 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card (twistHom σ).range ≤ 3 := by
      have h1 : (Finset.univ.filter (fun y : Kˣ => y ∈ (twistHom σ).range)) ⊆
          Finset.univ.filter (fun y : Kˣ => y ^ 3 = 1) := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hcon y hy
      have h2 := Finset.card_le_card h1
      have h3 : (Finset.univ.filter (fun y : Kˣ => y ^ 3 = 1)).card ≤ 3 :=
        IsCyclic.card_pow_eq_one_le (by norm_num)
      have h4 : Nat.card (twistHom σ).range =
          (Finset.univ.filter (fun y : Kˣ => y ∈ (twistHom σ).range)).card := by
        rw [← Nat.card_eq_finsetCard]
        exact Nat.card_congr (Equiv.subtypeEquivRight (fun y => by simp))
      omega
    rw [hR] at hle
    nlinarith
  obtain ⟨w, rfl⟩ := hvR
  set u : K := ((twistHom σ w : Kˣ) : K) with hu
  have huw : u = σ (w : K) * (w : K)⁻¹ := by
    rw [hu, twistHom_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hw0 : (w : K) ≠ 0 := w.ne_zero
  have hσw0 : σ (w : K) ≠ 0 := by rw [map_ne_zero]; exact hw0
  have hσσw0 : σ (σ (w : K)) ≠ 0 := by rw [map_ne_zero, map_ne_zero]; exact hw0
  have hu0 : u ≠ 0 := by rw [huw]; exact mul_ne_zero hσw0 (inv_ne_zero hw0)
  have hN : u * σ u * σ (σ u) = 1 := by
    rw [huw]
    simp only [map_mul, map_inv₀, hσ3]
    field_simp
  refine ⟨u, hu0, hN, fun hmem => hv3 ?_⟩
  have hσu0 : σ u ≠ 0 := by rw [map_ne_zero]; exact hu0
  have hσσu0 : σ (σ u) ≠ 0 := by rw [map_ne_zero, map_ne_zero]; exact hu0
  have hfix := (hk _).1 hmem
  rw [map_mul, map_inv₀] at hfix
  have h1 : σ u * σ u = u * σ (σ u) := by
    field_simp at hfix
    linear_combination hfix
  have h2 : (σ u) ^ 3 = 1 := by
    rw [← hN]
    linear_combination σ u * h1
  have h3 : u ^ 3 = 1 := by
    apply σ.injective
    rw [map_pow, h2, map_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ← hu, h3, Units.val_one]

end Twist

section Lift

variable {K : Type} [Field K] (k : Subfield K)

theorem exists_map_eq_of_mem {M : GL (Fin 3) K}
    (hM : ∀ i j, (M : Matrix (Fin 3) (Fin 3) K) i j ∈ k) :
    ∃ M' : GL (Fin 3) k, GeneralLinearGroup.map k.subtype M' = M := by
  set N : Matrix (Fin 3) (Fin 3) k := Matrix.of fun i j => ⟨(M : Matrix (Fin 3) (Fin 3) K) i j,
    hM i j⟩ with hNdef
  have hN : N.map k.subtype = (M : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rfl
  have hdet : IsUnit N.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hM0 : (M : Matrix (Fin 3) (Fin 3) K).det = 0 := by
      have h1 : (N.map k.subtype).det = k.subtype N.det := (RingHom.map_det k.subtype N).symm
      rw [← hN, h1, h0, map_zero]
    have hMu : IsUnit (M : Matrix (Fin 3) (Fin 3) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
    exact hMu.ne_zero hM0
  refine ⟨((Matrix.isUnit_iff_isUnit_det N).2 hdet).unit, Units.ext ?_⟩
  ext i j
  rw [GeneralLinearGroup.map_apply]
  rfl

theorem exists_units_map_eq_of_mem {c : Kˣ} (hc : (c : K) ∈ k) :
    ∃ c' : kˣ, Units.map k.subtype.toMonoidHom c' = c := by
  refine ⟨Units.mk0 ⟨(c : K), hc⟩ (fun h => c.ne_zero (congrArg Subtype.val h)), ?_⟩
  apply Units.ext
  rfl

theorem map_subtype_injective :
    Function.Injective (GeneralLinearGroup.map k.subtype : GL (Fin 3) k →* GL (Fin 3) K) := by
  intro A B h
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i j) h
  simp only [GeneralLinearGroup.map_apply] at this
  exact this

theorem conjUnit_map_subtype (P : GL (Fin 3) k) (g : SpecialLinearGroup (Fin 3) k) :
    conjUnit (GeneralLinearGroup.map k.subtype P) (SpecialLinearGroup.map k.subtype g) =
      SpecialLinearGroup.map k.subtype (conjUnit P g) := by
  apply Subtype.ext
  rw [conjUnit_coe, ← GeneralLinearGroup.map_inv]
  change (GeneralLinearGroup.map k.subtype P : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) k).map k.subtype *
      (GeneralLinearGroup.map k.subtype P⁻¹ : Matrix (Fin 3) (Fin 3) K) =
    ((conjUnit P g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map k.subtype
  rw [conjUnit_coe]
  have hP : ∀ Q : GL (Fin 3) k, (GeneralLinearGroup.map k.subtype Q : Matrix (Fin 3) (Fin 3) K) =
      (Q : Matrix (Fin 3) (Fin 3) k).map k.subtype := fun Q => by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    rfl
  rw [hP, hP, Matrix.map_mul, Matrix.map_mul]

theorem conjUnit_mem_slSub (P : GL (Fin 3) k) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k) :
    conjUnit (GeneralLinearGroup.map k.subtype P) g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k := by
  obtain ⟨g', rfl⟩ := hg
  rw [conjUnit_map_subtype]
  exact ⟨_, rfl⟩

end Lift

section Gen

variable {K : Type} [Field K]

theorem conjAut_proj_eq_conjUnit (A : GL (Fin 3) K) (g : SpecialLinearGroup (Fin 3) K) :
    conjAut 3 K A (proj 3 K g) = proj 3 K (conjUnit A g) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, conjUnit_coe]

theorem fieldAut_proj_of_mem_slSub {σ : K ≃+* K} {k : Subfield K}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k) :
    fieldAut 3 K σ (proj 3 K g) = proj 3 K g := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  have h := (CFSG.RankThree.PartOne.CTP.mem_slSub.1 hg) i j
  change σ ((g : Matrix (Fin 3) (Fin 3) K) i j) = (g : Matrix (Fin 3) (Fin 3) K) i j
  exact (hk _).1 h

theorem eq_top_of_conj_root [Finite K] {k : Subfield K} (hkK : Nat.card K = Nat.card k ^ 3)
    {Y : Subgroup (projectiveSL 3 K)}
    (hY : ∀ g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k, proj 3 K g ∈ Y) (P : GL (Fin 3) k)
    {c : K} (hc : c ∉ k)
    (hPc : proj 3 K (conjUnit (GeneralLinearGroup.map k.subtype P)
      (SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) c)) ∈ Y) :
    Y = ⊤ := by
  set H : Subgroup (SpecialLinearGroup (Fin 3) K) := Y.comap (proj 3 K) with hH
  have hH2 : H.comap (conjUnit (GeneralLinearGroup.map k.subtype P)) = ⊤ := by
    refine CFSG.RankThree.PartOne.CTP.eq_top_of_root_not_mem (n := 3) ?_ le_rfl Nat.prime_three
      hkK hc (by decide : (0 : Fin 3) ≠ 1) hPc
    intro g hg
    exact hY _ (conjUnit_mem_slSub k P hg)
  have hHtop : H = ⊤ := eq_top_of_comap_conjUnit _ hH2
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := proj_surjective 3 K y
  have hg : g ∈ H := by rw [hHtop]; trivial
  exact hg

theorem fieldAut_not_mem_linearAutGroup [Finite K] {σ : K ≃+* K} (hσ : σ ≠ 1) :
    fieldAut 3 K σ ∉ linearAutGroup 3 K := by
  intro h
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 h
  have h1 : conjAut 3 K A⁻¹ * fieldAut 3 K σ = 1 := by rw [map_inv, hA, inv_mul_cancel]
  exact hσ (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _ h1).1

theorem not_isInnerAut_fieldAut [Finite K] {σ : K ≃+* K} (hσ : σ ≠ 1) :
    ¬ IsInnerAut (fieldAut 3 K σ) := fun h =>
  fieldAut_not_mem_linearAutGroup hσ (innAut_le_linearAutGroup 3 K h)

theorem diagSL_mul_xr01 (a b d : K) (h : a * b * d = 1) (c : K) :
    diagSL a b d h * SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) c =
      SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) (a / b * c) *
        diagSL a b d h := by
  have hb : b ≠ 0 := by rintro rfl; simp at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]
  all_goals field_simp

end Gen

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
