module

public import CFSG.Quasithin.Background.HTriPermute
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin

namespace H

namespace Tri

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type*} [Field K]

section Root

variable {n : ℕ}

@[expose] noncomputable def trGL (i j : Fin n) (h : i ≠ j) (c : K) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j h c]; exact one_ne_zero)

theorem coe_trGL (i j : Fin n) (h : i ≠ j) (c : K) :
    ((trGL i j h c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.transvection i j c :=
  rfl

@[expose] noncomputable def trHom (i j : Fin n) (h : i ≠ j) : Multiplicative K →* GL (Fin n) K
    where
  toFun c := trGL i j h (Multiplicative.toAdd c)
  map_one' := Units.ext (by rw [coe_trGL, toAdd_one, transvection_zero i j, Units.val_one])
  map_mul' a b := Units.ext (by
    rw [Units.val_mul, coe_trGL, coe_trGL, coe_trGL, toAdd_mul]
    exact (transvection_mul_transvection_same i j h _ _).symm)

theorem trHom_apply (i j : Fin n) (h : i ≠ j) (c : Multiplicative K) :
    trHom i j h c = trGL i j h (Multiplicative.toAdd c) := rfl

theorem trGL_apply_same (i j : Fin n) (h : i ≠ j) (c : K) :
    ((trGL i j h c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = c := by
  rw [coe_trGL, transvection, Matrix.add_apply, one_apply_ne h, single_apply_same, zero_add]

theorem trHom_injective (i j : Fin n) (h : i ≠ j) : Function.Injective (trHom (K := K) i j h) := by
  intro a b hab
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) hab
  simp only [trHom_apply, trGL_apply_same] at this
  exact this

noncomputable abbrev rootGL (i j : Fin n) (h : i ≠ j) : Subgroup (GL (Fin n) K) :=
  (trHom i j h).range

theorem mem_rootGL {i j : Fin n} {h : i ≠ j} {g : GL (Fin n) K} :
    g ∈ rootGL i j h ↔ ∃ c : K, g = trGL i j h c :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩,
    fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem rootGL_comm {i j : Fin n} {h : i ≠ j} :
    ∀ a ∈ rootGL (K := K) i j h, ∀ b ∈ rootGL (K := K) i j h, a * b = b * a := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem rootGL_mul_self [CharP K 2] {i j : Fin n} {h : i ≠ j} :
    ∀ e ∈ rootGL (K := K) i j h, e * e = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_mul, ← map_one (trHom (K := K) i j h)]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]

theorem card_rootGL (i j : Fin n) (h : i ≠ j) :
    Nat.card (rootGL (K := K) i j h) = Nat.card K :=
  (Nat.card_congr (MonoidHom.ofInjective (trHom_injective (K := K) i j h)).toEquiv).symm

theorem entry_eq_zero_of_commute {i j : Fin n} {c : K} (hc : c ≠ 0)
    {b : Matrix (Fin n) (Fin n) K} (hb : transvection i j c * b = b * transvection i j c) :
    (∀ r, r ≠ i → b r i = 0) ∧ ∀ s, s ≠ j → b j s = 0 := by
  constructor
  · intro r hr
    have h1 := congrFun (congrFun hb r) j
    rw [transvection_mul_apply_of_ne i j r j hr, mul_transvection_apply_same] at h1
    have h2 : c * b r i = 0 := left_eq_add.mp h1
    exact (mul_eq_zero.mp h2).resolve_left hc
  · intro s hs
    have h1 := congrFun (congrFun hb i) s
    rw [transvection_mul_apply_same, mul_transvection_apply_of_ne i j i s hs] at h1
    have h2 : c * b j s = 0 := (add_eq_left.mp h1)
    exact (mul_eq_zero.mp h2).resolve_left hc

theorem ne_zero_of_trGL_ne_one {i j : Fin n} {h : i ≠ j} {c : K} (hc : trGL i j h c ≠ 1) :
    c ≠ 0 := by
  rintro rfl
  apply hc
  apply Units.ext
  rw [coe_trGL, transvection_zero i j, Units.val_one]

end Root

@[expose] def borGL (n : ℕ) (K : Type*) [Field K] : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K).IsUpperTriangular}
  mul_mem' := fun {a b} ha hb => by
    change ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular
    rw [Units.val_mul]
    exact BlockTriangular.mul ha hb
  one_mem' := by
    change ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular
    rw [Units.val_one]
    exact blockTriangular_one
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular
    have := a.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular ha

theorem mem_borGL {n : ℕ} {g : GL (Fin n) K} :
    g ∈ borGL n K ↔ ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) K) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

theorem mem_borGL_two {g : GL (Fin 2) K} :
    g ∈ borGL 2 K ↔ (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [mem_borGL]
  refine ⟨fun h => h 1 0 (by decide), fun h i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact h

theorem mem_borGL_three {g : GL (Fin 3) K} :
    g ∈ borGL 3 K ↔ (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  rw [mem_borGL]
  refine ⟨fun h => ⟨h 1 0 (by decide), h 2 0 (by decide), h 2 1 (by decide)⟩,
    fun ⟨h1, h2, h3⟩ i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

noncomputable abbrev uni2 (K : Type*) [Field K] : Subgroup (GL (Fin 2) K) :=
  rootGL (0 : Fin 2) 1 (by decide)

theorem triangular_two [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {B : Subgroup (GL (Fin 2) K)}
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 2) K)) * (uni2 K : Set (GL (Fin 2) K)) =
      (uni2 K : Set (GL (Fin 2) K)) * B) : B ≤ borGL 2 K := by
  have hU : IsPGroup 2 (uni2 K) := fun g =>
    ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (rootGL_mul_self _ g.2)⟩
  rcases exists_normal_or_le_normalizer hBab hBodd hU hBU with ⟨O, hO1, hOU, hON⟩ | hN
  · obtain ⟨o, ho1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO1
    obtain ⟨c, hc⟩ := mem_rootGL.mp (hOU o.2)
    have hc0 : c ≠ 0 := ne_zero_of_trGL_ne_one (by
      rw [← hc]
      exact fun h => ho1 (Subtype.ext h))
    intro b hb
    have hbN := hON (le_sup_left (b := uni2 K) hb)
    have h1 : b * o * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hbN o).mp o.2
    obtain ⟨d, hd⟩ := mem_rootGL.mp (hOU h1)
    have h2 : (b : Matrix (Fin 2) (Fin 2) K) * transvection 0 1 c =
        transvection 0 1 d * (b : Matrix (Fin 2) (Fin 2) K) := by
      have h3 : b * (o : GL (Fin 2) K) = trGL 0 1 (by decide) d * b := by
        rw [← hd]
        group
      have h4 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h3
      simp only [Units.val_mul, hc, coe_trGL] at h4
      exact h4
    have h5 := congrFun (congrFun h2 1) 1
    rw [mul_transvection_apply_same, transvection_mul_apply_of_ne 0 1 1 1 (by decide)] at h5
    have h6 : c * (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := add_eq_left.mp h5
    rw [mem_borGL_two]
    exact (mul_eq_zero.mp h6).resolve_left hc0
  · refine le_of_commute (E := uni2 K) hN rootGL_comm rootGL_mul_self
      (by rw [card_rootGL]; exact hK) hBodd ?_
    intro e he he1 b _ heb
    obtain ⟨c, rfl⟩ := mem_rootGL.mp he
    have hc0 := ne_zero_of_trGL_ne_one he1
    have h1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) heb
    simp only [Units.val_mul, coe_trGL] at h1
    rw [mem_borGL_two]
    exact (entry_eq_zero_of_commute hc0 h1).1 1 (by decide)

theorem map_le_borGL_two [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ}
    {Q B U : Subgroup (GL (Fin m) K)} (ψ : ↥Q →* GL (Fin 2) K) (hBQ : B ≤ Q) (hUQ : U ≤ Q)
    (hψU : (U.subgroupOf Q).map ψ = uni2 K) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin m) K)) * (U : Set (GL (Fin m) K)) = (U : Set (GL (Fin m) K)) * B) :
    (B.subgroupOf Q).map ψ ≤ borGL 2 K := by
  refine triangular_two hK ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBab _ ha _ hb)
  · have h1 : Nat.card (B.subgroupOf Q) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
    exact Odd.of_dvd_nat (h1 ▸ hBodd) (Subgroup.card_map_dvd _ _)
  · rw [← hψU, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul,
      subgroupOf_mul_comm hBQ hUQ hBU]

@[expose] noncomputable def uni3 (K : Type*) [Field K] : Subgroup (GL (Fin 3) K) :=
  (LinearFlag.unitriangular 3 K).map Matrix.SpecialLinearGroup.toGL

theorem uni3_entries {g : GL (Fin 3) K} (hg : g ∈ uni3 K) :
    (∀ i j : Fin 3, j < i → (g : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
      ∀ i : Fin 3, (g : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
  obtain ⟨u, hu, rfl⟩ := hg
  exact LinearFlag.mem_unitriangular.mp hu

theorem trGL_mem_uni3 {i j : Fin 3} (hij : i < j) (c : K) : trGL i j hij.ne c ∈ uni3 K := by
  let u : SpecialLinearGroup (Fin 3) K :=
    ⟨transvection i j c, det_transvection_of_ne i j hij.ne c⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, LinearFlag.mem_unitriangular]
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · change transvection i j c a b = 0
    rw [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hba), zero_add,
      single_apply_of_ne _ _ _ _ _ (by
        rintro ⟨rfl, rfl⟩
        exact absurd (hij.trans hba) (lt_irrefl _))]
  · change transvection i j c a a = 1
    rw [transvection, Matrix.add_apply, one_apply_eq,
      single_apply_of_ne _ _ _ _ _ (by
        rintro ⟨rfl, h⟩
        exact hij.ne h.symm), add_zero]

theorem rootGL_le_uni3 : rootGL (K := K) (0 : Fin 3) 2 (by decide) ≤ uni3 K := by
  rintro _ ⟨c, rfl⟩
  exact trGL_mem_uni3 (i := 0) (j := 2) (by decide) _

theorem card_uni3 [Finite K] : Nat.card (uni3 K) = Nat.card K ^ 3 := by
  rw [uni3, Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective,
    LinearFlag.card_unitriangular]

theorem isPGroup_uni3 [Finite K] [CharP K 2] : IsPGroup 2 (uni3 K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  refine IsPGroup.of_card (n := 3 * k) ?_
  rw [card_uni3, Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]

theorem stab_of_normal {Q O : Subgroup (GL (Fin 3) K)} (hUQ : uni3 K ≤ Q) (hO1 : O ≠ ⊥)
    (hOU : O ≤ uni3 K) (hQN : Q ≤ Subgroup.normalizer (O : Set (GL (Fin 3) K))) :
    (∀ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) ∨
      ∀ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  classical
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {v | ∀ o ∈ O, (o : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
      add_mem' := fun {v w} hv hw o ho => by rw [mulVec_add, hv o ho, hw o ho]
      zero_mem' := fun o _ => mulVec_zero _
      smul_mem' := fun c v hv o ho => by rw [mulVec_smul, hv o ho] }
  have hmemW : ∀ {v : Fin 3 → K}, v ∈ W ↔ ∀ o ∈ O, (o : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v :=
    Iff.rfl
  have hpres : ∀ g ∈ Subgroup.normalizer (O : Set (GL (Fin 3) K)), ∀ v ∈ W,
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro g hg v hv
    rw [hmemW]
    intro o ho
    have h1 : g⁻¹ * o * g ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) o).mp ho
      simpa using this
    have h2 := hmemW.mp hv _ h1
    have h3 : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ * o * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (o : Matrix (Fin 3) (Fin 3) K) * g := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    calc (o : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (((g⁻¹ * o * g : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by rw [mulVec_mulVec, mulVec_mulVec, h3]
      _ = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by rw [h2]
  have hinv : ∀ u ∈ LinearFlag.unitriangular 3 K, ∀ v ∈ W,
      (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := fun u hu v hv =>
    hpres (Matrix.SpecialLinearGroup.toGL u) (hQN (hUQ ⟨u, hu, rfl⟩)) v hv
  obtain ⟨m, -, hWm⟩ := LinearFlag.eq_flagSpace_of_invariant hinv
  have hcol : ∀ (M : Matrix (Fin 3) (Fin 3) K) (j i : Fin 3),
      (M *ᵥ Pi.single j 1) i = M i j := fun M j i => by
    rw [mulVec_single_one]
    rfl
  have he0 : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
    rw [hmemW]
    intro o ho
    obtain ⟨hlow, hdiag⟩ := uni3_entries (hOU ho)
    ext i
    rw [hcol]
    fin_cases i
    · simpa using hdiag 0
    · simpa using hlow 1 0 (by decide)
    · simpa using hlow 2 0 (by decide)
  have hWtop : ∃ v, v ∉ W := by
    by_contra h
    push Not at h
    apply hO1
    rw [eq_bot_iff]
    intro o ho
    rw [Subgroup.mem_bot]
    apply Units.ext
    ext i j
    have h1 := congrFun (hmemW.mp (h (Pi.single j 1)) o ho) i
    rw [hcol] at h1
    rw [h1, Units.val_one, one_apply, Pi.single_apply]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [LinearFlag.flagSpace_zero] at hWm
    have h1 : (Pi.single 0 1 : Fin 3 → K) ∈ (⊥ : Submodule K (Fin 3 → K)) := hWm ▸ he0
    rw [Submodule.mem_bot] at h1
    have := congrFun h1 0
    simp at this
  have hm2 : m ≤ 2 := by
    by_contra hm
    obtain ⟨v, hv⟩ := hWtop
    apply hv
    rw [hWm, LinearFlag.mem_flagSpace]
    intro j hj
    have := j.2
    omega
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl
  · left
    intro g hg
    have h := hpres g (hQN hg) _ he0
    rw [hWm, LinearFlag.mem_flagSpace] at h
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    rw [hcol] at h1 h2
    exact ⟨h1, h2⟩
  · right
    have he1 : (Pi.single 1 1 : Fin 3 → K) ∈ W := by
      rw [hWm, LinearFlag.mem_flagSpace]
      intro j hj
      have hj2 : j = 2 := by
        have := j.2
        ext
        simp only [Fin.val_two]
        omega
      rw [hj2]
      exact Pi.single_eq_of_ne (by decide) _
    intro g hg
    have h0 := hpres g (hQN hg) _ he0
    have h1 := hpres g (hQN hg) _ he1
    rw [hWm, LinearFlag.mem_flagSpace] at h0 h1
    have h0' := h0 2 (by norm_num)
    have h1' := h1 2 (by norm_num)
    rw [hcol] at h0' h1'
    exact ⟨h0', h1'⟩

@[expose] def lowerMat (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => g i.succ j.succ

@[expose] def upperMat (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => g i.castSucc j.castSucc

theorem lowerMat_mul {g h : Matrix (Fin 3) (Fin 3) K} (hg : g 1 0 = 0 ∧ g 2 0 = 0) :
    lowerMat (g * h) = lowerMat g * lowerMat h := by
  ext i j
  simp only [lowerMat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_succ (n := 2)]
  have : g i.succ 0 = 0 := by fin_cases i <;> simp [hg.1, hg.2]
  rw [this, zero_mul, zero_add]

theorem upperMat_mul {g h : Matrix (Fin 3) (Fin 3) K} (hh : h 2 0 = 0 ∧ h 2 1 = 0) :
    upperMat (g * h) = upperMat g * upperMat h := by
  ext i j
  simp only [upperMat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_castSucc (n := 2)]
  have : h (Fin.last 2) j.castSucc = 0 := by fin_cases j <;> simp [hh.1, hh.2]
  rw [this, mul_zero, add_zero]

theorem lowerMat_one : lowerMat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  simp [lowerMat, Matrix.one_apply, Fin.succ_inj]

theorem upperMat_one : upperMat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  simp [upperMat, Matrix.one_apply, Fin.castSucc_inj]

@[expose] def lowerHom {Q : Subgroup (GL (Fin 3) K)}
    (hQ : ∀ g ∈ Q,
      (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) :
    ↥Q →* GL (Fin 2) K where
  toFun g :=
    { val := lowerMat ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      inv := lowerMat (((g : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      val_inv := by
        rw [← lowerMat_mul (hQ _ g.2), ← Units.val_mul, mul_inv_cancel, Units.val_one,
          lowerMat_one]
      inv_val := by
        rw [← lowerMat_mul (hQ _ (Q.inv_mem g.2)), ← Units.val_mul, inv_mul_cancel,
          Units.val_one, lowerMat_one] }
  map_one' := Units.ext (by
    change lowerMat ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Units.val_one, lowerMat_one])
  map_mul' a b := Units.ext (by
    change lowerMat (((a * b : ↥Q) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lowerMat ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        lowerMat ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Subgroup.coe_mul, Units.val_mul, lowerMat_mul (hQ _ a.2)])

@[expose] def upperHom {Q : Subgroup (GL (Fin 3) K)}
    (hQ : ∀ g ∈ Q,
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    ↥Q →* GL (Fin 2) K where
  toFun g :=
    { val := upperMat ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      inv := upperMat (((g : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      val_inv := by
        rw [← upperMat_mul (hQ _ (Q.inv_mem g.2)), ← Units.val_mul, mul_inv_cancel,
          Units.val_one, upperMat_one]
      inv_val := by
        rw [← upperMat_mul (hQ _ g.2), ← Units.val_mul, inv_mul_cancel, Units.val_one,
          upperMat_one] }
  map_one' := Units.ext (by
    change upperMat ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Units.val_one, upperMat_one])
  map_mul' a b := Units.ext (by
    change upperMat (((a * b : ↥Q) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      upperMat ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        upperMat ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Subgroup.coe_mul, Units.val_mul, upperMat_mul (hQ _ b.2)])

theorem lowerMat_eq_of_mem_uni3 {u : GL (Fin 3) K} (hu : u ∈ uni3 K) :
    lowerMat (u : Matrix (Fin 3) (Fin 3) K) =
      transvection (0 : Fin 2) 1 ((u : Matrix (Fin 3) (Fin 3) K) 1 2) := by
  obtain ⟨hlow, hdiag⟩ := uni3_entries hu
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [lowerMat, transvection] using hdiag 1
  · simp [lowerMat, transvection]
  · simpa [lowerMat, transvection] using hlow 2 1 (by decide)
  · simpa [lowerMat, transvection] using hdiag 2

theorem upperMat_eq_of_mem_uni3 {u : GL (Fin 3) K} (hu : u ∈ uni3 K) :
    upperMat (u : Matrix (Fin 3) (Fin 3) K) =
      transvection (0 : Fin 2) 1 ((u : Matrix (Fin 3) (Fin 3) K) 0 1) := by
  obtain ⟨hlow, hdiag⟩ := uni3_entries hu
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [upperMat, transvection] using hdiag 0
  · simp [upperMat, transvection]
  · simpa [upperMat, transvection] using hlow 1 0 (by decide)
  · simpa [upperMat, transvection] using hdiag 1

theorem map_lowerHom_uni3 {Q : Subgroup (GL (Fin 3) K)}
    (hQ : ∀ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (hUQ : uni3 K ≤ Q) : ((uni3 K).subgroupOf Q).map (lowerHom hQ) = uni2 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    refine mem_rootGL.mpr ⟨((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2, ?_⟩
    apply Units.ext
    exact lowerMat_eq_of_mem_uni3 hu
  · rintro _ ⟨c, rfl⟩
    have hmem := trGL_mem_uni3 (i := 1) (j := 2) (by decide) (Multiplicative.toAdd c)
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    have h1 := lowerMat_eq_of_mem_uni3 hmem
    rw [trGL_apply_same] at h1
    exact h1

theorem map_upperHom_uni3 {Q : Subgroup (GL (Fin 3) K)}
    (hQ : ∀ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (hUQ : uni3 K ≤ Q) : ((uni3 K).subgroupOf Q).map (upperHom hQ) = uni2 K := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    refine mem_rootGL.mpr ⟨((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1, ?_⟩
    apply Units.ext
    exact upperMat_eq_of_mem_uni3 hu
  · rintro _ ⟨c, rfl⟩
    have hmem := trGL_mem_uni3 (i := 0) (j := 1) (by decide) (Multiplicative.toAdd c)
    refine ⟨⟨_, hUQ hmem⟩, hmem, ?_⟩
    apply Units.ext
    have h1 := upperMat_eq_of_mem_uni3 hmem
    rw [trGL_apply_same] at h1
    exact h1

theorem triangular_three [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {B : Subgroup (GL (Fin 3) K)} (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 3) K)) * (uni3 K : Set (GL (Fin 3) K)) =
      (uni3 K : Set (GL (Fin 3) K)) * B) :
    B ≤ borGL 3 K := by
  rcases exists_normal_or_le_normalizer hBab hBodd isPGroup_uni3 hBU with
    ⟨O, hO1, hOU, hON⟩ | hN
  · rcases stab_of_normal le_sup_right hO1 hOU hON with h1 | h2
    · intro b hb
      have hbQ : b ∈ B ⊔ uni3 K := le_sup_left (b := uni3 K) hb
      obtain ⟨hb10, hb20⟩ := h1 b hbQ
      have hmap := map_le_borGL_two hK (lowerHom h1) le_sup_left le_sup_right
        (map_lowerHom_uni3 h1 le_sup_right) hBab hBodd hBU
      have hb' : lowerHom h1 ⟨b, hbQ⟩ ∈ borGL 2 K := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
      rw [mem_borGL_two] at hb'
      exact mem_borGL_three.mpr ⟨hb10, hb20, hb'⟩
    · intro b hb
      have hbQ : b ∈ B ⊔ uni3 K := le_sup_left (b := uni3 K) hb
      obtain ⟨hb20, hb21⟩ := h2 b hbQ
      have hmap := map_le_borGL_two hK (upperHom h2) le_sup_left le_sup_right
        (map_upperHom_uni3 h2 le_sup_right) hBab hBodd hBU
      have hb' : upperHom h2 ⟨b, hbQ⟩ ∈ borGL 2 K := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
      rw [mem_borGL_two] at hb'
      exact mem_borGL_three.mpr ⟨hb', hb20, hb21⟩
  · refine le_of_commute (E := rootGL (0 : Fin 3) 2 (by decide)) (rootGL_le_uni3.trans hN)
      rootGL_comm rootGL_mul_self (by rw [card_rootGL]; exact hK) hBodd ?_
    intro e he he1 b _ heb
    obtain ⟨c, rfl⟩ := mem_rootGL.mp he
    have hc0 := ne_zero_of_trGL_ne_one he1
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) heb
    simp only [Units.val_mul, coe_trGL] at h1
    obtain ⟨hr, hs⟩ := entry_eq_zero_of_commute hc0 h1
    exact mem_borGL_three.mpr ⟨hr 1 (by decide), hr 2 (by decide), hs 1 (by decide)⟩

end Tri

end H

end CFSG.Quasithin
