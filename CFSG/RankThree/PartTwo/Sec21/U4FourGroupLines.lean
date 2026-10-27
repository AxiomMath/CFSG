module

public import CFSG.RankThree.PartTwo.Sec21.Star22
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)

@[expose] def U4FourGroupLines (b : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), Nonempty (Y ≃* projSU 4 2 b) →
    ∀ F ℓ : Subgroup G, F ≤ Y → IsElemAbelian 3 F → ℓ ≤ F → Nat.card ℓ = 3 →
      ∃ U : Subgroup G, U ≤ Y ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
        F ≤ Subgroup.normalizer (U : Set G) ∧ F ⊓ Subgroup.centralizer (U : Set G) = ℓ

namespace U4FourLines

open Matrix
open CFSG.LieType.Universal.Unitary (SU mem_SU conjTr antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Comb_four exists_conj_into_d8Tor_su)
open U4Lines (torusD coe_torusD line_cases card_rootsOfUnity_three
  unitaryInvolution_rootsOfUnity eq_one_or_eq_or_eq_inv antidiag_four mapL embedOf mapL_le
  mapL_mono card_mapL mapL_conj card_galoisField_two_mul nonempty_projSU_mulEquiv_SU
  embedOf_injective mapLEquiv)

section Root

variable {F : Type} [Field F]

@[expose] def rootUnit (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0) (t : F) :
    GL (Fin 4) F :=
  ⟨1 + t • N, 1 - t • N, by
    rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hN, smul_zero, sub_zero,
      sub_add_cancel],
   by
    rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hN, smul_zero, add_zero,
      add_sub_cancel_right]⟩

theorem coe_rootUnit (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0) (t : F) :
    ((rootUnit N hN t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 + t • N := rfl

@[expose] def rootHom (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0) :
    Multiplicative F →* GL (Fin 4) F where
  toFun t := rootUnit N hN (Multiplicative.toAdd t)
  map_one' := Units.ext (by simp [coe_rootUnit])
  map_mul' s t := Units.ext (by
    simp only [coe_rootUnit, Units.val_mul, toAdd_mul]
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hN, smul_zero, add_zero,
      add_smul]
    abel)

theorem coe_rootHom (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0) (t : F) :
    ((rootHom N hN (Multiplicative.ofAdd t) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 + t • N := rfl

theorem rootHom_injective {N : Matrix (Fin 4) (Fin 4) F} (hN : N * N = 0) {i j : Fin 4}
    (hij : N i j = 1) : Function.Injective (rootHom N hN) := by
  intro s t h
  have h' := congrFun (congrFun (congrArg
    (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) h) i) j
  rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, coe_rootHom, coe_rootHom] at h'
  simp only [Matrix.add_apply, Matrix.smul_apply, hij, smul_eq_mul, mul_one,
    add_right_inj] at h'
  rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, h']

theorem rootHom_sq [CharP F 2] (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0)
    (t : Multiplicative F) : rootHom N hN t ^ 2 = 1 := by
  rw [sq, ← map_mul, ← map_one (rootHom N hN)]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one, ← two_mul, CharTwo.two_eq_zero, zero_mul]

theorem det_rootHom [CharP F 2] (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0)
    (t : Multiplicative F) :
    ((rootHom N hN t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have h2 := congrArg (fun x : GL (Fin 4) F => ((x : Matrix (Fin 4) (Fin 4) F)).det)
    (rootHom_sq N hN t)
  simp only [Units.val_pow_eq_pow_val, det_pow, Units.val_one, det_one] at h2
  have h3 : (((rootHom N hN t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det - 1) ^ 2 = 0 := by
    rw [sub_sq, h2, mul_one, one_pow, CharTwo.two_eq_zero, zero_mul, sub_zero,
      CharTwo.add_self_eq_zero]
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3)

end Root

section Four

variable {F : Type} [Field F] [CharP F 2]

@[expose] def fourAdd (ω : F) : ZMod 2 × ZMod 2 →+ F :=
  (ZMod.castHom (dvd_refl 2) F).toAddMonoidHom.coprod
    ((AddMonoidHom.mulRight ω).comp (ZMod.castHom (dvd_refl 2) F).toAddMonoidHom)

theorem fourAdd_apply (ω : F) (p : ZMod 2 × ZMod 2) :
    fourAdd ω p = ZMod.castHom (dvd_refl 2) F p.1 + ZMod.castHom (dvd_refl 2) F p.2 * ω := rfl

theorem mul_fourAdd {ω : F} (hω : ω ^ 2 = ω + 1) (p : ZMod 2 × ZMod 2) :
    ω * fourAdd ω p = fourAdd ω (p.2, p.1 + p.2) := by
  simp only [fourAdd_apply, map_add]
  linear_combination (ZMod.castHom (dvd_refl 2) F p.2) * hω

theorem fourAdd_injective {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    Function.Injective (fourAdd ω) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨i, j⟩ h
  rw [fourAdd_apply] at h
  have h11 : (1 : F) + ω ≠ 0 := fun h' => hω1 (by
    have := eq_neg_of_add_eq_zero_right h'
    rw [this, CharTwo.neg_eq])
  have h01 : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
  rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl <;>
    simp only [map_zero, map_one, zero_mul, one_mul, zero_add, add_zero] at h
  · rfl
  · exact absurd h hω0
  · exact absurd h one_ne_zero
  · exact absurd h h11

@[expose] def rootFour (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0) (ω : F) :
    Subgroup (GL (Fin 4) F) :=
  ((rootHom N hN).comp (AddMonoidHom.toMultiplicative (fourAdd ω))).range

theorem mem_rootFour {N : Matrix (Fin 4) (Fin 4) F} {hN : N * N = 0} {ω : F}
    {x : GL (Fin 4) F} :
    x ∈ rootFour N hN ω ↔ ∃ p, rootHom N hN (Multiplicative.ofAdd (fourAdd ω p)) = x := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Multiplicative.toAdd p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨Multiplicative.ofAdd p, rfl⟩

theorem card_rootFour {N : Matrix (Fin 4) (Fin 4) F} (hN : N * N = 0) {i j : Fin 4}
    (hij : N i j = 1) {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    Nat.card (rootFour N hN ω) = 4 := by
  have hinj : Function.Injective
      ((rootHom N hN).comp (AddMonoidHom.toMultiplicative (fourAdd ω))) :=
    (rootHom_injective hN hij).comp (fun p q h => (fourAdd_injective hω0 hω1)
      (Multiplicative.ofAdd.injective h))
  rw [rootFour, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem isElemAbelian_rootFour (N : Matrix (Fin 4) (Fin 4) F) (hN : N * N = 0) (ω : F) :
    IsElemAbelian 2 (rootFour N hN ω) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨p, hp⟩ := mem_rootFour.mp x.2
    obtain ⟨q, hq⟩ := mem_rootFour.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul (rootHom N hN),
      ← map_mul (rootHom N hN), mul_comm (Multiplicative.ofAdd (fourAdd ω p))]
  · obtain ⟨p, rfl⟩ := mem_rootFour.mp hx
    exact rootHom_sq N hN _

end Four

section Torus

variable {F : Type} [Field F] [CharP F 2]

theorem sq_eq_add_one {a : F} (h3 : a ^ 3 = 1) (h1 : a ≠ 1) : a ^ 2 = a + 1 := by
  have h : (a - 1) * (a ^ 2 + a + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · linear_combination h - (a + 1) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem exists_mul_fourAdd {a : F} (h3 : a ^ 3 = 1) (h1 : a ≠ 1) {μ : F}
    (hμ : μ = 1 ∨ μ = a ∨ μ = a⁻¹) (p : ZMod 2 × ZMod 2) :
    ∃ q, μ * fourAdd a p = fourAdd a q := by
  have h2 := sq_eq_add_one h3 h1
  rcases hμ with rfl | rfl | rfl
  · exact ⟨p, one_mul _⟩
  · exact ⟨_, mul_fourAdd h2 p⟩
  · have hinv : a⁻¹ = a * a := (eq_inv_of_mul_eq_one_left (by rw [← h3]; ring)).symm
    exact ⟨_, by rw [hinv, mul_assoc, mul_fourAdd h2, mul_fourAdd h2]⟩

theorem torus_le_normalizer_rootFour {N : Matrix (Fin 4) (Fin 4) F} (hN : N * N = 0)
    {ω : rootsOfUnity 3 F} (hμ : Nat.card (rootsOfUnity 3 F) = 3) (hω : ω ≠ 1)
    (χ : D8Mod 3 F →* rootsOfUnity 3 F)
    (hconj : ∀ v (t : F), torusD v * rootHom N hN (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom N hN (Multiplicative.ofAdd (((χ v : Fˣ) : F) * t))) :
    d8Tor 3 F 4 ≤ Subgroup.normalizer (rootFour N hN ((ω : Fˣ) : F) : Set (GL (Fin 4) F)) := by
  have ha3 : ((ω : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : ((ω : Fˣ) : F) ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  refine le_normalizer_of_forall_mul_mem fun x hx y hy => ?_
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := mem_rootFour.mp hy
  change torusD v * _ * (torusD v)⁻¹ ∈ _
  rw [hconj]
  have hμv : ((χ v : Fˣ) : F) = 1 ∨ ((χ v : Fˣ) : F) = ((ω : Fˣ) : F) ∨
      ((χ v : Fˣ) : F) = ((ω : Fˣ) : F)⁻¹ := by
    rcases eq_one_or_eq_or_eq_inv hμ hω (χ v) with h | h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Units.val_inv_eq_inv_val _))
  obtain ⟨q, hq⟩ := exists_mul_fourAdd ha3 ha1 hμv p
  rw [hq]
  exact mem_rootFour.mpr ⟨q, rfl⟩

theorem torusD_mem_centralizer_iff {N : Matrix (Fin 4) (Fin 4) F} (hN : N * N = 0)
    {i j : Fin 4} (hij : N i j = 1) (a : F) (χ : D8Mod 3 F →* rootsOfUnity 3 F)
    (hconj : ∀ v (t : F), torusD v * rootHom N hN (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom N hN (Multiplicative.ofAdd (((χ v : Fˣ) : F) * t))) (v : D8Mod 3 F) :
    torusD v ∈ Subgroup.centralizer (rootFour N hN a : Set (GL (Fin 4) F)) ↔ χ v = 1 := by
  constructor
  · intro h
    have h1 : rootHom N hN (Multiplicative.ofAdd 1) ∈ rootFour N hN a :=
      mem_rootFour.mpr ⟨(1, 0), by simp [fourAdd_apply]⟩
    have hc := Subgroup.mem_centralizer_iff.mp h _ h1
    have h2 : torusD v * rootHom N hN (Multiplicative.ofAdd 1) * (torusD v)⁻¹ =
        rootHom N hN (Multiplicative.ofAdd 1) := by
      rw [← hc, mul_inv_cancel_right]
    rw [hconj, mul_one] at h2
    have h3 := congrArg Multiplicative.toAdd (rootHom_injective hN hij h2)
    rw [toAdd_ofAdd, toAdd_ofAdd] at h3
    exact Subtype.ext (Units.ext h3)
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨p, rfl⟩ := mem_rootFour.mp hy
    have h2 := hconj v (fourAdd a p)
    rw [h, OneMemClass.coe_one, Units.val_one, one_mul] at h2
    calc rootHom N hN (Multiplicative.ofAdd (fourAdd a p)) * torusD v
        = torusD v * rootHom N hN (Multiplicative.ofAdd (fourAdd a p)) * (torusD v)⁻¹ *
            torusD v := by rw [h2]
      _ = torusD v * rootHom N hN (Multiplicative.ofAdd (fourAdd a p)) := by group

theorem fourAdd_fixed (σ : F ≃+* F) {ω : F} (hσ : σ ω = ω) (p : ZMod 2 × ZMod 2) :
    σ (fourAdd ω p) = fourAdd ω p := by
  have hc : ∀ z : ZMod 2, σ (ZMod.castHom (dvd_refl 2) F z) = ZMod.castHom (dvd_refl 2) F z :=
    fun z => DFunLike.congr_fun (RingHom.ext_zmod
      ((σ : F →+* F).comp (ZMod.castHom (dvd_refl 2) F)) (ZMod.castHom (dvd_refl 2) F)) z
  rw [fourAdd_apply, map_add, map_mul, hc, hc, hσ]

theorem exists_rootFour_line {b : ℕ} (hbe : Even b) [Finite F] (hF : Nat.card F = (2 ^ b) ^ 2)
    {N : Matrix (Fin 4) (Fin 4) F} (hN : N * N = 0) {i j : Fin 4} (hij : N i j = 1)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) (χ : D8Mod 3 F →* rootsOfUnity 3 F)
    (hconj : ∀ v (t : F), torusD v * rootHom N hN (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom N hN (Multiplicative.ofAdd (((χ v : Fˣ) : F) * t)))
    (hSU : ∀ t : F, unitaryInvolution F 2 b t = t →
      rootHom N hN (Multiplicative.ofAdd t) ∈ SU (unitaryInvolution F 2 b) 4)
    (w : D8Mod 3 F) (hw : χ w = 1) (hker : ∀ v, χ v = 1 → v ∈ Subgroup.zpowers w) :
    ∃ U : Subgroup (GL (Fin 4) F), U ≤ SU (unitaryInvolution F 2 b) 4 ∧ IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ d8Tor 3 F 4 ≤ Subgroup.normalizer (U : Set (GL (Fin 4) F)) ∧
      d8Tor 3 F 4 ⊓ Subgroup.centralizer (U : Set (GL (Fin 4) F)) =
        Subgroup.zpowers (torusD w) := by
  have hμ := card_rootsOfUnity_three hbe hF
  have ha3 : ((ω : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : ((ω : Fˣ) : F) ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : ((ω : Fˣ) : F) ≠ 0 := Units.ne_zero _
  refine ⟨rootFour N hN ((ω : Fˣ) : F), ?_, isElemAbelian_rootFour N hN _,
    card_rootFour hN hij ha0 ha1, torus_le_normalizer_rootFour hN hμ hω χ hconj, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := mem_rootFour.mp hx
    exact hSU _ (fourAdd_fixed _ (unitaryInvolution_rootsOfUnity hbe ω) p)
  · have hC := torusD_mem_centralizer_iff hN hij ((ω : Fˣ) : F) χ hconj
    ext x
    constructor
    · rintro ⟨⟨v, rfl⟩, hxC⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hker v ((hC v).mp hxC))
      exact ⟨k, (map_zpow torusD w k).symm⟩
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨⟨w ^ k, map_zpow torusD w k⟩, Subgroup.zpow_mem _ ((hC w).mpr hw) k⟩

end Torus

section Cases

variable {F : Type} [Field F]

@[expose] def nL : Matrix (Fin 4) (Fin 4) F := !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def nL' : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def nS : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]

@[expose] def nS' : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

theorem nL_mul_self : (nL : Matrix (Fin 4) (Fin 4) F) * nL = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nL, Matrix.mul_apply, Fin.sum_univ_four]

theorem nL'_mul_self : (nL' : Matrix (Fin 4) (Fin 4) F) * nL' = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nL', Matrix.mul_apply, Fin.sum_univ_four]

theorem nS_mul_self : (nS : Matrix (Fin 4) (Fin 4) F) * nS = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nS, Matrix.mul_apply, Fin.sum_univ_four]

theorem nS'_mul_self : (nS' : Matrix (Fin 4) (Fin 4) F) * nS' = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nS', Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def chiL : D8Mod 3 F →* rootsOfUnity 3 F :=
  MonoidHom.snd _ _ * MonoidHom.snd _ _

@[expose] def chiL' : D8Mod 3 F →* rootsOfUnity 3 F :=
  MonoidHom.fst _ _ * MonoidHom.fst _ _

@[expose] def chiS : D8Mod 3 F →* rootsOfUnity 3 F :=
  MonoidHom.fst _ _ * (MonoidHom.snd _ _)⁻¹

@[expose] def chiS' : D8Mod 3 F →* rootsOfUnity 3 F :=
  MonoidHom.fst _ _ * MonoidHom.snd _ _

theorem conj_nL (v : D8Mod 3 F) (t : F) :
    torusD v * rootHom nL nL_mul_self (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom nL nL_mul_self (Multiplicative.ofAdd (((chiL v : Fˣ) : F) * t)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rootHom, coe_rootHom, ← map_inv, coe_torusD,
    coe_torusD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nL, chiL, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]; ring

theorem conj_nL' (v : D8Mod 3 F) (t : F) :
    torusD v * rootHom nL' nL'_mul_self (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom nL' nL'_mul_self (Multiplicative.ofAdd (((chiL' v : Fˣ) : F) * t)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rootHom, coe_rootHom, ← map_inv, coe_torusD,
    coe_torusD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nL', chiL', Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]; ring

theorem conj_nS (v : D8Mod 3 F) (t : F) :
    torusD v * rootHom nS nS_mul_self (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom nS nS_mul_self (Multiplicative.ofAdd (((chiS v : Fˣ) : F) * t)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rootHom, coe_rootHom, ← map_inv, coe_torusD,
    coe_torusD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nS, chiS, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem conj_nS' (v : D8Mod 3 F) (t : F) :
    torusD v * rootHom nS' nS'_mul_self (Multiplicative.ofAdd t) * (torusD v)⁻¹ =
      rootHom nS' nS'_mul_self (Multiplicative.ofAdd (((chiS' v : Fˣ) : F) * t)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rootHom, coe_rootHom, ← map_inv, coe_torusD,
    coe_torusD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nS', chiS', Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

variable [CharP F 2] (σ : F ≃+* F)

theorem rootHom_nL_mem_SU (t : F) (ht : σ t = t) :
    rootHom nL nL_mul_self (Multiplicative.ofAdd t) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_rootHom _ _ _, ?_⟩
  rw [coe_rootHom, antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nL, conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, ht,
      CharTwo.add_self_eq_zero]

theorem rootHom_nL'_mem_SU (t : F) (ht : σ t = t) :
    rootHom nL' nL'_mul_self (Multiplicative.ofAdd t) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_rootHom _ _ _, ?_⟩
  rw [coe_rootHom, antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nL', conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, ht,
      CharTwo.add_self_eq_zero]

theorem rootHom_nS_mem_SU (t : F) (ht : σ t = t) :
    rootHom nS nS_mul_self (Multiplicative.ofAdd t) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_rootHom _ _ _, ?_⟩
  rw [coe_rootHom, antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nS, conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, ht,
      CharTwo.add_self_eq_zero]

theorem rootHom_nS'_mem_SU (t : F) (ht : σ t = t) :
    rootHom nS' nS'_mul_self (Multiplicative.ofAdd t) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_rootHom _ _ _, ?_⟩
  rw [coe_rootHom, antidiag_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nS', conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, ht,
      CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem eq_one_of_mul_self (hμ : Nat.card (rootsOfUnity 3 F) = 3) {u : rootsOfUnity 3 F}
    (h : u * u = 1) : u = 1 := by
  have h3 : u ^ 3 = 1 := by
    have := pow_card_eq_one' (G := rootsOfUnity 3 F) (x := u)
    rwa [hμ] at this
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [h3, h, inv_one, one_mul]

omit [CharP F 2] in
theorem mem_zpowers_of_chiL (hμ : Nat.card (rootsOfUnity 3 F) = 3) {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) (v : D8Mod 3 F) (hv : chiL v = 1) : v ∈ Subgroup.zpowers ((ω, 1) : D8Mod 3 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : v.2 = 1 := eq_one_of_mul_self hμ hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hμ hω (g' := v.1))
  exact ⟨k, Prod.ext (by simp only [Prod.pow_mk, hk])
    (by simp only [Prod.pow_mk, _root_.one_zpow, h2])⟩

omit [CharP F 2] in
theorem mem_zpowers_of_chiL' (hμ : Nat.card (rootsOfUnity 3 F) = 3) {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) (v : D8Mod 3 F) (hv : chiL' v = 1) :
    v ∈ Subgroup.zpowers ((1, ω) : D8Mod 3 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : v.1 = 1 := eq_one_of_mul_self hμ hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hμ hω (g' := v.2))
  exact ⟨k, Prod.ext (by simp only [Prod.pow_mk, _root_.one_zpow, h1])
    (by simp only [Prod.pow_mk, hk])⟩

omit [CharP F 2] in
theorem mem_zpowers_of_chiS (hμ : Nat.card (rootsOfUnity 3 F) = 3) {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) (v : D8Mod 3 F) (hv : chiS v = 1) : v ∈ Subgroup.zpowers ((ω, ω) : D8Mod 3 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h12 : v.1 = v.2 := mul_inv_eq_one.mp hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hμ hω (g' := v.1))
  exact ⟨k, Prod.ext (by simp only [Prod.pow_mk, hk]) (by simp only [Prod.pow_mk, hk, h12])⟩

omit [CharP F 2] in
theorem mem_zpowers_of_chiS' (hμ : Nat.card (rootsOfUnity 3 F) = 3) {ω : rootsOfUnity 3 F}
    (hω : ω ≠ 1) (v : D8Mod 3 F) (hv : chiS' v = 1) :
    v ∈ Subgroup.zpowers ((ω, ω⁻¹) : D8Mod 3 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h12 : v.2 = v.1⁻¹ := eq_inv_of_mul_eq_one_right hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hμ hω (g' := v.1))
  exact ⟨k, Prod.ext (by simp only [Prod.pow_mk, hk])
    (by simp only [Prod.pow_mk, h12, ← hk, _root_.inv_zpow])⟩

theorem exists_fourGroup_of_le_torus {b : ℕ} (hbe : Even b) [Finite F]
    (hF : Nat.card F = (2 ^ b) ^ 2) {ℓ : Subgroup (GL (Fin 4) F)} (hℓT : ℓ ≤ d8Tor 3 F 4)
    (h3 : Nat.card ℓ = 3) :
    ∃ U : Subgroup (GL (Fin 4) F), U ≤ SU (unitaryInvolution F 2 b) 4 ∧ IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ d8Tor 3 F 4 ≤ Subgroup.normalizer (U : Set (GL (Fin 4) F)) ∧
      d8Tor 3 F 4 ⊓ Subgroup.centralizer (U : Set (GL (Fin 4) F)) = ℓ := by
  have hμ := card_rootsOfUnity_three hbe hF
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  rcases line_cases hμ hω hℓT h3 with rfl | rfl | rfl | rfl
  · exact exists_rootFour_line hbe hF nL_mul_self (i := 1) (j := 2) rfl hω chiL conj_nL
      (rootHom_nL_mem_SU _) (ω, 1) (by simp [chiL]) (mem_zpowers_of_chiL hμ hω)
  · exact exists_rootFour_line hbe hF nL'_mul_self (i := 0) (j := 3) rfl hω chiL' conj_nL'
      (rootHom_nL'_mem_SU _) (1, ω) (by simp [chiL']) (mem_zpowers_of_chiL' hμ hω)
  · exact exists_rootFour_line hbe hF nS_mul_self (i := 0) (j := 1) rfl hω chiS conj_nS
      (rootHom_nS_mem_SU _) (ω, ω) (by simp [chiS]) (mem_zpowers_of_chiS hμ hω)
  · exact exists_rootFour_line hbe hF nS'_mul_self (i := 0) (j := 2) rfl hω chiS' conj_nS'
      (rootHom_nS'_mem_SU _) (ω, ω⁻¹) (by simp [chiS']) (mem_zpowers_of_chiS' hμ hω)

end Cases

section Transport

variable {G G' : Type} [Group G] [Group G']

@[expose] def FourGroupFor (Y F ℓ : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≤ Y ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
    F ≤ Subgroup.normalizer (U : Set G) ∧ F ⊓ Subgroup.centralizer (U : Set G) = ℓ

variable {Y : Subgroup G} {Y' : Subgroup G'} (e : Y ≃* Y')

theorem embedOf_apply (y : Y) : embedOf e y = ((e y : Y') : G') := rfl

theorem embedOf_mem_mapL_iff {Z : Subgroup G} (y : Y) : embedOf e y ∈ mapL e Z ↔ (y : G) ∈ Z := by
  constructor
  · rintro ⟨y', hy', h⟩
    rw [embedOf_injective e h] at hy'
    exact hy'
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem mem_centralizer_mapL_symm_iff {U' : Subgroup G'} (hU' : U' ≤ Y') (y : Y) :
    (y : G) ∈ Subgroup.centralizer (mapL e.symm U' : Set G) ↔
      embedOf e y ∈ Subgroup.centralizer (U' : Set G') := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have h1 := h (embedOf e.symm ⟨z, hU' hz⟩) ⟨⟨z, hU' hz⟩, hz, rfl⟩
    have h2 : e.symm ⟨z, hU' hz⟩ * y = y * e.symm ⟨z, hU' hz⟩ := Subtype.ext h1
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact congrArg Subtype.val h3
  · rintro h _ ⟨z, hz, rfl⟩
    have h1 := h (z : G') hz
    have h2 : z * e y = e y * z := Subtype.ext h1
    have h3 := congrArg e.symm h2
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h3
    exact congrArg Subtype.val h3

theorem isElemAbelian_of_mulEquiv {p : ℕ} {U : Subgroup G} {U' : Subgroup G'} (φ : U' ≃* U)
    (h : IsElemAbelian p U') : IsElemAbelian p U := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have hc := h.1.is_comm.comm (φ.symm x) (φ.symm y)
    have := congrArg φ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  · have h1 : (φ.symm ⟨x, hx⟩ : G') ^ p = 1 := h.2 _ (φ.symm ⟨x, hx⟩).2
    have h2 : φ.symm ⟨x, hx⟩ ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
    have h3 := congrArg φ h2
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h3
    exact congrArg Subtype.val h3

theorem fourGroupFor_of_mapL [Finite G] [Finite G'] {F ℓ : Subgroup G} (hFY : F ≤ Y)
    (hℓF : ℓ ≤ F) (h : FourGroupFor Y' (mapL e F) (mapL e ℓ)) : FourGroupFor Y F ℓ := by
  obtain ⟨U', hU'Y, hU'e, hU'4, hFN, hFC⟩ := h
  refine ⟨mapL e.symm U', mapL_le e.symm U',
    isElemAbelian_of_mulEquiv (mapLEquiv e.symm hU'Y) hU'e,
    by rw [card_mapL e.symm hU'Y, hU'4], ?_, ?_⟩
  · refine le_normalizer_of_forall_mul_mem fun x hx u hu => ?_
    obtain ⟨z, hz, rfl⟩ := hu
    have hxF : embedOf e ⟨x, hFY hx⟩ ∈ mapL e F := (embedOf_mem_mapL_iff e _).mpr hx
    have hconj := (Subgroup.mem_normalizer_iff.mp (hFN hxF) (z : G')).mp hz
    have heq : x * embedOf e.symm z * x⁻¹ =
        embedOf e.symm (e ⟨x, hFY hx⟩ * z * (e ⟨x, hFY hx⟩)⁻¹) := by
      rw [embedOf_apply, embedOf_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    rw [heq]
    exact ⟨_, hconj, rfl⟩
  · ext x
    constructor
    · rintro ⟨hxF, hxC⟩
      have hC := (mem_centralizer_mapL_symm_iff e hU'Y ⟨x, hFY hxF⟩).mp hxC
      have hmem : embedOf e ⟨x, hFY hxF⟩ ∈ mapL e ℓ :=
        hFC ▸ ⟨(embedOf_mem_mapL_iff e _).mpr hxF, hC⟩
      exact (embedOf_mem_mapL_iff e _).mp hmem
    · intro hxℓ
      have hxF := hℓF hxℓ
      have hmem : embedOf e ⟨x, hFY hxF⟩ ∈ mapL e F ⊓ Subgroup.centralizer (U' : Set G') :=
        hFC ▸ (embedOf_mem_mapL_iff e _).mpr hxℓ
      exact ⟨hxF, (mem_centralizer_mapL_symm_iff e hU'Y ⟨x, hFY hxF⟩).mpr hmem.2⟩

theorem pow_three_of_mem_mapL {F : Subgroup G} (hF : ∀ x ∈ F, x ^ 3 = 1) :
    ∀ x ∈ mapL e F, x ^ 3 = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact hF _ hy),
    map_one]

end Transport

section KFact

variable {b : ℕ}

theorem fourGroupFor_SU (hb : 0 < b) (hbe : Even b)
    {F ℓ : Subgroup (GL (Fin 4) (GaloisField 2 (2 * b)))}
    (hFY : F ≤ SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) (hF3 : ∀ x ∈ F, x ^ 3 = 1)
    (hℓF : ℓ ≤ F) (hℓ3 : Nat.card ℓ = 3) :
    FourGroupFor (SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) F ℓ := by
  have hF := card_galoisField_two_mul b hb
  have hX : ∀ x ∈ F.subgroupOf (SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4),
      x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hF3 _ hx)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hF
    Nat.prime_three (by norm_num) (three_dvd_two_pow_sub_one hbe) _ hX
  have hT : ∀ Z ≤ F, mapL (MulAut.conj g) Z ≤ d8Tor 3 (GaloisField 2 (2 * b)) 4 := by
    intro Z hZ
    rw [mapL_conj g (hZ.trans hFY)]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hFY (hZ hx)⟩ (hZ hx)
  refine fourGroupFor_of_mapL (MulAut.conj g) hFY hℓF ?_
  obtain ⟨U, hUY, hUe, hU4, hTN, hTC⟩ := exists_fourGroup_of_le_torus hbe hF (hT ℓ hℓF)
    (by rw [card_mapL _ (hℓF.trans hFY), hℓ3])
  refine ⟨U, hUY, hUe, hU4, (hT F le_rfl).trans hTN, ?_⟩
  apply le_antisymm
  · rw [← hTC]
    exact inf_le_inf_right _ (hT F le_rfl)
  · exact le_inf (mapL_mono _ hℓF) (hTC ▸ inf_le_right)

theorem u4FourGroupLines (hb : 0 < b) (hbe : Even b) : U4FourGroupLines b := by
  intro G _ _ Y ⟨eY⟩ F ℓ hFY hFe hℓF hℓ3
  obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU b hb
  set E := eY.trans e₀
  exact fourGroupFor_of_mapL E hFY hℓF (fourGroupFor_SU hb hbe (mapL_le E F)
    (pow_three_of_mem_mapL E hFe.2) (mapL_mono E hℓF) (by rw [card_mapL E (hℓF.trans hFY), hℓ3]))

end KFact

end U4FourLines

end CFSG.RankThree.PartTwo.Sec21
