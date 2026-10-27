module

public import CFSG.RankThree.PartOne.Q1327C.BL4Cell
public import CFSG.LieType.Simplicity.Classical
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne

public section

namespace CFSG.RankThree.PartOne.Q1327C

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

variable {k : Type} [Field k]

theorem exists_conj_diag_sl4 [Finite k] {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : kˣ, IsPrimitiveRoot ζ p) (X : Subgroup (SL4 k)) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∃ g : SL4 k, ∀ x ∈ X, ∃ D : Fin 4 → k,
      ((g * x * g⁻¹ : SL4 k) : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧
        ∀ i, D i ^ p = 1 := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, hA⟩ := exists_conj_diagonal_of_commuting_pow_eq_one
    (IsPrimitiveRoot.coe_units_iff.mpr hζ) X hcomm hexp
  let δ : kˣ := Matrix.GeneralLinearGroup.det A
  let D0 : GL (Fin 4) k := diagU (Function.update (1 : Fin 4 → kˣ) 0 δ⁻¹)
  have hD0det : ((D0 : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k).det = (δ⁻¹ : kˣ) := by
    rw [det_diagU]
    simp [Fin.prod_univ_succ, Function.update_apply]
  have hgdet : ((D0 * A : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hD0det]
    have : ((A : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k).det = (δ : k) := rfl
    rw [this, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let g : SL4 k := ⟨((D0 * A : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k), hgdet⟩
  have hgGL : Matrix.SpecialLinearGroup.toGL g = D0 * A := Units.ext rfl
  refine ⟨g, fun x hx => ?_⟩
  have hconj : (Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) : GL (Fin 4) k) =
      D0 * (A * Matrix.SpecialLinearGroup.toGL x * A⁻¹) * D0⁻¹ := by
    rw [map_mul, map_mul, map_inv, hgGL]
    group
  have hdiag : ((D0 * (A * Matrix.SpecialLinearGroup.toGL x * A⁻¹) * D0⁻¹ : GL (Fin 4) k) :
      Matrix (Fin 4) (Fin 4) k).IsDiag := by
    intro a b hab
    obtain ⟨d, hd⟩ : ∃ d : Fin 4 → kˣ, D0 = diagU d := ⟨_, rfl⟩
    have hmid : (((A * Matrix.SpecialLinearGroup.toGL x * A⁻¹ : GL (Fin 4) k)) :
        Matrix (Fin 4) (Fin 4) k) a b = 0 := by
      have h1 := hA x hx a b hab
      rw [Units.val_mul, Units.val_mul]
      exact h1
    rw [hd, ← diagU_inv, Units.val_mul, Units.val_mul, diagU_val, diagU_val, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hmid]
    simp
  have hM : ((g * x * g⁻¹ : SL4 k) : Matrix (Fin 4) (Fin 4) k).IsDiag := by
    have hmat : ((g * x * g⁻¹ : SL4 k) : Matrix (Fin 4) (Fin 4) k) =
        ((Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) : GL (Fin 4) k) :
          Matrix (Fin 4) (Fin 4) k) := rfl
    rw [hmat, hconj]
    exact hdiag
  have hMd : ((g * x * g⁻¹ : SL4 k) : Matrix (Fin 4) (Fin 4) k) =
      Matrix.diagonal (Matrix.diag ((g * x * g⁻¹ : SL4 k) : Matrix (Fin 4) (Fin 4) k)) :=
    hM.diagonal_diag.symm
  refine ⟨Matrix.diag ((g * x * g⁻¹ : SL4 k) : Matrix (Fin 4) (Fin 4) k), hMd, fun i => ?_⟩
  have hpow : (g * x * g⁻¹) ^ p = 1 := by
    rw [conj_pow, hexp x hx, mul_one, mul_inv_cancel]
  have h1 : ((((g * x * g⁻¹) ^ p : SL4 k)) : Matrix (Fin 4) (Fin 4) k) = 1 := by
    rw [hpow]
    rfl
  rw [Matrix.SpecialLinearGroup.coe_pow, hMd, Matrix.diagonal_pow] at h1
  have h2 := congrFun (congrFun h1 i) i
  simpa using h2

theorem center_sl4_bot [CharP k 2] : Subgroup.center (SL4 k) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 4 = 0 := by
      linear_combination hr + (1 - 2 * r ^ 3 + 3 * r ^ 2 - 2 * r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem card_sl2_B [Finite k] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = Nat.card k * (Nat.card k ^ 2 - 1) :=
  CFSG.AGLEmbedding.ParabPrime.card_sl2

theorem mul_sq_sub_one_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 - 1 < b ^ 2 - 1 := by
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    omega
  calc a * (a ^ 2 - 1) ≤ b * (a ^ 2 - 1) := Nat.mul_le_mul_right _ hab.le
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left h2 (by omega)

theorem eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (mul_sq_sub_one_lt ha hab).ne
  · exact hab
  · exact absurd h.symm (mul_sq_sub_one_lt hb hab).ne

theorem card_psl2_B {Y : Type} [Group Y] {f : ℕ} (hmod : StatedClassicalModel Y .PSL 2 2 f) :
    Nat.card Y = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hmod

theorem card_autFixedInG {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {F : Subgroup G}
    (hF : IsElementaryAbelian p F) (hFcard : Nat.card F = p ^ 3) {t : MulAut ↥F}
    (ht : IsAutReflection p F t) : Nat.card (autFixedInG F t) = p ^ 2 := by
  have := hF
  have hc : ∀ u v : ↥F, u * v = v * u := fun u v => IsMulCommutative.is_comm.comm u v
  let _ : CommGroup ↥F := { (inferInstance : Group ↥F) with mul_comm := hc }
  let φ : ↥F →* ↥F := MonoidHom.mk' (fun e => t e * e⁻¹) (fun a b => by
    rw [map_mul, _root_.mul_inv_rev, mul_comm b⁻¹ a⁻¹]
    exact mul_mul_mul_comm _ _ _ _)
  have hker : φ.ker = autFixed F t := by
    ext x
    change t x * x⁻¹ = 1 ↔ t.toMonoidHom x = (MonoidHom.id ↥F) x
    exact mul_inv_eq_one
  have hrange : φ.range = autMoved F t := by
    unfold autMoved
    have : Set.range (fun e : ↥F => t e * e⁻¹) = (φ.range : Set ↥F) := by
      rw [MonoidHom.coe_range]
      rfl
    rw [this, Subgroup.closure_eq]
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, ht.2, hFcard] at h1
  have h2 : Nat.card (autFixed F t) = p ^ 2 := by
    have : Nat.card (autFixed F t) * p = p ^ 2 * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos this
  unfold autFixedInG
  rw [Subgroup.card_map_of_injective F.subtype_injective, h2]

theorem false_of_l4_split {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}
    (h : Q1327.T123Base p X A₀ F)
    (hdat : ∃ (t : MulAut ↥F) (K : Subgroup G) (f : ℕ), t ∈ torusImage F X ∧
      IsAutReflection p F t ∧ K ≤ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G) ∧
      K.subgroupOf (X ⊓ Subgroup.centralizer (autFixedInG F t : Set G)) ∈
        thetaComponents p ↥(X ⊓ Subgroup.centralizer (autFixedInG F t : Set G)) ∧
      autMovedInG F t ≤ K ∧ StatedClassicalModel ↥K .PSL 2 2 f ∧ 2 ≤ f ∧ p ∣ 2 ^ f + 1)
    (hm : ∃ g : ℕ, 1 ≤ g ∧ p ∣ 2 ^ g - 1 ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 g) : False := by
  obtain ⟨g, hg1, hpg, hadm, k, hkf, hkfin, hk, ⟨e⟩⟩ := hm
  obtain ⟨t, Kc, f, -, hrefl, hKle, hKtheta, -, hmodel, hf2, hpf⟩ := hdat
  have hp := h.prime
  have hp5 := h.five_le
  have hZ : NoZ p X := h.center_pPrime
  have hchar : CharP k 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hk
  have hrk : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, hk]
    exact hpg
  have : Fact p.Prime := ⟨hp⟩
  have hζ : ∃ ζ : kˣ, IsPrimitiveRoot ζ p := by
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hrk
    exact ⟨ζ, by rw [← hζ]; exact IsPrimitiveRoot.orderOf ζ⟩
  let χ : Matrix.ProjectiveSpecialLinearGroup (Fin 4) k ≃* SL4 k :=
    (QuotientGroup.quotientMulEquivOfEq center_sl4_bot).trans QuotientGroup.quotientBot
  let ψ : ↥X ⧸ Subgroup.center ↥X ≃* SL4 k :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 k).symm.trans χ)
  let ρ₀ : ↥X →* SL4 k := ψ.toMonoidHom.comp (proj X)
  have hρ₀surj : Function.Surjective ρ₀ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρ₀ker : ρ₀.ker = Subgroup.center ↥X := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hF := h.F_elem
  have hFexp : ∀ a ∈ F, a ^ p = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian (A := F) a ha
  have hFmexp : ∀ x ∈ (F.subgroupOf X).map ρ₀, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ p = 1 := Subtype.ext (hFexp y (Subgroup.mem_subgroupOf.1 hy))
    rw [this, map_one]
  have hFmcomm : ∀ x ∈ (F.subgroupOf X).map ρ₀, ∀ y ∈ (F.subgroupOf X).map ρ₀, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := h.F_elem.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : G), Subgroup.mem_subgroupOf.1 hb⟩
    exact congrArg (fun y : ↥F => (y : G)) this
  obtain ⟨gm, hgm⟩ := exists_conj_diag_sl4 hp hζ _ hFmexp hFmcomm
  let ρ : ↥X →* SL4 k := (MulAut.conj gm).toMonoidHom.comp ρ₀
  have hρsurj : Function.Surjective ρ := (MulAut.conj gm).surjective.comp hρ₀surj
  have hρker : ρ.ker = Subgroup.center ↥X := by
    rw [← hρ₀ker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact MulEquiv.map_eq_one_iff (MulAut.conj gm)
  have hdiag : ∀ x : ↥X, (x : G) ∈ F → ∃ D : Fin 4 → k,
      (ρ x : Matrix (Fin 4) (Fin 4) k) = Matrix.diagonal D ∧ ∀ i, D i ^ p = 1 :=
    fun x hx => hgm (ρ₀ x) ⟨x, hx, rfl⟩
  have hFix : autFixedInG F t ≤ F := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hFixcard : Nat.card (autFixedInG F t) = p ^ 2 :=
    card_autFixedInG hp hF h.F_card hrefl
  have hKC : Kc ≤ cent X (autFixedInG F t) := hKle
  have hsimpleK : IsSimpleGroup ↥Kc :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥Kc 2 2 f hmodel).2
  have hKsimple : IsSimpleGroup ↥(Kc.subgroupOf (cent X (autFixedInG F t))) :=
    (Subgroup.subgroupOfEquivOfLe hKC).isSimpleGroup
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg1
  have h4 : 4 ≤ Nat.card k := by
    have := Nat.le_of_dvd (by omega) hpg
    rw [hk]
    omega
  have hsimple2 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    KCRootAxis.sl2_isSimpleGroup h4
  have hcard := l4_cell_card hp hp5 hZ hrk hsimple2 ρ hρsurj hρker h.F_le hFexp hFix hFixcard hdiag
    hKtheta.1 hKsimple hKtheta.2.1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, card_psl2_B hmodel,
    card_sl2_B, hk] at hcard
  have hgf : g = f := by
    have h2f : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have := eq_of_mul_sq_sub_one_eq h2f (by omega) hcard
    exact (Nat.pow_right_injective le_rfl this).symm
  subst hgf
  have h2 : p ∣ 2 := by
    have := Nat.dvd_sub hpf hpg
    have e2 : 2 ^ g + 1 - (2 ^ g - 1) = 2 := by omega
    rwa [e2] at this
  have := Nat.le_of_dvd (by norm_num) h2
  omega

end CFSG.RankThree.PartOne.Q1327C
