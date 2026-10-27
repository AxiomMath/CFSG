module

public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3
public import CFSG.Quasithin.EmptyFaithful.A38c15Gl2
public import CFSG.RankThree.SubgroupLists2.OmegaThree
public import CFSG.RankThree.PartOne.N1322.CaseGL32
public import CFSG.RankThree.PartOne.N1322.Pure
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.A38c15

open Matrix CFSG.RepresentationTheory CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] def glImage (M : Subgroup SL(3, ZMod p)) : Subgroup (GL (Fin 3) (ZMod p)) :=
  M.map Matrix.SpecialLinearGroup.toGL

theorem det_of_mem_glImage {M : Subgroup SL(3, ZMod p)} {g : GL (Fin 3) (ZMod p)}
    (hg : g ∈ glImage M) : (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
  obtain ⟨m, -, rfl⟩ := hg
  exact m.2

noncomputable def glImageEquiv (M : Subgroup SL(3, ZMod p)) : ↥M ≃* ↥(glImage M) :=
  M.equivMapOfInjective Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective

theorem isSolvable_of_glImage {M : Subgroup SL(3, ZMod p)} (h : Group.IsSolvable ↥(glImage M)) :
    Group.IsSolvable ↥M :=
  Group.isSolvable_of_isSolvable_injective (f := (glImageEquiv M).toMonoidHom)
    (glImageEquiv M).injective

theorem glImage_irreducible {M : Subgroup SL(3, ZMod p)} (hirr : IsIrreducibleSL3 M) :
    IsIrreducibleMatrixRep (glImage M).subtype := by
  intro W hW
  refine hirr W fun g hg w hw => ?_
  have := hW ⟨Matrix.SpecialLinearGroup.toGL g, g, hg, rfl⟩ w hw
  simpa using this

theorem eq_top_of_stated_le_glImage {M : Subgroup SL(3, ZMod p)}
    (h : StatedSL 3 (ZMod p) ≤ glImage M) : M = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : Matrix.SpecialLinearGroup.toGL g ∈ StatedSL 3 (ZMod p) := by
    rw [statedSL_eq_range_toGL]
    exact ⟨g, rfl⟩
  obtain ⟨m, hm, hmg⟩ := h hg
  have := Matrix.SpecialLinearGroup.toGL_injective hmg
  rwa [← this]

theorem card_sl3_zmod : Nat.card SL(3, ZMod p) = p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) := by
  have hpp : p.Prime := Fact.out
  have h := Matrix.card_SL_field (𝔽 := ZMod p) 3
  rw [ZMod.card] at h
  rw [h, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hpp.one_lt; omega⟩
  have hk : 0 < k := by have := hpp.one_lt; omega
  have e1 : (k + 1) ^ 3 - 1 = k * (k ^ 2 + 3 * k + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (k + 1) ^ 3 - (k + 1) = (k + 1) * k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (k + 1) ^ 3 - (k + 1) ^ 2 = (k + 1) ^ 2 * k := Nat.sub_eq_of_eq_add (by ring)
  have e4 : (k + 1) ^ 2 - 1 = k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, e3, e4, Nat.add_sub_cancel]
  exact Nat.div_eq_of_eq_mul_left hk (by ring)

theorem sixteen_dvd_card_sl3 (hp2 : p ≠ 2) : 16 ∣ Nat.card SL(3, ZMod p) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := hpp.odd_of_ne_two hp2
  rw [card_sl3_zmod, hm]
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (2 * m + 1) ^ 3 - 1 = 2 * (m * (4 * m ^ 2 + 6 * m + 3)) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2]
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  exact ⟨(2 * m + 1) ^ 3 * (m * (4 * m ^ 2 + 6 * m + 3)) * j, by rw [hj]; ring⟩

@[expose] def scalarsDetOne (p : ℕ) [Fact p.Prime] : Subgroup (GL (Fin 3) (ZMod p)) :=
  Subgroup.center (GL (Fin 3) (ZMod p)) ⊓ (Matrix.GeneralLinearGroup.det).ker

theorem mem_scalarsDetOne {g : GL (Fin 3) (ZMod p)} :
    g ∈ scalarsDetOne p ↔ g ∈ Subgroup.center (GL (Fin 3) (ZMod p)) ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
  simp only [scalarsDetOne, Subgroup.mem_inf, MonoidHom.mem_ker]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    have := congrArg Units.val h
    simpa using this
  · intro h
    exact Units.ext (by simpa using h)

theorem pow_three_eq_one_of_mem_scalarsDetOne {z : GL (Fin 3) (ZMod p)}
    (hz : z ∈ scalarsDetOne p) : z ^ 3 = 1 := by
  obtain ⟨hzc, hzd⟩ := mem_scalarsDetOne.mp hz
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzc
  obtain ⟨u, rfl⟩ := hzc
  have h1 : (u : ZMod p) ^ 3 = 1 := by
    have := Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) u
    have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)).det = ((u ^ Fintype.card (Fin 3) : (ZMod p)ˣ) : ZMod p) :=
      congrArg Units.val this
    rw [hzd] at h2
    simpa using h2.symm
  have h3 : u ^ 3 = 1 := Units.ext (by simpa using h1)
  rw [← map_pow, h3, map_one]

theorem odd_card_scalarsDetOne : Odd (Nat.card (scalarsDetOne p)) := by
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (scalarsDetOne p) := by omega
  have := Fact.mk Nat.prime_two
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz3 : (z : GL (Fin 3) (ZMod p)) ^ 3 = 1 := pow_three_eq_one_of_mem_scalarsDetOne z.2
  have hz2 : (z : GL (Fin 3) (ZMod p)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have : (z : GL (Fin 3) (ZMod p)) = 1 := by
    have h' : (z : GL (Fin 3) (ZMod p)) =
        (z : GL (Fin 3) (ZMod p)) ^ 3 * ((z : GL (Fin 3) (ZMod p)) ^ 2)⁻¹ := by group
    rw [hz3, hz2] at h'
    simpa using h'
  have hz1 : z = 1 := Subtype.ext this
  have := hz
  rw [hz1, orderOf_one] at this
  omega

theorem exists_odd_dvd_of_decomp {M : Subgroup SL(3, ZMod p)} (hodd : Odd M.index)
    {Y : Subgroup (GL (Fin 3) (ZMod p))}
    (hY : ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hdec : ∀ g ∈ glImage M, ∃ y ∈ Y, ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)), g = y * z) :
    ∃ u : ℕ, Odd u ∧ Nat.card SL(3, ZMod p) ∣ Nat.card Y * u := by
  classical
  let φ : ↥Y × ↥(scalarsDetOne p) →* GL (Fin 3) (ZMod p) :=
    MonoidHom.noncommCoprod Y.subtype (scalarsDetOne p).subtype (fun y z =>
      (Subgroup.mem_center_iff.mp (mem_scalarsDetOne.mp z.2).1) y)
  let K' : Subgroup (GL (Fin 3) (ZMod p)) := φ.range
  have hGK' : glImage M ≤ K' := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec g hg
    have hdg := det_of_mem_glImage hg
    have hzd : (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, hY y hy, one_mul] at hdg
      exact hdg
    exact ⟨(⟨y, hy⟩, ⟨z, mem_scalarsDetOne.mpr ⟨hz, hzd⟩⟩), rfl⟩
  let K : Subgroup SL(3, ZMod p) := K'.comap Matrix.SpecialLinearGroup.toGL
  have hMK : M ≤ K := fun m hm => hGK' ⟨m, hm, rfl⟩
  have hidxK : Odd K.index := Odd.of_dvd_nat hodd (Subgroup.index_dvd_of_le hMK)
  have hK : Nat.card K ∣ Nat.card K' := by
    have h1 : K.map Matrix.SpecialLinearGroup.toGL ≤ K' := by
      rintro _ ⟨k, hk, rfl⟩
      exact hk
    rw [← Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective]
    exact Subgroup.card_dvd_of_le h1
  have hK' : Nat.card K' ∣ Nat.card Y * Nat.card (scalarsDetOne p) := by
    have := Subgroup.card_range_dvd φ
    rwa [Nat.card_prod] at this
  refine ⟨Nat.card (scalarsDetOne p) * K.index, odd_card_scalarsDetOne.mul hidxK, ?_⟩
  have h := Subgroup.card_mul_index K
  rw [← h]
  calc Nat.card K * K.index ∣ (Nat.card Y * Nat.card (scalarsDetOne p)) * K.index :=
        Nat.mul_dvd_mul_right (hK.trans hK') _
    _ = Nat.card Y * (Nat.card (scalarsDetOne p) * K.index) := by ring

theorem scalar_of_commute_of_nonabelian {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hnab : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    {S : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hS : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * S = S * g) :
    ∃ c : ZMod p, S = Matrix.scalar (Fin 3) c := by
  rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirr with h | ⟨hcyc, -, -⟩
  · exact h S hS
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have : IsMulCommutative ↥H := hcyc.isMulCommutative
    exact hab (congrArg (fun x : ↥H => (x : GL (Fin 3) (ZMod p)))
      (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem mem_center_of_scalar {g : GL (Fin 3) (ZMod p)} {c : ZMod p}
    (h : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.scalar (Fin 3) c) :
    g ∈ Subgroup.center (GL (Fin 3) (ZMod p)) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, h.symm⟩

theorem alt5_nonabelian : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨inv5, c5, fun h => ?_⟩
  have h1 : inv5 * c5 * inv5⁻¹ = c5 := by rw [h, mul_inv_cancel_right]
  rw [inv5_conj] at h1
  have h3 : c5 ^ 3 = 1 := by
    have : c5 * c5 ^ 3 = c5 * 1 := by rw [← pow_succ', mul_one]; exact h1
    exact mul_left_cancel this
  have h2 : c5 ^ 2 = 1 := by
    have : c5 ^ 3 * c5 ^ 2 = c5 ^ 3 * 1 := by rw [← pow_add, mul_one, h3]; exact c5_pow_five
    exact mul_left_cancel this
  apply c5_ne_one
  calc c5 = c5 ^ 3 := by rw [pow_succ, h2, one_mul]
    _ = 1 := h3

theorem false_of_alt5 (hp2 : p ≠ 2) {M : Subgroup SL(3, ZMod p)} (hodd : Odd M.index)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ glImage M)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e : H ≃* alternatingGroup (Fin 5))
    (hdec : ∀ g ∈ glImage M, ∃ h ∈ H, ∃ z ∈ glImage M,
      (∀ y ∈ glImage M, z * y = y * z) ∧ g = h * z) : False := by
  have hnab : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt5_nonabelian
    refine ⟨(e.symm a : GL (Fin 3) (ZMod p)), (e.symm a).2, (e.symm b : GL (Fin 3) (ZMod p)),
      (e.symm b).2, fun h => hab ?_⟩
    have h' : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
    have := congrArg e h'
    simpa using this
  have hdecomp : ∀ g ∈ glImage M, ∃ y ∈ H, ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)),
      g = y * z := by
    intro g hg
    obtain ⟨h, hh, z, hz, hzc, rfl⟩ := hdec g hg
    refine ⟨h, hh, z, ?_, rfl⟩
    have hcomm : ∀ x ∈ H, ((x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        (z : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        (z : Matrix (Fin 3) (Fin 3) (ZMod p)) * (x : GL (Fin 3) (ZMod p)) := fun x hx => by
      rw [← Units.val_mul, ← Units.val_mul, hzc x (hHG hx)]
    obtain ⟨c, hc⟩ := scalar_of_commute_of_nonabelian hirr hnab hcomm
    exact mem_center_of_scalar hc
  obtain ⟨u, hu, hdvd⟩ := exists_odd_dvd_of_decomp hodd
    (fun y hy => det_of_mem_glImage (hHG hy)) hdecomp
  have h16 := sixteen_dvd_card_sl3 (p := p) hp2
  have hH : Nat.card H = 60 := by rw [Nat.card_congr e.toEquiv, card_alt_five_fin]
  rw [hH] at hdvd
  have h := h16.trans hdvd
  obtain ⟨v, rfl⟩ := hu
  omega

section Omega

open CFSG.RankThree.SubgroupLists (soGL omegaGL card_soGL_three mem_soGL)

theorem commute_inv_mul_forms {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    {M M' : Matrix σ σ K} (hdet : M.det ≠ 0) {h : GL σ K}
    (hM : (h : Matrix σ σ K)ᵀ * M * (h : Matrix σ σ K) = M)
    (hM' : (h : Matrix σ σ K)ᵀ * M' * (h : Matrix σ σ K) = M') :
    (h : Matrix σ σ K) * (M⁻¹ * M') = (M⁻¹ * M') * (h : Matrix σ σ K) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set H : Matrix σ σ K := (h : Matrix σ σ K) with hH
  set Hi : Matrix σ σ K := ((h⁻¹ : GL σ K) : Matrix σ σ K) with hHi
  have hHHi : H * Hi = 1 := by rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHit : Hiᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hHHi, Matrix.transpose_one]
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have s1 : M * H = Hiᵀ * M := by
    calc M * H = (Hiᵀ * Hᵀ) * M * H := by rw [hHit, Matrix.one_mul]
      _ = Hiᵀ * (Hᵀ * M * H) := by simp only [Matrix.mul_assoc]
      _ = Hiᵀ * M := by rw [hM]
  have s2 : M' * H = Hiᵀ * M' := by
    calc M' * H = (Hiᵀ * Hᵀ) * M' * H := by rw [hHit, Matrix.one_mul]
      _ = Hiᵀ * (Hᵀ * M' * H) := by simp only [Matrix.mul_assoc]
      _ = Hiᵀ * M' := by rw [hM']
  have s3 : H * M⁻¹ = M⁻¹ * Hiᵀ := by
    calc H * M⁻¹ = M⁻¹ * (M * H) * M⁻¹ := by
          rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
      _ = M⁻¹ * (Hiᵀ * M) * M⁻¹ := by rw [s1]
      _ = M⁻¹ * Hiᵀ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hMN, Matrix.mul_one]
  calc H * (M⁻¹ * M') = (H * M⁻¹) * M' := by rw [Matrix.mul_assoc]
    _ = (M⁻¹ * Hiᵀ) * M' := by rw [s3]
    _ = M⁻¹ * (Hiᵀ * M') := by rw [Matrix.mul_assoc]
    _ = M⁻¹ * (M' * H) := by rw [s2]
    _ = (M⁻¹ * M') * H := by rw [Matrix.mul_assoc]

theorem sub_eq_pred (p : ℕ) (hp : 1 ≤ p) : (p ^ 3 - 1) - p * (p ^ 2 - 1) = p - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have e1 : (k + 1) ^ 3 - 1 = k * (k ^ 2 + 3 * k + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (k + 1) ^ 2 - 1 = k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, Nat.add_sub_cancel]
  exact Nat.sub_eq_of_eq_add (by ring)

theorem omega_commutant_scalar (hp2 : p ≠ 2) {M₀ : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hMt : M₀ᵀ = M₀) (hdet : M₀.det ≠ 0) (hirr : IsIrreducibleMatrixRep (omegaGL M₀).subtype)
    {S : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hS : ∀ g ∈ omegaGL M₀, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * S = S * g) :
    ∃ c : ZMod p, S = Matrix.scalar (Fin 3) c := by
  rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirr with
    h | ⟨-, hd3, hnd⟩
  · exact h S hS
  · exfalso
    have hcard : Nat.card (omegaGL M₀) ∣ p * (p ^ 2 - 1) := by
      rw [← card_soGL_three hp2 hMt hdet]
      exact Subgroup.card_dvd_of_le (Subgroup.commutator_le_self _)
    rw [Nat.card_zmod] at hd3 hnd
    apply hnd
    have h1 := Nat.dvd_sub hd3 hcard
    rwa [sub_eq_pred p (Fact.out : p.Prime).one_lt.le] at h1

theorem scalar_mul_eq_smul {n : ℕ} (c : ZMod p) (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    Matrix.scalar (Fin n) c * A = c • A := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem false_of_omega (hp2 : p ≠ 2) {M : Subgroup SL(3, ZMod p)} (hodd : Odd M.index)
    {M₀ : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : M₀ᵀ = M₀) (hdet : M₀.det ≠ 0)
    (hnorm : ∀ g ∈ glImage M, ∀ x ∈ omegaGL M₀, g * x * g⁻¹ ∈ omegaGL M₀)
    (hirr : IsIrreducibleMatrixRep (omegaGL M₀).subtype) : False := by
  have hΩ : ∀ h ∈ omegaGL M₀, (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
      (h : Matrix (Fin 3) (Fin 3) (ZMod p)) = M₀ := fun h hh =>
    (mem_soGL.mp (Subgroup.commutator_le_self _ hh)).1
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hdet
  have hform : ∀ g ∈ glImage M, ∃ l : ZMod p, l ^ 3 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        l • M₀ := by
    intro g hg
    set M' := (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) with hM'
    have hinv : ∀ h ∈ omegaGL M₀, (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M' *
        (h : Matrix (Fin 3) (Fin 3) (ZMod p)) = M' := by
      intro h hh
      have hh' := hΩ _ (hnorm g hg h hh)
      have e1 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * (h : Matrix (Fin 3) (Fin 3) (ZMod p)) =
          ((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
        rw [← Units.val_mul, ← Units.val_mul]
        exact congrArg Units.val (by group)
      calc (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M' * (h : Matrix (Fin 3) (Fin 3) (ZMod p))
          = ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) * (h : Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ *
              M₀ * ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
                (h : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
            simp only [hM', Matrix.transpose_mul, Matrix.mul_assoc]
        _ = (((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
              (g : Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ * M₀ *
              (((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
                (g : Matrix (Fin 3) (Fin 3) (ZMod p))) := by rw [e1]
        _ = (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
              (((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
                ((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) *
              (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = M' := by rw [hh']
    obtain ⟨l, hl⟩ := omega_commutant_scalar hp2 hMt hdet hirr
      (S := M₀⁻¹ * M') (fun h hh => commute_inv_mul_forms hdet (hΩ h hh) (hinv h hh))
    have hM'eq : M' = l • M₀ := by
      calc M' = (M₀ * M₀⁻¹) * M' := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
        _ = M₀ * (M₀⁻¹ * M') := by rw [Matrix.mul_assoc]
        _ = M₀ * Matrix.scalar (Fin 3) l := by rw [hl]
        _ = l • M₀ := by
            ext i j
            simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
    refine ⟨l, ?_, hM'eq⟩
    have hdg := det_of_mem_glImage hg
    have h1 := congrArg Matrix.det hM'eq
    rw [hM', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdg, one_mul, mul_one,
      Matrix.det_smul, Fintype.card_fin] at h1
    have h2 : (l ^ 3 - 1) * M₀.det = 0 := by linear_combination -h1
    have := (mul_eq_zero.mp h2).resolve_right hdet
    linear_combination this
  have hdecomp : ∀ g ∈ glImage M, ∃ y ∈ soGL M₀, ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)),
      g = y * z := by
    intro g hg
    obtain ⟨l, hl3, hl⟩ := hform g hg
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl3
    let w : (ZMod p)ˣ := Units.mk0 l hl0 ^ 2
    have hwv : (w : ZMod p) = l ^ 2 := by simp [w]
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) w⁻¹ * g, ?_,
      Matrix.GeneralLinearGroup.scalar (Fin 3) w, ?_, ?_⟩
    · rw [mem_soGL]
      have hwinv : ((w⁻¹ : (ZMod p)ˣ) : ZMod p) = (l ^ 2)⁻¹ := by
        rw [Units.val_inv_eq_inv_val, hwv]
      have hc3 : ((l ^ 2)⁻¹) ^ 3 = 1 := by
        have h6 : (l ^ 2) ^ 3 = 1 := by
          rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hl3, one_pow]
        rw [inv_pow, h6, inv_one]
      have hcc : ((l ^ 2)⁻¹) * (((l ^ 2)⁻¹) * l) = 1 := by
        calc ((l ^ 2)⁻¹) * (((l ^ 2)⁻¹) * l) = (l ^ 3)⁻¹ := by field_simp
          _ = 1 := by rw [hl3, inv_one]
      have hy : ((Matrix.GeneralLinearGroup.scalar (Fin 3) w⁻¹ * g : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)) = ((l ^ 2)⁻¹) • (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
        rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hwinv, scalar_mul_eq_smul]
      constructor
      · rw [hy]
        simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [hl, smul_smul, mul_assoc, hcc, one_smul]
      · rw [hy, Matrix.det_smul, det_of_mem_glImage hg, mul_one, Fintype.card_fin]
        exact hc3
    · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨w, rfl⟩
    · rw [mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, ← map_mul,
        inv_mul_cancel, map_one, one_mul]
  obtain ⟨u, hu', hdvd⟩ := exists_odd_dvd_of_decomp hodd
    (fun y hy => (mem_soGL.mp hy).2) hdecomp
  rw [card_soGL_three hp2 hMt hdet, card_sl3_zmod] at hdvd
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  have hpos : 0 < p * (p ^ 2 - 1) := by
    have : 1 < p ^ 2 := by nlinarith
    exact Nat.mul_pos hpp.pos (by omega)
  have hrew : p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) = p * (p ^ 2 - 1) * (p ^ 2 * (p ^ 3 - 1)) := by
    ring
  rw [hrew] at hdvd
  have hd := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  have hev : 2 ∣ p ^ 3 - 1 := by
    have hodd3 : Odd (p ^ 3) := (hpp.odd_of_ne_two hp2).pow
    exact (Nat.Odd.sub_odd hodd3 odd_one).two_dvd
  have h2u : 2 ∣ u := hev.trans ((Dvd.intro_left _ rfl).trans hd)
  exact (Nat.not_even_iff_odd.mpr hu') (even_iff_two_dvd.mpr h2u)

end Omega

theorem card_alt_six_fin : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem false_of_threeA6 (hN6 : CFSG.RankThree.PartOne.N1322.KF1322ThreeA6Norm) (hp2 : p ≠ 2)
    {M : Subgroup SL(3, ZMod p)} (hodd : Odd M.index)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ glImage M)
    (hnorm : ∀ g ∈ glImage M, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (e : Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)))
    (hp30 : p % 30 = 1 ∨ p % 30 = 19) : False := by
  have hpp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    have := hpp.two_le
    omega
  have hdecomp : ∀ g ∈ glImage M, ∃ y ∈ H, ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)),
      g = y * z := by
    intro g hg
    obtain ⟨h, hh, z, hz, rfl⟩ := hN6 p hp5 H hirr hperf hZ e g (hnorm g hg)
    exact ⟨h, hh, z, Subgroup.mem_center_iff.mpr fun y => (hz y).symm, rfl⟩
  obtain ⟨u, hu, hdvd⟩ := exists_odd_dvd_of_decomp hodd
    (fun y hy => det_of_mem_glImage (hHG hy)) hdecomp
  have h16 := sixteen_dvd_card_sl3 (p := p) hp2
  have hH : Nat.card H = 1080 := by
    obtain ⟨e'⟩ := e
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
    rw [Nat.card_congr e'.toEquiv, card_alt_six_fin, hZ] at h
    omega
  rw [hH] at hdvd
  have h := h16.trans hdvd
  obtain ⟨v, rfl⟩ := hu
  omega

section L32

open CFSG.RankThree.PartOne.N1322 (Mat2 matUnit matUnit_val det_GL32 G32_noncomm)
open CFSG.QuasithinUnique.Setup.Family (GL32 aut_GL32_cases)
open CFSG.LieType.SteinbergBR.AutGL32 (tau tau_val card_GL32)

theorem mat_order7_data : ∃ X : Mat2, X.det = 1 ∧ X ^ 7 = 1 ∧ X ≠ 1 ∧
    (∃ K : Mat2, K.det = 1 ∧ K * X = X ^ 2 * K) ∧
    (∃ K : Mat2, K.det = 1 ∧ K * (X ^ 6)ᵀ = X ^ 6 * K) := by
  refine ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], ?_⟩
  decide +kernel

theorem exists_x7_data : ∃ x : GL32, x ^ 7 = 1 ∧ x ≠ 1 ∧ IsConj x (x ^ 2) ∧
    IsConj (tau x) x⁻¹ := by
  obtain ⟨X, hXd, hX7, hX1, ⟨K, hKd, hK⟩, ⟨K', hKd', hK'⟩⟩ := mat_order7_data
  obtain ⟨x, hx⟩ : ∃ x : GL32, (x : Mat2) = X := ⟨matUnit X hXd, rfl⟩
  have hx7 : x ^ 7 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hx, hX7]; rfl)
  have hx1 : x ≠ 1 := fun h => hX1 (by
    have := congrArg (fun u : GL32 => (u : Mat2)) h
    simpa [hx] using this)
  have hxinv : x⁻¹ = x ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx7)
  refine ⟨x, hx7, hx1, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k : GL32, (k : Mat2) = K := ⟨matUnit K hKd, rfl⟩
    refine isConj_iff.mpr ⟨k, ?_⟩
    have h1 : k * x = x ^ 2 * k := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hk, hx, Units.val_pow_eq_pow_val, hx]
      exact hK)
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  · obtain ⟨k, hk⟩ : ∃ k : GL32, (k : Mat2) = K' := ⟨matUnit K' hKd', rfl⟩
    refine isConj_iff.mpr ⟨k, ?_⟩
    have htx : ((tau x : GL32) : Mat2) = (X ^ 6)ᵀ := by
      rw [tau_val, hxinv, Units.val_pow_eq_pow_val, hx]
    have h1 : k * tau x = x⁻¹ * k := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hk, htx, hxinv, Units.val_pow_eq_pow_val, hx]
      exact hK')
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]

theorem normalizes_gl32 (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdetH : ∀ y ∈ H, (y : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e : H ≃* GL32)
    {g : GL (Fin 3) (ZMod p)} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hg' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    ∃ h ∈ H, ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)), g = h * z := by
  classical
  have hnab : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := G32_noncomm
    refine ⟨(e.symm a : GL (Fin 3) (ZMod p)), (e.symm a).2, (e.symm b : GL (Fin 3) (ZMod p)),
      (e.symm b).2, fun h => hab ?_⟩
    have h' : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
    have := congrArg e h'
    simpa using this
  let α : ↥H ≃* ↥H :=
    { toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hg' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hα : ∀ x : ↥H, ((α x : ↥H) : GL (Fin 3) (ZMod p)) = g * x * g⁻¹ := fun x => rfl
  let α' : MulAut GL32 := (e.symm.trans α).trans e
  let ι : GL32 →* GL (Fin 3) (ZMod p) := H.subtype.comp e.symm.toMonoidHom
  have hι : ∀ x : GL32, ι (α' x) = g * ι x * g⁻¹ := by
    intro x
    show ((e.symm (e (α (e.symm x))) : ↥H) : GL (Fin 3) (ZMod p)) = _
    rw [e.symm_apply_apply, hα]
    rfl
  have hιe : ∀ y : ↥H, ι (e y) = y := fun y => by simp [ι]
  have hιinj : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  rcases aut_GL32_cases α' with ⟨s, hs⟩ | ⟨s, hs⟩
  ·
    let h₀ : ↥H := e.symm s
    have hconj : ∀ y ∈ H, g * y * g⁻¹ = (h₀ : GL (Fin 3) (ZMod p)) * y *
        (h₀ : GL (Fin 3) (ZMod p))⁻¹ := by
      intro y hy
      have h1 := hι (e ⟨y, hy⟩)
      rw [hs, MulAut.conj_apply, map_mul, map_mul, map_inv, hιe] at h1
      have hs' : ι s = (h₀ : GL (Fin 3) (ZMod p)) := rfl
      rw [hs'] at h1
      exact h1.symm
    have hcomm : ∀ y ∈ H, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        (((h₀ : GL (Fin 3) (ZMod p))⁻¹ * g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        (((h₀ : GL (Fin 3) (ZMod p))⁻¹ * g : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)) * y := by
      intro y hy
      have h1 := hconj y hy
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      calc y * ((h₀ : GL (Fin 3) (ZMod p))⁻¹ * g)
          = (h₀ : GL (Fin 3) (ZMod p))⁻¹ * ((h₀ : GL (Fin 3) (ZMod p)) * y *
              (h₀ : GL (Fin 3) (ZMod p))⁻¹) * g := by group
        _ = (h₀ : GL (Fin 3) (ZMod p))⁻¹ * (g * y * g⁻¹) * g := by rw [h1]
        _ = ((h₀ : GL (Fin 3) (ZMod p))⁻¹ * g) * y := by group
    obtain ⟨c, hc⟩ := scalar_of_commute_of_nonabelian hirr hnab hcomm
    refine ⟨(h₀ : GL (Fin 3) (ZMod p)), h₀.2, (h₀ : GL (Fin 3) (ZMod p))⁻¹ * g,
      mem_center_of_scalar hc, ?_⟩
    group
  ·
    exfalso
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
    have h7 : (7 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((7 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp7 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp h')
    have h8 : (8 : ZMod p) ≠ 0 := by
      have : (8 : ZMod p) = 2 ^ 3 := by norm_num
      rw [this]
      exact pow_ne_zero 3 h2
    have htr : ∀ x : GL32, ((ι (tau x) : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace =
        ((ι x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace := by
      intro x
      have h1 := hι x
      rw [hs, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      have t1 := congrArg (fun z : GL (Fin 3) (ZMod p) =>
        (z : Matrix (Fin 3) (Fin 3) (ZMod p)).trace) h1
      simp only [Units.val_mul, Matrix.trace_units_conj] at t1
      exact t1
    obtain ⟨x, hx7, hx1, hxc, hτc⟩ := exists_x7_data
    set X : GL (Fin 3) (ZMod p) := ι x with hX
    have hXdet : (X : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := hdetH _ (e.symm x).2
    have hX7 : X ^ 7 = 1 := by rw [hX, ← map_pow, hx7, map_one]
    have hX1 : X ≠ 1 := fun h => hx1 (hιinj (by rw [map_one]; exact h))
    have hXc : IsConj X (X ^ 2) := by
      have := ι.map_isConj hxc
      rwa [map_pow] at this
    have hτ : IsConj (ι (tau x)) (X⁻¹) := by
      have := ι.map_isConj hτc
      rwa [map_inv] at this
    have ht1 : (X : Matrix (Fin 3) (Fin 3) (ZMod p)).trace =
        ((X⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).trace := by
      rw [← htr x]
      exact CFSG.RankThree.SubgroupLists.trace_eq_of_isConj hτ
    have h12 : (X : Matrix (Fin 3) (Fin 3) (ZMod p)).trace =
        ((X : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ 2).trace := by
      rw [← CFSG.RankThree.SubgroupLists.coe_pow_trace]
      exact CFSG.RankThree.SubgroupLists.trace_eq_of_isConj hXc
    have hsq := CFSG.RankThree.SubgroupLists.trace_sq_sl3 X hXdet
    have hq := CFSG.RankThree.SubgroupLists.sq_two_mul_trace_add_one_eq_neg_seven hXdet hX7 hX1 h2
      h7 hXc
    set t := (X : Matrix (Fin 3) (Fin 3) (ZMod p)).trace with ht
    have e2 : t ^ 2 = 3 * t := by
      linear_combination (-1 : ZMod p) * hsq + (-1 : ZMod p) * h12 + (-2 : ZMod p) * ht1
    have h3 : 8 * (2 * t + 1) = 0 := by linear_combination hq - 4 * e2
    have h4 : 2 * t + 1 = 0 := (mul_eq_zero.mp h3).resolve_left h8
    apply h7
    linear_combination 4 * e2 - (2 * t - 7) * h4

theorem false_of_gl32 (hp2 : p ≠ 2) (hp7 : p ≠ 7) {M : Subgroup SL(3, ZMod p)}
    (hodd : Odd M.index) {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ glImage M)
    (hnorm : ∀ g ∈ glImage M, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e : H ≃* GL32) : False := by
  have hdetH : ∀ y ∈ H, (y : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := fun y hy =>
    det_of_mem_glImage (hHG hy)
  have hdecomp : ∀ g ∈ glImage M, ∃ y ∈ H, ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod p)),
      g = y * z := by
    intro g hg
    obtain ⟨h, hh, z, hz, rfl⟩ := normalizes_gl32 hp2 hp7 hdetH hirr e (hnorm g hg)
      (fun x hx => by
        have := hnorm g⁻¹ ((glImage M).inv_mem hg) x hx
        simpa using this)
    exact ⟨h, hh, z, hz, rfl⟩
  obtain ⟨u, hu, hdvd⟩ := exists_odd_dvd_of_decomp hodd hdetH hdecomp
  have h16 := sixteen_dvd_card_sl3 (p := p) hp2
  have hH : Nat.card H = 168 := by rw [Nat.card_congr e.toEquiv, card_GL32]
  rw [hH] at hdvd
  have h := h16.trans hdvd
  obtain ⟨v, rfl⟩ := hu
  omega

end L32

end CFSG.Quasithin.A38c15
