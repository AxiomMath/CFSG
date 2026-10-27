module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool} {T : Type} [Group T]

structure LModel (π : Bool) (p f : ℕ) (K : Type) [Field K] (T : Type) [Group T] where
  μ : ↥(slPi π 3 (p ^ f) K) →* T
  surjective : Function.Surjective μ
  ker_iff : ∀ g : ↥(slPi π 3 (p ^ f) K), μ g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K

noncomputable def LModel.ofEquiv (e : T ≃* projImage (slPi π 3 (p ^ f) K)) :
    LModel π p f K T where
  μ := e.symm.toMonoidHom.comp (projOf (slPi π 3 (p ^ f) K))
  surjective := e.symm.surjective.comp (projOf_surjective _)
  ker_iff g := by
    change e.symm (projOf (slPi π 3 (p ^ f) K) g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← mem_ker_projOf, MonoidHom.mem_ker]

theorem exists_lmodel {n : ℕ} (hn : 1 ≤ n) (h : Sec4.IsoLThreePi T 2 n) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π 2 n K ∧ ModThree π (2 ^ n) ∧
      Nonempty (LModel π 2 n K T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, GaloisField 2 n, inferInstance, ⟨Nat.prime_two, hn, ?_⟩, hq3,
      ⟨LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage _ _)))⟩⟩
    rw [GaloisField.card 2 n (by omega)]
    rfl
  · refine ⟨false, GaloisField 2 (2 * n), inferInstance, ⟨Nat.prime_two, hn, ?_⟩, hq3,
      ⟨LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage _ _)))⟩⟩
    rw [GaloisField.card 2 (2 * n) (by omega)]
    change 2 ^ (2 * n) = (2 ^ n) ^ 2
    rw [← pow_mul, mul_comm]

theorem unitary_of (hK : PiField π p f K) : π = false → UnitaryFieldData p f K := fun h => by
  subst h
  exact hK.unitary

theorem det_eq_one (hK : PiField π p f K) (g : ↥(slPi π 3 (p ^ f) K)) :
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  ((mem_slPi_iff (unitary_of hK)).mp g.2).2

theorem commutator_scalar (hK : PiField π p f K) (M : LModel π p f K T)
    {g₁ g₂ : ↥(slPi π 3 (p ^ f) K)} (h : M.μ g₁ * M.μ g₂ = M.μ g₂ * M.μ g₁) :
    ∃ u : Kˣ, u ^ 3 = 1 ∧ (g₁ : GL (Fin 3) K) * g₂ * (g₁ : GL (Fin 3) K)⁻¹ *
      (g₂ : GL (Fin 3) K)⁻¹ = GeneralLinearGroup.scalar (Fin 3) u := by
  have hc : M.μ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨u, hu⟩ := (M.ker_iff _).mp hc
  have hu' : (g₁ : GL (Fin 3) K) * g₂ * (g₁ : GL (Fin 3) K)⁻¹ * (g₂ : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u := hu.symm
  refine ⟨u, ?_, hu'⟩
  have hd := det_eq_one hK (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)
  have hd' : ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← hu']
    exact hd
  rw [det_scalar_three] at hd'
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, hd', Units.val_one])

theorem heis_conj {G : Type*} [Group G] {a b s : G} (hs : ∀ g : G, g * s = s * g)
    (h : b * a * b⁻¹ = s * a) (i j : ℕ) :
    (b ^ j * a ^ i) * a * (b ^ j * a ^ i)⁻¹ = s ^ j * a ∧
      (b ^ j * a ^ i) * b * (b ^ j * a ^ i)⁻¹ = s⁻¹ ^ i * b := by
  have hsc : ∀ (k : ℕ) (g : G), g * s ^ k = s ^ k * g := fun k g => (Commute.pow_right
    (show Commute g s from hs g) k).eq
  have hsi : ∀ (k : ℕ) (g : G), g * s⁻¹ ^ k = s⁻¹ ^ k * g := fun k g => (Commute.pow_right
    (show Commute g s⁻¹ from (show Commute g s from hs g).inv_right) k).eq
  have hb : ∀ j : ℕ, b ^ j * a * (b ^ j)⁻¹ = s ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc b ^ (j + 1) * a * (b ^ (j + 1))⁻¹ = b * (b ^ j * a * (b ^ j)⁻¹) * b⁻¹ := by
            rw [pow_succ']
            group
        _ = b * (s ^ j * a) * b⁻¹ := by rw [ih]
        _ = (b * s ^ j) * a * b⁻¹ := by group
        _ = (s ^ j * b) * a * b⁻¹ := by rw [hsc j b]
        _ = s ^ j * (b * a * b⁻¹) := by group
        _ = s ^ (j + 1) * a := by rw [h, ← mul_assoc, pow_succ]
  have ha : ∀ i : ℕ, a ^ i * b * (a ^ i)⁻¹ = s⁻¹ ^ i * b := by
    have hab : a * b * a⁻¹ = s⁻¹ * b := by
      have h1 : b * a = s * a * b := by
        calc b * a = (b * a * b⁻¹) * b := by group
          _ = s * a * b := by rw [h]
      calc a * b * a⁻¹ = s⁻¹ * (s * a * b) * a⁻¹ := by group
        _ = s⁻¹ * (b * a) * a⁻¹ := by rw [h1]
        _ = s⁻¹ * b := by group
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc a ^ (i + 1) * b * (a ^ (i + 1))⁻¹ = a * (a ^ i * b * (a ^ i)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
        _ = a * (s⁻¹ ^ i * b) * a⁻¹ := by rw [ih]
        _ = (a * s⁻¹ ^ i) * b * a⁻¹ := by group
        _ = (s⁻¹ ^ i * a) * b * a⁻¹ := by rw [hsi i a]
        _ = s⁻¹ ^ i * (a * b * a⁻¹) := by group
        _ = s⁻¹ ^ (i + 1) * b := by rw [hab, ← mul_assoc, pow_succ]
  constructor
  · calc (b ^ j * a ^ i) * a * (b ^ j * a ^ i)⁻¹ = b ^ j * (a ^ i * a * (a ^ i)⁻¹) * (b ^ j)⁻¹ := by
          group
      _ = b ^ j * a * (b ^ j)⁻¹ := by
          congr 2
          group
      _ = s ^ j * a := hb j
  · calc (b ^ j * a ^ i) * b * (b ^ j * a ^ i)⁻¹ =
          b ^ j * (a ^ i * b * (a ^ i)⁻¹) * (b ^ j)⁻¹ := by group
      _ = b ^ j * (s⁻¹ ^ i * b) * (b ^ j)⁻¹ := by rw [ha i]
      _ = (b ^ j * s⁻¹ ^ i) * b * (b ^ j)⁻¹ := by group
      _ = (s⁻¹ ^ i * b ^ j) * b * (b ^ j)⁻¹ := by rw [hsi i (b ^ j)]
      _ = s⁻¹ ^ i * (b ^ j * b * (b ^ j)⁻¹) := by group
      _ = s⁻¹ ^ i * b := by
          congr 1
          group

theorem exists_pow_of_cube {c u : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hu : u ^ 3 = 1) :
    ∃ j : ℕ, u = c ^ j := by
  have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc1' : (c : K) ≠ 1 := fun h => hc1 (Units.ext h)
  have hu3 : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hc3' hc1' hu3 with h | h | h
  · exact ⟨0, Units.ext (by rw [h, pow_zero, Units.val_one])⟩
  · exact ⟨1, Units.ext (by rw [h, pow_one])⟩
  · exact ⟨2, Units.ext (by rw [h, Units.val_pow_eq_pow_val])⟩

theorem commute_of_conj_eq {G : Type*} [Group G] {a x g : G} (h : g * a * g⁻¹ = x * a * x⁻¹) :
    (x⁻¹ * g) * a = a * (x⁻¹ * g) := by
  calc (x⁻¹ * g) * a = x⁻¹ * (g * a * g⁻¹) * g := by group
    _ = x⁻¹ * (x * a * x⁻¹) * g := by rw [h]
    _ = a * (x⁻¹ * g) := by group

theorem centralizer_le_of_nonabelian (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (M : LModel π p f K T) {E : Subgroup T} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {a b : ↥(slPi π 3 (p ^ f) K)} (ha : M.μ a ∈ E) (hb : M.μ b ∈ E) (hab : a * b ≠ b * a)
    {t : T} (ht : ∀ e ∈ E, t * e = e * t) : t ∈ E := by
  have h3 := hK.three_ne_zero hq
  obtain ⟨c, hc3, hcdef⟩ := commutator_scalar hK M (g₁ := b) (g₂ := a) (hEc _ hb _ ha)
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hab
    rw [map_one] at hcdef
    have : (b : GL (Fin 3) K) * a = a * b := by
      calc (b : GL (Fin 3) K) * a = ((b : GL (Fin 3) K) * a * (b : GL (Fin 3) K)⁻¹ *
          (a : GL (Fin 3) K)⁻¹) * (a * b) := by group
        _ = a * b := by rw [hcdef, one_mul]
    exact Subtype.ext this.symm
  have hζ : (b : GL (Fin 3) K) * a * (b : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c * a := by
    calc (b : GL (Fin 3) K) * a * (b : GL (Fin 3) K)⁻¹ =
        ((b : GL (Fin 3) K) * a * (b : GL (Fin 3) K)⁻¹ * (a : GL (Fin 3) K)⁻¹) * a := by group
      _ = _ := by rw [hcdef]
  have hsc : ∀ g : GL (Fin 3) K, g * GeneralLinearGroup.scalar (Fin 3) c =
      GeneralLinearGroup.scalar (Fin 3) c * g := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g).eq
  obtain ⟨g, rfl⟩ := M.surjective t
  obtain ⟨ua, hua3, hua⟩ := commutator_scalar hK M (g₁ := g) (g₂ := a) (ht _ ha)
  obtain ⟨ub, hub3, hub⟩ := commutator_scalar hK M (g₁ := g) (g₂ := b) (ht _ hb)
  have hci3 : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have hci1 : c⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.mp h)
  obtain ⟨j, hj⟩ := exists_pow_of_cube hc3 hc1 hua3
  obtain ⟨i, hi⟩ := exists_pow_of_cube hci3 hci1 hub3
  set x : ↥(slPi π 3 (p ^ f) K) := b ^ j * a ^ i with hx
  have hxc : (x : GL (Fin 3) K) = (b : GL (Fin 3) K) ^ j * (a : GL (Fin 3) K) ^ i := by
    rw [hx]
    simp
  obtain ⟨hx1, hx2⟩ := heis_conj (a := (a : GL (Fin 3) K)) (b := (b : GL (Fin 3) K)) hsc hζ i j
  rw [← hxc] at hx1 hx2
  have hga : (g : GL (Fin 3) K) * a * (g : GL (Fin 3) K)⁻¹ =
      (x : GL (Fin 3) K) * a * (x : GL (Fin 3) K)⁻¹ := by
    rw [hx1, ← map_pow, ← hj]
    calc (g : GL (Fin 3) K) * a * (g : GL (Fin 3) K)⁻¹ =
        ((g : GL (Fin 3) K) * a * (g : GL (Fin 3) K)⁻¹ * (a : GL (Fin 3) K)⁻¹) * a := by group
      _ = _ := by rw [hua]
  have hgb : (g : GL (Fin 3) K) * b * (g : GL (Fin 3) K)⁻¹ =
      (x : GL (Fin 3) K) * b * (x : GL (Fin 3) K)⁻¹ := by
    rw [hx2, ← map_inv, ← map_pow, ← hi]
    calc (g : GL (Fin 3) K) * b * (g : GL (Fin 3) K)⁻¹ =
        ((g : GL (Fin 3) K) * b * (g : GL (Fin 3) K)⁻¹ * (b : GL (Fin 3) K)⁻¹) * b := by group
      _ = _ := by rw [hub]
  have hr := mem_statedScalars_of_commute_heis h3 hc1 hc3 hζ (r := (x : GL (Fin 3) K)⁻¹ * g)
    (commute_of_conj_eq hgb) (commute_of_conj_eq hga)
  have hμ : M.μ (x⁻¹ * g) = 1 := (M.ker_iff _).mpr (by simpa using hr)
  have hgx : M.μ g = M.μ x := by
    rw [map_mul, map_inv, inv_mul_eq_one] at hμ
    exact hμ.symm
  rw [hgx, hx, map_mul, map_pow, map_pow]
  exact mul_mem (pow_mem hb j) (pow_mem ha i)

theorem type_data (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {a : GL (Fin 3) K} (haL : a ∈ slPi π 3 (p ^ f) K) (haZ : a ∉ StatedScalars (Fin 3) K)
    (ha3 : a ^ 3 ∈ StatedScalars (Fin 3) K) :
    ∃ y : GL (Fin 3) K, (∃ z ∈ StatedScalars (Fin 3) K, y = a * z) ∧
      ((Nonempty (↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ≃*
          Multiplicative (ZMod (qSubPi π (p ^ f))) × Multiplicative (ZMod (qSubPi π (p ^ f)))) ∧
        (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}).relIndex
          (centMod (slPi π 3 (p ^ f) K) y) = 3) ∨
      ((∃ g ∈ glPi π 3 (p ^ f) K, ∃ e : Kˣ, e ≠ 1 ∧ g⁻¹ * y * g = diagE e) ∧
        centMod (slPi π 3 (p ^ f) K) y = slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y})) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπ := unitary_of hK
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have haH : a ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ haL
  have haZ' : a ∉ zPi π 3 (p ^ f) K := fun h =>
    haZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)
  have ha3' : a ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem haH 3, ha3⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 haH haZ' ha3'
  refine ⟨a * z, ⟨z, mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz, rfl⟩, ?_⟩
  rcases h with ⟨-, hiso, hrel⟩ | ⟨⟨g, hg, e, he, hD⟩, -, hcent⟩ | ⟨-, hirr, -⟩
  · exact Or.inl ⟨hiso, hrel⟩
  · refine Or.inr ⟨⟨g, hg, e, ?_, hD⟩, hcent⟩
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      simp at hτ
    rintro rfl
    rw [Units.val_one] at he
    rcases he with he | he
    · exact hτ1 he.symm
    · apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, ← he, div_one]
  · exact absurd ⟨a, haL, fun m _ => rfl⟩ (not_inner_of_type3 hK hq haH ⟨haZ', ha3', hirr⟩)

theorem blockHom_commute_diag (b : Kˣ) (B : GL (Fin 2) K) :
    blockHom B * diagUnits (b⁻¹ * b⁻¹) b b = diagUnits (b⁻¹ * b⁻¹) b b * blockHom B := by
  apply Units.ext
  simp only [Units.val_mul, coe_blockHom, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem exists_centralizing_pElement (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {r : ℕ} (hr : r.Prime) (hrN : r ∣ qSubPi π (p ^ f))
    {a : GL (Fin 3) K} (haL : a ∈ slPi π 3 (p ^ f) K) (haZ : a ∉ StatedScalars (Fin 3) K)
    (ha3 : a ^ 3 ∈ StatedScalars (Fin 3) K) {S : Set (GL (Fin 3) K)}
    (hSL : ∀ e ∈ S, e ∈ slPi π 3 (p ^ f) K) (hS : ∀ e ∈ S, e * a = a * e) :
    ∃ u ∈ slPi π 3 (p ^ f) K, u ^ r = 1 ∧ u ≠ 1 ∧ ∀ e ∈ S, u * e = e * u := by
  have := hK.finite
  have : Fact r.Prime := ⟨hr⟩
  have hπ := unitary_of hK
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := type_data hK hq haL haZ ha3
  have hzc : ∀ g : GL (Fin 3) K, g * z = z * g := fun g => commute_of_mem_statedScalars hz g
  have hSy : ∀ e ∈ S, e ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {a * z} := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨hSL e he, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc e * (a * z) = (e * a) * z := by rw [mul_assoc]
      _ = (a * e) * z := by rw [hS e he]
      _ = a * (e * z) := by rw [mul_assoc]
      _ = a * (z * e) := by rw [← hzc e]
      _ = a * z * e := by rw [mul_assoc]
  rcases hy with ⟨⟨eA⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -⟩
  ·
    set A := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {a * z} with hA
    have hAc : ∀ u v : ↥A, u * v = v * u := by
      intro u v
      apply eA.injective
      rw [map_mul, map_mul, mul_comm]
    have hN0 : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
    have hAcard : Nat.card A = qSubPi π (p ^ f) * qSubPi π (p ^ f) := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_prod]
      congr 1 <;> exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod _)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) r
      (by rw [hAcard]; exact dvd_mul_of_dvd_left hrN _)
    refine ⟨(u : GL (Fin 3) K), u.2.1, ?_, ?_, fun e he => ?_⟩
    · have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Subtype.val this
    · intro h1
      have : u = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hu
      exact hr.one_lt.ne hu
    · exact congrArg Subtype.val (hAc u ⟨e, hSy e he⟩)
  ·
    have hN0 : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(rootsOfUnity (qSubPi π (p ^ f)) K)) r
      (by rw [card_rootsOfUnity_qSubPi hK hq]; exact hrN)
    set c : Kˣ := (b : Kˣ) with hc
    have hcr : c ^ r = 1 := by
      have := pow_orderOf_eq_one b
      rw [hb] at this
      exact congrArg Subtype.val this
    have hc1 : c ≠ 1 := by
      intro h1
      have : b = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hb
      exact hr.one_lt.ne hb
    have hcN : c ∈ rootsOfUnity (qSubPi π (p ^ f)) K := b.2
    set u₀ : GL (Fin 3) K := diagUnits (c⁻¹ * c⁻¹) c c with hu₀
    have hu₀t : u₀ = torusHom (c⁻¹ * c⁻¹, c) := by
      rw [hu₀, torusHom]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk]
      congr 1
      group
    have hu₀L : u₀ ∈ slPi π 3 (p ^ f) K := by
      rw [hu₀t]
      exact torusHom_mem_slPi hK (mul_mem (inv_mem hcN) (inv_mem hcN)) hcN
    refine ⟨g * u₀ * g⁻¹, conj_mem_slPi hπ hg hu₀L, ?_, ?_, fun ε hε => ?_⟩
    · rw [conj_pow, hu₀t, ← map_pow]
      have : (c⁻¹ * c⁻¹, c) ^ r = 1 := by
        rw [Prod.pow_def, mul_pow, inv_pow, hcr]
        simp
      rw [this, map_one]
      group
    · intro h1
      have h2 : u₀ = 1 := by
        have : g⁻¹ * (g * u₀ * g⁻¹) * g = 1 := by rw [h1]; group
        simpa [mul_assoc] using this
      rw [hu₀t, ← map_one (torusHom (K := K))] at h2
      have h3 := torusHom_injective h2
      exact hc1 (congrArg Prod.snd h3)
    ·
      have hεy := hSy ε hε
      have hε' : g⁻¹ * ε * g ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE e} := by
        have h := map_conj_centralizer hπ (inv_mem hg) (a * z)
        have hm : (MulAut.conj g⁻¹) ε ∈
            (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {a * z}).map (MulAut.conj g⁻¹).toMonoidHom :=
          ⟨ε, hεy, rfl⟩
        rw [h, inv_inv, hD] at hm
        simpa [MulAut.conj_apply] using hm
      rw [centralizer_diagE_eq hK he] at hε'
      obtain ⟨B, -, hB⟩ := hε'
      have hcomm := blockHom_commute_diag c B
      rw [← hu₀] at hcomm
      rw [hB] at hcomm
      calc g * u₀ * g⁻¹ * ε = g * (u₀ * (g⁻¹ * ε * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * ε * g) * u₀) * g⁻¹ := by rw [← hcomm]
        _ = ε * (g * u₀ * g⁻¹) := by group

theorem μ_ne_one (hK : PiField π p f K) (M : LModel π p f K T) {r : ℕ} (hr : r.Prime)
    (hr3 : r ≠ 3) {u : ↥(slPi π 3 (p ^ f) K)} (hu : u ^ r = 1) (hu1 : u ≠ 1) : M.μ u ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (M.ker_iff u).mp h
  have hdet := det_eq_one hK u
  have hc3 : c ^ 3 = 1 := by
    rw [← hc, det_scalar_three] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  have hcr : c ^ r = 1 := by
    have h1 : ((u : GL (Fin 3) K)) ^ r = 1 := congrArg Subtype.val hu
    rw [← hc, ← map_pow] at h1
    exact scalar_injective_three (by rw [h1, map_one])
  have hcop : Nat.gcd 3 r = 1 := (Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3)
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hc3, hcr⟩
    rwa [hcop, pow_one] at this
  apply hu1
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem mem_centMod_of_commute (hK : PiField π p f K) (M : LModel π p f K T)
    {a ε : ↥(slPi π 3 (p ^ f) K)} {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (h : M.μ ε * M.μ a = M.μ a * M.μ ε) :
    (ε : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) ((a : GL (Fin 3) K) * z) := by
  obtain ⟨u, -, hu⟩ := commutator_scalar hK M h
  refine mem_centMod_iff_scalar.mpr ⟨ε.2, GeneralLinearGroup.scalar (Fin 3) u,
    ⟨u, rfl⟩, ?_⟩
  have hzc : (ε : GL (Fin 3) K) * z = z * ε := commute_of_mem_statedScalars hz ε
  calc (ε : GL (Fin 3) K) * (a * z) * (ε : GL (Fin 3) K)⁻¹ =
      ((ε : GL (Fin 3) K) * a * (ε : GL (Fin 3) K)⁻¹) * ((ε : GL (Fin 3) K) * z *
        (ε : GL (Fin 3) K)⁻¹) := by group
    _ = ((ε : GL (Fin 3) K) * a * (ε : GL (Fin 3) K)⁻¹ * (a : GL (Fin 3) K)⁻¹) * a * z := by
        rw [hzc]
        group
    _ = GeneralLinearGroup.scalar (Fin 3) u * (a * z) := by rw [hu, mul_assoc]

theorem mul_mem_of_mem_centMod {L : Subgroup (GL (Fin 3) K)} {y g t : GL (Fin 3) K}
    (hg : g ∈ centMod L y) (ht : t ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) :
    g * t * g⁻¹ ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
  obtain ⟨hgL, z, hz, hgy⟩ := mem_centMod_iff_scalar.mp hg
  refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem hgL ht.1) (L.inv_mem hgL), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x => commute_of_mem_statedScalars hz x
  have hzc' : ∀ x : GL (Fin 3) K, x * z⁻¹ = z⁻¹ * x := fun x => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hzc x, inv_mul_cancel_left]
  have hty : t * y = y * t := Subgroup.mem_centralizer_singleton_iff.mp ht.2
  have hy : y = z⁻¹ * (g * y * g⁻¹) := by rw [hgy]; group
  calc g * t * g⁻¹ * y = g * t * g⁻¹ * (z⁻¹ * (g * y * g⁻¹)) := by rw [← hy]
    _ = z⁻¹ * (g * t * g⁻¹) * (g * y * g⁻¹) := by
        rw [← mul_assoc, hzc' (g * t * g⁻¹)]
    _ = z⁻¹ * (g * (t * y) * g⁻¹) := by group
    _ = z⁻¹ * (g * (y * t) * g⁻¹) := by rw [hty]
    _ = z⁻¹ * (g * y * g⁻¹) * (g * t * g⁻¹) := by group
    _ = y * (g * t * g⁻¹) := by rw [← hy]

end CFSG.RankThree.PartTwo.Sec15.KS1424
