module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiIrred

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def ModNine (π : Bool) (q : ℕ) : Prop := cond π (q % 9 = 1) (q % 9 = 8)

theorem modNine_iff {q : ℕ} (hq1 : 1 ≤ q) : ModNine π q ↔ 9 ∣ qSubPi π q := by
  cases π
  · change q % 9 = 8 ↔ 9 ∣ q + 1
    omega
  · change q % 9 = 1 ↔ 9 ∣ q - 1
    omega

theorem eq_conj_of_inv_conj {g y D : GL (Fin 3) K} (h : g⁻¹ * y * g = D) :
    y = g * D * g⁻¹ := by
  rw [← h]
  group

theorem det_inv_conj (g y : GL (Fin 3) K) :
    GeneralLinearGroup.det (g⁻¹ * y * g) = GeneralLinearGroup.det y := by
  rw [map_mul, map_mul, map_inv, mul_comm _ (GeneralLinearGroup.det y), mul_assoc,
    inv_mul_cancel, mul_one]

theorem scalar_mem_glPi_iff (hK : PiField π p f K) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ glPi π 3 (p ^ f) K ↔
      c ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  cases π
  · rw [scalar_mem_glPi_false_iff hK.unitary, mem_rootsOfUnity, Units.ext_iff,
      Units.val_pow_eq_pow_val, Units.val_one]
    rfl
  · have := hK.finite
    exact ⟨fun _ => mem_rootsOfUnity_of_card (by simpa [piCard] using hK.card) c,
      fun _ => mem_glPi_true _ _⟩

theorem exists_scalar_of_mem_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {z : GL (Fin 3) K} (hz : z ∈ zPi π 3 (p ^ f) K) :
    ∃ ξ ∈ rootsOfUnity (qSubPi π (p ^ f)) K, GeneralLinearGroup.scalar (Fin 3) ξ = z := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  rw [zPi_eq hπ hq' hτ hτ1] at hz
  obtain ⟨hzH, ξ, rfl⟩ := Subgroup.mem_inf.mp hz
  exact ⟨ξ, (scalar_mem_glPi_iff hK ξ).mp hzH, rfl⟩

theorem scalar_mem_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ξ : Kˣ} (hξ : ξ ∈ rootsOfUnity (qSubPi π (p ^ f)) K) :
    GeneralLinearGroup.scalar (Fin 3) ξ ∈ zPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  rw [zPi_eq hπ hq' hτ hτ1]
  exact Subgroup.mem_inf.mpr ⟨(scalar_mem_glPi_iff hK ξ).mpr hξ, ⟨ξ, rfl⟩⟩

theorem det_diagE (e : Kˣ) : GeneralLinearGroup.det (diagE e) = e := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagE, det_diagonal, Fin.prod_univ_three]
  simp

theorem diagTau_pow_three {τ : K} (hτ : τ ^ 3 = 1) : diagTau hτ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal hτ, diagonal_pow, Units.val_one,
    ← diagonal_one]
  congr 1
  funext i
  have h6 : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, pow_mul', hτ, one_pow]
  fin_cases i <;> simp [hτ, h6]

theorem diagE_pow_three {e : Kˣ} (he : (e : K) ^ 3 = 1) : diagE e ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagE, diagonal_pow, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [he]

theorem cycThree_pow_conj_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) (k : ℕ) :
    cycThree ^ k * diagTau hτ * (cycThree ^ k)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ (2 * k)) * diagTau hτ := by
  have h1 : cycThree * diagTau hτ * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ := by
    apply Units.ext
    rw [cycThree_conj_diagTau hτ, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Units.val_pow_eq_pow_val, Units.val_mk0]
  induction k with
  | zero => simp
  | succ k ih =>
    have hsc : ∀ (s : Kˣ) (g : GL (Fin 3) K),
        g * GeneralLinearGroup.scalar (Fin 3) s = GeneralLinearGroup.scalar (Fin 3) s * g :=
      fun s g => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s g).eq
    calc cycThree ^ (k + 1) * diagTau hτ * (cycThree ^ (k + 1))⁻¹ =
        cycThree * (cycThree ^ k * diagTau hτ * (cycThree ^ k)⁻¹) * cycThree⁻¹ := by
          rw [pow_succ']
          group
      _ = cycThree * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ (2 * k)) *
          diagTau hτ) * cycThree⁻¹ := by rw [ih]
      _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ (2 * k)) *
          (cycThree * diagTau hτ * cycThree⁻¹) := by
          rw [← mul_assoc, hsc]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ (2 * (k + 1))) * diagTau hτ := by
          rw [h1, ← mul_assoc, ← map_mul, ← pow_add]
          ring_nf

theorem rank3II_4_10_one (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K)
    (hxZ : x ∉ zPi π 3 (p ^ f) K) (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) :
    ∃ y : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y = x * z) ∧
      (((∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y * g = diagTau hτ) ∧
          Nonempty (↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ≃*
            Multiplicative (ZMod (qSubPi π (p ^ f))) × Multiplicative (ZMod (qSubPi π (p ^ f)))) ∧
          (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}).relIndex
            (centMod (slPi π 3 (p ^ f) K) y) = 3) ∨
        ((∃ g ∈ glPi π 3 (p ^ f) K, ∃ e : Kˣ, ((e : K) = τ ∨ (e : K) = τ ^ 2) ∧
            g⁻¹ * y * g = diagE e) ∧
          Nonempty (↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ≃* glPi π 2 (p ^ f) K) ∧
          centMod (slPi π 3 (p ^ f) K) y = slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ∨
        (orderOf y = ordProj[3] (qSubPi π ((p ^ f) ^ 3)) ∧
          (∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
            W = ⊥ ∨ W = ⊤) ∧
          (∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
            W = ⊥ ∨ W = ⊤) ∧
          IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ∧
          Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) =
            qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f) ∧
          ∃ w ∈ slPi π 3 (p ^ f) K, orderOf w = 3 ∧
            w ∉ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} ∧
            centMod (slPi π 3 (p ^ f) K) y =
              (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ⊔ Subgroup.zpowers w ∧
            Nat.card ↥(slPi π 3 (p ^ f) K ⊓
              Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K))) = 3)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  rw [zPi_eq hπ hq' hτ hτ1] at hx3 hxZ
  obtain ⟨-, c, hc⟩ := Subgroup.mem_inf.mp hx3
  have hxs : x ∉ StatedScalars (Fin 3) K := fun h => hxZ (Subgroup.mem_inf.mpr ⟨hxH, h⟩)
  by_cases hcube : ∃ μ : K, μ ^ 3 = c
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [← hμ]; ring)
    have hxμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
      rw [← hc]
      congr 1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ]
    obtain ⟨y, ⟨z, hz, rfl⟩, g, hg, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hxμ
    refine ⟨x * z, ⟨z, hz, rfl⟩, ?_⟩
    rcases hD with hD | ⟨e, he, hD⟩
    · have hy := eq_conj_of_inv_conj hD
      refine Or.inl ⟨⟨g, hg, hD⟩, ?_, ?_⟩
      · obtain ⟨φ⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
        rw [hy, ← map_conj_centralizer hπ hg]
        exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans φ⟩
      · rw [hy, ← map_conj_centralizer hπ hg, ← map_conj_centMod hπ hg,
          Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
        exact relindex_centralizer_diagTau hK hq hτ hτ1
    · have hy := eq_conj_of_inv_conj hD
      have he3 : (e : K) ^ 3 = 1 := by
        rcases he with he | he <;> rw [he]
        · exact hτ
        · rw [← pow_mul, pow_mul', hτ, one_pow]
      have he1 : e ≠ 1 := by
        intro h1
        rw [h1, Units.val_one] at he
        rcases he with he | he
        · exact hτ1 he.symm
        · apply hτ1
          calc τ = τ ^ 3 / τ ^ 2 := by field_simp
            _ = 1 := by rw [hτ, ← he, div_one]
      refine Or.inr (Or.inl ⟨⟨g, hg, e, he, hD⟩, ?_, ?_⟩)
      · obtain ⟨φ⟩ := centralizer_diagE_mulEquiv (π := π) (p := p) (f := f) hK he1
        rw [hy, ← map_conj_centralizer hπ hg]
        exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans φ⟩
      · rw [hy, ← map_conj_centralizer hπ hg, ← map_conj_centMod hπ hg,
          centMod_diagE_eq π he3 h3]
  · push Not at hcube
    obtain ⟨y, hyxz, hord, hirrx, hirry, hcyc, hcard, w, hwL, hwo, hwC, hcent, hcard3⟩ :=
      irreducible_case hK hq hτ hτ1 hxH hc.symm hcube
    exact ⟨y, hyxz,
      Or.inr (Or.inr ⟨hord, hirrx, hirry, hcyc, hcard, w, hwL, hwo, hwC, hcent, hcard3⟩)⟩

theorem rank3II_4_10_two (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K)
    (hxZ : x ∉ zPi π 3 (p ^ f) K) (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) :
    (∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, x * m * x⁻¹ = l * m * l⁻¹) ↔
      (∃ y : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y = x * z) ∧
          ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y * g = diagTau hτ) ∨
        ((∃ y : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y = x * z) ∧
            ∃ g ∈ glPi π 3 (p ^ f) K, ∃ e : Kˣ, ((e : K) = τ ∨ (e : K) = τ ^ 2) ∧
              g⁻¹ * y * g = diagE e) ∧
          ModNine π (p ^ f)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  have hN0 := qSubPi_ne_zero hK hq
  have : NeZero (qSubPi π (p ^ f)) := ⟨hN0⟩
  have hTcard := card_rootsOfUnity_qSubPi hK hq
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  have he3 : ∀ e : Kˣ, ((e : K) = τ ∨ (e : K) = τ ^ 2) → (e : K) ^ 3 = 1 := by
    rintro e (he | he) <;> rw [he]
    · exact hτ
    · rw [← pow_mul, pow_mul', hτ, one_pow]
  have he1 : ∀ e : Kˣ, ((e : K) = τ ∨ (e : K) = τ ^ 2) → e ≠ 1 := by
    rintro e he rfl
    rw [Units.val_one] at he
    rcases he with he | he
    · exact hτ1 he.symm
    · apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, ← he, div_one]
  rw [inducesInner_iff hπ hq' hτ hτ1 hxH]
  constructor
  · rintro ⟨l, hl, z₀, hz₀, hx⟩
    have hdetl : GeneralLinearGroup.det l = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact ((mem_slPi_iff hπ).mp hl).2)
    obtain ⟨ζ₀, hζ₀, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz₀
    have hzx := hx3
    rw [zPi_eq hπ hq' hτ hτ1] at hzx
    obtain ⟨-, c, hc⟩ := Subgroup.mem_inf.mp hzx
    have hxs : x ∉ StatedScalars (Fin 3) K := fun h =>
      hxZ ((zPi_eq hπ hq' hτ hτ1) ▸ Subgroup.mem_inf.mpr ⟨hxH, h⟩)
    by_cases hcube : ∃ μ : K, μ ^ 3 = c
    · obtain ⟨μ, hμ⟩ := hcube
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        exact c.ne_zero (by rw [← hμ]; ring)
      have hxμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
        rw [← hc]
        congr 1
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ]
      obtain ⟨y, ⟨z, hz, rfl⟩, g, hg, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hxμ
      rcases hD with hD | ⟨e, he, hD⟩
      · exact Or.inl ⟨x * z, ⟨z, hz, rfl⟩, g, hg, hD⟩
      · refine Or.inr ⟨⟨x * z, ⟨z, hz, rfl⟩, g, hg, e, he, hD⟩, ?_⟩
        obtain ⟨ζ, hζ, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
        have hdet := det_inv_conj g (x * GeneralLinearGroup.scalar (Fin 3) ζ)
        have hdetsc : ∀ s : Kˣ, GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) s) =
            s ^ 3 := fun s => Units.ext (by
          rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
        rw [hD, det_diagE, hx, map_mul, map_mul, hdetl, one_mul, hdetsc, hdetsc, ← mul_pow]
          at hdet
        set ξ := ζ₀ * ζ
        have hξ : ξ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := mul_mem hζ₀ hζ
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hord : orderOf ξ = 3 ^ (1 + 1) := by
          refine orderOf_eq_prime_pow (by rw [pow_one, ← hdet]; exact he1 e he) ?_
          rw [show 3 ^ (1 + 1) = 3 * 3 by norm_num, pow_mul, ← hdet]
          exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact he3 e he)
        rw [modNine_iff hq1, show 9 = 3 ^ (1 + 1) by norm_num, ← hord]
        apply orderOf_dvd_of_pow_eq_one
        exact (mem_rootsOfUnity _ _).mp hξ
    ·
      push Not at hcube
      exfalso
      have hxm : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • 1 := by
        rw [← Units.val_pow_eq_pow_val, ← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
      have hdx := det_eq_of_cube hcube hxm
      apply hcube (ζ₀ : K)
      rw [← hdx, hx, Units.val_mul, det_mul, ← GeneralLinearGroup.val_det_apply, hdetl,
        Units.val_one, one_mul, det_scalar]
  · rintro (⟨_, ⟨z, hz, rfl⟩, g, hg, hD⟩ | ⟨⟨_, ⟨z, hz, rfl⟩, g, hg, e, he, hD⟩, h9⟩)
    · have hyL : x * z ∈ slPi π 3 (p ^ f) K := by
        rw [eq_conj_of_inv_conj hD]
        exact conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ)
      exact ⟨x * z, hyL, z⁻¹, inv_mem hz, by group⟩
    ·
      have h9' := (modNine_iff hq1).mp h9
      have he3' : e ^ 3 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact he3 e he)
      have hEmem : e⁻¹ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
        rw [mem_rootsOfUnity]
        obtain ⟨r, hr⟩ := dvd_trans (by norm_num : 3 ∣ 9) h9'
        rw [hr, pow_mul, inv_pow, he3', inv_one, one_pow]
      set E : rootsOfUnity (qSubPi π (p ^ f)) K := ⟨e⁻¹, hEmem⟩
      have hE : E ^ (Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / 3) = 1 := by
        rw [hTcard]
        obtain ⟨r, hr⟩ := h9'
        have h93 : qSubPi π (p ^ f) / 3 = 3 * r := by omega
        rw [h93, pow_mul]
        have : E ^ 3 = 1 := by
          apply Subtype.ext
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
          change e⁻¹ ^ 3 = 1
          rw [inv_pow, he3', inv_one]
        rw [this, one_pow]
      obtain ⟨s, hs⟩ := exists_pow_three_eq (by rw [hTcard]; exact three_dvd_qSubPi hq) hE
      set ξ := (s : Kˣ)
      have hξ3 : ξ ^ 3 = e⁻¹ := by
        have := congrArg (fun u : rootsOfUnity (qSubPi π (p ^ f)) K => (u : Kˣ)) hs
        simpa using this
      have hξZ := scalar_mem_zPi hK hq hτ hτ1 s.2
      have hyH : x * z ∈ glPi π 3 (p ^ f) K :=
        mul_mem hxH (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).1
      have hdet := det_inv_conj g (x * z)
      rw [hD, det_diagE] at hdet
      refine ⟨x * z * GeneralLinearGroup.scalar (Fin 3) ξ, ?_,
        (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ * z⁻¹, mul_mem (inv_mem hξZ) (inv_mem hz),
        by group⟩
      rw [mem_slPi_iff hπ]
      refine ⟨mul_mem hyH (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hξZ)).1, ?_⟩
      rw [Units.val_mul, det_mul, det_scalar, ← GeneralLinearGroup.val_det_apply, ← hdet,
        ← Units.val_pow_eq_pow_val, hξ3, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem rank3II_4_10_three (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K} (hxL : x ∈ slPi π 3 (p ^ f) K)
    (hxZ : x ∉ zPi π 3 (p ^ f) K) (hx : orderOf x = 3) :
    ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * x * g = diagTau hτ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hxH := slPi_le_glPi hπ hxL
  have hxs : x ∉ StatedScalars (Fin 3) K := fun h =>
    hxZ ((zPi_eq hπ hq' hτ hτ1) ▸ Subgroup.mem_inf.mpr ⟨hxH, h⟩)
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hx1 : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) (1 ^ 3) := by rw [hx3, one_pow, map_one]
  have hdetx : GeneralLinearGroup.det x = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact ((mem_slPi_iff hπ).mp hxL).2)
  obtain ⟨y, ⟨z, hz, rfl⟩, g, hg, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hx1
  obtain ⟨ζ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  have hsc : ∀ g : GL (Fin 3) K,
      g * GeneralLinearGroup.scalar (Fin 3) ζ = GeneralLinearGroup.scalar (Fin 3) ζ * g :=
    fun g => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq
  have hcube : ∀ D : GL (Fin 3) K, D ^ 3 = 1 →
      g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) * g = D → ζ ^ 3 = 1 := by
    intro D hD3 hgD
    have h1 : (x * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 = 1 := by
      rw [eq_conj_of_inv_conj hgD]
      calc (g * D * g⁻¹) ^ 3 = g * D ^ 3 * g⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul]
            group
        _ = 1 := by rw [hD3, mul_one, mul_inv_cancel]
    have h2 : (x * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 =
        GeneralLinearGroup.scalar (Fin 3) ζ ^ 3 := by
      rw [(show Commute x (GeneralLinearGroup.scalar (Fin 3) ζ) from hsc x).mul_pow, hx3,
        one_mul]
    apply scalar_injective_three
    rw [map_pow, map_one, ← h2, h1]
  rcases hD with hD | ⟨e, he, hD⟩
  · have hζ3 := hcube _ (diagTau_pow_three hτ) hD
    have hgx : g⁻¹ * x * g = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * diagTau hτ := by
      calc g⁻¹ * x * g = g⁻¹ * x * (g * GeneralLinearGroup.scalar (Fin 3) ζ) *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
        _ = g⁻¹ * x * (GeneralLinearGroup.scalar (Fin 3) ζ * g) *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by rw [hsc g]
        _ = g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) * g *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
        _ = diagTau hτ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by rw [hD, map_inv]
        _ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * diagTau hτ :=
          (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ _).eq
    have hζ3' : ((ζ⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, ← Units.val_pow_eq_pow_val, hζ3, Units.val_one,
        inv_one]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ζ⁻¹ = Units.mk0 τ hτ0 ^ (2 * k) := by
      rcases cube_root_cases hτ hτ1 hζ3' with h | h | h
      · exact ⟨0, Units.ext (by rw [h]; simp)⟩
      · refine ⟨2, Units.ext ?_⟩
        rw [h, Units.val_pow_eq_pow_val, Units.val_mk0]
        calc τ = τ ^ 3 * τ := by rw [hτ, one_mul]
          _ = τ ^ (2 * 2) := by ring
      · exact ⟨1, Units.ext (by rw [h, Units.val_pow_eq_pow_val, Units.val_mk0])⟩
    refine ⟨g * cycThree ^ k, mul_mem hg (pow_mem (slPi_le_glPi hπ (cycThree_mem_slPi hπ)) k),
      ?_⟩
    rw [hk, ← cycThree_pow_conj_diagTau hτ hτ0 k] at hgx
    calc (g * cycThree ^ k)⁻¹ * x * (g * cycThree ^ k) =
        (cycThree ^ k)⁻¹ * (g⁻¹ * x * g) * cycThree ^ k := by group
      _ = diagTau hτ := by rw [hgx]; group
  · exfalso
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have hζ3 := hcube _ (diagE_pow_three he3) hD
    have hdet := det_inv_conj g (x * GeneralLinearGroup.scalar (Fin 3) ζ)
    rw [hD, det_diagE, map_mul, hdetx, one_mul] at hdet
    have : e = ζ ^ 3 := by
      rw [hdet]
      exact Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
    rw [this, hζ3, Units.val_one] at he
    rcases he with he | he
    · exact hτ1 he.symm
    · apply hτ1
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, ← he, div_one]

end CFSG.RankThree.PartTwo.Sec4
