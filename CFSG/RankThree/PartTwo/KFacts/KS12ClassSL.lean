module

public import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section SL

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem diagUnits_mul_diagTau (u : Kˣ) {τ : K} (hτ : τ ^ 3 = 1) :
    diagUnits u 1 1 * diagTau hτ = diagTau hτ * diagUnits u 1 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagTau_eq_diagonal hτ,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem exists_conj_diagTau_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {d : GL (Fin 3) K} (hd : d ∈ slPi π 3 (p ^ f) K)
    (hd3 : d ^ 3 = 1) (hds : d ∉ StatedScalars (Fin 3) K) :
    ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ ∃ g ∈ slPi π 3 (p ^ f) K,
      g⁻¹ * (d * GeneralLinearGroup.scalar (Fin 3) ζ) * g = diagTau hτ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hdH : d ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hd
  have hμ : d ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((1 : Kˣ) ^ 3) := by
    rw [one_pow, map_one, hd3]
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hcase⟩ := exists_diag_normal_form hK hq hτ hτ1 hdH hds hμ
  have hzZ' := (zPi_eq hπ hq' hτ hτ1) ▸ hzZ
  obtain ⟨ζ, rfl⟩ := (Subgroup.mem_inf.mp hzZ').2
  have hdet_d : (d : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hd).2
  have hconjdet : ∀ D : GL (Fin 3) K,
      g⁻¹ * (d * GeneralLinearGroup.scalar (Fin 3) ζ) * g = D →
        (D : Matrix (Fin 3) (Fin 3) K).det = (ζ : K) ^ 3 := by
    intro D hD
    rw [← hD, Units.val_mul, Units.val_mul, det_mul, det_mul, Units.val_mul, det_mul, hdet_d,
      one_mul, det_scalar_three, mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one, one_mul]
  rcases hcase with hD | ⟨e, he, hD⟩
  ·
    have hζ3 : ζ ^ 3 = 1 := by
      have h1 := hconjdet _ hD
      rw [((mem_slPi_iff hπ).mp (diagTau_mem_slPi hπ hq' hτ)).2] at h1
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h1, Units.val_one])
    set u : Kˣ := (GeneralLinearGroup.det g)⁻¹ with hu
    have hur : u ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
      inv_mem (det_mem_rootsOfUnity hK hg)
    set g' := g * diagUnits u 1 1 with hg'
    have hg'H : g' ∈ glPi π 3 (p ^ f) K :=
      mul_mem hg (diagUnits_mem_glPi hK hur (one_mem _) (one_mem _))
    have hg'det : (g' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [hg', Units.val_mul, det_mul, coe_diagUnits, det_diagonal, Fin.prod_univ_three,
        ← GeneralLinearGroup.val_det_apply]
      simp only [hu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Units.val_one, mul_one, ← Units.val_mul,
        mul_inv_cancel]
    refine ⟨ζ, hζ3, g', (mem_slPi_iff hπ).mpr ⟨hg'H, hg'det⟩, ?_⟩
    have hc := diagUnits_mul_diagTau u hτ
    calc g'⁻¹ * (d * GeneralLinearGroup.scalar (Fin 3) ζ) * g'
        = (diagUnits u 1 1)⁻¹ * (g⁻¹ * (d * GeneralLinearGroup.scalar (Fin 3) ζ) * g) *
            diagUnits u 1 1 := by rw [hg']; group
      _ = (diagUnits u 1 1)⁻¹ * (diagUnits u 1 1 * diagTau hτ) := by rw [hD, mul_assoc, hc]
      _ = diagTau hτ := by group
  ·
    exfalso
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he
      · rw [he, hτ]
      · rw [he, ← pow_mul, mul_comm, pow_mul, hτ, one_pow]
    have hD3 : (diagE e : GL (Fin 3) K) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, coe_diagE, diagonal_pow, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [he3]
    have hy3 : (d * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 = 1 := by
      have h1 : g⁻¹ * (d * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 * g = 1 := by
        have h0 := conj_pow (a := g⁻¹) (b := d * GeneralLinearGroup.scalar (Fin 3) ζ) (i := 3)
        rw [inv_inv] at h0
        rw [← h0, hD, hD3]
      calc (d * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3
          = g * (g⁻¹ * (d * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 * g) * g⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    have hζ3 : ζ ^ 3 = 1 := by
      have hcz : Commute d (GeneralLinearGroup.scalar (Fin 3) ζ) :=
        CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ d
      rw [hcz.mul_pow, hd3, one_mul, ← map_pow] at hy3
      exact scalar_injective_three (by rw [hy3, map_one])
    have h1 := hconjdet _ hD
    rw [coe_diagE, det_diagonal, Fin.prod_univ_three] at h1
    have h2 : (e : K) = 1 := by
      have : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
      simpa [this] using h1
    rcases he with he | he
    · exact hτ1 (he ▸ h2)
    · apply hτ1
      have h3 : τ ^ 2 = 1 := he ▸ h2
      linear_combination hτ - τ * h3

theorem exists_conj_eq_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (T₁ T₂ : Subgroup (slPi π 3 (p ^ f) K)) (hT₁e : ∀ t ∈ T₁, t ^ 3 = 1) (hT₁9 : Nat.card T₁ = 9)
    (hZT₁ : Subgroup.center (slPi π 3 (p ^ f) K) ≤ T₁) (hT₂e : ∀ t ∈ T₂, t ^ 3 = 1)
    (hT₂9 : Nat.card T₂ = 9) (hZT₂ : Subgroup.center (slPi π 3 (p ^ f) K) ≤ T₂) :
    ∃ x : slPi π 3 (p ^ f) K, T₂ = T₁.map (MulAut.conj x).toMonoidHom := by
  have := hK.finite
  set Z := Subgroup.center (slPi π 3 (p ^ f) K) with hZdef
  have hZ3 : Nat.card Z = 3 := card_center_slPi hK hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have key : ∀ T : Subgroup (slPi π 3 (p ^ f) K), (∀ t ∈ T, t ^ 3 = 1) → Nat.card T = 9 →
      Z ≤ T → ∃ y ∈ T, y ∉ Z ∧ ∃ g : slPi π 3 (p ^ f) K,
        ((g⁻¹ * y * g : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = diagTau hτ := by
    intro T hTe hT9 hZT
    obtain ⟨d, hdT, hdZ⟩ : ∃ d ∈ T, d ∉ Z := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.card_le_of_le (show T ≤ Z from hcon)
      rw [hT9, hZ3] at this
      omega
    have hds : (d : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
      intro hs
      apply hdZ
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (commute_of_mem_statedScalars hs (g : GL (Fin 3) K))
    have hd3 : (d : GL (Fin 3) K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hTe d hdT, Subgroup.coe_one]
    obtain ⟨ζ, hζ3, g, hgS, hg⟩ := exists_conj_diagTau_slPi hK hq hτ hτ1 d.2 hd3 hds
    set s : slPi π 3 (p ^ f) K :=
      ⟨GeneralLinearGroup.scalar (Fin 3) ζ, scalar_mem_slPi_of_pow_three hK hq hζ3⟩
    have hsZ : s ∈ Z := Subgroup.mem_center_iff.mpr fun h =>
      Subtype.ext (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ (h : GL (Fin 3) K)).eq
    refine ⟨d * s, T.mul_mem hdT (hZT hsZ), fun hZ => hdZ ?_, ⟨g, hgS⟩, ?_⟩
    · have := Z.mul_mem hZ (Z.inv_mem hsZ)
      rwa [mul_inv_cancel_right] at this
    · rw [← hg]
      rfl
  obtain ⟨y₁, hy₁T, hy₁Z, g₁, hg₁⟩ := key T₁ hT₁e hT₁9 hZT₁
  obtain ⟨y₂, hy₂T, hy₂Z, g₂, hg₂⟩ := key T₂ hT₂e hT₂9 hZT₂
  set x := g₂ * g₁⁻¹ with hx
  have hxy : x * y₁ * x⁻¹ = y₂ := by
    have h1 : g₁⁻¹ * y₁ * g₁ = g₂⁻¹ * y₂ * g₂ := Subtype.ext (by rw [hg₁, hg₂])
    calc x * y₁ * x⁻¹ = g₂ * (g₁⁻¹ * y₁ * g₁) * g₂⁻¹ := by rw [hx]; group
      _ = y₂ := by rw [h1]; group
  refine ⟨x, ?_⟩
  set M := T₁.map (MulAut.conj x).toMonoidHom with hM
  have hM9 : Nat.card M = 9 := by
    rw [hM, Subgroup.card_map_of_injective (MulAut.conj x).injective, hT₁9]
  set I := M ⊓ T₂ with hI
  have hZI : Z ≤ I := by
    refine le_inf (fun z hz => ⟨z, hZT₁ hz, ?_⟩) hZT₂
    change x * z * x⁻¹ = z
    rw [Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right]
  have hy₂I : y₂ ∈ I := ⟨⟨y₁, hy₁T, hxy⟩, hy₂T⟩
  have hI9 : Nat.card I = 9 := by
    have hdvd : Nat.card I ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hT₂9]
      exact Subgroup.card_dvd_of_le inf_le_right
    have h3 : 3 ∣ Nat.card I := by
      have h0 := Subgroup.card_dvd_of_le hZI
      rwa [hZ3] at h0
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hk] at h3
      norm_num at h3
    · exfalso
      have hZeq : Z = I := Subgroup.eq_of_le_of_card_ge hZI (by rw [hk, hZ3, pow_one])
      exact hy₂Z (hZeq ▸ hy₂I)
    · rw [hk]
      norm_num
  have hIT : I = T₂ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hI9, hT₂9])
  have hT₂M : T₂ ≤ M := hIT ▸ inf_le_left
  exact Subgroup.eq_of_le_of_card_ge hT₂M (by rw [hM9, hT₂9])

end SL

theorem ks12ClassSL : KS12ClassSL := by
  intro X _ _ hX T₁ T₂ hT₁ hT₁9 hZT₁ hT₂ hT₂9 hZT₂
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨π, f, hK, hq, ⟨e⟩⟩ : ∃ (π : Bool) (f : ℕ), PiField π (ringChar K) f K ∧
      ModThree π (ringChar K ^ f) ∧ Nonempty (X ≃* slPi π 3 (ringChar K ^ f) K) := by
    rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
    · refine ⟨true, n, ⟨hp, n.2, hnc⟩, ?_, ⟨e⟩⟩
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, pow_zero] at hm
          rw [hm] at hq
          norm_num at hq
        · exact h0
      refine ⟨false, m, ⟨hp, hm1, by rw [hK, hm]; rfl⟩, ?_, ⟨hm ▸ e⟩⟩
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
  set S := slPi π 3 (ringChar K ^ f) K
  have hmapZ : (Subgroup.center X).map e.toMonoidHom = Subgroup.center S :=
    Subgroup.map_center_eq e
  have hT : ∀ T : Subgroup X, CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 9 →
      Subgroup.center X ≤ T → (∀ t ∈ T.map e.toMonoidHom, t ^ 3 = 1) ∧
        Nat.card (T.map e.toMonoidHom) = 9 ∧ Subgroup.center S ≤ T.map e.toMonoidHom := by
    intro T hTe hT9 hZT
    refine ⟨?_, by rw [Subgroup.card_map_of_injective e.injective, hT9], ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      rw [← map_pow, hTe.2 t ht, map_one]
    · rw [← hmapZ]
      exact Subgroup.map_mono hZT
  obtain ⟨h₁e, h₁9, h₁Z⟩ := hT T₁ hT₁ hT₁9 hZT₁
  obtain ⟨h₂e, h₂9, h₂Z⟩ := hT T₂ hT₂ hT₂9 hZT₂
  obtain ⟨x, hx⟩ := exists_conj_eq_slPi hK hq _ _ h₁e h₁9 h₁Z h₂e h₂9 h₂Z
  refine ⟨e.symm x, ?_⟩
  ext t
  constructor
  · intro ht
    have h1 : e t ∈ (T₁.map e.toMonoidHom).map (MulAut.conj x).toMonoidHom := hx ▸ ⟨t, ht, rfl⟩
    obtain ⟨_, ⟨t₁, ht₁, rfl⟩, h2⟩ := h1
    refine ⟨t₁, ht₁, e.injective ?_⟩
    rw [← h2]
    simp [map_mul, map_inv]
  · rintro ⟨t₁, ht₁, rfl⟩
    have h1 : e (e.symm x * t₁ * (e.symm x)⁻¹) ∈ T₂.map e.toMonoidHom := by
      rw [hx]
      refine ⟨e t₁, ⟨t₁, ht₁, rfl⟩, ?_⟩
      simp [map_mul, map_inv]
    obtain ⟨t₂, ht₂, h2⟩ := h1
    have : t₂ = e.symm x * t₁ * (e.symm x)⁻¹ := e.injective h2
    change e.symm x * t₁ * (e.symm x)⁻¹ ∈ T₂
    rw [← this]
    exact ht₂

theorem ks12ClassT :
    KS12ClassT :=
  ks12ClassT_of ks12OutInner ks12ClassSL

end CFSG.RankThree.PartTwo.KFacts
