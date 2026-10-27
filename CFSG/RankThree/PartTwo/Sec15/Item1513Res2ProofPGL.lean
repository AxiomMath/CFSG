module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTransv
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldTwo
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Proof1513Res2

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Sylow

variable {M : Type*} [Group M] [Finite M]

theorem pow_three_eq_one_of_not_dvd (h27 : ¬ 27 ∣ Nat.card M) {H : Subgroup M}
    (hH : CFSG.Assembly.IsElemAbelian 3 H) (hH9 : Nat.card H = 9) {x : M} {v : ℕ}
    (hx : x ^ 3 ^ v = 1) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    have hord : orderOf x ∣ 3 ^ v := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  have hHp : IsPGroup 3 H := IsPGroup.of_card (n := 2) (by rw [hH9]; norm_num)
  obtain ⟨S', hS'⟩ := hHp.exists_le_sylow
  have hk : (Nat.card M).factorization 3 ≤ 2 := by
    by_contra hlt
    push Not at hlt
    apply h27
    exact (pow_dvd_pow 3 hlt).trans (Nat.ordProj_dvd (Nat.card M) 3)
  have hS'card : Nat.card (S' : Subgroup M) ≤ 9 := by
    rw [Sylow.card_eq_multiplicity]
    calc 3 ^ (Nat.card M).factorization 3 ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 9 := by norm_num
  have hS'H : (S' : Subgroup M) = H :=
    (Subgroup.eq_of_le_of_card_ge hS' (by rw [hH9]; exact hS'card)).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S' S
  have hxS : x ∈ (S : Subgroup M) := hS (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, hS'H] at hxS
  obtain ⟨h, hh, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hxS
  rw [MulAut.smul_def, ← map_pow, hH.2 h hh, map_one]

end Sylow

section Hessian

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_hessian (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ H : Subgroup (projImage (slPi π 3 (p ^ f) K)), CFSG.Assembly.IsElemAbelian 3 H ∧
      Nat.card H = 9 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set M := projImage (slPi π 3 (p ^ f) K) with hM
  set d : M := ⟨ProjGenLinGroup.mk (diagTau hτ),
    Subgroup.mem_map_of_mem _ (diagTau_mem_slPi hπ hq' hτ)⟩ with hd
  set c : M := ⟨ProjGenLinGroup.mk cycThree,
    Subgroup.mem_map_of_mem _ (cycThree_mem_slPi hπ)⟩ with hc
  have hd3 : d ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hd, ← map_pow, diagTau_pow_three hτ, map_one, Subgroup.coe_one])
  have hc3 : c ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hc, ← map_pow, cycThree_pow_three, map_one, Subgroup.coe_one])
  have hd1 : d ≠ 1 := fun h =>
    Sec13.Item138Proof.mk_diagTau_ne_one hτ hτ1 (congrArg Subtype.val h)
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdc : d * c = c * d := Subtype.ext (mk_diagTau_cycThree hτ)
  have hcd : c ∉ Subgroup.zpowers d := by
    rintro ⟨k, hk⟩
    have hk' : ProjGenLinGroup.mk (diagTau hτ) ^ k = ProjGenLinGroup.mk cycThree := by
      have := congrArg Subtype.val hk
      simpa [hd, hc] using this
    have R3 := mk_phase_diagTau hτ
    have R4 := mk_phase_cycThree hτ
    set T := ProjGenLinGroup.mk (phaseGL hτ)
    set D := ProjGenLinGroup.mk (diagTau hτ)
    set C := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
    have hTk : T * D ^ k * T⁻¹ = D ^ k := by
      rw [← conj_zpow, R3]
    rw [hk'] at hTk
    rw [hTk] at R4
    apply Sec13.Item138Proof.mk_diagTau_ne_one hτ hτ1
    calc D = D * C * C⁻¹ := by group
      _ = 1 := by rw [← R4, mul_inv_cancel]
  refine ⟨Subgroup.zpowers d ⊔ Subgroup.zpowers c,
    Sec13.isElemAbelian_zpowers_sup hd3 hc3 hdc, ?_⟩
  exact card_zpowers_sup_zpowers hc3 hdo hcd hdc.symm

theorem pow_three_eq_one_of_mem_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) {x : ProjGenLinGroup (Fin 3) K}
    (hx : x ∈ projImage (slPi π 3 (p ^ f) K)) {v : ℕ} (hxv : x ^ 3 ^ v = 1) : x ^ 3 = 1 := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  obtain ⟨H, hH, hH9⟩ := exists_hessian hK hq
  have h27 := KSL3Two.not_dvd_card_projImage hK hq h9
  have h := pow_three_eq_one_of_not_dvd h27 hH hH9 (x := ⟨x, hx⟩) (v := v)
    (Subtype.ext (by simpa using hxv))
  simpa using congrArg Subtype.val h

end Hessian

section Frame

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem scalar_mul_comm (u : Kˣ) (A : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) u * A = A * GeneralLinearGroup.scalar (Fin 3) u :=
  (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq.symm

theorem conj_scalar_mul (x : GL (Fin 3) K) (u : Kˣ) (A : GL (Fin 3) K) :
    x * (GeneralLinearGroup.scalar (Fin 3) u * A) * x⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u * (x * A * x⁻¹) := by
  calc x * (GeneralLinearGroup.scalar (Fin 3) u * A) * x⁻¹
      = (x * GeneralLinearGroup.scalar (Fin 3) u) * A * x⁻¹ := by group
    _ = (GeneralLinearGroup.scalar (Fin 3) u * x) * A * x⁻¹ := by rw [scalar_mul_comm u x]
    _ = GeneralLinearGroup.scalar (Fin 3) u * (x * A * x⁻¹) := by group

theorem inv_mul_scalar_mul (x : GL (Fin 3) K) (u : Kˣ) :
    x⁻¹ * GeneralLinearGroup.scalar (Fin 3) u * x = GeneralLinearGroup.scalar (Fin 3) u := by
  rw [mul_assoc, scalar_mul_comm u x, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_back_of_eq (g c a : GL (Fin 3) K) (u : Kˣ)
    (hu : g * c * g⁻¹ * a * (g * c * g⁻¹)⁻¹ * GeneralLinearGroup.scalar (Fin 3) u = a) :
    c * (g⁻¹ * a * g) * c⁻¹ * GeneralLinearGroup.scalar (Fin 3) u = g⁻¹ * a * g := by
  calc c * (g⁻¹ * a * g) * c⁻¹ * GeneralLinearGroup.scalar (Fin 3) u
      = c * (g⁻¹ * a * g) * c⁻¹ * (g⁻¹ * GeneralLinearGroup.scalar (Fin 3) u * g) := by
        rw [inv_mul_scalar_mul]
    _ = g⁻¹ * (g * c * g⁻¹ * a * (g * c * g⁻¹)⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) * g := by
        group
    _ = g⁻¹ * a * g := by rw [hu]

theorem diagUnits_mul_scalar_ne {τ : Kˣ} (hτ : τ ≠ 1) (u : Kˣ) :
    diagUnits 1 1 τ * GeneralLinearGroup.scalar (Fin 3) u ≠ diagUnits 1 τ 1 := by
  intro h
  have e0 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have e1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp only [Units.val_mul, coe_diagUnits, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_mul_diagonal, diagonal_apply_eq] at e0 e1
  simp at e0 e1
  apply hτ
  apply Units.ext
  rw [← e1, e0, Units.val_one]

theorem diagUnits_eq_scalar_mul (s t : Kˣ) :
    diagUnits t 1 s = GeneralLinearGroup.scalar (Fin 3) t * diagUnits 1 t⁻¹ (s * t⁻¹) := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits,
    coe_diagUnits, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp
  field_simp

theorem det_conj_eq (g a : GL (Fin 3) K) :
    ((g * a * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (a : Matrix (Fin 3) (Fin 3) K).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem exists_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (ProjGenLinGroup (Fin 3) K)} (hEP : E ≤ projImage (glPi π 3 (p ^ f) K))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    (hd : ∀ y : GL (Fin 3) K, ProjGenLinGroup.mk y ∈ E →
      ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i) :
    ∃ s ∈ projImage (slPi π 3 (p ^ f) K), s ^ 3 = 1 ∧
      s ∈ Subgroup.normalizer (E : Set (ProjGenLinGroup (Fin 3) K)) ∧
      s ∉ Subgroup.centralizer (E : Set (ProjGenLinGroup (Fin 3) K)) := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set D : Subgroup (GL (Fin 3) K) := E.comap ProjGenLinGroup.mk ⊓ glPi π 3 (p ^ f) K with hD
  have hmemD : ∀ y, y ∈ D ↔ ProjGenLinGroup.mk y ∈ E ∧ y ∈ glPi π 3 (p ^ f) K :=
    fun y => Iff.rfl
  have hDE : D.map ProjGenLinGroup.mk = E := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ((hmemD y).mp hy).1
    · intro e he
      obtain ⟨y, hy, rfl⟩ := hEP he
      exact ⟨y, (hmemD y).mpr ⟨he, hy⟩, rfl⟩
  have hcardD : Nat.card ↥(D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K))) = 9 := by
    have hker : ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp D.subtype).ker =
        ((ProjGenLinGroup.mk : GL (Fin 3) K →* _).comp D.subtype).ker := by
      ext y
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mk_eq_one_iff_mem_statedScalars.symm
    have h1 := card_range_eq_of_ker_eq _ _ hker
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, hDE, hE9] at h1
    exact h1
  have hC : IsTypeC π (p ^ f) K D := by
    refine ⟨inf_le_right, fun a ha => ?_, hcardD, b, hb, fun a ha => hd a ((hmemD a).mp ha).1⟩
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow]
    exact hE.2 _ ((hmemD a).mp ha).1
  obtain ⟨g, hg, hconj, hsurj⟩ := isTypeC_conj_std hK hq hC
  set c₀ : GL (Fin 3) K := cycThree with hc₀
  set σ := g * c₀ * g⁻¹ with hσ
  have hcS : c₀ ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hσS : σ ∈ slPi π 3 (p ^ f) K := by
    have hcS' := (mem_slPi_iff hπ).mp hcS
    refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hg hcS'.1) (inv_mem hg), ?_⟩
    rw [hσ, det_conj_eq]
    exact hcS'.2
  refine ⟨ProjGenLinGroup.mk σ, Subgroup.mem_map_of_mem _ hσS, ?_, ?_, ?_⟩
  · rw [← map_pow, hσ, conj_pow, hc₀, cycThree_pow_three, mul_one, mul_inv_cancel, map_one]
  · refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨y, hy, rfl⟩ := hEP he
    have hyD : y ∈ D := (hmemD y).mpr ⟨he, hy⟩
    obtain ⟨l, s, t, hs, ht, hl⟩ := hconj y hyD
    obtain ⟨a, haD, l', hl'⟩ := hsurj t⁻¹ (inv_mem ht) (s * t⁻¹) (mul_mem hs (inv_mem ht))
    have key : σ * y * σ⁻¹ = GeneralLinearGroup.scalar (Fin 3) (l * t * l'⁻¹) * a := by
      have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
        rw [← hl]
        group
      have ha' : a = g * (GeneralLinearGroup.scalar (Fin 3) l' * diagUnits 1 t⁻¹ (s * t⁻¹)) *
          g⁻¹ := by
        rw [← hl']
        group
      have hcd : c₀ * diagUnits 1 s t * c₀⁻¹ = diagUnits t 1 s := cycThree_conj_diagUnits 1 s t
      rw [diagUnits_eq_scalar_mul] at hcd
      calc σ * y * σ⁻¹
          = g * (c₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * c₀⁻¹) * g⁻¹ := by
            rw [hy', hσ]
            group
        _ = g * (GeneralLinearGroup.scalar (Fin 3) l * (c₀ * diagUnits 1 s t * c₀⁻¹)) *
              g⁻¹ := by
            rw [conj_scalar_mul c₀ l]
        _ = g * (GeneralLinearGroup.scalar (Fin 3) (l * t * l'⁻¹) *
              (GeneralLinearGroup.scalar (Fin 3) l' * diagUnits 1 t⁻¹ (s * t⁻¹))) * g⁻¹ := by
            rw [hcd]
            congr 2
            simp only [map_mul, map_inv]
            group
        _ = GeneralLinearGroup.scalar (Fin 3) (l * t * l'⁻¹) * a := by
            rw [conj_scalar_mul g, ha']
    show ProjGenLinGroup.mk σ * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk σ)⁻¹ ∈ E
    rw [← map_inv, ← map_mul, ← map_mul, key, map_mul, ProjGenLinGroup.mk_scalar, one_mul]
    exact ((hmemD a).mp haD).1
  · intro hcen
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      simp at hτ
    set τu : Kˣ := Units.mk0 τ hτ0 with hτu
    have hτu3 : τu ∈ rootsOfUnity 3 K := by
      rw [mem_rootsOfUnity]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ, Units.val_one])
    obtain ⟨a, haD, l, hl⟩ := hsurj τu hτu3 1 (one_mem _)
    have hcomm := Subgroup.mem_centralizer_iff.mp hcen (ProjGenLinGroup.mk a)
      ((hmemD a).mp haD).1
    have h1 : ProjGenLinGroup.mk (σ * a * σ⁻¹) = ProjGenLinGroup.mk a := by
      rw [map_mul, map_mul, map_inv, ← hcomm]
      group
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
    have h2 := conj_back_of_eq g c₀ a u hu
    rw [hl, conj_scalar_mul c₀ l, hc₀, cycThree_conj_diagUnits, mul_assoc] at h2
    have hτu1 : τu ≠ 1 := fun h => hτ1 (by rw [← Units.val_mk0 hτ0, ← hτu, h, Units.val_one])
    exact diagUnits_mul_scalar_ne hτu1 u (mul_left_cancel h2)

end Frame

section HeisMatrices

variable {K : Type} [Field K]

theorem eq_tau_or_sq {τ c : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hc : c ^ 3 = 1) (hc1 : c ≠ 1) :
    c = τ ∨ c = τ ^ 2 := by
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have h : (c - 1) * ((c - τ) * (c - τ ^ 2)) = 0 := by
    linear_combination hc - c ^ 2 * hs + c * hτ + c * hs - hτ
  have h' : (c - τ) * (c - τ ^ 2) = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc1)
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h1)

theorem entry_aux {a di dj si sj δi ζ : K} (h : di ≠ ζ * dj ∨ si = δi * sj)
    (hrel : di * a = ζ * (a * dj)) : si * a = δi * a * sj := by
  rcases h with h | h
  · have ha : a = 0 := by
      have h1 : (di - ζ * dj) * a = 0 := by linear_combination hrel
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr h)
    rw [ha]
    ring
  · rw [h]
    ring

theorem pow_eq_pow_iff_mod {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (a b : ℕ) :
    τ ^ a = τ ^ b ↔ a % 3 = b % 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf τ = 3 := orderOf_eq_prime hτ hτ1
  have h0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hu : IsUnit τ := isUnit_iff_ne_zero.mpr h0
  constructor
  · intro h
    have h' : (hu.unit) ^ a = (hu.unit) ^ b := Units.ext (by simpa using h)
    have hordu : orderOf hu.unit = 3 := by rw [← orderOf_units, IsUnit.unit_spec, hord]
    rw [pow_eq_pow_iff_modEq, hordu] at h'
    exact h'
  · intro h
    rw [← pow_mod_orderOf, hord, h, ← hord, pow_mod_orderOf]

theorem cond_of_mod {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (e f : Fin 3 → ℕ) (m r k : ℕ)
    (h : ∀ i j, e i % 3 ≠ (m + e j) % 3 ∨ f i % 3 = (r + k * e i + f j) % 3) :
    ∀ i j, τ ^ (e i) ≠ τ ^ m * τ ^ (e j) ∨ τ ^ (f i) = τ ^ r * (τ ^ (e i)) ^ k * τ ^ (f j) := by
  intro i j
  rcases h i j with h | h
  · left
    intro h'
    rw [← pow_add] at h'
    exact h ((pow_eq_pow_iff_mod hτ hτ1 _ _).mp h')
  · right
    rw [← pow_mul, ← pow_add, ← pow_add, pow_eq_pow_iff_mod hτ hτ1, mul_comm (e i) k]
    exact h

theorem diag_mul_of_rel {d s δ : Fin 3 → K} {ζ : K} {Y : Matrix (Fin 3) (Fin 3) K}
    (hrel : diagonal d * Y = ζ • (Y * diagonal d))
    (hc : ∀ i j, d i ≠ ζ * d j ∨ s i = δ i * s j) :
    diagonal s * Y = diagonal δ * Y * diagonal s := by
  ext i j
  have hij := congrFun (congrFun hrel i) j
  simp only [diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  exact entry_aux (hc i j) hij

theorem vec_diagTau_eq (τ : K) : (![τ, τ ^ 2, 1] : Fin 3 → K) = fun i => τ ^ ((![1, 2, 0] :
    Fin 3 → ℕ) i) := by
  funext i
  fin_cases i <;> simp

theorem vec_phase_eq (τ : K) : (![1, τ, 1] : Fin 3 → K) = fun i => τ ^ ((![0, 1, 0] :
    Fin 3 → ℕ) i) := by
  funext i
  fin_cases i <;> simp

theorem diag_mul_of_tau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {Y : Matrix (Fin 3) (Fin 3) K}
    (hrel : diagonal ![τ, τ ^ 2, 1] * Y = τ • (Y * diagonal ![τ, τ ^ 2, 1])) :
    diagonal ![1, τ, 1] * Y = diagonal (fun i => τ ^ 2 * (![τ, τ ^ 2, 1] : Fin 3 → K) i) * Y *
      diagonal ![1, τ, 1] := by
  rw [vec_diagTau_eq] at hrel ⊢
  rw [vec_phase_eq]
  refine diag_mul_of_rel hrel fun i j => ?_
  have h := cond_of_mod hτ hτ1 ![1, 2, 0] ![0, 1, 0] 1 2 1 (by decide) i j
  simpa only [pow_one] using h

theorem diag_mul_of_tau_sq {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Y : Matrix (Fin 3) (Fin 3) K}
    (hrel : diagonal ![τ, τ ^ 2, 1] * Y = τ ^ 2 • (Y * diagonal ![τ, τ ^ 2, 1])) :
    diagonal ![1, τ, 1] * Y = diagonal (fun i => ((![τ, τ ^ 2, 1] : Fin 3 → K) i) ^ 2) * Y *
      diagonal ![1, τ, 1] := by
  rw [vec_diagTau_eq] at hrel ⊢
  rw [vec_phase_eq]
  refine diag_mul_of_rel hrel fun i j => ?_
  have h := cond_of_mod hτ hτ1 ![1, 2, 0] ![0, 1, 0] 2 0 2 (by decide) i j
  simpa only [pow_zero, one_mul] using h

end HeisMatrices

section HeisGL

variable {K : Type} [Field K]

theorem coe_scalar_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (u : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (u : K) * (![τ, τ ^ 2, 1] : Fin 3 → K) i) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagTau_eq_diagonal,
    diagonal_mul_diagonal]

theorem coe_diagTau_sq {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagTau hτ ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => ((![τ, τ ^ 2, 1] : Fin 3 → K) i) ^ 2) := by
  rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, diagonal_pow]
  rfl

theorem coe_diagUnits_phase {τ : K} (hτ0 : τ ≠ 0) :
    ((diagUnits 1 (Units.mk0 τ hτ0) 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![1, τ, 1] := by
  rw [coe_diagUnits]
  simp

theorem diagUnits_pow_three_eq_one {τu : Kˣ} (h : τu ∈ rootsOfUnity 3 K) :
    diagUnits 1 τu 1 ^ 3 = 1 := by
  have h3 : (τu : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp h, Units.val_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagUnits, diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h3]

theorem heis_conj {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hτ0 : τ ≠ 0) {g X y : GL (Fin 3) K}
    {ζ : Kˣ} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hD : g⁻¹ * X * g = diagTau hτ)
    (hrel : X * y * X⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y) :
    (g * diagUnits 1 (Units.mk0 τ hτ0) 1 * g⁻¹) * X =
        X * (g * diagUnits 1 (Units.mk0 τ hτ0) 1 * g⁻¹) ∧
      ((g * diagUnits 1 (Units.mk0 τ hτ0) 1 * g⁻¹) * y *
          (g * diagUnits 1 (Units.mk0 τ hτ0) 1 * g⁻¹)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * X * y ∨
        (g * diagUnits 1 (Units.mk0 τ hτ0) 1 * g⁻¹) * y *
          (g * diagUnits 1 (Units.mk0 τ hτ0) 1 * g⁻¹)⁻¹ = X ^ 2 * y) := by
  set S : GL (Fin 3) K := diagUnits 1 (Units.mk0 τ hτ0) 1 with hS
  set D : GL (Fin 3) K := diagTau hτ with hDdef
  have hX : X = g * D * g⁻¹ := by
    rw [← hD]
    group
  have hSD : S * D = D * S := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hS, coe_diagUnits_phase, hDdef, coe_diagTau_eq_diagonal,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  refine ⟨?_, ?_⟩
  · rw [hX]
    calc g * S * g⁻¹ * (g * D * g⁻¹) = g * (S * D) * g⁻¹ := by group
      _ = g * (D * S) * g⁻¹ := by rw [hSD]
      _ = g * D * g⁻¹ * (g * S * g⁻¹) := by group
  obtain ⟨Y, hY⟩ : ∃ Y, Y = g⁻¹ * y * g := ⟨_, rfl⟩
  have hYrel : D * Y * D⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * Y := by
    rw [hY, ← hD]
    calc g⁻¹ * X * g * (g⁻¹ * y * g) * (g⁻¹ * X * g)⁻¹ = g⁻¹ * (X * y * X⁻¹) * g⁻¹⁻¹ := by
          group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ * y) * g⁻¹⁻¹ := by rw [hrel]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * (g⁻¹ * y * g) := by
          rw [conj_scalar_mul, inv_inv]
  have hmat : (D : Matrix (Fin 3) (Fin 3) K) * Y =
      (ζ : K) • ((Y : Matrix (Fin 3) (Fin 3) K) * D) := by
    have h1 : D * Y = GeneralLinearGroup.scalar (Fin 3) ζ * Y * D := by
      rw [← hYrel]
      group
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul] at h2
    exact h2
  rw [hDdef, coe_diagTau_eq_diagonal] at hmat
  have hζ3K : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hζ1K : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  have hconj : (g * S * g⁻¹) * y * (g * S * g⁻¹)⁻¹ = g * (S * Y * S⁻¹) * g⁻¹ := by
    rw [hY]
    group
  rcases eq_tau_or_sq hτ hτ1 hζ3K hζ1K with hζτ | hζτ
  · left
    rw [hζτ] at hmat
    have hm := diag_mul_of_tau hτ hτ1 hmat
    have hG : S * Y = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * D) * Y * S := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hS, coe_diagUnits_phase, hDdef,
        coe_scalar_mul_diagTau, Units.val_pow_eq_pow_val, Units.val_mk0]
      exact hm
    have hG' : S * Y * S⁻¹ = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * D) * Y := by
      rw [hG]
      group
    rw [hconj, hG', hX, hY]
    calc g * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * D * (g⁻¹ * y * g)) * g⁻¹
        = g * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) *
            (D * (g⁻¹ * y * g))) * g⁻¹ := by rw [mul_assoc (GeneralLinearGroup.scalar _ _)]
      _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) *
            (g * (D * (g⁻¹ * y * g)) * g⁻¹) := by rw [conj_scalar_mul]
      _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * (g * D * g⁻¹) * y := by
          group
  · right
    rw [hζτ] at hmat
    have hm := diag_mul_of_tau_sq hτ hτ1 hmat
    have hG : S * Y = D ^ 2 * Y * S := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hS, coe_diagUnits_phase, hDdef,
        coe_diagTau_sq]
      exact hm
    have hG' : S * Y * S⁻¹ = D ^ 2 * Y := by
      rw [hG]
      group
    rw [hconj, hG', hX, hY, conj_pow]
    group

end HeisGL

section Quot

variable {K : Type} [Field K]

@[expose] noncomputable def pglEquivQuot (K : Type) [Field K] :
    ProjGenLinGroup (Fin 3) K ≃* GL (Fin 3) K ⧸ StatedScalars (Fin 3) K :=
  QuotientGroup.quotientMulEquivOfEq (GeneralLinearGroup.center_eq_range_scalar)

theorem pglEquivQuot_mk (y : GL (Fin 3) K) :
    pglEquivQuot K (ProjGenLinGroup.mk y) = (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := rfl

theorem mem_map_pglEquivQuot {E : Subgroup (ProjGenLinGroup (Fin 3) K)} {y : GL (Fin 3) K} :
    (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E.map (pglEquivQuot K).toMonoidHom ↔
      ProjGenLinGroup.mk y ∈ E := by
  rw [← pglEquivQuot_mk, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem map_pglEquivQuot_facts {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    (∀ x ∈ E.map (pglEquivQuot K).toMonoidHom, ∀ y ∈ E.map (pglEquivQuot K).toMonoidHom,
      x * y = y * x) ∧ (∀ x ∈ E.map (pglEquivQuot K).toMonoidHom, x ^ 3 = 1) ∧
      Nat.card (E.map (pglEquivQuot K).toMonoidHom) = Nat.card E := by
  have hE' := Sec13.isElemAbelian_map hE (pglEquivQuot K).toMonoidHom
  refine ⟨fun x hx y hy => congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
    hE'.2, Subgroup.card_map_of_injective (pglEquivQuot K).injective⟩

theorem card_le_nine_pgl (h3 : (3 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {E : Subgroup (ProjGenLinGroup (Fin 3) K)} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  obtain ⟨hc, he, hcard⟩ := map_pglEquivQuot_facts hE
  rw [← hcard]
  exact card_le_nine_of_comm h3 hτ hτ1 _ hc he

theorem exists_scalar_of_mk_comm {y y' : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk y * ProjGenLinGroup.mk y' =
      ProjGenLinGroup.mk y' * ProjGenLinGroup.mk y) :
    ∃ c : Kˣ, y * y' * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * y' := by
  have h1 : y * y' * y⁻¹ * y'⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩

theorem mk_ne_one_of_heis {y y' : GL (Fin 3) K} {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y * y' * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y') :
    ProjGenLinGroup.mk y ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ := mk_eq_one_iff_mem_statedScalars.mp h
  rw [← hu, scalar_mul_comm, mul_inv_cancel_right] at hζ
  apply hζ1
  have h2 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
    calc GeneralLinearGroup.scalar (Fin 3) ζ = GeneralLinearGroup.scalar (Fin 3) ζ * y' * y'⁻¹ := by
          group
      _ = 1 := by rw [← hζ, mul_inv_cancel]
  have h3 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h2
  simp [GeneralLinearGroup.coe_scalar] at h3
  exact h3

theorem mk_not_mem_zpowers_of_heis {y y' : GL (Fin 3) K} {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y * y' * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y') :
    ProjGenLinGroup.mk y' ∉ Subgroup.zpowers (ProjGenLinGroup.mk y) := by
  rintro ⟨k, hk⟩
  change ProjGenLinGroup.mk y ^ k = ProjGenLinGroup.mk y' at hk
  rw [← map_zpow] at hk
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hk
  rw [← hu] at hζ
  have hc : y * (y ^ k * GeneralLinearGroup.scalar (Fin 3) u) * y⁻¹ =
      y ^ k * GeneralLinearGroup.scalar (Fin 3) u := by
    rw [← scalar_mul_comm, conj_scalar_mul, show y * y ^ k * y⁻¹ = y ^ k by group]
  rw [hc] at hζ
  have h2 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
    calc GeneralLinearGroup.scalar (Fin 3) ζ =
        GeneralLinearGroup.scalar (Fin 3) ζ * (y ^ k * GeneralLinearGroup.scalar (Fin 3) u) *
          (y ^ k * GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by group
      _ = 1 := by rw [← hζ, mul_inv_cancel]
  apply hζ1
  have h3 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h2
  simp [GeneralLinearGroup.coe_scalar] at h3
  exact h3

end Quot

section Heis

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_type_one (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (ProjGenLinGroup (Fin 3) K)} (hEP : E ≤ projImage (glPi π 3 (p ^ f) K))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {y₁ y₂ : GL (Fin 3) K}
    (h₁ : ProjGenLinGroup.mk y₁ ∈ E) (h₂ : ProjGenLinGroup.mk y₂ ∈ E) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∃ l ∈ glPi π 3 (p ^ f) K, ProjGenLinGroup.mk l ∈ E ∧ ProjGenLinGroup.mk l ≠ 1 ∧
      Type123 π (p ^ f) K l 1 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  obtain ⟨hcomm, -, -⟩ := map_pglEquivQuot_facts hE
  have hy₁1 := mk_ne_one_of_heis hζ1 hζ
  have hy₂ := mk_not_mem_zpowers_of_heis hζ1 hζ
  obtain ⟨w₁, hw₁, hw₁e⟩ := hEP h₁
  obtain ⟨w₂, hw₂, hw₂e⟩ := hEP h₂
  set C := rootsOfUnity (qSubPi π (p ^ f)) K
  obtain ⟨l, hlH, hlE, hl1, μ, hμ, hdet⟩ : ∃ l ∈ glPi π 3 (p ^ f) K, ProjGenLinGroup.mk l ∈ E ∧
      ProjGenLinGroup.mk l ≠ 1 ∧ ∃ μ : Kˣ, μ ∈ C ∧
        (l : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3 := by
    by_cases hc : ∃ μ : C, μ ^ 3 = ⟨GeneralLinearGroup.det w₁, det_mem_rootsOfUnity hK hw₁⟩
    · obtain ⟨μ, hμ⟩ := hc
      refine ⟨w₁, hw₁, hw₁e ▸ h₁, hw₁e ▸ hy₁1, μ, μ.2, ?_⟩
      have h1 := congrArg (fun t : C => ((t : Kˣ) : K)) hμ
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val,
        GeneralLinearGroup.val_det_apply] at h1
      exact h1.symm
    · push Not at hc
      obtain ⟨k, μ, hkμ⟩ := exists_mul_pow_eq_cube
        (⟨GeneralLinearGroup.det w₂, det_mem_rootsOfUnity hK hw₂⟩ : C) hc
      refine ⟨w₂ * w₁ ^ k, mul_mem hw₂ (pow_mem hw₁ k), ?_, ?_, μ, μ.2, ?_⟩
      · rw [map_mul, map_pow, hw₁e, hw₂e]
        exact mul_mem h₂ (pow_mem h₁ k)
      · rw [map_mul, map_pow, hw₁e, hw₂e]
        intro h
        apply hy₂
        rw [mul_eq_one_iff_eq_inv] at h
        rw [h, ← zpow_natCast, ← _root_.zpow_neg]
        exact Subgroup.zpow_mem_zpowers _ _
      · have h1 := congrArg (fun t : C => ((t : Kˣ) : K)) hkμ
        simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
          GeneralLinearGroup.val_det_apply] at h1
        rw [Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Matrix.det_pow]
        exact h1
  have hlZ : l ∉ zPi π 3 (p ^ f) K := fun hz =>
    hl1 (mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz))
  have hl3 : l ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hlH 3, mk_eq_one_iff_mem_statedScalars.mp ?_⟩
    rw [map_pow]
    exact hE.2 _ hlE
  rcases type13_of_heisP hK hq hcomm (mem_map_pglEquivQuot.mpr h₁) (mem_map_pglEquivQuot.mpr h₂)
      hζ1 hζ hlH hlZ hl3 (mem_map_pglEquivQuot.mpr hlE) with h1 | h3
  · exact ⟨l, hlH, hlE, hl1, h1⟩
  · exfalso
    obtain ⟨l₀, hl₀, -, hl₀'⟩ := exists_inner_of_det_eq_cube hK hlH
      ((scalar_mem_glPi_iff hK μ).mpr hμ) hdet
    exact not_inner_of_type3 hK hq hlH h3 ⟨l₀, hl₀, fun m _ => hl₀' m⟩

theorem exists_partner (h3 : (3 : K) ≠ 0) {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {y₁ y₂ : GL (Fin 3) K}
    (h₁ : ProjGenLinGroup.mk y₁ ∈ E) (h₂ : ProjGenLinGroup.mk y₂ ∈ E) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) {l : GL (Fin 3) K}
    (hlE : ProjGenLinGroup.mk l ∈ E) (hl1 : ProjGenLinGroup.mk l ≠ 1) :
    ∃ y : GL (Fin 3) K, ProjGenLinGroup.mk y ∈ E ∧ ∃ ζ' : Kˣ, ζ' ≠ 1 ∧
      l * y * l⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ' * y := by
  have hc : ∀ {a b : ProjGenLinGroup (Fin 3) K}, a ∈ E → b ∈ E → a * b = b * a :=
    fun ha hb => congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  obtain ⟨c₁, hc₁⟩ := exists_scalar_of_mk_comm (hc hlE h₁)
  obtain ⟨c₂, hc₂⟩ := exists_scalar_of_mk_comm (hc hlE h₂)
  by_cases h1 : c₁ = 1
  · by_cases h2 : c₂ = 1
    · exfalso
      apply hl1
      apply mk_eq_one_iff_mem_statedScalars.mpr
      refine mem_statedScalars_of_commute_heis h3 hζ1 (pow_three_eq_one_of_conj_eq_scalar_mul hζ)
        hζ ?_ ?_
      · rw [h1, map_one, one_mul] at hc₁
        calc l * y₁ = l * y₁ * l⁻¹ * l := by group
          _ = y₁ * l := by rw [hc₁]
      · rw [h2, map_one, one_mul] at hc₂
        calc l * y₂ = l * y₂ * l⁻¹ * l := by group
          _ = y₂ * l := by rw [hc₂]
    · exact ⟨y₂, h₂, c₂, h2, hc₂⟩
  · exact ⟨y₁, h₁, c₁, h1, hc₁⟩

theorem exists_of_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hEP : E ≤ projImage (glPi π 3 (p ^ f) K)) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {y₁ y₂ : GL (Fin 3) K}
    (h₁ : ProjGenLinGroup.mk y₁ ∈ E) (h₂ : ProjGenLinGroup.mk y₂ ∈ E) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∃ s ∈ projImage (slPi π 3 (p ^ f) K), s ^ 3 = 1 ∧
      s ∈ Subgroup.normalizer (E : Set (ProjGenLinGroup (Fin 3) K)) ∧
      s ∉ Subgroup.centralizer (E : Set (ProjGenLinGroup (Fin 3) K)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨l, hlH, hlE, hl1, hl⟩ := exists_type_one hK hq hEP hE h₁ h₂ hζ1 hζ
  obtain ⟨y, hyE, ζ', hζ'1, hrel⟩ := exists_partner h3 hE h₁ h₂ hζ1 hζ hlE hl1
  obtain ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ := hl
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  obtain ⟨ν, rfl⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  set X := l * GeneralLinearGroup.scalar (Fin 3) ν with hX
  have hrelX : X * y * X⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ' * y := by
    calc X * y * X⁻¹ = l * (GeneralLinearGroup.scalar (Fin 3) ν * y *
          (GeneralLinearGroup.scalar (Fin 3) ν)⁻¹) * l⁻¹ := by rw [hX]; group
      _ = l * y * l⁻¹ := by rw [scalar_mul_comm ν y, mul_inv_cancel_right]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ' * y := hrel
  have hmkX : ProjGenLinGroup.mk X = ProjGenLinGroup.mk l := by
    rw [hX, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  have hζ'3 := pow_three_eq_one_of_conj_eq_scalar_mul hrel
  obtain ⟨hcommX, hcases⟩ := heis_conj hτ hτ1 hτ0 hζ'3 hζ'1 hD hrelX
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  set S : GL (Fin 3) K := diagUnits 1 τu 1 with hS
  set σ := g * S * g⁻¹ with hσ
  have hτu3 : τu ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ, Units.val_one])
  have hSH : S ∈ glPi π 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (one_mem _) (cube_root_mem_qSubPi hq hτu3) (one_mem _)
  have hσH : σ ∈ glPi π 3 (p ^ f) K := mul_mem (mul_mem hg hSH) (inv_mem hg)
  obtain ⟨μ, hμ, hμ3⟩ := exists_cube_root_tau hK hq h9 hτ
  have hdet : (σ : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3 := by
    rw [hσ, det_conj_eq, hS, hτu, coe_diagUnits_phase, det_diagonal, Fin.prod_univ_three, hμ3]
    simp
  obtain ⟨l₀, hl₀, ⟨z₀, hz₀⟩, -⟩ := exists_inner_of_det_eq_cube hK hσH
    ((scalar_mem_glPi_iff hK μ).mpr hμ) hdet
  have hmkσ : ProjGenLinGroup.mk σ = ProjGenLinGroup.mk l₀ := by
    rw [hz₀, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  have hl3 : ProjGenLinGroup.mk l ^ 3 = 1 := hE.2 _ hlE
  have hlo : orderOf (ProjGenLinGroup.mk l) = 3 := orderOf_eq_prime hl3 hl1
  have hyl : ProjGenLinGroup.mk y ∉ Subgroup.zpowers (ProjGenLinGroup.mk l) :=
    mk_not_mem_zpowers_of_heis hζ'1 hrel
  have hcly : ProjGenLinGroup.mk y * ProjGenLinGroup.mk l =
      ProjGenLinGroup.mk l * ProjGenLinGroup.mk y :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hyE⟩ ⟨_, hlE⟩)
  have hEeq : Subgroup.zpowers (ProjGenLinGroup.mk l) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y)
      = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hlE)
      (Subgroup.zpowers_le.mpr hyE)) ?_
    rw [hE9, card_zpowers_sup_zpowers (hE.2 _ hyE) hlo hyl hcly]
  have hσl : ProjGenLinGroup.mk σ * ProjGenLinGroup.mk l * (ProjGenLinGroup.mk σ)⁻¹ =
      ProjGenLinGroup.mk l := by
    rw [← hmkX, ← map_inv, ← map_mul, ← map_mul, hσ, hcommX, mul_inv_cancel_right]
  obtain ⟨k, hk1, hk2, hσy⟩ : ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧
      ProjGenLinGroup.mk σ * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk σ)⁻¹ =
        ProjGenLinGroup.mk l ^ k * ProjGenLinGroup.mk y := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rcases hcases with h | h
    · refine ⟨1, le_rfl, by norm_num, ?_⟩
      rw [h, map_mul, map_mul, ProjGenLinGroup.mk_scalar, one_mul, hmkX, pow_one]
    · refine ⟨2, by norm_num, le_rfl, ?_⟩
      rw [h, map_mul, map_pow, hmkX]
  refine ⟨ProjGenLinGroup.mk σ, hmkσ ▸ Subgroup.mem_map_of_mem _ hl₀, ?_, ?_, ?_⟩
  · rw [← map_pow, hσ, conj_pow, hS, diagUnits_pow_three_eq_one hτu3, mul_one, mul_inv_cancel,
      map_one]
  · refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have hle : E.map (MulAut.conj (ProjGenLinGroup.mk σ)).toMonoidHom ≤ E := by
      rw [← hEeq, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · change ProjGenLinGroup.mk σ * ProjGenLinGroup.mk l * (ProjGenLinGroup.mk σ)⁻¹ ∈ _
        rw [hσl]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · change ProjGenLinGroup.mk σ * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk σ)⁻¹ ∈ _
        rw [hσy]
        exact mul_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    exact hle ⟨e, he, rfl⟩
  · intro hcen
    have hc := Subgroup.mem_centralizer_iff.mp hcen (ProjGenLinGroup.mk y) hyE
    have h1 : ProjGenLinGroup.mk σ * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk σ)⁻¹ =
        ProjGenLinGroup.mk y := by
      rw [← hc, mul_inv_cancel_right]
    rw [hσy] at h1
    have hlk : ProjGenLinGroup.mk l ^ k = 1 := by
      calc ProjGenLinGroup.mk l ^ k = ProjGenLinGroup.mk l ^ k * ProjGenLinGroup.mk y *
          (ProjGenLinGroup.mk y)⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one hlk
    rw [hlo] at this
    have := Nat.le_of_dvd (by omega) this
    omega

end Heis

section Model

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_of_modNine (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hEP : E ≤ projImage (glPi π 3 (p ^ f) K)) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) :
    ∃ s ∈ projImage (slPi π 3 (p ^ f) K), s ^ 3 = 1 ∧
      s ∈ Subgroup.normalizer (E : Set (ProjGenLinGroup (Fin 3) K)) ∧
      s ∉ Subgroup.centralizer (E : Set (ProjGenLinGroup (Fin 3) K)) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨hc, he, hcard⟩ := map_pglEquivQuot_facts hE
  rcases frame_or_heis h3 hτ hτ1 _ hc he (by rw [hcard, hE9]; norm_num) with
    ⟨b, hb, hd, -⟩ | ⟨y₁, y₂, h₁, h₂, ζ, hζ1, hζ⟩
  · exact exists_of_frame hK hq hEP hE hE9 hb fun y hy => hd y (mem_map_pglEquivQuot.mpr hy)
  · exact exists_of_heis hK hq h9 hEP hE hE9 (mem_map_pglEquivQuot.mp h₁)
      (mem_map_pglEquivQuot.mp h₂) hζ1 hζ

theorem card_eq_card_ker_mul_card_range {G H : Type*} [Group G] [Group H] (φ : G →* H) :
    Nat.card G = Nat.card φ.ker * Nat.card φ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]

theorem prod_facts {P : Type*} [Group P] [Finite P] {E : Subgroup (Multiplicative (ZMod 3) × P)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (h9 : ∀ F : Subgroup P, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9) :
    Nat.card (E.map (MonoidHom.snd _ P)) = 9 ∧
      ∀ z : Multiplicative (ZMod 3), ∀ y ∈ E.map (MonoidHom.snd _ P), (z, y) ∈ E := by
  set φ : E →* P := (MonoidHom.snd _ P).comp E.subtype with hφ
  have hrange : φ.range = E.map (MonoidHom.snd _ P) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard := card_eq_card_ker_mul_card_range φ
  rw [hrange, hE27] at hcard
  have hEbar : Nat.card (E.map (MonoidHom.snd _ P)) ≤ 9 :=
    h9 _ (Sec13.isElemAbelian_map hE _)
  set ψ : φ.ker → Multiplicative (ZMod 3) := fun e => (e : E).1.1 with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have ha : ((a : E) : Multiplicative (ZMod 3) × P).2 = 1 := a.2
    have hb : ((b : E) : Multiplicative (ZMod 3) × P).2 = 1 := b.2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hab (ha.trans hb.symm)
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hker : Nat.card φ.ker ≤ 3 := (Nat.card_le_card_of_injective ψ hψinj).trans hZ3.le
  have hk3 : Nat.card φ.ker = 3 ∧ Nat.card (E.map (MonoidHom.snd _ P)) = 9 := by
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    have hpos' : 0 < Nat.card (E.map (MonoidHom.snd _ P)) := Nat.card_pos
    constructor <;> nlinarith
  have hψbij : Function.Bijective ψ := hψinj.bijective_of_nat_card_le (by rw [hZ3, hk3.1])
  have hz1 : ∀ z : Multiplicative (ZMod 3), (z, (1 : P)) ∈ E := by
    intro z
    obtain ⟨⟨⟨w, hwE⟩, hw2⟩, hwz⟩ := hψbij.2 z
    have hw2' : w.2 = 1 := hw2
    have hwz' : w.1 = z := hwz
    have hw : w = (z, 1) := Prod.ext hwz' hw2'
    rw [← hw]
    exact hwE
  refine ⟨hk3.2, fun z y hy => ?_⟩
  obtain ⟨e, heE, rfl⟩ := hy
  have hze : (z, (MonoidHom.snd _ P) e) = (z * e.1⁻¹, (1 : P)) * e := by
    refine Prod.ext ?_ ?_
    · exact (inv_mul_cancel_right z e.1).symm
    · simp
  rw [hze]
  exact mul_mem (hz1 _) heE

theorem one_mul_mul_one_inv {M : Type*} [Group M] (a : M) : 1 * a * 1⁻¹ = a := by simp

theorem exists_model_of {G : Type*} [Group G] [Finite G] {P M : Subgroup G} (hMP : M ≤ P)
    (hcommP : commutator P = M.subgroupOf P)
    (hle9 : ∀ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9)
    (hcase : (∀ x ∈ M, ∀ v : ℕ, x ^ 3 ^ v = 1 → x ^ 3 = 1) ∨
      (∀ F : Subgroup G, F ≤ P → CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 →
        ∃ s ∈ M, s ^ 3 = 1 ∧ s ∈ Subgroup.normalizer (F : Set G) ∧
          s ∉ Subgroup.centralizer (F : Set G)))
    {E : Subgroup (Multiplicative (ZMod 3) × P)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hx : ∃ x ∈ commutator (Multiplicative (ZMod 3) × P), (∃ v : ℕ, x ^ 3 ^ v = 1) ∧
      x ∈ Subgroup.normalizer (E : Set (Multiplicative (ZMod 3) × P)) ∧
      x ∉ Subgroup.centralizer (E : Set (Multiplicative (ZMod 3) × P))) :
    ∃ s ∈ commutator (Multiplicative (ZMod 3) × P), s ^ 3 = 1 ∧
      s ∈ Subgroup.normalizer (E : Set (Multiplicative (ZMod 3) × P)) ∧
      s ∉ Subgroup.centralizer (E : Set (Multiplicative (ZMod 3) × P)) := by
  classical
  have hcommY : commutator (Multiplicative (ZMod 3) × P) =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (commutator P) :=
    Sec13.commutator_zthree_prod P
  obtain ⟨x, hxC, ⟨v, hxv⟩, hxN, hxCE⟩ := hx
  rcases hcase with hpow | hexists
  ·
    refine ⟨x, hxC, ?_, hxN, hxCE⟩
    have hxC' := hxC
    rw [hcommY] at hxC'
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hxC'
    rw [hcommP] at hx2
    have hx1' : x.1 = 1 := Subgroup.mem_bot.mp hx1
    have hx2v : ((x.2 : P) : G) ^ 3 ^ v = 1 := by
      have := congrArg (fun t : Multiplicative (ZMod 3) × P => ((t.2 : P) : G)) hxv
      simpa using this
    have hx23 := hpow _ (Subgroup.mem_subgroupOf.mp hx2) v hx2v
    refine Prod.ext (by simp [hx1']) (Subtype.ext ?_)
    simpa using hx23
  · have hle9P : ∀ F : Subgroup P, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9 := by
      intro F hF
      rw [← Subgroup.card_map_of_injective P.subtype_injective]
      exact hle9 _ (Sec13.isElemAbelian_map hF _)
    obtain ⟨hcard9, hprod⟩ := prod_facts hE hE27 hle9P
    have hmemF : ∀ y : P, (y : G) ∈ (E.map (MonoidHom.snd _ P)).map P.subtype ↔
        y ∈ E.map (MonoidHom.snd _ P) := fun y =>
      Subgroup.mem_map_iff_mem P.subtype_injective
    obtain ⟨s₁, hs₁M, hs₁3, hs₁N, hs₁C⟩ := hexists ((E.map (MonoidHom.snd _ P)).map P.subtype)
      (Subgroup.map_subtype_le _) (Sec13.isElemAbelian_map (Sec13.isElemAbelian_map hE _) _)
      (by rw [Subgroup.card_map_of_injective P.subtype_injective, hcard9])
    set sb : P := ⟨s₁, hMP hs₁M⟩ with hsb
    refine ⟨(1, sb), ?_, ?_, ?_, ?_⟩
    · rw [hcommY]
      refine ⟨Subgroup.mem_bot.mpr rfl, ?_⟩
      rw [hcommP]
      exact Subgroup.mem_subgroupOf.mpr hs₁M
    · refine Prod.ext (by simp) (Subtype.ext ?_)
      simpa [hsb] using hs₁3
    · refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have he₂ : e.2 ∈ E.map (MonoidHom.snd _ P) := ⟨e, he, rfl⟩
      have h1 : (s₁ * (e.2 : G) * s₁⁻¹) ∈ (E.map (MonoidHom.snd _ P)).map P.subtype :=
        (Subgroup.mem_normalizer_iff.mp hs₁N _).mp ((hmemF e.2).mpr he₂)
      have h2 : sb * e.2 * sb⁻¹ ∈ E.map (MonoidHom.snd _ P) :=
        (hmemF _).mp (by simpa [hsb] using h1)
      have h4 : ((1 : Multiplicative (ZMod 3)), sb) * e * ((1 : Multiplicative (ZMod 3)), sb)⁻¹ =
          (e.1, sb * e.2 * sb⁻¹) := by
        refine Prod.ext ?_ rfl
        exact one_mul_mul_one_inv e.1
      change ((1 : Multiplicative (ZMod 3)), sb) * e * ((1 : Multiplicative (ZMod 3)), sb)⁻¹ ∈ E
      rw [h4]
      exact hprod e.1 _ h2
    · intro hcen
      apply hs₁C
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨y', hy', rfl⟩ := hy
      obtain ⟨e, he, rfl⟩ := hy'
      have hc := Subgroup.mem_centralizer_iff.mp hcen e he
      have hc2 := congrArg (fun t : Multiplicative (ZMod 3) × P => ((t.2 : P) : G)) hc
      simpa [hsb] using hc2

theorem exists_model (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {E : Subgroup (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hx : ∃ x ∈ commutator (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K)),
      (∃ v : ℕ, x ^ 3 ^ v = 1) ∧
      x ∈ Subgroup.normalizer (E : Set (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K)))
      ∧ x ∉ Subgroup.centralizer
        (E : Set (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K)))) :
    ∃ s ∈ commutator (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K)), s ^ 3 = 1 ∧
      s ∈ Subgroup.normalizer (E : Set (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K)))
      ∧ s ∉ Subgroup.centralizer
        (E : Set (Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) K))) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  refine exists_model_of (Subgroup.map_mono (slPi_le_glPi hπ))
    (Sec13.commutator_projImage_glPi hK hq2) (fun F hF => card_le_nine_pgl h3 hτ hτ1 hF) ?_
    hE hE27 hx
  by_cases h9 : p ^ f % 9 = 1 ∨ p ^ f % 9 = 8
  · right
    have h9' : 9 ∣ qSubPi π (p ^ f) := by
      have h1 : 1 ≤ p ^ f := by omega
      rw [← modNine_iff h1]
      cases π
      · change p ^ f % 3 = 2 at hq
        change p ^ f % 9 = 8
        omega
      · change p ^ f % 3 = 1 at hq
        change p ^ f % 9 = 1
        omega
    exact fun F hFP hF hF9 => exists_of_modNine hK hq h9' hFP hF hF9
  · left
    exact fun x hx v hxv => pow_three_eq_one_of_mem_projImage hK hq h9 hx hxv

end Model

section Transport

variable {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)

theorem mem_commutator_iff_map {x : X} : φ x ∈ commutator Y ↔ x ∈ commutator X := by
  have h1 : (commutator X).map φ.toMonoidHom = commutator Y := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ φ.surjective]
  rw [← h1]
  exact Subgroup.mem_map_iff_mem φ.injective

theorem mem_normalizer_iff_map {E : Subgroup X} {x : X} :
    φ x ∈ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup Y) : Set Y) ↔
      x ∈ Subgroup.normalizer (E : Set X) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.mem_map_iff_mem φ.injective

theorem mem_centralizer_iff_map {E : Subgroup X} {x : X} :
    φ x ∈ Subgroup.centralizer ((E.map φ.toMonoidHom : Subgroup Y) : Set Y) ↔
      x ∈ Subgroup.centralizer (E : Set X) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h e he
    have := h (φ e) ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact φ.injective this
  · rintro h _ ⟨e, he, rfl⟩
    change φ e * φ x = φ x * φ e
    rw [← map_mul, ← map_mul, h e he]

end Transport

end Proof1513Res2

open Proof1513Res2 in
theorem ks1513Z3PGLOrderThree : KS1513Z3PGLOrderThree := by
  intro X _ _ hX hns E hE hE27 _ hx
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hX
  have := hK.finite
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have h2 : p ^ f = 2 := by
      have hf : f ≠ 0 := by have := hK.one_le; omega
      have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
      omega
    cases π
    · apply hns
      have hs := Sec13.isSolvable_projImage_glPi_two hK h2
      have : Group.IsSolvable (Multiplicative (ZMod 3) ×
          CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi false 3 (p ^ f) K)) := inferInstance
      exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    · change p ^ f % 3 = 1 at hq
      omega
  have hE' := Sec13.isElemAbelian_map hE φ.toMonoidHom
  have hE'27 : Nat.card (E.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE27]
  obtain ⟨x, hxC, ⟨v, hxv⟩, hxN, hxCE⟩ := hx
  obtain ⟨s, hsC, hs3, hsN, hsCE⟩ := exists_model hK hq hq2 hE' hE'27
    ⟨φ x, (mem_commutator_iff_map φ).mpr hxC, ⟨v, by rw [← map_pow, hxv, map_one]⟩,
      (mem_normalizer_iff_map φ).mpr hxN, fun h => hxCE ((mem_centralizer_iff_map φ).mp h)⟩
  have hs : φ (φ.symm s) = s := φ.apply_symm_apply s
  refine ⟨φ.symm s, (mem_commutator_iff_map φ).mp (by rw [hs]; exact hsC), ?_,
    (mem_normalizer_iff_map φ).mp (by rw [hs]; exact hsN), fun h => hsCE ?_⟩
  · rw [← map_pow, hs3, map_one]
  · have := (mem_centralizer_iff_map φ).mpr h
    rwa [hs] at this


end CFSG.RankThree.PartTwo.Sec15
