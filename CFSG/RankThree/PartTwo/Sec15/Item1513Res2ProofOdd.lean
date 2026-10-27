module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Res2ProofPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Proof1513Res2

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Monomial

variable {K : Type} [Field K]

theorem entry_conj_aux {a Δi Δj dj di' l : K} (h : Δj ≠ l * Δi ∨ dj = di')
    (hrel : a * Δj = l * (Δi * a)) : a * dj = di' * a := by
  rcases h with h | h
  · have ha : a = 0 := by
      have h1 : a * (Δj - l * Δi) = 0 := by linear_combination hrel
      exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h)
    rw [ha]
    ring
  · rw [h]
    ring

theorem conj_diag_of_rel {Δ d d' : Fin 3 → K} {l : K} {Y : Matrix (Fin 3) (Fin 3) K}
    (hrel : Y * diagonal Δ = l • (diagonal Δ * Y))
    (hc : ∀ i j, Δ j ≠ l * Δ i ∨ d j = d' i) :
    Y * diagonal d = diagonal d' * Y := by
  ext i j
  have hij := congrFun (congrFun hrel i) j
  simp only [diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  exact entry_conj_aux (hc i j) hij

theorem cond_conj_of_mod {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (e a a' : Fin 3 → ℕ) (m : ℕ)
    (h : ∀ i j, e j % 3 ≠ (m + e i) % 3 ∨ a j % 2 = a' i % 2) :
    ∀ i j, τ ^ (e j) ≠ τ ^ m * τ ^ (e i) ∨ (-1 : K) ^ (a j) = (-1 : K) ^ (a' i) := by
  intro i j
  rcases h i j with h | h
  · left
    intro h'
    rw [← pow_add] at h'
    exact h ((pow_eq_pow_iff_mod hτ hτ1 _ _).mp h')
  · right
    rw [neg_one_pow_eq_pow_mod_two (a j), h, ← neg_one_pow_eq_pow_mod_two]

@[expose] noncomputable def signDiag (a : Fin 3 → ℕ) : GL (Fin 3) K :=
  diagUnits ((-1 : Kˣ) ^ (a 0)) ((-1 : Kˣ) ^ (a 1)) ((-1 : Kˣ) ^ (a 2))

theorem coe_signDiag (a : Fin 3 → ℕ) :
    ((signDiag a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => (-1 : K) ^ (a i)) := by
  rw [signDiag, coe_diagUnits]
  congr 1
  funext i
  fin_cases i <;> simp

theorem signDiag_sq (a : Fin 3 → ℕ) : (signDiag a : GL (Fin 3) K) ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_signDiag, diagonal_pow, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← pow_mul, pow_mul']

theorem signDiag_commute_diag (a : Fin 3 → ℕ) {Δ : Fin 3 → K} :
    ((signDiag a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal Δ =
      diagonal Δ * ((signDiag a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [coe_signDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem diagTau_vec_eq (τ : K) :
    (![τ, τ ^ 2, 1] : Fin 3 → K) = fun i => τ ^ ((![1, 2, 0] : Fin 3 → ℕ) i) := by
  funext i
  fin_cases i <;> simp

end Monomial

section Odd

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem two_dvd_qSubPi (hK : PiField π p f K) (hp2 : p ≠ 2) : 2 ∣ qSubPi π (p ^ f) := by
  have hodd : Odd (p ^ f) := (hK.prime.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨k, hk⟩ := hodd
  cases π
  · exact ⟨k + 1, by change p ^ f + 1 = _; omega⟩
  · exact ⟨k, by change p ^ f - 1 = _; omega⟩

theorem neg_one_mem_rootsOfUnity (hK : PiField π p f K) (hp2 : p ≠ 2) (k : ℕ) :
    (-1 : Kˣ) ^ k ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  obtain ⟨m, hm⟩ := two_dvd_qSubPi hK hp2
  rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, hm, pow_mul, neg_one_sq, one_pow, one_pow]

theorem signDiag_mem_slPi (hK : PiField π p f K) (hp2 : p ≠ 2) {a : Fin 3 → ℕ}
    (ha : (a 0 + a 1 + a 2) % 2 = 0) : (signDiag a : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  refine (mem_slPi_iff hπ).mpr ⟨diagUnits_mem_glPi hK (neg_one_mem_rootsOfUnity hK hp2 _)
    (neg_one_mem_rootsOfUnity hK hp2 _) (neg_one_mem_rootsOfUnity hK hp2 _), ?_⟩
  rw [coe_signDiag, det_diagonal, Fin.prod_univ_three, ← pow_add, ← pow_add,
    neg_one_pow_eq_pow_mod_two, ha, pow_zero]

theorem conj_mem_slPi (hK : PiField π p f K) {g D : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hD : D ∈ slPi π 3 (p ^ f) K) : g * D * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hD' := (mem_slPi_iff hπ).mp hD
  refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hg hD'.1) (inv_mem hg), ?_⟩
  rw [det_conj_eq]
  exact hD'.2

theorem mk_conj_signDiag_ne_one (h2 : (2 : K) ≠ 0) (g : GL (Fin 3) K) {a : Fin 3 → ℕ} {i j : Fin 3}
    (hij : a i % 2 ≠ a j % 2) : ProjGenLinGroup.mk (g * signDiag a * g⁻¹) ≠ 1 := by
  intro h
  rw [mk_eq_one_iff_mem_statedScalars] at h
  have h' : signDiag a ∈ StatedScalars (Fin 3) K := by
    have h1 := (inv_conj_mem_statedScalars_iff g (g * signDiag a * g⁻¹)).mpr h
    have : g⁻¹ * (g * signDiag a * g⁻¹) * g = signDiag a := by group
    rwa [this] at h1
  obtain ⟨u, hu⟩ := h'
  have ei := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i i) hu
  have ej := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) j j) hu
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
    coe_signDiag] at ei ej
  have hne : (-1 : K) ≠ 1 := by
    intro h1
    apply h2
    linear_combination -h1
  rcases Nat.mod_two_eq_zero_or_one (a i) with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one (a j) with hj | hj
  · exact hij (hi.trans hj.symm)
  · rw [neg_one_pow_eq_pow_mod_two, hi, pow_zero] at ei
    rw [neg_one_pow_eq_pow_mod_two, hj, pow_one] at ej
    exact hne (ej.symm.trans ei)
  · rw [neg_one_pow_eq_pow_mod_two, hi, pow_one] at ei
    rw [neg_one_pow_eq_pow_mod_two, hj, pow_zero] at ej
    exact hne (ei.symm.trans ej)
  · exact hij (hi.trans hj.symm)

theorem mk_conj_signDiag_sq (g : GL (Fin 3) K) (a : Fin 3 → ℕ) :
    ProjGenLinGroup.mk (g * signDiag a * g⁻¹) ^ 2 = 1 := by
  rw [← map_pow, conj_pow, signDiag_sq, mul_one, mul_inv_cancel, map_one]

theorem isPGroup_zpowers_of_sq {M : Type*} [Group M] {x : M} (hx : x ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, zpow_natCast, hx, _root_.one_zpow, Subgroup.coe_one]

theorem mk_conj_comm {g D Δ : GL (Fin 3) K}
    (hc : (D : Matrix (Fin 3) (Fin 3) K) * Δ = Δ * D) :
    ProjGenLinGroup.mk (g * D * g⁻¹) * ProjGenLinGroup.mk (g * Δ * g⁻¹) =
      ProjGenLinGroup.mk (g * Δ * g⁻¹) * ProjGenLinGroup.mk (g * D * g⁻¹) := by
  have h : D * Δ = Δ * D := Units.ext (by rw [Units.val_mul, Units.val_mul, hc])
  rw [← map_mul, ← map_mul]
  congr 1
  calc g * D * g⁻¹ * (g * Δ * g⁻¹) = g * (D * Δ) * g⁻¹ := by group
    _ = g * (Δ * D) * g⁻¹ := by rw [h]
    _ = g * Δ * g⁻¹ * (g * D * g⁻¹) := by group

theorem conj_signDiag_eq {g X s D : GL (Fin 3) K} {l : Kˣ} (hD : g⁻¹ * X * g = D)
    (hs : s * X * s⁻¹ = GeneralLinearGroup.scalar (Fin 3) l * X) {Δ : Fin 3 → K}
    (hΔ : (D : Matrix (Fin 3) (Fin 3) K) = diagonal Δ) {a a' : Fin 3 → ℕ}
    (hc : ∀ i j, Δ j ≠ (l : K) * Δ i ∨ (-1 : K) ^ (a j) = (-1 : K) ^ (a' i)) :
    s * (g * signDiag a * g⁻¹) * s⁻¹ = g * signDiag a' * g⁻¹ := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = g⁻¹ * s * g := ⟨_, rfl⟩
  have hYrel : Y * D * Y⁻¹ = GeneralLinearGroup.scalar (Fin 3) l * D := by
    rw [hY, ← hD]
    calc g⁻¹ * s * g * (g⁻¹ * X * g) * (g⁻¹ * s * g)⁻¹ = g⁻¹ * (s * X * s⁻¹) * g⁻¹⁻¹ := by
          group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) l * X) * g⁻¹⁻¹ := by rw [hs]
      _ = GeneralLinearGroup.scalar (Fin 3) l * (g⁻¹ * X * g) := by
          rw [conj_scalar_mul, inv_inv]
  have hmat : (Y : Matrix (Fin 3) (Fin 3) K) * diagonal Δ =
      (l : K) • (diagonal Δ * (Y : Matrix (Fin 3) (Fin 3) K)) := by
    have h1 : Y * D = GeneralLinearGroup.scalar (Fin 3) l * D * Y := by
      rw [← hYrel]
      group
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul] at h2
    rw [← hΔ]
    exact h2
  have hm := conj_diag_of_rel hmat hc
  have hG : Y * signDiag a = signDiag a' * Y := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_signDiag, coe_signDiag]
    exact hm
  have hG' : Y * signDiag a * Y⁻¹ = signDiag a' := by
    rw [hG]
    group
  calc s * (g * signDiag a * g⁻¹) * s⁻¹ = g * (Y * signDiag a * Y⁻¹) * g⁻¹ := by
        rw [hY]
        group
    _ = g * signDiag a' * g⁻¹ := by rw [hG']

theorem signDiag_mul :
    (signDiag ![1, 1, 0] : GL (Fin 3) K) * signDiag ![1, 0, 1] = signDiag ![0, 1, 1] := by
  apply Units.ext
  rw [Units.val_mul, coe_signDiag, coe_signDiag, coe_signDiag, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem exists_two_normal_of_type1 (hK : PiField π p f K) (hp2 : p ≠ 2) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g X : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hD : g⁻¹ * X * g = diagTau hτ) :
    ∃ V : Subgroup (ProjGenLinGroup (Fin 3) K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      V ≤ projImage (slPi π 3 (p ^ f) K) ∧
      V ≤ Subgroup.centralizer {ProjGenLinGroup.mk X} ∧
      Subgroup.centralizer {ProjGenLinGroup.mk X} ≤ Subgroup.normalizer (V : Set _) := by
  classical
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have := hK.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp this)
  set t₁ := ProjGenLinGroup.mk (g * signDiag ![1, 1, 0] * g⁻¹) with ht₁
  set t₂ := ProjGenLinGroup.mk (g * signDiag ![1, 0, 1] * g⁻¹) with ht₂
  set t₃ := ProjGenLinGroup.mk (g * signDiag ![0, 1, 1] * g⁻¹) with ht₃
  have ht₃eq : t₃ = t₁ * t₂ := by
    rw [ht₁, ht₂, ht₃, ← map_mul, ← signDiag_mul]
    congr 1
    group
  have hX : X = g * diagTau hτ * g⁻¹ := by
    rw [← hD]
    group
  have hcomm₁ : t₁ * t₂ = t₂ * t₁ := mk_conj_comm (by
    rw [coe_signDiag, coe_signDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring)
  set V := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hV
  have hV2 : IsPGroup 2 V := IsPGroup.to_sup_of_normal_right'
    (isPGroup_zpowers_of_sq (mk_conj_signDiag_sq g _))
    (isPGroup_zpowers_of_sq (mk_conj_signDiag_sq g _))
    (by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff.mp hy]
      exact hcomm₁.symm)
  have hXc : ∀ a : Fin 3 → ℕ, ProjGenLinGroup.mk (g * signDiag a * g⁻¹) ∈
      Subgroup.centralizer {ProjGenLinGroup.mk X} := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff, hX]
    have hcD : ((signDiag a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (signDiag a : GL (Fin 3) K) := by
      rw [coe_diagTau_eq_diagonal]
      exact signDiag_commute_diag a
    exact mk_conj_comm (g := g) hcD
  refine ⟨V, ?_, hV2, ?_, ?_, ?_⟩
  · intro hbot
    apply mk_conj_signDiag_ne_one h2 g (a := ![1, 1, 0]) (i := 0) (j := 2) (by decide)
    have : t₁ ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · have hs₁ : (signDiag ![1, 1, 0] : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
      signDiag_mem_slPi hK hp2 (by decide)
    have hs₂ : (signDiag ![1, 0, 1] : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
      signDiag_mem_slPi hK hp2 (by decide)
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_map_of_mem _ (conj_mem_slPi hK hg hs₁)
    · exact Subgroup.mem_map_of_mem _ (conj_mem_slPi hK hg hs₂)
  · exact sup_le (Subgroup.zpowers_le.mpr (hXc _)) (Subgroup.zpowers_le.mpr (hXc _))
  · intro n hn
    obtain ⟨s, rfl⟩ := ProjGenLinGroup.mk_surjective n
    obtain ⟨l, hl⟩ := exists_scalar_of_mk_comm (Subgroup.mem_centralizer_singleton_iff.mp hn)
    have hl3 := pow_three_eq_one_of_conj_eq_scalar_mul hl
    have hΔ := coe_diagTau_eq_diagonal hτ
    rw [diagTau_vec_eq] at hΔ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (l : K) = τ ^ m ∧ m < 3 := by
      by_cases hl1 : l = 1
      · exact ⟨0, by rw [hl1, Units.val_one, pow_zero], by norm_num⟩
      · have hl3K : (l : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hl3, Units.val_one]
        rcases eq_tau_or_sq hτ hτ1 hl3K (fun h => hl1 (Units.ext h)) with h | h
        · exact ⟨1, by rw [h, pow_one], by norm_num⟩
        · exact ⟨2, h, by norm_num⟩
    have hmem : ∀ a : Fin 3 → ℕ, (∃ a' : Fin 3 → ℕ, (∀ i j, (![1, 2, 0] : Fin 3 → ℕ) j % 3 ≠
        (m + (![1, 2, 0] : Fin 3 → ℕ) i) % 3 ∨ a j % 2 = a' i % 2) ∧
        ProjGenLinGroup.mk (g * signDiag a' * g⁻¹) ∈ V) →
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk (g * signDiag a * g⁻¹) *
          (ProjGenLinGroup.mk s)⁻¹ ∈ V := by
      rintro a ⟨a', ha', hV'⟩
      have hcond : ∀ i j, (fun i => τ ^ ((![1, 2, 0] : Fin 3 → ℕ) i)) j ≠
          (l : K) * (fun i => τ ^ ((![1, 2, 0] : Fin 3 → ℕ) i)) i ∨
          (-1 : K) ^ (a j) = (-1 : K) ^ (a' i) := by
        rw [hm.1]
        exact cond_conj_of_mod hτ hτ1 _ _ _ m ha'
      have hconj := conj_signDiag_eq (D := diagTau hτ)
        (Δ := fun i => τ ^ ((![1, 2, 0] : Fin 3 → ℕ) i)) (a := a) (a' := a') hD hl hΔ hcond
      rw [← map_inv, ← map_mul, ← map_mul, hconj]
      exact hV'
    have ht₁V : t₁ ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have ht₂V : t₂ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have ht₃V : t₃ ∈ V := ht₃eq ▸ mul_mem ht₁V ht₂V
    have hc₁ : ProjGenLinGroup.mk s * t₁ * (ProjGenLinGroup.mk s)⁻¹ ∈ V := by
      apply hmem
      obtain ⟨hm1, hm2⟩ := hm
      interval_cases m
      · exact ⟨![1, 1, 0], by decide, ht₁V⟩
      · exact ⟨![1, 0, 1], by decide, ht₂V⟩
      · exact ⟨![0, 1, 1], by decide, ht₃V⟩
    have hc₂ : ProjGenLinGroup.mk s * t₂ * (ProjGenLinGroup.mk s)⁻¹ ∈ V := by
      apply hmem
      obtain ⟨hm1, hm2⟩ := hm
      interval_cases m
      · exact ⟨![1, 0, 1], by decide, ht₂V⟩
      · exact ⟨![0, 1, 1], by decide, ht₃V⟩
      · exact ⟨![1, 1, 0], by decide, ht₁V⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : V.map (MulAut.conj (ProjGenLinGroup.mk s)).toMonoidHom ≤ V := by
      rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      exact sup_le (Subgroup.zpowers_le.mpr hc₁) (Subgroup.zpowers_le.mpr hc₂)
    exact hle ⟨x, hx, rfl⟩

theorem exists_two_normal_of_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hp2 : p ≠ 2) {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1) {g X : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hD : g⁻¹ * X * g = diagE e) :
    ∃ V : Subgroup (ProjGenLinGroup (Fin 3) K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      V ≤ projImage (slPi π 3 (p ^ f) K) ∧
      V ≤ Subgroup.centralizer {ProjGenLinGroup.mk X} ∧
      Subgroup.centralizer {ProjGenLinGroup.mk X} ≤ Subgroup.normalizer (V : Set _) := by
  classical
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have := hK.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp this)
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  set t := ProjGenLinGroup.mk (g * signDiag ![0, 1, 1] * g⁻¹) with ht
  have hX : X = g * diagE e * g⁻¹ := by
    rw [← hD]
    group
  have hΔ : ((diagE e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(e : K), 1, 1] :=
    coe_diagE e
  refine ⟨Subgroup.zpowers t, ?_, isPGroup_zpowers_of_sq (mk_conj_signDiag_sq g _), ?_, ?_, ?_⟩
  · intro hbot
    apply mk_conj_signDiag_ne_one h2 g (a := ![0, 1, 1]) (i := 0) (j := 1) (by decide)
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · have hs : (signDiag ![0, 1, 1] : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
      signDiag_mem_slPi hK hp2 (by decide)
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ (conj_mem_slPi hK hg hs))
  · refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff, hX]
    have hcD : ((signDiag ![0, 1, 1] : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((diagE e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((diagE e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (signDiag ![0, 1, 1] : GL (Fin 3) K) := by
      rw [hΔ]
      exact signDiag_commute_diag _
    exact mk_conj_comm (g := g) hcD
  · intro n hn
    obtain ⟨s, rfl⟩ := ProjGenLinGroup.mk_surjective n
    obtain ⟨l, hl⟩ := exists_scalar_of_mk_comm (Subgroup.mem_centralizer_singleton_iff.mp hn)
    have hl1 : l = 1 := by
      by_contra hl1
      have htr := trace_eq_zero_of_conj_eq_scalar_mul hl1 hl
      have htr' : (X : Matrix (Fin 3) (Fin 3) K).trace = (e : K) + 2 := by
        rw [← trace_inv_conj g X, hD, trace_diagE]
      rw [htr'] at htr
      have he : (e : K) = -2 := by linear_combination htr
      rw [he] at he3
      apply h3
      have h9 : (3 : K) * 3 = 0 := by linear_combination -he3
      exact (mul_self_eq_zero).mp h9
    rw [hl1] at hl
    have hcond : ∀ i j, (![(e : K), 1, 1] : Fin 3 → K) j ≠
        ((1 : Kˣ) : K) * (![(e : K), 1, 1] : Fin 3 → K) i ∨
        (-1 : K) ^ ((![0, 1, 1] : Fin 3 → ℕ) j) = (-1 : K) ^ ((![0, 1, 1] : Fin 3 → ℕ) i) := by
      have he1' : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
      intro i j
      fin_cases i <;> fin_cases j <;> simp [he1', Ne.symm he1']
    have hconj := conj_signDiag_eq (D := diagE e) (Δ := ![(e : K), 1, 1]) (a := ![0, 1, 1])
      (a' := ![0, 1, 1]) hD hl hΔ hcond
    have hst : ProjGenLinGroup.mk s * t * (ProjGenLinGroup.mk s)⁻¹ = t := by
      rw [ht, ← map_inv, ← map_mul, ← map_mul, hconj]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hst]
    exact Subgroup.zpow_mem_zpowers t k

theorem exists_two_normal (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hp2 : p ≠ 2)
    {z : ProjGenLinGroup (Fin 3) K} (hzM : z ∈ projImage (slPi π 3 (p ^ f) K)) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) :
    ∃ V : Subgroup (ProjGenLinGroup (Fin 3) K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      V ≤ projImage (slPi π 3 (p ^ f) K) ∧ V ≤ Subgroup.centralizer {z} ∧
      Subgroup.centralizer {z} ≤ Subgroup.normalizer (V : Set _) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y, hyS, rfl⟩ := hzM
  have hyH : y ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hyS
  have hyZ : y ∉ zPi π 3 (p ^ f) K := fun hz =>
    hz1 (mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz))
  have hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hyH 3, mk_eq_one_iff_mem_statedScalars.mp ?_⟩
    rw [map_pow]
    exact hz3
  have hmk : ∀ ζ ∈ zPi π 3 (p ^ f) K, ProjGenLinGroup.mk (y * ζ) = ProjGenLinGroup.mk y := by
    intro ζ hζ
    rw [map_mul, mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hζ),
      mul_one]
  rcases type123_exhaust hK hq hyH hyZ hy3 with h1 | h2 | h3
  · obtain ⟨τ', hτ', hτ'1, ζ, hζ, g, hg, hD⟩ := h1
    have h := exists_two_normal_of_type1 hK hp2 hτ' hτ'1 hg hD
    rwa [hmk ζ hζ] at h
  · obtain ⟨e, he3, he1, ζ, hζ, g, hg, hD⟩ := h2
    have h := exists_two_normal_of_type2 hK hq hp2 he3 he1 hg hD
    rwa [hmk ζ hζ] at h
  · exact (not_inner_of_type3 hK hq hyH h3 ⟨y, hyS, fun m _ => rfl⟩).elim

end Odd

section Abstract

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem pCoreOf_two_centralizer_ne_bot (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hp2 : p ≠ 2) {X : Type*} [Group X] [Finite X]
    (ψ : X ≃* projImage (slPi π 3 (p ^ f) K)) {z : X} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set X)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := projImage (slPi π 3 (p ^ f) K) with hM
  have hz1' : ((ψ z : M) : ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    apply hz1
    apply ψ.injective
    rw [map_one]
    exact Subtype.ext h
  have hz3' : ((ψ z : M) : ProjGenLinGroup (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hz3, map_one, Subgroup.coe_one]
  obtain ⟨V, hV1, hV2, hVM, hVC, hVN⟩ := exists_two_normal hK hq hp2 (ψ z).2 hz1' hz3'
  set VX : Subgroup X := (V.subgroupOf M).map ψ.symm.toMonoidHom with hVX
  have hmemVX : ∀ x : X, x ∈ VX ↔ ((ψ x : M) : ProjGenLinGroup (Fin 3) K) ∈ V := by
    intro x
    rw [hVX, Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf]
  have hVXC : VX ≤ Subgroup.centralizer ({z} : Set X) := by
    intro x hx
    have h1 := hVC ((hmemVX x).mp hx)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    apply ψ.injective
    apply Subtype.ext
    simpa using h1
  have hVXN : Subgroup.centralizer ({z} : Set X) ≤ Subgroup.normalizer (VX : Set X) := by
    intro n hn
    have hn' : ((ψ n : M) : ProjGenLinGroup (Fin 3) K) ∈ Subgroup.centralizer
        {((ψ z : M) : ProjGenLinGroup (Fin 3) K)} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hn ⊢
      have := congrArg (fun t : X => ((ψ t : M) : ProjGenLinGroup (Fin 3) K)) hn
      simpa using this
    have hN := hVN hn'
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro x
    rw [hmemVX, hmemVX]
    simpa using hN ((ψ x : M) : ProjGenLinGroup (Fin 3) K)
  have hVX2 : IsPGroup 2 VX := by
    refine IsPGroup.map ?_ _
    exact hV2.comap_subtype
  have hVX1 : VX ≠ ⊥ := by
    intro hbot
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have hvM : v ∈ M := hVM hv
    have : ψ.symm ⟨v, hvM⟩ ∈ VX := (hmemVX _).mpr (by simpa using hv)
    rw [hbot, Subgroup.mem_bot] at this
    have h1 : (⟨v, hvM⟩ : M) = 1 := by
      have := congrArg ψ this
      simpa using this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  intro hbot
  apply hVX1
  rw [eq_bot_iff, ← hbot]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVXC hVXN hVX2

end Abstract

end Proof1513Res2

end CFSG.RankThree.PartTwo.Sec15
