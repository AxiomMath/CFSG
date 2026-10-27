module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Type2
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage projSU projSL)
open Matrix (ProjGenLinGroup)
open Matrix CFSG.LocalAnalysis.ComponentInitial

@[expose] def ElemWitness (X : Type*) [Group X] : Prop :=
  ∃ j d : X, j ^ 3 = 1 ∧ j ≠ 1 ∧ d ^ 3 = 1 ∧ j * d = d * j ∧ d ∉ Subgroup.zpowers j ∧
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ j ∈ Subgroup.normalizer (V : Set X)

theorem ElemWitness.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    (h : ElemWitness Y) : ElemWitness X := by
  obtain ⟨j, d, hj3, hj1, hd3, hjd, hdj, V, hV, hV2, hjV⟩ := h
  refine ⟨ψ.symm j, ψ.symm d, by rw [← map_pow, hj3, map_one], fun h => hj1 ?_,
    by rw [← map_pow, hd3, map_one], by rw [← map_mul, ← map_mul, hjd], fun hmem => hdj ?_,
    V.map ψ.symm.toMonoidHom, fun hbot => hV ?_, hV2.map _, ?_⟩
  · have := congrArg ψ h
    simpa using this
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg ψ hk
    simpa using this
  · rw [eq_bot_iff]
    intro v hv
    have : ψ.symm v ∈ V.map ψ.symm.toMonoidHom := Subgroup.mem_map_of_mem _ hv
    rw [hbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg ψ this
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_normalizer_iff.mp hjV (ψ x))

theorem mem_normalizer_of_conj_mem_of_pow_three {X : Type*} [Group X] {V : Subgroup X} {j : X}
    (hj3 : j ^ 3 = 1) (h : ∀ v ∈ V, j * v * j⁻¹ ∈ V) :
    j ∈ Subgroup.normalizer (V : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h v, fun hv => ?_⟩
  have h2 := h _ (h _ hv)
  have heq : j * (j * (j * v * j⁻¹) * j⁻¹) * j⁻¹ = v := by
    calc j * (j * (j * v * j⁻¹) * j⁻¹) * j⁻¹ = j ^ 3 * v * (j ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = v := by rw [hj3, one_mul, inv_one, mul_one]
  rw [← heq]
  exact h2

section Model

variable {K : Type} [Field K]

theorem elemWitness_projImage_of {H : Subgroup (GL (Fin 3) K)} {J D : GL (Fin 3) K}
    (hJ : J ∈ H) (hD : D ∈ H) (hJ3 : ProjGenLinGroup.mk (J ^ 3) = 1)
    (hJ1 : ProjGenLinGroup.mk J ≠ 1) (hD3 : ProjGenLinGroup.mk (D ^ 3) = 1)
    (hJD : ProjGenLinGroup.mk (J * D) = ProjGenLinGroup.mk (D * J))
    (hDJ : ∀ m : ℕ, m < 3 → ProjGenLinGroup.mk (J ^ m) ≠ ProjGenLinGroup.mk D)
    {V : Subgroup (projImage H)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hJV : ∀ v ∈ V, projOf H ⟨J, hJ⟩ * v * (projOf H ⟨J, hJ⟩)⁻¹ ∈ V) :
    ElemWitness (projImage H) := by
  set j := projOf H ⟨J, hJ⟩ with hjdef
  set d := projOf H ⟨D, hD⟩ with hddef
  have hjc : (j : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk J := coe_projOf H _
  have hdc : (d : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk D := coe_projOf H _
  have hjpow : ∀ m : ℕ, ((j ^ m : projImage H) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (J ^ m) := fun m => by rw [Subgroup.coe_pow, hjc, map_pow]
  have hj3 : j ^ 3 = 1 := Subtype.ext (by rw [hjpow, hJ3]; rfl)
  refine ⟨j, d, hj3, fun h => hJ1 ?_, Subtype.ext ?_, Subtype.ext ?_, fun hmem => ?_, V, hV,
    hV2, mem_normalizer_of_conj_mem_of_pow_three hj3 hJV⟩
  · rw [← hjc, h]
    rfl
  · rw [Subgroup.coe_pow, hdc, ← map_pow, hD3]
    rfl
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, hjc, hdc, ← map_mul, ← map_mul, hJD]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hk' : j ^ k = j ^ ((k % 3).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
      exact zpow_eq_zpow_emod' k hj3
    have hlt : (k % 3).toNat < 3 := by omega
    apply hDJ _ hlt
    rw [← hjpow, ← hdc, ← hk, hk']

end Model

section Mats

variable {K : Type} [Field K]

theorem exists_scalar_of_mk_eq_one {A : GL (Fin 3) K} (h : ProjGenLinGroup.mk A = 1) :
    ∃ u : Kˣ, ∀ i k : Fin 3, (A : Matrix (Fin 3) (Fin 3) K) i k = if i = k then (u : K) else 0 := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, rfl⟩ := h
  refine ⟨u, fun i k => ?_⟩
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem mk_ne_one_of_diag_ne {A : GL (Fin 3) K} {i k : Fin 3}
    (h : (A : Matrix (Fin 3) (Fin 3) K) i i ≠ (A : Matrix (Fin 3) (Fin 3) K) k k) :
    ProjGenLinGroup.mk A ≠ 1 := by
  intro h1
  obtain ⟨u, hu⟩ := exists_scalar_of_mk_eq_one h1
  apply h
  rw [hu, hu, if_pos rfl, if_pos rfl]

theorem mk_ne_one_of_offdiag_ne {A : GL (Fin 3) K} {i k : Fin 3} (hik : i ≠ k)
    (h : (A : Matrix (Fin 3) (Fin 3) K) i k ≠ 0) : ProjGenLinGroup.mk A ≠ 1 := by
  intro h1
  obtain ⟨u, hu⟩ := exists_scalar_of_mk_eq_one h1
  apply h
  rw [hu, if_neg hik]

theorem exists_scalar_of_mk_eq_mk {A B : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk A = ProjGenLinGroup.mk B) :
    ∃ u : Kˣ, ∀ i k : Fin 3,
      (A : Matrix (Fin 3) (Fin 3) K) i k * u = (B : Matrix (Fin 3) (Fin 3) K) i k := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  refine ⟨u, fun i k => ?_⟩
  rw [← hu, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal]

end Mats

section Cases

variable {K : Type} [Field K]

theorem diagTau_pow_entry {τ : K} (hτ : τ ^ 3 = 1) {m : ℕ} (hm : m < 3) :
    ((diagTau hτ ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = τ ^ m := by
  interval_cases m <;>
    simp [Units.val_pow_eq_pow_val, coe_diagTau, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem mk_diagTau_pow_ne_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) {m : ℕ} (hm : m < 3) :
    ProjGenLinGroup.mk (diagTau hτ ^ m) ≠ ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by
  intro h
  obtain ⟨u, hu⟩ := exists_scalar_of_mk_eq_mk h
  have h00 := hu 0 0
  rw [diagTau_pow_entry hτ hm] at h00
  have hc00 : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 0 := by
    simp [coe_cycThree]
  rw [hc00] at h00
  exact mul_ne_zero (pow_ne_zero _ hτ0) u.ne_zero h00

theorem mk_diagTau_mul_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    ProjGenLinGroup.mk (diagTau hτ * cycThree) =
      ProjGenLinGroup.mk ((cycThree : GL (Fin 3) K) * diagTau hτ) := by
  have h1 : ProjGenLinGroup.mk ((cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹) =
      ProjGenLinGroup.mk (diagTau hτ) := by
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨(Units.mk0 τ hτ0)⁻¹ ^ 2, ?_⟩
    apply Units.ext
    rw [Units.val_mul, cycThree_conj_diagTau hτ, GeneralLinearGroup.coe_scalar, coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply] <;>
      field_simp
  rw [map_mul, map_mul, map_inv] at h1
  rw [map_mul, map_mul]
  calc ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
      = (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ) *
          (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹) *
            ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by rw [h1]
    _ = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ) := by
        group

end Cases

theorem zpowers_involution_witness {X : Type*} [Group X] {j t : X} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hjt : j * t = t * j) :
    Subgroup.zpowers t ≠ ⊥ ∧ IsPGroup 2 (Subgroup.zpowers t) ∧
      ∀ v ∈ Subgroup.zpowers t, j * v * j⁻¹ ∈ Subgroup.zpowers t := by
  refine ⟨fun h => ht1 ?_, fun v => ⟨1, ?_⟩, fun v hv => ?_⟩
  · have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [h, Subgroup.mem_bot] at this
    exact this
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp v.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hk, OneMemClass.coe_one, pow_one, ← zpow_natCast,
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ht2, _root_.one_zpow]
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hjt' : j * t * j⁻¹ = t := by rw [hjt, mul_inv_cancel_right]
    rw [← conj_zpow, hjt']
    exact Subgroup.zpow_mem_zpowers t k

section Odd

variable {K : Type} [Field K] {p f : ℕ}

@[expose] noncomputable def negDiag : GL (Fin 3) K := diagUnits (-1) (-1) 1

theorem coe_negDiag :
    ((negDiag : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
  rw [negDiag, coe_diagUnits]
  simp

theorem negDiag_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K) :
    (negDiag : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((negDiag : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_negDiag, det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_negDiag]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, transpose_apply, diagonal_apply]
  · rw [mem_slPi_true]
    exact hdet

theorem negDiag_sq : (negDiag : GL (Fin 3) K) ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_negDiag, Units.val_one, sq, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagTau_mul_negDiag {τ : K} (hτ : τ ^ 3 = 1) :
    diagTau hτ * (negDiag : GL (Fin 3) K) = negDiag * diagTau hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_negDiag, coe_diagTau]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, diagonal_apply]

theorem elemWitness_odd {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hp2 : p ≠ 2) : ElemWitness (projImage (slPi π 3 (p ^ f) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hm1 : (-1 : K) ≠ 1 := by
    have := hK.charP
    intro h
    have h2 : ((2 : ℕ) : K) = 0 := by
      have : (2 : K) = 1 - (-1) := by ring
      rw [Nat.cast_ofNat, this, h, sub_self]
    have hp : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp hp)
  set H := slPi π 3 (p ^ f) K with hH
  have hJ := diagTau_mem_slPi hπ hq' hτ
  have hD := cycThree_mem_slPi (p := p) (f := f) (K := K) hπ
  have hT := negDiag_mem_slPi (p := p) (f := f) (K := K) hπ
  set t := projOf H ⟨negDiag, hT⟩ with htdef
  have ht2 : t ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨negDiag, hT⟩ : H) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact negDiag_sq)
    rw [this, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h' : ProjGenLinGroup.mk (negDiag : GL (Fin 3) K) = 1 := by
      have := congrArg (fun x : projImage H => (x : ProjGenLinGroup (Fin 3) K)) h
      simpa [htdef, coe_projOf] using this
    refine mk_ne_one_of_diag_ne (i := 0) (k := 2) ?_ h'
    simpa [coe_negDiag] using hm1
  have hjt : projOf H ⟨diagTau hτ, hJ⟩ * t = t * projOf H ⟨diagTau hτ, hJ⟩ := by
    rw [htdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (diagTau_mul_negDiag hτ)
  obtain ⟨hV, hV2, hJV⟩ := zpowers_involution_witness ht2 ht1 hjt
  refine elemWitness_projImage_of hJ hD ?_ ?_ ?_ (mk_diagTau_mul_cycThree hτ hτ0)
    (fun m hm => mk_diagTau_pow_ne_cycThree hτ hτ0 hm) hV hV2 hJV
  · rw [diagTau_pow_three hτ, map_one]
  · refine mk_ne_one_of_diag_ne (i := 0) (k := 2) ?_
    simpa [coe_diagTau] using hτ1
  · rw [KFacts.cycThree_pow_three, map_one]

end Odd

section Two

variable {K : Type} [Field K] {f : ℕ}

theorem diagUnits_pow (a b c : Kˣ) (m : ℕ) :
    (diagUnits a b c : GL (Fin 3) K) ^ m = diagUnits (a ^ m) (b ^ m) (c ^ m) := by
  induction m with
  | zero =>
    apply Units.ext
    rw [pow_zero, Units.val_one, coe_diagUnits, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, pow_succ, pow_succ, pow_succ]

theorem negSwap01_sq : (negSwap01 : GL (Fin 3) K) ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_negSwap01, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sq, mul_apply, Fin.sum_univ_three]

theorem diagUnits_mul_negSwap01 (a c : Kˣ) :
    diagUnits a a c * (negSwap01 : GL (Fin 3) K) = negSwap01 * diagUnits a a c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_negSwap01]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, diagonal_apply]

theorem elemWitness_unitary_nine (hK : PiField false 2 f K) (h9 : 9 ∣ 2 ^ f + 1) :
    ElemWitness (projImage (slPi false 3 (2 ^ f) K)) := by
  have h := hK.unitary
  have hπ : false = false → UnitaryFieldData 2 f K := fun _ => h
  have := hK.finite
  have hq9 : 2 ^ f % 9 = 8 := by omega
  have hcardK : Nat.card K = (2 ^ f) ^ 2 := by rw [hK.card]; rfl
  have h9K : 9 ∣ Nat.card K - 1 := by
    rw [hcardK]
    have hsq : (2 ^ f) ^ 2 % 9 = 1 := by rw [Nat.pow_mod, hq9]
    have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hcard9 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := K) (d := 9) h9K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity 9 K)
  have hζo : orderOf ζ = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hζ, hcard9]
  set μ : Kˣ := (ζ : Kˣ) with hμ
  have hμo : orderOf μ = 9 := by rw [hμ, Subgroup.orderOf_coe, hζo]
  have hμ9 : μ ^ 9 = 1 := hμo ▸ pow_orderOf_eq_one μ
  have hμ3 : μ ^ 3 ≠ 1 := by
    intro h3
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hμo] at this
    norm_num at this
  set τ : K := ((μ ^ 3 : Kˣ) : K) with hτdef
  have hτ : τ ^ 3 = 1 := by
    rw [hτdef, ← Units.val_pow_eq_pow_val, ← pow_mul, show 3 * 3 = 9 by rfl, hμ9, Units.val_one]
  have hτ1 : τ ≠ 1 := fun h1 => hμ3 (Units.ext h1)
  have hτ0 : τ ≠ 0 := (μ ^ 3).ne_zero
  have hroot : ∀ u : Kˣ, u ^ 9 = 1 → u ∈ rootsOfUnity (qSubPi false (2 ^ f)) K := by
    intro u hu
    rw [mem_rootsOfUnity]
    obtain ⟨k, hk⟩ := h9
    change u ^ (2 ^ f + 1) = 1
    rw [hk, pow_mul, hu, one_pow]
  set J : GL (Fin 3) K := diagUnits μ μ (μ⁻¹ ^ 2) with hJdef
  have hJmem : J ∈ slPi false 3 (2 ^ f) K := by
    rw [mem_slPi_iff hπ]
    refine ⟨diagUnits_mem_glPi hK (hroot μ hμ9) (hroot μ hμ9) (hroot _ ?_), ?_⟩
    · rw [← pow_mul, inv_pow, show 2 * 9 = 9 * 2 by rfl, pow_mul, hμ9, one_pow, inv_one]
    · rw [hJdef, coe_diagUnits, det_fin_three]
      simp
      field_simp
  have hDmem := diagTau_mem_slPi hπ (fun _ => by change 2 ^ f % 3 = 2; omega) hτ
  have hTmem := negSwap01_mem_slPi (p := 2) (f := f) (K := K) hπ
  set H := slPi false 3 (2 ^ f) K with hH
  set t := projOf H ⟨negSwap01, hTmem⟩ with htdef
  have ht2 : t ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨negSwap01, hTmem⟩ : H) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact negSwap01_sq)
    rw [this, map_one]
  have ht1 : t ≠ 1 := by
    intro h1
    have h' : ProjGenLinGroup.mk (negSwap01 : GL (Fin 3) K) = 1 := by
      have := congrArg (fun x : projImage H => (x : ProjGenLinGroup (Fin 3) K)) h1
      simpa [htdef, coe_projOf] using this
    exact mk_ne_one_of_offdiag_ne (i := 0) (k := 1) (by decide) (by simp [coe_negSwap01]) h'
  have hjt : projOf H ⟨J, hJmem⟩ * t = t * projOf H ⟨J, hJmem⟩ := by
    rw [htdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (diagUnits_mul_negSwap01 μ _)
  obtain ⟨hV, hV2, hJV⟩ := zpowers_involution_witness ht2 ht1 hjt
  refine elemWitness_projImage_of hJmem hDmem ?_ ?_ ?_ ?_ ?_ hV hV2 hJV
  ·
    rw [hJdef, diagUnits_pow]
    have h6 : (μ⁻¹ ^ 2) ^ 3 = μ ^ 3 := by
      rw [← pow_mul, inv_pow, show 2 * 3 = 6 by rfl]
      calc (μ ^ 6)⁻¹ = μ ^ 3 * (μ ^ 9)⁻¹ := by group
        _ = μ ^ 3 := by rw [hμ9, inv_one, mul_one]
    rw [h6]
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨μ ^ 3, ?_⟩
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  · refine mk_ne_one_of_diag_ne (i := 0) (k := 2) ?_
    rw [hJdef, coe_diagUnits]
    simp only [diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    intro heq
    apply hμ3
    have heq' : μ = μ⁻¹ ^ 2 := Units.ext heq
    calc μ ^ 3 = μ * μ ^ 2 := by group
      _ = μ⁻¹ ^ 2 * μ ^ 2 := by rw [← heq']
      _ = 1 := by group
  · rw [diagTau_pow_three hτ, map_one]
  · congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hJdef, coe_diagUnits, coe_diagTau]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, diagonal_apply] <;>
      ring
  · intro m hm heq
    obtain ⟨u, hu⟩ := exists_scalar_of_mk_eq_mk heq
    have h00 := hu 0 0
    have h11 := hu 1 1
    rw [hJdef, diagUnits_pow, coe_diagUnits, coe_diagTau] at h00 h11
    simp at h00 h11
    rw [h00] at h11
    apply hτ1
    have : τ * (τ - 1) = 0 := by linear_combination -h11
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hτ0
    · linear_combination h0

end Two

section LinTwo

variable {K : Type} [Field K] {f : ℕ}

@[expose] def transvec02 (a : K) : GL (Fin 3) K :=
  ⟨!![1, 0, a; 0, 1, 0; 0, 0, 1], !![1, 0, -a; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_transvec02 (a : K) :
    ((transvec02 a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, a; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem transvec02_add (a b : K) : transvec02 (a + b) = transvec02 a * transvec02 b := by
  apply Units.ext
  rw [Units.val_mul, coe_transvec02, coe_transvec02, coe_transvec02]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, add_comm]

theorem transvec02_zero : transvec02 (0 : K) = 1 := by
  apply Units.ext
  rw [coe_transvec02, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

@[expose] noncomputable def transvecHom : Multiplicative K →* GL (Fin 3) K where
  toFun a := transvec02 (Multiplicative.toAdd a)
  map_one' := transvec02_zero
  map_mul' a b := transvec02_add _ _

theorem transvec02_mem_slPi_true (q : ℕ) (a : K) : transvec02 a ∈ slPi true 3 q K := by
  rw [mem_slPi_true, coe_transvec02, det_fin_three]
  simp

theorem diagTau_conj_transvec02 {τ : K} (hτ : τ ^ 3 = 1) (a : K) :
    diagTau hτ * transvec02 a * (diagTau hτ)⁻¹ = transvec02 (τ * a) := by
  have h1 : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
  have h2 : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transvec02, coe_transvec02, coe_diagTau,
    show (((diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] from rfl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h1, h2]

theorem elemWitness_linear_two (hK : PiField true 2 f K) (hq : ModThree true (2 ^ f)) :
    ElemWitness (projImage (slPi true 3 (2 ^ f) K)) := by
  have hπ : true = false → UnitaryFieldData 2 f K := fun h => absurd h (by decide)
  have : CharP K 2 := hK.charP
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set H := slPi true 3 (2 ^ f) K with hH
  have hJ := diagTau_mem_slPi hπ (fun h => absurd h (by decide)) hτ
  have hD := cycThree_mem_slPi (p := 2) (f := f) (K := K) hπ
  set ρ : Multiplicative K →* projImage H :=
    (projOf H).comp (transvecHom.codRestrict H fun a => transvec02_mem_slPi_true _ _) with hρdef
  have hρ : ∀ a, ((ρ a : projImage H) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (transvec02 (Multiplicative.toAdd a)) := fun a => rfl
  have hV : ρ.range ≠ ⊥ := by
    intro hbot
    have hmem : ρ (Multiplicative.ofAdd 1) ∈ ρ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h' : ProjGenLinGroup.mk (transvec02 (1 : K)) = 1 := by
      have := congrArg (fun x : projImage H => (x : ProjGenLinGroup (Fin 3) K)) hmem
      simpa [hρ] using this
    exact mk_ne_one_of_offdiag_ne (i := 0) (k := 2) (by decide) (by simp [coe_transvec02]) h'
  have hV2 : IsPGroup 2 ρ.range := by
    intro v
    obtain ⟨a, ha⟩ := v.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, ← ha, ← map_pow]
    have ha2 : a ^ 2 = 1 := by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [ha2, map_one]
    rfl
  have hJV : ∀ v ∈ ρ.range, projOf H ⟨diagTau hτ, hJ⟩ * v * (projOf H ⟨diagTau hτ, hJ⟩)⁻¹ ∈
      ρ.range := by
    rintro _ ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (τ * Multiplicative.toAdd a), Subtype.ext ?_⟩
    rw [hρ, toAdd_ofAdd, ← diagTau_conj_transvec02 hτ, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_projOf, hρ]
  refine elemWitness_projImage_of hJ hD ?_ ?_ ?_ (mk_diagTau_mul_cycThree hτ hτ0)
    (fun m hm => mk_diagTau_pow_ne_cycThree hτ hτ0 hm) hV hV2 hJV
  · rw [diagTau_pow_three hτ, map_one]
  · refine mk_ne_one_of_diag_ne (i := 0) (k := 2) ?_
    simpa [coe_diagTau] using hτ1
  · rw [KFacts.cycThree_pow_three, map_one]

end LinTwo

theorem k13PZeroElem_holds : K13PZeroElem := by
  intro X _ _ hX hXq
  obtain ⟨p, e, _, he, hiso⟩ := hX
  by_cases hexc : p = 2 ∧ p ^ e % 3 = 2 ∧ ¬ 9 ∣ p ^ e + 1
  · right
    obtain ⟨rfl, hq2, h9⟩ := hexc
    rcases hiso with ⟨hq1, -⟩ | ⟨-, ⟨φ⟩⟩
    · omega
    · have hodd : Odd e := by
        rcases Nat.even_or_odd e with ⟨k, rfl⟩ | h
        · exfalso
          have h4 : 2 ^ (k + k) % 3 = 1 := by
            rw [← two_mul, pow_mul, Nat.pow_mod]
            norm_num
          omega
        · exact h
      refine ⟨e, hodd, ?_, ?_, ⟨φ⟩⟩
      · by_contra h1
        have he1 : e = 1 := by omega
        subst he1
        have hs := Sec13.isSolvable_projSU_two
        have hsolv : IsSolvable X :=
          solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
        have : Group.IsPerfect X := hXq.1
        have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hXq
        exact Group.IsPerfect.not_isSolvable X hsolv
      · rintro ⟨m, rfl⟩
        apply h9
        obtain ⟨r, rfl⟩ := (Nat.odd_mul.mp hodd).2
        have h8 : 2 ^ (3 * (2 * r + 1)) % 9 = 8 := by
          rw [show 3 * (2 * r + 1) = 6 * r + 3 by ring, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        omega
  · left
    obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
    refine ElemWitness.of_mulEquiv ψ ?_
    by_cases hp2 : p = 2
    · subst hp2
      cases π
      · have h9 : 9 ∣ 2 ^ e + 1 := by
          by_contra h9
          exact hexc ⟨rfl, hq, h9⟩
        exact elemWitness_unitary_nine hK h9
      · exact elemWitness_linear_two hK hq
    · exact elemWitness_odd hK hq hp2

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
