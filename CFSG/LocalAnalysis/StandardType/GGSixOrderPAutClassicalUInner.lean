module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFrame
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace OrdPInnerSU

theorem exists_pow_eq_of_coprime {M : Type*} [CommGroup M] {p n N : ℕ}
    (hcop : Nat.Coprime p (Nat.gcd n N)) {δ l : M} (hδ : δ ^ N = 1) (hl : l ^ N = 1)
    (hδl : δ ^ p = l ^ n) : ∃ ν : M, ν ^ N = 1 ∧ ν ^ n = δ := by
  have hd : ((Nat.gcd n N : ℕ) : ℤ) = n * Nat.gcdA n N + N * Nat.gcdB n N :=
    Nat.gcd_eq_gcd_ab n N
  have h1 : ((Nat.gcd p (Nat.gcd n N) : ℕ) : ℤ) =
      p * Nat.gcdA p (Nat.gcd n N) + (Nat.gcd n N) * Nat.gcdB p (Nat.gcd n N) :=
    Nat.gcd_eq_gcd_ab p (Nat.gcd n N)
  rw [hcop, Nat.cast_one] at h1
  set x := Nat.gcdA p (Nat.gcd n N)
  set w := Nat.gcdB p (Nat.gcd n N)
  set a := Nat.gcdA n N
  set b := Nat.gcdB n N
  have hδN : δ ^ (N : ℤ) = 1 := by rw [_root_.zpow_natCast, hδ]
  have hlN : l ^ (N : ℤ) = 1 := by rw [_root_.zpow_natCast, hl]
  have hδp : δ ^ (p : ℤ) = l ^ (n : ℤ) := by rw [_root_.zpow_natCast, _root_.zpow_natCast, hδl]
  refine ⟨l ^ x * δ ^ (w * a), ?_, ?_⟩
  · rw [← _root_.zpow_natCast, _root_.mul_zpow, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm x,
      mul_comm (w * a), _root_.zpow_mul, _root_.zpow_mul, hlN, hδN, _root_.one_zpow,
      _root_.one_zpow, one_mul]
  · have e1 : (1 : ℤ) = p * x + n * (w * a) + N * (b * w) := by
      have : ((Nat.gcd n N : ℕ) : ℤ) * w = (n * a + N * b) * w := by rw [hd]
      linear_combination h1 + this
    calc (l ^ x * δ ^ (w * a)) ^ n = (l ^ x * δ ^ (w * a)) ^ (n : ℤ) :=
          (_root_.zpow_natCast _ _).symm
      _ = (l ^ (n : ℤ)) ^ x * δ ^ ((n : ℤ) * (w * a)) := by
        rw [_root_.mul_zpow, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm x, mul_comm (w * a),
          _root_.zpow_mul]
      _ = (δ ^ (p : ℤ)) ^ x * δ ^ ((n : ℤ) * (w * a)) * (δ ^ (N : ℤ)) ^ (b * w) := by
        rw [hδp, hδN, _root_.one_zpow, mul_one]
      _ = δ ^ ((p : ℤ) * x + n * (w * a) + N * (b * w)) := by
        rw [← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add, ← _root_.zpow_add]
      _ = δ := by rw [← e1, _root_.zpow_one]

section Identity

variable {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)

include h in
theorem det_pow_eq_one_of_mem {B : GL (Fin n) K} (hB : B ∈ primeFormUnitary h (idGram K n)) :
    (B : Matrix (Fin n) (Fin n) K).det ^ (2 ^ f + 1) = 1 := by
  have h1 := congrArg Matrix.det (mem_primeFormUnitary.1 hB)
  rw [idGram, Units.val_one, Matrix.mul_one, det_mul, det_transpose, det_one] at h1
  have h2 : ((B : Matrix (Fin n) (Fin n) K).map h.bar).det =
      h.bar (B : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det h.bar _).symm
  rw [h2, UnitaryFieldData.bar_apply] at h1
  rw [pow_succ]
  exact h1

include h in
theorem pow_eq_one_of_scalar_mem [NeZero n] {l : Kˣ}
    (hl : Matrix.GeneralLinearGroup.scalar (Fin n) l ∈ primeFormUnitary h (idGram K n)) :
    l ^ (2 ^ f + 1) = 1 := by
  have h1 := (SUTorus.scalar_mem_primeFormUnitary_iff h l).mp hl
  rw [UnitaryFieldData.bar_apply] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
  exact h1

include h in
theorem scalar_mem_of_pow [NeZero n] {l : Kˣ} (hl : l ^ (2 ^ f + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin n) l ∈ primeFormUnitary h (idGram K n) := by
  rw [SUTorus.scalar_mem_primeFormUnitary_iff h l, UnitaryFieldData.bar_apply,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, hl, Units.val_one]

theorem det_scalar_units (l : Kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) l) = l ^ n := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Units.val_pow_eq_pow_val]

theorem mem_suPairs_self {G : Type*} [Group G] (φ : ↥(unitarySU 2 f K n) →* G)
    (s : ↥(unitarySU 2 f K n)) : (φ s, (s : GL (Fin n) K)) ∈ SUTorus.suPairs φ := by
  refine ⟨Subgroup.le_normalizer s.2, fun u v hv => ?_⟩
  have hv' : v = s * u * s⁻¹ := Subtype.ext (by rw [hv]; rfl)
  rw [hv', map_mul, map_mul, map_inv]

include h in
theorem exists_mul_diagHom_mem (hn : 1 ≤ n) {H : GL (Fin n) K}
    (hH : H ∈ primeFormUnitary h (idGram K n)) :
    ∃ τ : Fin n → Kˣ, H * diagHom n τ ∈ unitarySU 2 f K n := by
  classical
  set δ := Matrix.GeneralLinearGroup.det H with hδ
  have hδq : δ ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hδ, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_pow_eq_one_of_mem h hH
  set i₀ : Fin n := ⟨0, hn⟩
  set τ : Fin n → Kˣ := Pi.mulSingle i₀ δ⁻¹ with hτ
  have hτq : ∀ k, ((τ k : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
    intro k
    rw [← Units.val_pow_eq_pow_val, hτ]
    by_cases hk : k = i₀
    · rw [hk, Pi.mulSingle_eq_same, inv_pow, hδq, inv_one, Units.val_one]
    · rw [Pi.mulSingle_eq_of_ne hk, one_pow, Units.val_one]
  refine ⟨τ, TableBUE.mem_unitarySU_of_mem_primeFormUnitary h
    (mul_mem hH (TableBUD.diagHom_mem_primeFormUnitary h hτq)) ?_⟩
  rw [Units.val_mul, det_mul, det_diagHom, ← Units.coe_prod, hτ, Finset.prod_pi_mulSingle']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← hδ, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

include h in
theorem exists_su_conj_diag (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(unitarySU 2 f K n)} (hA : IsElemAbelian p A) :
    ∃ P : ↥(unitarySU 2 f K n), ∀ x ∈ A, ∃ σ : Fin n → Kˣ,
      ((P⁻¹ * x * P : ↥(unitarySU 2 f K n)) : GL (Fin n) K) = diagHom n σ := by
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA
  obtain ⟨τ, hPD⟩ := exists_mul_diagHom_mem h hn hP
  refine ⟨⟨P * diagHom n τ, hPD⟩, fun x hx => ?_⟩
  obtain ⟨σ, hσ⟩ := hPd x hx
  refine ⟨σ, ?_⟩
  rw [TableBUE.coe_conjSU] at hσ
  change (P * diagHom n τ)⁻¹ * (x : GL (Fin n) K) * (P * diagHom n τ) = diagHom n σ
  calc (P * diagHom n τ)⁻¹ * (x : GL (Fin n) K) * (P * diagHom n τ) =
      (diagHom n τ)⁻¹ * (P⁻¹ * x * P) * diagHom n τ := by group
    _ = (diagHom n τ)⁻¹ * diagHom n σ * diagHom n τ := by rw [hσ]
    _ = diagHom n σ := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm τ⁻¹ σ, mul_assoc, inv_mul_cancel, mul_one]

end Identity

section Inner

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {G : Type} [Group G]

omit [CharP F 2] in
theorem exists_eq_of_mem_suPairs (h : UnitaryFieldData 2 f F) (hn : 4 ≤ n)
    {φ : ↥(unitarySU 2 f F n) →* G} (hker₁ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n))
    (hC₁ : Subgroup.centralizer (φ.range : Set G) = ⊥) {p : ℕ}
    (hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1))) {c : G} {B : GL (Fin n) F}
    (hBU : B ∈ primeFormUnitary h (idGram F n)) (hB : (c⁻¹, B) ∈ SUTorus.suPairs φ)
    (hcp : c ^ p = 1) : ∃ s : ↥(unitarySU 2 f F n), φ s = c ∧ s ^ p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero n := ⟨by omega⟩
  have hF : Nat.card F = (2 ^ f) ^ 2 := h.card_eq_sq
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd (show 2 ^ f + 1 ≠ 1 by
    have := Nat.one_le_two_pow (n := f)
    omega)
  have hBp : ((1 : G), B ^ p) ∈ SUTorus.suPairs φ := by
    have h1 := (SUTorus.suPairs φ).pow_mem hB p
    rwa [Prod.pow_mk, inv_pow, hcp, inv_one] at h1
  obtain ⟨l, hl⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hr hrq hker₁ hBp
  have hlU : Matrix.GeneralLinearGroup.scalar (Fin n) l ∈ primeFormUnitary h (idGram F n) := by
    rw [← hl]
    exact (primeFormUnitary h (idGram F n)).pow_mem hBU p
  have hlq : l ^ (2 ^ f + 1) = 1 := pow_eq_one_of_scalar_mem h hlU
  set δ := Matrix.GeneralLinearGroup.det B with hδdef
  have hδq : δ ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hδdef, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_pow_eq_one_of_mem h hBU
  have hδp : δ ^ p = l ^ n := by
    rw [hδdef, ← map_pow, hl, det_scalar_units]
  obtain ⟨ν, hνq, hνn⟩ := exists_pow_eq_of_coprime hcop hδq hlq hδp
  set B' := Matrix.GeneralLinearGroup.scalar (Fin n) ν⁻¹ * B with hB'def
  have hB'U : B' ∈ primeFormUnitary h (idGram F n) :=
    mul_mem (scalar_mem_of_pow h (by rw [inv_pow, hνq, inv_one])) hBU
  have hB'det : (B' : Matrix (Fin n) (Fin n) F).det = 1 := by
    have e : Matrix.GeneralLinearGroup.det B' = 1 := by
      rw [hB'def, map_mul, det_scalar_units, inv_pow, hνn, ← hδdef, inv_mul_cancel]
    have := congrArg Units.val e
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  have hB'SU : B' ∈ unitarySU 2 f F n :=
    TableBUE.mem_unitarySU_of_mem_primeFormUnitary h hB'U hB'det
  have hB'pair : (c⁻¹, B') ∈ SUTorus.suPairs φ := by
    have h1 := (SUTorus.suPairs φ).mul_mem (SUTorus.one_scalar_mem_suPairs φ ν⁻¹) hB
    rwa [Prod.mk_mul_mk, one_mul] at h1
  set b' : ↥(unitarySU 2 f F n) := ⟨B', hB'SU⟩ with hb'
  have hcb : c⁻¹ = φ b' := by
    have h1 := (SUTorus.suPairs φ).mul_mem hB'pair
      ((SUTorus.suPairs φ).inv_mem (mem_suPairs_self φ b'))
    rw [Prod.inv_mk, Prod.mk_mul_mk, show (b' : GL (Fin n) F) = B' from rfl, mul_inv_cancel] at h1
    have h2 := SUTorus.mem_centralizer_of_mem_suPairs_one h1
    rw [hC₁, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  set s₀ := b'⁻¹ with hs₀
  have hφs₀ : φ s₀ = c := by rw [hs₀, map_inv, ← hcb, inv_inv]
  set d := Nat.gcd n (2 ^ f + 1) with hd
  have hz1 : φ (s₀ ^ p) = 1 := by rw [map_pow, hφs₀, hcp]
  obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ (s₀ ^ p) hz1
  have hzd : (s₀ ^ p) ^ d = 1 := by
    obtain ⟨hdet, huni⟩ := (mem_unitarySU_iff h).mp (s₀ ^ p).2
    rw [he, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    rw [he, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at huni
    have hbar := congrFun (Matrix.diagonal_injective huni) ⟨0, by omega⟩
    simp only [UnitaryFieldData.bar_apply] at hbar
    have heq : e ^ (2 ^ f + 1) = 1 := by rw [pow_succ]; exact hbar
    have hed : e ^ d = 1 := pow_gcd_eq_one.mpr ⟨hdet, heq⟩
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, he, ← map_pow, hed, map_one]
    rfl
  have hcop' : Nat.gcd d p = 1 := (Nat.coprime_comm.mp hcop)
  have hbez : ((Nat.gcd d p : ℕ) : ℤ) = d * Nat.gcdA d p + p * Nat.gcdB d p :=
    Nat.gcd_eq_gcd_ab d p
  rw [hcop', Nat.cast_one] at hbez
  refine ⟨s₀ ^ ((d : ℤ) * Nat.gcdA d p), ?_, ?_⟩
  · rw [map_zpow, hφs₀]
    have e1 : (d : ℤ) * Nat.gcdA d p = 1 - p * Nat.gcdB d p := by linear_combination -hbez
    rw [e1, _root_.zpow_sub, _root_.zpow_one, _root_.zpow_mul, _root_.zpow_natCast, hcp,
      _root_.one_zpow, inv_one, mul_one]
  · rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, _root_.zpow_mul,
      _root_.zpow_natCast, _root_.zpow_natCast, hzd, _root_.one_zpow]

include hF in
theorem exists_eq_frame_of_innerDiag (hf : 1 ≤ f) (hn : 4 ≤ n)
    {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {P₀ : GL (Fin n) F}
    (hP₀ : conjTr (unitaryInvolution F 2 f) (P₀ : Matrix (Fin n) (Fin n) F) *
      (P₀ : Matrix (Fin n) (Fin n) F) = antidiag n)
    {p : ℕ} (hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1))) {c : G}
    (hc : GGPsiInnerDiag (Unitary.rootDatum hF n) ψ c) (hcp : c ^ p = 1) :
    ∃ s : ↥(unitarySU 2 f F n), SURep.ggFrameU hF ψ P₀ hP₀ s = c ∧ s ^ p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn G ψ hker c hc
  refine exists_eq_of_mem_suPairs h hn (SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker)
    (by rw [SURep.range_ggFrameU]; exact hC) hcop
    (SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA)) ?_ hcp
  exact SUTorus.mem_suPairs_transfer P₀ hP₀
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n) hA
    (fun u => by rw [inv_inv]; exact hAc u)

end Inner

section Split

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

omit [Finite F] [CharP F 2] in
theorem commute_of_frame {P x z : ↥(unitarySU 2 f F n)} {σ τ : Fin n → Fˣ}
    (hx : ((P⁻¹ * x * P : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = diagHom n σ)
    (hz : ((P⁻¹ * z * P : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = diagHom n τ) :
    x * z = z * x := by
  apply Subtype.ext
  have hx' : (x : GL (Fin n) F) = (P : GL (Fin n) F) * diagHom n σ * (P : GL (Fin n) F)⁻¹ := by
    have h1 : (P : GL (Fin n) F)⁻¹ * x * P = diagHom n σ := hx
    rw [← h1]
    group
  have hz' : (z : GL (Fin n) F) = (P : GL (Fin n) F) * diagHom n τ * (P : GL (Fin n) F)⁻¹ := by
    have h1 : (P : GL (Fin n) F)⁻¹ * z * P = diagHom n τ := hz
    rw [← h1]
    group
  simp only [Subgroup.coe_mul]
  rw [hx', hz']
  calc (P : GL (Fin n) F) * diagHom n σ * (P : GL (Fin n) F)⁻¹ *
        ((P : GL (Fin n) F) * diagHom n τ * (P : GL (Fin n) F)⁻¹) =
      (P : GL (Fin n) F) * (diagHom n σ * diagHom n τ) * (P : GL (Fin n) F)⁻¹ := by group
    _ = (P : GL (Fin n) F) * (diagHom n τ * diagHom n σ) * (P : GL (Fin n) F)⁻¹ := by
      rw [← map_mul, ← map_mul, mul_comm]
    _ = (P : GL (Fin n) F) * diagHom n τ * (P : GL (Fin n) F)⁻¹ *
        ((P : GL (Fin n) F) * diagHom n σ * (P : GL (Fin n) F)⁻¹) := by group

include hF in
theorem exists_bstar_frame {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G}
    (hf : 1 ≤ f) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : p ∣ 2 ^ f + 1) (hpn : ¬ p ∣ n) {P₀ : GL (Fin n) F}
    (hP₀ : conjTr (unitaryInvolution F 2 f) (P₀ : Matrix (Fin n) (Fin n) F) *
      (P₀ : Matrix (Fin n) (Fin n) F) = antidiag n) :
    ∃ P : ↥(unitarySU 2 f F n), ∀ b ∈ Bs, ∃ x : ↥(unitarySU 2 f F n),
      SURep.ggFrameU hF ψ P₀ hP₀ x = b ∧ x ^ p = 1 ∧ ∃ σ : Fin n → Fˣ,
        ((P⁻¹ * x * P : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = diagHom n σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have hpp := hS.prime
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hpn' : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpn
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => hpn (hd.trans (Nat.gcd_dvd_left _ _))
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hker₁ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hBsφ : Bs ≤ φ.range := fun b hb => by
    obtain ⟨s, hs, -⟩ := exists_eq_frame_of_innerDiag hF hf hn hker hC hP₀ hcop
      (hS.innerDiag b hb) (hS.elem.2 b hb)
    exact ⟨s, hs⟩
  have hnp : ∀ z ∈ φ.rangeRestrict.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    rw [MonoidHom.ker_rangeRestrict] at hz
    obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ z hz
    obtain ⟨hdet, -⟩ := (mem_unitarySU_iff h).mp z.2
    rw [he, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    have hep : e ^ p = 1 := by
      have h1 := congrArg (fun g : ↥(unitarySU 2 f F n) =>
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hzp
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, he, ← map_pow, OneMemClass.coe_one,
        Units.val_one] at h1
      have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.scalar_apply] using h2
    have he1 : e = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hep, hdet⟩
      rwa [hpn'.gcd_eq_one, pow_one] at h1
    apply Subtype.ext
    apply Units.ext
    rw [he, he1, map_one]
    rfl
  have hAb : IsElemAbelian p (Bs.subgroupOf φ.range) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact TableB.IsElemAbelian.comm hS.elem (Subgroup.mem_subgroupOf.mp a.2)
        (Subgroup.mem_subgroupOf.mp b.2)
    · simpa using hS.elem.2 _ (Subgroup.mem_subgroupOf.mp ha)
  obtain ⟨A, hAmap, -, hA, -⟩ := TableBUE.exists_lift_of_noTorsion φ.rangeRestrict
    φ.rangeRestrict_surjective hpp hnp hAb
  obtain ⟨P, hP⟩ := exists_su_conj_diag h (by omega) hpp hpq hA
  refine ⟨P, fun b hb => ?_⟩
  have hb' : (⟨b, hBsφ hb⟩ : φ.range) ∈ Bs.subgroupOf φ.range := Subgroup.mem_subgroupOf.mpr hb
  rw [← hAmap] at hb'
  obtain ⟨x, hx, hxe⟩ := hb'
  exact ⟨x, congrArg Subtype.val hxe, hA.2 x hx, hP x hx⟩

include hF in
theorem exists_conj_mem_centralizer_split {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hf : 1 ≤ f) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : p ∣ 2 ^ f + 1) (hpn : ¬ p ∣ n) {y : G} (hyp : y ^ p = 1)
    (hy : GGPsiInnerDiag (Unitary.rootDatum hF n) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have hpp := hS.prime
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => hpn (hd.trans (Nat.gcd_dvd_left _ _))
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hrφ : φ.range = G₀ := (SURep.range_ggFrameU hF ψ P₀ hP₀).trans hrange
  obtain ⟨s₁, hs₁, hs₁p⟩ := exists_eq_frame_of_innerDiag hF hf hn hker hC hP₀ hcop hy hyp
  rw [← hφ] at hs₁
  obtain ⟨P, hP⟩ := exists_bstar_frame hF hf hS hpq hpn hP₀
  have hzp : IsElemAbelian p (Subgroup.zpowers s₁) := by
    refine ⟨Subgroup.zpowers_isMulCommutative _, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hs₁p, _root_.one_zpow]
  obtain ⟨P₁, hP₁⟩ := exists_su_conj_diag h (by omega) hpp hpq hzp
  obtain ⟨σ₁, hσ₁⟩ := hP₁ s₁ (Subgroup.mem_zpowers s₁)
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ↥(unitarySU 2 f F n), m₀ = P₁ * P⁻¹ := ⟨_, rfl⟩
  refine ⟨φ m₀, Subgroup.le_normalizer (hrφ ▸ ⟨m₀, rfl⟩), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨x, hxb, -, σx, hσx⟩ := hP b hb
  rw [← hφ] at hxb
  have hσ₁' : ((P⁻¹ * (m₀⁻¹ * s₁ * m₀) * P : ↥(unitarySU 2 f F n)) : GL (Fin n) F) =
      diagHom n σ₁ := by
    rw [← hσ₁, hm₀]
    congr 1
    group
  have hcomm := commute_of_frame hσx hσ₁'
  calc b * ((φ m₀)⁻¹ * y * φ m₀) = φ (x * (m₀⁻¹ * s₁ * m₀)) := by
        rw [map_mul, map_mul, map_mul, map_inv, hxb, hs₁]
    _ = φ (m₀⁻¹ * s₁ * m₀ * x) := by rw [hcomm]
    _ = (φ m₀)⁻¹ * y * φ m₀ * b := by rw [map_mul, map_mul, map_mul, map_inv, hxb, hs₁]

end Split

end OrdPInnerSU

section Family

theorem ggOrdPInnerConj_PSU_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ → ¬ GGOutdiagPrimeConfig p .PSU n f →
    p ∣ 2 ^ f + 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hout hpq y _ hyo hy
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hpn : ¬ p ∣ n := fun hpn => hout (Or.inr (Or.inl ⟨rfl, hpn, hpq⟩))
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact OrdPInnerSU.exists_conj_mem_centralizer_split
    (F := GaloisField 2 (2 * (f + 1))) (card_galoisField_two_mul 2 (f + 1) (by omega)) (by omega)
    hS hpq hpn hyp hy

@[expose] def GGOrdPInnerConjPSUNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSU n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f + 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPInnerConjAt_PSU_of_nonsplit (h : GGOrdPInnerConjPSUNonsplit) :
    GGOrdPInnerConjAt .PSU := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hout y hyM hyo hy
  by_cases hpq : p ∣ 2 ^ f + 1
  · exact ggOrdPInnerConj_PSU_split G p Bs G₀ n f ψ hS hout hpq y hyM hyo hy
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hy

end Family

end CFSG.StandardType
