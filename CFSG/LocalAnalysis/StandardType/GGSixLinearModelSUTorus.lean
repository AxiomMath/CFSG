module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUAut

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace SUModel

variable {f : ℕ} {K : Type} [Field K] {n : ℕ} {G : Type} [Group G]

theorem diagHom_eq_diagGL {m : ℕ} (τ : Fin (m + 1) → Kˣ) :
    diagHom (m + 1) τ = InnerDiagA.diagGL τ :=
  Units.ext (by rw [coe_diagHom, InnerDiagA.coe_diagGL])

theorem det_scalar (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c) = c ^ n := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Units.val_pow_eq_pow_val]

theorem scalar_mem_unitary [NeZero n] (h : UnitaryFieldData 2 f K) {c : Kˣ}
    (hc : c ^ (2 ^ f + 1) = 1) :
    GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
  rw [SUTorus.scalar_mem_primeFormUnitary_iff, h.bar_apply]
  have h1 : ((c : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  rwa [pow_succ] at h1

theorem pow_add_one_of_pow_eq_one {p : ℕ} (hpq : p ∣ 2 ^ f + 1) {x : Kˣ} (hx : x ^ p = 1) :
    x ^ (2 ^ f + 1) = 1 := by
  obtain ⟨k, hk⟩ := hpq
  rw [hk, pow_mul, hx, one_pow]

theorem frameTorus_eq {p : ℕ} (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    {φ : ↥(unitarySU 2 f K n) →* G} (hkerφ : SURep.GGFrameKer φ)
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsD : ∀ b ∈ Bs, SURep.GGFrameDiagU φ b) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    UnitModel.frameTorus p h φ = Bs := by
  refine le_antisymm (UnitModel.frameTorus_le h hcent hBsD hom) fun b hb => ?_
  obtain ⟨τ, hτ⟩ := hBsD b hb
  have i0 : Fin n := ⟨0, by omega⟩
  set τ' : Fin n → Kˣ := fun i => (τ i0)⁻¹ * τ i with hτ'
  have hτ'p : ∀ i, τ' i ^ p = 1 := fun i => by
    rw [hτ', mul_pow, inv_pow, SURep.pow_eq_pow_of_frameActs hkerφ h hn (hexp b hb) hτ i i0,
      inv_mul_cancel]
  have hτ'N : ∀ i, ((τ' i : Kˣ) : K) ^ (2 ^ f + 1) = 1 := fun i => by
    rw [hτ', Units.val_mul, mul_pow, Units.val_inv_eq_inv_val, inv_pow, hτ.1 i0, hτ.1 i, inv_one,
      one_mul]
  have hτeq : τ = fun i => τ i0 * τ' i := funext fun i => by rw [hτ', mul_inv_cancel_left]
  rw [hτeq] at hτ
  exact ⟨τ', hτ'p, UnitModel.frameActs_of_scalar hτ hτ'N⟩


theorem exists_conj_mem_frameTorus_of_det [Finite K] (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hnp : n = p)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {φ : ↥(unitarySU 2 f K n) →* G}
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {y : G} (hyp : y ^ p = 1)
    {Y : GL (Fin n) K} (hYU : Y ∈ primeFormUnitary h (idGram K n))
    (hY : (y, Y) ∈ SUTorus.suPairs φ) (hdet : ∃ c : Kˣ, c ^ p = GeneralLinearGroup.det Y) :
    ∃ s : ↥(unitarySU 2 f K n), (φ s)⁻¹ * y * φ s ∈ UnitModel.frameTorus p h φ := by
  have : NeZero n := ⟨by rw [hnp]; exact hp.ne_zero⟩
  have hn3 : 3 ≤ n := by have := hp.two_le; omega
  have hpow : ∀ u : Kˣ, u ^ n = u ^ p := fun u => by rw [hnp]
  have hYp := (SUTorus.suPairs φ).pow_mem hY p
  rw [Prod.pow_mk, hyp] at hYp
  obtain ⟨l', hl'⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hp hpq hker hYp
  obtain ⟨c, hc⟩ := hdet
  have hcN : c ^ (2 ^ f + 1) = 1 :=
    SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hc (UnitModel.det_pow_eq_one_of_mem h hYU)
  set Y₁ := GeneralLinearGroup.scalar (Fin n) c⁻¹ * Y with hY₁
  have hY₁det : GeneralLinearGroup.det Y₁ = 1 := by
    rw [hY₁, map_mul, det_scalar, hpow, inv_pow, hc, inv_mul_cancel]
  set l := (c⁻¹) ^ p * l' with hl
  have hY₁p : Y₁ ^ p = GeneralLinearGroup.scalar (Fin n) l := by
    rw [hY₁, (TypeA.PGLTor.commute_scalar c⁻¹ Y).mul_pow, hl', ← map_pow, ← map_mul, hl]
  have hlp : l ^ p = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hY₁p
    rw [map_pow, hY₁det, one_pow, det_scalar, hpow] at h1
    exact h1.symm
  obtain ⟨ν, hν⟩ : ∃ ν : Kˣ, ν ^ p = l := by
    by_contra hne
    have hnot : ∀ b : K, b ^ p ≠ (l : K) := by
      intro b hb
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hb
        exact l.ne_zero hb.symm
      exact hne ⟨Units.mk0 b hb0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hb])⟩
    have hdetl := LinModel.det_eq_of_pow_eq_scalar hp hp2 (by rw [Fintype.card_fin, hnp])
      (M := ((Y₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (c := (l : K))
      (by rw [← Units.val_pow_eq_pow_val, hY₁p, GeneralLinearGroup.coe_scalar]) hnot
    have h1 := GeneralLinearGroup.val_det_apply Y₁
    rw [hY₁det, Units.val_one, hdetl] at h1
    exact hne ⟨1, by rw [one_pow]; exact Units.ext h1⟩
  have hνN : ν ^ (2 ^ f + 1) = 1 :=
    SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hν (pow_add_one_of_pow_eq_one hpq hlp)
  set Y₂ := GeneralLinearGroup.scalar (Fin n) ν⁻¹ * Y₁ with hY₂
  have hY₂U : Y₂ ∈ primeFormUnitary h (idGram K n) := by
    refine (primeFormUnitary h _).mul_mem (scalar_mem_unitary h (by rw [inv_pow, hνN, inv_one]))
      ((primeFormUnitary h _).mul_mem (scalar_mem_unitary h (by rw [inv_pow, hcN, inv_one])) hYU)
  have hY₂p : Y₂ ^ p = 1 := by
    rw [hY₂, (TypeA.PGLTor.commute_scalar ν⁻¹ Y₁).mul_pow, hY₁p, ← map_pow, ← map_mul, inv_pow,
      hν, inv_mul_cancel, map_one]
  have hY₂pair : (y, Y₂) ∈ SUTorus.suPairs φ := by
    have h1 := (SUTorus.suPairs φ).mul_mem (SUTorus.one_scalar_mem_suPairs φ ν⁻¹)
      ((SUTorus.suPairs φ).mul_mem (SUTorus.one_scalar_mem_suPairs φ c⁻¹) hY)
    rwa [Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul] at h1
  obtain ⟨s₀, τ, hτ⟩ := UnitModel.exists_det_one_conj_diag h hp hpq hY₂U hY₂p
  refine ⟨s₀, ?_⟩
  have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem
    ((SUTorus.suPairs φ).inv_mem (UnitModel.mem_suPairs_coe φ s₀)) hY₂pair)
    (UnitModel.mem_suPairs_coe φ s₀)
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, hτ] at h1
  have hτp : ∀ i, τ i ^ p = 1 := by
    have h2 : diagHom n (τ ^ p) = 1 := by
      rw [map_pow, ← hτ, show ((s₀ : GL (Fin n) K))⁻¹ * Y₂ * s₀ =
        MulAut.conj ((s₀ : GL (Fin n) K))⁻¹ Y₂ by rw [MulAut.conj_apply, inv_inv], ← map_pow,
        hY₂p, map_one]
    intro i
    have h3 := congrFun (diagHom_injective n (h2.trans (map_one _).symm)) i
    simpa using h3
  have hτN : ∀ i, ((τ i : Kˣ) : K) ^ (2 ^ f + 1) = 1 := fun i => by
    rw [← Units.val_pow_eq_pow_val, pow_add_one_of_pow_eq_one hpq (hτp i), Units.val_one]
  exact ⟨τ, hτp, hτN, fun s s' hs' => h1.2 s s' hs'⟩

theorem exists_mem_suPairs_of_det [Finite K] (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hnp : n = p)
    {φ : ↥(unitarySU 2 f K n) →* G} {g₀ : G} {A₀ : GL (Fin n) K}
    (hA₀U : A₀ ∈ primeFormUnitary h (idGram K n)) (h₀ : (g₀, A₀) ∈ SUTorus.suPairs φ)
    (hdet : ¬ ∃ c : Kˣ, c ^ p = GeneralLinearGroup.det A₀) {A : GL (Fin n) K}
    (hAU : A ∈ primeFormUnitary h (idGram K n)) : ∃ g : G, (g, A) ∈ SUTorus.suPairs φ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero n := ⟨by rw [hnp]; exact hp.ne_zero⟩
  have hpow : ∀ u : Kˣ, u ^ n = u ^ p := fun u => by rw [hnp]
  set x : TypeA.PGLTor.PowQuot K p := QuotientGroup.mk (GeneralLinearGroup.det A₀) with hx
  have hx1 : x ≠ 1 := fun h' => hdet (TypeA.PGLTor.powQuot_mk_eq_one_iff.mp h')
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨_, rfl⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have htop : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hord]
    exact TypeA.PGLTor.card_powQuot_le
  have hmem : (QuotientGroup.mk (GeneralLinearGroup.det A) : TypeA.PGLTor.PowQuot K p) ∈
      Subgroup.zpowers x := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [hx, ← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' : c ^ p = (GeneralLinearGroup.det A₀ ^ k)⁻¹ * GeneralLinearGroup.det A := hc
  have hdA₀ : GeneralLinearGroup.det A₀ ^ (2 ^ f + 1) = 1 := UnitModel.det_pow_eq_one_of_mem h hA₀U
  have hdA : GeneralLinearGroup.det A ^ (2 ^ f + 1) = 1 := UnitModel.det_pow_eq_one_of_mem h hAU
  have hcN : c ^ (2 ^ f + 1) = 1 := SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hc' (by
    rw [mul_pow, inv_pow, hdA, mul_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm k,
      _root_.zpow_mul, zpow_natCast, hdA₀, _root_.one_zpow, inv_one])
  set S := GeneralLinearGroup.scalar (Fin n) c⁻¹ * A * A₀ ^ (-k) with hS
  have hSU : S ∈ primeFormUnitary h (idGram K n) :=
    (primeFormUnitary h _).mul_mem ((primeFormUnitary h _).mul_mem
      (scalar_mem_unitary h (by rw [inv_pow, hcN, inv_one])) hAU)
      ((primeFormUnitary h _).zpow_mem hA₀U _)
  have hdA' : GeneralLinearGroup.det A = GeneralLinearGroup.det A₀ ^ k * c ^ p := by
    rw [hc']
    group
  have hSdet : GeneralLinearGroup.det S = 1 := by
    rw [hS, map_mul, map_mul, map_zpow, det_scalar, hpow, hdA',
      mul_comm (GeneralLinearGroup.det A₀ ^ k) (c ^ p)]
    group
  have hSSU : S ∈ unitarySU 2 f K n := by
    rw [mem_unitarySU_iff h]
    refine ⟨by rw [← GeneralLinearGroup.val_det_apply, hSdet, Units.val_one], ?_⟩
    have h1 := mem_primeFormUnitary.mp hSU
    rwa [idGram, Units.val_one, Matrix.mul_one] at h1
  have hg := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem
    (SUTorus.one_scalar_mem_suPairs φ c) (UnitModel.mem_suPairs_coe φ ⟨S, hSSU⟩))
    ((SUTorus.suPairs φ).zpow_mem h₀ k)
  rw [Prod.pow_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul] at hg
  have hA : GeneralLinearGroup.scalar (Fin n) c * S * A₀ ^ k = A := by
    rw [hS, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul, mul_assoc,
      ← _root_.zpow_add, neg_add_cancel, _root_.zpow_zero, mul_one]
  rw [hA] at hg
  exact ⟨_, hg⟩

end SUModel

end CFSG.StandardType
