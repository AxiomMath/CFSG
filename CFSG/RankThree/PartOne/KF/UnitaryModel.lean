module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem torusSU_le_unitarySU (h : UnitaryFieldData ℓ f K) (hpq : p ∣ ℓ ^ f + 1) :
    torusSU p n K ≤ unitarySU ℓ f K n := by
  rintro g hg
  obtain ⟨d, hd1, hd2, rfl⟩ := mem_torusSU_iff.mp hg
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [det_diagU, ← Units.coe_prod, hd2, Units.val_one]
  · rw [diagU_val, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun i => h.bar (d i : K) * (d i : K)) = fun _ => 1 := funext fun i =>
      bar_eq_inv_of_pow_eq_one h hpq (by
        have := congrArg (fun u : Kˣ => (u : K)) (hd1 i)
        simpa using this)
    rw [this, Matrix.diagonal_one]


theorem scalars_subgroupOf_eq_bot (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 1 ≤ n)
    (hgcd : Nat.gcd n (2 ^ f + 1) = 1) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) = ⊥ := by
  have h1 := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn).2.2
  rw [hgcd] at h1
  exact Subgroup.card_eq_one.mp h1

@[expose] noncomputable def projEquivOfBot {H : Subgroup (GL (Fin n) K)}
    (hbot : (StatedScalars (Fin n) K).subgroupOf H = ⊥) : StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot

theorem exists_diag_iso_le_of_iso {Lg : Type} [Group Lg] (hU : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (ψ₀ : unitarySU ℓ f K n ≃* Lg) (F : Subgroup Lg)
    (hFexp : ∀ x ∈ F, x ^ p = 1) (hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    ∃ ψ : unitarySU ℓ f K n ≃* Lg, ∀ g : unitarySU ℓ f K n, ψ g ∈ F →
      (g : GL (Fin n) K) ∈ torusSU p n K := by
  classical
  have hfinK : Finite K := hU.finite
  have hle := unitarySU_le_primeFormUnitary (n := n) hU
  set F₀ : Subgroup (unitarySU ℓ f K n) := F.comap (ψ₀ : unitarySU ℓ f K n →* Lg) with hF₀
  have hmem : ∀ x : unitarySU ℓ f K n, x ∈ F₀ ↔ ψ₀ x ∈ F := fun x => Iff.rfl
  set G' : Subgroup (primeFormUnitary hU (idGram K n)) := F₀.map (Subgroup.inclusion hle) with hG'
  have hG'mem : ∀ x ∈ G', ∃ x₀ ∈ F₀, Subgroup.inclusion hle x₀ = x := fun x hx => by
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp hx
    exact ⟨x₀, hx₀, hx⟩
  have hGcomm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hG'mem y hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply ψ₀.injective
    rw [map_mul, map_mul]
    exact hFcomm _ ((hmem x₀).mp hx₀) _ ((hmem y₀).mp hy₀)
  have hGpow : ∀ x ∈ G', x ^ p = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    rw [← map_pow]
    have : x₀ ^ p = 1 := ψ₀.injective (by rw [map_pow, map_one]; exact hFexp _ ((hmem x₀).mp hx₀))
    rw [this, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag hU hp hpq G' hGcomm hGpow
  refine ⟨(conjSU hU P).trans ψ₀, fun g hg => ?_⟩
  have hx₀ : conjSU hU P g ∈ F₀ := hg
  have hdiag := hP _ (Subgroup.mem_map.mpr ⟨_, hx₀, rfl⟩)
  have hco : (((P⁻¹ * Subgroup.inclusion hle (conjSU hU P g) * P :
      primeFormUnitary hU (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    congr 1
    simp [coe_conjSU, mul_assoc]
  rw [hco] at hdiag
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
  have hgp : (g : GL (Fin n) K) ^ p = 1 := by
    have : g ^ p = 1 := by
      apply ((conjSU hU P).trans ψ₀).injective
      rw [map_pow, map_one]
      exact hFexp _ hg
    have h2 := congrArg (fun x : unitarySU ℓ f K n => (x : GL (Fin n) K)) this
    simpa using h2
  refine mem_torusSU_iff.mpr ⟨d, fun i => ?_, ?_, hd⟩
  · have h1 : diagU (d ^ p) = 1 := by
      rw [← diagU_pow, hd, hgp]
    have h2 : d ^ p = 1 := diagU_injective (h1.trans diagU_one.symm)
    exact congrFun h2 i
  · have hdet := ((mem_unitarySU_iff hU).mp g.2).1
    rw [← hd, det_diagU] at hdet
    exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)


theorem exists_diag_iso_le {Lg : Type} [Group Lg] [Finite Lg] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hZ : Subgroup.center Lg = ⊥)
    (e : Lg ⧸ Subgroup.center Lg ≃* StatedProj (StatedSU 4 (2 ^ f) K))
    (F : Subgroup Lg) (hFexp : ∀ x ∈ F, x ^ p = 1) (hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    ∃ ψ : unitarySU 2 f K 4 ≃* Lg, ∀ g : unitarySU 2 f K 4, ψ g ∈ F →
      (g : GL (Fin 4) K) ∈ torusSU p 4 K := by
  classical
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hodd : Nat.gcd 4 (2 ^ f + 1) = 1 := by
    have h2 : Odd (2 ^ f + 1) := by
      have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact this.add_one
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h2)
    simpa using this
  let ce : Lg ⧸ Subgroup.center Lg ≃* Lg :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let pe := projEquivOfBot (scalars_subgroupOf_eq_bot hK (by norm_num : 1 ≤ 4) hodd)
  let ψ₀ : unitarySU 2 f K 4 ≃* Lg := pe.symm.trans (e.symm.trans ce)
  exact exists_diag_iso_le_of_iso hU hp hpq ψ₀ F hFexp hFcomm

theorem exists_diag_iso {Lg : Type} [Group Lg] [Finite Lg] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hZ : Subgroup.center Lg = ⊥)
    (e : Lg ⧸ Subgroup.center Lg ≃* StatedProj (StatedSU 4 (2 ^ f) K))
    (F : Subgroup Lg) (hFexp : ∀ x ∈ F, x ^ p = 1) (hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hFcard : Nat.card F = p ^ 3) :
    ∃ ψ : unitarySU 2 f K 4 ≃* Lg, ∀ g : unitarySU 2 f K 4,
      ψ g ∈ F ↔ (g : GL (Fin 4) K) ∈ torusSU p 4 K := by
  classical
  have hfinK : Finite K := (⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩ :
    UnitaryFieldData 2 f K).finite
  obtain ⟨ψ, hsub⟩ := exists_diag_iso_le hf hK hp hpq hZ e F hFexp hFcomm
  refine ⟨ψ, fun g => ?_⟩
  set Ft : Subgroup (unitarySU 2 f K 4) :=
    F.comap (ψ : unitarySU 2 f K 4 →* Lg) with hFt
  have hFtle : Ft.map (unitarySU 2 f K 4).subtype ≤ torusSU p 4 K := by
    rintro _ ⟨g, hg, rfl⟩
    exact hsub g hg
  have hcard : Nat.card (Ft.map (unitarySU 2 f K 4).subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (unitarySU 2 f K 4).subtype_injective, hFt,
      Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective (MulEquiv.injective _),
      hFcard]
  have hTcard : Nat.card (torusSU p 4 K) ≤ p ^ 3 := card_torusSU_le hp.pos 3
  have heq : Ft.map (unitarySU 2 f K 4).subtype = torusSU p 4 K :=
    Subgroup.eq_of_le_of_card_ge hFtle (by rw [hcard]; exact hTcard)
  constructor
  · exact hsub g
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.mp hg
    have : g' = g := Subtype.ext hgg
    rw [← this]
    exact hg'

end CFSG.RankThree.PartOne.KFU
