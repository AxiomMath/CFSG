module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.SplitTorusPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CoprimePSU
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitaryDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGKGPosLocalHypTw
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.KGPosSU

open CFSG.LieType.Universal CFSG.Assembly CFSG.Open CFSG.StandardType.TableCRes
  CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits

section Card

theorem card_range_le_of_isDiag {t : ℕ} {p : ℕ} (hp : 0 < p)
    (E : Subgroup ↥(Unitary.SU (PSUσ t) 6)) (hdiag : ∀ x ∈ E, (mat (PSUσ t) 6 x).IsDiag)
    (hpow : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 3 := by
  classical
  let S : Finset (PSUF t) := (Polynomial.nthRoots p (1 : PSUF t)).toFinset
  have hS : S.card ≤ p :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p (1 : PSUF t))
  have hunit : ∀ x ∈ E, ∀ s : Fin 6,
      PSUσ t (mat (PSUσ t) 6 x s s) * mat (PSUσ t) 6 x (Fin.rev s) (Fin.rev s) = 1 := by
    intro x hx s
    have hd : mat (PSUσ t) 6 x = Matrix.diagonal fun i => mat (PSUσ t) 6 x i i := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp only [Matrix.diagonal_apply_ne _ hij]
        exact hdiag x hx hij
    have hu : Unitary.conjTr (PSUσ t) (Matrix.diagonal fun i => mat (PSUσ t) 6 x i i) *
        Unitary.antidiag 6 * Matrix.diagonal (fun i => mat (PSUσ t) 6 x i i) =
          Unitary.antidiag 6 := by
      rw [← hd]
      exact x.property.2
    have hi := congrFun (congrFun hu s) (Fin.rev s)
    simpa [Unitary.conjTr, Unitary.antidiag, Matrix.diagonal, Matrix.mul_apply] using hi
  let φ : E → (Fin 3 → S) := fun x i =>
    ⟨mat (PSUσ t) 6 (x : ↥(Unitary.SU (PSUσ t) 6)) (Fin.castLE (by norm_num) i)
        (Fin.castLE (by norm_num) i), by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp]
      have h := congrArg (fun y => mat (PSUσ t) 6 y (Fin.castLE (by norm_num) i)
        (Fin.castLE (by norm_num) i)) (hpow x x.2)
      simp only [map_pow, map_one] at h
      have hd : mat (PSUσ t) 6 (x : ↥(Unitary.SU (PSUσ t) 6)) =
          Matrix.diagonal fun j => mat (PSUσ t) 6 (x : ↥(Unitary.SU (PSUσ t) 6)) j j := by
        ext a b
        by_cases hab : a = b
        · subst b
          simp
        · simp only [Matrix.diagonal_apply_ne _ hab]
          exact hdiag x x.2 hab
      rw [hd, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at h
      simpa using h⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hlow : ∀ s : Fin 6, s.val < 3 →
        mat (PSUσ t) 6 (x : ↥(Unitary.SU (PSUσ t) 6)) s s =
          mat (PSUσ t) 6 (y : ↥(Unitary.SU (PSUσ t) 6)) s s := by
      intro s hs
      have h := congrArg (fun z => ((z ⟨s.val, hs⟩ : S) : PSUF t)) hxy
      simpa [φ, Fin.castLE] using h
    have hall : ∀ s : Fin 6, mat (PSUσ t) 6 (x : ↥(Unitary.SU (PSUσ t) 6)) s s =
        mat (PSUσ t) 6 (y : ↥(Unitary.SU (PSUσ t) 6)) s s := by
      intro s
      by_cases hs : s.val < 3
      · exact hlow s hs
      · have hr : (Fin.rev s).val < 3 := by rw [Fin.val_rev]; omega
        have hx := hunit x x.2 (Fin.rev s)
        have hy := hunit y y.2 (Fin.rev s)
        rw [Fin.rev_rev] at hx hy
        rw [hlow _ hr] at hx
        exact (eq_inv_of_mul_eq_one_right hx).trans (eq_inv_of_mul_eq_one_right hy).symm
    apply Subtype.ext
    apply mat_injective
    ext i j
    by_cases hij : i = j
    · subst j
      exact hall i
    · rw [hdiag x x.2 hij, hdiag y y.2 hij]
  calc Nat.card E ≤ Nat.card (Fin 3 → S) := Nat.card_le_card_of_injective φ hφ
    _ = S.card ^ 3 := by simp [Nat.card_eq_fintype_card]
    _ ≤ p ^ 3 := Nat.pow_le_pow_left hS 3

end Card

section Lifts

theorem exists_diag_lift_SU {G : Type} [Group G] [Finite G] {p t : ℕ} {Bs X : Subgroup G}
    (ψ : ↥(Unitary.SU (PSUσ t) 6) →* G) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ (t + 1) - 1) (hker : ψ.ker ≤ Subgroup.center _) (hrange : ψ.range = X)
    (hBs : IsElemAbelian p Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF t) 6) ψ b)
    (hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs)
    (h4 : p ^ 4 ≤ Nat.card ↥Bs) :
    ∃ (g : ↥(Unitary.SU (PSUσ t) 6)) (ℓ : ↥Bs →* ↥(Unitary.SU (PSUσ t) 6)),
      (∀ (b : ↥Bs) (u : ↥(Unitary.SU (PSUσ t) 6)),
        (b : G)⁻¹ * ψ (g⁻¹ * u * g) * (b : G) = ψ (g⁻¹ * (ℓ b * u * (ℓ b)⁻¹) * g)) ∧
      ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
      (∀ b, ℓ b ^ p = 1) ∧ p ^ 3 ≤ Nat.card ℓ.range ∧
      ∀ b, (mat (PSUσ t) 6 (ℓ b)).IsDiag := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSU 6 2 (t + 1) :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  have hN' : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hN
  have hcard' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤
      Nat.card Bs := by
    rw [hrange]
    exact hcard
  have hpq' : ¬ p ∣ 2 ^ (t + 1) + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  obtain ⟨ℓ, hℓ, hkerℓ, hpowℓ, hrankℓ⟩ := exists_unitary_lift_kernel_rank
    ψ hker hadm hp hp2 Bs hBs hN' hdiag h4 hpq' hcard'
  rw [hrange] at hkerℓ
  let E : Subgroup ↥(Unitary.SU (PSUσ t) 6) := ℓ.range
  have hE : IsElemAbelian p E := by
    constructor
    · apply isMulCommutative_iff.mpr
      rintro ⟨u, hu⟩ ⟨v, hv⟩
      obtain ⟨b, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := hv
      apply Subtype.ext
      change ℓ b * ℓ c = ℓ c * ℓ b
      rw [← map_mul, ← map_mul]
      exact congrArg ℓ (isMulCommutative_iff.mp hBs.1 b c)
    · rintro u ⟨b, rfl⟩
      exact hpowℓ b
  obtain ⟨g, hg⟩ := exists_conj_isDiag_PSU (F := PSUF t) (r := 3) (card_PSUF t) (by omega)
    (by decide) hp hp2 hpq E hE hrankℓ
  let ℓ' : ↥Bs →* ↥(Unitary.SU (PSUσ t) 6) := (MulAut.conj g).toMonoidHom.comp ℓ
  have hℓ' : ∀ b, ℓ' b = g * ℓ b * g⁻¹ := fun _ => rfl
  have hkerℓ' : ℓ'.ker = ℓ.ker := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hℓ']
    constructor
    · intro h
      calc ℓ b = g⁻¹ * (g * ℓ b * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hcardr : Nat.card ℓ'.range = Nat.card ℓ.range := by
    have h : ℓ'.range = ℓ.range.map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.range_comp]
    rw [h, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  refine ⟨g, ℓ', fun b u => ?_, ?_, fun b => ?_, ?_, fun b => ?_⟩
  · rw [hℓ, hℓ']
    exact congrArg ψ (by group)
  · rw [hkerℓ']
    exact hkerℓ
  · rw [hℓ', conj_pow, hpowℓ, mul_one, mul_inv_cancel]
  · rw [hcardr]
    exact hrankℓ
  · exact hg (ℓ b) ⟨b, rfl⟩

theorem exists_conj_lift {G : Type} [Group G] {t : ℕ} {Bs : Subgroup G}
    (ψ : ↥(Unitary.SU (PSUσ t) 6) →* G) (g : ↥(Unitary.SU (PSUσ t) 6))
    (ℓ : ↥Bs →* ↥(Unitary.SU (PSUσ t) 6))
    (hℓ : ∀ (b : ↥Bs) (u : ↥(Unitary.SU (PSUσ t) 6)),
      (b : G)⁻¹ * ψ (g⁻¹ * u * g) * (b : G) = ψ (g⁻¹ * (ℓ b * u * (ℓ b)⁻¹) * g)) :
    ∃ ψ' : ↥(Unitary.SU (PSUσ t) 6) →* G, ψ' = ψ.comp (MulAut.conj g⁻¹).toMonoidHom ∧
      ψ'.ker = ψ.ker ∧ ψ'.range = ψ.range ∧
      ∀ (b : ↥Bs) (u : ↥(Unitary.SU (PSUσ t) 6)),
        (b : G)⁻¹ * ψ' u * (b : G) = ψ' (ℓ b * u * (ℓ b)⁻¹) := by
  have hψ' : ∀ u, (ψ.comp (MulAut.conj g⁻¹).toMonoidHom) u = ψ (g⁻¹ * u * g) := fun u => by
    change ψ (g⁻¹ * u * g⁻¹⁻¹) = _
    rw [inv_inv]
  refine ⟨_, rfl, ?_, ?_, fun b u => by rw [hψ', hψ']; exact hℓ b u⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ', map_mul, map_mul, map_inv]
    constructor
    · intro h
      have h' := congrArg (fun z : G => ψ g * z * (ψ g)⁻¹) h
      convert h' using 1 <;> group
    · intro h
      rw [h]
      group
  · ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨g⁻¹ * u * g, (hψ' u).symm⟩
    · rintro ⟨u, rfl⟩
      refine ⟨g * u * g⁻¹, ?_⟩
      rw [hψ']
      exact congrArg ψ (by group)

end Lifts

section Torality

theorem torus_card_of_diag_lift {G : Type} [Group G] [Finite G] {p t : ℕ} (hp : 0 < p)
    {Bs X : Subgroup G} (ψ : ↥(Unitary.SU (PSUσ t) 6) →* G)
    (ℓ : ↥Bs →* ↥(Unitary.SU (PSUσ t) 6))
    (hℓ : ∀ (b : ↥Bs) (u : ↥(Unitary.SU (PSUσ t) 6)),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hkerℓ : ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G))
    (hpowℓ : ∀ b, ℓ b ^ p = 1) (hdiagℓ : ∀ b, (mat (PSUσ t) 6 (ℓ b)).IsDiag) :
    (∀ b ∈ Bs, ∃ s ∈ ggTorus (Unitary.rootDatum (card_PSUF t) 6),
        ∀ z, b * ψ z * b⁻¹ = ψ (s * z * s⁻¹)) ∧
      Nat.card ↥Bs ≤ p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  refine ⟨fun b hb => ⟨(ℓ ⟨b, hb⟩)⁻¹, inv_mem (MpStdSU.mem_ggTorus_of_isDiag (card_PSUF t)
      (hdiagℓ ⟨b, hb⟩)), fun z => ?_⟩, ?_⟩
  · have h := hℓ ⟨b, hb⟩ ((ℓ ⟨b, hb⟩)⁻¹ * z * ℓ ⟨b, hb⟩)
    rw [show ℓ ⟨b, hb⟩ * ((ℓ ⟨b, hb⟩)⁻¹ * z * ℓ ⟨b, hb⟩) * (ℓ ⟨b, hb⟩)⁻¹ = z by group] at h
    rw [inv_inv, ← h]
    group
  · have hrange_le : Nat.card ℓ.range ≤ p ^ 3 :=
      card_range_le_of_isDiag hp ℓ.range (by rintro _ ⟨b, rfl⟩; exact hdiagℓ b)
        (by rintro _ ⟨b, rfl⟩; exact hpowℓ b)
    have hk : Nat.card ℓ.ker = Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
      rw [← hkerℓ, Subgroup.card_map_of_injective Bs.subtype_injective]
    have hmul := Subgroup.card_ker_mul_card_range ℓ
    rw [hk] at hmul
    calc Nat.card ↥Bs = Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) * Nat.card ℓ.range :=
          hmul.symm
      _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) * p ^ 3 :=
          Nat.mul_le_mul_left _ hrange_le
      _ = p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := mul_comm _ _

end Torality

end CFSG.StandardType.KGPosSU
