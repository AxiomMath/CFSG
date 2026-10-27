module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux5
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux9
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagCommonAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

section Det

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSDet_eq_of_induces (h : GGNSLocalHyp p B Bs K f n ψ) (hdv : 2 ^ f + 1 ∣ n)
    {b : G} {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b g₂) :
    Matrix.GeneralLinearGroup.det g₁ = Matrix.GeneralLinearGroup.det g₂ := by
  have hn0 : 0 < n := by have := h.four_le; omega
  have hz := ggNSPosPA_conj_inv_mul_of_same_action (ψ := ψ) h₁ h₂
  have hzU : ggIsUnitaryMat (p := 2) (f := f) (g₁⁻¹ * g₂) :=
    ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv h₁.1) h₂.1
  obtain ⟨c, hc⟩ := ggNSPosPA_scalar_of_conj_trivial h hzU hz
  have hdet2 : (Matrix.scalar (Fin n) c).det = c ^ n := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simp [Finset.prod_const]
  have hdetne := Matrix.GeneralLinearGroup.det_ne_zero (g₁⁻¹ * g₂)
  rw [hc, hdet2] at hdetne
  have hc0 : c ≠ 0 := fun h0 => hdetne (by rw [h0, zero_pow (by omega)])
  have hzs : g₁⁻¹ * g₂ = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) :=
    Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar]; exact hc)
  have hnorm : c ^ (2 ^ f + 1) = 1 :=
    (ggNSPosPE_scalar_isUnitary_iff hn0 (Units.mk0 c hc0)).mp (hzs ▸ hzU)
  have hcn : c ^ n = 1 := by
    obtain ⟨k, hk⟩ := hdv
    rw [hk, pow_mul, hnorm, one_pow]
  have hdz : Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hc, hdet2, hcn]
    all_goals simp
  rw [map_mul, map_inv, inv_mul_eq_one] at hdz
  exact hdz

theorem exists_ggNSDetChar (h : GGNSLocalHyp p B Bs K f n ψ) (hdv : 2 ^ f + 1 ∣ n) :
    ∃ δ : ↥Bs →* Kˣ, ∀ (b : ↥Bs) (g : GL (Fin n) K),
      GGInducesUnitary (p := 2) (f := f) ψ (b : G) g → Matrix.GeneralLinearGroup.det g = δ b := by
  classical
  choose g hg using fun b : ↥Bs => h.acts (b : G) b.2
  have key : ∀ (b : ↥Bs) (g' : GL (Fin n) K), GGInducesUnitary (p := 2) (f := f) ψ (b : G) g' →
      Matrix.GeneralLinearGroup.det g' = Matrix.GeneralLinearGroup.det (g b) :=
    fun b g' hg' => ggNSDet_eq_of_induces h hdv hg' (hg b)
  refine ⟨{ toFun := fun b => Matrix.GeneralLinearGroup.det (g b)
            map_one' := ?_
            map_mul' := ?_ }, fun b g' hg' => key b g' hg'⟩
  · have h1 : GGInducesUnitary (p := 2) (f := f) ψ ((1 : ↥Bs) : G) (1 : GL (Fin n) K) := by
      have := ggNSPosPA_induces_self (ψ := ψ) (1 : Su K 2 f n)
      simpa using this
    have := key 1 1 h1
    simpa using this.symm
  · intro b₁ b₂
    have h12 : GGInducesUnitary (p := 2) (f := f) ψ ((b₁ * b₂ : ↥Bs) : G) (g b₁ * g b₂) := by
      have := ggNSPosPA7_induces_mul (hg b₁) (hg b₂)
      simpa using this
    have := key (b₁ * b₂) (g b₁ * g b₂) h12
    rw [map_mul] at this
    exact this.symm

theorem ggNSDetChar_conj (h : GGNSLocalHyp p B Bs K f n ψ) {δ : ↥Bs →* Kˣ}
    (hδ : ∀ (b : ↥Bs) (g : GL (Fin n) K), GGInducesUnitary (p := 2) (f := f) ψ (b : G) g →
      Matrix.GeneralLinearGroup.det g = δ b)
    (b b' : ↥Bs) (s : Su K 2 f n) (hb' : (b' : G) = ψ s * (b : G) * (ψ s)⁻¹) : δ b' = δ b := by
  obtain ⟨g, hg⟩ := h.acts (b : G) b.2
  have h1 := ggNSPosPA_induces_self (ψ := ψ) s
  have h2 := ggNSPosPA_induces_self (ψ := ψ) s⁻¹
  have h3 := ggNSPosPA7_induces_mul (ggNSPosPA7_induces_mul h1 hg) h2
  rw [map_inv] at h3
  have h4 : GGInducesUnitary (p := 2) (f := f) ψ (b' : G)
      ((s : GL (Fin n) K) * g * ((s⁻¹ : Su K 2 f n) : GL (Fin n) K)) := by
    rw [hb']
    exact h3
  rw [← hδ b' _ h4, ← hδ b g hg]
  rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end Det

section Count

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

theorem ggNSDet_scalar_induces_one {c : Kˣ} (hc : (c : K) ^ (2 ^ f + 1) = 1) :
    GGInducesUnitary (p := 2) (f := f) ψ (1 : G)
      (Matrix.GeneralLinearGroup.scalar (Fin 6) c) := by
  refine ⟨(ggNSPosPE_scalar_isUnitary_iff (by norm_num) c).mpr hc, fun x => ⟨x, ?_, ?_⟩⟩
  · have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 6) c * (x : GL (Fin 6) K) =
        (x : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c :=
      Matrix.GeneralLinearGroup.scalar_commute c (x : GL (Fin 6) K)
    calc (x : GL (Fin 6) K)
        = (x : GL (Fin 6) K) * Matrix.GeneralLinearGroup.scalar (Fin 6) c *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (x : GL (Fin 6) K) *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by rw [hcomm]
  · simp

theorem ggNSDet_card_le_of_det_one (h : GGNSLocalHyp p B Bs K f 6 ψ) (hK : Nat.card K = 4)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) {δ : ↥Bs →* Kˣ}
    (hδ : ∀ (b : ↥Bs) (g : GL (Fin 6) K), GGInducesUnitary (p := 2) (f := f) ψ (b : G) g →
      Matrix.GeneralLinearGroup.det g = δ b)
    (h1 : ∀ b, δ b = 1) :
    Nat.card ↥Bs ≤ 3 ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
  classical
  have hKu : Nat.card Kˣ = 3 := by
    have h := Nat.card_units K
    rw [hK] at h
    simpa using h
  have hcube : ∀ c : Kˣ, c ^ 3 = 1 := fun c => by
    have := pow_card_eq_one' (G := Kˣ) (x := c)
    rwa [hKu] at this
  have h2f : 2 ^ f = 2 := by
    have h4 : (2 ^ f) ^ 2 = 2 ^ 2 :=
      calc (2 ^ f) ^ 2 = Nat.card K := h.card.symm
        _ = 4 := hK
        _ = 2 ^ 2 := by norm_num
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h4
  have hq : ∀ c : Kˣ, (c : K) ^ (2 ^ f + 1) = 1 := fun c => by
    rw [h2f]
    have := congrArg Units.val (hcube c)
    simpa using this
  have hnorm : ∀ b : ↥Bs, ∃ (g : GL (Fin 6) K) (d : Fin 6 → K),
      (g : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal d ∧ d 0 = 1 ∧
        Matrix.GeneralLinearGroup.det g = 1 ∧
        GGInducesUnitary (p := 2) (f := f) ψ (b : G) g := by
    intro b
    obtain ⟨g₀, ⟨d, hd0⟩, hg₀⟩ := hd (b : G) b.2
    have hdet0 : Matrix.GeneralLinearGroup.det g₀ = 1 := by
      rw [hδ b g₀ hg₀]
      exact h1 b
    have hdetK : ∏ i, d i = 1 := by
      have := congrArg Units.val hdet0
      rw [Matrix.GeneralLinearGroup.val_det_apply, hd0, Matrix.det_diagonal] at this
      simpa using this
    have hdne : ∀ i, d i ≠ 0 := fun i h0 => by
      have : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
      rw [hdetK] at this
      exact one_ne_zero this
    let c : Kˣ := (Units.mk0 (d 0) (hdne 0))⁻¹
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c * g₀, fun i => (c : K) * d i, ?_, ?_, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hd0, Matrix.scalar_apply,
        Matrix.diagonal_mul_diagonal]
    · simp [c, hdne 0]
    · rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, hdet0, mul_one, Fintype.card_fin]
      have h6 : c ^ 6 = (c ^ 3) ^ 2 := pow_mul c 3 2
      rw [h6, hcube c, one_pow]
    · have hind := ggNSPosPA7_induces_mul (ggNSDet_scalar_induces_one (ψ := ψ) (hq c)) hg₀
      simpa using hind
  choose g d hgd hd0 hdet hind using hnorm
  have hdK : ∀ b : ↥Bs, ∏ i, d b i = 1 := by
    intro b
    have := congrArg Units.val (hdet b)
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgd b, Matrix.det_diagonal] at this
    simpa using this
  have hdne : ∀ (b : ↥Bs) (i : Fin 6), d b i ≠ 0 := fun b i h0 => by
    have : ∏ i, d b i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdK b] at this
    exact one_ne_zero this
  let Θ : ↥Bs → (Fin 4 → Kˣ) := fun b j =>
    Units.mk0 (d b ⟨(j : ℕ) + 1, by omega⟩) (hdne b _)
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (ψ.range : Set G)
  have hfib : ∀ b b' : ↥Bs, Θ b = Θ b' → ((b : G)⁻¹ * (b' : G)) ∈ C := by
    intro b b' hΘ
    have hΘi : ∀ j : Fin 4, d b ⟨(j : ℕ) + 1, by omega⟩ = d b' ⟨(j : ℕ) + 1, by omega⟩ :=
      fun j => congrArg Units.val (congrFun hΘ j)
    have hd1 : d b 1 = d b' 1 := hΘi 0
    have hd2 : d b 2 = d b' 2 := hΘi 1
    have hd3 : d b 3 = d b' 3 := hΘi 2
    have hd4 : d b 4 = d b' 4 := hΘi 3
    have hd5 : d b 5 = d b' 5 := by
      have e1 := hdK b
      have e2 := hdK b'
      rw [Fin.prod_univ_six, hd0 b, one_mul] at e1
      rw [Fin.prod_univ_six, hd0 b', one_mul] at e2
      rw [← hd1, ← hd2, ← hd3, ← hd4] at e2
      have hP : d b 1 * d b 2 * d b 3 * d b 4 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (hdne b 1) (hdne b 2)) (hdne b 3)) (hdne b 4)
      exact mul_left_cancel₀ hP (e1.trans e2.symm)
    have hdeq : d b = d b' := by
      funext i
      fin_cases i
      · exact (hd0 b).trans (hd0 b').symm
      · exact hd1
      · exact hd2
      · exact hd3
      · exact hd4
      · exact hd5
    have hgeq : g b = g b' := by
      apply Units.ext
      rw [hgd b, hgd b', hdeq]
    have hb1 := hind b
    have hb2 := hind b'
    rw [← hgeq] at hb2
    refine Subgroup.mem_inf.2 ⟨(Bs.mul_mem (Bs.inv_mem b.2) b'.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro w ⟨u, rfl⟩
    obtain ⟨y, hy, hby⟩ := hb1.2 u
    obtain ⟨y', hy', hby'⟩ := hb2.2 u
    have hyy : y = y' := Subtype.ext (hy.trans hy'.symm)
    rw [hyy] at hby
    have heq : (b : G) * ψ u * (b : G)⁻¹ = (b' : G) * ψ u * (b' : G)⁻¹ := hby.trans hby'.symm
    calc ψ u * ((b : G)⁻¹ * (b' : G)) = (b : G)⁻¹ * ((b : G) * ψ u * (b : G)⁻¹) * (b' : G) := by group
      _ = (b : G)⁻¹ * ((b' : G) * ψ u * (b' : G)⁻¹) * (b' : G) := by rw [heq]
      _ = ((b : G)⁻¹ * (b' : G)) * ψ u := by group
  let rep : ↥Bs → ↥Bs := fun b => Function.invFun Θ (Θ b)
  have hrep : ∀ b, Θ (rep b) = Θ b := fun b => Function.invFun_eq ⟨b, rfl⟩
  have hrep' : ∀ b b', Θ b = Θ b' → rep b = rep b' := fun b b' hb => by
    show Function.invFun Θ (Θ b) = Function.invFun Θ (Θ b')
    rw [hb]
  let Φ : ↥Bs → (Fin 4 → Kˣ) × ↥C := fun b =>
    (Θ b, ⟨((rep b : ↥Bs) : G)⁻¹ * (b : G), hfib (rep b) b (hrep b)⟩)
  have hinj : Function.Injective Φ := by
    intro b b' hbb
    have hΘ : Θ b = Θ b' := congrArg Prod.fst hbb
    have hr : rep b = rep b' := hrep' b b' hΘ
    have h2 : ((rep b : ↥Bs) : G)⁻¹ * (b : G) = ((rep b' : ↥Bs) : G)⁻¹ * (b' : G) :=
      congrArg Subtype.val (congrArg Prod.snd hbb)
    rw [hr] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have hcard := Nat.card_le_card_of_injective Φ hinj
  have h4 : Nat.card (Fin 4) = 4 := by simp
  rw [Nat.card_prod, Nat.card_fun, hKu, h4] at hcard
  exact hcard

theorem ggNSDet_exists_ne_one (h : GGNSLocalHyp p B Bs K f 6 ψ) (hK : Nat.card K = 4)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) {δ : ↥Bs →* Kˣ}
    (hδ : ∀ (b : ↥Bs) (g : GL (Fin 6) K), GGInducesUnitary (p := 2) (f := f) ψ (b : G) g →
      Matrix.GeneralLinearGroup.det g = δ b)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ 3)
    (hBs : 3 ^ 6 ≤ Nat.card ↥Bs) : ∃ b : ↥Bs, δ b ≠ 1 := by
  by_contra hno
  push Not at hno
  have h1 := ggNSDet_card_le_of_det_one h hK hd hδ hno
  have h2 : 3 ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ 3 ^ 4 * 3 :=
    Nat.mul_le_mul_left _ hC
  have h3 : 3 ^ 6 ≤ 3 ^ 4 * 3 := hBs.trans (h1.trans h2)
  norm_num at h3

end Count

end CFSG.StandardType

end
