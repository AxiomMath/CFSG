module

public import CFSG.RankThree.PartOne.KSP6.Struct

public section

namespace CFSG.RankThree.PartOne.KSP6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom torus
  torusHom_injective)

section Conj

variable {K : Type} [Field K]

theorem mat_torusHom (τ : Fin 3 → Kˣ) :
    mat (torusHom τ) = fromBlocks (diagonal fun i => (τ i : K)) 0 0
      (diagonal fun i => (((τ i)⁻¹ : Kˣ) : K)) := by
  rw [mat, coe_torusHom, ← fromBlocks_diagonal]

theorem diagonal_mul_diagonal_inv (τ : Fin 3 → Kˣ) :
    (diagonal fun i => (τ i : K)) * (diagonal fun i => (((τ i)⁻¹ : Kˣ) : K)) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact Units.mul_inv _

theorem diagonal_inv_mul_diagonal (τ : Fin 3 → Kˣ) :
    (diagonal fun i => (((τ i)⁻¹ : Kˣ) : K)) * (diagonal fun i => (τ i : K)) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact Units.inv_mul _

theorem mat_torus_conj_siegel (τ : Fin 3 → Kˣ) {v : StatedSp 3 K} {B : Matrix (Fin 3) (Fin 3) K}
    (hv : mat v = fromBlocks 1 B 0 1) :
    mat (torusHom τ * v * (torusHom τ)⁻¹) =
      fromBlocks 1 ((diagonal fun i => (τ i : K)) * B * (diagonal fun i => (τ i : K))) 0 1 := by
  rw [← map_inv, mat_mul, mat_mul, hv, mat_torusHom, mat_torusHom, fromBlocks_multiply,
    fromBlocks_multiply]
  have h1 := diagonal_mul_diagonal_inv τ
  have h2 := diagonal_inv_mul_diagonal τ
  simp only [Pi.inv_apply, inv_inv, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]
  rw [Matrix.mul_assoc _ _ (diagonal fun i => (τ i : K)), h1, h2]

theorem torus_conj_mem_siegel {t v : StatedSp 3 K} (ht : t ∈ torus 3 K)
    (hv : v ∈ siegelRadicalSp 3 K) : t * v * t⁻¹ ∈ siegelRadicalSp 3 K := by
  obtain ⟨τ, rfl⟩ := ht
  obtain ⟨B, hB, hvB⟩ := mem_siegelRadicalSp.1 hv
  have hvB' : mat v = fromBlocks 1 B 0 1 := hvB
  refine mem_siegelRadicalSp.2 ⟨_, ?_, mat_torus_conj_siegel τ hvB'⟩
  rw [transpose_mul, transpose_mul, diagonal_transpose, hB, Matrix.mul_assoc]

theorem torusHom_comm_longRoot {τ : Fin 3 → Kˣ} (hτ : τ 0 = 1) {x : StatedSp 3 K}
    (hx : x ∈ longRoot K) : torusHom τ * x = x * torusHom τ := by
  obtain ⟨a, hxa⟩ := mem_longRoot.1 hx
  have h := mat_torus_conj_siegel τ hxa
  have hD : (diagonal fun i => (τ i : K)) * Matrix.single (0 : Fin 3) (0 : Fin 3) a *
      (diagonal fun i => (τ i : K)) = Matrix.single 0 0 a := by
    ext i j
    rw [mul_single_mul_apply]
    fin_cases i <;> fin_cases j <;> simp [hτ]
  rw [hD, ← hxa] at h
  have h' : torusHom τ * x * (torusHom τ)⁻¹ = x := mat_inj h
  calc torusHom τ * x = torusHom τ * x * (torusHom τ)⁻¹ * torusHom τ := by group
    _ = x * torusHom τ := by rw [h']

end Conj

section Sylow

variable {K : Type} [Field K] [Finite K]

theorem prod_Icc_three (q : ℕ) :
    ∏ j ∈ Finset.Icc 1 3, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) := by
  rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide]
  simp [Finset.prod_insert, mul_assoc]

theorem card_S_formula (d : ℕ) :
    (d + 1) ^ (3 ^ 2) * ((((d + 1) ^ 2 - 1) * ((d + 1) ^ 4 - 1) * ((d + 1) ^ 6 - 1))) =
      d ^ 3 * ((d + 1) ^ 9 * ((d + 2) ^ 2 * (((d + 1) ^ 2 + 1) *
        (1 + (d + 1) + (d + 1) ^ 2 + (d + 1) ^ 3 + (d + 1) ^ 4 + (d + 1) ^ 5)))) := by
  have h2 : (d + 1) ^ 2 - 1 = d * (d + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h4 : (d + 1) ^ 4 - 1 = d * (d + 2) * ((d + 1) ^ 2 + 1) := Nat.sub_eq_of_eq_add (by ring)
  have h6 : (d + 1) ^ 6 - 1 = d * (1 + (d + 1) + (d + 1) ^ 2 + (d + 1) ^ 3 + (d + 1) ^ 4 +
      (d + 1) ^ 5) := Nat.sub_eq_of_eq_add (by ring)
  rw [h2, h4, h6]
  ring

omit [Finite K] in
theorem card_torus : Nat.card ↥(torus 3 K) = (Nat.card K - 1) ^ 3 := by
  have h : Nat.card ↥(torus 3 K) = Nat.card (Fin 3 → Kˣ) :=
    (Nat.card_congr (MonoidHom.ofInjective (torusHom_injective (r := 3) (k := K))).toEquiv).symm
  rw [h, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]

theorem exists_conj_torus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    {A : Subgroup (StatedSp 3 K)} (hA : IsPGroup p A) :
    ∃ s : StatedSp 3 K, ∀ a ∈ A, s⁻¹ * a * s ∈ torus 3 K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨d, hd⟩ : ∃ d, Nat.card K = d + 1 := ⟨Nat.card K - 1, by omega⟩
  have hdq : Nat.card K - 1 = d := by omega
  rw [hdq] at hpq
  set M : ℕ := (d + 1) ^ 9 * ((d + 2) ^ 2 * (((d + 1) ^ 2 + 1) *
        (1 + (d + 1) + (d + 1) ^ 2 + (d + 1) ^ 3 + (d + 1) ^ 4 + (d + 1) ^ 5))) with hM
  have hS : Nat.card (StatedSp 3 K) = d ^ 3 * M := by
    rw [SymplecticFlag.card_statedSp, prod_Icc_three, hd]
    exact card_S_formula d
  have hT : Nat.card ↥(torus 3 K) = d ^ 3 := by rw [card_torus, hdq]
  have hpM : ¬ p ∣ M := by
    intro h
    have h0 : ((M : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff M p).2 h
    have hd0 : ((d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).2 hpq
    have h48 : ((M : ℕ) : ZMod p) = 48 := by
      rw [hM]
      push_cast
      rw [hd0]
      norm_num
    rw [h48] at h0
    have h1 : p ∣ 48 := (ZMod.natCast_eq_zero_iff 48 p).1 (by exact_mod_cast h0)
    have h48' : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [h48'] at h1
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have h3 := hp.dvd_of_dvd_pow h2
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
  obtain ⟨P⟩ : Nonempty (Sylow p ↥(torus 3 K)) := inferInstance
  set P₁ : Subgroup (StatedSp 3 K) := (P : Subgroup ↥(torus 3 K)).map (torus 3 K).subtype with hP₁
  have hP₁p : IsPGroup p P₁ := P.isPGroup'.map _
  have hindex : P₁.index = (P : Subgroup ↥(torus 3 K)).index * M := by
    have h1 : Nat.card P₁ = Nat.card P :=
      Subgroup.card_map_of_injective (torus 3 K).subtype_injective
    have h2 := P₁.card_mul_index
    have h3 := (P : Subgroup ↥(torus 3 K)).card_mul_index
    rw [hS] at h2
    rw [hT] at h3
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card P₁)
    rw [h2]
    calc d ^ 3 * M = (Nat.card P * (P : Subgroup ↥(torus 3 K)).index) * M := by rw [h3]
      _ = Nat.card P₁ * ((P : Subgroup ↥(torus 3 K)).index * M) := by rw [h1]; ring
  have hnd : ¬ p ∣ P₁.index := by
    rw [hindex]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact P.not_dvd_index h1
    · exact hpM h1
  let Q₁ : Sylow p (StatedSp 3 K) := hP₁p.toSylow hnd
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 3 K) Q₁ Q
  refine ⟨g, fun a ha => ?_⟩
  have haQ : a ∈ (Q : Subgroup (StatedSp 3 K)) := hAQ ha
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at haQ
  obtain ⟨b, hb, hba⟩ := haQ
  have hb' : b ∈ P₁ := hb
  obtain ⟨t, htP, rfl⟩ := hb'
  have : g⁻¹ * a * g = t := by
    rw [← hba]
    simp
    group
  rw [this]
  exact t.2

end Sylow

section Chi

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def chi1 (K : Type) [Field K] :
    ↥(torusHom (r := 3) (k := K)).range →* Kˣ :=
  (Pi.evalMonoidHom (fun _ : Fin 3 => Kˣ) 0).comp
    (MonoidHom.ofInjective (torusHom_injective (r := 3) (k := K))).symm.toMonoidHom

omit [Finite K] in
theorem chi1_torusHom (τ : Fin 3 → Kˣ) :
    chi1 K ⟨torusHom τ, SymplecticTorusWeyl.torusHom_mem_torus τ⟩ = τ 0 := by
  have : (⟨torusHom τ, SymplecticTorusWeyl.torusHom_mem_torus τ⟩ :
      ↥(torusHom (r := 3) (k := K)).range) =
      MonoidHom.ofInjective (torusHom_injective (r := 3) (k := K)) τ := rfl
  rw [chi1, MonoidHom.comp_apply, this]
  simp

theorem exists_index_le_torus {p : ℕ} (hp : 0 < p) {A : Subgroup (StatedSp 3 K)}
    (hA : ∀ a ∈ A, a ^ p = 1) (s : StatedSp 3 K) (hs : ∀ a ∈ A, s⁻¹ * a * s ∈ torus 3 K) :
    ∃ B ≤ A, Nat.card A ≤ p * Nat.card B ∧
      ∀ b ∈ B, ∃ τ : Fin 3 → Kˣ, τ 0 = 1 ∧ s⁻¹ * b * s = torusHom τ := by
  classical
  have := Fintype.ofFinite K
  let cs : ↥A →* ↥(torusHom (r := 3) (k := K)).range :=
    ((MulAut.conj s⁻¹).toMonoidHom.comp A.subtype).codRestrict (torusHom (r := 3) (k := K)).range
      (fun a => by
        have h1 : ((MulAut.conj s⁻¹).toMonoidHom.comp A.subtype) a =
            s⁻¹ * (a : StatedSp 3 K) * s := by
          simp
        rw [h1]
        exact hs a a.2)
  let ε : ↥A →* Kˣ := (chi1 K).comp cs
  refine ⟨ε.ker.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 : Nat.card (ε.ker.map A.subtype) = Nat.card ε.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 := ε.ker.card_mul_index
    rw [Subgroup.index_ker] at h2
    have h3 : Nat.card ε.range ≤ p := by
      have hpow : ∀ u : ↥ε.range, (u.1 : Kˣ) ^ p = 1 := by
        rintro ⟨_, a, rfl⟩
        rw [← map_pow]
        have : (a ^ p : ↥A) = 1 := Subtype.ext (hA a a.2)
        rw [this, map_one]
      calc Nat.card ε.range ≤ Nat.card {x : Kˣ // x ^ p = 1} :=
            Nat.card_le_card_of_injective (fun u => ⟨u.1, hpow u⟩) (fun u w h =>
              Subtype.ext (by have := congrArg Subtype.val h; exact this))
        _ = (Finset.univ.filter fun x : Kˣ => x ^ p = 1).card := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ p := IsCyclic.card_pow_eq_one_le hp
    rw [h1, ← h2]
    calc Nat.card ε.ker * Nat.card ε.range ≤ Nat.card ε.ker * p := Nat.mul_le_mul_left _ h3
      _ = p * Nat.card ε.ker := mul_comm _ _
  · rintro _ ⟨a, ha, rfl⟩
    have hcs : (cs a : StatedSp 3 K) = s⁻¹ * (a : StatedSp 3 K) * s := by
      simp [cs]
    obtain ⟨τ, hτ⟩ := (cs a).2
    refine ⟨τ, ?_, ?_⟩
    · have h1 : ε a = 1 := ha
      have h2 : chi1 K (cs a) = τ 0 := by
        have : cs a = ⟨torusHom τ, SymplecticTorusWeyl.torusHom_mem_torus τ⟩ := Subtype.ext hτ.symm
        rw [this, chi1_torusHom]
      exact h2.symm.trans h1
    · show s⁻¹ * (a : StatedSp 3 K) * s = torusHom τ
      rw [← hcs, hτ]

end Chi

end CFSG.RankThree.PartOne.KSP6
