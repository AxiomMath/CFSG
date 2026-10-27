module

public import CFSG.RankThree.PartOne.SLB4B.ModelL
public import CFSG.RankThree.PartOne.SRC.CentralizerGen
public import CFSG.RankThree.PartOne.SRC.ModelL4
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
public import CFSG.LieType.Steinberg.CentralExt.SLThree

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix Subgroup CFSG CFSG.RankThree.PartOne.SRC CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups

section PSL

variable {F : Type*} [Field F] {m : ℕ}

@[expose] noncomputable def psl4Emb : SpecialLinearGroup (Fin 4) F →* PSL(4 + m, F) :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (4 + m)) F))).comp blockHom

theorem psl4Emb_injective (hm : 1 ≤ m) : Function.Injective (psl4Emb (F := F) (m := m)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [psl4Emb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hA
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hA
    (Fin.natAdd 4 (⟨0, hm⟩ : Fin m))
  have h1 : ((blockHom (m := m) A : SpecialLinearGroup (Fin (4 + m)) F) :
      Matrix (Fin (4 + m)) (Fin (4 + m)) F) (Fin.natAdd 4 (⟨0, hm⟩ : Fin m))
        (Fin.natAdd 4 (⟨0, hm⟩ : Fin m)) = 1 := by
    rw [coe_blockHom, blockMat_inr_inr]
    simp
  rw [h1] at hs
  have hA1 : (blockHom (m := m) A : SpecialLinearGroup (Fin (4 + m)) F) = 1 :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one, ← hs, map_one])
  exact blockHom_injective (hA1.trans (map_one blockHom).symm)

@[expose] noncomputable def pslSign : PSL(4 + m, F) :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (4 + m)) F)) signSL

theorem psl4Emb_comm (A : SpecialLinearGroup (Fin 4) F) :
    psl4Emb (m := m) A * pslSign = pslSign * psl4Emb A := by
  rw [psl4Emb, pslSign, MonoidHom.comp_apply, ← map_mul, ← map_mul, blockHom_comm_signSL]

theorem orderOf_pslSign (hm : 1 ≤ m) (h : (-1 : F) ≠ 1) :
    orderOf (pslSign (F := F) (m := m)) = 2 := by
  have h2 : (pslSign (F := F) (m := m)) ^ 2 = 1 := by
    rw [pslSign, ← map_pow, signSL_sq, map_one]
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [pslSign, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact signSL_not_mem_center hm h h1

end PSL

section Cover

variable {F : Type} [Field F] [Finite F]

theorem pow_eq_one_of_mem_center {n : ℕ} [NeZero n] {z : SpecialLinearGroup (Fin n) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) : z ^ n = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow]
  rw [Fintype.card_fin] at hr
  rw [hr, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem coprime_card_center_SL {p n : ℕ} [NeZero n] (hp : p.Prime) (hpn : ¬ p ∣ n) :
    Nat.Coprime p (Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F))) := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center (SpecialLinearGroup (Fin n) F)) p hdvd
  have h1 : (x : SpecialLinearGroup (Fin n) F) ^ n = 1 := pow_eq_one_of_mem_center x.2
  have h2 : orderOf x ∣ n := by
    refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
    simpa using h1
  rw [hx] at h2
  exact hpn h2

theorem invol4_not_mem_center (h : (-1 : F) ≠ 1) :
    (invol4 : SpecialLinearGroup (Fin 4) F) ∉ Subgroup.center (SpecialLinearGroup (Fin 4) F) := by
  intro hc
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc (0 : Fin 4)
  have e2 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 2) hs
  simp [coe_invol4, Matrix.scalar_apply] at e2
  exact h e2

theorem sl4_exists_section_of_central {p e : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ e)
    (hp2 : p ≠ 2) {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin 4) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin 4) F →* E, ∀ g, π (σ g) = g := by
  have hp : p.Prime := Fact.out
  by_cases h5 : 5 ≤ Nat.card F
  · exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (m := 3)
      (by norm_num) h5 hπ hcen
  · have hodd : Odd (Nat.card F) := hF ▸ (hp.eq_two_or_odd'.resolve_left hp2).pow
    have h3 : 3 ≤ Nat.card F := by
      have he : e ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hF
        have : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
        omega
      rw [hF]
      calc 3 ≤ p := by have := hp.two_le; omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero he)
    have hF3 : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_card_three (m := 3)
      (by norm_num) hF3 hπ hcen

theorem cover_sl4 {p e : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2)
    (W : Type) [Group W] [Finite W] (ρ : W →* SpecialLinearGroup (Fin 4) F)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have hp : p.Prime := Fact.out
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq F p]; exact hp2)
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, pow_zero] at hF
      have : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact h0
  have hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 4) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 4 F (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hp4 : ¬ p ∣ 4 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hd)))
  have hZ : Nat.Coprime p (Nat.card (Subgroup.center (SpecialLinearGroup (Fin 4) F))) :=
    coprime_card_center_SL hp hp4
  have hhc : (invol4 : SpecialLinearGroup (Fin 4) F) ∉
      Subgroup.center (SpecialLinearGroup (Fin 4) F) := invol4_not_mem_center hneg
  have hho : Nat.Coprime (orderOf (invol4 : SpecialLinearGroup (Fin 4) F)) p := by
    have hdvd : orderOf (invol4 : SpecialLinearGroup (Fin 4) F) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one invol4_sq
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hclosed : ∀ (W : Type) [Group W] [Finite W] (π : W →* SpecialLinearGroup (Fin 4) F),
      Function.Surjective π → π.ker ≤ Subgroup.center W → IsPGroup p π.ker →
        ∃ s : SpecialLinearGroup (Fin 4) F →* W, ∀ g, π (s g) = g :=
    fun W _ _ π hπ hcen _ => sl4_exists_section_of_central hF hp2 hπ hcen
  set φ := lowBlockSL 4 F p
  have hφ : Function.Injective φ :=
    unipotentSL_injective _ _ (lowBlockMap_injective (by norm_num))
  have hW : ∀ w : Fin 2 × Fin 2 → F, p • w = 0 := fun w => by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p,
      zero_smul]
  have hpow : ∀ a : Multiplicative (Fin 2 × Fin 2 → F), a ^ p = 1 := fun a =>
    Multiplicative.toAdd.injective (by rw [toAdd_pow, toAdd_one]; exact hW _)
  have hEA : IsElementaryAbelian p φ.range :=
    CFSG.RankThree.PartOne.SRC.isElementaryAbelian_range φ hpow
  have hcard : Nat.card φ.range = p ^ (4 * e) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, hF, Nat.card_prod, Nat.card_fin, ← pow_mul, mul_comm]
  exact rank_four_of_cover_quasisimple hp2 hQ hZ _ hhc hho hclosed hEA (k := 4 * e)
    (by omega) hcard ρ hρ hker

theorem rankFourCover_psl {p e : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ e)
    (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n) :
    RankFourCover p (ProjectiveSpecialLinearGroup (Fin n) F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  have hm : 1 ≤ m := by omega
  have hp : p.Prime := Fact.out
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq F p]; exact hp2)
  exact rankFourCover_of_cover_ker hp hp2 (fun W _ _ ρ hρ hker => cover_sl4 hF hp2 W ρ hρ hker)
    (psl4Emb (m := m)) (fun A hA => by rw [psl4Emb_injective hm (hA.trans (map_one _).symm), one_pow])
    (orderOf_pslSign hm hneg) psl4Emb_comm

end Cover

end CFSG.RankThree.PartOne.SLB4B
