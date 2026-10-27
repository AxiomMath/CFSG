module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped MatrixGroups

theorem card_centralizer_of_isReeType_one {L : Type} [Group L] [Finite L]
    (h : F07.IsReeType L 1) {t : L} (ht : orderOf t = 2)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 3)
    (e : ↥(Subgroup.centralizer ({t} : Set L)) ≃*
      (Multiplicative (ZMod 2) × PSL(2, F))) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set L)) = 24 := by
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [hF, ZMod.card]
  let φ : PSL(2, F) ≃* PSL(2, ZMod 3) :=
    CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)
  have hpsl : Nat.card (PSL(2, F)) = 12 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.GorensteinWalter.nat_card_psl2_zmod3]
  have hmult : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod]
  calc
    Nat.card ↥(Subgroup.centralizer ({t} : Set L))
        = Nat.card (Multiplicative (ZMod 2) × PSL(2, F)) := Nat.card_congr e.toEquiv
    _ = Nat.card (Multiplicative (ZMod 2)) * Nat.card (PSL(2, F)) := Nat.card_prod _ _
    _ = 2 * 12 := by rw [hmult, hpsl]
    _ = 24 := by norm_num

theorem card_sylow_two_of_isReeType_one {L : Type} [Group L] [Finite L]
    (h : F07.IsReeType L 1) (S : Sylow 2 L) : Nat.card (S : Subgroup L) = 8 := by
  have hcomm : ∀ S : Sylow 2 L, IsMulCommutative (S : Subgroup L) := h.2.1
  obtain ⟨t, ht, F, hField, hFintype, hFcard, hcent⟩ := h.2.2
  letI : Field F := hField
  letI : Fintype F := hFintype
  have hF : Fintype.card F = 3 := by simpa using hFcard
  obtain ⟨e⟩ := hcent
  have hC : Nat.card ↥(Subgroup.centralizer ({t} : Set L)) = 24 :=
    card_centralizer_of_isReeType_one h ht F hF e
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzpow : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨S', hzS'⟩ := IsPGroup.exists_le_sylow hzpow
  have htS' : t ∈ (S' : Subgroup L) := hzS' (Subgroup.mem_zpowers t)
  have hS'C : (S' : Subgroup L) ≤ Subgroup.centralizer ({t} : Set L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((hcomm S').is_comm.comm ⟨x, hx⟩ ⟨t, htS'⟩)
  have hdvdC : Nat.card (S' : Subgroup L) ∣ 24 := by
    rw [← hC]
    exact Subgroup.card_dvd_of_le hS'C
  have h24dvdL : 24 ∣ Nat.card L := by
    simpa [hC] using
      Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({t} : Set L))
  have h8dvdS' : 2 ^ 3 ∣ Nat.card (S' : Subgroup L) :=
    Sylow.pow_dvd_card_of_pow_dvd_card S'
      ((by norm_num : (2 : ℕ) ^ 3 ∣ 24).trans h24dvdL)
  let f := Nat.factorization (Nat.card L) 2
  have hS'card : Nat.card (S' : Subgroup L) = 2 ^ f := Sylow.card_eq_multiplicity S'
  have h24fac : (24 : ℕ).factorization 2 = 3 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  have hf_le : f ≤ 3 := by
    have hdvd : 2 ^ f ∣ 24 := by simpa [hS'card] using hdvdC
    have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (by norm_num : (24 : ℕ) ≠ 0)).mp hdvd
    rw [h24fac] at h
    exact h
  have hle_f : 3 ≤ f := by
    have hdvd : 2 ^ 3 ∣ 2 ^ f := by simpa [hS'card] using h8dvdS'
    have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (pow_ne_zero f (by norm_num : (2 : ℕ) ≠ 0))).mp hdvd
    simpa only [Nat.factorization_pow_self Nat.prime_two] using h
  have hf : f = 3 := le_antisymm hf_le hle_f
  calc
    Nat.card (S : Subgroup L) = 2 ^ f := Sylow.card_eq_multiplicity S
    _ = 2 ^ 3 := by rw [hf]
    _ = 8 := by norm_num

theorem isMulCommutative_sylow_two_of_le {X : Type} [Group X] [Finite X]
    {K L : Subgroup X}
    (hKL : K ≤ L) (hLab : ∀ S : Sylow 2 ↥L, IsMulCommutative (S : Subgroup ↥L))
    (S : Sylow 2 ↥K) : IsMulCommutative (S : Subgroup ↥K) := by
  have hSmap : IsPGroup 2 ((S : Subgroup ↥K).map (Subgroup.inclusion hKL)) :=
    S.isPGroup'.map (Subgroup.inclusion hKL)
  obtain ⟨SL, hle⟩ := hSmap.exists_le_sylow
  haveI : IsMulCommutative (SL : Subgroup ↥L) := hLab SL
  refine IsMulCommutative.of_comm fun x y => ?_
  apply Subtype.ext
  apply Subgroup.inclusion_injective hKL
  have hx : Subgroup.inclusion hKL (x : ↥K) ∈ (SL : Subgroup ↥L) :=
    hle ⟨(x : ↥K), x.2, rfl⟩
  have hy : Subgroup.inclusion hKL (y : ↥K) ∈ (SL : Subgroup ↥L) :=
    hle ⟨(y : ↥K), y.2, rfl⟩
  have hcomm :
      (⟨Subgroup.inclusion hKL (x : ↥K), hx⟩ : ↥SL) *
          ⟨Subgroup.inclusion hKL (y : ↥K), hy⟩ =
        ⟨Subgroup.inclusion hKL (y : ↥K), hy⟩ *
          ⟨Subgroup.inclusion hKL (x : ↥K), hx⟩ :=
    mul_comm' _ _
  simpa [map_mul] using congrArg Subtype.val hcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
