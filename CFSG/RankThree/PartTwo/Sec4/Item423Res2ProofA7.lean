module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv KFacts.KP2

theorem factorization_card_alt7 : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 :=
  factorization_card_alternatingGroup (m := 280) (by norm_num) (by decide) (by norm_num)

@[expose] def eNine7 : Subgroup (alternatingGroup (Fin 7)) :=
  eNine.subgroupOf (alternatingGroup (Fin 7))

theorem card_eNine7 : Nat.card eNine7 = 9 := by
  rw [← card_eNine]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv

@[expose] def r7 : alternatingGroup (Fin 7) := ⟨rFour, rFour_spec.1⟩

theorem rFour_conj_eNineF : ∀ i j : Fin 3, ∃ m n : Fin 3,
    rFour * eNineF i j * rFour⁻¹ = eNineF m n := by
  decide +kernel

theorem r7_mem_normalizer :
    r7 ∈ Subgroup.normalizer (eNine7 : Set (alternatingGroup (Fin 7))) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨i, j, hij⟩ : (x : Perm (Fin 7)) ∈ eNine := hx
  obtain ⟨m, n, hmn⟩ := rFour_conj_eNineF i j
  show ((r7 * x * r7⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ eNine
  refine ⟨m, n, ?_⟩
  change rFour * (x : Perm (Fin 7)) * rFour⁻¹ = eNineF m n
  rw [hij, hmn]

@[expose] noncomputable def rho7 : MulAut eNine7 :=
  eNine7.normalizerMonoidHom ⟨r7, r7_mem_normalizer⟩

theorem rho7_mem : rho7 ∈ autIn ⊤ eNine7 :=
  mem_autIn_iff.mpr ⟨r7, r7_mem_normalizer, Subgroup.mem_top _, rfl⟩

theorem rho7_pow_apply (k : ℕ) (x : eNine7) :
    (((rho7 ^ k) x : eNine7) : Perm (Fin 7)) = rFour ^ k * x * (rFour ^ k)⁻¹ := by
  rw [rho7, ← map_pow]
  rw [Sec4.normalizerMonoidHom_apply_coe]
  simp [r7]

theorem mem_zpowers_rho7 {σ : MulAut eNine7} (hσ : σ ∈ autIn ⊤ eNine7) :
    σ ∈ Subgroup.zpowers rho7 := by
  obtain ⟨h, hN, -, rfl⟩ := mem_autIn_iff.mp hσ
  have hNp : (h : Perm (Fin 7)) ∈ Subgroup.normalizer (eNine : Set (Perm (Fin 7))) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hyA : y ∈ alternatingGroup (Fin 7) := eNine_le_alternatingGroup hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hN ⟨y, hyA⟩).mp hy
    exact h1
  obtain ⟨k, i, j, hk⟩ := exists_rFour_pow_of_mem_normalizer hNp h.2
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℕ), ?_⟩
  rw [zpow_natCast]
  refine MulEquiv.ext fun x => Subtype.ext (Subtype.ext ?_)
  rw [rho7_pow_apply]
  change _ = (h : Perm (Fin 7)) * x * (h : Perm (Fin 7))⁻¹
  obtain ⟨a, b, hab⟩ : ((x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ eNine := x.2
  rw [hk, hab, mul_inv_rev, mul_assoc (rFour ^ (k : ℕ)) (eNineF i j), eNineF_comm i j a b]
  group

theorem rho7_pow_four : rho7 ^ 4 = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext (Subtype.ext ?_)
  rw [rho7_pow_apply, rFour_spec.2.2.2.2]
  simp

theorem rho7_sq_ne_one : rho7 ^ 2 ≠ 1 := by
  intro h
  have hc : cOne ∈ alternatingGroup (Fin 7) := eNine_le_alternatingGroup cOne_mem_eNine
  set x : eNine7 := ⟨⟨cOne, hc⟩, cOne_mem_eNine⟩
  have h1 := congrArg (fun σ : MulAut eNine7 => ((σ x : eNine7) : Perm (Fin 7))) h
  simp only [MulAut.one_apply] at h1
  rw [rho7_pow_apply, rFour_spec.2.2.2.1, tInv_conj_eq_inv cOne_mem_eNine] at h1
  have h2 : cOne⁻¹ = cOne := h1
  exact absurd h2 (by decide)

theorem orderOf_rho7 : orderOf rho7 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : rho7 ^ 2 ^ (1 + 1) = 1 := rho7_pow_four
  have h2 : ¬ rho7 ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact rho7_sq_ne_one
  exact orderOf_eq_prime_pow h2 h4

theorem autIn_eNine7_eq : autIn ⊤ eNine7 = Subgroup.zpowers rho7 :=
  le_antisymm (fun _ hσ => mem_zpowers_rho7 hσ) (Subgroup.zpowers_le.mpr rho7_mem)

noncomputable def autIn_eNine7_equiv : autIn ⊤ eNine7 ≃* Multiplicative (ZMod 4) :=
  (MulEquiv.subgroupCongr autIn_eNine7_eq).trans (mulEquivOfCyclicCardEq (by
    rw [Nat.card_zpowers, orderOf_rho7, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]))

theorem nonempty_autIn_alt7 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 7))
    {D : Subgroup X} (hD9 : Nat.card D = 9) :
    Nonempty (autIn (⊤ : Subgroup X) D ≃* Multiplicative (ZMod 4)) := by
  have hD9' : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine factorization_card_alt7 hD9' card_eNine7
  have f2 := Sporadic.autInTopCongr (MulAut.conj g) (D.map e.toMonoidHom)
  rw [show (D.map e.toMonoidHom).map (MulAut.conj g : alternatingGroup (Fin 7) ≃*
    alternatingGroup (Fin 7)).toMonoidHom = eNine7 from hg] at f2
  exact ⟨(Sporadic.autInTopCongr e D).trans (f2.trans autIn_eNine7_equiv)⟩

theorem census423_of_alt7 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 7)) :
    Census423 X := by
  intro D _ hD9 _ _ _
  exact Or.inl ⟨⟨e⟩, nonempty_autIn_alt7 e hD9⟩

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
