module

public import CFSG.Quasithin.EmptyFaithful.S153NMl2Frat
import CFSG.Quasithin.EmptyFaithful.S153NMl2Card
import CFSG.Quasithin.EmptyFaithful.S1565M3

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

private theorem sylow_of_isSylowTwoOf {J S : Subgroup (MulAut W)} (hS : IsSylowTwoOf S J) :
    ∃ P : Sylow 2 ↥J, (P : Subgroup ↥J) = S.subgroupOf J := by
  obtain ⟨hSJ, hp, hidx⟩ := hS
  have hp' : IsPGroup 2 ↥(S.subgroupOf J) :=
    hp.of_injective (Subgroup.subgroupOfEquivOfLe hSJ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSJ).injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hp'.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

private theorem mem_normalizer_of_subgroupOf {J S : Subgroup (MulAut W)} (hSJ : S ≤ J) {b : ↥J}
    (hb : b ∈ Subgroup.normalizer ((S.subgroupOf J : Subgroup ↥J) : Set ↥J)) :
    (b : MulAut W) ∈ Subgroup.normalizer (S : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff] at hb ⊢
  intro x
  constructor
  · intro hx
    have h1 := (hb ⟨x, hSJ hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hx
    have hxJ : x ∈ J := by
      have h1 := J.mul_mem (J.mul_mem (J.inv_mem b.2) (hSJ hx)) b.2
      simpa [mul_assoc] using h1
    exact Subgroup.mem_subgroupOf.1 ((hb ⟨x, hxJ⟩).2 (Subgroup.mem_subgroupOf.2 hx))

variable [Finite W]

theorem false_of_natural_sl2 (hW : ∀ v : W, v ^ 2 = 1) {Γ J : Subgroup (MulAut W)} {w : W}
    {𝒪 : Set (Subgroup (MulAut W))} (hD : Insp67Data Γ w 𝒪) (hJ : J = ffJ Γ) (hJne : J ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hnat : BinaryNaturalSL J ⊤ (fixV J) 2 n) : False := by
  subst hJ
  have hns : ¬ IsStrongFFModule (ffJ Γ) := not_isStrongFFModule_of_natural_sl2 hnat
  obtain ⟨-, S, hS, hN⟩ := frattini_ffJ_of_not_strong hW hD hns
  obtain ⟨P, hP⟩ := sylow_of_isSylowTwoOf hS
  have hnat' : BinaryNaturalSL (ffJ Γ) ⊤ (⊤ ⊓ fixV (ffJ Γ)) 2 n := by
    rwa [top_inf_eq]
  obtain ⟨b, hbN, -, -, -, hreg⟩ := natfree_sl2_of_two_le hn hnat' P
  rw [hP] at hbN
  have hbN' : (b : MulAut W) ∈ Subgroup.normalizer (S : Set (MulAut W)) :=
    mem_normalizer_of_subgroupOf hS.1 hbN
  have hbstab : (b : MulAut W) ∈ stabAt Γ w := hN ⟨hbN', b.2⟩
  have hbw : (b : MulAut W) w = w := hbstab.2
  have hw : w ∈ (⊤ : Subgroup W) ⊓ fixV (ffJ Γ) :=
    hreg w trivial (by rw [hbw, mul_inv_cancel]; exact one_mem _)
  exact not_mem_fixV_of_gen hD.gen (B6.ffJ_le Γ) (ffJ_subgroupOf_normal Γ) hJne hw.2

end CFSG.Quasithin.S153N
