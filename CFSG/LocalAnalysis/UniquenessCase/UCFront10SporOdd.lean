module

import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem card_dvd_card_GL_of_inf_centralizer_eq_bot {T A : Subgroup X} {z : X} {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hT : IsPGroup 2 T) (hzT : z ∈ T) (hzz : z * z = 1)
    (hZ : ∀ t ∈ T, (∀ s ∈ T, s * t = t * s) → t = 1 ∨ t = z)
    (hA : CFSG.Open.IsElemAbelian p A) (hAn : Nat.card A = p ^ n) (hA1 : A ≠ ⊥)
    (hTA : T ≤ normalizer (A : Set X)) (hAz : A ⊓ centralizer {z} = ⊥) :
    Nat.card T ∣ Nat.card (GL (Fin n) (ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian p ↥A := hA.isElementaryAbelian
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, Commute a b := fun a ha b hb => by
    have h := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  have hnormA : ∀ g ∈ T, ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.1 (hTA hg) a).1 ha
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hinv : ∀ a ∈ A, z * a * z⁻¹ = a⁻¹ := by
    intro a ha
    have hw : z * a * z⁻¹ ∈ A := hnormA _ hzT a ha
    have hb : a * (z * a * z⁻¹) ∈ A ⊓ centralizer {z} := by
      refine Subgroup.mem_inf.2 ⟨A.mul_mem ha hw, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := (hAcomm a ha _ hw).eq
      rw [hzinv] at hc ⊢
      calc a * (z * a * z) * z = z * a * z * a * z := by rw [hc]
        _ = z * (a * (z * a * z)) := by group
    rw [hAz] at hb
    exact eq_inv_of_mul_eq_one_right (Subgroup.mem_bot.1 hb)
  have hfaith : ∀ g ∈ T, (∀ x ∈ A, g * x * g⁻¹ = x) → g = 1 := by
    intro g hg hgA
    by_contra hg1
    obtain ⟨K, hKdef⟩ : ∃ K : Subgroup ↥T, K = (centralizer (A : Set X)).subgroupOf T :=
      ⟨_, rfl⟩
    have hKn : K.Normal := by
      constructor
      intro k hk s
      rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hk ⊢
      intro a ha
      have ha' : (s : X)⁻¹ * a * (s : X) ∈ A := by
        have h := hnormA _ (T.inv_mem s.2) a ha
        rwa [inv_inv] at h
      have hka := hk _ ha'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      calc a * ((s : X) * (k : X) * (s : X)⁻¹)
          = (s : X) * (((s : X)⁻¹ * a * (s : X)) * (k : X)) * (s : X)⁻¹ := by group
        _ = (s : X) * ((k : X) * ((s : X)⁻¹ * a * (s : X))) * (s : X)⁻¹ := by rw [hka]
        _ = ((s : X) * (k : X) * (s : X)⁻¹) * a := by group
    have hK1 : K ≠ ⊥ := by
      intro h
      have hgK : (⟨g, hg⟩ : ↥T) ∈ K := by
        rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro a ha
        exact (mul_inv_eq_iff_eq_mul.1 (hgA a ha)).symm
      rw [h] at hgK
      exact hg1 ((Subgroup.mk_eq_one _).1 (Subgroup.mem_bot.1 hgK))
    have : Group.IsNilpotent ↥T := hT.isNilpotent
    obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hK1)
    obtain ⟨hwK, hwZ⟩ := Subgroup.mem_inf.1 hw
    have hwz : (w : X) = z := by
      refine (hZ (w : X) w.2 fun s hs => ?_).resolve_left fun h => hw1 (Subtype.ext h)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hwZ ⟨s, hs⟩)
    rw [hKdef, Subgroup.mem_subgroupOf, hwz] at hwK
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hza : a * z = z * a := (Subgroup.mem_centralizer_iff.1 hwK) a ha
    have h1 : a⁻¹ = a := by rw [← hinv a ha, ← hza, mul_inv_cancel_right]
    have ha2 : a ^ 2 = 1 := by
      calc a ^ 2 = a⁻¹ * a := by rw [h1, pow_two]
        _ = 1 := inv_mul_cancel a
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one (hA.2 a ha)))
  exact CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.card_dvd_card_GL_of_faithful hp (P := A) (E := T)
    hAn hnormA hfaith

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
