module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Mod

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem q16_false_of_sylow_le (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) (S : Sylow 2 G)
    (hSM : (S : Subgroup G) ≤ M) : False := by
  have hall : ∀ P : Subgroup G, IsPGroup 2 P → (Q16.sqSub P).relIndex P ≤ 32 := by
    intro P hP
    obtain ⟨S', hPS'⟩ := hP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
    have hle : P.map (MulAut.conj g).toMonoidHom ≤ M := by
      refine le_trans ?_ hSM
      rw [← hg]
      intro y hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).2 (by
        simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hPS' hp)
    have hP' : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) := hP.map _
    have h := D.q16_relindex_sqSub_le hR hQ hle hP'
    rwa [Q16.relindex_sqSub_conj] at h
  have h2 := Q16.evenRank_le_two_of_relindex_sqSub_le C.S.charTwo hall
  have h3 : CFSG.Open.evenRank G = 3 := C.S.evenRank
  omega

theorem q16_card_M (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) :
    Nat.card ↥M = 16 * Nat.card ↥C.θ.range := by
  have h1 := C.card_eq_card_inf_mul hR (le_refl M)
  rw [inf_eq_right.2 (pCoreOf_le_self M), hQ, Subgroup.subgroupOf_self,
    ← MonoidHom.range_eq_map] at h1
  exact h1

theorem sylow_of_card_of_not_dvd {H : Subgroup G} {k : ℕ} (hH : Nat.card H = 2 ^ k)
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card G) : ∃ S : Sylow 2 G, (S : Subgroup G) = H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ^ k ∣ Nat.card G := hH ▸ Subgroup.card_subgroup_dvd_card H
  have hle : k ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hG0).1 hdvd
  have hlt : ¬ k + 1 ≤ (Nat.card G).factorization 2 := fun h =>
    hk ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hG0).2 h)
  have heq : (Nat.card G).factorization 2 = k := by omega
  exact ⟨Sylow.ofCard H (by rw [hH, heq]), rfl⟩

include D in
theorem q16_false_of_not_dvd (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) (hsurj : Function.Surjective C.θ)
    (h9 : ¬ 2 ^ 9 ∣ Nat.card G) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : Nat.card ↥M = 2 ^ 8 * 45 := by
    rw [q16_card_M hR hQ, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥M))
  have hS₀ : Nat.card ↥(S₀ : Subgroup ↥M) = 2 ^ 8 := by
    rw [Sylow.card_eq_multiplicity, hM]
    congr 1
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 45 by norm_num)]
  have hS₁ : Nat.card ↥((S₀ : Subgroup ↥M).map M.subtype) = 2 ^ 8 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hS₀]
  obtain ⟨S, hS⟩ := sylow_of_card_of_not_dvd hS₁ h9
  refine D.q16_false_of_sylow_le hR hQ S ?_
  rw [hS]
  exact Subgroup.map_subtype_le _

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
