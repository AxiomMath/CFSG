module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPGU
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projSL)

theorem two_pow_odd_mod_three {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem isCyclic_sylow_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] {f : G →* H} (hf : Function.Surjective f) (hG : ∀ S : Sylow p G, IsCyclic S)
    (Q : Sylow p H) : IsCyclic Q := by
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  have := hG S
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem card_inf_inner_le_three {X : Type*} [Group X] [Finite X]
    (hX : ∀ S : Sylow 3 X, IsCyclic S) {D : Subgroup (MulAut X)} (hD : ∀ α ∈ D, α ^ 3 = 1)
    (hDI : D ≤ (MulAut.conj : X →* MulAut X).range) : Nat.card D ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hI : ∀ P : Sylow 3 (MulAut.conj : X →* MulAut X).range, IsCyclic P :=
    isCyclic_sylow_of_surjective (MonoidHom.rangeRestrict_surjective _) hX
  have hpg : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hD x x.2)⟩
  have : IsCyclic D := isCyclic_of_le_of_forall_sylow hI hpg hDI
  exact card_le_three_of_isCyclic hD

theorem kF82TwoPSL3Odd : KF82TwoPSL3Odd := by
  intro n hn Γ hΓ ⟨τ, hτΓ, hτ⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn0]
    exact two_pow_odd_mod_three hn
  have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 n)) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) (GaloisField 2 n) →* _)
      ProjGenLinGroup.mk_surjective
  have : Finite (MulAut (projSL 3 (GaloisField 2 n))) :=
    Finite.of_injective (fun e : MulAut (projSL 3 (GaloisField 2 n)) => (e : _ → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  have hcyc : KFacts.OutThreeCyclic (projSL 3 (GaloisField 2 n)) :=
    (KFacts.outThreeCyclic_psl3 _).of_mulEquiv (Sec4.projSLEquivProjectiveSL 3 _)
  have hk : ∀ β ∈ Γ, ∃ k < 3, τ ^ k * β ∈
      (MulAut.conj : projSL 3 (GaloisField 2 n) →* MulAut _).range := fun β hβ =>
    hcyc τ β (congrArg Subtype.val (hΓ.1.is_comm.comm ⟨τ, hτΓ⟩ ⟨β, hβ⟩)) (hΓ.2 τ hτΓ)
      (hΓ.2 β hβ) hτ
  have hle3 := KFacts.card_le_three_mul_card_inf_of_forall_pow_mul_mem hτΓ hk
  have hD := card_inf_inner_le_three (KFacts.isCyclic_sylow_three_projSL hK)
    (fun α hα => hΓ.2 α (Subgroup.mem_inf.mp hα).1) inf_le_right
  omega

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
