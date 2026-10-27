module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofSix
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.RankThreeEven (projSp projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

@[expose] def K423Inner46SixLieRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ n : ℕ, 1 ≤ n ∧
        (Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
          (Even n ∧ Nonempty (X ≃* projSU 4 2 n)))) ∨
      ∃ f : ℕ, Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
        Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨
        Blueprint.ReeTitsModel X .twistedF4 2 f) →
    IsQuasisimple X → Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

namespace Res423Four

variable {X : Type} [Group X] [Finite X]

theorem census423_of_u4_odd {n : ℕ} (hn : Odd n) (eX : X ≃* projSU 4 2 n) :
    Census423 X := by
  intro D hD hD9
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDe := hD.prop
  have hmax : ∀ x : X, x ^ 3 = 1 → (∀ y ∈ D, x * y = y * x) → x ∈ D := by
    intro x hx3 hxD
    by_contra hx
    have hsup := Sec5.isElemAbelian_sup_zpowers hDe hx hx3 (fun y hy => (hxD y hy).symm)
    exact hx (hD.2 hsup.1 le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hn1 : 1 ≤ n := hn.pos
  set F := GaloisField 2 (2 * n) with hFdef
  have hF : Nat.card F = (2 ^ n) ^ 2 := Res417Six.card_galoisField_two_mul hn1
  have hU : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hn
  have hDexp : ∀ x ∈ D, x ^ 3 = 1 := hDe.2
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eX.symm) D hDexp hDcomm
  set T : Subgroup (unitarySU 2 n F 4) := (torusSU 3 4 F).subgroupOf (unitarySU 2 n F 4)
    with hTdef
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (t : GL (Fin 4) F) ^ 3 = 1
    rw [← hd, diagU_pow, show d ^ 3 = 1 from funext hd1, diagU_one]
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (s : GL (Fin 4) F) * t = t * s
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm d d']
  have hmap : D.map (ψ.symm.trans (MulAut.conj 1)).toMonoidHom = T := by
    refine Res417Six.map_eq_of_conj_le ψ.symm hmax hTcomm hTexp fun x hx => ?_
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.mem_subgroupOf.mpr (hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hx))
  have hdvd : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 2 ^ n + 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        zify [Nat.one_le_pow 2 (2 ^ n) (by omega), hq]
        ring
      rw [this]
      exact dvd_mul_left _ _
    exact h3.trans h1
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have := hζ.dvd_of_pow_eq_one 2 h
    norm_num at this
  have hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU 3 4 F, ent x i i ≠ ent x j j :=
    fun i j hij => torusSU_char_distinct hζ3 hζ2 hij
  obtain ⟨SM⟩ := SymCtx.ofMatrixGroup (unitarySU 2 n F 4) (torusSU_le_unitarySU hU h3)
    (fun σ => permGL_mem_unitarySU hU σ) hdist
  have hcard := Res417Six.card_eq_of_map_eq _ hmap
  rw [SM.card_F (m := 3) rfl (by norm_num) ⟨ζ, hζ⟩, hD9] at hcard
  norm_num at hcard

end Res423Four

open Res423Four

theorem k423Inner46SixLie_of (h : K423Inner46SixLieRest) : K423Inner46SixLie := by
  intro X _ _ hX hq hZ hSL
  rcases hX with ⟨n, hn, hSp | ⟨⟨eU⟩⟩⟩ | hX
  · exact h X (Or.inl ⟨n, hn, Or.inl hSp⟩) hq hZ hSL
  · rcases Nat.even_or_odd n with hev | hodd
    · exact h X (Or.inl ⟨n, hn, Or.inr ⟨hev, ⟨eU⟩⟩⟩) hq hZ hSL
    · exact census423_of_u4_odd hodd eU
  · exact h X (Or.inr hX) hq hZ hSL

end CFSG.RankThree.PartTwo.Sec4
