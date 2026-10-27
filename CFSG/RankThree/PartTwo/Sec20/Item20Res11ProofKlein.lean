module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res11

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.BenderSuzuki.PFchapter1section1 (TwoRankAtLeastTwo)

theorem exists_klein_of_surjective {Y H : Type*} [Group Y] [Finite Y] [Group H]
    (π : Y →* H) (hπ : Function.Surjective π) (U : Subgroup H) [Finite U]
    (hUexp : ∀ x : U, x * x = 1) (hU : 4 < Nat.card U) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_cases hY : TwoRankAtLeastTwo Y
  · exact Sec11.LSSolvableProof.exists_klein_of_twoRank hY
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 U := fun x => ⟨1, by rw [pow_one, sq]; exact hUexp x⟩
  set Ut : Subgroup Y := U.comap π with hUt
  let πU : Ut →* U := (π.comp Ut.subtype).codRestrict U (fun x => x.2)
  have hπU : Function.Surjective πU := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hπ u
    exact ⟨⟨y, hu⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Ut) := inferInstance
  have hPU : (P : Subgroup Ut).map πU = ⊤ := by
    have h := (P.mapSurjective hπU).is_maximal' (Q := ⊤) (hUp.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hPY : ¬ TwoRankAtLeastTwo P := fun h => hY
    (CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective (Ut.subtype.comp (P : Subgroup Ut).subtype)
      (Subtype.val_injective.comp Subtype.val_injective) h)
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  have hS : (S : Subgroup P) = ⊤ := by
    have h := S.is_maximal' (Q := ⊤) (P.isPGroup'.to_subgroup ⊤) le_top
    exact h.symm
  set θ : (S : Subgroup P) →* U :=
    (πU.comp (P : Subgroup Ut).subtype).comp (S : Subgroup P).subtype with hθdef
  have hθ : Function.Surjective θ := by
    intro u
    have hu : u ∈ (P : Subgroup Ut).map πU := by rw [hPU]; exact Subgroup.mem_top u
    obtain ⟨x, hx, rfl⟩ := hu
    refine ⟨⟨⟨x, hx⟩, ?_⟩, rfl⟩
    rw [hS]
    exact Subgroup.mem_top _
  have hU4 : Nat.card U ≤ 4 := by
    rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hPY S with hcyc | hq
    ·
      have : IsCyclic U := isCyclic_of_surjective θ hθ
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := U)
      have hcard := Nat.card_zpowers g
      have hzp : Subgroup.zpowers g = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hg x
      rw [hzp, Subgroup.card_top] at hcard
      have hord : orderOf g ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hUexp g)
      omega
    · obtain ⟨r, -, ⟨ϕ⟩⟩ := hq
      exact Sec11.LSSolvableProof.natCard_le_four_of_quaternion (θ.comp ϕ.symm.toMonoidHom)
        (hθ.comp ϕ.symm.surjective) hUexp
  omega

theorem exists_klein_of_surjective_projSL_three {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (hn : 3 ≤ n) (π : Y →* projSL 3 (GaloisField 2 n)) (hπ : Function.Surjective π) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  set φ := Sec4.Census.DoubleCoverRanksTwo.rootHom (K := GaloisField 2 n) with hφ
  set U : Subgroup (projSL 3 (GaloisField 2 n)) := φ.range with hU
  have hUcard : Nat.card U = 2 ^ n := by
    rw [hU, hφ, Sec4.Census.DoubleCoverRanksTwo.card_range_rootHom,
      GaloisField.card 2 n (by omega)]
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; positivity)
  have hUexp : ∀ x : U, x * x = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, ← map_one φ]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero _
  have h8 : 4 < 2 ^ n :=
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact exists_klein_of_surjective π hπ U hUexp (by rw [hUcard]; exact h8)

theorem exists_klein_of_kType {K : Type*} [Group K] [Finite K] [hperf : Group.IsPerfect K]
    (hK : (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n))))
    {Y : Type*} [Group Y] (f : K →* Y) (hf : ∃ k, f k ≠ 1) :
    ∃ a b : K, f a * f a = 1 ∧ f b * f b = 1 ∧ f a * f b = f b * f a ∧ f a ≠ 1 ∧ f b ≠ 1 ∧
      f a ≠ f b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 K with hN
  have hNsolv : Group.IsSolvable N := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := K)).isNilpotent
    infer_instance
  have hsimple : IsSimpleGroup (K ⧸ N) := by
    rcases hK with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 n)
      exact e.isSimpleGroup
    · have := Sec11.LSSolvableProof.isSimpleGroup_projSL (f := n) (by omega)
      exact e.isSimpleGroup
  have hker : f.ker ≤ N := Sec11.LSSolvableProof.ker_le_of_perfect hNsolv hsimple f hf
  let fbar : K ⧸ f.ker →* Y := QuotientGroup.lift f.ker f (fun _ hx => hx)
  have hinj : Function.Injective fbar := Sec11.LSSolvableProof.liftKer_injective f
  let q : K ⧸ f.ker →* K ⧸ N :=
    QuotientGroup.map f.ker N (MonoidHom.id K) (by rw [Subgroup.comap_id]; exact hker)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨QuotientGroup.mk' f.ker k, rfl⟩
  obtain ⟨a', b', ha, hb, hab, ha1, hb1, hne⟩ :
      ∃ a b : K ⧸ f.ker, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
    rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact exists_klein_of_surjective_projSL_three hn (e.toMonoidHom.comp q)
        (e.surjective.comp hq)
    · exact Sec11.LSSolvableProof.exists_klein_four hn (e.toMonoidHom.comp q)
        (e.surjective.comp hq)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective f.ker a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective f.ker b'
  have hfa : ∀ x : K, f x = fbar (QuotientGroup.mk' f.ker x) := fun x => rfl
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfa, ← map_mul fbar, ha, map_one]
  · rw [hfa, ← map_mul fbar, hb, map_one]
  · rw [hfa a, hfa b, ← map_mul fbar, ← map_mul fbar, hab]
  · intro h
    exact ha1 (hinj (by rw [← hfa, h, map_one]))
  · intro h
    exact hb1 (hinj (by rw [← hfa, h, map_one]))
  · intro h
    exact hne (hinj (by rw [← hfa, ← hfa, h]))

end CFSG.RankThree.PartTwo.Sec20.Res11
