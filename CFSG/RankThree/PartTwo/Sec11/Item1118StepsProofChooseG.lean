module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.RankThree.PartTwo.Sec11.Item1119ProofBasic

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1118StepsProof

section Group

variable {G : Type*} [Group G]

theorem exists_mul_commute_of_conj_mem [Finite G] {S₀ : Subgroup G} {j g : G}
    (hS₀ : IsPGroup 3 S₀) (hj : ∃ k : ℕ, j ^ 2 ^ k = 1)
    (hjS : j ∈ Subgroup.normalizer (S₀ : Set G)) (hjg : g⁻¹ * (j * g * j⁻¹) ∈ S₀) :
    ∃ z ∈ S₀, g * z * j = j * (g * z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype S₀ := Fintype.ofFinite S₀
  have hmem : ∀ z ∈ S₀, g⁻¹ * (j * (g * z) * j⁻¹) ∈ S₀ := by
    intro z hz
    have e : g⁻¹ * (j * (g * z) * j⁻¹) = (g⁻¹ * (j * g * j⁻¹)) * (j * z * j⁻¹) := by group
    rw [e]
    exact S₀.mul_mem hjg ((Subgroup.mem_normalizer_iff.mp hjS z).mp hz)
  let f : S₀ → S₀ := fun z => ⟨g⁻¹ * (j * (g * z) * j⁻¹), hmem z z.2⟩
  have hf : Function.Injective f := by
    intro z z' hzz
    have h1 : g⁻¹ * (j * (g * (z : G)) * j⁻¹) = g⁻¹ * (j * (g * (z' : G)) * j⁻¹) :=
      congrArg Subtype.val hzz
    have h2 : j * (g * (z : G)) * j⁻¹ = j * (g * (z' : G)) * j⁻¹ := mul_left_cancel h1
    have h3 : j * (g * (z : G)) = j * (g * (z' : G)) := mul_right_cancel h2
    have h4 : g * (z : G) = g * (z' : G) := mul_left_cancel h3
    exact Subtype.ext (mul_left_cancel h4)
  set σ : Equiv.Perm S₀ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf) with hσ
  have hσn : ∀ n : ℕ, ∀ z : S₀, ((σ ^ n) z : G) = g⁻¹ * (j ^ n * (g * z) * (j ^ n)⁻¹) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply]
      change g⁻¹ * (j * (g * ((σ ^ n) z : G)) * j⁻¹) = _
      rw [ih z, pow_succ']
      group
  obtain ⟨k, hk⟩ := hj
  have hσk : σ ^ 2 ^ k = 1 := by
    refine Equiv.ext fun z => Subtype.ext ?_
    rw [hσn, hk]
    simp
  have hcard : ¬ 2 ∣ Fintype.card S₀ := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS₀
    rw [← Nat.card_eq_fintype_card, hm]
    intro h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
  obtain ⟨z, hz⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσk
  refine ⟨z, z.2, ?_⟩
  have hfix : g⁻¹ * (j * (g * (z : G)) * j⁻¹) = z := congrArg Subtype.val hz
  have h3 : j * (g * (z : G)) * j⁻¹ = g * z := by
    calc j * (g * (z : G)) * j⁻¹ = g * (g⁻¹ * (j * (g * (z : G)) * j⁻¹)) := by group
      _ = g * z := by rw [hfix]
  calc g * (z : G) * j = (j * (g * (z : G)) * j⁻¹) * j := by rw [h3]
    _ = j * (g * z) := by group

theorem conj_conj_eq_of_inverts {t g c a d : G} (htc : t * c = c * t) (hta : t * a = a * t)
    (htd : t * d * t⁻¹ = d⁻¹) (hga : g * a = a * g) (hgd : g * d = d * g)
    (htu : t * (g * c * g⁻¹ * c⁻¹) * t⁻¹ = (g * c * g⁻¹ * c⁻¹)⁻¹)
    (hgu : g * (g * c * g⁻¹ * c⁻¹) = g * c * g⁻¹ * c⁻¹ * g) :
    ∀ z ∈ Subgroup.closure ({c, a, d} : Set G),
      t * g * t⁻¹ * z * (t * g * t⁻¹)⁻¹ = g⁻¹ * z * g := by
  have hta' : Commute t a := hta
  have hga' : Commute g a := hga
  have hgd' : Commute g d := hgd
  have hle : Subgroup.closure ({c, a, d} : Set G) ≤
      (MulAut.conj (t * g * t⁻¹)).toMonoidHom.eqLocus (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    refine ⟨?_, ?_, ?_⟩
    ·
      change t * g * t⁻¹ * c * (t * g * t⁻¹)⁻¹ = g⁻¹ * c * g⁻¹⁻¹
      set u := g * c * g⁻¹ * c⁻¹ with hu
      have hgc : g * c * g⁻¹ = u * c := by rw [hu]; group
      have hl : t * g * t⁻¹ * c * (t * g * t⁻¹)⁻¹ = u⁻¹ * c := by
        calc t * g * t⁻¹ * c * (t * g * t⁻¹)⁻¹ = t * g * (t⁻¹ * (c * t)) * g⁻¹ * t⁻¹ := by
              group
          _ = t * (g * c * g⁻¹) * t⁻¹ := by rw [← htc]; group
          _ = t * u * t⁻¹ * (t * c * t⁻¹) := by rw [hgc]; group
          _ = u⁻¹ * c := by rw [htu, htc, mul_inv_cancel_right]
      have hgu' : g⁻¹ * u * g = u := by
        calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
          _ = u := by rw [← hgu]; group
      have hr : g⁻¹ * c * g⁻¹⁻¹ = u⁻¹ * c := by
        calc g⁻¹ * c * g⁻¹⁻¹ = u⁻¹ * (g⁻¹ * u * g) * (g⁻¹ * c * g) := by rw [hgu']; group
          _ = u⁻¹ * (g⁻¹ * (u * c) * g) := by group
          _ = u⁻¹ * (g⁻¹ * (g * c * g⁻¹) * g) := by rw [hgc]
          _ = u⁻¹ * c := by group
      rw [hl, hr]
    ·
      change t * g * t⁻¹ * a * (t * g * t⁻¹)⁻¹ = g⁻¹ * a * g⁻¹⁻¹
      have hT : Commute (t * g * t⁻¹) a := (hta'.mul_left hga').mul_left hta'.inv_left
      rw [hT.eq, mul_inv_cancel_right, inv_inv, hga'.inv_left.eq, inv_mul_cancel_right]
    ·
      change t * g * t⁻¹ * d * (t * g * t⁻¹)⁻¹ = g⁻¹ * d * g⁻¹⁻¹
      have htd' : t⁻¹ * d * t = d⁻¹ := by
        calc t⁻¹ * d * t = (t⁻¹ * (t * d * t⁻¹) * t)⁻¹ := by rw [htd]; group
          _ = d⁻¹ := by group
      have hgdi : g * d⁻¹ * g⁻¹ = d⁻¹ := by rw [hgd'.inv_right.eq, mul_inv_cancel_right]
      calc t * g * t⁻¹ * d * (t * g * t⁻¹)⁻¹ = t * (g * (t⁻¹ * d * t) * g⁻¹) * t⁻¹ := by group
        _ = (t * d * t⁻¹)⁻¹ := by rw [htd', hgdi]; group
        _ = g⁻¹ * d * g⁻¹⁻¹ := by
          rw [htd, inv_inv, inv_inv, hgd'.inv_left.eq, inv_mul_cancel_right]
  intro z hz
  have h := hle hz
  change t * g * t⁻¹ * z * (t * g * t⁻¹)⁻¹ = g⁻¹ * z * g⁻¹⁻¹ at h
  rwa [inv_inv] at h

end Group

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

end Item1118StepsProof

end CFSG.RankThree.PartTwo.Sec11
