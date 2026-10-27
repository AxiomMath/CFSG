module

public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE

section Rational


theorem fixed_pSubgroup_le_range {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K L : Type} [Field K]
    [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (X : Subgroup (ModGL τ L)) [Finite X] (hXC : X ≤ adjointGroup τ L)
    (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) {P : Subgroup (ModGL τ L)} (hPX : P ≤ X)
    (hP : IsPGroup p P) : P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hdτ⟩ : ∃ d : ℕ, d ≤ 2 ∧
      ((τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) := by
    rcases hτ with rfl | rfl
    · exact ⟨2, le_rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨1, by norm_num, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have hrel := (finite_fixed_subgroup_rational_perfect d hdτ Fr hFr X hXC hXF).1
  set H := (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) with hH
  have hd0 : d ≠ 0 := by omega
  have hrelle : H.relIndex X ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hrel
  have hXne : H.relIndex X ≠ 0 := fun h => by
    rw [h] at hrel
    exact hd0 (zero_dvd_iff.1 hrel)
  have hle : H.relIndex P ≤ H.relIndex X := Subgroup.relIndex_le_of_le_right hPX hXne
  have hfin : Finite P := Finite.of_injective (Subgroup.inclusion hPX)
    (Subgroup.inclusion_injective hPX)
  obtain ⟨n, hn⟩ := hP.index (H.subgroupOf P)
  have hidx : H.relIndex P = p ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have : 3 ≤ p ^ n := le_trans h3 (Nat.le_self_pow hne p)
    omega
  rw [hn0, pow_zero] at hidx
  exact Subgroup.relIndex_eq_one.1 hidx

theorem exists_rational_of_fixed_pTorsion {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K L : Type}
    [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {y : ModGL τ L} (hy : y ∈ adjointGroup τ L) (hyF : Units.map (entrywiseHom Fr) y = y)
    (hyp : y ^ p = 1) :
    ∃ c : adjointGroup τ K, baseChangeGL (algebraMap K L) (c : ModGL τ K) = y := by
  classical
  have hfin : Finite (Subgroup.zpowers y) :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hyp⟩)
  have hXC : Subgroup.zpowers y ≤ adjointGroup τ L := (Subgroup.zpowers_le).2 hy
  have hXF : ∀ x ∈ Subgroup.zpowers y, Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, hyF]
  have hP : IsPGroup p (Subgroup.zpowers y) := fun x => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hyp, one_zpow]
    rfl⟩
  have hle := fixed_pSubgroup_le_range hτ hp hp2 Fr hFr (Subgroup.zpowers y) hXC hXF
    (le_refl _) hP
  obtain ⟨c, hc, hcy⟩ := hle (Subgroup.mem_zpowers y)
  exact ⟨⟨c, hc⟩, hcy⟩

end Rational

end ExcFramesHalf

end CFSG.StandardType
