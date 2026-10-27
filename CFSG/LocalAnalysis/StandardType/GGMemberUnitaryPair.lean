module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPairAux
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

private theorem ggPairConcl_comm_supp_upp {G : Type} [Group G] [Finite G] {n : ℕ}
    {Bs X : Subgroup G} {r r' : MulAut ↥Bs}
    {ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs)} {a₁ b₁ c₁ d₁ : Fin n}
    (hab₁ : a₁ ≠ b₁) (hcd₁ : c₁ ≠ d₁)
    (hr_eq : r = ((ε (Equiv.swap a₁ b₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hr'_eq : r' = ((ε (Equiv.swap c₁ d₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hne : r ≠ r') (hcomm : r * r' = r' * r) :
    ∀ x : Fin n, Equiv.swap a₁ b₁ x = x ∨ Equiv.swap c₁ d₁ x = x := by
  have hcomm_swap : Equiv.swap a₁ b₁ * Equiv.swap c₁ d₁ =
      Equiv.swap c₁ d₁ * Equiv.swap a₁ b₁ := by
    apply ε.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    rw [← hr_eq, ← hr'_eq]
    exact hcomm
  have hne_swap : Equiv.swap a₁ b₁ ≠ Equiv.swap c₁ d₁ := by
    intro h
    apply hne
    rw [hr_eq, hr'_eq, h]
  exact Equiv.Perm.disjoint_iff_eq_or_eq.mp
    (ggMUP1_swap_disjoint hab₁ hcd₁ hcomm_swap hne_swap)

private theorem ggPairConcl_comm_upp {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} {r r' : MulAut ↥Bs} {a₁ b₁ c₁ d₁ : Fin n}
    (hdisj : ∀ x : Fin n, Equiv.swap a₁ b₁ x = x ∨ Equiv.swap c₁ d₁ x = x)
    (hab₁ : a₁ ≠ b₁) (hcd₁ : c₁ ≠ d₁)
    (hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a₁ b₁).map ψ)
    (hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 f n c₁ d₁).map ψ) :
    ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a := by
  intro a ha b hb
  have hac : a₁ ≠ c₁ := by
    intro h
    rcases hdisj a₁ with h1 | h2
    · rw [Equiv.swap_apply_left] at h1
      exact hab₁ h1.symm
    · rw [h, Equiv.swap_apply_left] at h2
      exact hcd₁ h2.symm
  have had : a₁ ≠ d₁ := by
    intro h
    rcases hdisj a₁ with h1 | h2
    · rw [Equiv.swap_apply_left] at h1
      exact hab₁ h1.symm
    · rw [h, Equiv.swap_apply_right] at h2
      exact hcd₁ h2
  have hbc : b₁ ≠ c₁ := by
    intro h
    rcases hdisj b₁ with h1 | h2
    · rw [Equiv.swap_apply_right] at h1
      exact hab₁ h1
    · rw [h, Equiv.swap_apply_left] at h2
      exact hcd₁ h2.symm
  have hbd : b₁ ≠ d₁ := by
    intro h
    rcases hdisj b₁ with h1 | h2
    · rw [Equiv.swap_apply_right] at h1
      exact hab₁ h1
    · rw [h, Equiv.swap_apply_right] at h2
      exact hcd₁ h2
  rw [hrS] at ha
  rw [hr'S] at hb
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hb
  simpa only [map_mul] using
    congrArg ψ (ggMUP1_suPairBlock_comm hac had hbc hbd u hu v hv)

private theorem ggPairConcl_noncomm_upp {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} {r r' : MulAut ↥Bs}
    {ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs)} {a₁ b₁ c₁ d₁ : Fin n}
    (hab₁ : a₁ ≠ b₁) (hcd₁ : c₁ ≠ d₁)
    (hr_eq : r = ((ε (Equiv.swap a₁ b₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hr'_eq : r' = ((ε (Equiv.swap c₁ d₁) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a₁ b₁).map ψ)
    (hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 f n c₁ d₁).map ψ)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hn4 : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hnc : r * r' ≠ r' * r) :
    ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2] (f' : ℕ),
      Nat.card K' = (2 ^ f') ^ 2 →
      Nat.card (ggRankOneIn X Bs r) = 2 ^ f' * ((2 ^ f') ^ 2 - 1) →
      ∃ W : Subgroup G, UnitaryBlockStandardPair K' 2 f' W
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs r') := by
  intro K' _ _ _ f' hK' hS
  have hnc_swap : Equiv.swap a₁ b₁ * Equiv.swap c₁ d₁ ≠
      Equiv.swap c₁ d₁ * Equiv.swap a₁ b₁ := by
    intro hswap
    apply hnc
    have h3 := congrArg (fun π : Equiv.Perm (Fin n) =>
      ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) hswap
    simp only [map_mul, Subgroup.coe_mul] at h3
    rw [← hr_eq, ← hr'_eq] at h3
    exact h3
  obtain ⟨x, y, z, hxy, hyz, hxz, hxy_eq, hyz_eq⟩ :=
    ggMUP1_share3 hab₁ hcd₁ hnc_swap
  obtain ⟨W, hW⟩ := ggPhanNSAPairAux_stdPair (K := K) (f := f) (n := n) ψ hker
    (by omega) hxy hyz hxz
  have e1 : (ggSuPairBlock K 2 f n x y).map ψ = ggRankOneIn X Bs r := by
    rw [ggMUP1_suPairBlock_congr (K := K) (p := 2) (f := f) (n := n)
      (a := x) (b := y) (c := a₁) (d := b₁) hxy_eq.symm, ← hrS]
  have e2 : (ggSuPairBlock K 2 f n y z).map ψ = ggRankOneIn X Bs r' := by
    rw [ggMUP1_suPairBlock_congr (K := K) (p := 2) (f := f) (n := n)
      (a := y) (b := z) (c := c₁) (d := d₁) hyz_eq.symm, ← hr'S]
  rw [e1, e2] at hW
  exact ⟨W, ggPhanNSAPairAux_stdPair_of_card hKcard hK' hW hS⟩

theorem ggPairConcl_of_unitary_position {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hn4 : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hpos : GGTableBPosSU p Bs X K f n ψ)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrA' : r' ∈ ggAutomizer X Bs)
    (hrefl : GGIsReflection p r) (hrefl' : GGIsReflection p r') (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  classical
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  obtain ⟨a₁, b₁, hab₁, hr_eq⟩ := ggMUR1_refl_eq_swap hp hp2 hBs ε hεrefl hrA hrefl
  obtain ⟨c₁, d₁, hcd₁, hr'_eq⟩ := ggMUR1_refl_eq_swap hp hp2 hBs ε hεrefl hrA' hrefl'
  have hrS : ggRankOneIn X Bs r = (ggSuPairBlock K 2 f n a₁ b₁).map ψ := by
    rw [hr_eq]; exact hεlevi a₁ b₁ hab₁
  have hr'S : ggRankOneIn X Bs r' = (ggSuPairBlock K 2 f n c₁ d₁).map ψ := by
    rw [hr'_eq]; exact hεlevi c₁ d₁ hcd₁
  exact ⟨fun hcomm => ggPairConcl_comm_upp
      (ggPairConcl_comm_supp_upp hab₁ hcd₁ hr_eq hr'_eq hne hcomm) hab₁ hcd₁ hrS hr'S,
    ggPairConcl_noncomm_upp hab₁ hcd₁ hr_eq hr'_eq hrS hr'S hKcard hn4 hker⟩

theorem ggPairUnitaryMemberInput_holds :
    GGPairUnitaryMemberInput := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 X hX hXns hU r hrA hrC r' hrA' hrC' hne
  obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hKcard, hn4, hker, hrange, hpq, hpos, -⟩ :=
    ggMemberUnitary_position hcfg hX hU
  exact ggPairConcl_of_unitary_position (ggRouteCfg_prime hcfg).1 (ggRouteCfg_prime hcfg).2
    (ggRouteCfg_isElemAbelian hcfg) hKcard hn4 hker hpos hrA hrA'
    (ggCoxRefl_isReflection hpres.2 hrC) (ggCoxRefl_isReflection hpres.2 hrC') hne

end CFSG.StandardType

end
