module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79TP

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.odd_K (h : FS79Hyp b t b₁ b₂ J) :
    Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers b)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup H := Opp 3 (Nor (Subgroup.zpowers b)) with hO
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  by_contra hodd
  have hEven : Even (Nat.card O) := Nat.not_odd_iff_even.mp hodd
  have h2dvd : 2 ∣ Nat.card O := even_iff_two_dvd.mp hEven
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    rw [hO]
    exact L14.Opp_coprime 3 _
  have h3dvd : ¬ 3 ∣ Nat.card O := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop hd
  have hBN : B ≤ Nor (Subgroup.zpowers b) := fun β hβ =>
    fs79_cen_le_nor_zpowers b
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.B_comm hβ (FS79Hyp.zpowers_le_B b b₁ b₂
        (Subgroup.mem_zpowers b))))
  have hBO : B ≤ Subgroup.normalizer (O : Set H) := by
    intro β hβ
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    exact L14.Opp_conj_mem (hBN hβ) hz
  have hB3 : IsPGroup 3 B := by
    have hE := h.isElemAb_B
    rw [← hB] at hE
    haveI : IsElementaryAbelian 3 ↥B := hE.1
    exact IsElementaryAbelian.isPGroup 3 ↥B
  obtain ⟨R, hRsyl, -, hBR⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
      (q := 3) (r := 2) (A := B) (K := O) (P := ⊥)
      Nat.prime_three Nat.prime_two hB3 hBO h3dvd bot_le IsPGroup.of_bot
      Subgroup.le_normalizer_of_normal
  have hR2 : IsPGroup 2 R := CFSG.ABGLocalTools.IsSylowOf.isPGroup hRsyl
  have hRbot : R = ⊥ := h.no_two R hR2 (by simpa [hB, Nor] using hBR)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ¬ 2 ∣ R.relIndex O := (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
  exact hndvd (by rw [hRbot, Subgroup.relIndex_bot_left]; exact h2dvd)

theorem exists_conj_le_abg {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K P X : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hXK : X ≤ K)
    (hX : IsPGroup p X) : ∃ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ P := by
  obtain ⟨Q, rfl⟩ := hP
  have hXsub : IsPGroup p (X.subgroupOf K) := hX.comap_subtype
  obtain ⟨S, hS⟩ := hXsub.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K Q S
  refine ⟨((g : ↥K) : G)⁻¹, K.inv_mem g.2, fun x hx => ?_⟩
  have hxS : (⟨x, hXK hx⟩ : ↥K) ∈ ((g • Q : Sylow p ↥K) : Subgroup ↥K) := by
    rw [hg]
    exact hS (show (⟨x, hXK hx⟩ : ↥K) ∈ X.subgroupOf K from hx)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨s, hs, hseq⟩ := hxS
  have h1 := congrArg Subtype.val hseq
  have h2 : ((g : ↥K) : G) * (s : G) * ((g : ↥K) : G)⁻¹ = x := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have h3 : ((g : ↥K) : G)⁻¹ * x * ((g : ↥K) : G) = (s : G) := by
    rw [← h2]
    group
  have : ((g : ↥K) : G)⁻¹ * x * ((g : ↥K) : G)⁻¹⁻¹ = (s : G) := by
    rw [inv_inv]
    exact h3
  rw [this]
  exact ⟨s, hs, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
