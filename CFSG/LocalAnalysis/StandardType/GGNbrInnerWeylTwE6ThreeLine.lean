module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

namespace NbrTwE6Three

theorem pow_succ_le_card_of_ne {p k : ℕ} (hp : p.Prime) {H : Type} [Group H]
    {A : Subgroup H} [Finite A] (hA : IsElemAbelian p A) (hle : p ^ k ≤ Nat.card A)
    (hne : Nat.card A ≠ p ^ k) : p ^ (k + 1) ≤ Nat.card A := by
  have := Fact.mk hp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hA)
  rw [hm] at hle hne ⊢
  have h1 : k ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have h2 : k ≠ m := fun h => hne (by rw [h])
  exact Nat.pow_le_pow_right hp.pos (by omega)

end NbrTwE6Three

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggLAut_mem_range_conj_of_ggGamma {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {b : G} (hb : b ∈ Bs)
    (h : ggGamma K hN ⟨b, hb⟩ ∈ (MulAut.conj : K →* MulAut K).range) :
    ggLAut K θ ⟨b, hN hb⟩ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨ggQuotHom θ k, ?_⟩
  ext r
  obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
  have h1 := ggBeta_ggQuotHom K hN θ ⟨b, hb⟩ l
  rw [ggBeta_eq] at h1
  rw [h1, ← hk]
  simp [ggQuotHom_apply]

theorem ggNbrInnerWeyl_of_good {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs) {n : K}
    (hn : GGTorusWeylElt p (ggGamma K hN).range n)
    (hmv : MulAut.conj n * ggGamma K hN ⟨x, hxBs⟩ * (MulAut.conj n)⁻¹ ∉
        Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩) ∨
      (n * (ggGamma K hN ⟨x, hxBs⟩ n)⁻¹ ∈ Subgroup.center K ∧
        n * (ggGamma K hN ⟨x, hxBs⟩ n)⁻¹ ≠ 1)) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_ggTorusWeylElt hN hSC hn
  have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hnN b).mp hb
  refine ⟨(n : G), n.2, fun b hb => ?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun c hc =>
      TableB.IsElemAbelian.comm hBs hc (hWB b hb)
  rcases hmv with hmv | ⟨hz, hz1⟩
  · intro hmem
    apply hmv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have e : (⟨(n : G) * x * (n : G)⁻¹, hWB x hxBs⟩ : Bs) = (⟨x, hxBs⟩ : Bs) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [← ggGamma_conj K hN n ⟨x, hxBs⟩ (hWB x hxBs), e, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzG : ((n * (γ ⟨x, hxBs⟩ n)⁻¹ : K) : G) = x ^ (k - 1) := by
      push_cast
      rw [hγ, ggGamma_coe, zpow_sub_one, hk]
      group
    apply not_mem_centralizer_of_nbr hnb
    have hzC : x ^ (k - 1) ∈ Subgroup.centralizer (K : Set G) := by
      rw [← hzG, Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
      exact congrArg Subtype.val h1
    have hz1' : x ^ (k - 1) ≠ 1 := by
      rw [← hzG]
      intro h
      exact hz1 (Subtype.ext (by simpa using h))
    have hxp : x ^ p = 1 := hBs.2 x (hcfg.tableB_facts.2.2.1)
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hz1' (one_zpow _)
    have hcard : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have hmemz : (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) ∈
        Subgroup.zpowers (⟨x ^ (k - 1), Subgroup.zpow_mem_zpowers x (k - 1)⟩ :
          Subgroup.zpowers x) :=
      mem_zpowers_of_prime_card hcard (fun h => hz1' (congrArg Subtype.val h))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemz
    have hxm : (x ^ (k - 1)) ^ m = x := by simpa using congrArg Subtype.val hm
    rw [← hxm]
    exact Subgroup.zpow_mem _ hzC m

end Config

end CFSG.StandardType

end
