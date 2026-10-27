module

public import CFSG.Quasithin.Background.C124BlockA
public import CFSG.Quasithin.Vol2.Ch1Comm

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_prod {X T L : Subgroup G} (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have key : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G) := by
    intro t ht
    set L' := L.map (MulAut.conj t).toMonoidHom with hL'
    have hL'c : L' ∈ cComp X := map_conj_mem_cComp hL (hT.1 ht)
    have hnor : L' ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_mem_cComp hL hL'c
    set B : Subgroup G := X ⊓ Subgroup.normalizer (L : Set G) with hB
    have hLB : L ≤ B := le_inf hLX Subgroup.le_normalizer
    have hL'B : L' ≤ B := le_inf (le_of_mem_cComp hL'c) hnor
    have hperf : ⁅L', L'⁆ = L' := by
      rw [hL', ← Subgroup.map_commutator, perfect_of_mem_cComp hL]
    have hnorm : (L.subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLB).2 inf_le_right
    have h2 : IsPGroup 2 (↥B ⧸ L.subgroupOf B) := by
      intro q
      obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨l, hl, t', ht', hbt⟩ := hprod b hb.1
      have ht'B : t' ∈ B := by
        have : t' = l⁻¹ * b := by rw [hbt]; group
        rw [this]
        exact B.mul_mem (B.inv_mem (hLB hl)) hb
      obtain ⟨n, hn⟩ := hT.2.1 ⟨t', ht'⟩
      refine ⟨n, ?_⟩
      have hmk : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ L.subgroupOf B) =
          QuotientGroup.mk ⟨t', ht'B⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        show (b : G)⁻¹ * t' ∈ L
        have h1 : b⁻¹ * t' = t'⁻¹ * l⁻¹ * t'⁻¹⁻¹ := by rw [hbt]; group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.1 (B.inv_mem ht'B).2 l⁻¹).1 (L.inv_mem hl)
      rw [hmk, ← QuotientGroup.mk_pow]
      have : (⟨t', ht'B⟩ : ↥B) ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [this]
      rfl
    let φ : ↥L' →* ↥B ⧸ L.subgroupOf B :=
      (QuotientGroup.mk' (L.subgroupOf B)).comp (Subgroup.inclusion hL'B)
    have hker : φ.ker = ⊤ :=
      noTwoQuot_of_perfect hperf φ.ker
        (h2.of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ))
    have hle : L' ≤ L := by
      intro x hx
      have : (⟨x, hx⟩ : ↥L') ∈ φ.ker := by rw [hker]; trivial
      rw [MonoidHom.mem_ker] at this
      have h1 : (QuotientGroup.mk (⟨x, hL'B hx⟩ : ↥B) : ↥B ⧸ L.subgroupOf B) = 1 := this
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    have heq : L' = L := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hL', Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact A38.map_conj_eq_iff.1 heq
  intro x hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hprod x hx
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hl) (key t ht)

end CFSG.Quasithin.C124
