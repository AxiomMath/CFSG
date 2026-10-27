module

public import CFSG.Quasithin.EmptyFaithful.SzF53MNatL2
import all CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Mod

open Equiv CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

set_option maxRecDepth 100000 in
private theorem orth_card_l2 : (commIterF orth S5SylF 2).card = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem orth_l2_table : ∀ τ ∈ S5SylF,
    (∀ y ∈ commIterF orth S5SylF 2, orth.act τ y = y) ↔ τ ∈ S5ThatF := by
  decide +kernel

private theorem S5That_le_S5Syl : ∀ τ ∈ S5ThatF, τ ∈ S5SylF := by
  decide +kernel

theorem card_S5That : Nat.card S5That = 4 := by
  have h : S5ThatF.card = 4 := by decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5That_iff)

theorem orth_centralizer_l2 {τ : Perm (Fin 5)} (hτ : τ ∈ S5Syl) (Y : Subgroup orth.W)
    (hY : IsInvSub orth S5Syl Y) (hc : Nat.card Y = 4) :
    (∀ y ∈ Y, orth.act τ y = y) ↔ τ ∈ S5That := by
  have hcard : Nat.card (commIter orth S5Syl 2) = 2 ^ 2 := by
    rw [card_commIter orth mem_S5Syl_iff, orth_card_l2]
    norm_num
  have hYeq : Y = commIter orth S5Syl 2 :=
    ((lemma26 orth (Or.inl rfl) 2 (by norm_num)).unique ⟨hY, by rw [hc]; norm_num⟩
      ⟨isInvSub_commIter orth S5Syl 2, hcard⟩)
  rw [mem_S5That_iff, ← orth_l2_table τ ((mem_S5Syl_iff τ).mp hτ), hYeq]
  exact forall_congr' fun y => by rw [mem_commIter_iff orth mem_S5Syl_iff]

theorem IsOrthSec.relIndex_centralizer_l2 {F L X : Subgroup G} (h : IsOrthSec F L X)
    {S₀ : Subgroup G} (hS : IsSylowTwoOf S₀ F) {U : Subgroup G} (hLU : L ≤ U) (hUX : U ≤ X)
    (hn : S₀ ≤ Subgroup.normalizer (U : Set G)) (h4 : L.relIndex U = 4) :
    (cSecIn F L X).relIndex (cSecIn S₀ L U) = 4 := by
  have hLX : L ≤ X := hLU.trans hUX
  have hsec := IsModelSec.isSec h hLX
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := h
  have hS₀F : S₀ ≤ F := hS.1
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ := hsd.exists_normalized hθs hθk hS
  have hinvU : ∀ k ∈ S₀, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    ((Subgroup.mem_normalizer_iff.mp (hn hk)) u).mp hu
  obtain ⟨Y, hY, hYm⟩ := (hsd'.invariant_iff_sub hS₀F hLU hUX).mp hinvU
  have hYinv : IsInvSub orth S5Syl Y := by rw [← hPS]; exact hY
  have hYcard : Nat.card Y = 4 := by
    have h1 : Nat.card (Y.map β') = Nat.card Y := Subgroup.card_map_of_injective hsd'.inj
    rw [← h1, hYm]
    have hk : (QuotientGroup.mk' (L.subgroupOf X)).ker = L.subgroupOf X :=
      QuotientGroup.ker_mk' _
    rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hUX, h4]
  have hmemΨ : ∀ s : G, ∀ hs : s ∈ S₀, Ψ ⟨s, hS₀F hs⟩ ∈ S5Syl := fun s hs => by
    rw [← hPS]; exact ⟨⟨s, hS₀F hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hcle : cSecIn S₀ L U ≤ S₀ := (Subgroup.closure_le S₀).mpr fun _ hx => hx.1
  have hcS : ∀ s : G, ∀ hs : s ∈ S₀, s ∈ cSecIn S₀ L U ↔ Ψ ⟨s, hS₀F hs⟩ ∈ S5That := by
    intro s hs
    have h1 : s ∈ cSecIn S₀ L U ↔ ∀ x ∈ U, s * x * s⁻¹ * x⁻¹ ∈ L := by
      constructor
      · intro hmem
        exact (X1512.mem_cSecIn_of_normalizes (hS₀F.trans hsec.normL) hmem).2
      · intro hall
        exact Subgroup.subset_closure ⟨hs, hall⟩
    rw [h1, hsd'.act_trivial_iff hUX hYm (hS₀F hs)]
    exact orth_centralizer_l2 (hmemΨ s hs) Y hYinv hYcard
  have hDF : cSecIn S₀ L U ≤ F := hcle.trans hS₀F
  rw [← Subgroup.relIndex_subgroupOf hDF, ← hkΨ, Subgroup.relIndex_ker]
  have hmap : ((cSecIn S₀ L U).subgroupOf F).map Ψ = S5That := by
    ext τ
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hd' := Subgroup.mem_subgroupOf.mp hd
      exact (hcS d (hcle hd')).mp hd'
    · intro hτ
      have hτS : τ ∈ S5Syl :=
        (mem_S5Syl_iff τ).mpr (S5That_le_S5Syl τ ((mem_S5That_iff τ).mp hτ))
      rw [← hPS] at hτS
      obtain ⟨d, hd, rfl⟩ := hτS
      have hdS : (d : G) ∈ S₀ := Subgroup.mem_subgroupOf.mp hd
      exact ⟨d, Subgroup.mem_subgroupOf.mpr ((hcS d hdS).mpr hτ), rfl⟩
  rw [hmap, card_S5That]

end CFSG.Quasithin.F53Mod
