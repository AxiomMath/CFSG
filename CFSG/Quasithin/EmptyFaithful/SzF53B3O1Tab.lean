module

public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin.F53B3.O1

open Equiv CFSG.Quasithin.F53Mod CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

set_option maxRecDepth 100000 in
theorem orth_not_comm_fixed_table : ∀ t ∈ S5SylF, t ≠ 1 →
    ∃ w : orth.W, ∃ s ∈ S5SylF, orth.act s (orth.act t w * w⁻¹) ≠ orth.act t w * w⁻¹ := by
  decide +kernel

@[expose] def l3 : Subgroup orth.W where
  carrier := {w | Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 = 0}
  one_mem' := by
    show Multiplicative.toAdd ((1 : ↥(G6.coreMod 5)).1) 4 = 0
    rfl
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    show Multiplicative.toAdd ((x : ↥(G6.coreMod 5)).1 * (y : ↥(G6.coreMod 5)).1) 4 = 0
    rw [toAdd_mul, Pi.add_apply, hx, hy, add_zero]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    show Multiplicative.toAdd ((x : ↥(G6.coreMod 5)).1⁻¹) 4 = 0
    rw [toAdd_inv, Pi.neg_apply, hx]
    rfl

theorem mem_l3 {w : orth.W} : w ∈ l3 ↔ Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 = 0 := Iff.rfl

set_option maxRecDepth 100000 in
private theorem l3_inv_table : ∀ b ∈ S5SylF, ∀ u : orth.W,
    Multiplicative.toAdd (u : ↥(G6.coreMod 5)).1 4 = 0 →
      Multiplicative.toAdd ((orth.act b u : orth.W) : ↥(G6.coreMod 5)).1 4 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem l3_card_table :
    (Finset.univ.filter fun w : orth.W => Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 = 0).card
      = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem orth_l3_table : ∀ t ∈ S5SylF, t ≠ 1 →
    (∀ w : orth.W, Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 = 0 → orth.act t w = w) →
    (∃ c : orth.W, ∀ w : orth.W, orth.act t w * w⁻¹ = 1 ∨ orth.act t w * w⁻¹ = c) → False := by
  decide +kernel

theorem isInvSub_l3 : IsInvSub orth S5Syl l3 := fun b hb u hu =>
  l3_inv_table b ((mem_S5Syl_iff b).mp hb) u hu

theorem card_l3 : Nat.card l3 = 2 ^ 3 := by
  have h : Nat.card l3 = (Finset.univ.filter fun w : orth.W =>
      Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 4 = 0).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by simp [mem_l3])
  rw [h, l3_card_table]
  norm_num

theorem eq_l3_of_invSub {U : Subgroup orth.W} (hU : IsInvSub orth S5Syl U)
    (hc : Nat.card U = 2 ^ 3) : U = l3 :=
  (lemma26 orth (Or.inl rfl) 3 (by norm_num)).unique ⟨hU, hc⟩ ⟨isInvSub_l3, card_l3⟩

theorem orth_not_comm_fixed [Finite G] {F L X S₀ : Subgroup G} (h : IsOrthSec F L X)
    (hq : Nonempty (OTwoQuot F ≃* Perm (Fin 5))) (hS : IsSylowTwoOf S₀ F) {u : G} (hu : u ∈ S₀)
    (huQ : u ∉ pCoreOf 2 F)
    (hfix : ∀ v ∈ X, ∀ s ∈ S₀,
      s * (u * v * u⁻¹ * v⁻¹) * s⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ ∈ L) : False := by
  have hcs := IsModelSec.cSecIn_eq_pCoreOf h hq
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ := hsd.exists_normalized hθs hθk hS
  have huF : u ∈ F := hS.1 hu
  have hu1 : Ψ ⟨u, huF⟩ ≠ 1 := by
    intro h1
    apply huQ
    rw [← hcs]
    exact (mem_cSecIn_iff_of_ker hkΨ huF).mp h1
  have huP : Ψ ⟨u, huF⟩ ∈ S5Syl := by
    rw [← hPS]
    exact ⟨⟨u, huF⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have key : ∀ (w : orth.W), ∀ τ ∈ S5Syl,
      orth.act τ (orth.act (Ψ ⟨u, huF⟩) w * w⁻¹) = orth.act (Ψ ⟨u, huF⟩) w * w⁻¹ := by
    intro w τ hτ
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β' w)
    obtain ⟨hax, h1⟩ := hsd'.beta_comm huF hx.symm
    rw [← hPS] at hτ
    obtain ⟨s', hs', rfl⟩ := hτ
    obtain ⟨hkx, h2⟩ := hsd'.equiv s' _ ⟨u * x * u⁻¹ * x⁻¹, hax⟩ h1
    apply hsd'.inj
    rw [h2, h1]
    exact (mk_eq_iff_mem.mpr (hfix x x.2 s' (Subgroup.mem_subgroupOf.mp hs'))).symm
  obtain ⟨w, s, hs, hne⟩ := orth_not_comm_fixed_table (Ψ ⟨u, huF⟩) ((mem_S5Syl_iff _).mp huP) hu1
  exact hne (key w s ((mem_S5Syl_iff s).mpr hs))

theorem orth_no_rank_one [Finite G] {F L X S₀ R : Subgroup G} (h : IsOrthSec F L X)
    (hq : Nonempty (OTwoQuot F ≃* Perm (Fin 5))) (hS : IsSylowTwoOf S₀ F) (hLR : L ≤ R)
    (hRX : R ≤ X) (hR8 : L.relIndex R = 8) (hRn : S₀ ≤ Subgroup.normalizer (R : Set G)) {u : G}
    (hu : u ∈ S₀) (huQ : u ∉ pCoreOf 2 F) (hcomm : ∀ r ∈ R, u * r = r * u)
    (hrk : ∃ c ∈ X, ∀ v ∈ X, u * v * u⁻¹ * v⁻¹ ∈ L ∨ (u * v * u⁻¹ * v⁻¹) * c⁻¹ ∈ L) : False := by
  have hcs := IsModelSec.cSecIn_eq_pCoreOf h hq
  have hLX : L ≤ X := hLR.trans hRX
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ := hsd.exists_normalized hθs hθk hS
  have huF : u ∈ F := hS.1 hu
  have hu1 : Ψ ⟨u, huF⟩ ≠ 1 := by
    intro h1
    apply huQ
    rw [← hcs]
    exact (mem_cSecIn_iff_of_ker hkΨ huF).mp h1
  have huP : Ψ ⟨u, huF⟩ ∈ S5Syl := by
    rw [← hPS]
    exact ⟨⟨u, huF⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hinvR : ∀ k ∈ S₀, ∀ r ∈ R, k * r * k⁻¹ ∈ R := fun k hk r hr =>
    ((Subgroup.mem_normalizer_iff.mp (hRn hk)) r).mp hr
  obtain ⟨Y, hY, hYm⟩ := (hsd'.invariant_iff_sub hS.1 hLR hRX).mp hinvR
  have hYinv : IsInvSub orth S5Syl Y := by rw [← hPS]; exact hY
  have hYcard : Nat.card Y = 2 ^ 3 := by
    have h1 : Nat.card (Y.map β') = Nat.card Y := Subgroup.card_map_of_injective hsd'.inj
    rw [← h1, hYm]
    have hk : (QuotientGroup.mk' (L.subgroupOf X)).ker = L.subgroupOf X :=
      QuotientGroup.ker_mk' _
    rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hRX, hR8]
    norm_num
  have hYl3 : Y = l3 := eq_l3_of_invSub hYinv hYcard
  have hfixY : ∀ w ∈ Y, orth.act (Ψ ⟨u, huF⟩) w = w := by
    intro w hw
    have hmem : β' w ∈ Y.map β' := ⟨w, hw, rfl⟩
    rw [hYm] at hmem
    obtain ⟨c, hc, hcw⟩ := hmem
    have hcR : (c : G) ∈ R := Subgroup.mem_subgroupOf.mp hc
    obtain ⟨hkx, h2⟩ := hsd'.equiv ⟨u, huF⟩ w c hcw.symm
    apply hsd'.inj
    rw [h2, ← hcw]
    have e : u * (c : G) * u⁻¹ = c := by
      rw [hcomm c hcR]; group
    exact congrArg QuotientGroup.mk (Subtype.ext e)
  obtain ⟨c0, hc0X, hc0⟩ := hrk
  obtain ⟨cm, hcm⟩ := hsd'.surj (QuotientGroup.mk ⟨c0, hc0X⟩)
  have hrank : ∀ w : orth.W, orth.act (Ψ ⟨u, huF⟩) w * w⁻¹ = 1 ∨
      orth.act (Ψ ⟨u, huF⟩) w * w⁻¹ = cm := by
    intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β' w)
    obtain ⟨hax, h1⟩ := hsd'.beta_comm huF hx.symm
    rcases hc0 x x.2 with h | h
    · left
      apply hsd'.inj
      rw [h1, map_one]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)
    · right
      apply hsd'.inj
      rw [h1, hcm]
      exact (mk_eq_iff_mem.mpr h).symm
  exact orth_l3_table (Ψ ⟨u, huF⟩) ((mem_S5Syl_iff _).mp huP) hu1
    (fun w hw => hfixY w (hYl3 ▸ hw)) ⟨cm, hrank⟩

end CFSG.Quasithin.F53B3.O1
