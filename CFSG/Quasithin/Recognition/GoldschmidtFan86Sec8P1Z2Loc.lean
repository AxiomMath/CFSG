module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalGcirc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

theorem units_sq_eq_one_unique {p : ℕ} (hp : p = 3 ∨ p = 5) (u w : (ZMod p)ˣ) (hu : u ≠ 1)
    (hu2 : u * u = 1) (hw : w ≠ 1) (hw2 : w * w = 1) : u = w := by
  rcases hp with rfl | rfl
  · revert u w; decide
  · revert u w; decide

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan40_of_fan71b {F : FanTree Γ G} (h : Fan71b F) : Fan40 F :=
  fun k hk1 hk4 hk => h.2 k hk1 (by omega) hk

theorem mem_gcirc_of_sq_eq_one {α β : V} {g : G}
    (hg : g ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) (hg2 : g * g = 1) :
    g ∈ Gcirc Γ G α β :=
  ⟨hg, by rw [hg2]; exact one_mem _⟩

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem mul_mem_nbrStab_of_sq_eq_one {v a : V} (hva : Γ.Adj v a) {z z' : G}
    (hz : z ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)
    (hz' : z' ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a)
    (hz2 : z * z = 1) (hz2' : z' * z' = 1) (hn : z ∉ nbrStab Γ G v)
    (hn' : z' ∉ nbrStab Γ G v) : z * z' ∈ nbrStab Γ G v := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hva
  have hp : pval Γ v = 3 ∨ pval Γ v = 5 := F.valence v
  let e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := ⟨z, hz⟩
  let e' : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := ⟨z', hz'⟩
  have he2 : e * e = 1 := Subtype.ext hz2
  have he2' : e' * e' = 1 := Subtype.ext hz2'
  have h1 : φ e ≠ 1 := fun h => hn ((hφ e).2 h)
  have h1' : φ e' ≠ 1 := fun h => hn' ((hφ e').2 h)
  have h2 : φ e * φ e = 1 := by rw [← map_mul, he2, map_one]
  have h2' : φ e' * φ e' = 1 := by rw [← map_mul, he2', map_one]
  have h3 := units_sq_eq_one_unique hp (φ e) (φ e') h1 h2 h1' h2'
  have h4 : φ (e * e') = 1 := by rw [map_mul, ← h3]; exact h2
  exact (hφ (e * e')).2 h4

theorem false_of_four_nbrs {c a₁ a₂ a₃ a₄ : V} (hc : pval Γ c = 3) (h₁ : Γ.Adj c a₁)
    (h₂ : Γ.Adj c a₂) (h₃ : Γ.Adj c a₃) (h₄ : Γ.Adj c a₄) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃)
    (h14 : a₁ ≠ a₄) (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄) : False := by
  have hfin := (F.ncard_neighborSet_le c).2
  have hcard : (Γ.neighborSet c).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hc
  have hsub : ({a₁, a₂, a₃, a₄} : Set V) ⊆ Γ.neighborSet c := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a₁, a₂, a₃, a₄} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13, h14]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [h23, h24]) (Set.toFinite _),
      Set.ncard_pair h34]
  have := Set.ncard_le_ncard hsub hfin
  omega

theorem exists_mem_nbrStab_smul_eq_of_valence_three (h40 : Fan40 F) {a c u u' : V}
    (hac : Γ.Adj a c) (hc : pval Γ c = 3) (hu : Γ.Adj c u) (hua : u ≠ a)
    (hu' : Γ.Adj c u') (hu'a : u' ≠ a) : ∃ k ∈ nbrStab Γ G a, k • u = u' := by
  by_cases huu : u = u'
  · exact ⟨1, one_mem _, by rw [one_smul, huu]⟩
  obtain ⟨k, hkK, hkc⟩ := Set.not_subset.1 (F.not_nbrStab_le_nbrStab h40 hac)
  have hka : k • a = a := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer a hkK)
  have hkc' : k • c = c := mem_nbrStab.1 hkK c hac
  have hadj : Γ.Adj c (k • u) := by
    have := (F.adj_smul k c u).2 hu
    rwa [hkc'] at this
  have hne_u : k • u ≠ u := fun h => hkc (F.fix_two_nbrs hac.symm hu hua.symm hka h)
  have hne_a : k • u ≠ a := fun h => hua (MulAction.injective k (h.trans hka.symm))
  refine ⟨k, hkK, ?_⟩
  by_contra hne
  exact F.false_of_four_nbrs hc hac.symm hu hu' hadj hua.symm hu'a.symm hne_a.symm huu hne_u.symm
    (Ne.symm hne)

theorem val3_of_adj_val5 {u v : V} (huv : Γ.Adj u v) (h : pval Γ u = 5) : pval Γ v = 3 := by
  have h1 := F.alternating u v huv
  have e1 : pval Γ u = Nat.card (Γ.neighborSet u) := rfl
  have e2 : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
  rcases F.valence v with h' | h' <;> omega

theorem val5_of_adj_val3 {u v : V} (huv : Γ.Adj u v) (h : pval Γ u = 3) : pval Γ v = 5 := by
  have h1 := F.alternating u v huv
  have e1 : pval Γ u = Nat.card (Γ.neighborSet u) := rfl
  have e2 : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
  rcases F.valence v with h' | h' <;> omega

theorem nbrStab_le_gcirc {α β : V} (hαβ : Γ.Adj α β) {k : G} (hk : k ∈ nbrStab Γ G α) :
    k ∈ Gcirc Γ G α β :=
  ⟨⟨F.nbrStab_le_stabilizer α hk, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk β hαβ)⟩,
    (nbrStab Γ G α).mul_mem hk hk⟩

theorem gcirc_mul_mem {α β : V} (hαβ : Γ.Adj α β) {g h : G} (hg : g ∈ Gcirc Γ G α β)
    (hh : h ∈ Gcirc Γ G α β) : g * h ∈ Gcirc Γ G α β := by
  obtain ⟨H, hH, -⟩ := F.exists_gcircSubgroup hαβ
  have hg' : g ∈ H := by rw [← SetLike.mem_coe, hH]; exact hg
  have hh' : h ∈ H := by rw [← SetLike.mem_coe, hH]; exact hh
  rw [← hH, SetLike.mem_coe]
  exact H.mul_mem hg' hh'

theorem z2_branches (h40 : Fan40 F) {a β c₁ c₂ δ δ' : V} {s : G} (ha : pval Γ a = 5)
    (haβ : Γ.Adj a β) (hc₁ : Γ.Adj a c₁) (hc₂ : Γ.Adj a c₂) (hδ : Γ.Adj c₁ δ) (hδa : δ ≠ a)
    (hδ' : Γ.Adj c₂ δ') (hδ'a : δ' ≠ a) (hs : s ∈ Gcirc Γ G a β)
    (hnot : ¬ ∃ g ∈ Gcirc Γ G a β, g • δ = δ') : c₁ ≠ c₂ ∧ c₂ ≠ s • c₁ := by
  constructor
  · rintro rfl
    obtain ⟨k, hk, hkδ⟩ := F.exists_mem_nbrStab_smul_eq_of_valence_three h40 hc₁
      (F.val3_of_adj_val5 hc₁ ha) hδ hδa hδ' hδ'a
    exact hnot ⟨k, F.nbrStab_le_gcirc haβ hk, hkδ⟩
  · intro h
    have hsa : s • a = a := MulAction.mem_stabilizer_iff.1 hs.1.1
    have hadj : Γ.Adj c₂ (s • δ) := by
      have := (F.adj_smul s c₁ δ).2 hδ
      rwa [← h] at this
    have hne : s • δ ≠ a := fun h' => hδa (MulAction.injective s (h'.trans hsa.symm))
    obtain ⟨k, hk, hkδ⟩ := F.exists_mem_nbrStab_smul_eq_of_valence_three h40 hc₂
      (F.val3_of_adj_val5 hc₂ ha) hadj hne hδ' hδ'a
    refine hnot ⟨k * s, F.gcirc_mul_mem haβ (F.nbrStab_le_gcirc haβ hk) hs, ?_⟩
    rw [mul_smul, hkδ]

end FanTree

end CFSG.Quasithin.Fan86
