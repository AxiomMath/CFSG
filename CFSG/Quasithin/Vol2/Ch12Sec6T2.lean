module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec6Nc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P S126T2
open scoped IsMulCommutative

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem wt_permAct (σ : Equiv.Perm (Fin 8)) (x : PermMod 8) : wt (permAct 8 σ x) = wt x := by
  unfold wt
  refine Finset.card_equiv σ⁻¹ fun i => ?_
  rw [Finset.mem_filter, Finset.mem_filter, permAct_apply]
  exact ⟨fun h => ⟨Finset.mem_univ _, h.2⟩, fun h => ⟨Finset.mem_univ _, h.2⟩⟩

omit [Finite G] in
theorem nonsing_of_wtTwo {F : Frame126 T L V} {u : G} (h : WtTwo F u) : F.Nonsing u := by
  obtain ⟨E, hu, hw⟩ := h
  exact ⟨hu, ⟨_, (E.β_eq ⟨u, hu⟩).symm, hw⟩⟩

theorem wtTwo_conj (hH : Hyp126 G T L V) {F : Frame126 T L V} {u l : G}
    (hlL : l ∈ Subgroup.normalizer (L : Set G)) (hlV : l ∈ Subgroup.normalizer (V : Set G))
    (h : WtTwo F u) : WtTwo F (l * u * l⁻¹) := by
  obtain ⟨E, hu, hw⟩ := h
  obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH hlL hlV
  have hlu : l * u * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hlV u).1 hu
  refine ⟨E, hlu, ?_⟩
  rw [E.act l hlL hlV σ hσ ⟨u, hu⟩ ⟨_, hlu⟩ rfl, coreAct_coe, wt_permAct]
  exact hw

theorem ne_one_of_nonsing {y : D8} (h : IsNonsing y) : y ≠ 1 := by
  rintro rfl
  obtain ⟨m, hm, hw⟩ := h
  rw [S126FE.mk_eq_one_iff] at hm
  rcases hm with rfl | rfl
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

theorem nonsing_e01 : IsNonsing (QuotientGroup.mk (pe 0 1) : D8) :=
  ⟨pe 0 1, rfl, by decide⟩

end S126T2

theorem theorem12_6_2_of (hD1 : Lemma12_6_3) (hD13 : Final1262) : Theorem12_6_2 := by
  classical
  intro G _ _ T L V _ F hH v hv
  by_contra hGv
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hLM : L ≤ M := Subgroup.le_normalizer
  obtain ⟨v₁, hv₁, hv₁M, hv₁c⟩ : ∃ v₁ : G, F.Nonsing v₁ ∧ ¬ Gv v₁ ≤ M ∧
      (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
        (∃ u : G, WtTwo F u ∧ ¬ Gv u ≤ M) → WtTwo F v₁) := by
    by_cases hc : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧ ∃ u : G, WtTwo F u ∧ ¬ Gv u ≤ M
    · obtain ⟨-, u, hu2, huM⟩ := hc
      exact ⟨u, nonsing_of_wtTwo hu2, huM, fun _ _ => hu2⟩
    · exact ⟨v, hv, hGv, fun hZ hex => absurd ⟨hZ, hex⟩ hc⟩
  obtain ⟨hv₁V, hv₁n⟩ := hv₁
  obtain ⟨w₀, hw₀⟩ := F.β_surj (QuotientGroup.mk (pe 0 1))
  have hex := (S126L1a.part1 F ⟨v₁, hv₁V⟩ w₀ (ne_one_of_nonsing hv₁n)
    (hw₀ ▸ ne_one_of_nonsing nonsing_e01)).2 (iff_of_true hv₁n (hw₀ ▸ nonsing_e01))
  obtain ⟨l, hlL, hlV, hlβ⟩ := hex
  set v₂ := l * v₁ * l⁻¹ with hv₂def
  have hv₂V : v₂ ∈ V := (Subgroup.mem_normalizer_iff.1 hlV v₁).1 hv₁V
  have hcoord : F.β ⟨v₂, hv₂V⟩ = QuotientGroup.mk (pe 0 1) := by
    rw [← hw₀, ← hlβ]
    congr 1
  have hv₂M : ¬ Gv v₂ ≤ M := by
    intro h
    apply hv₁M
    intro x hx
    have hx' : l * x * l⁻¹ ∈ Gv v₂ := by
      rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [hv₂def]
      calc l * x * l⁻¹ * (l * v₁ * l⁻¹) = l * (x * v₁) * l⁻¹ := by group
        _ = l * (v₁ * x) * l⁻¹ := by rw [hx]
        _ = l * v₁ * l⁻¹ * (l * x * l⁻¹) := by group
    have h1 := h hx'
    have h2 := M.mul_mem (M.mul_mem (M.inv_mem (hLM hlL)) h1) (hLM hlL)
    rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h2
  have hv₂c : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
      (∃ u : G, WtTwo F u ∧ ¬ Gv u ≤ M) → WtTwo F v₂ := fun hZ hex =>
    wtTwo_conj hH (hLM hlL) hlV (hv₁c hZ hex)
  obtain ⟨Kv, hK1, hK2, hK3, hK4, hK5⟩ := hD1 G T L V F hH v₂ hv₂V hcoord
  have hTvN : Tv T v₂ ≤ Gv v₂ ⊓ Subgroup.normalizer (Lv L v₂ : Set G) := by
    refine le_inf inf_le_right ?_
    refine le_trans ?_ (normalizer_le_normalizer_perfectCore (L ⊓ Gv v₂))
    refine (le_inf ((inf_le_left : Tv T v₂ ≤ T).trans hH.hyp.normalizes) ?_).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact (inf_le_right : Tv T v₂ ≤ Gv v₂).trans Subgroup.le_normalizer
  have hTv2 : IsPGroup 2 (Tv T v₂) := hH.hyp.sylow.1.to_le inf_le_left
  obtain ⟨P, hTvP, hP⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le hTvN hTv2
  obtain ⟨S, hPS, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf_of_le
    (hP.1.trans inf_le_left) hP.2.1
  have hSN : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ Subgroup.normalizer (Lv L v₂ : Set G))
      (Gv v₂ ⊓ Subgroup.normalizer (Lv L v₂ : Set G)) := by
    have heq := hP.eq_of_le (le_inf hPS (hP.1.trans inf_le_right))
      (inf_le_inf_right _ hS.1) (hS.2.1.to_inf_left)
    rw [heq]
    exact hP
  exact hD13 G T L V F v₂ Kv S
    ⟨hH, hv₂V, hcoord, hv₂M, hv₂c, hK1, hK2, hK3, hK4, hK5, hS, hTvP.trans hPS, hSN⟩

end CFSG.Quasithin.H13
