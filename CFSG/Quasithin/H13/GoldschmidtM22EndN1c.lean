module

public import CFSG.Quasithin.Background.G6Basic
public import CFSG.Quasithin.H13.GoldschmidtM22EndN1b

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem isSwap_of_sq_fin3 (σ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h2 : σ * σ = 1) :
    σ.IsSwap := by
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → σ.support.card = 2 := by decide
  exact Equiv.Perm.card_support_eq_two.mp (key σ h1 h2)

omit [Finite G] in
theorem mem_zpowers_involution {X : Type*} [Group X] {p : X} (hp : p * p = 1) {x : X}
    (hx : x ∈ Subgroup.zpowers p) : x = 1 ∨ x = p := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hp, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hp, one_zpow, one_mul]

section Main

variable [Fact (IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T))]
  (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
  (h6210 : Stmt6_2_10) (hZS : ch6ZS T L V = V ⊓ UU T L V)
  (z₀ : G) (hz₀ : z₀ ∈ ch6ZS T L V) (hz₀Z : z₀ ∉ quasithinOmegaOneCenter T)
  (hw : ∀ (z : G) (hz : z ∈ ch6ZS T L V),
    zt T L V z hz = 1 ∨ zt T L V z hz = zt T L V z₀ hz₀)
  (a : ↥(HH T)) (haV : (a : G) ∈ V) (ha1 : rep T L V a ≠ 1)

include h hZS h6210 hw haV ha1 in
theorem commV_rep_eq : commV (Subgroup.zpowers (rep T L V a)) =
    Subgroup.zpowers (zt T L V z₀ hz₀) := by
  have hform := rep_form h h6210 hZS z₀ hz₀ hw a haV
  have ha2 : rep T L V a * rep T L V a = 1 := by
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      simpa [pow_two] using h.toHyp611.isElemAbelian.2 (a : G) haV)
    rw [this, map_one]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    rcases mem_zpowers_involution ha2 hx with rfl | rfl
    · simp
    · rcases hform v with h1 | h1
      · rw [h1, mul_inv_cancel]; exact Subgroup.one_mem _
      · rw [h1, mul_comm v, mul_inv_cancel_right]; exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    obtain ⟨v, hv⟩ : ∃ v, rep T L V a v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact ha1 (MulEquiv.ext hcon)
    have h1 : rep T L V a v = v * zt T L V z₀ hz₀ := (hform v).resolve_left hv
    exact Subgroup.subset_closure ⟨rep T L V a, Subgroup.mem_zpowers _, v, by
      rw [h1, mul_comm v, mul_inv_cancel_right]⟩

include h hw in
omit hZS h6210 haV ha1 in
theorem span_rep :
    G6.submoduleClosure (rep T L V).range (Subgroup.zpowers (zt T L V z₀ hz₀)) = ⊤ := by
  set S := G6.submoduleClosure (rep T L V).range (Subgroup.zpowers (zt T L V z₀ hz₀)) with hS
  have hmem : ∀ y : ↥(HH T), ∀ q ∈ Subgroup.zpowers (zt T L V z₀ hz₀), rep T L V y q ∈ S :=
    fun y q hq => Subgroup.mem_iSup_of_mem (rep T L V y)
      (Subgroup.mem_iSup_of_mem ⟨y, rfl⟩ ⟨q, hq, rfl⟩)
  have hQ : ∀ g : G, g ∈ UU T L V → ∃ hg : g ∈ UU T L V, tmk T L V ⟨g, hg⟩ ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hp : y * z * y⁻¹ ∈ UU T L V := mem_conjClosure hy hz
      refine ⟨hp, ?_⟩
      have e : tmk T L V ⟨y * z * y⁻¹, hp⟩ = rep T L V ⟨y, hy⟩ (zt T L V z hz) := by
        rw [zt, rep_mk]
        congr 1
      rcases hw z hz with h1 | h1
      · rw [e, h1, map_one]
        exact S.one_mem
      · rw [e, h1]
        exact hmem _ _ (Subgroup.mem_zpowers _)
    | one =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      have : tmk T L V ⟨1, Subgroup.one_mem _⟩ = 1 := (tmk_eq_one_iff _).mpr (Subgroup.one_mem _)
      rw [this]
      exact S.one_mem
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx', ihx'⟩ := ihx
      obtain ⟨hy', ihy'⟩ := ihy
      refine ⟨Subgroup.mul_mem _ hx' hy', ?_⟩
      have : tmk T L V ⟨x * y, Subgroup.mul_mem _ hx' hy'⟩ =
          tmk T L V ⟨x, hx'⟩ * tmk T L V ⟨y, hy'⟩ :=
        tmk_mul (⟨x, hx'⟩ : ↥(UU T L V)) ⟨y, hy'⟩
      rw [this]
      exact S.mul_mem ihx' ihy'
    | inv x hx ihx =>
      obtain ⟨hx', ihx'⟩ := ihx
      refine ⟨Subgroup.inv_mem _ hx', ?_⟩
      have : tmk T L V ⟨x⁻¹, Subgroup.inv_mem _ hx'⟩ = (tmk T L V ⟨x, hx'⟩)⁻¹ :=
        tmk_inv (⟨x, hx'⟩ : ↥(UU T L V))
      rw [this]
      exact S.inv_mem ihx'
  refine top_unique fun q _ => ?_
  obtain ⟨u, rfl⟩ := Sec.mk_surjective (UU T L V) (quasithinOmegaOneCenter T) q
  obtain ⟨hg, hg'⟩ := hQ u.1 u.2
  exact hg'

include h hZ hZS h6210 hz₀Z hw haV ha1 in
theorem normalizer_V_of_rep_comm (h629 : Stmt6_2_9) (c : ↥(HH T))
    (hc : rep T L V c * rep T L V a = rep T L V a * rep T L V c) :
    (c : G) ∈ Subgroup.normalizer (V : Set G) := by
  have hform := rep_form h h6210 hZS z₀ hz₀ hw a haV
  have hw1 : zt T L V z₀ hz₀ ≠ 1 := fun h1 => hz₀Z ((tmk_eq_one_iff _).mp h1)
  obtain ⟨v, hv⟩ : ∃ v, rep T L V a v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact ha1 (MulEquiv.ext hcon)
  have h1 : rep T L V a v = v * zt T L V z₀ hz₀ := (hform v).resolve_left hv
  have hfix : rep T L V c (zt T L V z₀ hz₀) = zt T L V z₀ hz₀ := by
    have hzv : zt T L V z₀ hz₀ = rep T L V a v * v⁻¹ := by
      rw [h1, mul_comm v, mul_inv_cancel_right]
    have hc' : rep T L V c (rep T L V a v) = rep T L V a (rep T L V c v) := by
      have := congrArg (fun φ : MulAut (Ut T L V) => φ v) hc
      simpa using this
    have e1 : rep T L V c (zt T L V z₀ hz₀) =
        rep T L V a (rep T L V c v) * (rep T L V c v)⁻¹ := by
      conv_lhs => rw [hzv]
      rw [map_mul, map_inv, hc']
    rcases hform (rep T L V c v) with h2 | h2
    · exfalso
      rw [h2, mul_inv_cancel] at e1
      apply hw1
      have : rep T L V c (zt T L V z₀ hz₀) = rep T L V c 1 := by rw [e1, map_one]
      exact (rep T L V c).injective this
    · rw [e1, h2, mul_comm (rep T L V c v), mul_inv_cancel_right]
  have hN := mem_normalizer_ZS_of_fix h hZ z₀ hz₀ hw c hfix
  exact HH_inf_normalizer_ZS_le h h629 ⟨c.2, hN⟩

end Main

end CFSG.Quasithin.H13.GM22
