module

public import CFSG.Quasithin.EmptyFaithful.FLc3Ctx
public import CFSG.Quasithin.Background.FLc3Pos

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem natural_positive {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L)
    (hML2 : mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G)) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (h : @DirectSumOfCopies ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU) (autOn L (uOf1527 Z₂ L))
      ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)) ⊥ (FFModel.nat (StatedSL n (ZMod 2))) 1) :
    IsNaturalUL L (uLOf1527 Z₂ L) ∧ Nat.card (zUOf1528 Z₂ L) = 2 := by
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hF.hU
  have hn3 : 3 ≤ n := by omega
  obtain ⟨I, π, -, -, hsup, hreal⟩ := h
  have hI0 : I ⟨0, Nat.one_pos⟩ = (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) := by
    rw [← hsup, bot_sup_eq]
    exact (iSup_unique (f := I)).symm
  have hreal0 := hreal ⟨0, Nat.one_pos⟩
  rw [hI0] at hreal0
  obtain ⟨D⟩ := FLc.vmodelNat hreal0 (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨a, ha⟩ := FLc.exists_ne_one_nat (by omega : 1 ≤ n)
  have hne : (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) ≠ ⊥ := FLc.ne_bot_of_surj D.β D.surj a ha
  have hne' : uLOf1527 Z₂ L ≠ ⊥ := fun h => hne (by rw [h, Subgroup.bot_subgroupOf])
  have hρ₀inj : Function.Injective (FLc.rhoOf π) :=
    rho_inj_of_ne_bot hF hn3 (FLc.rhoOf π) (FLc.rhoOf_surj hreal0.1) hne'
  obtain ⟨hh, -, -, -, -, hfixS⟩ :=
    normalize_rho hF hn3 (FLc.rhoOf π) (FLc.rhoOf_surj hreal0.1) (FLc.rhoOf_mem π) hne'
  have hπinj : Function.Injective π := FLc.injective_of_rhoOf_injective hρ₀inj
  have hLU := hF.LU
  let θ : ↥L →* MulAut ↥(uOf1527 Z₂ L) :=
    (conjAct (uOf1527 Z₂ L)).comp (Subgroup.inclusion hLU)
  have hθ : ∀ (l : ↥L) (v : ↥(uOf1527 Z₂ L)),
      (uOf1527 Z₂ L).subtype (θ l v) = (l : G) * (uOf1527 Z₂ L).subtype v * (l : G)⁻¹ := fun l v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (uOf1527 Z₂ L)
      (Subgroup.inclusion le_rfl (Subgroup.inclusion hLU l)) v
  have hθmem : ∀ l : ↥L, θ l ∈ autOn L (uOf1527 Z₂ L) := fun l =>
    Subgroup.mem_map.2 ⟨⟨(l : G), hLU l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hHθ : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ l : ↥L, θ l = k := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, hxk⟩
  have key := FLc.isNaturalSection_of_realizes (uOf1527 Z₂ L).subtype Subtype.val_injective θ hθ hθmem hHθ
    hπinj hreal0
  have hmap : ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)).map (uOf1527 Z₂ L).subtype = uLOf1527 Z₂ L :=
    Subgroup.map_subgroupOf_eq_of_le hF.ULU
  rw [hmap] at key
  have hzUU : zUOf1528 Z₂ L ≤ uOf1527 Z₂ L := hF.ZUle.trans hF.ULU
  have hcardle : Nat.card (zUOf1528 Z₂ L) ≤ 2 := by
    let W : Subgroup ↥(uOf1527 Z₂ L) := (zUOf1528 Z₂ L).subgroupOf (uOf1527 Z₂ L)
    have hWU : W ≤ (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) := fun w hw =>
      Subgroup.mem_subgroupOf.2 (hF.ZUle (Subgroup.mem_subgroupOf.1 hw))
    have h2 := FLc.card_le_two_of_ut_fixed (by omega : 1 ≤ n) (D.rtwist hh) hWU
      (fun w hw s hs => hfixS s hs w (Subgroup.mem_subgroupOf.1 hw))
    have e : Nat.card ↥W = Nat.card ↥(zUOf1528 Z₂ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzUU).toEquiv
    omega
  have hzne : zUOf1528 Z₂ L ≠ ⊥ := by
    intro hz
    apply hF.MLne
    have hnb : Subgroup.normalizer (((⊥ : Subgroup G)) : Set G) = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true]
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro hx
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [← e, hx]
        group
    rw [hML2, hz, hnb]
    exact inf_top_eq L
  have hcard1 : Nat.card (zUOf1528 Z₂ L) ≠ 1 := fun h1 => hzne (Subgroup.card_eq_one.1 h1)
  have hcard0 : 0 < Nat.card (zUOf1528 Z₂ L) := Nat.card_pos
  exact ⟨⟨n, hn, key⟩, by omega⟩

theorem input15128Natural_holds : Input15128Natural := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hns hML2 hoff
  have hF := facts_of_ctx hc
  obtain ⟨hU, halt⟩ := hc.h27
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hU
  have hU2 : ∀ a ∈ uOf1527 Z₂ L, a ^ 2 = 1 := hU.2
  have hV2 : ∀ w : ↥(uOf1527 Z₂ L), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hU2 w w.2)
  rcases halt with ⟨Z, hZ1, -, h⟩ | h | h | ⟨n, hn, k, hk1, hkn, h⟩
  · exact (ctx_excl hF (FLc.excl_ext4 hV2 (fun z hz => (hZ1 hz).1) h) hoff).elim
  · exact (ctx_excl hF (FLc.excl_ext5 hV2 h) hoff).elim
  · exact absurd ⟨hU, h⟩ hns
  · by_cases hk : k = 1
    · subst hk
      exact natural_positive hF hML2 hn h
    · exact (ctx_excl hF (FLc.excl_nat2 hV2 (by omega) (by omega) h) hoff).elim

end CFSG.Quasithin
