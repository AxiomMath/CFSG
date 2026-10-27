module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.Timmesfeld.Bridge.Asc72Local
import CFSG.Timmesfeld.Bridge.Asc72BenderInvolution
import CFSG.Timmesfeld.Bridge.Asc72LocalImage
import CFSG.OddTranspositions.PartThree.Ten.Assembly
import CFSG.OddTranspositions.PartThree.Ten.SwapBlocks
import CFSG.OddTranspositions.PartThree.Ten.SwapKlein
import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoWreath
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 WreathEndgame
open CFSG.BenderSuzuki
open Equiv SemidirectProduct

variable {f m : ℕ}

private theorem swp_three (s u t : PSL2Model f) {i j : Fin m} (hij : i ≠ j)
    (huu : u * u = 1) (htu : Commute t u) :
    swp (t * s) i j * swp (t * u * s) i j * swp s i j = swp (u * s) i j := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have htueq : t * u = u * t := htu.eq
  have h1 : t * s * (t * u * s)⁻¹ = u := by
    rw [mul_inv_rev, mul_inv_rev, huinv]
    calc t * s * (s⁻¹ * (u * t⁻¹)) = t * (u * t⁻¹) := by group
      _ = t * u * t⁻¹ := by group
      _ = u * t * t⁻¹ := by rw [htueq]
      _ = u := by group
  have h2 : (t * s)⁻¹ * (t * u * s) * s⁻¹ = (u * s)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, huinv]
    group
  refine SemidirectProduct.ext (funext fun l => ?_) ?_
  · by_cases hli : l = i
    · subst hli
      rw [SwapKlein.swp_mul_swp_mul_swp_left_fst (t * s) (t * u * s) s hij,
        swp_left_fst hij, h1]
    · by_cases hlj : l = j
      · subst hlj
        rw [SwapKlein.swp_mul_swp_mul_swp_left_snd (t * s) (t * u * s) s hij,
          swp_left_snd hij]
        exact h2
      · rw [SwapKlein.swp_mul_swp_mul_swp_left_of_ne (t * s) (t * u * s) s hli hlj,
          swp_left_of_ne hli hlj]
  · rw [SemidirectProduct.mul_right, SwapKlein.swp_mul_swp_right (t * s) (t * u * s),
      swp_right, swp_right, one_mul]

private theorem conj_swp_mem_commSet {S : Set (L2Wreath f m)}
    (hS : ∀ g, ∀ x ∈ S, g * x * g⁻¹ ∈ S) {a c : L2Wreath f m} {i j : Fin m} (hij : i ≠ j)
    {s u t : PSL2Model f} (ha : a = swp (u * s) i j) (hc : c = swp s i j) (hcS : c ∈ S)
    (htt : t * t = 1) (huu : u * u = 1) (ht1 : t ≠ 1) (htu : t ≠ u)
    (htucomm : Commute t u) :
    swp (t * s) i j ∈ commSet (centSet S c) a ∧
      swp (t * u * s) i j ∈ commSet (centSet S c) a := by
  let g1 : L2Wreath f m := inl (Pi.mulSingle i t)
  let b1 : L2Wreath f m := g1 * c * g1⁻¹
  let g2 : L2Wreath f m := inl (Pi.mulSingle i (t * u))
  let b2 : L2Wreath f m := g2 * c * g2⁻¹
  have hb1_eq : b1 = swp (t * s) i j := by
    dsimp only [b1, g1]; rw [hc, SwapBlocks.inl_conj_swp (Pi.mulSingle i t) s hij]
    simp [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm]
  have hb2_eq : b2 = swp (t * u * s) i j := by
    dsimp only [b2, g2]; rw [hc, SwapBlocks.inl_conj_swp (Pi.mulSingle i (t * u)) s hij]
    simp [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have htu2 : (t * u) * (t * u) = 1 := by
    rw [show (t * u) * (t * u) = t * (u * t) * u by group, ← htucomm.eq,
      show t * (t * u) * u = (t * t) * (u * u) by group, htt, huu, mul_one]
  have hb1c : Commute b1 c := by
    rw [hb1_eq, hc]
    exact (SwapKlein.commute_swp_swp_iff (t * s) s hij).2
      (by rw [show (t * s) * s⁻¹ = t by group]; exact htt)
  have hb1a : Commute b1 a := by
    rw [hb1_eq, ha]
    exact (SwapKlein.commute_swp_swp_iff (t * s) (u * s) hij).2
      (by rw [show (t * s) * (u * s)⁻¹ = t * u by rw [mul_inv_rev, huinv]; group]; exact htu2)
  have hb2c : Commute b2 c := by
    rw [hb2_eq, hc]
    exact (SwapKlein.commute_swp_swp_iff (t * u * s) s hij).2
      (by rw [show (t * u * s) * s⁻¹ = t * u by group]; exact htu2)
  have hb2a : Commute b2 a := by
    rw [hb2_eq, ha]
    exact (SwapKlein.commute_swp_swp_iff (t * u * s) (u * s) hij).2
      (by rw [show (t * u * s) * (u * s)⁻¹ = t by
            rw [mul_inv_rev, huinv]
            rw [show t * u * s * (s⁻¹ * u) = t * (u * u) by group, huu, mul_one]]; exact htt)
  have hb1_ne_a : b1 ≠ a := fun h => htu (mul_right_cancel
    (SwapKlein.swp_injective _ _ hij (hb1_eq.symm.trans (h.trans ha))))
  have hb2_ne_a : b2 ≠ a := fun h => ht1 <| by
    simpa [mul_assoc, huinv, huu] using congrArg (fun x : PSL2Model f => x * u⁻¹)
      (mul_right_cancel (SwapKlein.swp_injective _ _ hij (hb2_eq.symm.trans (h.trans ha))))
  rw [← hb1_eq, ← hb2_eq]
  exact ⟨⟨⟨hS g1 c hcS, hb1c⟩, hb1a, hb1_ne_a⟩, ⟨⟨hS g2 c hcS, hb2c⟩, hb2a, hb2_ne_a⟩⟩

private theorem sameSwaps_mem_aux {S : Set (L2Wreath f m)}
    (hS : ∀ g, ∀ x ∈ S, g * x * g⁻¹ ∈ S) {a c : L2Wreath f m} {i j : Fin m} (hij : i ≠ j)
    {s u t : PSL2Model f} (ha : a = swp (u * s) i j) (hc : c = swp s i j) (hcS : c ∈ S)
    (htt : t * t = 1) (huu : u * u = 1) (ht1 : t ≠ 1) (htu : t ≠ u)
    (htucomm : Commute t u) (hac : a ≠ c) (hcomm : Commute a c) :
    a ∈ Subgroup.closure (commSet (centSet S c) a) := by
  obtain ⟨hb1mem, hb2mem⟩ := conj_swp_mem_commSet hS hij ha hc hcS htt huu ht1 htu htucomm
  have hcmem : c ∈ commSet (centSet S c) a :=
    ⟨⟨hcS, Commute.refl c⟩, hcomm.symm, hac.symm⟩
  have hprod : swp (t * s) i j * swp (t * u * s) i j * c = a := by
    rw [hc, ha]
    exact swp_three s u t hij huu htucomm
  have hprodmem : swp (t * s) i j * swp (t * u * s) i j * c ∈
      Subgroup.closure (commSet (centSet S c) a) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hb1mem)
      (Subgroup.subset_closure hb2mem)) (Subgroup.subset_closure hcmem)
  rwa [hprod] at hprodmem

theorem mem_closure_commSet_centSet_sameSwaps {f m : ℕ} (hf : 2 ≤ f) {τ : Equiv.Perm (Fin m)}
    {S : Set (L2Wreath f m)} (hS : ∀ g, ∀ x ∈ S, g * x * g⁻¹ ∈ S) {a c : L2Wreath f m}
    (ha : a ∈ sameSwaps f m τ) (hc : c ∈ sameSwaps f m τ) (hcS : c ∈ S) (hac : a ≠ c)
    (hcomm : Commute a c) : a ∈ Subgroup.closure (commSet (centSet S c) a) := by
  obtain ⟨i, j, hij, har, -⟩ := ha.1
  have hτ : τ = swap i j := by rw [← ha.2, har]
  have hcr : c.right = swap i j := by rw [hc.2, hτ]
  have ha0 : a = swp (a.left i) i j := eq_swp_of_right_eq ha.1 hij har
  have hc0 : c = swp (c.left i) i j := eq_swp_of_right_eq hc.1 hij hcr
  set s : PSL2Model f := c.left i
  set u : PSL2Model f := a.left i * s⁻¹ with hu
  have hcomm' : Commute (swp (a.left i) i j) (swp s i j) := by rw [← ha0, ← hc0]; exact hcomm
  have huu : u * u = 1 := (SwapKlein.commute_swp_swp_iff (a.left i) s hij).1 hcomm'
  have hu1 : u ≠ 1 := by
    intro h
    apply hac
    have hai : a.left i = s := mul_inv_eq_one.mp h
    rw [ha0, hc0, hai]
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
  obtain ⟨t, ht2, htu, htucomm⟩ :=
    IsBenderGroup.exists_involution_commute_ne
      (IsBenderGroup.isPSL2 f hf (MulEquiv.refl _)) hu2
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have has : a.left i = u * s := by rw [hu]; group
  have ha_eq : a = swp (u * s) i j := by rw [ha0, has]
  have hc_eq : c = swp s i j := hc0
  exact sameSwaps_mem_aux hS hij ha_eq hc_eq hcS htt huu ht1 htu htucomm.symm hac hcomm

private theorem mem_closure_of_image_mem {X Y : Type*} [Group X] [Group Y] (Φ : X ≃* Y)
    {E : Set X} {a c : X}
    (h : Φ a ∈ Subgroup.closure (commSet (centSet (Φ '' E) (Φ c)) (Φ a))) :
    a ∈ Subgroup.closure (commSet (centSet E c) a) := by
  have hcent : ∀ u : X, u ∈ centSet E c ↔ Φ u ∈ centSet (Φ '' E) (Φ c) :=
    fun u => by rw [centSet_image]; exact (Φ.injective.mem_set_image).symm
  have hcommimage : commSet (centSet (Φ '' E) (Φ c)) (Φ a) =
      Φ '' commSet (centSet E c) a :=
    WreathEndgame.commSet_map Φ hcent a
  have hmap : Subgroup.closure (commSet (centSet (Φ '' E) (Φ c)) (Φ a)) =
      (Subgroup.closure (commSet (centSet E c) a)).map (Φ : X →* Y) := by
    rw [hcommimage, WreathEndgame.closure_image_mulEquiv]
    rfl
  have hmem : Φ a ∈ (Subgroup.closure (commSet (centSet E c) a)).map (Φ : X →* Y) := by
    rw [← hmap]
    exact h
  exact (Subgroup.mem_map_iff_mem Φ.injective).1 hmem

private theorem wreath_key_image
    {X : Type} [Group X] [Finite X] {E : Set X} (hY : HypothesisC E)
    {f m : ℕ} (hf : 2 ≤ f) (Φ : X ≃* L2Wreath f m)
    (hΦS : ∀ u ∈ E, Φ u ∈ swapSet f m) (hiff : ∀ x, x ∈ E ↔ Φ x ∈ swapSet f m)
    {a c : X} (ha : a ∈ hY.alpha) (hc : c ∈ hY.alpha) (hac : a ≠ c) (hcomm : Commute a c) :
    Φ a ∈ Subgroup.closure (commSet (centSet (Φ '' E) (Φ c)) (Φ a)) := by
  classical
  have hB : SwapBlocks.IsSwapBlock (Φ '' hY.alpha) :=
    isSwapBlock_image Φ hiff hY.isBlock_alpha
  have haD : a ∈ E := hY.isBlock_alpha.subset ha
  have hcD : c ∈ E := hY.isBlock_alpha.subset hc
  have hnot1 : Φ '' hY.alpha ≠ {Φ a} := by
    intro h
    have : Φ c ∈ ({Φ a} : Set (L2Wreath f m)) := h ▸ ⟨c, hc, rfl⟩
    rw [Set.mem_singleton_iff] at this
    exact hac (Φ.injective this).symm
  have hnotall : Φ '' hY.alpha ≠ swapSet f m := by
    intro h
    apply hY.isBlock_alpha.ne_univ
    refine Set.Subset.antisymm hY.isBlock_alpha.subset fun x hx => ?_
    have hmem : Φ x ∈ Φ '' hY.alpha := h ▸ (hiff x).1 hx
    obtain ⟨y, hy, hyx⟩ := hmem
    exact Φ.injective hyx ▸ hy
  have hS : ∀ g, ∀ x ∈ Φ '' E, g * x * g⁻¹ ∈ Φ '' E := by
    intro g x hx
    obtain ⟨u, huE, rfl⟩ := hx
    refine ⟨Φ.symm g * u * (Φ.symm g)⁻¹, hY.setup.normal _ u huE, ?_⟩
    simp
  have hkey_of_same {i j : Fin m} (hij : i ≠ j) (haR : (Φ a).right = swap i j)
      (hcR : (Φ c).right = swap i j) :
      Φ a ∈ Subgroup.closure (commSet (centSet (Φ '' E) (Φ c)) (Φ a)) := by
    refine mem_closure_commSet_centSet_sameSwaps hf hS ⟨hΦS a haD, haR⟩
      ⟨hΦS c hcD, hcR⟩ ⟨c, hcD, rfl⟩ (fun h => hac (Φ.injective h)) ?_
    exact hcomm.map Φ
  obtain ⟨i, j, hij, har, -⟩ := hΦS a haD
  rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | rfl | hm5
  · have h01 : ∀ i j : Fin 2, i ≠ j → swap i j = swap 0 1 := by decide
    refine hkey_of_same (i := 0) (j := 1) (by decide) ?_ ?_
    · rw [har, h01 i j hij]
    · obtain ⟨i', j', hij', hcr, -⟩ := hΦS c hcD
      rw [hcr, h01 i' j' hij']
  · exact (false_of_three_four hY.setup hY.conn (Or.inl rfl) Φ hΦS).elim
  · exact (false_of_three_four hY.setup hY.conn (Or.inr rfl) Φ hΦS).elim
  · have hus : Φ a ∈ Φ '' hY.alpha := ⟨a, ha, rfl⟩
    rcases SwapBlocks.swap_block_trichotomy hf hm5 hB hus hij har with h | h | h
    · exact absurd h hnot1
    · have hcB : Φ c ∈ Φ '' hY.alpha := ⟨c, hc, rfl⟩
      exact hkey_of_same hij (h ▸ hus).2 (h ▸ hcB).2
    · exact absurd h hnotall

theorem mem_closure_commSet_centSet_of_blockKernel_ne_bot
    {X : Type} [Group X] [Finite X] {E : Set X}
    (hY : HypothesisC E) (hrad : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥)
    (hK : blockKernel hY.alpha ≠ ⊥) {a c : X} (ha : a ∈ hY.alpha) (hc : c ∈ hY.alpha)
    (hac : a ≠ c) (hcomm : Commute a c) :
    a ∈ Subgroup.closure (commSet (centSet E c) a) := by
  classical
  obtain ⟨f, m, hf, Φ, hΦ⟩ := exists_l2Wreath_class_of_blockKernel_ne_bot hY hrad hK
  have hΦS : ∀ u ∈ E, Φ u ∈ swapSet f m := fun u hu => hΦ u hu
  have hm2 : 2 ≤ m := two_le_of_mem_swapSet (hΦS hY.d hY.hd)
  have hiff : ∀ x, x ∈ E ↔ Φ x ∈ swapSet f m := mem_D_iff_mem_swapSet hY.setup hm2 Φ hΦS
  exact mem_closure_of_image_mem Φ (wreath_key_image hY hf Φ hΦS hiff ha hc hac hcomm)

end CFSG.OddTranspositions.PartThree.ElevenThree
