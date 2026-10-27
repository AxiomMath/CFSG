module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
public import CFSG.OddTranspositions.PartThree.Ten.SwapImage
public import CFSG.OddTranspositions.PartThree.Ten.SwapBlocks
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.PartThree.Ten.SingletonBlock
import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 SemidirectProduct

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
@[expose] def tenBlockImage (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (β : Set G) : Set (L2Wreath f n) :=
  tenHom hC e '' {x : Halpha D hC.alpha | (x : G) ∈ β}

omit [Finite G] in
theorem mem_tenBlockImage_iff (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    {β : Set G} {w : L2Wreath f n} :
    w ∈ tenBlockImage hC e β ↔ ∃ z : Halpha D hC.alpha, (z : G) ∈ β ∧ tenHom hC e z = w :=
  Iff.rfl

theorem isSwapBlock_tenBlockImage (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f) (hn : 5 ≤ n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    SwapBlocks.IsSwapBlock (tenBlockImage hC e β) := by
  have hSodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  refine ⟨?_, ?_⟩
  · rw [← tenHom_image_DstarH hC hf hn e]
    exact Set.image_mono fun x hx => subset_DalphaStar hβ hx
  · intro w b hb hwb
    obtain ⟨x, hx, rfl⟩ := (mem_tenBlockImage_iff hC e).1 hb
    obtain ⟨h, rfl⟩ := tenHom_surjective hC e w
    obtain ⟨y, hy, hyq⟩ := (mem_tenBlockImage_iff hC e).1 hwb
    have hxS : x ∈ DstarH hC := subset_DalphaStar hβ hx
    have heq : y = h * x * h⁻¹ :=
      eq_of_tenHom_eq hC e hQ (hSodd.mul_self_eq_one (subset_DalphaStar hβ hy))
        (hSodd.mul_self_eq_one (DstarH_conj_mem hC hxS))
        (by rw [hyq, map_mul, map_mul, map_inv])
    have hmem : (h : G) * x * (h : G)⁻¹ ∈ β := by
      have : ((h * x * h⁻¹ : Halpha D hC.alpha) : G) ∈ β := heq ▸ hy
      exact this
    have hclaim := conj_mem_iff_of_conj_image_eq (conj_image_eq_of_mem hC h.2 hβ hx hmem)
    rw [SwapBlocks.mem_conjStab]
    intro x'
    simp only [mem_tenBlockImage_iff]
    constructor
    · rintro ⟨z', hz', hz'q⟩
      refine ⟨h⁻¹ * z' * h, (hclaim ((h⁻¹ * z' * h : Halpha D hC.alpha) : G)).1 ?_, ?_⟩
      · rw [show (h : G) * ((h⁻¹ * z' * h : Halpha D hC.alpha) : G) * (h : G)⁻¹ = z' by
          simp [mul_assoc]]
        exact hz'
      · rw [map_mul, map_mul, map_inv, hz'q]
        group
    · rintro ⟨z, hz, hzq⟩
      exact ⟨h * z * h⁻¹, (hclaim z).2 hz, by rw [map_mul, map_mul, map_inv, hzq]⟩

theorem false_of_tenBlockImage_eq_singleton (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f)
    (hn : 5 ≤ n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥)
    (hnot : ¬ hC.alpha ⊆ (Halpha D hC.alpha : Set G)) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {v' : Halpha D hC.alpha} (hv' : (v' : G) ∈ β)
    (hB1 : tenBlockImage hC e β = {tenHom hC e v'}) : False := by
  have hSodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  have hsing : β = {(v' : G)} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hv', fun x hx => ?_⟩
    have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hx⟩
    have hmem : tenHom hC e ⟨x, hxH⟩ ∈ tenBlockImage hC e β :=
      (mem_tenBlockImage_iff hC e).2 ⟨⟨x, hxH⟩, hx, rfl⟩
    rw [hB1, Set.mem_singleton_iff] at hmem
    exact congrArg Subtype.val (eq_of_tenHom_eq hC e hQ
      (hSodd.mul_self_eq_one (subset_DalphaStar hβ hx))
      (hSodd.mul_self_eq_one (subset_DalphaStar hβ hv')) hmem)
  exact false_of_alpha_eq_singleton hC hf hn e hQ hnot
    (alpha_eq_singleton_of_mem_Dalpha hC hβ hsing)

theorem false_of_tenBlockImage_eq_swapSet (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f)
    (hn : 5 ≤ n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥)
    (hnot : ¬ hC.alpha ⊆ (Halpha D hC.alpha : Set G)) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hB3 : tenBlockImage hC e β = WreathEndgame.swapSet f n) : False := by
  have hSodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  refine hnot (alpha_subset_Halpha hC hβ fun γ hγ => ?_)
  obtain ⟨x, hx⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
  have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨γ, hγ, hx⟩
  have hxS : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈ DstarH hC := subset_DalphaStar hγ hx
  have hmem : tenHom hC e ⟨x, hxH⟩ ∈ WreathEndgame.swapSet f n := by
    rw [← tenHom_image_DstarH hC hf hn e]
    exact Set.mem_image_of_mem _ hxS
  rw [← hB3] at hmem
  obtain ⟨y, hy, hyq⟩ := (mem_tenBlockImage_iff hC e).1 hmem
  have hyx : y = ⟨x, hxH⟩ :=
    eq_of_tenHom_eq hC e hQ (hSodd.mul_self_eq_one (subset_DalphaStar hβ hy))
      (hSodd.mul_self_eq_one hxS) hyq
  have hxβ : x ∈ β := by
    rw [hyx] at hy
    exact hy
  rcases eq_or_disjoint_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ.1 hβ.1 with h | h
  · exact h
  · exact absurd hxβ (Set.disjoint_left.1 h hx)

theorem eq_conj_of_tenBlockImage_eq_sameSwaps (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {v' : Halpha D hC.alpha} (hv' : (v' : G) ∈ β) {i j : Fin n} (hij : i ≠ j)
    (hB2 : tenBlockImage hC e β = WreathEndgame.sameSwaps f n (Equiv.swap i j)) :
    β = {x | ∃ l ∈ tenBase hC e, x = l * (v' : G) * l⁻¹} := by
  have hSodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  have hsB : tenHom hC e v' ∈ tenBlockImage hC e β :=
    (mem_tenBlockImage_iff hC e).2 ⟨v', hv', rfl⟩
  rw [hB2] at hsB
  obtain ⟨a, ha⟩ : ∃ a, tenHom hC e v' = WreathEndgame.swp a i j :=
    ⟨_, WreathEndgame.eq_swp_of_right_eq hsB.1 hij hsB.2⟩
  have hv'S : v' ∈ DstarH hC := subset_DalphaStar hβ hv'
  ext x
  constructor
  · intro hx
    have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hx⟩
    have hxS : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈ DstarH hC := subset_DalphaStar hβ hx
    have hmem : tenHom hC e ⟨x, hxH⟩ ∈ tenBlockImage hC e β :=
      (mem_tenBlockImage_iff hC e).2 ⟨⟨x, hxH⟩, hx, rfl⟩
    rw [hB2] at hmem
    obtain ⟨c, hc⟩ : ∃ c, tenHom hC e ⟨x, hxH⟩ = WreathEndgame.swp c i j :=
      ⟨_, WreathEndgame.eq_swp_of_right_eq hmem.1 hij hmem.2⟩
    set y₀ : Fin n → CFSG.Theory.Comparator.PSL2Model f := Pi.mulSingle i (c * a⁻¹) with hy₀
    have hy₀conj : inl y₀ * tenHom hC e v' * (inl y₀)⁻¹ = tenHom hC e ⟨x, hxH⟩ := by
      rw [ha, hc, SwapBlocks.inl_conj_swp y₀ a hij]
      congr 1
      simp [hy₀, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm]
    obtain ⟨l₀, hl₀⟩ := tenHom_surjective hC e (inl y₀)
    refine ⟨(l₀ : G), ⟨l₀, ⟨y₀, hl₀.symm⟩, rfl⟩, ?_⟩
    have hl₀v : l₀ * v' * l₀⁻¹ = ⟨x, hxH⟩ :=
      eq_of_tenHom_eq hC e hQ (hSodd.mul_self_eq_one (DstarH_conj_mem hC hv'S))
        (hSodd.mul_self_eq_one hxS) (by rw [map_mul, map_mul, map_inv, hl₀, hy₀conj])
    exact (congrArg Subtype.val hl₀v).symm
  · rintro ⟨l, ⟨l₀, hl₀, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hl₀
    have hy' : inl y = tenHom hC e l₀ := hy
    have hconj : tenHom hC e (l₀ * v' * l₀⁻¹) = WreathEndgame.swp (y i * a * (y j)⁻¹) i j := by
      rw [map_mul, map_mul, map_inv, ← hy', ha, SwapBlocks.inl_conj_swp y a hij]
    have hmem : tenHom hC e (l₀ * v' * l₀⁻¹) ∈ tenBlockImage hC e β := by
      rw [hB2]
      exact ⟨by rw [hconj]; exact WreathEndgame.swp_mem hij, by rw [hconj]; rfl⟩
    obtain ⟨z, hz, hzq⟩ := (mem_tenBlockImage_iff hC e).1 hmem
    have hzeq : z = l₀ * v' * l₀⁻¹ :=
      eq_of_tenHom_eq hC e hQ (hSodd.mul_self_eq_one (subset_DalphaStar hβ hz))
        (hSodd.mul_self_eq_one (DstarH_conj_mem hC hv'S)) hzq
    rw [hzeq] at hz
    exact hz

theorem tenThree_of_tenTwo (h2 : TenTwo) : TenThree := by
  intro G _ _ D hC f n hT e β hβ v hv
  obtain ⟨hQ, hnot⟩ := h2 G D hC f n hT
  have hf := hT.two_le
  have hn := hT.five_le
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hv⟩
  have hBblock := isSwapBlock_tenBlockImage hC hf hn e hQ hβ
  have hsB : tenHom hC e ⟨v, hvH⟩ ∈ tenBlockImage hC e β :=
    (mem_tenBlockImage_iff hC e).2 ⟨⟨v, hvH⟩, hv, rfl⟩
  obtain ⟨i, j, hij, hsr, -⟩ := hBblock.subset hsB
  rcases SwapBlocks.swap_block_trichotomy hf hn hBblock hsB hij hsr with hB1 | hB2 | hB3
  · exact (false_of_tenBlockImage_eq_singleton hC hf hn e hQ hnot hβ (v' := ⟨v, hvH⟩) hv hB1).elim
  · exact eq_conj_of_tenBlockImage_eq_sameSwaps hC e hQ hβ (v' := ⟨v, hvH⟩) hv hij hB2
  · exact (false_of_tenBlockImage_eq_swapSet hC hf hn e hQ hnot hβ hB3).elim

end CFSG.OddTranspositions.PartThree

end
