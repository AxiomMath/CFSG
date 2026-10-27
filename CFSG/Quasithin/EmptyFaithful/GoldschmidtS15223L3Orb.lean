module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2V2Lift
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.C2Eleven
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_oPrimeResidualOf_of_le {Y Y' : Subgroup G} {g : G}
    (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y') {x : G} (hx : x ∈ oPrimeResidualOf 3 Y) :
    g * x * g⁻¹ ∈ oPrimeResidualOf 3 Y' := by
  unfold oPrimeResidualOf at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxY, k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨hg x hxY, k, ?_⟩
    rw [C2Eleven.orderOf_conj_eq]
    exact hk
  | one => simp
  | mul a b _ _ ha hb => simpa [mul_assoc] using mul_mem ha hb
  | inv a _ ha => simpa [mul_assoc] using inv_mem ha

theorem not_le_of_perfect {I S X Mc K : Subgroup G} (hOrb : A3Orbits G) (hsq : IsSQTKIn I)
    (hS : IsSylowTwoOf S I) (hX : X ∈ cComp I) (hSMc : S ≤ Mc)
    (hP1 : ∀ Y : Subgroup G, GenByOrderThree Y → Y ≤ I →
      I ≤ Subgroup.normalizer (Y : Set G) → Y ≤ Mc → ¬ Y ≤ K → quasithinV2 Y = ⊥)
    (hKsolv : Group.IsSolvable ↥K) (hgen : GenByOrderThree X)
    (hns : ¬ Group.IsSolvable ↥X) (hV2 : quasithinV2 X ≠ ⊥) : ¬ X ≤ Mc := by
  intro hXMc
  have hres : X = oPrimeResidualOf 3 X := hgen.eq_oPrimeResidualOf
  have hXI : X ≤ I := le_of_mem_cComp hX
  have horb := (hOrb I S X hsq hS hX).1
  have hconj : ∀ g ∈ I, ∃ s ∈ S, conjByElt g X = conjByElt s X := fun g hg => by
    have : conjByElt g X ∈ conjSubgroupsBy I X := ⟨g, hg, rfl⟩
    rw [horb] at this
    obtain ⟨s, hs, hse⟩ := this
    exact ⟨s, hs, hse⟩
  have hmemc : ∀ g ∈ I, ∀ x ∈ X, g * x * g⁻¹ ∈ conjByElt g X := fun g hg x hx => by
    rw [mem_conjByElt]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]
    exact hx
  set X₀ := conjClosure X I with hX₀
  have hX₀I : X₀ ≤ I := conjClosure_le fun g hg x hx =>
    I.mul_mem (I.mul_mem hg (hXI hx)) (I.inv_mem hg)
  have hIN : I ≤ Subgroup.normalizer (X₀ : Set G) := le_normalizer_conjClosure X I
  have hXX₀ : X ≤ X₀ := le_conjClosure X I
  have hX₀Mc : X₀ ≤ Mc := conjClosure_le fun g hg x hx => by
    obtain ⟨s, hs, hgs⟩ := hconj g hg
    have h1 : g * x * g⁻¹ ∈ conjByElt s X := hgs ▸ hmemc g hg x hx
    have h2 : s⁻¹ * (g * x * g⁻¹) * s ∈ X := mem_conjByElt.mp h1
    have h3 : s * (s⁻¹ * (g * x * g⁻¹) * s) * s⁻¹ ∈ Mc :=
      Mc.mul_mem (Mc.mul_mem (hSMc hs) (hXMc h2)) (Mc.inv_mem (hSMc hs))
    simpa [mul_assoc] using h3
  have hX₀N : X₀ ≤ Subgroup.normalizer (X : Set G) := conjClosure_le fun g hg x hx =>
    le_normalizer_of_mem_cComp (L₁ := X) (L₂ := conjByElt g X) hX
      (map_conj_mem_cComp hX hg) (hmemc g hg x hx)
  have hgen' : GenByOrderThree X₀ := genByOrderThree_conjClosure hgen
  have hXK : ¬ X₀ ≤ K := by
    intro h
    exact hns (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (hXX₀.trans h) : Function.Injective
        (Subgroup.inclusion (hXX₀.trans h))))
  have hV := hP1 X₀ hgen' hX₀I hIN hX₀Mc hXK
  exact quasithinV2_ne_bot_of_normal hres hXX₀ hX₀N hV2 hV

end CFSG.Quasithin.S15223
