module

public import CFSG.Timmesfeld.Bridge.RootStructThmD
public import CFSG.Timmesfeld.Bridge.RootSetsRankOne

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

private theorem map_conj_subgroupOf_eq {C X : Subgroup G} (hXC : X ≤ C) (c : C) :
    (X.subgroupOf C).map (MulAut.conj c).toMonoidHom =
      (X.map (MulAut.conj (c : G)).toMonoidHom).subgroupOf C := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hXC hx⟩, hx, Subtype.ext (by simpa using hxy)⟩

theorem oneOpposite_symm (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {b x : G} (hb : b ∈ D) (hx : x ∈ D) (hodd : Odd (orderOf (b * x)))
    (h : OneOpposite D b x) : OneOpposite D x b := by
  obtain ⟨e, he, hbe, hbeD, h4⟩ := h
  have hb2 := hD.mul_self_eq_one hb
  have hx2 := hD.mul_self_eq_one hx
  set σ := dihedralSwap b x
  have h1 : σ * b * σ⁻¹ = x := dihedralSwap_conj hb2 hx2 hodd
  have h2 : σ * x * σ⁻¹ = b := dihedralSwap_conj' hb2 hx2 hodd
  refine ⟨σ * e * σ⁻¹, conj_mem_of_isClass hclass σ he, ?_, ?_, ?_⟩
  · rw [← h1]
    exact (Commute.conj_iff σ).2 hbe
  · rw [← h1, show σ * b * σ⁻¹ * (σ * e * σ⁻¹) = σ * (b * e) * σ⁻¹ by group]
    exact conj_mem_of_isClass hclass σ hbeD
  · rw [← h2, show σ * x * σ⁻¹ * (σ * e * σ⁻¹) = σ * (x * e) * σ⁻¹ by group, orderOf_conj_eq]
    exact h4

theorem OneOpposite.of_mem_rootSet (hD : IsRootInvolutionSet D) {b x x' : G} (hx : x ∈ D)
    (hx' : x' ∈ rootSet D x) (h : OneOpposite D b x) : OneOpposite D b x' := by
  obtain ⟨e, he, hbe, hbeD, h4⟩ := h
  exact ⟨e, he, hbe, hbeD, (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx' he).2 h4⟩

theorem moufangPair_of_oneOpposite (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hQ : Moufang.CommLambda D) {b x : G} (hb : b ∈ D) (hx : x ∈ D) (hbx : ¬ Commute b x)
    (hodd : Odd (orderOf (b * x))) (h1 : OneOpposite D b x) : MoufangPair D x b := by
  have hD := h.root
  have hoddxb : Odd (orderOf (x * b)) := by rwa [orderOf_mul_comm_eq]
  have h2 := oneOpposite_symm h.isClass hD hb hx hodd h1
  refine ⟨fun x' hx' => ?_, fun b' hb' => ?_⟩
  · obtain ⟨hodd', hnc⟩ :=
      odd_orderOf_mul_of_mem_rootSet hD hx hb hx' (mem_rootSet_self hb) hoddxb
        (fun h' => hbx h'.symm)
    exact exists_orderOf_mul_eq_three_of_oneOpposite h hc hs hQ hb hx'.1 hnc hodd'
      (h1.of_mem_rootSet hD hx hx')
  · obtain ⟨hodd', hnc⟩ :=
      odd_orderOf_mul_of_mem_rootSet hD hb hx hb' (mem_rootSet_self hx) hodd hbx
    obtain ⟨x', hx', h3⟩ := exists_orderOf_mul_eq_three_of_oneOpposite h hc hs hQ hx hb'.1 hnc
      hodd' (h2.of_mem_rootSet hD hb hb')
    exact ⟨x', hx', (orderOf_mul_comm_eq b' x').trans h3⟩

theorem isElemAbRankOne_of_moufangPair [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) {d c : G} (hd : d ∈ D) (hcD : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hM : MoufangPair D d c) :
    IsElemAbRankOne ((rootGroup D d).subgroupOf (rootGroup D d ⊔ rootGroup D c))
      ((rootGroup D c).subgroupOf (rootGroup D d ⊔ rootGroup D c)) := by
  set X := rootGroup D d ⊔ rootGroup D c
  have hAX : rootGroup D d ≤ X := le_sup_left
  have hBX : rootGroup D c ≤ X := le_sup_right
  have hcd : ¬ Commute c d := fun h => hdc h.symm
  have hoddcd : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hAX hBX, Subgroup.subgroupOf_self]
  · intro heq
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hAX, inf_eq_left.2 hBX] at heq
    exact rootGroup_ne_of_opposite hclass hd hcD hdc heq
  · intro a ha a' ha'
    exact Subtype.ext (commute_of_mem_rootGroup hd ha ha').eq
  · intro a ha
    exact Subtype.ext (mul_self_eq_one_of_mem_rootGroup hD hd ha)
  · intro a ha ha1
    have ha1' : (a : G) ≠ 1 := fun h' => ha1 (Subtype.ext h')
    have haT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hd ha ha1'
    obtain ⟨b, hb, h3⟩ := hM.1 a haT
    refine ⟨⟨b, hBX (rootSet_subset_rootGroup D c hb)⟩, rootSet_subset_rootGroup D c hb,
      fun h' => hD.ne_one hb.1 (congrArg Subtype.val h'), ?_⟩
    rw [map_conj_subgroupOf_eq hAX, map_conj_subgroupOf_eq hBX]
    exact congrArg (fun H => H.subgroupOf X)
      ((map_conj_rootGroup_eq_iff_of_mem hclass hD hd hcD hdc hodd haT hb).2 h3)
  · intro b hb hb1
    have hb1' : (b : G) ≠ 1 := fun h' => hb1 (Subtype.ext h')
    have hbT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcD hb hb1'
    obtain ⟨a, ha, h3⟩ := hM.2 b hbT
    refine ⟨⟨a, hAX (rootSet_subset_rootGroup D d ha)⟩, rootSet_subset_rootGroup D d ha,
      fun h' => hD.ne_one ha.1 (congrArg Subtype.val h'), ?_⟩
    rw [map_conj_subgroupOf_eq hBX, map_conj_subgroupOf_eq hAX]
    exact congrArg (fun H => H.subgroupOf X)
      ((map_conj_rootGroup_eq_iff_of_mem hclass hD hd hcD hdc hodd ha hbT).2 h3).symm

theorem exists_mulEquiv_SL2_of_oneOpposite {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hQ : Moufang.CommLambda D) {b x : G} (hb : b ∈ D)
    (hx : x ∈ D)
    (hbx : ¬ Commute b x) (hodd : Odd (orderOf (b * x))) (h1 : OneOpposite D b x)
    (hq : 4 ≤ Nat.card (rootGroup D b)) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D b)) = 2 ^ n ∧
      ∃ φ : ↥(rootGroup D x ⊔ rootGroup D b) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D b)).map φ.toMonoidHom =
            upperUnipotent (GaloisField 2 n) ∧
          ((rootGroup D b).subgroupOf (rootGroup D x ⊔ rootGroup D b)).map φ.toMonoidHom =
            lowerUnipotent (GaloisField 2 n) := by
  have := h.finite
  have hD := h.root
  have hxb : ¬ Commute x b := fun h' => hbx h'.symm
  have hoddxb : Odd (orderOf (x * b)) := by rwa [orderOf_mul_comm_eq]
  have hR := isElemAbRankOne_of_moufangPair h.isClass hD hc hx hb hxb hoddxb
    (moufangPair_of_oneOpposite h hc hs hQ hb hx hbx hodd h1)
  refine rankOne_mulEquiv_SL2 hR ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    card_rootGroup_eq h.isClass hD hc hb hx]
  exact hq

end CFSG.Timmesfeld.Bridge
