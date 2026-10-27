module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row21Key
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row21Sl2
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Stellmacher.L3YC

namespace Row21

theorem contra_of_natural {K : Type} [Group K] [Finite K] {N Lb : Subgroup K} [N.Normal]
    (hLbN : Lb ≤ N) (hcard : Nat.card Lb = 336)
    (hsup : N = Lb ⊔ (CFSG.oddCore ↥N).map N.subtype)
    (hnat : NaturalSL2Action 7 ↥N (CFSG.fittingSubgroup ↥N))
    (hFO : CFSG.fittingSubgroup ↥N = CFSG.oddCore ↥N)
    {ē g : K} (hēL : ē ∈ Lb) (hē3 : orderOf ē = 3) (hgē : g * ē = ē * g)
    (hg : g ∉ Subgroup.normalizer (Lb : Set K)) : False := by
  classical
  obtain ⟨e, ψ, hsurj, hker, hact⟩ := hnat
  have hkerψ : ∀ x : ↥N, ψ x = 1 ↔ x ∈ CFSG.fittingSubgroup ↥N := fun x => by
    rw [← MonoidHom.mem_ker, hker]
  have hBcard : Nat.card (Lb.subgroupOf N) = 336 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLbN).toEquiv
  have hsup' : Lb.subgroupOf N ⊔ CFSG.fittingSubgroup ↥N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLbN, hFO, ← hsup,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfact : ∀ x : ↥N, ∃ b ∈ Lb.subgroupOf N, ∃ v ∈ CFSG.fittingSubgroup ↥N, x = b * v := by
    intro x
    have hx : x ∈ Lb.subgroupOf N ⊔ CFSG.fittingSubgroup ↥N := hsup' ▸ Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    exact ⟨y, hy, z, hz, hyz.symm⟩
  let φ : ↥(Lb.subgroupOf N) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
    ψ.comp (Lb.subgroupOf N).subtype
  have hφsurj : Function.Surjective φ := by
    intro m
    obtain ⟨n, rfl⟩ := hsurj m
    obtain ⟨b, hb, v, hv, rfl⟩ := hfact n
    refine ⟨⟨b, hb⟩, ?_⟩
    show ψ b = ψ (b * v)
    rw [map_mul, (hkerψ v).mpr hv, mul_one]
  have hφinj : Function.Injective φ :=
    (hφsurj.bijective_of_nat_card_le (by rw [hBcard, card_sl2_seven])).1
  have hBF : ∀ x ∈ Lb.subgroupOf N, x ∈ CFSG.fittingSubgroup ↥N → x = 1 := by
    intro x hxB hxF
    have : φ ⟨x, hxB⟩ = φ 1 := by
      show ψ x = ψ 1
      rw [map_one]
      exact (hkerψ x).mpr hxF
    exact congrArg Subtype.val (hφinj this)
  have hodd : Odd (Nat.card (CFSG.fittingSubgroup ↥N)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
    decide
  obtain ⟨zb, hzb⟩ := hφsurj (-1)
  have hψz : ψ (zb : ↥N) = -1 := hzb
  have hzc : ∀ b ∈ Lb.subgroupOf N, (zb : ↥N) * b = b * (zb : ↥N) := by
    intro b hb
    have : φ (zb * ⟨b, hb⟩) = φ (⟨b, hb⟩ * zb) := by
      rw [map_mul, map_mul, hzb]
      exact Row21.neg_one_mul _
    exact congrArg Subtype.val (hφinj this)
  have hz2 : (zb : ↥N) * zb = 1 := by
    have : φ (zb * zb) = φ 1 := by
      rw [map_mul, hzb, map_one]
      exact Row21.neg_one_mul_neg_one
    exact congrArg Subtype.val (hφinj this)
  have hzinv : ∀ v ∈ CFSG.fittingSubgroup ↥N, (zb : ↥N) * v * (zb : ↥N)⁻¹ = v⁻¹ := by
    intro v hv
    have h := hact zb ⟨v, hv⟩
    rw [hψz, Row21.neg_mulVec] at h
    have h2 : e (MulAut.conjNormal (zb : ↥N) ⟨v, hv⟩) = e (⟨v, hv⟩ : CFSG.fittingSubgroup ↥N)⁻¹ := by
      rw [h, ofAdd_neg, ofAdd_toAdd, map_inv]
      rfl
    exact congrArg Subtype.val (e.injective h2)
  let e0 : ↥N := ⟨ē, hLbN hēL⟩
  have he0B : e0 ∈ Lb.subgroupOf N := hēL
  have he03 : e0 ^ 3 = 1 := by
    refine Subtype.ext ?_
    show ē ^ 3 = 1
    rw [← hē3]
    exact pow_orderOf_eq_one ē
  have he0ne : e0 ≠ 1 := by
    intro h
    have : ē = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hē3
    omega
  have hψe3 : ψ e0 ^ 3 = 1 := by rw [← map_pow, he03, map_one]
  have hψe1 : ψ e0 ≠ 1 := fun h => he0ne (by
    have : φ ⟨e0, he0B⟩ = φ 1 := by
      show ψ e0 = ψ 1
      rw [map_one]
      exact h
    exact congrArg Subtype.val (hφinj this))
  have hec : ∀ v ∈ CFSG.fittingSubgroup ↥N, e0 * v * e0⁻¹ = v → v = 1 := by
    intro v hv hcv
    have h := hact e0 ⟨v, hv⟩
    have hc : MulAut.conjNormal e0 ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext hcv
    rw [hc] at h
    have hw : ((ψ e0 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :
        Matrix (Fin 2) (Fin 2) (ZMod 7)) *ᵥ Multiplicative.toAdd (e ⟨v, hv⟩) =
        Multiplicative.toAdd (e ⟨v, hv⟩) := by
      have := congrArg Multiplicative.toAdd h
      simpa using this.symm
    have h0 := Row21.three_no_fixed (ψ e0) hψe3 hψe1 _ hw
    have h1 : e ⟨v, hv⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h0
    have h2 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2
  let α : ↥N →* ↥N := (MulAut.conjNormal g : MulAut ↥N).toMonoidHom
  have hαe : α e0 = e0 := by
    refine Subtype.ext ?_
    show g * ē * g⁻¹ = ē
    rw [hgē, mul_inv_cancel_right]
  have hψα : ψ (α zb) = -1 := by
    have hα2 : α zb * α zb = 1 := by rw [← map_mul, hz2, map_one]
    have h1 : ψ (α zb) * ψ (α zb) = 1 := by rw [← map_mul, hα2, map_one]
    rcases Row21.sq_eq_one _ h1 with h | h
    · exfalso
      have hαF : α zb ∈ CFSG.fittingSubgroup ↥N := (hkerψ _).mp h
      have h3 : α zb = 1 :=
        Row21.eq_one_of_sq_eq_one hodd hαF (by rw [pow_two]; exact hα2)
      have hz1 : (zb : ↥N) = 1 :=
        (MulAut.conjNormal g : MulAut ↥N).injective (h3.trans (map_one (MulAut.conjNormal g : MulAut ↥N)).symm)
      rw [hz1, map_one] at hψz
      exact Row21.neg_one_ne_one hψz.symm
    · exact h
  have hαz : (zb : ↥N)⁻¹ * α zb ∈ CFSG.fittingSubgroup ↥N :=
    (hkerψ _).mp (by rw [map_mul, map_inv, hψz, hψα, inv_mul_cancel])
  have key := Row21.map_mem_of_odd_complement (V := CFSG.fittingSubgroup ↥N)
    (B := Lb.subgroupOf N) hodd hfact hBF hzc hzinv he0B hec α hαe hαz
  refine hg (Subgroup.mem_normalizer_fintype fun a ha => ?_)
  exact key ⟨a, hLbN ha⟩ ha

end Row21

end Stellmacher.L3YC

end CFSG.Quasithin
