module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
import CFSG.CGT.Timmesfeld75.Core214Proof

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n : ℕ}

private noncomputable def autRestrict {X : Type} [Group X] {O : Subgroup X}
    (f : MulAut X) (hf : O.map (f : X →* X) = O) : MulAut O :=
  (Subgroup.equivMapOfInjective O (f : X →* X) f.injective).trans
    (MulEquiv.subgroupCongr hf)

private theorem autRestrict_coe {X : Type} [Group X] {O : Subgroup X}
    (f : MulAut X) (hf : O.map (f : X →* X) = O) (z : O) :
    (autRestrict f hf z : X) = f z := rfl

private theorem eq_of_agree_on_sup {X : Type} [Group X] {Y O : Subgroup X} [O.Normal]
    (hsup : Y ⊔ O = ⊤) {f g : MulAut X}
    (hY : ∀ y ∈ Y, f y = g y) (hO : ∀ z ∈ O, f z = g z) : f = g := by
  ext x
  have hx : x ∈ (↑(Y ⊔ O) : Set X) := by rw [hsup, Subgroup.coe_top]; trivial
  rw [Subgroup.mul_normal] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  rw [map_mul, map_mul, hY y hy, hO z hz]

private theorem units_mul_self_eq_one_iff {p : ℕ} [Fact p.Prime] (x : (ZMod p)ˣ) :
    x * x = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have h' : (x : ZMod p) * (x : ZMod p) = 1 := by
      simpa using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by simpa using h1))
  · rintro (rfl | rfl) <;> simp

theorem Shape166.exists_eq_conj_of_index_two
    (hY : IsElemAbelian 2 Y) (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y n)
    (hn1 : n = 1) (hPrime : (Nat.card (fusionOddCore X)).Prime)
    (α : MulAut X) (hα : α * α = 1) (hαY : ∀ y ∈ Y, α y = y) :
    ∃ y ∈ Y, α = MulAut.conj y := by
  obtain ⟨hcardY0, hcase | hcase⟩ := hX
  · exact absurd (hn1 ▸ hcase.1) (lt_irrefl 1)
  have hsup : Y ⊔ fusionOddCore X = ⊤ := hcase.2.1
  have hcardY : Nat.card Y = 2 := by rw [hcardY0, hn1]; norm_num
  have hOddO : Odd (Nat.card (fusionOddCore X)) :=
    CFSG.CGT.Timmesfeld75.odd_card_fusionOddCore X
  obtain ⟨tY, htY⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 (by rw [hcardY])
  let t : X := tY
  have ht_mem : t ∈ Y := tY.2
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_coe, htY]
  have hYzp : Subgroup.zpowers t = Y := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr ht_mem
    · rw [Nat.card_zpowers, ht, hcardY]
  have hnoncent : ¬ (∀ z ∈ fusionOddCore X, t * z * t⁻¹ = z) := by
    intro hcent
    have hYnormal : Y.Normal := by
      rw [Subgroup.normal_iff_map_conj_eq]
      intro g
      have hg : g ∈ (↑(Y ⊔ fusionOddCore X) : Set X) := by
        rw [hsup, Subgroup.coe_top]; trivial
      rw [Subgroup.mul_normal, Set.mem_mul] at hg
      obtain ⟨y0, hy0, z0, hz0, rfl⟩ := hg
      have hzu : ∀ u ∈ Y, z0 * u * z0⁻¹ = u := by
        intro u hu
        have hu' : u ∈ Subgroup.zpowers t := hYzp ▸ hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
        have htzz : t * z0 = z0 * t := by
          have h := hcent z0 hz0
          calc t * z0 = (t * z0 * t⁻¹) * t := by group
            _ = z0 * t := by rw [h]
        have hzt : z0 * t * z0⁻¹ = t := by
          rw [← htzz]; group
        calc z0 * t ^ j * z0⁻¹ = MulAut.conj z0 (t ^ j) := by rw [MulAut.conj_apply]
          _ = (MulAut.conj z0 t) ^ j := by rw [map_zpow]
          _ = t ^ j := by rw [MulAut.conj_apply, hzt]
      have hle : Y.map (MulAut.conj (y0 * z0)) ≤ Y := by
        rintro w ⟨u, hu, rfl⟩
        change (y0 * z0) * u * (y0 * z0)⁻¹ ∈ Y
        have hzu' : z0 * u * z0⁻¹ = u := hzu u hu
        have hy0u : y0 * u = u * y0 :=
          congrArg Subtype.val (hY.1.is_comm.comm ⟨y0, hy0⟩ ⟨u, hu⟩)
        have hcalc : (y0 * z0) * u * (y0 * z0)⁻¹ = y0 * u * y0⁻¹ := by
          calc (y0 * z0) * u * (y0 * z0)⁻¹ = y0 * (z0 * u * z0⁻¹) * y0⁻¹ := by group
            _ = y0 * u * y0⁻¹ := by rw [hzu']
        rw [hcalc]
        have : y0 * u * y0⁻¹ = u := by rw [hy0u]; group
        rw [this]
        exact hu
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq
        (Subgroup.card_map_of_injective (K := Y)
          (MulAut.conj (y0 * z0)).injective).symm)
    have hYtop : Y = ⊤ := by
      have h := hgen
      rw [Subgroup.normalClosure_eq_self Y] at h
      exact h
    have hOleY : fusionOddCore X ≤ Y := by rw [hYtop]; exact le_top
    have hdvd : Nat.card (fusionOddCore X) ∣ Nat.card Y := Subgroup.card_dvd_of_le hOleY
    rw [hcardY] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact hPrime.ne_one h
    · rw [h] at hOddO
      norm_num at hOddO
  have hαOmap : (fusionOddCore X).map (α : X →* X) = fusionOddCore X := by
    have hle : (fusionOddCore X).map (α : X →* X) ≤ fusionOddCore X :=
      le_sSup ⟨(fusionOddCore_normal X).map (α : X →* X) α.surjective,
        by rw [Subgroup.card_map_of_injective (K := fusionOddCore X) α.injective]
           exact hOddO⟩
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (K := fusionOddCore X) α.injective).symm)
  have hτOmap : (fusionOddCore X).map (MulAut.conj t : X →* X) = fusionOddCore X :=
    Subgroup.Normal.map_conj_eq (H := fusionOddCore X) t
  haveI : Fact (Nat.card (fusionOddCore X)).Prime := ⟨hPrime⟩
  haveI : IsCyclic (fusionOddCore X) := isCyclic_of_prime_card (α := fusionOddCore X) rfl
  have hαOsq : autRestrict α hαOmap * autRestrict α hαOmap = 1 := by
    ext z
    show (α : X →* X) ((α : X →* X) (z : X)) = (z : X)
    have h := congrArg (fun β : MulAut X => β (z : X)) hα
    simpa using h
  have ht2 : t * t = 1 := by rw [← pow_two]; exact hY.2 t ht_mem
  have hconj2 : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← map_mul, ht2, map_one]
  have hτOsq :
      autRestrict (MulAut.conj t) hτOmap * autRestrict (MulAut.conj t) hτOmap = 1 := by
    ext z
    show (MulAut.conj t) ((MulAut.conj t) (z : X)) = (z : X)
    have h := congrArg (fun β : MulAut X => β (z : X)) hconj2
    simpa using h
  have hτ_ne : autRestrict (MulAut.conj t) hτOmap ≠ 1 := by
    intro h
    apply hnoncent
    intro z hz
    have hz' := congrArg (fun w : fusionOddCore X => (w : X))
      (congrArg (fun β : MulAut (fusionOddCore X) => β ⟨z, hz⟩) h)
    simpa [autRestrict_coe, MulAut.conj_apply] using hz'
  let e := IsCyclic.mulAutMulEquiv (fusionOddCore X)
  have hxα2 : e (autRestrict α hαOmap) * e (autRestrict α hαOmap) = 1 := by
    rw [← map_mul, hαOsq, map_one]
  have hxτ2 : e (autRestrict (MulAut.conj t) hτOmap) *
      e (autRestrict (MulAut.conj t) hτOmap) = 1 := by
    rw [← map_mul, hτOsq, map_one]
  have hxτ_ne : e (autRestrict (MulAut.conj t) hτOmap) ≠ 1 := by
    intro h
    exact hτ_ne (e.injective (by rw [h, map_one]))
  have hxα : e (autRestrict α hαOmap) = 1 ∨ e (autRestrict α hαOmap) = -1 :=
    (units_mul_self_eq_one_iff _).mp hxα2
  have hxτ : e (autRestrict (MulAut.conj t) hτOmap) = 1 ∨
      e (autRestrict (MulAut.conj t) hτOmap) = -1 :=
    (units_mul_self_eq_one_iff _).mp hxτ2
  have hxτ_eq : e (autRestrict (MulAut.conj t) hτOmap) = -1 := by
    rcases hxτ with h | h
    · exact absurd h hxτ_ne
    · exact h
  have hαOcases : autRestrict α hαOmap = 1 ∨
      autRestrict α hαOmap = autRestrict (MulAut.conj t) hτOmap := by
    rcases hxα with h | h
    · left
      exact e.injective (by rw [h, map_one])
    · right
      exact e.injective (by rw [h, hxτ_eq])
  rcases hαOcases with h1 | h2
  · have hfixO : ∀ z ∈ fusionOddCore X, α z = z := by
      intro z hz
      have hz' := congrArg (fun w : fusionOddCore X => (w : X))
        (congrArg (fun β : MulAut (fusionOddCore X) => β ⟨z, hz⟩) h1)
      simpa [autRestrict_coe] using hz'
    have hα_eq_one : α = 1 := eq_of_agree_on_sup (g := 1) hsup hαY hfixO
    refine ⟨1, Y.one_mem, ?_⟩
    rw [hα_eq_one, map_one]
  · have hfixO : ∀ z ∈ fusionOddCore X, α z = t * z * t⁻¹ := by
      intro z hz
      have hz' := congrArg (fun w : fusionOddCore X => (w : X))
        (congrArg (fun β : MulAut (fusionOddCore X) => β ⟨z, hz⟩) h2)
      simpa [autRestrict_coe, MulAut.conj_apply] using hz'
    have hfixO' : ∀ z ∈ fusionOddCore X, α z = MulAut.conj t z := by
      intro z hz
      rw [hfixO z hz, MulAut.conj_apply]
    have hconjY : ∀ y ∈ Y, MulAut.conj t y = y := by
      intro y hy
      rw [MulAut.conj_apply]
      have hy0 : y * t = t * y :=
        congrArg Subtype.val (hY.1.is_comm.comm ⟨y, hy⟩ ⟨t, ht_mem⟩)
      calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [hy0]
        _ = y := by group
    refine ⟨t, ht_mem, ?_⟩
    exact eq_of_agree_on_sup hsup (fun y hy => by rw [hαY y hy, hconjY y hy]) hfixO'

end CFSG.LocalAnalysis.WeakClosure81

end
