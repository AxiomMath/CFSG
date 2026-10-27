module

public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Lifting a centralizing Klein four across an odd central kernel
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A Klein four in a quotient by an odd central subgroup has a Klein-four
lift. If the quotient subgroup centralizes the image of `A`, the lift
centralizes `A` itself. -/
public theorem exists_kleinFour_lift_centralizing_of_odd_central_kernel
    {E : Type u} [Group E] [Finite E]
    (Z A : Subgroup E) [Z.Normal]
    (hZodd : Odd (Nat.card Z))
    (hZcent : Z ≤ Subgroup.center E)
    (Vbar : Subgroup (E ⧸ Z))
    (hVK : IsKleinFour Vbar)
    (hVcent : Vbar ≤ Subgroup.centralizer
      (A.map (QuotientGroup.mk' Z) : Set (E ⧸ Z))) :
    ∃ V : Subgroup E, IsKleinFour V ∧
      V.map (QuotientGroup.mk' Z) = Vbar ∧
      V ≤ Subgroup.centralizer (A : Set E) := by
  classical
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  let L : Subgroup E := Vbar.comap q
  have hZleL : Z ≤ L := by
    intro z hz
    change q z ∈ Vbar
    rw [show q z = 1 by exact (QuotientGroup.eq_one_iff (N := Z) z).2 hz]
    exact Vbar.one_mem
  let N : Subgroup L := Z.subgroupOf L
  have hNnormal : N.Normal := by
    exact (inferInstance : Z.Normal).subgroupOf L
  let : N.Normal := hNnormal
  let f : L →* Vbar :=
    (q.comp L.subtype).codRestrict Vbar (fun x => x.2)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z y
    have hxL : x ∈ L := by
      change q x ∈ Vbar
      rw [show q x = (y : E ⧸ Z) by simpa [q] using hx]
      exact y.2
    refine ⟨⟨x, hxL⟩, ?_⟩
    apply Subtype.ext
    change q x = (y : E ⧸ Z)
    exact hx
  have hker : f.ker = N := by
    ext x
    constructor
    · intro hx
      apply Subgroup.mem_subgroupOf.mpr
      apply (QuotientGroup.eq_one_iff (N := Z) (x : E)).mp
      exact congrArg Subtype.val hx
    · intro hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := Z) (x : E)).mpr
        (Subgroup.mem_subgroupOf.mp hx)
  have hNindex : N.index = 4 := by
    rw [← hker, Subgroup.index_ker]
    have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hfsurj
    rw [hrange]
    simpa using hVK.card_four
  have hNcard : Nat.card N = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleL).toEquiv
  have hNodd : Odd (Nat.card N) := by simpa [hNcard] using hZodd
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNindex]
    exact (Nat.coprime_two_right.mpr hNodd).pow_right 2
  obtain ⟨W, hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hWcard : Nat.card W = 4 := by
    rw [← hcomp.symm.index_eq_card, hNindex]
  have hWinfN : W ⊓ N = ⊥ := hcomp.disjoint.symm.eq_bot
  have hfWinj : Function.Injective (f.comp W.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff (f.comp W.subtype)).mp
    apply le_bot_iff.mp
    intro x hx
    have hxN : (x : L) ∈ N := by
      rw [← hker]
      exact hx
    have hxInf : (x : L) ∈ W ⊓ N := ⟨x.2, hxN⟩
    rw [hWinfN] at hxInf
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxInf
  have hfrange : (f.comp W.subtype).range = W.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eWrange : W ≃* (f.comp W.subtype).range :=
    MulEquiv.ofBijective (f.comp W.subtype).rangeRestrict
      ⟨fun x y hxy => hfWinj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective (f.comp W.subtype)⟩
  have hWmapcard : Nat.card (W.map f) = Nat.card W := by
    rw [← hfrange]
    exact (Nat.card_congr eWrange.toEquiv).symm
  have hWmap : W.map f = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hWmapcard, hWcard, hVK.card_four]
  have hfWsurj : Function.Surjective (f.comp W.subtype) := by
    intro y
    have hy : (y : Vbar) ∈ W.map f := by
      rw [hWmap]
      exact Subgroup.mem_top y
    rcases Subgroup.mem_map.mp hy with ⟨x, hxW, hxy⟩
    refine ⟨⟨x, hxW⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  let eW : W ≃* Vbar :=
    MulEquiv.ofBijective (f.comp W.subtype) ⟨hfWinj, hfWsurj⟩
  have hWK : IsKleinFour W := {
    card_four := hWcard
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eW).trans hVK.exponent_two
  }
  let V : Subgroup E := W.map L.subtype
  have hVLcard : Nat.card V = Nat.card W :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hVKL : IsKleinFour V := {
    card_four := by rw [hVLcard, hWcard]
    exponent_two := by
      let eVL : W ≃* V := Subgroup.equivMapOfInjective W L.subtype
        L.subtype_injective
      exact (Monoid.exponent_eq_of_mulEquiv eVL).symm.trans hWK.exponent_two
  }
  refine ⟨V, hVKL, ?_, ?_⟩
  · change (W.map L.subtype).map q = Vbar
    rw [Subgroup.map_map]
    have hfcomp : q.comp L.subtype = Vbar.subtype.comp f := by
      ext x
      rfl
    rw [hfcomp, ← Subgroup.map_map, hWmap,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · intro v hv
    rcases Subgroup.mem_map.mp hv with ⟨w, hwW, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hwbar : (f w : E ⧸ Z) ∈ Vbar := (f w).2
    have hacent := (Subgroup.mem_centralizer_iff.mp (hVcent hwbar))
      (q a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    have hfw : (f w : E ⧸ Z) = q (w : E) := by rfl
    rw [hfw] at hacent
    have hqcomm : q (w : E) * q a = q a * q (w : E) := by
      exact hacent.symm
    let z : E := (w : E) * a * (w : E)⁻¹ * a⁻¹
    have hzZ : z ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) z).mp
      change q ((w : E) * a * (w : E)⁻¹ * a⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hqcomm]
      group
    have hw2L : (w : L) ^ 2 = 1 := by
      simpa [pow_two] using
        congrArg Subtype.val (hWK.mul_self (⟨w, hwW⟩ : W))
    have hw2 : (w : E) ^ 2 = 1 := congrArg Subtype.val hw2L
    have hzcenter : z ∈ Subgroup.center E := hZcent hzZ
    have hzcommw : z * (w : E) = (w : E) * z :=
      (Subgroup.mem_center_iff.mp hzcenter (w : E)).symm
    have hzinv : (w : E)⁻¹ = (w : E) := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_two] using hw2
    have hconj : (w : E) * a * (w : E)⁻¹ = z * a := by
      dsimp [z]
      group
    have hmul : (w : E) * (w : E) = 1 := by
      simpa [pow_two] using hw2
    have haeq : a = z ^ 2 * a := by
      calc
        a = (w : E) * ((w : E) * a * (w : E)⁻¹) * (w : E)⁻¹ := by
          symm
          rw [hzinv]
          calc
            (w : E) * ((w : E) * a * (w : E)) * (w : E) =
                ((w : E) * (w : E)) * a * ((w : E) * (w : E)) := by group
            _ = a := by rw [hmul]; simp
        _ = (w : E) * (z * a) * (w : E)⁻¹ := by rw [hconj]
        _ = z * ((w : E) * a * (w : E)⁻¹) := by
          calc
            (w : E) * (z * a) * (w : E)⁻¹ =
                ((w : E) * z) * a * (w : E)⁻¹ := by group
            _ = (z * (w : E)) * a * (w : E)⁻¹ := by rw [hzcommw]
            _ = z * ((w : E) * a * (w : E)⁻¹) := by group
        _ = z * (z * a) := by rw [hconj]
        _ = z ^ 2 * a := by rw [pow_two]; group
    have hz2 : z ^ 2 = 1 := by
      apply mul_right_cancel (b := a)
      simpa using haeq.symm
    have hord2 : orderOf z ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := z) (n := 2)).mpr hz2
    have hordZ : orderOf z ∣ Nat.card Z :=
      Subgroup.orderOf_dvd_natCard Z hzZ
    have hord1 : orderOf z = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_two_left.mpr hZodd) hord2 hordZ
    have hz1 : z = 1 := orderOf_eq_one_iff.mp hord1
    have hfix : (w : E) * a * (w : E)⁻¹ = a := by
      rw [hconj, hz1, one_mul]
    have hcomm : (w : E) * a = a * (w : E) :=
      mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hfix)
    exact hcomm.symm

end CFSG.GorensteinWalter
