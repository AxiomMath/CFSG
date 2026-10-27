module

public import CFSG.RankThree.GroupTheory.SteinbergCESmallAlternatingFiveActor
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.ComponentClassification CFSG.RankThree.GroupTheory
open CFSG.Blueprint
open CFSG.Sporadic.LySchreier (involution_centralizers_quasisimple)

theorem ly_two_subgroup_commuting_five_le_sixteen
    {T : Type} [Group T] [Finite T] (hT : Nonempty (T ≃* NativeSporadic.Ly)) {b : T}
    (hbord : orderOf b = 5) (R : Subgroup T) (hR2 : IsPGroup 2 R)
    (hbR : ∀ u ∈ R, b * u * b⁻¹ = u) : Nat.card R ≤ 16 := by
  classical
  have hb5 : b ^ 5 = 1 := hbord ▸ pow_orderOf_eq_one b
  by_cases hRnt : Nontrivial R
  swap
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hRnt
    have h1 : Nat.card R = 1 := Nat.card_unique
    omega
  have hZnt : Nontrivial (Subgroup.center R) := hR2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center R) :=
    hR2.of_injective (Subgroup.center R).subtype (Subgroup.center R).subtype_injective
  have h2dvd : 2 ∣ Nat.card (Subgroup.center R) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZ2
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
      rw [hn] at this
      omega
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2 h2dvd
  set w : T := (((z : Subgroup.center R) : R) : T) with hwdef
  have hwR : w ∈ R := ((z : Subgroup.center R) : R).2
  have hw2 : orderOf w = 2 := by
    rw [hwdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hwcomm : ∀ r ∈ R, r * w = w * r := by
    intro r hr
    have := Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  set C : Subgroup T := Subgroup.centralizer ({w} : Set T) with hC
  have hRC : R ≤ C := fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hwcomm r hr)
  have hbC : b ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have := hbR w hwR
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨-, hcard2, ⟨φ⟩⟩ := involution_centralizers_quasisimple hT w hw2
  let ψ : ↥C →* ↥(alternatingGroup (Fin 11)) :=
    (φ : ↥C ⧸ Subgroup.center ↥C →* ↥(alternatingGroup (Fin 11))).comp
      (QuotientGroup.mk' (Subgroup.center ↥C))
  have hψker : ∀ x : ↥C, ψ x = 1 ↔ x ∈ Subgroup.center ↥C := by
    intro x
    change φ (x : ↥C ⧸ Subgroup.center ↥C) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let ι : ↥R →* ↥C := Subgroup.inclusion hRC
  let θ : ↥R →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (ψ.comp ι)
  have hkercard : Nat.card θ.ker ≤ 2 := by
    rw [← hcard2]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨ι (x : ↥R), (hψker (ι x)).mp (Subtype.ext (by
        have h1 : θ (x : ↥R) = 1 := x.2
        exact h1))⟩ : Subgroup.center ↥C)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subgroup.inclusion_injective hRC
    exact congrArg Subtype.val hxy
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set σ' : ↥(alternatingGroup (Fin 11)) := ψ ⟨b, hbC⟩ with hσ'
  set σ : Equiv.Perm (Fin 11) := (σ' : Equiv.Perm (Fin 11)) with hσ
  have hσ5 : orderOf σ = 5 := by
    have hpow : σ' ^ 5 = 1 := by
      rw [hσ', ← map_pow]
      have : (⟨b, hbC⟩ : ↥C) ^ 5 = 1 := Subtype.ext (by simpa using hb5)
      rw [this, map_one]
    have hne : σ' ≠ 1 := by
      intro h1
      have hcen : (⟨b, hbC⟩ : ↥C) ∈ Subgroup.center ↥C := (hψker ⟨b, hbC⟩).mp (hσ' ▸ h1)
      have h2 : (⟨b, hbC⟩ : ↥C) ^ 2 = 1 := by
        have := pow_card_eq_one' (G := Subgroup.center ↥C) (x := ⟨⟨b, hbC⟩, hcen⟩)
        rw [hcard2] at this
        exact congrArg Subtype.val this
      have h2' : b ^ 2 = 1 := congrArg Subtype.val h2
      have : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one h2'
      rw [hbord] at this
      omega
    have hσ'ord : orderOf σ' = 5 := orderOf_eq_prime hpow hne
    rw [hσ, Subgroup.orderOf_coe]
    exact hσ'ord
  have hXσ : ∀ r : ↥R, θ r * σ = σ * θ r := by
    intro r
    have hcomm' : ι r * ⟨b, hbC⟩ = ⟨b, hbC⟩ * ι r := by
      apply Subtype.ext
      have := hbR (r : T) r.2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have h1 : ψ (ι r) * σ' = σ' * ψ (ι r) := by
      rw [hσ', ← map_mul, ← map_mul, hcomm']
    exact congrArg Subtype.val h1
  have hX2 : IsPGroup 2 θ.range := hR2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hXA : θ.range ≤ alternatingGroup (Fin 11) := by
    rintro _ ⟨r, rfl⟩
    exact (ψ (ι r)).2
  have hX8 : Nat.card θ.range ≤ 8 :=
    card_le_eight_of_commute_orderOf_five (n := 11) (by norm_num) hσ5 hX2 hXA (by
      rintro _ ⟨r, rfl⟩
      exact hXσ r)
  have hkerrange := Subgroup.card_ker_mul_card_range θ
  have hkpos : 0 < Nat.card θ.ker := Nat.card_pos
  have hrpos : 0 < Nat.card θ.range := Nat.card_pos
  calc Nat.card R = Nat.card θ.ker * Nat.card θ.range := hkerrange.symm
    _ ≤ 2 * 8 := Nat.mul_le_mul hkercard hX8

end CFSG.RankThree.PartOne.FOCD
