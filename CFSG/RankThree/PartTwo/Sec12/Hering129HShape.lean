module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFK
public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Shape

variable {G : Type} [Group G] [Finite G]

theorem not_mem_thetaQuotCentralizer_of_central_sq {c : G} {X Y : Subgroup G}
    (hXY : X ≤ Y) (hcX : c ∈ X) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hZ2 : ∀ z ∈ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X), z ^ 2 = 1) :
    c ∉ Sec4.thetaQuotCentralizer Y := by
  intro hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθsol, hθchar, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  haveI : θ.Characteristic := hθchar
  haveI : θ.Normal := inferInstance
  let cX : X := ⟨c, hcX⟩
  have hcent : (QuotientGroup.mk cX : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    have hu := (Sec6.mem_thetaQuotCentralizer_iff.mp hc).2 (u : G) (hXY u.2)
    have htX : (u : G)⁻¹ * ((c : G) * u * c⁻¹) ∈ X :=
      X.mul_mem (X.inv_mem u.2) (X.mul_mem (X.mul_mem hcX u.2) (X.inv_mem hcX))
    have ht := mem_theta_of_mem_theta_of_le hXY htX hu
    have hmem : (u * cX)⁻¹ * (cX * u) ∈ θ := by
      have h1 : cX⁻¹ * (⟨_, htX⟩ : X) * cX ∈ θ := by
        have := (inferInstance : θ.Normal).conj_mem _ ht cX⁻¹
        simpa using this
      convert h1 using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hc' : (cX : G) = c := rfl
      rw [hc']
      group
    exact QuotientGroup.eq.mpr hmem
  have hsq := hZ2 _ hcent
  have hcube : (QuotientGroup.mk cX : ↥X ⧸ θ) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : cX ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this]
    rfl
  have h1 : (QuotientGroup.mk cX : ↥X ⧸ θ) = 1 :=
    eq_one_of_pow_three_of_pow_two_pow hcube (k := 1) (by simpa using hsq)
  have hcθ : cX ∈ θ := (QuotientGroup.eq_one_iff _).mp h1
  have hord : orderOf (⟨cX, hcθ⟩ : θ) = 3 := by
    rw [← Subgroup.orderOf_coe]
    have : cX ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    have hne : cX ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    exact orderOf_eq_prime this hne
  apply hθ3
  rw [← hord]
  exact orderOf_dvd_natCard _

@[expose] def Gap129YShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y →
        (Typ129I K Y ∨ Typ129II K Y ∨ Typ129IV q Y ∨ Typ129IIIcType L Y)

end Shape

end CFSG.RankThree.PartTwo.Sec12
