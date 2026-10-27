module

public import CFSG.Quasithin.EmptyFaithful.S153G93DTwo
public import CFSG.Quasithin.EmptyFaithful.S153G93DOne

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

theorem input15358G93_of_inputs (h38 : A38ForSQTKCat) (hA21 : AsA21SQTKSection)
    (hS : A38TypesSimple) (hB45 : AsB45) (hD37 : D37Core) (h1 : OneCases) (h2 : TwoCases) :
    CFSG.Quasithin.Input15358G93 := by
  intro W _ _ hW H K A a m hq hO2 hIrrH hmin hnc hIrrK hAH hAcomm hA2 hAcard hWm hAK haA ha1 ha2
    hrk hbig hT
  obtain ⟨T', hT', haT', hcT', hfix, hthree⟩ := hT
  obtain ⟨hKH, hKnorm, hK1, hKmin⟩ := hmin
  have hmin : IsMinNormalIn H K := ⟨hKH, hKnorm, hK1, hKmin⟩
  have haH : a ∈ H := hAH haA
  have haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K := hKnorm a haH
  have hKn : H ≤ Subgroup.normalizer (K : Set (MulAut W)) := le_normalizer_of_normalizes hKnorm
  rcases exists_twoStruct_of_minNormal h38 hS hq hO2 hmin hnc with hcomp | ⟨N, N', g, hst⟩
  ·
    obtain ⟨hsimple, -⟩ := simple_of_component hmin hnc hcomp
    have hnt : 1 < Nat.card ↥(fixV T') := by rw [hfix]; norm_num
    have : Nontrivial ↥(fixV T') := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(fixV T'))
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hthree' : ∀ k ∈ K, orderOf k = 3 → k z ≠ z := by
      intro k hk hk3 hkz
      obtain ⟨z', hz', hkz'⟩ := hthree k (hKH hk) hk3
      have hz'1 : z' ≠ 1 := fun h => hkz' (by rw [h, map_one])
      have hcard := hfix
      rw [Nat.card_eq_two_iff] at hcard
      obtain ⟨x, y, hxy, hset⟩ := hcard
      have hmem : ∀ u : ↥(fixV T'), u = x ∨ u = y := fun u => by
        have : u ∈ ({x, y} : Set ↥(fixV T')) := by rw [hset]; trivial
        simpa using this
      have hzz' : (⟨z, hz⟩ : ↥(fixV T')) = ⟨z', hz'⟩ := by
        by_contra hne
        have h1' : (1 : ↥(fixV T')) ≠ ⟨z, hz⟩ := fun h => hz1' (congrArg Subtype.val h).symm
        have h2' : (1 : ↥(fixV T')) ≠ ⟨z', hz'⟩ := fun h => hz'1 (congrArg Subtype.val h).symm
        rcases hmem 1 with h | h <;> rcases hmem ⟨z, hz⟩ with h' | h' <;>
          rcases hmem ⟨z', hz'⟩ with h'' | h'' <;> simp_all
      have : z = z' := congrArg Subtype.val hzz'
      exact hkz' (by rw [← this]; exact hkz)
    have hnab : ∃ x y : ↥K, x * y ≠ y * x := by
      by_contra hall
      push Not at hall
      apply hnc
      intro x hx y hy
      exact congrArg Subtype.val (hall ⟨x, hx⟩ ⟨y, hy⟩)
    have hS' : IsSylowTwoOf (T' ⊓ K) K := A4.isSylowTwoOf_inf_normal hT' hKH hKn
    have hC : Ctx1 W (K ⊔ Subgroup.zpowers a) K a (T' ⊓ K) z :=
      ⟨hW, hsimple, hnab, hIrrK, hbig, rfl, haN, ha1, ha2, hrk, hS', fun x hx => hcT' x hx.1,
        fun x hx => hz x hx.1, hz1', hthree'⟩
    exact one_component_false hA21 hB45 h1 hq hKH hC
  ·
    obtain ⟨hKqn, -, -, -⟩ := minNormal_subgroupOf hmin hnc
    obtain ⟨L₁, L₂, t, hd⟩ := exists_twoDataG hS hKH hT' hst hKqn
    exact two_false hA21 hD37 h2 hq hKH hKnorm hT' hd hW hIrrK hbig haH haT' haN ha1 ha2 hrk hcT'

end S153G93D

end CFSG.Quasithin
