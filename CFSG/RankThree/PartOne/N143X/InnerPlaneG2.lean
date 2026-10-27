module

public import CFSG.RankThree.PartOne.S11c.OddG2Plane

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne

theorem planeCentralizes_inner_G2
    {T : Type} [Group T] [Finite T] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : ChevalleyExceptionalModel T .G2 ℓ f) {p : ℕ} {E : Subgroup (MulAut T)}
    {U : Subgroup T} (hplane : PlaneOn p E U)
    (hpinner : E ≤ (MulAut.conj : T →* MulAut T).range) : PlaneCentralizes E U := by
  classical
  have hp := hplane.prime
  have hp3 := hplane.three_lt
  have : IsElementaryAbelian p E := hplane.elementary
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  let e' : T ≃* adjointGroup .G2 K := e.trans (adjointQuotientEquiv .G2 K)
  have hinj := conj_injective_of_mulEquiv_adjointGroup e'
  let E' : Subgroup T := E.comap (MulAut.conj : T →* MulAut T)
  have hE'map : E'.map (MulAut.conj : T →* MulAut T) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 fun β hβ => hpinner hβ
  let eEE' : E' ≃* E :=
    (Subgroup.equivMapOfInjective E' MulAut.conj hinj).trans (MulEquiv.subgroupCongr hE'map)
  have : Fact p.Prime := ⟨hp⟩
  have hE'el : IsElementaryAbelian p E' :=
    isElementaryAbelian_of_mulEquiv' eEE'.symm hplane.elementary
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [Nat.card_congr eEE'.toEquiv]
    exact hplane.card
  have hE'U : ∀ x ∈ E', ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    hplane.normalized (MulAut.conj x) hx u hu
  let φ : T →* ModGL .G2 K := (adjointGroup .G2 K).subtype.comp e'.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e'.injective
  have hφC : ∀ x, φ x ∈ adjointGroup .G2 K := fun x => (e' x).2
  have hE'φ : IsElementaryAbelian p (E'.map φ) := IsElementaryAbelian.map (A := E') φ
  have hUfin : Finite (U.map φ) :=
    Finite.of_surjective (fun u : U => (⟨φ u, u, u.2, rfl⟩ : U.map φ))
      (by rintro ⟨_, u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩)
  have hmain := g2_plane_centralizes hKodd hp hp3 (E := E'.map φ) (U := U.map φ)
    (by rintro _ ⟨y, -, rfl⟩; exact hφC y) (by rintro _ ⟨y, -, rfl⟩; exact hφC y)
    (by rw [Subgroup.card_map_of_injective hφ]; exact hE'card)
    (hplane.two_group.map φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨u, hu, rfl⟩
      exact ⟨x * u * x⁻¹, hE'U x hx u hu, by simp [map_mul]⟩)
  intro β hβ u hu
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ E', MulAut.conj x = β := by
    have : β ∈ E'.map (MulAut.conj : T →* MulAut T) := hE'map ▸ hβ
    obtain ⟨x, hx, hxβ⟩ := this
    exact ⟨x, hx, hxβ⟩
  have hc := hmain (φ x) ⟨x, hx, rfl⟩ (φ u) ⟨u, hu, rfl⟩
  have hxu : x * u = u * x := hφ (by rw [map_mul, map_mul]; exact hc)
  change x * u * x⁻¹ = u
  rw [mul_inv_eq_iff_eq_mul]
  exact hxu

end CFSG.RankThree.PartOne.N143X
