module

public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.RankThree.PartOne.S11d.FieldTransfer
public import CFSG.RankThree.PartOne.TCX.Interface

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCX

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] (S : Subgroup X) {x : X}
    (h : ∀ s ∈ S, x * s * x⁻¹ ∈ S) : x ∈ Subgroup.normalizer (S : Set X) := by
  let f : ↥S → ↥S := fun s => ⟨x * (s : X) * x⁻¹, h s s.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h : x * (a : X) * x⁻¹ = x * (b : X) * x⁻¹ := congrArg Subtype.val hab
    simpa using h
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨s, hs⟩ := hsurj ⟨x * y * x⁻¹, hy⟩
  have hs' : x * (s : X) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hs
  have : (s : X) = y := by simpa using hs'
  rw [← this]
  exact s.2

variable {G : Type} [Group G] [Finite G]

omit [Group G] [Finite G] in
theorem pRank_perfectResidual_eq_of_hom {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (θ : X →* Y) (hsurj : Function.Surjective θ)
    (hker : ∀ z ∈ θ.ker, Nat.Coprime (orderOf z) p) :
    CFSG.pRank p ↥(perfectResidual Y) = CFSG.pRank p ↥(perfectResidual X) := by
  classical
  have hmap : (perfectResidual X).map θ = perfectResidual Y :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq θ hsurj
  let θ' : ↥(perfectResidual X) →* ↥(perfectResidual Y) :=
    (θ.comp (perfectResidual X).subtype).codRestrict (perfectResidual Y)
      (fun x => by rw [← hmap]; exact ⟨x, x.2, rfl⟩)
  have hθ' : Function.Surjective θ' := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hNp : ¬ p ∣ Nat.card θ'.ker := by
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := θ'.ker) p hdvd
    have hz0ker : ((z : ↥(perfectResidual X)) : X) ∈ θ.ker := by
      have h1 : θ' (z : ↥(perfectResidual X)) = 1 := z.2
      exact congrArg Subtype.val h1
    have h3 := hker _ hz0ker
    have h4 : orderOf ((z : ↥(perfectResidual X)) : X) = p := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    rw [h4] at h3
    exact hp.one_lt.ne' ((Nat.coprime_self p).mp h3)
  have e1 : (↥(perfectResidual X) ⧸ θ'.ker) ≃* ↥(perfectResidual Y) :=
    QuotientGroup.quotientKerEquivOfSurjective θ' hθ'
  rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e1]
  exact CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp θ'.ker hNp

theorem pRank_fixRes_eq {p : ℕ} (hp : p.Prime) {J : Subgroup G} {u : G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hu : u ∈ Subgroup.normalizer (J : Set G))
    (hup : u ^ p = 1) :
    CFSG.pRank p ↥(fixRes (centerQuotientConj J ⟨u, hu⟩)) =
      CFSG.pRank p ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))) := by
  classical
  obtain ⟨θ, hsurj, hker, hθ⟩ := exists_fixed_hom hp hZ hu hup
  have h1 := pRank_perfectResidual_eq_of_hom hp θ hsurj (fun z hz =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun h => hZ (h.trans (orderOf_dvd_card_center_of_mem_ker hθ z hz)))))
  have e2 : ↥(perfectResidual ↥(fixSub (centerQuotientConj J ⟨u, hu⟩))) ≃*
      ↥(fixRes (centerQuotientConj J ⟨u, hu⟩)) :=
    (perfectResidual ↥(fixSub (centerQuotientConj J ⟨u, hu⟩))).equivMapOfInjective
      (fixSub (centerQuotientConj J ⟨u, hu⟩)).subtype (Subgroup.subtype_injective _)
  have e3 : ↥(perfectResidual ↥(J ⊓ Subgroup.centralizer ({u} : Set G))) ≃*
      ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))) :=
    (perfectResidual ↥(J ⊓ Subgroup.centralizer ({u} : Set G))).equivMapOfInjective
      (J ⊓ Subgroup.centralizer ({u} : Set G)).subtype (Subgroup.subtype_injective _)
  rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e2,
    ← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e3]
  exact h1

@[expose] def FieldFixedRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u → 2 ≤ CFSG.pRank p ↥J →
      2 ≤ CFSG.pRank p ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)))

end CFSG.RankThree.PartOne
