module

public import CFSG.RankThree.PartOne.S11c.OddG2Plane
public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.PartOne.S11c.ProjectiveDegree

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)

theorem isComponent_map_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    {L : Subgroup A} (hL : CFSG.IsComponent L) : CFSG.IsComponent (L.map φ.toMonoidHom) := by
  refine ⟨?_, hL.2.map (f := φ.toMonoidHom) φ.surjective⟩
  let e : ↥L ≃* ↥(L.map φ.toMonoidHom) := L.equivMapOfInjective φ.toMonoidHom φ.injective
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := e.toMonoidHom) hL.1
    e.surjective ?_
  by_contra hne
  have hne' : ∀ a : ↥L, e.toMonoidHom a = 1 := fun a => by_contra fun h => hne ⟨a, h⟩
  have hsub : Subsingleton ↥L :=
    ⟨fun a b => e.injective (((hne' a).trans (hne' b).symm : e.toMonoidHom a = e.toMonoidHom b))⟩
  have h1 := hL.1.2.1
  have : Subsingleton (↥L ⧸ Subgroup.center ↥L) :=
    Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
  exact h1.toNontrivial.exists_pair_ne.elim fun a hb => hb.elim fun b hab =>
    hab (Subsingleton.elim a b)

section PGL

variable {T : Type} [Group T] {Kf : Type} [Field Kf] [Finite Kf]

theorem g2_pgl_absurd
    (K : Subgroup T) (hK : StatedClassicalModel K .PSU 3 5 1) {ℓ : ℕ} [CharP Kf ℓ]
    (hℓ : ℓ.Prime) (h5 : ℓ ≠ 5) (e : T ≃* adjointGroup Tag.G2 Kf) : False := by
  classical
  let b : Module.Basis (Label Tag.G2) Kf (RootModule Tag.G2 Kf) := Finsupp.basisSingleOne
  let toMat : Module.End Kf (RootModule Tag.G2 Kf) ≃ₐ[Kf]
      Matrix (Label Tag.G2) (Label Tag.G2) Kf := LinearMap.toMatrixAlgEquiv b
  let φ : ↥K →* ModGL Tag.G2 Kf :=
    (adjointGroup Tag.G2 Kf).subtype.comp (e.toMonoidHom.comp K.subtype)
  let ρ : ↥K →* Matrix.GeneralLinearGroup (Label Tag.G2) Kf :=
    (Units.map toMat.toAlgHom.toMonoidHom).comp φ
  have hφ : Function.Injective φ :=
    Subtype.val_injective.comp (e.injective.comp K.subtype_injective)
  have hρ : Function.Injective ρ :=
    (Units.map_injective (f := toMat.toAlgHom.toMonoidHom) toMat.injective).comp hφ
  have h20 := unitary_three_five_projective_degree_bound_idx hK
    (five_ne_zero_of_charP hℓ h5) ρ hρ (MonoidHom.id ↥K) (fun x => ⟨x, rfl⟩) (fun g hg => by
      rw [MonoidHom.mem_ker] at hg
      rw [show g = 1 from hg, map_one]
      exact one_mem _)
  have hcard : Fintype.card (Label Tag.G2) = 14 := by
    show Fintype.card (Fin Tag.G2.rank ⊕ {v : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 v}) = 14
    rw [Fintype.card_sum, Fintype.card_fin, card_isRoot]
    rfl
  omega

end PGL

section Five

open CFSG.LieType.Chevalley.RootWeightDatum in
theorem g2_char_five_absurd
    {H : Type} [Group H] [Finite H] (hrank : CFSG.twoLocalOddRank H ≤ 3) (X : Subgroup H)
    {β : MulAut (↥X ⧸ Subgroup.center ↥X)} {K : Subgroup (↥X ⧸ Subgroup.center ↥X)}
    (hFive : FiveFixedPSU3 β K) {f : ℕ}
    (hmod : ChevalleyExceptionalModel (↥X ⧸ Subgroup.center ↥X) .G2 5 f) : False := by
  classical
  have hℓ : (5 : ℕ).Prime := Nat.prime_five
  have hℓ2 : (5 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ f := hmod.1.2.1
  have hloc : localRank 5 H ≤ 3 := by
    rcases Nat.eq_zero_or_pos (localRank 5 H) with h0 | hpos
    · omega
    · exact (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hℓ hℓ2
        (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hℓ hpos)).trans hrank
  obtain ⟨-, -, hinner⟩ := odd_G2_actual_central_cover_rank_three_five_actors_inner X hℓ hℓ2
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hloc hmod
  obtain ⟨t, rfl⟩ := hinner β hFive.1
  obtain ⟨Kf, _, _, hKf, ⟨e⟩⟩ := hmod.2
  have : Fintype Kf := Fintype.ofFinite Kf
  have hchar : CharP Kf 5 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hKf
  have : Fact (Nat.Prime 5) := ⟨hℓ⟩
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* adjointGroup Tag.G2 Kf :=
    e.trans (adjointQuotientEquiv Tag.G2 Kf)
  have hinj := conj_injective_of_mulEquiv_adjointGroup e'
  have hord : orderOf t = 5 := ((orderOf_injective _ hinj t).symm).trans hFive.1
  let y : ↥(adjointGroup Tag.G2 Kf) := e' t
  have hyord : orderOf y = 5 := by
    have h1 : orderOf (e' t) = 5 := by rw [MulEquiv.orderOf_eq]; exact hord
    exact h1
  let Q : Subgroup ↥(adjointGroup Tag.G2 Kf) := Subgroup.zpowers y
  have hQp : IsPGroup 5 Q :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one])
  have hQ : Q ≠ ⊥ := by
    intro h
    have hy : y ∈ Q := Subgroup.mem_zpowers y
    rw [h, Subgroup.mem_bot] at hy
    rw [hy, orderOf_one] at hyord
    omega
  let Hc : Subgroup ↥(adjointGroup Tag.G2 Kf) := Subgroup.centralizer (Q : Set _)
  have hfree := (RootWeightDatum.ordinary Tag.G2 : RootWeightDatum Kf)
    |>.defining_characteristic_root_local_groups_component_free 5 Q hQp hQ Hc (Or.inr rfl)
  have hC : (fixedSubgroup (MulAut.conj t : MulAut (↥X ⧸ Subgroup.center ↥X))).map
      e'.toMonoidHom = Hc := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      have hu' : t * u * t⁻¹ = u := hu
      have hcomm : t * u = u * t := by
        rw [mul_inv_eq_iff_eq_mul] at hu'
        exact hu'
      have hcy : Commute y (e' u) := by
        show e' t * e' u = e' u * e' t
        rw [← map_mul, ← map_mul, hcomm]
      exact (hcy.zpow_left n).eq
    · intro hz
      obtain ⟨u, rfl⟩ := e'.surjective z
      refine ⟨u, ?_, rfl⟩
      have hy : y * e' u = e' u * y :=
        (Subgroup.mem_centralizer_iff.1 hz) y (Subgroup.mem_zpowers y)
      have hcomm : t * u = u * t := e'.injective (by rw [map_mul, map_mul]; exact hy)
      show t * u * t⁻¹ = u
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm
  let ψ := (e'.subgroupMap (fixedSubgroup (MulAut.conj t : MulAut (↥X ⧸ Subgroup.center ↥X)))).trans
    (MulEquiv.subgroupCongr hC)
  exact hfree.2 _ (isComponent_map_mulEquiv ψ hFive.2.1.2)

theorem g2_five_fixed_absurd
    {H : Type} [Group H] [Finite H] (hrank : CFSG.twoLocalOddRank H ≤ 3) (X : Subgroup H)
    {β : MulAut (↥X ⧸ Subgroup.center ↥X)} {K : Subgroup (↥X ⧸ Subgroup.center ↥X)}
    (hFive : FiveFixedPSU3 β K) {ℓ f : ℕ}
    (hmod : ChevalleyExceptionalModel (↥X ⧸ Subgroup.center ↥X) .G2 ℓ f) : False := by
  classical
  by_cases h5 : ℓ = 5
  · subst h5
    exact g2_char_five_absurd hrank X hFive hmod
  · have hℓ : ℓ.Prime := hmod.1.1
    have hf : 1 ≤ f := hmod.1.2.1
    obtain ⟨Kf, _, _, hKf, ⟨e⟩⟩ := hmod.2
    have : Fintype Kf := Fintype.ofFinite Kf
    have hchar : CharP Kf ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hKf
    exact g2_pgl_absurd K hFive.2.2 hℓ h5 (e.trans (adjointQuotientEquiv Tag.G2 Kf))

end Five

end CFSG.RankThree.PartOne.HNRed
