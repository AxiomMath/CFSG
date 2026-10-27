module

public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private theorem s15k_jp_comm_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem s15k_jp_derived_map_eq {Γ G : Type*} [Group Γ] [Group G] {J : Subgroup G}
    (π : Γ →* ↥J) (hπ : Function.Surjective π) :
    (commutator Γ).map (J.subtype.comp π) = ⁅J, J⁆ := by
  have hrange : (J.subtype.comp π).range = J := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (π g).2
    · intro hx
      obtain ⟨g, hg⟩ := hπ ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]

theorem s15k_jp_index_eq {Γ G : Type*} [Group Γ] [Group G] {J : Subgroup G}
    (π : Γ →* ↥J) (hπ : Function.Bijective π) :
    (⁅J, J⁆.subgroupOf J).index = (commutator Γ).index := by
  have h1 : ⁅J, J⁆.subgroupOf J = _root_.commutator ↥J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (s15k_jp_comm_le J), Subgroup.map_subtype_commutator]
  have h2 : (commutator Γ).map π = _root_.commutator ↥J := by
    rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hπ.2]
    rfl
  rw [h1, ← h2]
  exact Subgroup.index_map_equiv (commutator Γ) (MulEquiv.ofBijective π hπ)

theorem s15k_jp_nat_derived {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : (FFModel.nat Γ).Realizes J R ⊥) :
    (⁅J, J⁆.subgroupOf J).index = (commutator ↥Γ).index ∧
      Nonempty (↥⁅J, J⁆ ≃* ↥⁅Γ, Γ⁆) ∧ (FFModel.nat ⁅Γ, Γ⁆).Realizes ⁅J, J⁆ R ⊥ := by
  obtain ⟨π₁, hπ⟩ := h
  let π : ↥Γ →* ↥J := π₁
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful Γ) hπ
  have hsurj : Function.Surjective π := hπ.1
  have hbij : Function.Bijective π := ⟨hinj, hsurj⟩
  let ψ : ↥Γ →* MulAut W := J.subtype.comp π
  have hψinj : Function.Injective ψ := J.subtype_injective.comp hinj
  have hmapψ : (commutator ↥Γ).map ψ = ⁅J, J⁆ := s15k_jp_derived_map_eq π hsurj
  have hmapΓ : (commutator ↥Γ).map Γ.subtype = ⁅Γ, Γ⁆ := Subgroup.map_subtype_commutator Γ
  refine ⟨?_, ?_, ?_⟩
  · exact s15k_jp_index_eq π hbij
  ·
    exact ⟨(((MulEquiv.subgroupCongr hmapΓ.symm).trans
      (Subgroup.equivMapOfInjective _ Γ.subtype Γ.subtype_injective).symm).trans
      ((Subgroup.equivMapOfInjective _ ψ hψinj).trans (MulEquiv.subgroupCongr hmapψ))).symm⟩
  ·
    obtain ⟨-, hZU, -, hUinv, hZinv, -, hkerinv, β, hβs, hβk, hβe⟩ := hπ
    let incl : ↥⁅Γ, Γ⁆ →* ↥Γ := Subgroup.inclusion (s15k_jp_comm_le Γ)
    have hmem : ∀ x : ↥⁅Γ, Γ⁆, ψ (incl x) ∈ ⁅J, J⁆ := by
      intro x
      have hx : (x : Matrix.GeneralLinearGroup ι K) ∈ (commutator ↥Γ).map Γ.subtype := by
        rw [hmapΓ]
        exact x.2
      obtain ⟨c, hc, hcx⟩ := hx
      have hinc : incl x = c := Subtype.ext hcx.symm
      rw [hinc, ← hmapψ]
      exact ⟨c, hc, rfl⟩
    let π' : ↥⁅Γ, Γ⁆ →* ↥⁅J, J⁆ := (ψ.comp incl).codRestrict ⁅J, J⁆ hmem
    refine ⟨π', ?_, hZU, bot_le, ?_, ?_, fun _ _ _ => trivial, ?_, β, hβs, hβk, ?_⟩
    · intro y
      have hy : (y : MulAut W) ∈ (commutator ↥Γ).map ψ := by
        rw [hmapψ]
        exact y.2
      obtain ⟨c, hc, hcy⟩ := hy
      have hcm : (c : Matrix.GeneralLinearGroup ι K) ∈ ⁅Γ, Γ⁆ := by
        rw [← hmapΓ]
        exact ⟨c, hc, rfl⟩
      refine ⟨⟨c, hcm⟩, Subtype.ext ?_⟩
      exact hcy
    · intro g u hu
      exact hUinv ⟨(g : MulAut W), s15k_jp_comm_le J g.2⟩ u hu
    · intro g z hz
      exact hZinv ⟨(g : MulAut W), s15k_jp_comm_le J g.2⟩ z hz
    · intro γ m hm
      exact hkerinv (incl γ) m hm
    · intro γ u m hu hm hum
      exact hβe (incl γ) u m hu hm hum


theorem s15k_jp_subgroupOf_commutator {G : Type*} [Group G] (O : Subgroup G) :
    ⁅O, O⁆.subgroupOf O = _root_.commutator ↥O := by
  apply Subgroup.map_injective O.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (s15k_jp_comm_le O), Subgroup.map_subtype_commutator]

theorem s15k_jp_commutator_index_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (_root_.commutator A).index = (_root_.commutator B).index := by
  have h : (_root_.commutator A).map (e : A →* B) = _root_.commutator B := by
    rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
    rfl
  rw [← h]
  exact (Subgroup.index_map_equiv (_root_.commutator A) e).symm

theorem s15k_jp_nat_perfect {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {J : Subgroup (MulAut W)} {R : Subgroup W} (hperf : Group.IsPerfect ↥Γ)
    (h : (FFModel.nat Γ).Realizes J R ⊥) :
    (⁅J, J⁆.subgroupOf J).index = 1 ∧ Nonempty (↥⁅J, J⁆ ≃* ↥Γ) ∧
      (FFModel.nat Γ).Realizes ⁅J, J⁆ R ⊥ := by
  obtain ⟨hidx, ⟨e⟩, hreal⟩ := s15k_jp_nat_derived h
  have hcomm : commutator ↥Γ = ⊤ := hperf.commutator_eq_top
  have hΓ : ⁅Γ, Γ⁆ = Γ := by
    rw [← Subgroup.map_subtype_commutator Γ, hcomm, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨?_, ⟨e.trans (MulEquiv.subgroupCongr hΓ)⟩, ?_⟩
  · rw [hidx, hcomm, Subgroup.index_top]
  · rw [hΓ] at hreal
    exact hreal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
