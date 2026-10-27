module

public import CFSG.RankThree.PartOne.N143X.WeylMatrix

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X

theorem range_map_le_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (E : Subgroup G) :
    E.normalizerMonoidHom.range.map (MulAut.congr (E.equivMapOfInjective f hf)).toMonoidHom ≤
      (E.map f).normalizerMonoidHom.range := by
  let ψ : E ≃* E.map f := E.equivMapOfInjective f hf
  let ρ : MulAut E ≃* MulAut (E.map f) := MulAut.congr ψ
  intro y hy
  obtain ⟨φ, ⟨n, rfl⟩, rfl⟩ := hy
  refine ⟨⟨f n, Subgroup.le_normalizer_map f ⟨n, n.2, rfl⟩⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨e, rfl⟩ := ψ.surjective x
  have h1 : (ρ.toMonoidHom (E.normalizerMonoidHom n)) (ψ e) =
      ψ ((E.normalizerMonoidHom n) e) := by
    change MulAut.congr ψ _ _ = _
    rw [MulAut.congr_apply]
    simp
  rw [h1]
  apply Subtype.ext
  change f (n : G) * f (e : G) * (f (n : G))⁻¹ = f ((n : G) * (e : G) * (n : G)⁻¹)
  simp

theorem exists_lifted_conf {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (M : Subgroup (GL ι K)) {Q : Type} [Group Q] (e : Q ≃* StatedProj M) {p : ℕ} [Fact p.Prime]
    {d : ℕ} (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1)
    (hpd : ¬ p ∣ d) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē)
    (hmax : ∀ D : Subgroup Q, IsElementaryAbelian p D → D ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ D → D ≤ Ē) :
    ∃ (F : Subgroup (GL ι K)) (eF : F ≃* Ē), IsElementaryAbelian p F ∧ F ≤ M ∧
      (∀ D : Subgroup (GL ι K), D ≤ M → IsElementaryAbelian p D → F ≤ D →
        D ≤ Subgroup.centralizer (F : Set (GL ι K)) → Nat.card D ≤ Nat.card F) ∧
      ∀ β ∈ Ē.normalizerMonoidHom.range, MulAut.congr eF.symm β ∈
        F.normalizerMonoidHom.range := by
  classical
  have hp := (Fact.out : p.Prime)
  have : Finite Q := Finite.of_equiv (StatedProj M) e.symm.toEquiv
  let N : Subgroup M := (StatedScalars ι K).subgroupOf M
  let π : M →* Q := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker ≤ Subgroup.center M := by
    rw [hπker]
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    have hcen : Matrix.GeneralLinearGroup.scalar ι c ∈ Subgroup.center (GL ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact Subgroup.mem_center_iff.1 hcen (y : GL ι K)
  have hpk : ¬ p ∣ Nat.card π.ker := by
    rw [hπker]
    exact not_dvd_card_scalarKernel' M hp hpd hd
  have hEp : IsPGroup p Ē := IsElementaryAbelian.isPGroup p Ē
  obtain ⟨F₀, hF₀p, hF₀map, hF₀inj, hFnorm⟩ := exists_pSubgroup_lift_normalizer π hπ hker hpk hEp
  let eF₁ : F₀ ≃* Ē := (MonoidHom.ofInjective hF₀inj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hF₀map]))
  have heF₁ : ∀ y : F₀, ((eF₁ y : Ē) : Q) = π (y : M) := fun y => rfl
  have hle₁ : ∀ β ∈ Ē.normalizerMonoidHom.range,
      MulAut.congr eF₁.symm β ∈ F₀.normalizerMonoidHom.range := by
    intro β hβ
    obtain ⟨n, rfl⟩ := hβ
    obtain ⟨g, hg⟩ := hπ (n : Q)
    have hn1 : ∀ u ∈ Ē, (n : Q) * u * (n : Q)⁻¹ ∈ Ē := fun u hu =>
      (Subgroup.mem_normalizer_iff.1 n.2 u).1 hu
    have hn2 : ∀ u ∈ Ē, (n : Q)⁻¹ * u * (n : Q) ∈ Ē := fun u hu => by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Ē : Set Q)).inv_mem n.2) u).1
        hu
      simpa using this
    have hgF : g ∈ Subgroup.normalizer (F₀ : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hFnorm g (by rw [hg]; exact hn1) (by rw [hg]; exact hn2) x hx
      · intro hx
        have := hFnorm g⁻¹ (by rw [map_inv, hg]; simpa using hn2)
          (by rw [map_inv, hg]; simpa using hn1) _ hx
        have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rwa [e] at this
    refine ⟨⟨g, hgF⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply hF₀inj
    change π (((F₀.normalizerMonoidHom ⟨g, hgF⟩) x : F₀) : M) =
      π ((((MulAut.congr eF₁.symm) (Ē.normalizerMonoidHom n)) x : F₀) : M)
    have h1 : π (((((MulAut.congr eF₁.symm) (Ē.normalizerMonoidHom n)) x : F₀) : M)) =
        (((Ē.normalizerMonoidHom n) (eF₁ x) : Ē) : Q) := by
      rw [MulAut.congr_apply]
      change π ((eF₁.symm ((Ē.normalizerMonoidHom n) (eF₁ (x : F₀))) : F₀) : M) = _
      rw [← heF₁, MulEquiv.apply_symm_apply]
    rw [h1]
    change π ((g : M) * (x : M) * (g : M)⁻¹) = (n : Q) * (((eF₁ x : Ē) : Q)) * (n : Q)⁻¹
    rw [map_mul, map_mul, map_inv, hg, ← heF₁]
  let F : Subgroup (GL ι K) := F₀.map M.subtype
  let ψ : F₀ ≃* F := F₀.equivMapOfInjective M.subtype M.subtype_injective
  let eF : F ≃* Ē := ψ.symm.trans eF₁
  have hle : ∀ β ∈ Ē.normalizerMonoidHom.range,
      MulAut.congr eF.symm β ∈ F.normalizerMonoidHom.range := by
    intro β hβ
    have h2 := range_map_le_of_injective M.subtype M.subtype_injective F₀
    have h3 : MulAut.congr eF.symm β = MulAut.congr ψ (MulAut.congr eF₁.symm β) := by
      ext x
      simp [eF, MulAut.congr_apply]
    rw [h3]
    exact h2 ⟨_, hle₁ β hβ, rfl⟩
  have hFel : IsElementaryAbelian p F := isElementaryAbelian_of_equiv eF.symm hE
  have hFM : F ≤ M := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨F, eF, hFel, hFM, ?_, hle⟩
  intro D hDM hDel hFD hDcent
  let D₀ : Subgroup M := D.comap M.subtype
  have hD₀map : D₀.map M.subtype = D := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.2 hDM
  have eD : D₀ ≃* D :=
    (D₀.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hD₀map)
  have hD₀el : IsElementaryAbelian p D₀ := isElementaryAbelian_of_equiv eD.symm hDel
  have hD₀p : IsPGroup p D₀ := IsElementaryAbelian.isPGroup p D₀
  have hinj : Function.Injective (π.comp D₀.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hker'
    have hxk : x ∈ π.ker := hker'
    obtain ⟨m, hm⟩ := hD₀p ⟨x, hx⟩
    have hxm : x ^ p ^ m = 1 := congrArg Subtype.val hm
    have h1 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hxm
    have h2 : orderOf x ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hxk
    have h3 : Nat.Coprime (p ^ m) (Nat.card π.ker) :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    have h4 : orderOf x = 1 := (Nat.Coprime.coprime_dvd_left h1 h3).eq_one_of_dvd h2
    exact Subtype.ext (orderOf_eq_one_iff.1 h4)
  let D' : Subgroup Q := D₀.map π
  have hD'el : IsElementaryAbelian p D' := by
    have := hD₀el
    exact IsElementaryAbelian.map π
  have hD'cent : D' ≤ Subgroup.centralizer (Ē : Set Q) := by
    rintro _ ⟨d, hd, rfl⟩ u hu
    have hu' : u ∈ F₀.map π := by rwa [hF₀map]
    obtain ⟨f, hf, rfl⟩ := hu'
    have hfF : ((f : M) : GL ι K) ∈ F := ⟨f, hf, rfl⟩
    have hdD : ((d : M) : GL ι K) ∈ D := hd
    have hcomm : ((d : M) : GL ι K) * (f : M) = (f : M) * ((d : M) : GL ι K) :=
      (Subgroup.mem_centralizer_iff.1 (hDcent hdD) _ hfF).symm
    have : (d : M) * f = f * (d : M) := Subtype.ext hcomm
    rw [← map_mul, ← map_mul, this]
  have hĒD' : Ē ≤ D' := by
    rw [← hF₀map]
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f, ?_, rfl⟩
    exact hFD ⟨f, hf, rfl⟩
  have hD'le : D' ≤ Ē := hmax D' hD'el hD'cent hĒD'
  have hcardD' : Nat.card D' = Nat.card D₀ := by
    have hrange : D' = (π.comp D₀.subtype).range := by
      show D₀.map π = _
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  calc Nat.card D = Nat.card D₀ := (Nat.card_congr eD.toEquiv).symm
    _ = Nat.card D' := hcardD'.symm
    _ ≤ Nat.card Ē := Subgroup.card_le_of_le hD'le
    _ = Nat.card F := (Nat.card_congr eF.toEquiv).symm

end CFSG.RankThree.PartOne.Q1327T.R8
