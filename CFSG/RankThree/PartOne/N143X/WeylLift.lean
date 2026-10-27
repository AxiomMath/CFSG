module

public import CFSG.RankThree.PartOne.S11c.CentralLift
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

theorem card_normalizerRange_dvd_of_injective {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Injective f) (E : Subgroup G) :
    Nat.card E.normalizerMonoidHom.range ∣ Nat.card (E.map f).normalizerMonoidHom.range := by
  let ψ : E ≃* E.map f := E.equivMapOfInjective f hf
  let ρ : MulAut E ≃* MulAut (E.map f) := MulAut.congr ψ
  have hle : E.normalizerMonoidHom.range.map ρ.toMonoidHom ≤
      (E.map f).normalizerMonoidHom.range := by
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
  have h1 : Nat.card (E.normalizerMonoidHom.range.map ρ.toMonoidHom) =
      Nat.card E.normalizerMonoidHom.range := Subgroup.card_map_of_injective ρ.injective
  rw [← h1]
  exact Subgroup.card_dvd_of_le hle

theorem exists_pSubgroup_lift_normalizer {M T : Type*} [Group M] [Group T] [Finite M]
    (π : M →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) {p : ℕ}
    [Fact p.Prime] (hpk : ¬ p ∣ Nat.card π.ker) {E : Subgroup T} (hE : IsPGroup p E) :
    ∃ F : Subgroup M, IsPGroup p F ∧ F.map π = E ∧ Function.Injective (π.comp F.subtype) ∧
      ∀ e : M, (∀ u ∈ E, π e * u * (π e)⁻¹ ∈ E) → (∀ u ∈ E, (π e)⁻¹ * u * π e ∈ E) →
        ∀ x ∈ F, e * x * e⁻¹ ∈ F := by
  classical
  set G : Subgroup M := E.comap π with hG
  let f : G →* E := (π.comp G.subtype).codRestrict E fun x => x.2
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨⟨x, by rw [hG, Subgroup.mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  have : Finite E := Finite.of_surjective f hf
  have hnil : Group.IsNilpotent G := by
    have : Group.IsNilpotent E := hE.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro x hx
    have hxk : (x : M) ∈ π.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hxk) y)
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPc : (P : Subgroup G).Characteristic := Sylow.characteristic_of_normal P inferInstance
  refine ⟨P.map G.subtype, P.2.map _, map_sylow_comap π hπ hE P, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hker'
    have hxk : x ∈ π.ker := hker'
    obtain ⟨m, hm⟩ := (P.2.map G.subtype) ⟨x, hx⟩
    have hxm : x ^ p ^ m = 1 := congrArg Subtype.val hm
    have h1 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hxm
    have h2 : orderOf x ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hxk
    have h3 : Nat.Coprime (p ^ m) (Nat.card π.ker) :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpk)
    have h4 : orderOf x = 1 := (Nat.Coprime.coprime_dvd_left h1 h3).eq_one_of_dvd h2
    exact Subtype.ext (orderOf_eq_one_iff.1 h4)
  · intro e he he' x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem : ∀ z : M, π z ∈ E → π (e * z * e⁻¹) ∈ E := fun z hz => by
      rw [map_mul, map_mul, map_inv]
      exact he _ hz
    have hmem' : ∀ z : M, π z ∈ E → π (e⁻¹ * z * e) ∈ E := fun z hz => by
      rw [map_mul, map_mul, map_inv]
      exact he' _ hz
    let φ : G ≃* G :=
      { toFun := fun x => ⟨e * x * e⁻¹, hmem x x.2⟩
        invFun := fun x => ⟨e⁻¹ * x * e, hmem' x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x z => Subtype.ext (by simp [mul_assoc]) }
    have hφ : (P : Subgroup G).comap φ.toMonoidHom = P := hPc.fixed φ
    have hyφ : φ y ∈ (P : Subgroup G) := by
      have : y ∈ (P : Subgroup G).comap φ.toMonoidHom := by rw [hφ]; exact hy
      exact this
    exact ⟨φ y, hyφ, rfl⟩

theorem exists_lift_card_normalizerRange_dvd {M T : Type*} [Group M] [Group T] [Finite M]
    (π : M →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) {p : ℕ}
    [Fact p.Prime] (hpk : ¬ p ∣ Nat.card π.ker) {E : Subgroup T} (hE : IsPGroup p E) :
    ∃ F : Subgroup M, IsPGroup p F ∧ F.map π = E ∧ Function.Injective (π.comp F.subtype) ∧
      Nat.card E.normalizerMonoidHom.range ∣ Nat.card F.normalizerMonoidHom.range := by
  obtain ⟨F, hFp, hFmap, hFinj, hFnorm⟩ := exists_pSubgroup_lift_normalizer π hπ hker hpk hE
  refine ⟨F, hFp, hFmap, hFinj, ?_⟩
  let eF : F ≃* E := (MonoidHom.ofInjective hFinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hFmap]))
  have heF : ∀ y : F, ((eF y : E) : T) = π (y : M) := fun y => rfl
  let ρ : MulAut E ≃* MulAut F := MulAut.congr eF.symm
  have hle : E.normalizerMonoidHom.range.map ρ.toMonoidHom ≤ F.normalizerMonoidHom.range := by
    intro y hy
    obtain ⟨β, ⟨n, rfl⟩, rfl⟩ := hy
    obtain ⟨g, hg⟩ := hπ (n : T)
    have hn1 : ∀ u ∈ E, (n : T) * u * (n : T)⁻¹ ∈ E := fun u hu =>
      (Subgroup.mem_normalizer_iff.1 n.2 u).1 hu
    have hn2 : ∀ u ∈ E, (n : T)⁻¹ * u * (n : T) ∈ E := fun u hu => by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (E : Set T)).inv_mem n.2) u).1 hu
      simpa using this
    have hgF : g ∈ Subgroup.normalizer (F : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hFnorm g (by rw [hg]; exact hn1) (by rw [hg]; exact hn2) x hx
      · intro hx
        have := hFnorm g⁻¹ (by rw [map_inv, hg]; simpa using hn2) (by rw [map_inv, hg]; simpa
          using hn1) _ hx
        have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rwa [e] at this
    refine ⟨⟨g, hgF⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply hFinj
    change π (((F.normalizerMonoidHom ⟨g, hgF⟩) x : F) : M) = π ((((MulAut.congr eF.symm)
      (E.normalizerMonoidHom n)) x : F) : M)
    have h1 : π (((((MulAut.congr eF.symm) (E.normalizerMonoidHom n)) x : F) : M)) =
        (((E.normalizerMonoidHom n) (eF x) : E) : T) := by
      rw [MulAut.congr_apply]
      change π ((eF.symm ((E.normalizerMonoidHom n) (eF (x : F))) : F) : M) = _
      rw [← heF, MulEquiv.apply_symm_apply]
    rw [h1]
    change π ((g : M) * (x : M) * (g : M)⁻¹) = (n : T) * (((eF x : E) : T)) * (n : T)⁻¹
    rw [map_mul, map_mul, map_inv, hg, ← heF]
  have h1 : Nat.card (E.normalizerMonoidHom.range.map ρ.toMonoidHom) =
      Nat.card E.normalizerMonoidHom.range := Subgroup.card_map_of_injective ρ.injective
  rw [← h1]
  exact Subgroup.card_dvd_of_le hle

end CFSG.RankThree.PartOne.N143X
