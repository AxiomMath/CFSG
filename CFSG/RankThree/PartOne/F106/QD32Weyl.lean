module

public import CFSG.RankThree.PartOne.F106.QD32Dim
public import CFSG.RankThree.PartOne.F106.QD32Perm
public import CFSG.RankThree.PartOne.N143X.WeylMatrix

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N143X

theorem exists_qd32_embedding_normalizerRange {T : Type} [Group T] {E R : Subgroup T}
    (hRN : R ≤ normalizer (E : Set T)) (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : T) ∈ centralizer (E : Set T)) :
    ∃ f : QD32 →* E.normalizerMonoidHom.range, Function.Injective f := by
  let ι : ↥R →* ↥(normalizer (E : Set T)) := Subgroup.inclusion hRN
  let θ : ↥R →* E.normalizerMonoidHom.range :=
    (E.normalizerMonoidHom.comp ι).codRestrict _ (fun r => ⟨ι r, rfl⟩)
  have hθ : ∀ r : ↥R, θ r = 1 ↔ ψ r = 1 := by
    intro r
    rw [hψc]
    constructor
    · intro h
      have h1 : E.normalizerMonoidHom (ι r) = 1 := congrArg Subtype.val h
      have h2 : ι r ∈ E.normalizerMonoidHom.ker := h1
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
      exact h2
    · intro h
      apply Subtype.ext
      have : ι r ∈ E.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        exact h
      exact this
  have hker : ψ.ker ≤ θ.ker := fun r hr => (hθ r).mpr hr
  refine ⟨ψ.liftOfRightInverse (Function.surjInv hψs) (Function.rightInverse_surjInv hψs)
    ⟨θ, hker⟩, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨r, rfl⟩ := hψs x
  rw [MonoidHom.liftOfRightInverse_comp_apply] at hx
  exact (hθ r).mp hx

theorem exists_normalizerRange_embedding_of_injective {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Injective f) (E : Subgroup G) :
    ∃ g : E.normalizerMonoidHom.range →* (E.map f).normalizerMonoidHom.range,
      Function.Injective g := by
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
  refine ⟨(ρ.toMonoidHom.comp E.normalizerMonoidHom.range.subtype).codRestrict _
    (fun w => hle ⟨w, w.2, rfl⟩), ?_⟩
  intro x y hxy
  exact Subtype.ext (ρ.injective (congrArg Subtype.val hxy))

theorem exists_lift_normalizerRange_embedding {M T : Type*} [Group M] [Group T] [Finite M]
    (π : M →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) {p : ℕ}
    [Fact p.Prime] (hpk : ¬ p ∣ Nat.card π.ker) {E : Subgroup T} (hE : IsPGroup p E) :
    ∃ F : Subgroup M, IsPGroup p F ∧ F.map π = E ∧ Function.Injective (π.comp F.subtype) ∧
      ∃ g : E.normalizerMonoidHom.range →* F.normalizerMonoidHom.range, Function.Injective g := by
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
      have := (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (E : Set T)).inv_mem n.2) u).1 hu
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
  exact ⟨(ρ.toMonoidHom.comp E.normalizerMonoidHom.range.subtype).codRestrict _
    (fun w => hle ⟨w, w.2, rfl⟩), fun x y hxy =>
      Subtype.ext (ρ.injective (congrArg Subtype.val hxy))⟩

theorem exists_cover_embedding_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M)
    {p : ℕ} (hp : p.Prime) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    ∃ F : Subgroup (GL ι K), IsElementaryAbelian p F ∧ F ≤ M ∧ Nat.card F = Nat.card E ∧
      ∃ g : E.normalizerMonoidHom.range →* F.normalizerMonoidHom.range, Function.Injective g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup M := (StatedScalars ι K).subgroupOf M
  let π : M →* T := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
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
  have hEp : IsPGroup p E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p E
  obtain ⟨F₀, hF₀p, hF₀map, hF₀inj, g₁, hg₁⟩ :=
    exists_lift_normalizerRange_embedding π hπ hker hpk hEp
  let eF : F₀ ≃* E := (MonoidHom.ofInjective hF₀inj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hF₀map]))
  have hF₀el : IsElementaryAbelian p F₀ := isElementaryAbelian_of_equiv eF.symm hE
  have : IsElementaryAbelian p F₀ := hF₀el
  obtain ⟨g₂, hg₂⟩ := exists_normalizerRange_embedding_of_injective M.subtype M.subtype_injective F₀
  refine ⟨F₀.map M.subtype, IsElementaryAbelian.map_subtype, ?_, ?_, g₂.comp g₁, hg₂.comp hg₁⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.card_congr eF.toEquiv

theorem false_of_qd32_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {q d : ℕ}
    (hq : q.Prime) (hqK : (q : K) ≠ 0)
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hqd : ¬ q ∣ d)
    (hι : Fintype.card ι < 16) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (hRN : R ≤ normalizer (E : Set T)) (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : T) ∈ centralizer (E : Set T)) : False := by
  obtain ⟨F, hF, -, -, g, hg⟩ := exists_cover_embedding_of_matrix_model M e hq hd hqd hE
  obtain ⟨f, hf⟩ := exists_qd32_embedding_normalizerRange hRN ψ hψs hψc
  have : IsElementaryAbelian q F := hF
  exact not_exists_qd32_embedding hι (faithfulSmall_normalizer_range F hqK) ⟨g.comp f, hg.comp hf⟩

theorem false_of_qd32_embedding_gl {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {T : Type} [Group T] (φ : T →* GL ι K) (hφ : Function.Injective φ) {q : ℕ} (hq : q.Prime)
    (hqK : (q : K) ≠ 0) (hι : Fintype.card ι < 16) {E R : Subgroup T}
    (hE : IsElementaryAbelian q E) (hRN : R ≤ normalizer (E : Set T)) (ψ : ↥R →* QD32)
    (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : T) ∈ centralizer (E : Set T)) : False := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_normalizerRange_embedding_of_injective φ hφ E
  obtain ⟨f, hf⟩ := exists_qd32_embedding_normalizerRange hRN ψ hψs hψc
  have : IsElementaryAbelian q (E.map φ) := IsElementaryAbelian.map (A := E) φ
  exact not_exists_qd32_embedding hι (faithfulSmall_normalizer_range (E.map φ) hqK)
    ⟨g.comp f, hg.comp hf⟩

theorem card_ge_pow_four_of_normalizer_qd32 {T : Type} [Group T] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {E R : Subgroup T} [Finite E] (hE : IsElementaryAbelian q E)
    (hRN : R ≤ normalizer (E : Set T)) (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : T) ∈ centralizer (E : Set T)) : q ^ 4 ≤ Nat.card E := by
  obtain ⟨f, hf⟩ := exists_qd32_embedding_normalizerRange hRN ψ hψs hψc
  have : Fact q.Prime := ⟨hq⟩
  refine card_ge_pow_four_of_qd32 hq hq2 (fun x y => hE.is_comm.comm x y) (fun x => ?_)
    (E.normalizerMonoidHom.range.subtype.comp f)
    (E.normalizerMonoidHom.range.subtype_injective.comp hf)
  exact Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian (p := q) (x : T) x.2)

end CFSG.RankThree.PartOne.F106
