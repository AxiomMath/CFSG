module

public import CFSG.RankThree.PartOne.N143X.WeylLift
public import CFSG.Open.StatedAPI
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.N143X.Weights

public section

namespace CFSG.RankThree.PartOne.N143X

open Matrix CFSG CFSG.Assembly.LowTwoRank

theorem isElementaryAbelian_of_equiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsElementaryAbelian p G) : IsElementaryAbelian p H :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem not_dvd_card_scalarKernel' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (M : Subgroup (GL ι K)) [Finite M] {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) :
    ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf M) :=
  CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf M hp hpd hd

theorem exists_cover_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {p : ℕ}
    (hp : p.Prime) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    ∃ F : Subgroup (GL ι K), IsElementaryAbelian p F ∧ F ≤ M ∧ Nat.card F = Nat.card E ∧
      Nat.card E.normalizerMonoidHom.range ∣ Nat.card F.normalizerMonoidHom.range := by
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
  obtain ⟨F₀, hF₀p, hF₀map, hF₀inj, hdvd⟩ := exists_lift_card_normalizerRange_dvd π hπ hker hpk hEp
  let eF : F₀ ≃* E := (MonoidHom.ofInjective hF₀inj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hF₀map]))
  have hF₀el : IsElementaryAbelian p F₀ := isElementaryAbelian_of_equiv eF.symm hE
  have : IsElementaryAbelian p F₀ := hF₀el
  refine ⟨F₀.map M.subtype, IsElementaryAbelian.map_subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.card_congr eF.toEquiv
  · exact hdvd.trans (card_normalizerRange_dvd_of_injective M.subtype M.subtype_injective F₀)

theorem card_dvd_120_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {p : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) (hcard : Fintype.card ι ≤ 5) :
    Nat.card E.normalizerMonoidHom.range ∣ 120 := by
  obtain ⟨F, hF, -, -, hdvd⟩ := exists_cover_of_matrix_model M e hp hd hpd hE
  exact hdvd.trans (card_normalizer_range_dvd_120 F hpK hcard)

theorem card_dvd_384_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {p : ℕ}
    (hp : p.Prime) (hp2 : p % 2 = 1) (hpK : (p : K) ≠ 0) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hMJ : ∀ g ∈ M, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * ((g : GL ι K) : Matrix ι ι K) = J)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) (hcard : Fintype.card ι ≤ 8) :
    Nat.card E.normalizerMonoidHom.range ∣ 384 := by
  obtain ⟨F, hF, hFM, -, hdvd⟩ := exists_cover_of_matrix_model M e hp hd hpd hE
  exact hdvd.trans (card_normalizer_range_dvd_384 F hpK hp2 J hJ (fun g hg => hMJ g (hFM hg))
    hcard)

theorem factorization_three_le_one_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T]
    (e : T ≃* StatedProj M) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) (hcard : Fintype.card ι ≤ 5) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 :=
  factorization_three_le_of_dvd_120 (card_dvd_120_of_matrix_model M e hp hpK hd hpd hE hcard)

theorem factorization_three_le_one_of_matrix_model_form {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T]
    (e : T ≃* StatedProj M) {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hpK : (p : K) ≠ 0)
    {d : ℕ} (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1)
    (hpd : ¬ p ∣ d) (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hMJ : ∀ g ∈ M, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * ((g : GL ι K) : Matrix ι ι K) = J)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) (hcard : Fintype.card ι ≤ 8) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 :=
  factorization_three_le_of_dvd_384
    (card_dvd_384_of_matrix_model M e hp hp2 hpK hd hpd J hJ hMJ hE hcard)

theorem card_dvd_120_of_embedding {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {T : Type} [Group T] (ψ : T →* GL ι K) (hψ : Function.Injective ψ) {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {E : Subgroup T} (hE : IsElementaryAbelian p E)
    (hcard : Fintype.card ι ≤ 5) : Nat.card E.normalizerMonoidHom.range ∣ 120 := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p (E.map ψ) := IsElementaryAbelian.map (A := E) ψ
  exact (card_normalizerRange_dvd_of_injective ψ hψ E).trans
    (card_normalizer_range_dvd_120 (E.map ψ) hpK hcard)

theorem factorization_three_le_one_of_embedding {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {T : Type} [Group T] (ψ : T →* GL ι K) (hψ : Function.Injective ψ)
    {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {E : Subgroup T} (hE : IsElementaryAbelian p E)
    (hcard : Fintype.card ι ≤ 5) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 :=
  factorization_three_le_of_dvd_120 (card_dvd_120_of_embedding ψ hψ hp hpK hE hcard)

end CFSG.RankThree.PartOne.N143X
