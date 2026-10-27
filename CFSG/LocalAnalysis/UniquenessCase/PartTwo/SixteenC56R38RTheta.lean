module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem finite_mulAut_theta (S : OmegaModel W) : Finite (MulAut W) := by
  haveI : Finite W := Finite.of_injective (S.e : W → Multiplicative (OmI → S.K)) S.e.injective
  exact Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

theorem card_ringEquiv_four (hK : Nat.card S.K = 4) : Nat.card (S.K ≃+* S.K) = 2 :=
  CFSG.AGLEmbedding.UnitaryModel.card_ringEquiv S.K 2 2 (by rw [hK]; norm_num)

theorem relIndex_inf_linSub_dvd_two (hK : Nat.card S.K = 4) {X : Subgroup (MulAut W)}
    (hX : X ≤ omegaNorm S) : (X ⊓ linSub S).relIndex X ∣ 2 := by
  obtain ⟨θ, -, hθ1⟩ := exists_twistHom S
  let θX : ↥X →* (S.K ≃+* S.K) := θ.comp (Subgroup.inclusion hX)
  have hker : θX.ker = (X ⊓ linSub S).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change θ (Subgroup.inclusion hX x) = 1 ↔
      (x : MulAut W) ∈ X ∧ (x : MulAut W) ∈ linSub S
    have hx := hθ1 (Subgroup.inclusion hX x)
    rw [Subgroup.coe_inclusion] at hx
    rw [hx]
    simp
  have hrange : Nat.card θX.range ∣ 2 := by
    rw [← card_ringEquiv_four S hK]
    exact Subgroup.card_subgroup_dvd_card θX.range
  change ((X ⊓ linSub S).subgroupOf X).index ∣ 2
  rw [← hker, Subgroup.index_ker]
  exact hrange

theorem card_omegaNorm_inf_linSub_dvd_of_card_four (hK : Nat.card S.K = 4) :
    Nat.card ↥(omegaNorm S ⊓ linSub S) ∣ 2 ^ 5 * 3 ^ 3 * 5 ^ 2 := by
  have hdvd : Nat.card ↥(omegaNorm S ⊓ linSub S) ∣ Nat.card ↥(scalarSub S ⊔ isoSub S) :=
    Subgroup.card_dvd_of_le (omegaNorm_inf_linSub_le_sup S)
  rw [card_scalarSub_sup_isoSub_of_card_four S hK] at hdvd
  simpa [show 3 * 7200 = 2 ^ 5 * 3 ^ 3 * 5 ^ 2 by norm_num] using hdvd

theorem card_omegaNorm_dvd_of_card_four (hK : Nat.card S.K = 4) :
    Nat.card ↥(omegaNorm S) ∣ 2 ^ 6 * 3 ^ 3 * 5 ^ 2 := by
  have hrel : (omegaNorm S ⊓ linSub S).relIndex (omegaNorm S) ∣ 2 :=
    relIndex_inf_linSub_dvd_two S hK (X := omegaNorm S) le_rfl
  have hinfl : Nat.card ↥(omegaNorm S ⊓ linSub S) ∣ 2 ^ 5 * 3 ^ 3 * 5 ^ 2 :=
    card_omegaNorm_inf_linSub_dvd_of_card_four S hK
  have hmul := Subgroup.relIndex_mul_card (H := omegaNorm S ⊓ linSub S) (K := omegaNorm S)
  rw [inf_of_le_left inf_le_left] at hmul
  rw [← hmul]
  rw [← show 2 * (2 ^ 5 * 3 ^ 3 * 5 ^ 2) = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 by norm_num]
  exact Nat.mul_dvd_mul hrel hinfl

theorem le_linSub_of_isPGroup_three (hK : Nat.card S.K = 4) {P : Subgroup (MulAut W)}
    (hP : IsPGroup 3 P) (hPN : P ≤ omegaNorm S) : P ≤ linSub S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥P := by
    haveI := finite_mulAut_theta S
    exact Finite.of_injective (Subtype.val) Subtype.coe_injective
  have hrel2 : (P ⊓ linSub S).relIndex P ∣ 2 := relIndex_inf_linSub_dvd_two S hK hPN
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hrelP : (P ⊓ linSub S).relIndex P ∣ 3 ^ k := by
    change ((P ⊓ linSub S).subgroupOf P).index ∣ 3 ^ k
    rw [← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hrelP
  have hcop : Nat.Coprime (3 ^ j) 2 := (by norm_num : Nat.Coprime 3 2).pow_left j
  have hpj1 : 3 ^ j = 1 := by
    rw [hj] at hrel2
    exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hrel2
  have hrel1 : (P ⊓ linSub S).relIndex P = 1 := by rw [hj, hpj1]
  have hle : P ≤ P ⊓ linSub S := Subgroup.relIndex_eq_one.mp hrel1
  exact (le_inf_iff.mp hle).2

private theorem le_of_isPGroup_of_relIndex_coprime {G : Type*} [Group G] {p : ℕ}
    {A N B : Subgroup G} (hn : (A.subgroupOf N).Normal) (hcop : Nat.Coprime p (A.relIndex N))
    (hB : IsPGroup p B) (hBN : B ≤ N) : B ≤ A := by
  intro x hx
  let y : ↥N := ⟨x, hBN hx⟩
  obtain ⟨k, hk⟩ := hB ⟨x, hx⟩
  have hy : y ^ p ^ k = 1 := by
    apply Subtype.ext
    have := congrArg (Subtype.val) hk
    simpa using this
  have hord1 : orderOf (QuotientGroup.mk (s := A.subgroupOf N) y) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have hord2 : orderOf (QuotientGroup.mk (s := A.subgroupOf N) y) ∣ A.relIndex N :=
    orderOf_dvd_natCard _
  have hcop' : Nat.Coprime (p ^ k) (A.relIndex N) := hcop.pow_left k
  have h1 : orderOf (QuotientGroup.mk (s := A.subgroupOf N) y) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop' hord1 hord2
  have h2 : QuotientGroup.mk (s := A.subgroupOf N) y = 1 := orderOf_eq_one_iff.mp h1
  exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y).mp h2))

private theorem card_dvd_pow_of_isPGroup {G : Type*} [Group G] [Finite G] {p j N₀ : ℕ}
    (hp : p.Prime) {P N : Subgroup G} (hP : IsPGroup p P) (hPN : P ≤ N)
    (hN : Nat.card N ∣ N₀) (hj : ¬ p ^ (j + 1) ∣ N₀) : Nat.card P ∣ p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : p ^ k ∣ N₀ := by
    rw [← hk]
    exact (Subgroup.card_dvd_of_le hPN).trans hN
  rw [hk]
  by_contra hkj
  have hjk : j + 1 ≤ k := by
    by_contra h
    exact hkj (pow_dvd_pow p (by omega))
  exact hj ((pow_dvd_pow p hjk).trans hdvd)

theorem card_dvd_of_isPGroup_five (hK : Nat.card S.K = 4) {P : Subgroup (MulAut W)}
    (hP : IsPGroup 5 P) (hPN : P ≤ omegaNorm S) : Nat.card P ∣ 5 ^ 2 := by
  haveI := finite_mulAut_theta S
  exact card_dvd_pow_of_isPGroup (by norm_num) hP hPN (card_omegaNorm_dvd_of_card_four S hK)
    (by norm_num)

theorem relIndex_omega_omegaNorm_dvd_twelve (hK : Nat.card S.K = 4)
    (hΩ : Nat.card S.omega = 3600) : S.omega.relIndex (omegaNorm S) ∣ 12 := by
  haveI := finite_mulAut_theta S
  have hΩN : S.omega ≤ omegaNorm S := Subgroup.le_normalizer
  have hmul := Subgroup.relIndex_mul_card (H := S.omega) (K := omegaNorm S)
  rw [inf_of_le_left hΩN, hΩ] at hmul
  have h1 : S.omega.relIndex (omegaNorm S) * 3600 ∣ 12 * 3600 := by
    rw [hmul]
    have := card_omegaNorm_dvd_of_card_four S hK
    norm_num at this ⊢
    exact this
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1

theorem relIndex_inf_omega_dvd_twelve (hK : Nat.card S.K = 4) (hΩ : Nat.card S.omega = 3600)
    {X : Subgroup (MulAut W)} (hX : X ≤ omegaNorm S) : (X ⊓ S.omega).relIndex X ∣ 12 := by
  haveI := finite_mulAut_theta S
  have hn : (S.omega.subgroupOf (omegaNorm S)).Normal := Subgroup.normal_in_normalizer
  let f : ↥X →* ↥(omegaNorm S) ⧸ S.omega.subgroupOf (omegaNorm S) :=
    (QuotientGroup.mk' (S.omega.subgroupOf (omegaNorm S))).comp (Subgroup.inclusion hX)
  have hker : f.ker = (X ⊓ S.omega).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change (QuotientGroup.mk (Subgroup.inclusion hX x) :
        ↥(omegaNorm S) ⧸ S.omega.subgroupOf (omegaNorm S)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    simp
  have hrange : Nat.card f.range ∣ S.omega.relIndex (omegaNorm S) :=
    Subgroup.card_subgroup_dvd_card f.range
  have h12 := relIndex_omega_omegaNorm_dvd_twelve S hK hΩ
  change ((X ⊓ S.omega).subgroupOf X).index ∣ 12
  rw [← hker, Subgroup.index_ker]
  exact hrange.trans h12

theorem le_omega_of_isPGroup_five (hK : Nat.card S.K = 4) (hΩ : Nat.card S.omega = 3600)
    {B : Subgroup (MulAut W)} (hB : IsPGroup 5 B) (hBN : B ≤ omegaNorm S) : B ≤ S.omega := by
  have hn : (S.omega.subgroupOf (omegaNorm S)).Normal := Subgroup.normal_in_normalizer
  have hdvd := relIndex_omega_omegaNorm_dvd_twelve S hK hΩ
  have hcop : Nat.Coprime 5 (S.omega.relIndex (omegaNorm S)) :=
    Nat.Coprime.coprime_dvd_right hdvd (by norm_num)
  exact le_of_isPGroup_of_relIndex_coprime hn hcop hB hBN

theorem le_omega_of_isPGroup_three_of_le_isoSub (hK : Nat.card S.K = 4)
    (hΩ : Nat.card S.omega = 3600) {P : Subgroup (MulAut W)} (hP : IsPGroup 3 P)
    (hPO : P ≤ isoSub S) : P ≤ S.omega := by
  haveI := finite_mulAut_theta S
  have hΩO : S.omega ≤ isoSub S := omega_le_isoSub S
  have hmul := Subgroup.relIndex_mul_card (H := S.omega) (K := isoSub S)
  rw [inf_of_le_left hΩO, hΩ, card_isoSub_of_card_four S hK] at hmul
  have hrel : S.omega.relIndex (isoSub S) = 2 := by
    have h : S.omega.relIndex (isoSub S) * 3600 = 2 * 3600 := by rw [hmul]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hn : (S.omega.subgroupOf (isoSub S)).Normal := by
    haveI : (S.omega.subgroupOf (isoSub S)).FiniteIndex := by
      refine ⟨?_⟩
      change (S.omega.subgroupOf (isoSub S)).index ≠ 0
      change S.omega.relIndex (isoSub S) ≠ 0
      rw [hrel]
      norm_num
    exact Subgroup.normal_of_index_eq_two hrel
  exact le_of_isPGroup_of_relIndex_coprime hn (by rw [hrel]; norm_num) hP hPO

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
