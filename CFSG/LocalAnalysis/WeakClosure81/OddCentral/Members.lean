module
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenSix
public import CFSG.LocalAnalysis.WeakClosure81.SevenThirteen
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem hyp711_of_mem (h : Hyp711 V H E) {U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    Hyp711 U H E := by
  have hO := omegaSet_eq_of_mem hU
  have hK := kSub_eq_of_mem hU
  have hI := iSub_eq_of_mem hU
  obtain ⟨k₀, hk₀, hk₀e⟩ := h.transitive U hU
  refine
    { elemAbelian := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
      ti := isTI_of_mem_omegaSet hU h.ti
      noncyclic := by rw [hk₀e, card_conjSubgroup']; exact h.noncyclic
      abelian := h.abelian
      le := h.le
      normal := h.normal
      mem := by rw [hO]; exact hU
      omega_le := by rw [hO]; exact h.omega_le
      iSub_le := by rw [hI, hK]; exact h.iSub_le
      pcore_le := by rw [hK]; exact h.pcore_le
      jnormal := by rw [hK]; exact h.jnormal
      oddCore := by rw [hK]; exact h.oddCore
      transitive := ?_ }
  intro W hW
  rw [hO] at hW
  obtain ⟨k, hk, rfl⟩ := h.transitive W hW
  refine ⟨k₀⁻¹ * k, ?_, ?_⟩
  · rw [hK]; exact (kSub V H E).mul_mem ((kSub V H E).inv_mem hk₀) hk
  · rw [hk₀e, CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_left]

theorem eq_zpowers_of_card_two {X : Type} [Group X] {S : Subgroup X} (hS : Nat.card S = 2)
    {a : X} (ha : a ∈ S) (ha1 : a ≠ 1) : S = zpowers a := by
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have hle : zpowers a ≤ S := (zpowers_le).mpr ha
  have hdvd : orderOf a ∣ 2 := hS ▸ Subgroup.orderOf_dvd_natCard S ha
  have hne : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
  have ho : orderOf a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hS, Nat.card_zpowers, ho])).symm

theorem eq_one_or_eq_of_mem_zpowers {X : Type} [Group X] {e x : X} (he : e * e = 1)
    (hx : x ∈ zpowers e) : x = 1 ∨ x = e := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  have he2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, he2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, he2, one_zpow, one_mul, zpow_one]

theorem inf_eq_bot_of_ne (h : Hyp711 V H E) {U U' : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hU' : U' ∈ omegaSet V H E) (hne : U ≠ U') : U ⊓ U' = ⊥ := by
  obtain ⟨a, rfl, -, -⟩ := mem_omegaSet.mp hU
  obtain ⟨b, rfl, -, -⟩ := mem_omegaSet.mp hU'
  exact (inf_conjSubgroup_eq_bot_or_eq h.ti a b).resolve_right hne



theorem commutator_mem_inf (h : Hyp711 V H E) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    {u : G} (hu : u ∈ U) {a : G} (ha : a ∈ iSub V H E) :
    u * a * u⁻¹ * a⁻¹ ∈ U ⊓ iSub V H E := by
  have hle := commutator_iSub_zpowers_le_inf_iSub (hyp711_of_mem h hU) hu
  rw [iSub_eq_of_mem hU] at hle
  have hmem : ⁅a, u⁆ ∈ ⁅iSub V H E, zpowers u⁆ :=
    Subgroup.commutator_mem_commutator ha (mem_zpowers u)
  have := (U ⊓ iSub V H E).inv_mem (hle hmem)
  rwa [commutatorElement_inv, commutatorElement_def] at this

theorem isPGroup_of_barSub {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {P : Subgroup G}
    (hPK : P ≤ kSub V H E) (hP : IsPGroup 2 ↥(barSub (kSub V H E) φ P)) : IsPGroup 2 ↥P := by
  have hmap2 : IsPGroup 2 ((P.subgroupOf (kSub V H E)).map φ) := hP
  have hker : φ.ker = (pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact hφ.ker_iff x
  have hJ2 : IsPGroup 2 (pCoreOf 2 (kSub V H E)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (kSub V H E)
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E))).symm
  have hcomap2 : IsPGroup 2 (((P.subgroupOf (kSub V H E)).map φ).comap φ) :=
    IsPGroup.comap_of_ker_isPGroup hmap2 φ hker2
  have hPsub : IsPGroup 2 (P.subgroupOf (kSub V H E)) :=
    hcomap2.to_le (Subgroup.le_comap_map φ (P.subgroupOf (kSub V H E)))
  exact hPsub.of_equiv (Subgroup.subgroupOfEquivOfLe hPK)

theorem commute_of_isPGroup (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {U U' : Subgroup G} (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    (hP : IsPGroup 2 ↥(barSub (kSub V H E) φ U ⊔ barSub (kSub V H E) φ U')) :
    ∀ u ∈ U, ∀ u' ∈ U', u * u' = u' * u := by
  have hKH : (kSub V H E) ≤ H := kSub_le_of_forall_le h.omega_le
  have hJK : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
    CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E)
  obtain ⟨k₁, hk₁, rfl⟩ := h.transitive U hU
  obtain ⟨k₂, hk₂, rfl⟩ := h.transitive U' hU'
  have hUK : conjSubgroup V k₁ ≤ (kSub V H E) := le_kSub hU
  have hU'K : conjSubgroup V k₂ ≤ (kSub V H E) := le_kSub hU'
  have hconj : conjSubgroup (conjSubgroup V k₁) (k₁⁻¹ * k₂) = conjSubgroup V k₂ := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have hJbot : barSub (kSub V H E) φ (pCoreOf 2 (kSub V H E)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hx
    exact (Subgroup.mem_bot).mpr ((hφ.ker_iff k).mpr hk)
  have hPJ : IsPGroup 2 ↥(conjSubgroup V k₁ ⊔ conjSubgroup V k₂ ⊔ (pCoreOf 2 (kSub V H E))) := by
    apply isPGroup_of_barSub hφ (sup_le (sup_le hUK hU'K) hJK)
    rw [barSub_sup (sup_le hUK hU'K) hJK φ, barSub_sup hUK hU'K φ, hJbot,
      sup_bot_eq]
    exact hP
  have hOm : ∀ W ∈ omegaSet (conjSubgroup V k₁) H E, W ≤ H := by
    rw [omegaSet_eq_of_mem hU]; exact h.omega_le
  have hcomm := seven_three_one (V := conjSubgroup V k₁) (H := H) (E := E) (J := pCoreOf 2 (kSub V H E))
    (isElemAbelian_of_mem_omegaSet h.elemAbelian hU) (isTI_of_mem_omegaSet hU h.ti)
    h.abelian h.le h.normal (by rw [omegaSet_eq_of_mem hU]; exact hU) hOm h.pcore_le h.jnormal
    (h := k₁⁻¹ * k₂) (H.mul_mem (H.inv_mem (hKH hk₁)) (hKH hk₂)) (by rw [hconj]; exact hPJ)
  intro u hu u' hu'
  exact hcomm u hu u' (by rw [hconj]; exact hu')

theorem card_barSub_of_mem (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : Nat.card (barSub (kSub V H E) φ U) = 2 := by
  obtain ⟨k, hk, rfl⟩ := h.transitive U hU
  rw [show conjSubgroup V k = conjSubgroup V ((⟨k, hk⟩ : ↥(kSub V H E)) : G) from rfl,
    barSub_conjSubgroup φ V ⟨k, hk⟩]
  rw [CFSG.Quasithin.conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  exact hS

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
