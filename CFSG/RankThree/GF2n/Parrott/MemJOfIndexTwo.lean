module

public import CFSG.RankThree.GF2n.Parrott.CommutatorCentralizer
public import CFSG.GroupTheory.ClassTwoInvolutionIndexTwo

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem mem_center_J_iff (j : J z) :
    j ∈ Subgroup.center (J z) ↔ (j : G) ∈ centerIn (J z) := by
  rw [← QuotientV.centerIn_subgroupOf_eq_center, Subgroup.mem_subgroupOf]

theorem conjV_eq_one_of_conjZ_eq_one_of_sq_mem_centralizer (h : Tim79a.ParrottHyp z)
    {x : ↥(H z)} (hZx : conjZ z x = 1)
    (hsq : (x : G) ^ 2 ∈ Subgroup.centralizer (J z : Set G))
    (hidx : (Subgroup.centralizer {(x : G)}).relIndex (J z) = 2) :
    conjV h x = 1 := by
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  have hzc : Subgroup.zpowers z ≤ centerIn (J z) :=
    Subgroup.zpowers_le_of_mem ⟨z_mem_J h, z_centralizes_J h⟩
  have hsqc : ∀ v : J z, v * v ∈ Subgroup.center (J z) := fun v =>
    (mem_center_J_iff _).mpr (sq_mem_centerIn_J h v.2)
  have hcom : ∀ a b : J z, ⁅a, b⁆ ∈ Subgroup.center (J z) := by
    intro a b
    rw [mem_center_J_iff]
    have h1 : ((⁅a, b⁆ : J z) : G) ∈ ⁅J z, J z⁆ := by
      have := Subgroup.commutator_mem_commutator a.2 b.2
      simpa [commutatorElement_def] using this
    exact hzc (hJcomm ▸ h1)
  have hσσ : ∀ j : J z, conjJ' z x (conjJ' z x j) = j := by
    intro j
    apply Subtype.ext
    rw [conjJ'_apply_coe, conjJ'_apply_coe]
    have hc : (j : G) * ((x : G) * (x : G)) = ((x : G) * (x : G)) * (j : G) := by
      have := Subgroup.mem_centralizer_iff.mp hsq (j : G) j.2
      rwa [pow_two] at this
    calc (x : G) * ((x : G) * (j : G) * (x : G)⁻¹) * (x : G)⁻¹
        = ((x : G) * (x : G)) * (j : G) * ((x : G) * (x : G))⁻¹ := by group
      _ = ((j : G) * ((x : G) * (x : G))) * ((x : G) * (x : G))⁻¹ := by rw [hc]
      _ = (j : G) := by group
  have hZ : ∀ c ∈ Subgroup.center (J z), conjJ' z x c = c := by
    intro c hc
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    exact mul_mul_inv_eq_of_conjZ_eq_one hZx ((mem_center_J_iff c).mp hc)
  have hDmem : ∀ j : J z, j ∈ centralizerJ x ↔ conjJ' z x j = j := fun j => by
    rw [← autFixedSubgroup_conjJ'_eq_centralizerJ, mem_autFixedSubgroup]
  have hD : (centralizerJ x).index = 2 := by
    have : centralizerJ x = (Subgroup.centralizer {(x : G)}).subgroupOf (J z) :=
      Subgroup.inf_subgroupOf_right _ _
    rw [this]
    exact hidx
  have key : ∀ j : J z, conjJ' z x j * j⁻¹ ∈ Subgroup.center (J z) := fun j =>
    CFSG.GroupTheory.apply_mul_inv_mem_center_of_index_eq_two_of_class_two hsqc hcom
      (conjJ' z x) hσσ hZ hDmem hD j
  refine MulEquiv.ext fun v => ?_
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
  rw [conjV_mk]
  have hker : conjJ' z x j * j⁻¹ ∈ (QuotientV.pi z).ker := by
    rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf]
    exact (mem_center_J_iff _).mp (key j)
  have h1 := MonoidHom.mem_ker.mp hker
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

private theorem card_center_J (h : Tim79a.ParrottHyp z) : Nat.card (Subgroup.center (J z)) = 4 := by
  rw [← card_centerIn_J h, centerIn_eq_map_center,
    Subgroup.card_map_of_injective (J z).subtype_injective]

omit [Finite G] in
private theorem centralizer_J_inf_H_le (h : Tim79a.ParrottHyp z) :
    H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z := by
  obtain ⟨-, -, -, hcent, -⟩ := h
  simpa [J, H] using hcent

private theorem prime_eq_two_of_mem_ker (h : Tim79a.ParrottHyp z) {y : ↥(H z)}
    (hZy : conjZ z y = 1) (hVy : conjV h y = 1) {q : ℕ} (hq : q.Prime) (hyq : orderOf y = q) :
    q = 2 := by
  by_contra hq2
  have hcop : Nat.Coprime (orderOf y) (Nat.card (J z)) := by
    rw [hyq, card_J h]
    exact Nat.Coprime.pow_right 10 ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hcard := card_centralizerJ_eq_card_inf_mul_card_fixedBy h hcop
  have hZle : Subgroup.center (J z) ≤ centralizerJ y := by
    intro c hc
    rw [mem_centralizerJ_iff]
    have h1 := mul_mul_inv_eq_of_conjZ_eq_one hZy ((mem_center_J_iff c).mp hc)
    calc (c : G) * (y : G) = ((y : G) * (c : G) * (y : G)⁻¹) * (y : G) := by rw [h1]
      _ = (y : G) * (c : G) := by group
  rw [inf_eq_right.mpr hZle, hVy, map_one, MulAction.fixedBy_one_eq_univ, Nat.card_univ,
    card_center_J h, QuotientV.card_V h] at hcard
  have htop : centralizerJ y = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hcard, card_J h]
    norm_num
  have hcent : (y : G) ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have : (⟨j, hj⟩ : J z) ∈ centralizerJ y := htop ▸ Subgroup.mem_top _
    exact mem_centralizerJ_iff.mp this
  have hyJ : (y : G) ∈ J z := centralizer_J_inf_H_le h ⟨y.2, hcent⟩
  have hdvd : q ∣ Nat.card (J z) := by
    have := Subgroup.orderOf_dvd_natCard (J z) hyJ
    rwa [Subgroup.orderOf_coe, hyq] at this
  rw [card_J h] at hdvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))

theorem mem_J_of_conjZ_eq_one_of_conjV_eq_one (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hZx : conjZ z x = 1) (hVx : conjV h x = 1) : (x : G) ∈ J z := by
  let K : Subgroup ↥(H z) := (conjZ z).ker ⊓ (conjV h).ker
  have hKn : K.Normal := inferInstance
  have hKp : IsPGroup 2 K := by
    have hne : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hne (p := 2) (fun {q} hq hqdvd => by
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      refine prime_eq_two_of_mem_ker h (y := (y : ↥(H z)))
        (MonoidHom.mem_ker.mp y.2.1) (MonoidHom.mem_ker.mp y.2.2) hq ?_
      rw [Subgroup.orderOf_coe, hy])
    exact IsPGroup.of_card hpow
  have hle : K ≤ pCore 2 ↥(H z) := by
    unfold CFSG.pCore
    exact le_sSup ⟨hKn, hKp⟩
  have hxK : x ∈ K := ⟨MonoidHom.mem_ker.mpr hZx, MonoidHom.mem_ker.mpr hVx⟩
  have hx : x ∈ (J z).subgroupOf (H z) := by
    rw [J_subgroupOf_eq_pCore]
    exact hle hxK
  exact Subgroup.mem_subgroupOf.mp hx

theorem mem_J_of_conjZ_eq_one_of_sq_mem_centralizer (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hZx : conjZ z x = 1)
    (hsq : (x : G) ^ 2 ∈ Subgroup.centralizer (J z : Set G))
    (hidx : (Subgroup.centralizer {(x : G)}).relIndex (J z) = 2) :
    (x : G) ∈ J z :=
  mem_J_of_conjZ_eq_one_of_conjV_eq_one h hZx
    (conjV_eq_one_of_conjZ_eq_one_of_sq_mem_centralizer h hZx hsq hidx)

end CFSG.RankThree.GF2n.Parrott
