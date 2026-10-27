module

public import CFSG.OddTranspositions.SixFiveGlobal
public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem inf_closure_pair_eq_bot (hS : Setup G D) {Q : Subgroup G} (hQn : Q.Normal)
    (hQp : IsPGroup 2 Q) {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w) :
    Subgroup.closure ({u, w} : Set G) ⊓ Q = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzA, hzQ⟩ := hz
  by_contra hz1
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one hw
  have hodd : Odd (orderOf (u * w)) := hS.oddT.odd_of_not_commute hu hw hnc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey : ∀ x ∈ Q, Odd (orderOf x) → x = 1 := by
    intro x hx hoddx
    obtain ⟨n, hn⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hQp ⟨x, hx⟩
    have hn' : orderOf x = 2 ^ n := by rw [← Subgroup.orderOf_mk x hx]; exact hn
    rcases n with _ | n
    · simpa using hn'
    · rw [hn'] at hoddx
      apply absurd hoddx
      refine Nat.not_odd_iff_even.mpr ⟨2 ^ n, ?_⟩
      rw [pow_succ]; ring
  obtain ⟨k, hk | hk⟩ := CFSG.Timmesfeld.exists_zpow_of_mem_closure_pair hu2 hw2 hzA
  ·
    have hdvd : orderOf z ∣ orderOf (u * w) := by
      rw [hk]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    exact hz1 (hkey z hzQ (hodd.of_dvd_nat hdvd))
  ·
    rw [hk] at hzQ
    set r : G := u * w with hr
    have huz : u * (r ^ k * u) * u⁻¹ = r ^ (-k) * u := by
      rw [show u * (r ^ k * u) * u⁻¹ = u * r ^ k by group, hr]
      exact CFSG.Timmesfeld.mul_zpow_mul_eq_zpow_neg_mul hu2 hw2 k
    have huzQ : u * (r ^ k * u) * u⁻¹ ∈ Q := hQn.conj_mem _ hzQ u
    have h2k : r ^ (2 * k) ∈ Q := by
      have hmem : (r ^ k * u) * (u * (r ^ k * u) * u⁻¹) ∈ Q := Q.mul_mem hzQ huzQ
      rw [huz] at hmem
      have hneg : u * r ^ (-k) = r ^ k * u := by
        rw [hr]
        simpa using CFSG.Timmesfeld.mul_zpow_mul_eq_zpow_neg_mul hu2 hw2 (-k)
      have he : (r ^ k * u) * (r ^ (-k) * u) = r ^ (2 * k) := by
        rw [show (r ^ k * u) * (r ^ (-k) * u) = r ^ k * (u * r ^ (-k)) * u by group, hneg,
          show r ^ k * (r ^ k * u) * u = (r ^ k * r ^ k) * (u * u) by group, hu2, mul_one,
          ← zpow_add, show k + k = 2 * k by ring]
      rw [he] at hmem
      exact hmem
    have h2k1 : r ^ (2 * k) = 1 := by
      refine hkey _ h2k ?_
      have hdvd : orderOf (r ^ (2 * k)) ∣ orderOf r :=
        orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨2 * k, rfl⟩)
      rw [hr]
      exact hodd.of_dvd_nat hdvd
    have hrk : r ^ k = 1 := by
      have hsq : (r ^ k) * (r ^ k) = 1 := by
        rw [← zpow_add, show k + k = 2 * k by ring, h2k1]
      have hdvd : orderOf (r ^ k) ∣ orderOf r :=
        orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      have hdvd2 : orderOf (r ^ k) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
      rw [hr] at hdvd
      have hone : orderOf (r ^ k) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
        · exact h
        · exact absurd h (hodd.ne_two_of_dvd_nat hdvd)
      exact orderOf_eq_one_iff.mp hone
    rw [hrk, one_mul] at hzQ
    have hDQ : D ⊆ Q := by
      intro d hd
      obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hS.isClass hu hd)
      exact hQn.conj_mem u hzQ g
    have hGQ : (⊤ : Subgroup G) ≤ Q := by
      rw [← hS.gen]
      exact (Subgroup.closure_le (K := Q)).mpr hDQ
    have hQtop : Q = ⊤ := le_antisymm le_top hGQ
    have hP : IsPGroup 2 (⊤ : Subgroup G) := hQtop ▸ hQp
    exact hnc (hS.oddT.commute_of_isPGroup hP hu hw (Subgroup.mem_top u) (Subgroup.mem_top w))

theorem sixFive_widthStep (hS : Setup G D) {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G)
    {u w : G} (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hFnormal : (⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G).Normal) :
    Q ≤ ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ := by
  classical
  set F : Subgroup G := ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ with hF
  have hQn : Q.Normal := by rw [hQ]; exact CFSG.pCore_normal
  have hQp : IsPGroup 2 Q := by rw [hQ]; exact CFSG.pCore_isPGroup
  haveI : F.Normal := hFnormal
  set A : Subgroup G := Subgroup.closure ({u, w} : Set G) with hA
  have hQA : Q ⊔ A = ⊤ := hgenQ
  have hAQ : A ⊓ Q = ⊥ := inf_closure_pair_eq_bot hS hQn hQp hu hw hnc
  have hFQ : F ≤ Q := by
    rw [hF]
    exact sup_le (commutator_zpowers_le_of_normal hQn u) (commutator_zpowers_le_of_normal hQn w)
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one hw
  have hcomm_u : ∀ q ∈ Q, Commute (QuotientGroup.mk' F q) (QuotientGroup.mk' F u) := by
    intro q hq
    have h1 : (QuotientGroup.mk' F q) * (QuotientGroup.mk' F u) =
        (QuotientGroup.mk' F u) * (QuotientGroup.mk' F q) := by
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
      refine ⟨q⁻¹ * ⁅q, u⁆ * q, ?_, ?_⟩
      · simpa using hFnormal.conj_mem ⁅q, u⁆
          (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers u)))
          q⁻¹
      · rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hu2]
        rw [show q * u * (q⁻¹ * (q * u * q⁻¹ * u) * q) = q * (u * u) * q⁻¹ * (u * q) by group,
          hu2]
        group
    exact h1
  have hcomm_w : ∀ q ∈ Q, Commute (QuotientGroup.mk' F q) (QuotientGroup.mk' F w) := by
    intro q hq
    have h1 : (QuotientGroup.mk' F q) * (QuotientGroup.mk' F w) =
        (QuotientGroup.mk' F w) * (QuotientGroup.mk' F q) := by
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
      refine ⟨q⁻¹ * ⁅q, w⁆ * q, ?_, ?_⟩
      · simpa using hFnormal.conj_mem ⁅q, w⁆
          (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers w)))
          q⁻¹
      · rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hw2]
        rw [show q * w * (q⁻¹ * (q * w * q⁻¹ * w) * q) = q * (w * w) * q⁻¹ * (w * q) by group,
          hw2]
        group
    exact h1
  have hcent : ∀ q ∈ Q, ∀ a ∈ A, Commute (QuotientGroup.mk' F q) (QuotientGroup.mk' F a) := by
    intro q hq a ha
    have hle : A ≤ (Subgroup.centralizer ({QuotientGroup.mk' F q} : Set (G ⧸ F))).comap
        (QuotientGroup.mk' F) := by
      rw [hA]
      refine (Subgroup.closure_le (K := _)).mpr ?_
      intro x hx
      change (QuotientGroup.mk' F) x ∈ Subgroup.centralizer ({QuotientGroup.mk' F q} : Set (G ⧸ F))
      rcases hx with rfl | rfl
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm_u q hq).symm.eq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm_w q hq).symm.eq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
  have hDA : ∀ d ∈ D, QuotientGroup.mk' F d ∈ Subgroup.map (QuotientGroup.mk' F) A := by
    intro d hd
    obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hS.isClass hu hd)
    obtain ⟨q, hq, a, ha, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Q) (t := A)).mp
        (by rw [hQA]; exact Subgroup.mem_top g)
    set x : G := a * u * a⁻¹ with hx
    have hxA : x ∈ A := by
      rw [hx]
      exact A.mul_mem (A.mul_mem ha (Subgroup.subset_closure (by simp))) (A.inv_mem ha)
    refine Subgroup.mem_map.mpr ⟨x, hxA, ?_⟩
    have hq_comm : Commute (QuotientGroup.mk' F q) (QuotientGroup.mk' F x) := hcent q hq x hxA
    have hfix : QuotientGroup.mk' F q * QuotientGroup.mk' F x * (QuotientGroup.mk' F q)⁻¹ =
        QuotientGroup.mk' F x := by
      rw [hq_comm.eq]; group
    show QuotientGroup.mk' F x = QuotientGroup.mk' F (q * a * u * (q * a)⁻¹)
    rw [show q * a * u * (q * a)⁻¹ = q * x * q⁻¹ by rw [hx]; group]
    rw [map_mul, map_mul, map_inv]
    exact hfix.symm
  have htop : (⊤ : Subgroup (G ⧸ F)) = Subgroup.map (QuotientGroup.mk' F) A := by
    have hclosure : Subgroup.closure ((QuotientGroup.mk' F) '' D) = ⊤ := by
      rw [← MonoidHom.map_closure, hS.gen,
        Subgroup.map_top_of_surjective (QuotientGroup.mk' F) (QuotientGroup.mk'_surjective F)]
    have hle : Subgroup.closure ((QuotientGroup.mk' F) '' D) ≤
        Subgroup.map (QuotientGroup.mk' F) A := by
      refine (Subgroup.closure_le (K := _)).mpr ?_
      rintro x ⟨d, hd, rfl⟩
      exact hDA d hd
    rw [hclosure] at hle
    exact (le_antisymm le_top hle).symm
  have hinf : Subgroup.map (QuotientGroup.mk' F) Q ⊓ Subgroup.map (QuotientGroup.mk' F) A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxQ, hxA⟩ := hx
    rw [Subgroup.mem_map] at hxQ hxA
    obtain ⟨q, hq, rfl⟩ := hxQ
    obtain ⟨a, ha, haq⟩ := hxA
    have hmem : a⁻¹ * q ∈ F := by
      refine (QuotientGroup.eq_one_iff (a⁻¹ * q)).mp ?_
      show (QuotientGroup.mk' F) (a⁻¹ * q) = 1
      rw [map_mul, map_inv, ← haq, inv_mul_cancel]
    have haQ : a ∈ Q := by
      have hfQ : a⁻¹ * q ∈ Q := hFQ hmem
      have h := Q.mul_mem hq (Q.inv_mem hfQ)
      rwa [show q * (a⁻¹ * q)⁻¹ = a by group] at h
    have ha1 : a = 1 := by
      have h : a ∈ A ⊓ Q := ⟨ha, haQ⟩
      rw [hAQ] at h
      exact Subgroup.mem_bot.mp h
    rw [Subgroup.mem_bot]
    rw [← haq, ha1]
    exact map_one (QuotientGroup.mk' F)
  intro q hq
  have h1 : QuotientGroup.mk' F q ∈ Subgroup.map (QuotientGroup.mk' F) Q ⊓
      Subgroup.map (QuotientGroup.mk' F) A := by
    refine ⟨Subgroup.mem_map_of_mem (QuotientGroup.mk' F) hq, ?_⟩
    rw [← htop]
    exact Subgroup.mem_top _
  rw [hinf] at h1
  exact (QuotientGroup.eq_one_iff q).mp (Subgroup.mem_bot.mp h1)

theorem sixFiveGlobal_of_normalF (hS : Setup G D)
    {Q : Subgroup G} (hQ : Q = CFSG.pCore 2 G) {u w : G}
    (hu : u ∈ D) (hw : w ∈ D) (hnc : ¬ Commute u w)
    (hgenQ : Q ⊔ Subgroup.closure ({u, w} : Set G) = ⊤)
    (hFnormal : (⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G).Normal)
    (hPR : ⁅Q, Subgroup.zpowers u⁆ ≤
      Subgroup.normalizer ((⁅Q, Subgroup.zpowers w⁆ : Subgroup G) : Set G))
    (hZc : (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G) ≤ Subgroup.center G)
    (hZtop : Subgroup.center G ≤
      (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G))
    (hcardP : Nat.card (⁅Q, Subgroup.zpowers u⁆ : Subgroup G) =
      (D ∩ Subgroup.centralizer ({u} : Set G)).ncard *
        Nat.card (⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ : Subgroup G)) :
    Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ ∧
      Subgroup.center G = ⁅Q, Subgroup.zpowers u⁆ ⊓ ⁅Q, Subgroup.zpowers w⁆ ∧
      Nat.card Q = (D ∩ Subgroup.centralizer ({u} : Set G)).ncard ^ 2 *
        Nat.card (Subgroup.center G) := by
  have hQF : Q ≤ ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ :=
    sixFive_widthStep hS hQ hu hw hnc hgenQ hFnormal
  exact sixFiveGlobal hS.isClass hS.oddT hS.gen hQ hu hw hnc hgenQ hQF hPR hZc hZtop hcardP

end CFSG.OddTranspositions
