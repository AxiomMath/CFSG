module

public import CFSG.Quasithin.Vol2.Ch11SecBTCSteps
public import CFSG.Quasithin.Vol2.Ch11SecB21Hall
public import CFSG.Quasithin.Vol2.Ch11SecBTCStar

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_normalizer_of_star {H X K : Subgroup G} (hXH : X ≤ H)
    (hJ2 : IsPGroup 2 ↥(kerIn X H)) (hRJ : solvRad H ≤ kerIn X H) (hKc : K ∈ cComp H)
    (hZ : Subgroup.center ↥(E2.star X H K) = ⊥) {y : G} (hyX : y ∈ X) (hyK : y ∈ K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hyo : orderOf y = p) :
    pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJs : Group.IsSolvable ↥(kerIn X H) := by
    have := hJ2.isNilpotent
    infer_instance
  set π := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hπ
  intro r hr
  have hrX : r ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hr
  have hrH : r ∈ H := hXH hrX
  have hK'c : cjSub r K ∈ cComp H := by
    have := cComp_map_mulEquiv (MulAut.conj r) hKc
    rwa [map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hrH)] at this
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_star hXH hJs hRJ hK'c)
      (isComponent_star hXH hJs hRJ hKc) with h | h
  · exact mem_normalizer_of_map_conj_eq (eq_of_star_eq hXH hJs hK'c hKc h)
  exfalso
  have hyH : y ∈ H := hXH hyX
  have hryH : r * y * r⁻¹ ∈ H := H.mul_mem (H.mul_mem hrH hyH) (H.inv_mem hrH)
  have hc : r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 X := by
    have h1 : y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hyX) _).mp ((pCoreOf 2 X).inv_mem hr)
    have := (pCoreOf 2 X).mul_mem hr h1
    simpa [mul_assoc] using this
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨_, hc⟩
  have ha' : (r * y * r⁻¹ * y⁻¹) ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  set u := π ⟨r * y * r⁻¹, hryH⟩ with hu
  set v := π ⟨y, hyH⟩ with hv
  have huK : u ∈ E2.star X H (cjSub r K) := by
    refine ⟨⟨r * y * r⁻¹, hryH⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    show r * y * r⁻¹ ∈ cjSub r K
    rw [mem_cjSub]
    simpa [mul_assoc] using hyK
  have hvK : v ∈ E2.star X H K := ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hyK, rfl⟩
  have huv : Commute u v⁻¹ := by
    have := Subgroup.commutator_mem_commutator huK ((E2.star X H K).inv_mem hvK)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have h1 : (u * v⁻¹) ^ 2 ^ a = 1 := by
    have e : u * v⁻¹ = π ⟨r * y * r⁻¹ * y⁻¹, H.mul_mem hryH (H.inv_mem hyH)⟩ := by
      rw [hu, hv, ← map_inv, ← map_mul]
      rfl
    rw [e, ← map_pow]
    have e2 : (⟨r * y * r⁻¹ * y⁻¹, H.mul_mem hryH (H.inv_mem hyH)⟩ : ↥H) ^ 2 ^ a = 1 :=
      Subtype.ext (by simpa using ha')
    rw [e2, map_one]
  rw [huv.mul_pow, inv_pow, mul_inv_eq_one] at h1
  have hw : v ^ 2 ^ a = 1 := eq_one_of_mem_of_commutator_eq_bot hZ h
    ((E2.star X H K).pow_mem hvK _) (h1 ▸ (E2.star X H (cjSub r K)).pow_mem huK _)
  have hvp : v ^ p = 1 := by
    rw [hv, ← map_pow]
    have e3 : (⟨y, hyH⟩ : ↥H) ^ p = 1 := Subtype.ext (by simp [← hyo])
    rw [e3, map_one]
  have hv1 : v = 1 := eq_one_of_pow_two_pow_of_pow_prime hp hp2 hw hvp
  have hyJ : y ∈ kerIn X H := by
    rw [hv, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv1
    exact hv1
  obtain ⟨b, hb⟩ := hJ2 ⟨y, hyJ⟩
  have hb' : y ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hy1 : y = 1 :=
    eq_one_of_pow_two_pow_of_pow_prime hp hp2 hb' (hyo ▸ pow_orderOf_eq_one y)
  rw [hy1, orderOf_one] at hyo
  exact hp.one_lt.ne hyo

theorem exists_mem_hall_order {H X K D T : Subgroup G} (hXH : X ≤ H) (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hHK : H = K ⊔ T) (hJs : Group.IsSolvable ↥(kerIn X H))
    (hRJ : solvRad H ≤ kerIn X H) (hKc : K ∈ cComp H) (hD : Lin2.IsHallTwoPrimeOf D X)
    {y : G} (hyX : y ∈ X) (hyK : y ∈ K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hyo : orderOf y = p) : ∃ d ∈ D, d ∈ K ⊔ kerIn X H ∧ orderOf d = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := kerIn X H with hJdef
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hcj : ∀ h ∈ H, cjSub h K ≤ Subgroup.normalizer ((K ⊔ J : Subgroup G) : Set G) := by
    intro h hh
    have hK'c : cjSub h K ∈ cComp H := by
      have := cComp_map_mulEquiv (MulAut.conj h) hKc
      rwa [map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hh)] at this
    exact le_normalizer_sup_of_star hXH hJs hK'c hKc
      (CFSG.LocalCores.distinct_components_commute (isComponent_star hXH hJs hRJ hK'c)
        (isComponent_star hXH hJs hRJ hKc))
  have hEN : conjClosure K H ≤ Subgroup.normalizer ((K ⊔ J : Subgroup G) : Set G) :=
    conjClosure_le fun h hh z hz => hcj h hh (by rw [mem_cjSub]; simpa [mul_assoc] using hz)
  have hEH : conjClosure K H ≤ H := conjClosure_le fun h hh z hz =>
    H.mul_mem (H.mul_mem hh (hKH hz)) (H.inv_mem hh)
  have hsup : T ⊔ conjClosure K H = H := le_antisymm (sup_le hTH hEH)
    (hHK.le.trans (sup_le ((le_conjClosure K H).trans le_sup_right) le_sup_left))
  have h2E := B6.isTwoQuotient_of_sup_eq hT2 (le_normalizer_conjClosure K H) hsup
  have hDN : D ≤ Subgroup.normalizer ((K ⊔ J : Subgroup G) : Set G) := by
    intro d hd
    obtain ⟨a, ha⟩ := h2E d (hXH (hD.1 hd))
    have hodd : Odd (orderOf d) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard hd)
    exact hEN (mem_of_pow_two_pow_mem hodd ha)
  set W := X ⊓ (K ⊔ J) with hWdef
  have hDW : D ≤ Subgroup.normalizer (W : Set G) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hD.1 hd), hDN hd⟩
  have hHall : Lin2.IsHallTwoPrimeOf (D ⊓ W) W := by
    refine ⟨inf_le_right, hD.2.1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left), ?_⟩
    obtain ⟨m, hm⟩ := hD.2.2
    rw [B6.relIndex_inf_eq_relIndex_sup hDW]
    have hdvd : D.relIndex (D ⊔ W) ∣ D.relIndex X := by
      rw [← Subgroup.relIndex_mul_relIndex D (D ⊔ W) X le_sup_left (sup_le hD.1 inf_le_left)]
      exact Dvd.intro _ rfl
    rw [hm] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hyW : y ∈ W := ⟨hyX, Subgroup.mem_sup_left hyK⟩
  have hP : IsPGroup p ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨w, -, hle⟩ := exists_conj_le_hall hp2 hHall (Subgroup.zpowers_le.mpr hyW) hP
  have hd : w⁻¹ * y * w ∈ D ⊓ W := mem_conjSub.mp (hle (Subgroup.mem_zpowers y))
  refine ⟨w⁻¹ * y * w, hd.1, hd.2.2, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) y
  rw [MulAut.conj_apply, inv_inv] at this
  rw [this, hyo]

end CFSG.Quasithin.Vol2.Ch11.SecB
