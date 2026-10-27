module

public import CFSG.Sporadic.Th.Recog.CentSLocal
public import CFSG.GroupTheory.PSL27Recognition
public import CFSG.GroupTheory.CentralSplitTransfer
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Sporadic.Th.Recog

variable {G : Type} [Group G] [Finite G]


theorem commutator_centralizer_s_facts (C : ThCore G)
    (sM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4)) :
    ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G), Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆
        ⊓ Subgroup.zpowers (C.ψ sM : G) = ⊥ ∧
      ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
          Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ ⊔ Subgroup.zpowers (C.ψ sM : G) =
        Subgroup.centralizer ({(C.ψ sM : G)} : Set G) ∧
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel
          ↥⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
            Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ .PSL 2 7 1 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel
          ↥⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
            Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ .PSL 2 3 2) := by
  classical
  let s : G := (C.ψ sM : G)
  let CS : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let š : ↥CS := ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let N : Subgroup ↥CS := Subgroup.zpowers š
  have hsord : orderOf s = 7 := by
    rw [show s = ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) from rfl,
      Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hsM]
  have hšord : orderOf š = 7 := by
    rw [← Subgroup.orderOf_coe š]
    exact hsord
  have hcenter : š ∈ Subgroup.center ↥CS := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_singleton_iff.mp y.2
  haveI : N.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcenter)
  let X : Type := ↥CS ⧸ N
  let π : ↥CS →* X := QuotientGroup.mk' N
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπker : π.ker = N := QuotientGroup.ker_mk' N
  letI : Finite X := Finite.of_surjective π hπsurj
  obtain ⟨hcent, hO, j, hj⟩ := quotient_centralizer_facts C sM hsM hM7 π hπsurj hπker
  have hjne : j ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hj
    exact absurd hj (by norm_num)
  haveI : Nontrivial X := ⟨j, 1, hjne⟩
  have h7or9 := CFSG.statedClassicalModel_psl_two_seven_or_nine_of_centralizers hO hcent
  have hXcard : Nat.card X = 168 ∨ Nat.card X = 360 := by
    rcases h7or9 with h | h
    · exact Or.inl (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h)
    · exact Or.inr (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine h)
  have hXsimple : IsSimpleGroup X := by
    rcases h7or9 with h | h
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two h
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two h
  haveI : IsSimpleGroup X := hXsimple
  have hXperfect : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      have hcomm : IsMulCommutative X := (commutator_eq_bot_iff X).mp h
      haveI : IsMulCommutative X := hcomm
      have hprime : Nat.Prime (Nat.card X) :=
        (Group.is_simple_iff_prime_card (α := X)).mp hXsimple
      rcases hXcard with hc | hc <;> rw [hc] at hprime <;> norm_num at hprime
    · exact h
  have hcardN : Nat.card ↥N = 7 := by
    rw [Nat.card_zpowers, hšord]
  have hcardCS : Nat.card ↥CS = 7 * Nat.card X := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardN] at h
    change Nat.card ↥CS = 7 * Nat.card (↥CS ⧸ N)
    rw [mul_comm]
    exact h
  have hPcomm : ∃ P : Sylow 7 ↥CS, IsMulCommutative ↥P := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    let P : Sylow 7 ↥CS := Classical.choice Sylow.nonempty
    have hexp : ∃ n, Nat.card ↥P = 7 ^ n := IsPGroup.iff_card.mp P.isPGroup'
    obtain ⟨n, hn⟩ := hexp
    have hdvd : 7 ^ n ∣ 7 * Nat.card X := by
      rw [← hcardCS, ← hn]
      exact Subgroup.card_subgroup_dvd_card (P : Subgroup ↥CS)
    have hn2 : n ≤ 2 := by
      rcases hXcard with hc | hc <;> rw [hc] at hdvd
      · by_contra h
        have h3 : 7 ^ 3 ∣ 7 ^ n := pow_dvd_pow 7 (by omega)
        have h343 : 7 ^ 3 ∣ 1176 := h3.trans hdvd
        norm_num at h343
      · by_contra h
        have h3 : 7 ^ 3 ∣ 7 ^ n := pow_dvd_pow 7 (by omega)
        have h343 : 7 ^ 3 ∣ 2520 := h3.trans hdvd
        norm_num at h343
    have hab : IsMulCommutative ↥P := by
      interval_cases n
      · have h1 : Nat.card ↥P = 1 := by rw [hn]; norm_num
        haveI : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.mp h1).1
        exact IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _
      · haveI : IsCyclic ↥P := isCyclic_of_prime_card (p := 7) (by rw [hn]; norm_num)
        exact IsCyclic.isMulCommutative
      · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7) (by rw [hn])
    exact ⟨P, hab⟩
  obtain ⟨P, hPcomm⟩ := hPcomm
  have hinf : commutator ↥CS ⊓ N = ⊥ := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact CFSG.GroupTheory.commutator_inf_zpowers_eq_bot P hPcomm hcenter hšord
  have hmap : Subgroup.map π (commutator ↥CS) = ⊤ := by
    change Subgroup.map π ⁅(⊤ : Subgroup ↥CS), ⊤⁆ = ⊤
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπsurj]
    exact hXperfect
  have hsup : commutator ↥CS ⊔ N = ⊤ := by
    have h1 : Subgroup.comap π (Subgroup.map π (commutator ↥CS)) = ⊤ := by
      rw [hmap, Subgroup.comap_top]
    rw [Subgroup.comap_map_eq, hπker] at h1
    exact h1
  have hLdef : Subgroup.map CS.subtype (commutator ↥CS) = ⁅CS, CS⁆ :=
    Subgroup.map_subtype_commutator CS
  have hzp : Subgroup.map CS.subtype N = Subgroup.zpowers s := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hfirst : ⁅CS, CS⁆ ⊓ Subgroup.zpowers s = ⊥ := by
    rw [← hLdef, ← hzp,
      ← Subgroup.map_inf_eq _ _ CS.subtype CS.subtype_injective, hinf, Subgroup.map_bot]
  have hsecond : ⁅CS, CS⁆ ⊔ Subgroup.zpowers s = CS := by
    rw [← hLdef, ← hzp, ← Subgroup.map_sup, hsup]
    rw [Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨hfirst, hsecond, ?_⟩
  let πL : ↥(commutator ↥CS) →* X := π.comp (commutator ↥CS).subtype
  have hπLinj : Function.Injective πL := by
    intro x y hxy
    have hmem : ((x : ↥CS) * (y : ↥CS)⁻¹) ∈ commutator ↥CS :=
      (commutator ↥CS).mul_mem x.2 ((commutator ↥CS).inv_mem y.2)
    have hmemN : ((x : ↥CS) * (y : ↥CS)⁻¹) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change π ((x : ↥CS) * (y : ↥CS)⁻¹) = 1
      have h1 : πL (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      exact h1
    have hbot : ((x : ↥CS) * (y : ↥CS)⁻¹) ∈ commutator ↥CS ⊓ N := ⟨hmem, hmemN⟩
    rw [hinf, Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  have hπLsurj : Function.Surjective πL := by
    intro z
    have hz : z ∈ Subgroup.map π (commutator ↥CS) := by
      rw [hmap]
      exact Subgroup.mem_top z
    rw [Subgroup.mem_map] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    exact ⟨⟨x, hx⟩, hxz⟩
  let e : ↥(commutator ↥CS) ≃* X := MulEquiv.ofBijective πL ⟨hπLinj, hπLsurj⟩
  let eL : ↥(commutator ↥CS) ≃* ↥⁅CS, CS⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥CS) CS.subtype CS.subtype_injective).trans
      (MulEquiv.subgroupCongr hLdef)
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥⁅CS, CS⁆ .PSL 2 7 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥⁅CS, CS⁆ .PSL 2 3 2 := by
    rcases h7or9 with h | h
    · exact Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (eL.symm.trans e).symm h)
    · exact Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (eL.symm.trans e).symm h)
  exact hmodel

theorem psi_D8_le_L (C : ThCore G)
    (sM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4))
    (D8 : Subgroup ↥CFSG.Sporadic.Th.Max3.M) (hD8s : D8 ≤ Subgroup.centralizer {sM})
    (hD8 : Nat.card ↥D8 = 8) :
    ∀ d ∈ D8, (C.ψ d : G) ∈ ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
      Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ := by
  classical
  let s : G := (C.ψ sM : G)
  let CS : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let L : Subgroup G := ⁅CS, CS⁆
  let š : ↥CS := ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let N : Subgroup ↥CS := Subgroup.zpowers š
  have hsord : orderOf s = 7 := by
    rw [show s = ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) from rfl,
      Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hsM]
  have hšord : orderOf š = 7 := by
    rw [← Subgroup.orderOf_coe š]
    exact hsord
  have hcardN : Nat.card ↥N = 7 := by
    rw [Nat.card_zpowers, hšord]
  have hcenter : š ∈ Subgroup.center ↥CS := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_singleton_iff.mp y.2
  haveI : N.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcenter)
  have hA := commutator_centralizer_s_facts C sM hsM hM7
  have hdisj : L ⊓ Subgroup.zpowers s = ⊥ := hA.1
  have hsupL : L ⊔ Subgroup.zpowers s = CS := hA.2.1
  have hLdef : Subgroup.map CS.subtype (commutator ↥CS) = L :=
    Subgroup.map_subtype_commutator CS
  have hzp : Subgroup.map CS.subtype N = Subgroup.zpowers s := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hsupCS : commutator ↥CS ⊔ N = ⊤ := by
    apply Subgroup.map_injective CS.subtype_injective
    rw [Subgroup.map_sup, hLdef, hzp, hsupL, Subgroup.map_top, Subgroup.range_subtype]
  intro d hd
  have hcomm : d * sM = sM * d :=
    (Subgroup.mem_centralizer_iff.mp (hD8s hd) sM (Set.mem_singleton sM)).symm
  have hxmem : (C.ψ d : G) ∈ CS := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : C.ψ d * C.ψ sM = C.ψ sM * C.ψ d := by
      rw [← map_mul, ← map_mul, hcomm]
    have hc' : ((C.ψ d : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) *
        ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) =
        ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) *
        ((C.ψ d : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) :=
      congrArg (fun y : ↥(Subgroup.centralizer ({C.z} : Set G)) => (y : G)) hc
    simpa [s] using hc'
  have hx8 : (C.ψ d : G) ^ 8 = 1 := by
    have hdvd : orderOf d ∣ 8 := by
      have h := Subgroup.orderOf_dvd_natCard D8 hd
      rwa [hD8] at h
    have hord : orderOf (C.ψ d : G) = orderOf d := by
      rw [show (C.ψ d : G) = ((C.ψ d : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) from rfl,
        Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact hdvd
  let xš : ↥CS := ⟨(C.ψ d : G), hxmem⟩
  have hxš_sup : xš ∈ commutator ↥CS ⊔ N := by
    rw [hsupCS]
    exact Subgroup.mem_top xš
  obtain ⟨l, hl, n, hn, hln⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := commutator ↥CS) (t := N)).mp hxš_sup
  have hval : (l : G) * (n : G) = (C.ψ d : G) := by
    have h := congrArg (fun y : ↥CS => (y : G)) hln
    simpa [xš] using h
  have hlL : (l : G) ∈ L := by
    rw [← hLdef]
    exact Subgroup.mem_map_of_mem CS.subtype hl
  have hnS : (n : G) ∈ Subgroup.zpowers s := by
    rw [← hzp]
    exact Subgroup.mem_map_of_mem CS.subtype hn
  have hlncomm : Commute (l : G) (n : G) := by
    have hncent : n ∈ Subgroup.center ↥CS := (Subgroup.zpowers_le.mpr hcenter) hn
    exact congrArg (fun y : ↥CS => (y : G)) (Subgroup.mem_center_iff.mp hncent l)
  have h8eq : ((l : G) * (n : G)) ^ 8 = 1 := by
    rw [hval]
    exact hx8
  have hl8 : (l : G) ^ 8 = 1 := by
    have hz : (l : G) ^ 8 ∈ L ⊓ Subgroup.zpowers s := by
      constructor
      · exact L.pow_mem hlL 8
      · have hpow : (l : G) ^ 8 = ((n : G) ^ 8)⁻¹ := by
          rw [hlncomm.mul_pow] at h8eq
          exact eq_inv_of_mul_eq_one_left h8eq
        rw [hpow]
        exact (Subgroup.zpowers s).inv_mem ((Subgroup.zpowers s).pow_mem hnS 8)
    rw [hdisj, Subgroup.mem_bot] at hz
    exact hz
  have hn8 : (n : G) ^ 8 = 1 := by
    rw [hlncomm.mul_pow, hl8, one_mul] at h8eq
    exact h8eq
  have hn1 : (n : G) = 1 := by
    have h7 : orderOf (n : G) ∣ 7 := by
      have h := Subgroup.orderOf_dvd_natCard N hn
      rw [hcardN] at h
      rwa [Subgroup.orderOf_coe n]
    have h8 : orderOf (n : G) ∣ 8 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hn8
    have hd := Nat.dvd_gcd h7 h8
    rw [show Nat.gcd 7 8 = 1 by norm_num] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [← hval, hn1, mul_one]
  exact hlL

theorem t_centralizes_L (C : ThCore G)
    (sM tM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7) (htM : orderOf tM = 3)
    (hts : tM⁻¹ * sM * tM ∈ Subgroup.zpowers sM)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4))
    (D8 : Subgroup ↥CFSG.Sporadic.Th.Max3.M) (hD8s : D8 ≤ Subgroup.centralizer {sM})
    (hD8 : Nat.card ↥D8 = 8) (hD8t : ∀ d ∈ D8, Commute tM d) :
    ∀ x ∈ ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
      Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆, Commute (C.ψ tM : G) x := by
  classical
  let s : G := (C.ψ sM : G)
  let t : G := (C.ψ tM : G)
  let CS : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let L : Subgroup G := ⁅CS, CS⁆
  have hsord : orderOf s = 7 := by
    rw [show s = ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) from rfl,
      Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hsM]
  have htord : orderOf t = 3 := by
    rw [show t = ((C.ψ tM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) from rfl,
      Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hA := commutator_centralizer_s_facts C sM hsM hM7
  have hA1 : L ⊓ Subgroup.zpowers s = ⊥ := hA.1
  have hA2 : L ⊔ Subgroup.zpowers s = CS := hA.2.1
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 7 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 3 2 := hA.2.2
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hts
  have hts' : s ^ a = t⁻¹ * s * t := by
    have h := congrArg (fun y => ((C.ψ y : ↥(Subgroup.centralizer ({C.z} : Set G))) : G)) ha
    simpa [s, t, map_mul, map_inv, map_zpow] using h
  have hs'a : orderOf (s ^ a) = 7 := by
    have hsem : SemiconjBy t⁻¹ s (s ^ a) := by
      show t⁻¹ * s = s ^ a * t⁻¹
      calc t⁻¹ * s = (t⁻¹ * s * t) * t⁻¹ := by group
        _ = s ^ a * t⁻¹ := by rw [hts']
    exact (SemiconjBy.orderOf_eq t⁻¹ hsem).symm.trans hsord
  have hzeq : Subgroup.zpowers (s ^ a) = Subgroup.zpowers s := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers s).zpow_mem (Subgroup.mem_zpowers s) a)
    · rw [Nat.card_zpowers, Nat.card_zpowers, hs'a, hsord]
  have hcent_eq : Subgroup.centralizer ({s ^ a} : Set G) = CS := by
    rw [← Subgroup.centralizer_closure ({s ^ a} : Set G),
      ← Subgroup.zpowers_eq_closure (s ^ a), hzeq, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  let c : G →* G := (MulAut.conj t⁻¹).toMonoidHom
  have hc_inj : Function.Injective c := (MulAut.conj t⁻¹).injective
  have hCSmap_le : Subgroup.map c CS ≤ CS := by
    have h := Subgroup.map_centralizer_le_centralizer_image ({s} : Set G) c
    rw [Set.image_singleton] at h
    have hcs : c s = s ^ a := by
      rw [show c s = t⁻¹ * s * (t⁻¹)⁻¹ from rfl, inv_inv]
      exact hts'.symm
    rw [hcs, hcent_eq] at h
    exact h
  have hCSmap : Subgroup.map c CS = CS := by
    refine Subgroup.eq_of_le_of_card_ge hCSmap_le ?_
    rw [Subgroup.card_map_of_injective hc_inj]
  have hLmap : Subgroup.map c L = L := by
    show Subgroup.map c ⁅CS, CS⁆ = ⁅CS, CS⁆
    rw [Subgroup.map_commutator, hCSmap]
  let cL : ↥L →* ↥L :=
    { toFun := fun y => ⟨c (y : G), by
        have hy : c (y : G) ∈ Subgroup.map c L := Subgroup.mem_map_of_mem c y.2
        rwa [hLmap] at hy⟩
      map_one' := by ext; exact map_one c
      map_mul' := fun x y => by ext; exact map_mul c (x : G) (y : G) }
  have hcL_inj : Function.Injective cL := by
    intro x y hxy
    apply Subtype.ext
    exact (MulAut.conj t⁻¹).injective (Subtype.ext_iff.mp hxy)
  have hcL_surj : Function.Surjective cL := by
    intro y
    have hy : (y : G) ∈ Subgroup.map c L := by
      rw [hLmap]
      exact y.2
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let α : ↥L ≃* ↥L := MulEquiv.ofBijective cL ⟨hcL_inj, hcL_surj⟩
  have hα_apply : ∀ y : ↥L, ((α y : ↥L) : G) = t⁻¹ * (y : G) * t := by
    intro y
    change c (y : G) = t⁻¹ * (y : G) * t
    rw [show c (y : G) = t⁻¹ * (y : G) * (t⁻¹)⁻¹ from rfl, inv_inv]
  have ht3 : t ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, htord]
  have hα3 : α ^ 3 = 1 := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change ((α (α (α y)) : ↥L) : G) = (y : G)
    rw [hα_apply, hα_apply, hα_apply]
    have hinv3 : t⁻¹ * t⁻¹ * t⁻¹ = 1 := by
      calc t⁻¹ * t⁻¹ * t⁻¹ = (t⁻¹) ^ 3 := by rw [pow_three]; group
        _ = (t ^ 3)⁻¹ := by rw [inv_pow]
        _ = 1 := by rw [ht3, inv_one]
    have hL : t⁻¹ * (t⁻¹ * (t⁻¹ * (y : G) * t) * t) * t
        = (t⁻¹ * t⁻¹ * t⁻¹) * (y : G) * (t * t * t) := by group
    have ht3' : t * t * t = 1 := by
      calc t * t * t = t ^ 3 := by rw [pow_three]; group
        _ = 1 := ht3
    rw [hL, hinv3, ht3']
    group
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) ∣ 4 := by
    rcases hmodel with h | h
    · obtain ⟨-, F, hField, hFinite, hF, ⟨e⟩⟩ := h
      letI : Field F := hField
      letI : Finite F := hFinite
      have e' : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
        e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
      have hdiv := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
        (f := 1) Nat.prime_seven F (by rw [pow_one]; exact hF)).2 ↥L ⟨e'⟩
      rw [show (1 : ℕ) * Nat.gcd 2 (7 ^ 1 - 1) = 2 by norm_num] at hdiv
      exact hdiv.trans (by norm_num : 2 ∣ 4)
    · obtain ⟨-, F, hField, hFinite, hF, ⟨e⟩⟩ := h
      letI : Field F := hField
      letI : Finite F := hFinite
      have e' : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
        e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
      have hdiv := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
        Nat.prime_three F hF).2 ↥L ⟨e'⟩
      rw [show (2 : ℕ) * Nat.gcd 2 (3 ^ 2 - 1) = 4 by norm_num] at hdiv
      exact hdiv
  let αbar : CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L :=
    QuotientGroup.mk (s := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L) α
  have hbar3 : orderOf αbar ∣ 3 := by
    have h := orderOf_map_dvd
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)) α
    exact h.trans (orderOf_dvd_of_pow_eq_one hα3)
  have hbar4 : orderOf αbar ∣ 4 := (orderOf_dvd_natCard αbar).trans hOut
  have hbar1 : αbar = 1 := by
    have hd := Nat.dvd_gcd hbar3 hbar4
    rw [show Nat.gcd 3 4 = 1 by norm_num] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff (N :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L) α).mp hbar1
  have hLsimple : IsSimpleGroup ↥L := by
    rcases hmodel with h | h
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two h
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two h
  haveI : IsSimpleGroup ↥L := hLsimple
  have hLnoncomm : ¬ IsMulCommutative ↥L := by
    intro hcomm
    haveI : IsMulCommutative ↥L := hcomm
    have hprime : Nat.Prime (Nat.card ↥L) :=
      (Group.is_simple_iff_prime_card (α := ↥L)).mp hLsimple
    rcases hmodel with h | h
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h] at hprime
      norm_num at hprime
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine h] at hprime
      norm_num at hprime
  have hcenterbot : Subgroup.center ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      apply hLnoncomm
      refine IsMulCommutative.of_comm fun x y => ?_
      have hx : x ∈ Subgroup.center ↥L := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have hg3 : g ^ 3 = 1 := by
    have hcenter3 : g ^ 3 ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hconj : MulAut.conj (g ^ 3) = 1 := by
        rw [MulAut.conj.map_pow, hg, hα3]
      have h := congrArg (fun e : MulAut ↥L => e y) hconj
      simp only [MulAut.conj_apply, OneHom.one_apply] at h
      have h' : g ^ 3 * y * (g ^ 3)⁻¹ = y := by simpa using h
      calc y * g ^ 3 = (g ^ 3 * y * (g ^ 3)⁻¹) * g ^ 3 := by rw [h']
        _ = g ^ 3 * y := by group
    rw [hcenterbot, Subgroup.mem_bot] at hcenter3
    exact hcenter3
  obtain ⟨d₀s, hd₀s⟩ : ∃ x : ↥D8, orderOf x = 2 := by
    have h2 : 2 ∣ Nat.card ↥D8 := by rw [hD8]; norm_num
    exact exists_prime_orderOf_dvd_card' 2 h2
  let d₀ : ↥CFSG.Sporadic.Th.Max3.M := d₀s
  have hd₀mem : d₀ ∈ D8 := d₀s.2
  have hd₀ord : orderOf d₀ = 2 := by
    rw [Subgroup.orderOf_coe d₀s]
    exact hd₀s
  let w : G := (C.ψ d₀ : G)
  have hword : orderOf w = 2 := by
    rw [show w = ((C.ψ d₀ : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) from rfl,
      Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hd₀ord]
  have hws : w * s = s * w := by
    have hcomm : d₀ * sM = sM * d₀ :=
      (Subgroup.mem_centralizer_iff.mp (hD8s hd₀mem) sM (Set.mem_singleton sM)).symm
    have hc : C.ψ d₀ * C.ψ sM = C.ψ sM * C.ψ d₀ := by
      rw [← map_mul, ← map_mul, hcomm]
    have hc' : ((C.ψ d₀ : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) *
        ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) =
        ((C.ψ sM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) *
        ((C.ψ d₀ : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) :=
      congrArg (fun y : ↥(Subgroup.centralizer ({C.z} : Set G)) => (y : G)) hc
    show w * s = s * w
    simpa [s, w] using hc'
  have htw : t * w = w * t := by
    have hc : C.ψ tM * C.ψ d₀ = C.ψ d₀ * C.ψ tM := by
      have h := (hD8t d₀ hd₀mem).eq
      rw [← map_mul, ← map_mul, h]
    have hc' : ((C.ψ tM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) *
        ((C.ψ d₀ : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) =
        ((C.ψ d₀ : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) *
        ((C.ψ tM : ↥(Subgroup.centralizer ({C.z} : Set G))) : G) :=
      congrArg (fun y : ↥(Subgroup.centralizer ({C.z} : Set G)) => (y : G)) hc
    show t * w = w * t
    simpa [t, w] using hc'
  obtain ⟨D, hDinf, hDsup, hDiso⟩ :=
    centralizer_inf_split_of_involution C sM hsM hM7 hws hword
  have hwL : w ∈ L := psi_D8_le_L C sM hsM hM7 D8 hD8s hD8 d₀ hd₀mem
  have hαw : α ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
    apply Subtype.ext
    rw [hα_apply]
    calc t⁻¹ * w * t = t⁻¹ * (w * t) := by group
      _ = t⁻¹ * (t * w) := by rw [← htw]
      _ = w := by group
  have hgw : Commute (g : G) w := by
    have hconj : (MulAut.conj g) ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
      rw [hg]
      exact hαw
    have hval : (g : G) * w * (g : G)⁻¹ = w := by
      have h := congrArg (fun y : ↥L => (y : G)) hconj
      simpa [MulAut.conj_apply] using h
    show (g : G) * w = w * (g : G)
    calc (g : G) * w = ((g : G) * w * (g : G)⁻¹) * (g : G) := by group
      _ = w * (g : G) := by rw [hval]
  have hscenterG : ∀ y : ↥CS, (y : G) * s = s * (y : G) := by
    intro y
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  let E : Subgroup G := CS ⊓ Subgroup.centralizer ({w} : Set G)
  have hgE : (g : G) ∈ E := by
    refine ⟨Subgroup.commutator_le_self CS g.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hgw.eq
  have hDsup' : D ⊔ Subgroup.zpowers s = E := hDsup
  have hD_le_E : D ≤ E := by
    rw [← hDsup']
    exact le_sup_left
  have hS_le_E : Subgroup.zpowers s ≤ E := by
    rw [← hDsup']
    exact le_sup_right
  let DE : Subgroup ↥E := D.subgroupOf E
  let NE : Subgroup ↥E := (Subgroup.zpowers s).subgroupOf E
  have hDE_sup : DE ⊔ NE = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hD_le_E, inf_eq_left.mpr hS_le_E, hDsup', Subgroup.map_top,
      Subgroup.range_subtype]
  have hNE_normal : NE.Normal := by
    apply Subgroup.normal_of_le_center
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxs : (x : G) ∈ Subgroup.zpowers s := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxs
    have hcomm : Commute (y : G) s := hscenterG ⟨(y : G), y.2.1⟩
    show (y : G) * (x : G) = (x : G) * (y : G)
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  haveI : NE.Normal := hNE_normal
  let gE : ↥E := ⟨(g : G), hgE⟩
  have hgE_sup : gE ∈ NE ⊔ DE := by
    rw [show NE ⊔ DE = ⊤ by rw [sup_comm, hDE_sup]]
    exact Subgroup.mem_top gE
  obtain ⟨n, hn, d, hd, hnd⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := NE) (t := DE)).mp hgE_sup
  have hval : (n : G) * (d : G) = (g : G) := by
    have h := congrArg (fun y : ↥E => (y : G)) hnd
    simpa [gE] using h
  have hnS : (n : G) ∈ Subgroup.zpowers s := Subgroup.mem_subgroupOf.mp hn
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
  have hg3G : (g : G) ^ 3 = 1 := by
    have h := congrArg (fun y : ↥L => (y : G)) hg3
    simpa using h
  have hg3' : ((n : G) * (d : G)) ^ 3 = 1 := by
    rw [hval]
    exact hg3G
  have hnd_comm : Commute (n : G) (d : G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnS
    have hcomm : Commute (d : G) s := hscenterG ⟨(d : G), d.2.1⟩
    rw [← hk]
    exact (hcomm.zpow_right k).symm
  have hd3 : (d : G) ^ 3 = 1 := by
    rw [hnd_comm.mul_pow] at hg3'
    have hd3D : (d : G) ^ 3 ∈ D := D.pow_mem hdD 3
    have hd3S : (d : G) ^ 3 ∈ Subgroup.zpowers s := by
      have hEq : (d : G) ^ 3 = ((n : G) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hg3'
      rw [hEq]
      exact (Subgroup.zpowers s).inv_mem ((Subgroup.zpowers s).pow_mem hnS 3)
    have hbot : (d : G) ^ 3 ∈ D ⊓ Subgroup.zpowers s := ⟨hd3D, hd3S⟩
    rw [hDinf, Subgroup.mem_bot] at hbot
    exact hbot
  have hd_card : Nat.card ↥D = 8 := by
    obtain ⟨e⟩ := hDiso
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hd1 : (d : G) = 1 := by
    have h8 : orderOf (d : G) ∣ 8 := by
      have h := Subgroup.orderOf_dvd_natCard D hdD
      rwa [hd_card] at h
    have h3 : orderOf (d : G) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hd3
    have hdvd := Nat.dvd_gcd h8 h3
    rw [show Nat.gcd 8 3 = 1 by norm_num] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have hg_eq_n : (g : G) = (n : G) := by
    rw [← hval, hd1, mul_one]
  have hgS : (g : G) ∈ Subgroup.zpowers s := by
    rw [hg_eq_n]
    exact hnS
  have hg1G : (g : G) = 1 := by
    have hmem : (g : G) ∈ L ⊓ Subgroup.zpowers s := ⟨g.2, hgS⟩
    rw [hA1, Subgroup.mem_bot] at hmem
    exact hmem
  have hg1 : g = 1 := Subtype.ext hg1G
  have hα1 : α = 1 := by
    rw [← hg, hg1]
    exact map_one (MulAut.conj : ↥L →* MulAut ↥L)
  intro x hx
  have hαx : α ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hα1]
    rfl
  have hvalx : t⁻¹ * x * t = x := by
    have h := congrArg (fun y : ↥L => (y : G)) hαx
    rw [hα_apply] at h
    exact h
  have hx' : x = t * x * t⁻¹ := by
    calc x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      _ = t * x * t⁻¹ := by rw [hvalx]
  show t * x = x * t
  calc t * x = (t * x * t⁻¹) * t := by group
    _ = x * t := by rw [← hx']

theorem commutator_centralizer_s_psl_two_seven (C : ThCore G)
    (sM tM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7) (htM : orderOf tM = 3)
    (hts : tM⁻¹ * sM * tM ∈ Subgroup.zpowers sM)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4))
    (D8 : Subgroup ↥CFSG.Sporadic.Th.Max3.M) (hD8s : D8 ≤ Subgroup.centralizer {sM})
    (hD8 : Nat.card ↥D8 = 8) (hD8t : ∀ d ∈ D8, Commute tM d)
    (hK : Nat.card ↥⁅Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
      Subgroup.centralizer ({(C.ψ tM : G)} : Set G)⁆ = 7371 * 576) :
    ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G), Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆
        ⊓ Subgroup.zpowers (C.ψ sM : G) = ⊥ ∧
      ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
          Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ ⊔ Subgroup.zpowers (C.ψ sM : G) =
        Subgroup.centralizer ({(C.ψ sM : G)} : Set G) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        ↥⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
          Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ .PSL 2 7 1 := by
  classical
  let s : G := (C.ψ sM : G)
  let t : G := (C.ψ tM : G)
  let CS : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let CT : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let L : Subgroup G := ⁅CS, CS⁆
  have hA := commutator_centralizer_s_facts C sM hsM hM7
  have hA1 : L ⊓ Subgroup.zpowers s = ⊥ := hA.1
  have hA2 : L ⊔ Subgroup.zpowers s = CS := hA.2.1
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 7 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 2 3 2 := hA.2.2
  have htL : ∀ x ∈ L, Commute t x :=
    t_centralizes_L C sM tM hsM htM hts hM7 D8 hD8s hD8 hD8t
  have hLCT : L ≤ CT := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (htL x hx).eq.symm
  have hLsimple : IsSimpleGroup ↥L := by
    rcases hmodel with h | h
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two h
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two h
  haveI : IsSimpleGroup ↥L := hLsimple
  have hLnoncomm : ¬ IsMulCommutative ↥L := by
    intro hcomm
    haveI : IsMulCommutative ↥L := hcomm
    have hprime : Nat.Prime (Nat.card ↥L) :=
      (Group.is_simple_iff_prime_card (α := ↥L)).mp hLsimple
    rcases hmodel with h | h
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h] at hprime
      norm_num at hprime
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine h] at hprime
      norm_num at hprime
  have hLperfect : commutator ↥L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
    · exfalso
      exact hLnoncomm ((commutator_eq_bot_iff ↥L).mp h)
    · exact h
  have hLL : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L, hLperfect, Subgroup.map_top,
      Subgroup.range_subtype]
  have hL_le_K : L ≤ ⁅CT, CT⁆ := by
    rw [← hLL]
    exact Subgroup.commutator_mono hLCT hLCT
  have hK' : Nat.card ↥⁅CT, CT⁆ = 7371 * 576 := hK
  have hcardL_dvd : Nat.card ↥L ∣ 7371 * 576 := by
    have h := Subgroup.card_dvd_of_le hL_le_K
    rwa [hK'] at h
  rcases hmodel with h7 | h9
  · exact ⟨hA1, hA2, h7⟩
  · exfalso
    have h360 : Nat.card ↥L = 360 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine h9
    rw [h360] at hcardL_dvd
    norm_num at hcardL_dvd

theorem centralizer_s_split (C : ThCore G)
    (sM tM : ↥CFSG.Sporadic.Th.Max3.M) (hsM : orderOf sM = 7) (htM : orderOf tM = 3)
    (hts : tM⁻¹ * sM * tM ∈ Subgroup.zpowers sM)
    (hM7 : ∀ x : ↥CFSG.Sporadic.Th.Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥CFSG.Sporadic.Th.Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4))
    (D8 : Subgroup ↥CFSG.Sporadic.Th.Max3.M) (hD8s : D8 ≤ Subgroup.centralizer {sM})
    (hD8 : Nat.card ↥D8 = 8) (hD8t : ∀ d ∈ D8, Commute tM d)
    (hK : Nat.card ↥⁅Subgroup.centralizer ({(C.ψ tM : G)} : Set G),
      Subgroup.centralizer ({(C.ψ tM : G)} : Set G)⁆ = 7371 * 576) :
    ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({(C.ψ sM : G)} : Set G) ∧
      L ⊓ Subgroup.zpowers (C.ψ sM : G) = ⊥ ∧
      L ⊔ Subgroup.zpowers (C.ψ sM : G) = Subgroup.centralizer ({(C.ψ sM : G)} : Set G) ∧
      L = ⁅Subgroup.centralizer ({(C.ψ sM : G)} : Set G),
        Subgroup.centralizer ({(C.ψ sM : G)} : Set G)⁆ ∧
      Nonempty (↥L ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  let s : G := (C.ψ sM : G)
  let CS : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let L : Subgroup G := ⁅CS, CS⁆
  have h7 := commutator_centralizer_s_psl_two_seven C sM tM hsM htM hts hM7 D8 hD8s hD8 hD8t hK
  refine ⟨L, Subgroup.commutator_le_self CS, h7.1, h7.2.1, rfl, ?_⟩
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven h7.2.2
  exact ⟨e.trans (MulEquiv.ofBijective _
    CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)⟩
