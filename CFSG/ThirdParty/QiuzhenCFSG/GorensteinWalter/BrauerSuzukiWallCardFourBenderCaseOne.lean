module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourNormalizer

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallOrderThreeCentralizer
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender's first order-four counting case

This module formalizes Case 1 of Section 3 of Bender's *Finite groups with
large subgroups*.  The case hypothesis is
`C_G(X) ≠̸ N_G(V)`, i.e. non-containment, for the standard order-three
subgroup `X` in the normalizer of a self-centralizing Klein four `V`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The order-three subgroup in the order-24 Klein-four normalizer has a
normalizing involution.  It cannot centralize that subgroup, because every
involution centralizer has order eight. -/
private theorem exists_noncentralizing_involution_normalizing_order_three
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3) :
    ∃ u : G,
      u ∈ Subgroup.normalizer (V : Set G) ∧
      u ∈ Subgroup.normalizer (X : Set G) ∧
      IsInvolution u ∧
      u ∉ Subgroup.centralizer (X : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hVleN : V ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := V))
  let VN : Subgroup N := V.subgroupOf N
  let XN : Subgroup N := X.subgroupOf N
  have hVNcard : Nat.card VN = Nat.card V := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleN).toEquiv
  have hXNcard : Nat.card XN = 3 := by
    calc
      Nat.card XN = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv
      _ = 3 := hXcard
  have hVNnormal : VN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hVleN).mpr
    exact le_rfl
  have hXNindex : XN.index = 8 := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3)
    calc
      3 * XN.index = Nat.card XN * XN.index := by rw [hXNcard]
      _ = Nat.card N := XN.card_mul_index
      _ = 24 := by simpa [N] using hNcard
      _ = 3 * 8 := by norm_num
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hXNp : IsPGroup 3 XN := by
    apply IsPGroup.of_card (n := 1)
    simpa [hXNcard]
  have hthreeNotIndex : ¬ 3 ∣ XN.index := by
    rw [hXNindex]
    norm_num
  let P : Sylow 3 N := hXNp.toSylow hthreeNotIndex
  have hSylowDvd : Nat.card (Sylow 3 N) ∣ 8 := by
    simpa [P, hXNindex] using P.card_dvd_index
  have hSylowCard : Nat.card (Sylow 3 N) = 4 := by
    have hle : Nat.card (Sylow 3 N) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hSylowDvd
    have hmod : Nat.card (Sylow 3 N) % 3 = 1 := by
      simpa [Nat.ModEq] using (card_sylow_modEq_one 3 N :
        Nat.card (Sylow 3 N) ≡ 1 [MOD 3])
    have hpos : 0 < Nat.card (Sylow 3 N) := Nat.card_pos
    have hcases : Nat.card (Sylow 3 N) = 1 ∨
        Nat.card (Sylow 3 N) = 4 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two
          (m := 3) (i := Nat.card (Sylow 3 N))).mp (by
            simpa using hSylowDvd) with ⟨i, hi, hcard⟩
      interval_cases i <;> norm_num at hcard ⊢ <;> omega
    rcases hcases with hone | hfour
    · exfalso
      let : Subsingleton (Sylow 3 N) :=
        (Nat.card_eq_one_iff_unique.mp hone).1
      have hXNnormal : XN.Normal := by
        simpa [P] using Sylow.normal_of_subsingleton P
      have hVcard : Nat.card V = 4 := hV.card_four
      have hVNcardFour : Nat.card VN = 4 := by rw [hVNcard, hVcard]
      have hdisjoint : Disjoint VN XN := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [hVNcardFour, hXNcard]
        norm_num
      have hXleCentV : X ≤ Subgroup.centralizer (V : Set G) := by
        intro x hxX
        rw [Subgroup.mem_centralizer_iff]
        intro v hvV
        let xN : N := ⟨x, hXle hxX⟩
        let vN : N := ⟨v, hVleN hvV⟩
        have hxXN : xN ∈ XN := hxX
        have hvVN : vN ∈ VN := hvV
        have hcommN := Subgroup.commute_of_normal_of_disjoint
          VN XN hVNnormal hXNnormal hdisjoint vN xN hvVN hxXN
        exact congrArg Subtype.val hcommN.eq
      have hXleV : X ≤ V := by simpa [hCentV] using hXleCentV
      have hdvd : 3 ∣ Nat.card V := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le hXleV
      rw [hVcard] at hdvd
      norm_num at hdvd
    · exact hfour
  let R : Subgroup N := Subgroup.normalizer (XN : Set N)
  have hPcoe : (P : Subgroup N) = XN := rfl
  have hRindex : R.index = 4 := by
    calc
      R.index = Nat.card (Sylow 3 N) := by
        change (Subgroup.normalizer (XN : Set N)).index =
          Nat.card (Sylow 3 N)
        rw [← hPcoe]
        exact P.card_eq_index_normalizer.symm
      _ = 4 := hSylowCard
  have hRcard : Nat.card R = 6 := by
    have hmul := R.card_mul_index
    rw [hRindex] at hmul
    have hNcard' : Nat.card N = 24 := by simpa [N] using hNcard
    omega
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨uR, huROrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) 2 (by
      rw [hRcard]
      norm_num)
  let uN : N := (uR : N)
  let u : G := (uN : G)
  have huN : u ∈ N := uN.property
  have huNormXN : uN ∈ Subgroup.normalizer (XN : Set N) := uR.property
  have huNormX : u ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at huNormXN ⊢
    intro y
    constructor
    · intro hyX
      let yN : N := ⟨y, hXle hyX⟩
      have hyXN : yN ∈ XN := hyX
      have hconj := (huNormXN yN).mp hyXN
      exact hconj
    · intro hyX
      have hyN : y ∈ N := by
        have hconjN : u * y * u⁻¹ ∈ N := hXle hyX
        have hrecover : u⁻¹ * (u * y * u⁻¹) * u ∈ N :=
          N.mul_mem (N.mul_mem (N.inv_mem huN) hconjN) huN
        simpa [mul_assoc] using hrecover
      let yN : N := ⟨y, hyN⟩
      have hconj : uN * yN * uN⁻¹ ∈ XN := hyX
      exact (huNormXN yN).mpr hconj
  have huOrderN : orderOf uN = 2 := by
    simpa [uN] using (Subgroup.orderOf_coe uR).trans huROrder
  have huOrder : orderOf u = 2 := by
    simpa [u] using (Subgroup.orderOf_coe uN).trans huOrderN
  have huI : IsInvolution u := by
    constructor
    · intro huone
      rw [huone, orderOf_one] at huOrder
      omega
    · rw [← huOrder]
      exact pow_orderOf_eq_one u
  have hHcard : Nat.card h.H = 8 := by rw [h.card_H, hk]
  have huNotCentral : u ∉ Subgroup.centralizer (X : Set G) := by
    intro huCent
    have hXleCentU : X ≤ Subgroup.centralizer ({u} : Set G) := by
      intro x hxX
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp huCent x hxX
    have hdvd : Nat.card X ∣
        Nat.card (Subgroup.centralizer ({u} : Set G)) :=
      Subgroup.card_dvd_of_le hXleCentU
    rw [hXcard, centralizer_involution_card_eq_card_H h huI, hHcard] at hdvd
    norm_num at hdvd
  exact ⟨u, by simpa [N] using huN, huNormX, huI, huNotCentral⟩

/-- A noncentralizing involution normalizing a subgroup of order three
inverts a generator of that subgroup. -/
private theorem exists_order_three_generator_inverted_by_involution
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G)
    (hXcard : Nat.card X = 3)
    {u : G}
    (huNormX : u ∈ Subgroup.normalizer (X : Set G))
    (huI : IsInvolution u)
    (huNotCentral : u ∉ Subgroup.centralizer (X : Set G)) :
    ∃ x : G,
      x ∈ X ∧
      orderOf x = 3 ∧
      Subgroup.zpowers x = X ∧
      u * x * u⁻¹ = x⁻¹ := by
  classical
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨xX, hxXOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := X) 3 (by
      rw [hXcard])
  let x : G := (xX : G)
  have hxX : x ∈ X := xX.property
  have hxOrder : orderOf x = 3 := by
    simpa [x] using (Subgroup.orderOf_coe xX).trans hxXOrder
  have hxne : x ≠ 1 := by
    intro hxone
    rw [hxone, orderOf_one] at hxOrder
    omega
  have hzpowersLe : Subgroup.zpowers x ≤ X :=
    Subgroup.zpowers_le.mpr hxX
  have hzpowersCard : Nat.card (Subgroup.zpowers x) = 3 := by
    simpa [Nat.card_zpowers, hxOrder]
  have hzpowers : Subgroup.zpowers x = X :=
    Subgroup.eq_of_le_of_card_ge hzpowersLe (by
      rw [hXcard, hzpowersCard])
  let y : G := u * x * u⁻¹
  have hyX : y ∈ X := by
    exact (Subgroup.mem_normalizer_iff.mp huNormX x).mp hxX
  have huu : u * u = 1 := by
    simpa [pow_two] using huI.2
  have huInvSelf : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hyBack : u * y * u⁻¹ = x := by
    dsimp [y]
    rw [huInvSelf]
    calc
      u * (u * x * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [huu]; simp
  have hxyComm : x * y = y * x := by
    have hcomm :=
      (isCyclic_of_prime_card hXcard).isMulCommutative.is_comm.comm
        (⟨x, hxX⟩ : X) (⟨y, hyX⟩ : X)
    exact congrArg Subtype.val hcomm
  let m : G := x * y
  have hmX : m ∈ X := X.mul_mem hxX hyX
  have hmFixed : u * m * u⁻¹ = m := by
    calc
      u * m * u⁻¹ =
          (u * x * u⁻¹) * (u * y * u⁻¹) := by
            dsimp [m]
            group
      _ = y * x := by rw [hyBack]
      _ = x * y := hxyComm.symm
      _ = m := rfl
  have hmone : m = 1 := by
    by_contra hmne
    let mX : X := ⟨m, hmX⟩
    have hmXne : mX ≠ 1 := by
      intro hmXone
      exact hmne (congrArg Subtype.val hmXone)
    have hmGenerates : Subgroup.zpowers mX = ⊤ :=
      zpowers_eq_top_of_prime_card hXcard hmXne
    have hum : Commute u m := by
      change u * m = m * u
      have hmul := congrArg (fun z : G => z * u) hmFixed
      simpa [mul_assoc] using hmul
    have huCentX : u ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hzX
      let zX : X := ⟨z, hzX⟩
      have hzMem : zX ∈ Subgroup.zpowers mX := by
        rw [hmGenerates]
        exact Subgroup.mem_top zX
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzMem
      have hnG : m ^ n = z := congrArg Subtype.val hn
      have huz : Commute u z := by
        rw [← hnG]
        exact hum.zpow_right n
      exact huz.symm.eq
    exact huNotCentral huCentX
  refine ⟨x, hxX, hxOrder, hzpowers, ?_⟩
  change x * (u * x * u⁻¹) = 1 at hmone
  exact eq_inv_of_mul_eq_one_right hmone

/-- An element of order three cannot lie in a conjugate of the punctured
order-four subgroup `K`. -/
private theorem order_three_not_mem_bswKConjugates
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    {x : G} (hxOrder : orderOf x = 3) :
    x ∉ bswKConjugates h := by
  rintro ⟨a, haK, _hane, g, hconj⟩
  have horder : orderOf x = orderOf a := by
    rw [hconj]
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a
  have hdvd : orderOf a ∣ Nat.card h.K :=
    Subgroup.orderOf_dvd_natCard h.K haK
  rw [← horder, hxOrder, hk] at hdvd
  norm_num at hdvd

/-- After conjugating the normalizing involution to the distinguished `t`,
the Case-1 non-containment supplies a subgroup containing `⟨x⟩` but not the
selected centralizer `C_G(x)`. -/
private theorem exists_distinguished_inverted_order_three_case_one_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : ¬ Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G)) :
    ∃ x : G, ∃ L : Subgroup G,
      orderOf x = 3 ∧
      h.t * x * h.t⁻¹ = x⁻¹ ∧
      Subgroup.zpowers x ≤ L ∧
      ¬ Subgroup.centralizer ({x} : Set G) ≤ L := by
  classical
  obtain ⟨u, huNV, huNX, huI, huNotCentX⟩ :=
    exists_noncentralizing_involution_normalizing_order_three
      h hk V X hV hCentV hNcard hXle hXcard
  obtain ⟨x, hxX, hxOrder, _hzpowersX, hux⟩ :=
    exists_order_three_generator_inverted_by_involution
      X hXcard huNX huI huNotCentX
  obtain ⟨g, hgu⟩ := h.involutions_conjugate u huI
  obtain ⟨c, hcCentX, hcNotNV⟩ := SetLike.not_le_iff_exists.mp hcase
  let x' : G := g * x * g⁻¹
  let c' : G := g * c * g⁻¹
  let L : Subgroup G :=
    (Subgroup.normalizer (V : Set G)).conjBy g
  have hxOrder' : orderOf x' = 3 := by
    calc
      orderOf x' = orderOf x := by
        simpa [x', MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
      _ = 3 := hxOrder
  have htx' : h.t * x' * h.t⁻¹ = x'⁻¹ := by
    rw [← hgu]
    dsimp [x']
    calc
      (g * u * g⁻¹) * (g * x * g⁻¹) * (g * u * g⁻¹)⁻¹ =
          g * (u * x * u⁻¹) * g⁻¹ := by group
      _ = g * x⁻¹ * g⁻¹ := by rw [hux]
      _ = (g * x * g⁻¹)⁻¹ := by group
  have hx'L : x' ∈ L := by
    change g * x * g⁻¹ ∈
      (Subgroup.normalizer (V : Set G)).map
        (MulAut.conj g).toMonoidHom
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hXle hxX)
  have hcCommX : x * c = c * x :=
    Subgroup.mem_centralizer_iff.mp hcCentX x hxX
  have hc'Cent : c' ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    dsimp [x', c']
    calc
      (g * c * g⁻¹) * (g * x * g⁻¹) =
          g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [hcCommX]
      _ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
  have hc'NotL : c' ∉ L := by
    intro hc'L
    have hcPre : (MulAut.conj g).symm c' ∈
        Subgroup.normalizer (V : Set G) := by
      exact Subgroup.mem_map_equiv.mp hc'L
    apply hcNotNV
    simpa [c', MulAut.conj_apply, mul_assoc] using hcPre
  refine ⟨x', L, hxOrder', htx', Subgroup.zpowers_le.mpr hx'L, ?_⟩
  intro hCentLe
  exact hc'NotL (hCentLe hc'Cent)

/-- Numerical endpoint obtained from the selected-centralizer version of
Bender's fixed-coset count. -/
private theorem bender_case_one_selected_count_arithmetic
    (f n r e j mIndex involutions groupOrder : ℕ)
    (hf : 9 ≤ f)
    (hn : 2 ≤ n)
    (hnDvd : n ∣ 4)
    (hr : r * n = 8)
    (hMindex : mIndex = 1 + f * (r - 1) + e)
    (he : e = 0 ∨ f ≤ e)
    (hj : j ≤ e)
    (hInvolutions : involutions = f * 5 + j)
    (hglobal : mIndex * (f * n) = 8 * involutions)
    (horder : 8 * involutions = groupOrder) :
    f = 9 ∧ n = 4 ∧ r = 2 ∧ e = 0 ∧ j = 0 ∧
      involutions = 45 ∧ groupOrder = 360 := by
  have hnle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hnDvd
  have hnCases : n = 2 ∨ n = 4 := by
    interval_cases n
    · exact Or.inl rfl
    · norm_num at hnDvd
    · exact Or.inr rfl
  rcases hnCases with hnTwo | hnFour
  · subst n
    have hrFour : r = 4 := by omega
    subst r
    rw [hMindex, hInvolutions] at hglobal
    norm_num at hglobal
    rcases he with heZero | heLarge
    · subst e
      nlinarith
    · nlinarith
  · subst n
    have hrTwo : r = 2 := by omega
    subst r
    rw [hMindex, hInvolutions] at hglobal
    norm_num at hglobal
    have heZero : e = 0 := by
      rcases he with heZero | heLarge
      · exact heZero
      · nlinarith
    subst e
    have hjZero : j = 0 := by omega
    subst j
    have hfNine : f = 9 := by nlinarith
    subst f
    have hInv : involutions = 45 := by omega
    subst involutions
    omega

/-- The selected order-three centralizer and complement cardinal data forced
by Bender's first order-four case. -/
private theorem exists_order_nine_selected_centralizer_case_one_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (hcase :
      ∃ V X : Subgroup G,
        IsKleinFour V ∧
        Subgroup.centralizer (V : Set G) = V ∧
        Nat.card (Subgroup.normalizer (V : Set G)) = 24 ∧
        X ≤ Subgroup.normalizer (V : Set G) ∧
        Nat.card X = 3 ∧
        ¬ Subgroup.centralizer (X : Set G) ≤
          Subgroup.normalizer (V : Set G)) :
    ∃ x : G,
      orderOf x = 3 ∧
      h.t * x * h.t⁻¹ = x⁻¹ ∧
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 9 ∧
      Nat.card
        (h.K ⊓ Subgroup.normalizer
          (Subgroup.centralizer ({x} : Set G) : Set G) : Subgroup G) = 4 ∧
      h.H.index = 45 ∧
      Nat.card G = 360 := by
  classical
  obtain ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcase⟩ := hcase
  obtain ⟨x, L, hxOrder, htx, hzpowersL, hFnotL⟩ :=
    exists_distinguished_inverted_order_three_case_one_data
      h hk V X hV hCentV hNcard hXle hXcard hcase
  have hxne : x ≠ 1 := by
    intro hxone
    rw [hxone, orderOf_one] at hxOrder
    omega
  have hxOutside : x ∉ bswKConjugates h :=
    order_three_not_mem_bswKConjugates h hk hxOrder
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  obtain ⟨hFcomm, hFodd, hFCentInv, hFHall, hFTI⟩ :=
    h.inverted_order_three_centralizer_data hk hxOrder htx
  have hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F := by
    intro a haF hane
    exact (hFCentInv a haF hane).1
  have hFinv : ∀ a : G, a ∈ F →
      h.t * a * h.t⁻¹ = a⁻¹ := by
    intro a haF
    by_cases hane : a ≠ 1
    · exact (hFCentInv a haF hane).2
    · have haone : a = 1 := not_ne_iff.mp hane
      subst a
      simp
  have hxF : x ∈ F := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hzpowersF : Subgroup.zpowers x ≤ F :=
    Subgroup.zpowers_le.mpr hxF
  have hzpowersCard : Nat.card (Subgroup.zpowers x) = 3 := by
    simpa [Nat.card_zpowers, hxOrder]
  have hthreeDvdF : 3 ∣ Nat.card F := by
    rw [← hzpowersCard]
    exact Subgroup.card_dvd_of_le hzpowersF
  have hFneThree : Nat.card F ≠ 3 := by
    intro hFcard
    have hzpowersEq : Subgroup.zpowers x = F :=
      Subgroup.eq_of_le_of_card_ge hzpowersF (by
        rw [hFcard, hzpowersCard])
    apply hFnotL
    change F ≤ L
    rw [← hzpowersEq]
    exact hzpowersL
  have hFnine : 9 ≤ Nat.card F := by
    rcases hthreeDvdF with ⟨d, hd⟩
    have hFpos : 0 < Nat.card F := Nat.card_pos
    by_contra hnot
    have hFsmall : Nat.card F < 9 := Nat.lt_of_not_ge hnot
    have hdCases : d = 1 ∨ d = 2 := by omega
    rcases hdCases with hdOne | hdTwo
    · apply hFneThree
      omega
    · have hFsix : Nat.card F = 6 := by omega
      rw [hFsix] at hFodd
      norm_num at hFodd
  let e : ℕ := Nat.card
    (selected_centralizer_unoccupied_nonbase_cosets F)
  obtain ⟨r, j, hrPos, hrMul, hMindex, he, hj, hHindex⟩ :=
    selected_centralizer_bender_3_2_count_data
      h hxOutside hxne hFcomm hFodd hFinv hFHall hFTI
  let n : ℕ := Nat.card (h.K ⊓ M : Subgroup G)
  have hnTwo : 2 ≤ n := by
    simpa [n, M, F] using
      selected_centralizer_two_le_card_inf_K h hFinv
  have hnDvdFour : n ∣ 4 := by
    have hnDvdK : Nat.card (h.K ⊓ M : Subgroup G) ∣ Nat.card h.K :=
      Subgroup.card_dvd_of_le inf_le_left
    simpa [n, hk] using hnDvdK
  have hMcard : Nat.card M = Nat.card F * n := by
    simpa [M, F, n] using
      selected_centralizer_normalizer_card
        h hxOutside hxne hFodd hFinv
  have hHcard : Nat.card h.H = 8 := by
    rw [h.card_H, hk]
  have hglobal : M.index * (Nat.card F * n) = 8 * h.H.index := by
    calc
      M.index * (Nat.card F * n) = M.index * Nat.card M := by
        rw [hMcard]
      _ = Nat.card G := M.index_mul_card
      _ = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = 8 * h.H.index := by rw [hHcard]
  have horder : 8 * h.H.index = Nat.card G := by
    simpa [hHcard] using h.H.card_mul_index
  have hrMul' : r * n = 8 := by
    simpa [n, M, F, hk] using hrMul
  have hMindex' : M.index = 1 + Nat.card F * (r - 1) + e := by
    simpa [M, F, e] using hMindex
  have he' : e = 0 ∨ Nat.card F ≤ e := by
    simpa [e, F] using he
  have hHindex' : h.H.index = Nat.card F * 5 + j := by
    simpa [F, hk] using hHindex
  have hresult :=
    bender_case_one_selected_count_arithmetic
      (Nat.card F) n r e j M.index h.H.index (Nat.card G)
      hFnine hnTwo hnDvdFour hrMul' hMindex' he' hj hHindex'
      hglobal horder
  refine ⟨x, hxOrder, htx, ?_, ?_, hresult.2.2.2.2.2.1,
    hresult.2.2.2.2.2.2⟩
  · simpa [F] using hresult.1
  · simpa [n, M, F] using hresult.2.1

/-- Bender's first order-four case: if the order-three centralizer is not
contained in the self-centralizing Klein-four normalizer, then the ambient
group has order 360. -/
public theorem
    BrauerSuzukiWallHypotheses.card_eq_360_of_card_K_eq_four_of_bender_case_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (hcase :
      ∃ V X : Subgroup G,
        IsKleinFour V ∧
        Subgroup.centralizer (V : Set G) = V ∧
        Nat.card (Subgroup.normalizer (V : Set G)) = 24 ∧
        X ≤ Subgroup.normalizer (V : Set G) ∧
        Nat.card X = 3 ∧
        ¬ Subgroup.centralizer (X : Set G) ≤
          Subgroup.normalizer (V : Set G)) :
    Nat.card G = 360 := by
  obtain ⟨_x, _hxOrder, _htx, _hFcard, _hAcard, _hHindex, hGcard⟩ :=
    exists_order_nine_selected_centralizer_case_one_data h hk hcase
  exact hGcard

end CFSG.GorensteinWalter
