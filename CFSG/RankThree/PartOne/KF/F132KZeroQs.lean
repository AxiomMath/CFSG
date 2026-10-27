module

public import CFSG.RankThree.PartOne.KF.F132Gen
public import CFSG.RankThree.PartOne.KFOUT3.KtyGen
public import CFSG.RankThree.PartOne.KF.U4Ambient
public import CFSG.RankThree.PartOne.S12.Sec132
import CFSG.RankThree.PartOne.S12.PerfectOddPrime
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.RankThree.PartOne.N1322.Statements
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.KFOUT3
open CFSG.RankThree.PartOne.Torsion37 CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem kZero_le_of_block_qs (h : Sec12Hyp G p A c L E) (t : MulAut E)
    (hct : c ∈ autFixedInG E t) {B : Subgroup G} {z : G} (hBL : B ≤ L)
    (hBX : B ≤ Subgroup.centralizer (autFixedInG E t : Set G))
    (hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hBqs : IsQuasisimple B) (hzB : z ∈ B)
    (hE : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i) :
    kZero p E t ≤ B := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Subgroup.centralizer (autFixedInG E t : Set G) with hXdef
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hx y hct
  have hYsn := subnormal_inf_subgroupOf h hXc
  set B' : Subgroup X := B.subgroupOf X with hB'
  have hB'qs : IsQuasisimple B' :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBX).symm hBqs
  have hB'sn : B'.IsSubnormal := by
    refine Subgroup.IsSubnormal.step B' ((L ⊓ X).subgroupOf X)
      (fun b hb => ?_) hYsn ?_
    · rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact Subgroup.mem_inf.mpr ⟨hBL hb, hBX hb⟩
    · refine ⟨fun n hn g => ?_⟩
      have hn' : (((n : (L ⊓ X).subgroupOf X) : X) : G) ∈ B := hn
      have hg : ((((g : (L ⊓ X).subgroupOf X) : X) : G)) ∈ L ⊓ X := g.2
      show ((((g * n * g⁻¹ : (L ⊓ X).subgroupOf X) : X) : G)) ∈ B
      exact hBnorm _ hg _ hn'
  have hB'map : B'.map X.subtype = B := by
    rw [hB', Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hBX
  have hzX : z ∈ X := hBX hzB
  have hzB' : (⟨z, hzX⟩ : X) ∈ B' := hzB
  have hcomm : ∀ K : Subgroup X, IsComponent K → K ≠ B' → ⁅K, B'⁆ = ⊥ := by
    intro K hK hne
    rcases LocalCores.distinct_components_commute hK ⟨hB'qs, hB'sn⟩ with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hKE : ∀ K : Subgroup X, IsComponent K → K ≠ B' →
      K.map X.subtype ≤ Subgroup.centralizer (E : Set G) := by
    intro K hK hne k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨u, hu, i, rfl⟩ := hE e he
    have hcm : k' * ⟨z, hzX⟩ = ⟨z, hzX⟩ * k' := by
      have := Subgroup.commutator_mem_commutator hk' hzB'
      rw [hcomm K hK hne, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hz2 : (z : G) * (k' : G) = (k' : G) * z := congrArg Subtype.val hcm.symm
    have hu2 : u * (k' : G) = (k' : G) * u := (Subgroup.mem_centralizer_iff.mp k'.2 u hu)
    have hzi : (z : G) ^ i * (k' : G) = (k' : G) * z ^ i :=
      (Commute.zpow_left (show Commute z (k' : G) from hz2) i).eq
    show u * z ^ i * (k' : G) = (k' : G) * (u * z ^ i)
    rw [mul_assoc, hzi, ← mul_assoc, hu2, mul_assoc]
  set S : Set (Subgroup G) :=
    {M | ∃ K : Subgroup X, IsComponent K ∧ K ≠ B' ∧ K.map X.subtype = M} with hSdef
  set T : Subgroup G := sSup S with hTdef
  have hSE : ∀ M ∈ S, M ≤ Subgroup.centralizer (E : Set G) := by
    rintro M ⟨K, hK, hne, rfl⟩
    exact hKE K hK hne
  have hSB : ∀ M ∈ S, M ≤ Subgroup.centralizer (B : Set G) := by
    rintro M ⟨K, hK, hne, rfl⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← hB'map, ← Subgroup.map_commutator,
      hcomm K hK hne, Subgroup.map_bot]
  have hSp : ∀ M ∈ S, Group.IsPerfect M := by
    rintro M ⟨K, hK, -, rfl⟩
    exact isPerfect_map_subtype' hK.1.1
  have hTB : T ≤ Subgroup.centralizer (B : Set G) := sSup_le hSB
  have hTE : T ≤ Subgroup.centralizer (E : Set G) := sSup_le hSE
  have hTp : Group.IsPerfect T := isPerfect_sSup_of_forall_isPerfect' hSp
  have hT3 : ¬ p ∣ Nat.card T := by
    intro hdvd
    obtain ⟨e, he, hecenter⟩ := exists_pow_eq_one_not_mem_center_of_isPerfect hp2 hTp hdvd
    have heE : (e : G) ∈ E :=
      h.mem_of_pow_eq_one_of_commute (by simpa using congrArg Subtype.val he)
        (fun a ha => Subgroup.mem_centralizer_iff.mp (hTE e.2) a ha)
    apply hecenter
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hTE w.2) e heE).symm
  have hcop : ∀ v ∈ T, Nat.Coprime (orderOf v) p := by
    intro v hv
    have hdvd : orderOf v ∣ Nat.card T := by
      rw [← Subgroup.orderOf_mk v hv]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hT3).symm
  have hlayer : inSubgroup (fun K _ => layer K) X ≤ B ⊔ T := by
    show (layer ↥X).map X.subtype ≤ _
    rw [Subgroup.map_le_iff_le_comap, CFSG.layer]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    by_cases hKB : K = B'
    · rw [hKB, hB'map]
      exact le_sup_left
    · exact (le_sSup ⟨K, hK, hKB, rfl⟩ : K.map X.subtype ≤ T).trans le_sup_right
  have hBlayer : B ≤ inSubgroup (fun K _ => layer K) X := by
    show B ≤ (layer ↥X).map X.subtype
    rw [← hB'map]
    exact Subgroup.map_mono (le_sSup ⟨hB'qs, hB'sn⟩)
  have hK0le : kZero p E t ≤ B := by
    unfold kZero pElementSubgroup
    rw [Subgroup.closure_le]
    rintro x ⟨hxY, k, hk⟩
    have hxk : x ^ (p ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one x
    exact mem_of_pow_eq_one_of_mem_sup_centralizer' hTB hcop (hlayer hxY) hxk
  exact hK0le

theorem kZero_eq_of_layer_qs (h : Sec12Hyp G p A c L E) (hE3 : Nat.card E = p ^ 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcL : c ∉ L)
    {t : MulAut E} (htr : IsAutReflection p E t) (htL : t ∈ torusImage E L)
    (hsplit : E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
      Nat.card ↥(autMovedInG E t) = p)
    {b : G} (hbE : b ∈ E) (hbL : b ∈ L) (hb1 : b ≠ 1) (hbt : ((t ⟨b, hbE⟩ : E) : G) = b)
    (hAK : Nat.card ↥(E ⊓ kLayer L b) = p) (hKqs : IsQuasisimple ↥(kLayer L b))
    (hKz : ¬ p ∣ Nat.card (Subgroup.center ↥(kLayer L b))) :
    kZero p E t = kLayer L b ∧ autMovedInG E t ≤ kLayer L b ∧
      ∃ (z : G) (hzE : z ∈ E), z ∈ kLayer L b ∧ orderOf z = p ∧
        E ⊓ kLayer L b = Subgroup.zpowers z ∧ ((t ⟨z, hzE⟩ : E) : G) = z⁻¹ ∧
        E = autFixedInG E t ⊔ Subgroup.zpowers z := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp3 := h.three_lt
  have hEel := h.E_elem
  set K := kLayer L b with hK
  obtain ⟨hEsup, hCM, hM'card⟩ := hsplit
  have hKle : K ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := hKle.trans inf_le_right
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKL.trans hLc
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hfixiff : ∀ {e : G}, e ∈ autFixedInG E t ↔ ∃ he : e ∈ E, t ⟨e, he⟩ = ⟨e, he⟩ :=
    mem_autFixedInG_iff
  have hbC : b ∈ autFixedInG E t := hfixiff.mpr ⟨hbE, Subtype.ext hbt⟩
  have hcC : c ∈ autFixedInG E t := c_mem_autFixedInG h htL
  have hbp : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) b hbE
  have hcp : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) c hcE
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbc : b * c = c * b := hEcomm b hbE c hcE
  have hdiscbc : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro y hyb hyc
    by_contra hy1
    have hzx : Subgroup.zpowers y = Subgroup.zpowers c :=
      zpowers_eq_of_mem_of_ne_one hp hcord hyc hy1
    have hcx : c ∈ Subgroup.zpowers y := hzx ▸ Subgroup.mem_zpowers c
    have hyL : y ∈ L := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyb
      exact Subgroup.zpow_mem _ hbL k
    exact hcL (Subgroup.zpowers_le.2 hyL hcx)
  have hBCcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = p ^ 2 := by
    rw [card_sup_of_commute_disjoint (fun y hy y' hy' => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
        exact ((Commute.zpow_zpow (show Commute b c from hbc) i j)).eq) hdiscbc,
      Nat.card_zpowers, Nat.card_zpowers, hbord, hcord]
    ring
  have hBCleC : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ autFixedInG E t :=
    sup_le (Subgroup.zpowers_le.2 hbC) (Subgroup.zpowers_le.2 hcC)
  have hCleE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hM'leE : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hCcard : Nat.card ↥(autFixedInG E t) = p ^ 2 := by
    have h1 := card_sup_of_commute_disjoint (K := autFixedInG E t) (L := autMovedInG E t)
      (fun y hy y' hy' => hEcomm y (hCleE hy) y' (hM'leE hy')) (disjoint_iff.mpr hCM)
    have h2 : Nat.card ↥E = Nat.card ↥(autFixedInG E t ⊔ autMovedInG E t) := by rw [← hEsup]
    rw [h1, hM'card, hE3] at h2
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    rw [h3] at h2
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h2).symm
  have hCeq : Subgroup.zpowers b ⊔ Subgroup.zpowers c = autFixedInG E t :=
    Subgroup.eq_of_le_of_card_ge hBCleC (by rw [hBCcard, hCcard])
  have hCcentK : autFixedInG E t ≤ Subgroup.centralizer (K : Set G) := by
    rw [← hCeq]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKb hk)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKc hk)
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' p (G := ↥(E ⊓ K)) (by rw [hAK])
  set z : G := (z0 : G) with hzdef
  have hzE : z ∈ E := (Subgroup.mem_inf.mp z0.2).1
  have hzK : z ∈ K := (Subgroup.mem_inf.mp z0.2).2
  have hzord : orderOf z = p := by
    rw [hzdef, Subgroup.orderOf_coe]
    exact hz0
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzord
    exact hp.one_lt.ne hzord
  have hEKz : E ⊓ K = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hzE, hzK⟩))
      (by rw [Nat.card_zpowers, hzord, hAK])).symm
  have hnc : (⟨z, hzK⟩ : ↥K) ∉ Subgroup.center ↥K := by
    intro hzcen
    apply hKz
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hzcen
    rwa [Subgroup.orderOf_mk, hzord] at this
  have hzC : z ∉ autFixedInG E t := by
    intro hzC
    apply hnc
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hCcentK hzC) (k : G) k.2
  have hdisjCz : Disjoint (autFixedInG E t) (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro y hyC hyz
    by_contra hy1
    have hzx : Subgroup.zpowers y = Subgroup.zpowers z :=
      zpowers_eq_of_mem_of_ne_one hp hzord hyz hy1
    have hzy : z ∈ Subgroup.zpowers y := hzx ▸ Subgroup.mem_zpowers z
    exact hzC (Subgroup.zpowers_le.2 hyC hzy)
  have hzcomm : ∀ y ∈ autFixedInG E t, ∀ y' ∈ Subgroup.zpowers z, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    exact (Commute.zpow_right (show Commute y z from hEcomm y (hCleE hy) z hzE) i).eq
  have hEeq : E = autFixedInG E t ⊔ Subgroup.zpowers z := by
    have hle : autFixedInG E t ⊔ Subgroup.zpowers z ≤ E :=
      sup_le hCleE (Subgroup.zpowers_le.2 hzE)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_sup_of_commute_disjoint hzcomm hdisjCz, Nat.card_zpowers, hzord, hCcard, hE3]
    exact (by ring : p ^ 3 = p ^ 2 * p).le
  have hdec : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i := by
    intro e he
    rw [hEeq] at he
    obtain ⟨u, hu, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hzcomm he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨u, hu, i, rfl⟩
  have hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ k ∈ K,
      y * k * y⁻¹ ∈ K := by
    rintro y ⟨hyL, hyC⟩ k hk
    refine kLayer_conj_mem ⟨hyL, ?_⟩ hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hyC b hbC).symm
  have hBX : K ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hCcentK hu) k hk).symm
  refine ⟨le_antisymm (kZero_le_of_block_qs h t hcC hKL hBX hBnorm hKqs hzK hdec)
    (le_kZero_of_quasisimple h hcC hKL hBX hBnorm hKqs hzK hzord hnc), ?_⟩
  obtain ⟨x, hxmem, hxt⟩ := Subgroup.mem_map.mp htL
  have hlL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hxmem
  have hteq : ∀ e : E, ((t e : E) : G) = (x : G) * (e : G) * (x : G)⁻¹ := fun e => by
    rw [← hxt]
    rfl
  have hlb : (x : G) * b = b * (x : G) := by
    have h1 := hteq ⟨b, hbE⟩
    rw [hbt] at h1
    have h2 : b * (x : G) = (x : G) * b := by
      have : b = (x : G) * b * (x : G)⁻¹ := h1
      calc b * (x : G) = ((x : G) * b * (x : G)⁻¹) * (x : G) := by rw [← this]
        _ = (x : G) * b := by group
    exact h2.symm
  have hlcb : (x : G) ∈ L ⊓ Subgroup.centralizer ({b} : Set G) :=
    ⟨hlL, Subgroup.mem_centralizer_singleton_iff.mpr hlb⟩
  have htzmem : ((t ⟨z, hzE⟩ : E) : G) ∈ Subgroup.zpowers z := by
    rw [← hEKz]
    refine Subgroup.mem_inf.2 ⟨(t ⟨z, hzE⟩).2, ?_⟩
    rw [hteq]
    exact kLayer_conj_mem hlcb hzK
  set w : G := ((t ⟨z, hzE⟩ : E) : G) * z⁻¹ with hw
  have hwz : w ∈ Subgroup.zpowers z :=
    (Subgroup.zpowers z).mul_mem htzmem ((Subgroup.zpowers z).inv_mem (Subgroup.mem_zpowers z))
  have hw1 : w ≠ 1 := by
    intro h1
    apply hzC
    have h2 : ((t ⟨z, hzE⟩ : E) : G) = z := mul_inv_eq_one.mp h1
    exact hfixiff.mpr ⟨hzE, Subtype.ext h2⟩
  have hwM : w ∈ autMovedInG E t := by
    rw [Sec12Three.autMovedInG_eq_closure]
    exact Subgroup.subset_closure ⟨⟨z, hzE⟩, rfl⟩
  have hwp : w ^ p = 1 := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hwz
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzord,
      pow_orderOf_eq_one, one_zpow]
  have hword : orderOf w = p := orderOf_eq_prime hwp hw1
  have hzw : Subgroup.zpowers w = autMovedInG E t :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwM) (by
      rw [Nat.card_zpowers, hword, hM'card])
  refine ⟨?_, ?_⟩
  · rw [← hzw]
    exact (Subgroup.zpowers_le.2 hwz).trans (Subgroup.zpowers_le.2 hzK)
  have ht2 : ∀ e : E, t (t e) = e := by
    intro e
    have h1 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [htr.1, sq] at this
    exact DFunLike.congr_fun h1 e
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp htzmem
  have hts : t ⟨z, hzE⟩ = ⟨z, hzE⟩ ^ s := Subtype.ext (by rw [← hs]; rfl)
  have hss : (⟨z, hzE⟩ : E) ^ (s * s) = ⟨z, hzE⟩ := by
    have h1 := ht2 ⟨z, hzE⟩
    rw [hts, map_zpow, hts, ← zpow_mul] at h1
    exact h1
  have hss' : z ^ (s * s - 1) = 1 := by
    have h1 : z ^ (s * s) = z := congrArg Subtype.val hss
    rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
  have hdvd : (p : ℤ) ∣ (s - 1) * (s + 1) := by
    have := (orderOf_dvd_iff_zpow_eq_one).2 hss'
    rw [hzord] at this
    have e : s * s - 1 = (s - 1) * (s + 1) := by ring
    rwa [e] at this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htz : ((t ⟨z, hzE⟩ : E) : G) = z⁻¹ := by
    rcases hpz.dvd_or_dvd hdvd with h1 | h1
    · exfalso
      apply hzC
      have h2 : z ^ (s - 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).1 (by rw [hzord]; exact h1)
      have h3 : z ^ s = z := by
        rw [zpow_sub, zpow_one, mul_inv_eq_one] at h2
        exact h2
      refine hfixiff.mpr ⟨hzE, ?_⟩
      rw [hts]
      exact Subtype.ext h3
    · have h2 : z ^ (s + 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).1 (by rw [hzord]; exact h1)
      rw [← hs]
      rw [zpow_add, zpow_one, mul_eq_one_iff_eq_inv] at h2
      exact h2
  exact ⟨z, hzE, hzK, hzord, hEKz, htz, hEeq⟩

end CFSG.RankThree.PartOne.KF132
