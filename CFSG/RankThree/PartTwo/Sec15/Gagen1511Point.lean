module

public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Point

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem deltaZero_le_centralizer {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (LB : Subgroup G → Subgroup G) {c' : G} (hc'A : c' ∈ A) {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) :
    deltaZero A LB X ≤ Subgroup.centralizer ({c'} : Set G) := by
  refine sSup_le fun Q hQ => ?_
  obtain ⟨hQ0, hQX⟩ := hQ
  have hQeq : Q = ⁅Q, A⁆ := hQ0.2
  rw [hQeq]
  refine Subgroup.commutator_le.mpr fun q hq a ha => ?_
  have hqN : q⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c' : Set G) :=
    Subgroup.inv_mem _ (hX (hQX hq))
  have hqc : q⁻¹ * c' * q ∈ Subgroup.zpowers c' := by
    simpa using (Subgroup.mem_normalizer_iff.mp hqN c').mp (Subgroup.mem_zpowers c')
  have hqcA : q⁻¹ * c' * q ∈ A := (Subgroup.zpowers_le.mpr hc'A) hqc
  have hac : a * c' = c' * a := hA a ha c' hc'A
  have ha' : a⁻¹ * c' = c' * a⁻¹ := (Commute.inv_left (show Commute a c' from hac)).eq
  have hat : a * (q⁻¹ * c' * q) * a⁻¹ = q⁻¹ * c' * q := by
    rw [hA a ha (q⁻¹ * c' * q) hqcA]; group
  have hx : (q * a * q⁻¹) * c' = c' * (q * a * q⁻¹) := by
    have h1 : (q * a * q⁻¹) * c' * (q * a * q⁻¹)⁻¹ = c' := by
      calc (q * a * q⁻¹) * c' * (q * a * q⁻¹)⁻¹
          = q * (a * (q⁻¹ * c' * q) * a⁻¹) * q⁻¹ := by group
        _ = q * (q⁻¹ * c' * q) * q⁻¹ := by rw [hat]
        _ = c' := by group
    calc (q * a * q⁻¹) * c'
        = ((q * a * q⁻¹) * c' * (q * a * q⁻¹)⁻¹) * (q * a * q⁻¹) := by group
      _ = c' * (q * a * q⁻¹) := by rw [h1]
  have hxmem : q * a * q⁻¹ ∈ Subgroup.centralizer ({c'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hx
  have hamem : a⁻¹ ∈ Subgroup.centralizer ({c'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ha'
  have hprod : (q * a * q⁻¹) * a⁻¹ ∈ Subgroup.centralizer ({c'} : Set G) :=
    Subgroup.mul_mem _ hxmem hamem
  have heq : ⁅q, a⁆ = (q * a * q⁻¹) * a⁻¹ := by rw [commutatorElement_def]
  rwa [heq]

theorem mul_inv_mem_pPrimeCoreOf_of_eq {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {LB : Subgroup G → Subgroup G} {c' : G} (hc'A : c' ∈ A) {Y : Subgroup G}
    (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hdec : Y = pPrimeCoreOf 3 Y ⊔
      deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)))
    {y : G} (hy : y ∈ Y) : c' * y * c'⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y := by
  set O := pPrimeCoreOf 3 Y with hO
  set D := deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) with hD
  have hDY : D ≤ Y := (deltaZero_le _).trans inf_le_left
  have hDc : D ≤ Subgroup.centralizer ({c'} : Set G) :=
    deltaZero_le_centralizer hA LB hc'A inf_le_right
  have hc'Y : c' ∈ Subgroup.normalizer (Y : Set G) := hYA hc'A
  have hc'O : c' ∈ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 Y hc'Y
  have hDN : D ≤ Subgroup.normalizer (O : Set G) :=
    hDY.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hy' : y ∈ ((O : Set G) * (D : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O D hDN, ← hdec]
    exact hy
  obtain ⟨o, ho, d, hd, hod⟩ := hy'
  have hz : c' * o * c'⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp hc'O o).mp ho
  have hcd : c' * d * c'⁻¹ = d := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hDc hd)
    calc c' * d * c'⁻¹ = d * c' * c'⁻¹ := by rw [h]
      _ = d := by group
  have hmain : c' * (o * d) * c'⁻¹ * (o * d)⁻¹ = (c' * o * c'⁻¹) * o⁻¹ := by
    calc c' * (o * d) * c'⁻¹ * (o * d)⁻¹
        = (c' * o * c'⁻¹) * (c' * d * c'⁻¹) * (o * d)⁻¹ := by group
      _ = (c' * o * c'⁻¹) * o⁻¹ := by rw [hcd]; group
  rw [← hod, hmain]
  exact O.mul_mem hz (O.inv_mem ho)

theorem not_isSolvable_inf_centralizer {X N : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    (hXres : X = oPrimeResidualOf 3 X)
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X))
    (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal) (hN3 : ¬ 3 ∣ Nat.card N)
    (hdX : ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hdN : ∀ n ∈ N, d * n * d⁻¹ ∈ N)
    (htriv : ∀ x ∈ X, x⁻¹ * (d * x * d⁻¹) ∈ N) :
    ¬ Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ({d} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({d} : Set G) with hC
  set Cx : Subgroup ↥X := C.subgroupOf X with hCx
  set Nx : Subgroup ↥X := N.subgroupOf X with hNx
  let π : ↥X →* (↥X ⧸ CFSG.pCore 2 ↥X) := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hCN : X ≤ C ⊔ N := by
    intro x hx
    obtain ⟨m, hmN, hm⟩ := KSL3Two.exists_mul_mem_centralizer hN3 hd3 hdN (htriv x hx)
    have hxmX : x * m ∈ X := X.mul_mem hx (hNX hmN)
    have hcomm : x * m * d = d * (x * m) := by
      calc x * m * d = (d * (x * m) * d⁻¹) * d := by rw [hm]
        _ = d * (x * m) := by group
    have hxmC : x * m ∈ C :=
      ⟨hxmX, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    have hxeq : x = (x * m) * m⁻¹ := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hxmC (N.inv_mem hmN)
  have hCNx : Cx ⊔ Nx = ⊤ := by
    refine le_antisymm le_top ?_
    rw [hCx, hNx, ← Subgroup.subgroupOf_sup (inf_le_left : C ≤ X) hNX]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (hCN x.2)
  set Nq : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := Nx.map π with hNq
  have hNx_normal : Nx.Normal := by rw [hNx]; exact hNn
  have hNq_normal : Nq.Normal := by rw [hNq]; exact hNx_normal.map π hπsurj
  have hres_top : oPrimeResidual 3 ↥X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hXres.symm
  have hNq_ne_top : Nq ≠ ⊤ := by
    intro htop
    have hcardQ : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ∣ Nat.card ↥Nx := by
      have h := Subgroup.card_map_dvd Nx π
      rw [← hNq, htop, Subgroup.card_top] at h
      exact h
    have hNxcard : Nat.card ↥Nx = Nat.card N := by
      rw [hNx]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
    have h3Q : ¬ 3 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
      rw [hNxcard] at hcardQ
      exact fun h3 => hN3 (h3.trans hcardQ)
    have hgen : oPrimeResidual 3 ↥X ≤ CFSG.pCore 2 ↥X := by
      rw [oPrimeResidual, Subgroup.closure_le]
      rintro x ⟨k, hk⟩
      have hπ1 : π x = 1 := by
        have hdvd : orderOf (π x) ∣ 3 ^ k :=
          orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
        have hQdvd : orderOf (π x) ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) :=
          orderOf_dvd_natCard (π x)
        have h3ord : ¬ 3 ∣ orderOf (π x) := fun h => h3Q (h.trans hQdvd)
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
        have h3j : ¬ 3 ∣ 3 ^ j := by rwa [hj] at h3ord
        have hj0 : j = 0 := by
          by_contra hne
          exact h3j (dvd_pow_self 3 hne)
        have hord1 : orderOf (π x) = 1 := by rw [hj, hj0, pow_zero]
        exact orderOf_eq_one_iff.mp hord1
      exact (QuotientGroup.eq_one_iff x).mp hπ1
    have hPtop : CFSG.pCore 2 ↥X = ⊤ := top_le_iff.mp (hres_top ▸ hgen)
    have hsubQ : Subsingleton (↥X ⧸ CFSG.pCore 2 ↥X) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) b
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      have hxP : x ∈ CFSG.pCore 2 ↥X := by rw [hPtop]; exact Subgroup.mem_top x
      have hyP : y ∈ CFSG.pCore 2 ↥X := by rw [hPtop]; exact Subgroup.mem_top y
      rw [(QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥X) x).mpr hxP,
        (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥X) y).mpr hyP]
    haveI : Subsingleton (↥X ⧸ CFSG.pCore 2 ↥X) := hsubQ
    haveI : IsSimpleGroup ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸
        Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X)) := hq.2.1
    obtain ⟨a, b, hab⟩ := exists_pair_ne ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸
      Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X))
    exact hab (Subsingleton.elim a b)
  have hNq_center : Nq ≤ Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) := by
    haveI : Nq.Normal := hNq_normal
    have hqOpen : CFSG.Open.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hq
    exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hqOpen Nq
      hNq_ne_top
  have hNq_solv : Group.IsSolvable ↥Nq := by
    refine Group.isSolvable_of_comm fun a b => ?_
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hNq_center b.2) (a : ↥X ⧸ CFSG.pCore 2 ↥X))
  have hmap_top : Subgroup.map π (⊤ : Subgroup ↥X) = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hπsurj]
  have hQsup : (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) =
      Subgroup.map π Cx ⊔ Nq := by
    calc (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X))
        = Subgroup.map π (⊤ : Subgroup ↥X) := hmap_top.symm
      _ = Subgroup.map π (Cx ⊔ Nx) := by rw [hCNx]
      _ = Subgroup.map π Cx ⊔ Subgroup.map π Nx := Subgroup.map_sup Cx Nx π
      _ = Subgroup.map π Cx ⊔ Nq := by rw [hNq]
  intro hCsolv
  haveI : Group.IsSolvable ↥C := hCsolv
  have hCxsolv : Group.IsSolvable ↥Cx :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ X)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ X)).injective
  haveI : Group.IsSolvable ↥Cx := hCxsolv
  have hCq_solv : Group.IsSolvable ↥(Subgroup.map π Cx) := by
    let f : ↥Cx →* ↥(Subgroup.map π Cx) :=
      (π.comp Cx.subtype).codRestrict _ fun x => Subgroup.mem_map_of_mem π x.2
    exact Group.isSolvable_of_surjective (f := f) fun y => by
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Group.IsSolvable ↥(Subgroup.map π Cx) := hCq_solv
  have hQNq_solv : Group.IsSolvable ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ Nq) := by
    haveI : Nq.Normal := hNq_normal
    let ψ : ↥(Subgroup.map π Cx) →* ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ Nq) :=
      (QuotientGroup.mk' Nq).comp (Subgroup.map π Cx).subtype
    refine Group.isSolvable_of_surjective (f := ψ) fun z => ?_
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Nq z
    have hq : q ∈ Subgroup.map π Cx ⊔ Nq := by
      rw [← hQsup]; exact Subgroup.mem_top q
    obtain ⟨c, hc, n, hn, hcn⟩ := Subgroup.mem_sup_of_normal_right.mp hq
    refine ⟨⟨c, hc⟩, ?_⟩
    have hn1 : QuotientGroup.mk' Nq n = 1 :=
      (QuotientGroup.eq_one_iff (N := Nq) n).mpr hn
    change QuotientGroup.mk' Nq c = QuotientGroup.mk' Nq q
    rw [← hcn, map_mul, hn1, mul_one]
  have hQsolv : Group.IsSolvable (↥X ⧸ CFSG.pCore 2 ↥X) := by
    haveI : Nq.Normal := hNq_normal
    haveI : Group.IsSolvable ↥Nq := hNq_solv
    haveI : Group.IsSolvable ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ Nq) := hQNq_solv
    refine Group.isSolvable_of_ker_le_range Nq.subtype (QuotientGroup.mk' Nq) ?_
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  haveI : IsSimpleGroup ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸
      Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X)) := hq.2.1
  haveI hQnt : Nontrivial (↥X ⧸ CFSG.pCore 2 ↥X) :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective
      (Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X)))
  haveI : Group.IsPerfect (↥X ⧸ CFSG.pCore 2 ↥X) := hq.1
  exact Group.IsPerfect.not_isSolvable _ hQsolv

theorem zpowers_eq_of_eq_sup_deltaZero {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hsolv : ∀ d : ↥L, (d : G) ∈ A → d ≠ 1 →
      Group.IsSolvable ↥(Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) d} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))))
    {Y : Subgroup G} (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hmeet : MeetsY4 A (lB A) L Y) {c' : G} (hc'A : c' ∈ A) (hc'1 : c' ≠ 1)
    (hdec : Y = pPrimeCoreOf 3 Y ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))) :
    Subgroup.zpowers c' = Subgroup.zpowers c := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set O := pPrimeCoreOf 3 Y with hO
  have htrivY : ∀ y ∈ Y, c' * y * c'⁻¹ * y⁻¹ ∈ O := fun y hy =>
    mul_inv_mem_pPrimeCoreOf_of_eq (fun x hx y hy => hD.commute hx hy) (LB := lB A) hc'A hYA hdec hy
  obtain ⟨X₀, hX₀, hX₀LY⟩ := hmeet
  obtain ⟨hX₀scriptY, hX₀res, _, hX₀q⟩ := hX₀
  have hX₀Y : X₀ ≤ Y := hX₀LY.trans inf_le_right
  have hX₀L : X₀ ≤ L := hX₀LY.trans inf_le_left
  have hX₀N : A ≤ Subgroup.normalizer (X₀ : Set G) := hX₀scriptY.2
  have hX₀O : X₀ ≤ Subgroup.normalizer (O : Set G) :=
    hX₀Y.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hsup : c' ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hAeq ▸ hc'A
  obtain ⟨e, heP, d, hdPL, hed⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (hcomm := fun a ha b hb => hD.commute ((Subgroup.zpowers_le.mpr hD.mem_A) ha) (Subgroup.mem_inf.mp hb).1) hsup
  have heA : e ∈ A := (Subgroup.zpowers_le.mpr hD.mem_A) heP
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hdPL).1
  have hdL : d ∈ L := (Subgroup.mem_inf.mp hdPL).2
  have heO : e ∈ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 Y (hYA heA)
  have hex : ∀ x ∈ X₀, e * x * e⁻¹ = x := by
    intro x hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp heP
    have hcx : Commute c x :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hX₀L hx))).symm
    rw [← hi]
    calc c ^ i * x * (c ^ i)⁻¹ = (c ^ i * x) * (c ^ i)⁻¹ := rfl
      _ = (x * c ^ i) * (c ^ i)⁻¹ := by rw [(hcx.zpow_left i).eq]
      _ = x := by group
  have hdX : ∀ x ∈ X₀, d * x * d⁻¹ ∈ X₀ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hX₀N hdA) x).mp hx
  have hdO : d ∈ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 Y (hYA hdA)
  set N : Subgroup G := X₀ ⊓ O with hN
  have hNX₀ : N ≤ X₀ := inf_le_left
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have hO3 : ¬ 3 ∣ Nat.card O :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
    exact fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le (inf_le_right : N ≤ O)))
  have hNnormal : (N.subgroupOf X₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX₀, Subgroup.le_normalizer_iff]
    intro x hx n hn
    exact ⟨X₀.mul_mem (X₀.mul_mem hx (Subgroup.mem_inf.mp hn).1) (X₀.inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp (hX₀O hx) n).mp (Subgroup.mem_inf.mp hn).2⟩
  have hdN : ∀ n ∈ N, d * n * d⁻¹ ∈ N := by
    intro n hn
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hX₀N hdA) n).mp (Subgroup.mem_inf.mp hn).1,
      (Subgroup.mem_normalizer_iff.mp hdO n).mp (Subgroup.mem_inf.mp hn).2⟩
  have htrivN : ∀ x ∈ X₀, x⁻¹ * (d * x * d⁻¹) ∈ N := by
    intro x hx
    have h1 : c' * x * c'⁻¹ * x⁻¹ ∈ O := htrivY x (hX₀Y hx)
    have h2 : d * x * d⁻¹ * x⁻¹ ∈ O := by
      have hex'' : e⁻¹ * x * e = x := (congrArg (fun z => e⁻¹ * z * e) (hex x hx)).symm.trans
        (by group)
      have hex' : e⁻¹ * x⁻¹ * e = x⁻¹ := by
        calc e⁻¹ * x⁻¹ * e = (e⁻¹ * x * e)⁻¹ := by group
          _ = x⁻¹ := by rw [hex'']
      have h3 : e⁻¹ * (c' * x * c'⁻¹ * x⁻¹) * e = d * x * d⁻¹ * x⁻¹ := by
        rw [← hed]
        calc e⁻¹ * ((e * d) * x * (e * d)⁻¹ * x⁻¹) * e
            = d * x * d⁻¹ * (e⁻¹ * x⁻¹ * e) := by group
          _ = d * x * d⁻¹ * x⁻¹ := by rw [hex']
      rw [← h3]
      exact (Subgroup.mem_normalizer_iff''.mp heO (c' * x * c'⁻¹ * x⁻¹)).mp h1
    have h4 : x⁻¹ * (d * x * d⁻¹ * x⁻¹) * x ∈ O :=
      (Subgroup.mem_normalizer_iff''.mp (hX₀O hx) (d * x * d⁻¹ * x⁻¹)).mp h2
    have h5 : x⁻¹ * (d * x * d⁻¹ * x⁻¹) * x = x⁻¹ * (d * x * d⁻¹) := by group
    rw [h5] at h4
    exact ⟨X₀.mul_mem (X₀.inv_mem hx) (hdX x hx), h4⟩
  have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdA
  have hCns : ¬ Group.IsSolvable ↥(X₀ ⊓ Subgroup.centralizer ({d} : Set G)) :=
    not_isSolvable_inf_centralizer (X := X₀) (N := N) hd3 hX₀res hX₀q hNX₀ hNnormal hN3
      hdX hdN htrivN
  have hd1 : d = 1 := by
    by_contra hdne
    set θ := aschbacherSolvableCore 3 ↥L with hθ
    let πL : ↥L →* (↥L ⧸ θ) := QuotientGroup.mk' θ
    set C₀ : Subgroup G := X₀ ⊓ Subgroup.centralizer ({d} : Set G) with hC₀
    have hC₀L : C₀ ≤ L := inf_le_left.trans hX₀L
    set C₁ : Subgroup ↥L := C₀.subgroupOf L with hC₁
    let ψ : ↥C₁ →* (↥L ⧸ θ) := πL.comp C₁.subtype
    have hθsolv : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    let ι : ↥ψ.ker →* θ :=
      (C₁.subtype.comp ψ.ker.subtype).codRestrict θ
        fun y => (QuotientGroup.eq_one_iff (N := θ) (C₁.subtype y.1)).mp y.2
    have hιinj : Function.Injective ι := by
      intro a b hab
      have h : C₁.subtype (ψ.ker.subtype a) = C₁.subtype (ψ.ker.subtype b) :=
        congrArg (fun z : θ => (z : ↥L)) hab
      exact Subtype.ext (C₁.subtype_injective h)
    have hker_solv : Group.IsSolvable ↥ψ.ker := by
      haveI : Group.IsSolvable θ := hθsolv
      exact Group.isSolvable_of_isSolvable_injective hιinj
    have hrange_cent : ψ.range ≤
        Subgroup.centralizer ({πL ⟨d, hdL⟩} : Set (↥L ⧸ θ)) := by
      rintro _ ⟨c, rfl⟩
      have hc0 : ((c : ↥C₁) : ↥L) ∈ C₀.subgroupOf L := c.2
      have hcd : (((c : ↥C₁) : ↥L) : G) * d = d * (((c : ↥C₁) : ↥L) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc0)).2
      have hcommL : Commute ((c : ↥C₁) : ↥L) ⟨d, hdL⟩ := by
        show ((c : ↥C₁) : ↥L) * ⟨d, hdL⟩ = ⟨d, hdL⟩ * ((c : ↥C₁) : ↥L)
        apply Subtype.ext
        simpa using hcd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommL.map πL).eq
    have hCbar_nsolv : ¬ Group.IsSolvable ↥(Subgroup.centralizer
        ({πL ⟨d, hdL⟩} : Set (↥L ⧸ θ))) := by
      intro hcentSolv
      haveI : Group.IsSolvable ↥(Subgroup.centralizer
          ({πL ⟨d, hdL⟩} : Set (↥L ⧸ θ))) := hcentSolv
      have hrange_solv : Group.IsSolvable ↥ψ.range :=
        Group.isSolvable_of_isSolvable_injective
          (Subgroup.inclusion_injective hrange_cent)
      haveI : Group.IsSolvable ↥ψ.range := hrange_solv
      haveI : Group.IsSolvable ↥ψ.ker := hker_solv
      have hC₁solv : Group.IsSolvable ↥C₁ := by
        refine Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict ?_
        intro x hx
        exact ⟨⟨x, by simpa using hx⟩, rfl⟩
      haveI : Group.IsSolvable ↥C₁ := hC₁solv
      have hC₀solv : Group.IsSolvable ↥C₀ :=
        Group.isSolvable_of_surjective
          (f := (Subgroup.subgroupOfEquivOfLe hC₀L).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hC₀L).surjective
      exact hCns hC₀solv
    exact hCbar_nsolv (hsolv ⟨d, hdL⟩ hdA (fun h1 => hdne (congrArg Subtype.val h1)))
  have hc'P : c' ∈ Subgroup.zpowers c := by
    rw [← hed, hd1, mul_one]
    exact heP
  have hc'3 : c' ^ 3 = 1 := hD.isElemAbelian.2 c' hc'A
  have hc'ord : orderOf c' = 3 := orderOf_eq_prime hc'3 hc'1
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc'P) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hD.orderOf_eq, hc'ord]

end CFSG.RankThree.PartTwo.Sec15.Proof1511Point
