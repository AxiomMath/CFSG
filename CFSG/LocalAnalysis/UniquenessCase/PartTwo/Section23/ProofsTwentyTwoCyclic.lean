module

public import CFSG.LocalAnalysis.UniquenessCase.UCKSemiregularCommute
public import CFSG.GroupTheory.OddPGroupNoncyclicChar
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularInverted
public import CFSG.LocalAnalysis.UniquenessCase.UCKFixedPointFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

private theorem conj_zpow_eq_inv {K : Type*} [Group K] {t x : K}
    (h : t * x * t⁻¹ = x⁻¹) (i : ℤ) : t * x ^ i * t⁻¹ = (x ^ i)⁻¹ := by
  have hconj : MulAut.conj t x = x⁻¹ := by rw [MulAut.conj_apply]; exact h
  calc t * x ^ i * t⁻¹ = (MulAut.conj t) (x ^ i) := (MulAut.conj_apply t (x ^ i)).symm
    _ = ((MulAut.conj t) x) ^ i := map_zpow _ x i
    _ = (x⁻¹) ^ i := by rw [hconj]
    _ = (x ^ i)⁻¹ := inv_zpow x i

private theorem mem_normalizer_zpowers_of_torus {r : ℕ} {a b t : G} {c : Ctx23L D Ch}
    (hT : Ctx23L.OmegaPlusTorus c r a b t) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [conj_zpow_eq_inv hT.t_inv_a]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem (Subgroup.zpowers a)
      (Subgroup.mem_zpowers a) n)
  · intro hy
    have hta : t⁻¹ * a * t = a⁻¹ := by
      have h : t * a⁻¹ * t⁻¹ = a := by
        have h := congrArg Inv.inv hT.t_inv_a
        rw [show (t * a * t⁻¹)⁻¹ = t * a⁻¹ * t⁻¹ from by group] at h
        simpa using h
      calc t⁻¹ * a * t = t⁻¹ * (t * a⁻¹ * t⁻¹) * t := by rw [h]
        _ = a⁻¹ := by group
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : y = (a ^ n)⁻¹ := by
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = t⁻¹ * a ^ n * t := by rw [hn]
        _ = (a ^ n)⁻¹ := by
          simpa using conj_zpow_eq_inv (t := t⁻¹) (x := a) (by simpa using hta) n
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem (Subgroup.zpowers a)
      (Subgroup.mem_zpowers a) n)

private theorem normalizer_zpowers_ne_top_of_torus {r : ℕ} {a b t : G} {c : Ctx23L D Ch}
    (hT : Ctx23L.OmegaPlusTorus c r a b t) (hG : IsSimpleGroup G)
    (hnonab : ∃ x y : G, x * y ≠ y * x) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≠ ⊤ := by
  intro htop
  have hnormal : (Subgroup.zpowers a).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]; exact htop
  rcases hnormal.isSubnormal.eq_bot_or_top_of_isSimpleGroup hG with h | h
  · have h1 := hT.a_order
    rw [Subgroup.zpowers_eq_bot.mp h, orderOf_one] at h1
    exact hT.r_prime.ne_one h1.symm
  · obtain ⟨x, y, hxy⟩ := hnonab
    apply hxy
    have hx : x ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_top x
    have hy : y ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self a m n).eq

private theorem normalizer_zpowers_not_le_of_torus (D : Data G) {r : ℕ} {a b t : G}
    {c : Ctx23L D Ch} (hT : Ctx23L.OmegaPlusTorus c r a b t) :
    ¬ Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ D.M := by
  intro hle
  exact hT.t_not_mem_M (hle (mem_normalizer_zpowers_of_torus hT))

private theorem z_le_pCoreOf_normalizer_inf_and_ne_bot (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : Ctx23L.OmegaPlusTorus c r a b t) (hP : 2 ≤ CFSG.Open.pRank 2 D.Z) :
    D.Z ≤ CFSG.Open.pCoreOf 2
        (Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓ D.M) ∧
      CFSG.Open.pCoreOf 2
        (Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓ D.M) ≠ ⊥ := by
  classical
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]; exact (h4 h1930 c).2.2
  have hZleM : D.Z ≤ D.M := by rw [← (h4 h1930 c).1]; exact (h4 h1930 c).2.1
  have hZH : D.Z ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    intro z hz
    exact CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers a
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hT.a_centralizes z hz))
  have hZHM : D.Z ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓ D.M := le_inf hZH hZleM
  have hZ2 : IsPGroup 2 D.Z :=
    D.sylowM.isPGroup.to_le (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le D.T)
  have hle : D.Z ≤ CFSG.Open.pCoreOf 2
      (Subgroup.normalizer (Subgroup.zpowers a : Set G) ⊓ D.M) :=
    CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hZHM
      (fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hZM hx.2) y).mp hy) hZ2
  have hZne : D.Z ≠ ⊥ := by
    obtain ⟨x, hx, hx2⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank
      Nat.prime_two (by omega : 1 ≤ CFSG.Open.pRank 2 D.Z)
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, orderOf_one] at hx2
    exact (by norm_num : (1 : ℕ) ≠ 2) hx2
  refine ⟨hle, ?_⟩
  intro hbot
  rw [hbot] at hle
  exact hZne (le_bot_iff.mp hle)

private theorem bar_not_mem_zpowers_of_not_centralizes (D : Data G) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {x y : G} (hxM : x ∈ D.M) (hyM : y ∈ D.M) (hxr : orderOf x = r)
    (hyr : orderOf y = r) (hxy : x * y = y * x)
    (hxZ : x ∈ Subgroup.centralizer (D.Z : Set G))
    (hyZ : y ∉ Subgroup.centralizer (D.Z : Set G)) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨y, hyM⟩ : ↥D.M) : Bar2 D.M) ∉
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨x, hxM⟩ : ↥D.M)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  let u : ↥D.M := (⟨x, hxM⟩ : ↥D.M) ^ k * (⟨y, hyM⟩ : ↥D.M)⁻¹
  have huk : QuotientGroup.mk' N u = 1 := by
    dsimp only [u]
    rw [map_mul, map_zpow, map_inv, hk, mul_inv_cancel]
  have huN : u ∈ N := (QuotientGroup.eq_one_iff (N := N) (x := u)).mp huk
  have hcomm : Commute ((⟨x, hxM⟩ : ↥D.M) ^ k) ((⟨y, hyM⟩ : ↥D.M)⁻¹) :=
    ((show Commute (⟨x, hxM⟩ : ↥D.M) ⟨y, hyM⟩ from Subtype.ext hxy).zpow_left k).inv_right
  have h1 : orderOf ((⟨x, hxM⟩ : ↥D.M) ^ k) ∣ r := by
    calc orderOf ((⟨x, hxM⟩ : ↥D.M) ^ k) ∣ orderOf (⟨x, hxM⟩ : ↥D.M) :=
          orderOf_dvd_of_pow_eq_one (zpow_pow_orderOf (x := (⟨x, hxM⟩ : ↥D.M)) (i := k))
      _ = orderOf x := Subgroup.orderOf_mk x hxM
      _ = r := hxr
  have h2 : orderOf ((⟨y, hyM⟩ : ↥D.M)⁻¹) ∣ r := by
    rw [orderOf_inv, Subgroup.orderOf_mk, hyr]
  have hu_dvd : orderOf u ∣ r := by
    dsimp only [u]
    exact hcomm.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd h1 h2)
  have huodd : Odd (orderOf u) := Odd.of_dvd_nat (hr.odd_of_ne_two hr2) hu_dvd
  have hu1 : u = 1 :=
    CFSG.Quasithin.eq_one_of_odd_orderOf_of_mem (K := N) (CFSG.pCore_isPGroup (p := 2)) huN huodd
  have hxyk : (⟨x, hxM⟩ : ↥D.M) ^ k = ⟨y, hyM⟩ :=
    mul_inv_eq_one.mp (show (⟨x, hxM⟩ : ↥D.M) ^ k * (⟨y, hyM⟩ : ↥D.M)⁻¹ = 1 from hu1)
  have hxZ' : (x : G) ^ k ∈ Subgroup.centralizer (D.Z : Set G) :=
    Subgroup.zpow_mem _ hxZ k
  have hxykG : (x : G) ^ k = y := by
    simpa using congrArg Subtype.val hxyk
  exact hyZ (hxykG ▸ hxZ')

private theorem not_mem_zpowers_of_mem_zpowers_ne {K : Type*} [Group K] [Finite K] {q : ℕ}
    (hq : q.Prime) {x y z : K} (hx : orderOf x = q) (hy : orderOf y = q)
    (hyx : y ∉ Subgroup.zpowers x) (hz : z ∈ Subgroup.zpowers y) (hz1 : z ≠ 1) :
    z ∉ Subgroup.zpowers x := by
  intro hzx
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hz
  have ht_ne : ¬ (q : ℤ) ∣ t := by
    intro hdvd
    have h1 : y ^ t = 1 := by
      rw [← hy] at hdvd
      exact orderOf_dvd_iff_zpow_eq_one.mp hdvd
    exact hz1 (by rw [← ht, h1])
  have hyt_ne : y ^ t ≠ 1 := fun h1 => ht_ne (by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hy] at h)
  have hord : orderOf (y ^ t) = q := by
    have hdvd : orderOf (y ^ t) ∣ q := by
      rw [← hy]
      exact orderOf_dvd_of_pow_eq_one (zpow_pow_orderOf (x := y) (i := t))
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
    · exact absurd (orderOf_eq_one_iff.mp h1) hyt_ne
    · exact hq'
  have heq : Subgroup.zpowers (y ^ t) = Subgroup.zpowers y := by
    refine Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨t, rfl⟩)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hy]
  have hzy : Subgroup.zpowers z = Subgroup.zpowers y := by
    rw [← ht]; exact heq
  have hy_in : y ∈ Subgroup.zpowers z := by
    rw [hzy]; exact Subgroup.mem_zpowers y
  exact hyx ((Subgroup.zpowers_le.mpr hzx) hy_in)

private theorem exists_elemAbelian_card_sq_of_pCore (D : Data G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {Dbar : Subgroup (Bar2 D.M)} (hDbar_ne : Dbar ≠ ⊥)
    (hDq : IsPGroup q ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDnc : ¬ IsCyclic ↥Dbar) :
    ∃ Ebar : Subgroup (Bar2 D.M), Ebar ≤ Dbar ∧ CFSG.Open.IsElemAbelian q Ebar ∧
      Nat.card Ebar = q ^ 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hrank : 2 ≤ CFSG.Open.pRank q Dbar := by
    by_contra h
    have h1 : CFSG.Open.pRank q Dbar ≤ 1 := by omega
    have htop : CFSG.Open.pRank q (⊤ : Subgroup ↥Dbar) ≤ 1 := by
      rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Dbar]
    exact hDnc (CFSG.isCyclic_of_pRank_le_one hq hq2 hDq htop)
  have hq_dvd : q ∣ Nat.card ↥Dbar := by
    obtain ⟨k, hk⟩ := hDq.exists_card_eq
    rw [hk]
    refine dvd_pow_self q (fun hk0 => ?_)
    rw [hk0, pow_zero] at hk
    exact hDbar_ne (Subgroup.eq_bot_of_card_eq Dbar hk)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Dbar) q hq_dvd
  let X : Subgroup (Bar2 D.M) := (Subgroup.zpowers x).map Dbar.subtype
  have hXD : X ≤ Dbar := Subgroup.map_subtype_le _
  have hXcard : Nat.card X = q := by
    rw [show Nat.card X = Nat.card (Subgroup.zpowers x) from
      Subgroup.card_map_of_injective Dbar.subtype_injective, Nat.card_zpowers, hxord]
  obtain ⟨Ebar, -, hEbarD, hEbare, hEbarc⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime hDq hrank hXD hXcard
  exact ⟨Ebar, hEbarD, hEbare, hEbarc⟩

private theorem exists_elemAbelian_basis (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDbar_ne : Dbar ≠ ⊥) (hDq : IsPGroup q ↥Dbar)
    (hDexp : ∀ y ∈ Dbar, y ^ q = 1) (hDnc : ¬ IsCyclic ↥Dbar) :
    ∃ (Ebar : Subgroup (Bar2 D.M)) (x₁ x₂ : Bar2 D.M),
      Ebar ≤ Dbar ∧ CFSG.Open.IsElemAbelian q Ebar ∧ Nat.card Ebar = q ^ 2 ∧
      x₁ ∈ Ebar ∧ x₂ ∈ Ebar ∧ x₁ ≠ 1 ∧ orderOf x₁ = q ∧ orderOf x₂ = q ∧
      x₂ ∉ Subgroup.zpowers x₁ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Ebar, hEbarD, hEbare, hEbarc⟩ :=
    exists_elemAbelian_card_sq_of_pCore D hq hq2 hDbar_ne hDq hDexp hDnc
  have hEbar_ne : Ebar ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEbarc
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq.one_lt
    omega
  haveI : Nontrivial ↥Ebar := (Subgroup.nontrivial_iff_ne_bot Ebar).mpr hEbar_ne
  obtain ⟨x₁, hx₁ne⟩ := exists_ne (1 : ↥Ebar)
  have hx₁bar_ne : (x₁ : Bar2 D.M) ≠ 1 := fun h => hx₁ne (Subtype.ext h)
  have hx₁barq : (x₁ : Bar2 D.M) ^ q = 1 := hEbare.2 (x₁ : Bar2 D.M) x₁.2
  have hx₁ord : orderOf (x₁ : Bar2 D.M) = q := orderOf_eq_prime hx₁barq hx₁bar_ne
  have hx₁card : Nat.card (Subgroup.zpowers (x₁ : Bar2 D.M) : Subgroup (Bar2 D.M)) = q := by
    rw [Nat.card_zpowers, hx₁ord]
  obtain ⟨x₂, hx₂E, hx₂not⟩ : ∃ x₂ ∈ Ebar, x₂ ∉ Subgroup.zpowers (x₁ : Bar2 D.M) := by
    by_contra h
    push Not at h
    have hle : Ebar ≤ Subgroup.zpowers (x₁ : Bar2 D.M) := fun y hy => h y hy
    have hcard : q ^ 2 ≤ q := by
      have h := Subgroup.card_le_of_le hle
      rwa [hEbarc, hx₁card] at h
    have hlt : q < q ^ 2 := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ 2 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
    exact absurd hcard (not_le.mpr hlt)
  have hx₂ne : x₂ ≠ 1 := fun h => hx₂not (h ▸ Subgroup.one_mem (Subgroup.zpowers (x₁ : Bar2 D.M)))
  have hx₂q : x₂ ^ q = 1 := hEbare.2 x₂ hx₂E
  have hx₂ord : orderOf x₂ = q := orderOf_eq_prime hx₂q hx₂ne
  exact ⟨Ebar, (x₁ : Bar2 D.M), x₂, hEbarD, hEbare, hEbarc, x₁.2, hx₂E, hx₁bar_ne, hx₁ord,
    hx₂ord, hx₂not⟩

private theorem commutator_mem_pCore_of_commute_bar (D : Data G) {z₁ y : ↥D.M}
    (hyz : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁) :
    z₁ * y * z₁⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥D.M := by
  classical
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  refine (QuotientGroup.eq_one_iff (N := N) (x := z₁ * y * z₁⁻¹ * y⁻¹)).mp ?_
  change QuotientGroup.mk' N ⁅z₁, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hyz

private theorem exists_mul_centralizer_of_commute (D : Data G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {a : G} (haM : a ∈ D.M) {z₁ y : ↥D.M}
    (hz₁a : z₁ * ⟨a, haM⟩ = ⟨a, haM⟩ * z₁) (hz₁q : z₁ ^ q = 1) (hz₁ne : z₁ ≠ 1)
    (hya : y * ⟨a, haM⟩ = ⟨a, haM⟩ * y) (hyq : y ^ q = 1)
    (hyz : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁) :
    ∃ y' : ↥D.M, y' * ⟨a, haM⟩ = ⟨a, haM⟩ * y' ∧ y' * z₁ = z₁ * y' ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y' = QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  let X : Subgroup ↥D.M := Subgroup.centralizer ({⟨a, haM⟩} : Set ↥D.M)
  let N' : Subgroup ↥D.M := N ⊓ X
  let R : Subgroup ↥D.M := Subgroup.zpowers z₁
  have hyX : y ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hz₁X : z₁ ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hz₁a
  have hN'X : N' ≤ X := inf_le_right
  have hN'norm : (N'.subgroupOf X).Normal := by
    rw [show N' = N ⊓ X from rfl, Subgroup.inf_subgroupOf_right]; infer_instance
  have hRnorm : R ≤ Subgroup.normalizer (N' : Set ↥D.M) := Subgroup.zpowers_le.mpr
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hN'X).mp hN'norm hz₁X)
  have hN'2 : IsPGroup 2 N' := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).to_le inf_le_left
  have hsolv : Group.IsSolvable ↥N' := @IsNilpotent.to_isSolvable ↥N' _ hN'2.isNilpotent
  have hcop : Nat.Coprime (Nat.card ↥N') (Nat.card ↥R) := by
    obtain ⟨m, hm⟩ := hN'2.exists_card_eq
    rw [hm, Nat.card_zpowers, orderOf_eq_prime hz₁q hz₁ne]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (hq.odd_of_ne_two hq2))
  have hfixN : z₁ * y * z₁⁻¹ * y⁻¹ ∈ N := commutator_mem_pCore_of_commute_bar D hyz
  have hfixX : z₁ * y * z₁⁻¹ * y⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem hz₁X hyX) (X.inv_mem hz₁X)) (X.inv_mem hyX)
  have hxR : ∀ r' ∈ R, ⁅y, r'⁆ ∈ N' :=
    commutator_zpowers_mem_of_conj_mem (N := N') (x := y) (b := z₁)
      (hRnorm (Subgroup.mem_zpowers z₁)) (Subgroup.mem_inf.mpr ⟨hfixN, hfixX⟩)
  obtain ⟨n, hnN', hyinf⟩ :=
    CFSG.GroupTheory.exists_mul_mem_inf_centralizer_of_commutator_mem
      (X := X) (N := N') (R := R) hN'X hN'norm hRnorm hsolv hcop hyX hxR
  refine ⟨y * n, ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp hyinf.1
  · exact (Subgroup.mem_centralizer_iff.mp hyinf.2 z₁ (Subgroup.mem_zpowers z₁)).symm
  · rw [map_mul, show QuotientGroup.mk' N n = 1 from
      (QuotientGroup.eq_one_iff (N := N) (x := n)).mpr hnN'.1, mul_one]

private theorem zpow_mul_not_mem_centralizer (D : Data G) {r : ℕ} {a b t : G}
    {c : Ctx23L D Ch} (hT : Ctx23L.OmegaPlusTorus c r a b t) {i j : ℤ}
    (hj : ¬ (r : ℤ) ∣ j) :
    a ^ i * b ^ j ∉ Subgroup.centralizer (D.Z : Set G) := by
  intro hmem
  have hbpow : b ^ j ∈ Subgroup.centralizer (D.Z : Set G) := by
    have hai : a ^ i ∈ Subgroup.centralizer (D.Z : Set G) :=
      Subgroup.zpow_mem _ hT.a_centralizes i
    rw [show b ^ j = (a ^ i)⁻¹ * (a ^ i * b ^ j) from by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hai) hmem
  have hbj1 : b ^ j ≠ 1 := by
    intro h1
    exact hj (by
      have h := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hT.b_order] at h)
  have hzp : Subgroup.zpowers (b ^ j) = Subgroup.zpowers b :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers hT.r_prime
      (by rw [← hT.b_order]; exact pow_orderOf_eq_one b) hbj1
      (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
  exact hT.b_not_centralizes (Subgroup.zpowers_le.mpr hbpow (hzp ▸ Subgroup.mem_zpowers b))

private theorem inf_centralizer_bar_zpow_mul_eq_bot (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : Ctx23L.OmegaPlusTorus c r a b t) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) {i j : ℤ} (hj : ¬ (r : ℤ) ∣ j) :
    Dbar ⊓ Subgroup.centralizer
      ({((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
            (⟨a, Ctx23L.mem_M_of_torus c h1930 h4 hT⟩ : ↥D.M)) ^ i) *
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hT.b_mem_M⟩ : ↥D.M)) ^ j)} :
        Set (Bar2 D.M)) = ⊥ := by
  classical
  have haM : a ∈ D.M := Ctx23L.mem_M_of_torus c h1930 h4 hT
  have hbM : b ∈ D.M := hT.b_mem_M
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]; exact (h4 h1930 c).2.2
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
      (⟨a ^ i * b ^ j, D.M.mul_mem (D.M.zpow_mem haM i) (D.M.zpow_mem hbM j)⟩ : ↥D.M) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)) ^ i *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M)) ^ j := by
    rw [show (⟨a ^ i * b ^ j, D.M.mul_mem (D.M.zpow_mem haM i) (D.M.zpow_mem hbM j)⟩ : ↥D.M) =
      (⟨a, haM⟩ : ↥D.M) ^ i * (⟨b, hbM⟩ : ↥D.M) ^ j from Subtype.ext (by simp)]
    rw [map_mul, map_zpow, map_zpow]
  rw [← hmk]
  have hconj : t * (a ^ i * b ^ j) * t⁻¹ = (a ^ i * b ^ j)⁻¹ := by
    have hcommij : a ^ i * b ^ j = b ^ j * a ^ i :=
      ((show Commute a b from hT.commute).zpow_left i).zpow_right j |>.eq
    calc t * (a ^ i * b ^ j) * t⁻¹ = (t * a ^ i * t⁻¹) * (t * b ^ j * t⁻¹) := by group
      _ = (a ^ i)⁻¹ * (b ^ j)⁻¹ := by
        rw [conj_zpow_eq_inv hT.t_inv_a, conj_zpow_eq_inv hT.t_inv_b]
      _ = (a ^ i * b ^ j)⁻¹ := by rw [← mul_inv_rev, hcommij]
  exact Ctx23L.inf_centralizer_bar_eq_bot_of_inverted c hZM h1930 h6 hsp h71 hsig
    (D.M.mul_mem (D.M.zpow_mem haM i) (D.M.zpow_mem hbM j))
    (Odd.of_dvd_nat (hT.r_prime.odd_of_ne_two hT.r_ne_two)
      ((Commute.orderOf_mul_dvd_lcm
        (((show Commute a b from hT.commute).zpow_left i).zpow_right j)).trans
        (Nat.lcm_dvd
          (by rw [← hT.a_order]
              exact orderOf_dvd_of_pow_eq_one (zpow_pow_orderOf (x := a) (i := i)))
          (by rw [← hT.b_order]
              exact orderOf_dvd_of_pow_eq_one (zpow_pow_orderOf (x := b) (i := j))))))
    (zpow_mul_not_mem_centralizer D hT hj) hconj hq hq2 hDn hDq hDnc hDexp hDcl

private theorem centralizer_bar_of_noncyclic_pCore (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : Ctx23L.OmegaPlusTorus c r a b t) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqr : q ≠ r)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) :
    Dbar ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, Ctx23L.mem_M_of_torus c h1930 h4 hT⟩ :
        ↥D.M)} : Set (Bar2 D.M)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact r.Prime := ⟨hT.r_prime⟩
  have haM : a ∈ D.M := Ctx23L.mem_M_of_torus c h1930 h4 hT
  have hbM : b ∈ D.M := hT.b_mem_M
  have hcomm : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M)) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M)) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
      (Subtype.ext hT.commute)
  have hb_not : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M) : Bar2 D.M) ∉
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)) :=
    bar_not_mem_zpowers_of_not_centralizes D hT.r_prime hT.r_ne_two haM hbM hT.a_order
      hT.b_order hT.commute hT.a_centralizes hT.b_not_centralizes
  have hcop : Nat.Coprime r (Nat.card ↥Dbar) := by
    obtain ⟨k, hk⟩ := hDq.exists_card_eq
    rw [hk]
    exact ((Nat.coprime_primes hT.r_prime hq).mpr (Ne.symm hqr)).pow_right k
  have hnorm : ∀ x : Bar2 D.M, x ∈ Subgroup.normalizer (Dbar : Set (Bar2 D.M)) := fun _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hDn]; exact Subgroup.mem_top _
  refine CFSG.GroupTheory.le_centralizer_of_rank_two (x := QuotientGroup.mk'
      (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)) (y := QuotientGroup.mk'
      (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M)) (Q := Dbar)
    (by
      refine UCK.orderOf_mk'_pCore_eq_of_prime (M := ↥D.M) hT.r_prime hT.r_ne_two ?_
      rw [Subgroup.orderOf_mk]; exact hT.a_order)
    (by
      refine UCK.orderOf_mk'_pCore_eq_of_prime (M := ↥D.M) hT.r_prime hT.r_ne_two ?_
      rw [Subgroup.orderOf_mk]; exact hT.b_order) hcomm hb_not (hnorm _) (hnorm _) hcop ?_
  intro i j hj
  exact inf_centralizer_bar_zpow_mul_eq_bot D Ch h4 h1930 c hT h6 hsp h71 hsig hq hq2
    hDn hDq hDnc hDexp hDcl hj

private theorem false_of_eq_torus_prime (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : Ctx23L.OmegaPlusTorus c r a b t) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqr : q = r)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDbar_ne : Dbar ≠ ⊥) (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) : False := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]; exact (h4 h1930 c).2.2
  have hbM : b ∈ D.M := hT.b_mem_M
  have hbodd : Odd (orderOf b) :=
    hT.b_order ▸ (hqr.symm ▸ hT.r_prime.odd_of_ne_two hT.r_ne_two)
  have hsem := Ctx23L.inf_centralizer_bar_eq_bot_of_inverted c hZM h1930 h6 hsp h71 hsig hbM
    hbodd hT.b_not_centralizes hT.t_inv_b hq hq2 hDn hDq hDnc hDexp hDcl
  have hbpow : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M) : Bar2 D.M) ^ q = 1 := by
    have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
        (⟨b, hbM⟩ : ↥D.M) : Bar2 D.M) = q := by
      rw [UCK.orderOf_mk'_pCore_eq_of_prime (M := ↥D.M) hT.r_prime hT.r_ne_two
        (by rw [Subgroup.orderOf_mk]; exact hT.b_order), ← hqr]
    rw [← hord]; exact pow_orderOf_eq_one _
  have hbnorm : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M) : Bar2 D.M) ∈
      Subgroup.normalizer (Dbar : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hDn]; exact Subgroup.mem_top _
  obtain ⟨x, hxQ, hx1, hxcomm⟩ :=
    CFSG.GroupTheory.exists_ne_one_commute_of_isPGroup (q := q) hDq hDbar_ne hbpow hbnorm
  have hxmem : x ∈ Dbar ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hbM⟩ : ↥D.M)} : Set (Bar2 D.M)) :=
    ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxcomm⟩
  rw [hsem] at hxmem
  exact hx1 (Subgroup.mem_bot.mp hxmem)

private theorem exists_central_lift (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {a : G} (haM : a ∈ D.M) {Ebar : Subgroup (Bar2 D.M)} {x₁ x₂ : Bar2 D.M}
    (hEbare : CFSG.Open.IsElemAbelian q Ebar) (hx₁E : x₁ ∈ Ebar) (hx₂E : x₂ ∈ Ebar)
    {z₁ y₂ : ↥D.M} (hz₁a : z₁ * ⟨a, haM⟩ = ⟨a, haM⟩ * z₁) (hz₁q : z₁ ^ q = 1)
    (hz₁ne : z₁ ≠ 1)
    (hz₁mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁ ∈ Subgroup.zpowers x₁)
    (hy₂a : y₂ * ⟨a, haM⟩ = ⟨a, haM⟩ * y₂) (hy₂q : y₂ ^ q = 1) (hy₂ne : y₂ ≠ 1)
    (hy₂mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y₂ ∈ Subgroup.zpowers x₂) :
    ∃ y : ↥D.M, y * ⟨a, haM⟩ = ⟨a, haM⟩ * y ∧ y * z₁ = z₁ * y ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y = QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y₂ ∧
      y ^ q ∈ CFSG.pCore 2 ↥D.M ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsMulCommutative ↥Ebar := hEbare.1
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  have hz₁E : QuotientGroup.mk' N z₁ ∈ Ebar := Subgroup.zpowers_le.mpr hx₁E hz₁mem
  have hy₂E : QuotientGroup.mk' N y₂ ∈ Ebar := Subgroup.zpowers_le.mpr hx₂E hy₂mem
  have hy₂z : QuotientGroup.mk' N z₁ * QuotientGroup.mk' N y₂ =
      QuotientGroup.mk' N y₂ * QuotientGroup.mk' N z₁ := congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := ↥Ebar)).comm ⟨QuotientGroup.mk' N z₁, hz₁E⟩
      ⟨QuotientGroup.mk' N y₂, hy₂E⟩)
  obtain ⟨y, hya, hyz, hymk⟩ := exists_mul_centralizer_of_commute D hq hq2 haM hz₁a hz₁q
    hz₁ne hy₂a hy₂q hy₂z
  have hy₂mk_ne : QuotientGroup.mk' N y₂ ≠ 1 := by
    intro h1
    have hmemN : y₂ ∈ N := (QuotientGroup.eq_one_iff (N := N) (x := y₂)).mp h1
    have hodd : Odd (orderOf y₂) := by
      rw [orderOf_eq_prime hy₂q hy₂ne]; exact hq.odd_of_ne_two hq2
    exact hy₂ne (CFSG.Quasithin.eq_one_of_odd_orderOf_of_mem (K := N)
      (CFSG.pCore_isPGroup (p := 2)) hmemN hodd)
  have hymk_ne : QuotientGroup.mk' N y ≠ 1 := by rw [hymk]; exact hy₂mk_ne
  have hyqN : y ^ q ∈ N := by
    refine (QuotientGroup.eq_one_iff (N := N) (x := y ^ q)).mp ?_
    change QuotientGroup.mk' N (y ^ q) = 1
    rw [map_pow, hymk, ← map_pow, hy₂q, map_one]
  exact ⟨y, hya, hyz, hymk, hyqN, hymk_ne⟩

private theorem exists_pow_of_central_lift (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {a : G} (haM : a ∈ D.M) {x₂ : Bar2 D.M} {z₁ y : ↥D.M}
    (hya : y * ⟨a, haM⟩ = ⟨a, haM⟩ * y) (hyz : y * z₁ = z₁ * y)
    (hyqN : y ^ q ∈ CFSG.pCore 2 ↥D.M)
    (hymem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y ∈ Subgroup.zpowers x₂)
    (hymk_ne : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) y ≠ 1) (hx₂ord : orderOf x₂ = q) :
    ∃ z₂ : ↥D.M, z₂ * ⟨a, haM⟩ = ⟨a, haM⟩ * z₂ ∧ z₂ * z₁ = z₁ * z₂ ∧ z₂ ^ q = 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ∈ Subgroup.zpowers x₂ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
  have hord : orderOf (QuotientGroup.mk' N y) = q := by
    refine orderOf_eq_prime ?_ hymk_ne
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := N) (x := y ^ q)).mpr hyqN
  refine ⟨y ^ (2 ^ k), ((show Commute y ⟨a, haM⟩ from hya).pow_left (2 ^ k)).eq,
    ((show Commute y z₁ from hyz).pow_left (2 ^ k)).eq, ?_, ?_, ?_⟩
  · have h1 : (y ^ q) ^ (2 ^ k) = 1 := by
      have h := pow_card_eq_one' (x := (⟨y ^ q, hyqN⟩ : ↥N))
      rw [hk] at h
      exact congrArg Subtype.val h
    calc (y ^ (2 ^ k)) ^ q = y ^ (2 ^ k * q) := (pow_mul _ _ _).symm
      _ = y ^ (q * 2 ^ k) := by rw [Nat.mul_comm]
      _ = (y ^ q) ^ (2 ^ k) := pow_mul _ _ _
      _ = 1 := h1
  · rw [map_pow]
    exact Subgroup.pow_mem _ hymem (2 ^ k)
  · rw [map_pow]
    intro h1
    have hdvd : q ∣ 2 ^ k := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h1
    exact hq2 (Or.resolve_left
      ((Nat.dvd_prime Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd)) hq.ne_one)

private theorem not_mem_zpowers_second_lift (D : Data G) {q : ℕ} (hq : q.Prime)
    {x₁ x₂ : Bar2 D.M} (hx₁ord : orderOf x₁ = q) (hx₂ord : orderOf x₂ = q)
    (hx₂not : x₂ ∉ Subgroup.zpowers x₁) {z₁ z₂ : ↥D.M}
    (hz₁mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁ ∈ Subgroup.zpowers x₁)
    (hz₂mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ∈ Subgroup.zpowers x₂)
    (hz₂mk_ne : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ≠ 1) :
    z₂ ∉ Subgroup.zpowers z₁ := by
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hzmk : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ∈ Subgroup.zpowers x₁ := by
    rw [show QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁) ^ m from by rw [← hm, map_zpow]]
    exact Subgroup.zpow_mem _ hz₁mem m
  exact not_mem_zpowers_of_mem_zpowers_ne hq hx₁ord hx₂ord hx₂not hz₂mem hz₂mk_ne hzmk

private theorem map_sup_zpowers_le_barPreimage (D : Data G) {Ebar Dbar : Subgroup (Bar2 D.M)}
    {x₁ x₂ : Bar2 D.M} (hEbarD : Ebar ≤ Dbar) (hx₁E : x₁ ∈ Ebar) (hx₂E : x₂ ∈ Ebar)
    {z₁ z₂ : ↥D.M}
    (hz₁mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁ ∈ Subgroup.zpowers x₁)
    (hz₂mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ∈ Subgroup.zpowers x₂) :
    (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ≤ Dbar := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]; exact hEbarD (Subgroup.zpowers_le.mpr hx₁E hz₁mem)
  · rw [Subgroup.zpowers_le]; exact hEbarD (Subgroup.zpowers_le.mpr hx₂E hz₂mem)

private theorem exists_elemAbelian_map_of_sup (D : Data G) {q : ℕ} (hq : q.Prime)
    {a : G} (haM : a ∈ D.M) {Dbar Ebar : Subgroup (Bar2 D.M)} {x₁ x₂ : Bar2 D.M}
    (hEbarD : Ebar ≤ Dbar) (hx₁E : x₁ ∈ Ebar) (hx₂E : x₂ ∈ Ebar)
    {z₁ z₂ : ↥D.M} (hz₁a : z₁ * ⟨a, haM⟩ = ⟨a, haM⟩ * z₁)
    (hz₂a : z₂ * ⟨a, haM⟩ = ⟨a, haM⟩ * z₂) (hz₂z₁ : z₂ * z₁ = z₁ * z₂)
    (hz₁q : z₁ ^ q = 1) (hz₁ne : z₁ ≠ 1) (hz₂q : z₂ ^ q = 1)
    (hz₂_not : z₂ ∉ Subgroup.zpowers z₁)
    (hz₁mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₁ ∈ Subgroup.zpowers x₁)
    (hz₂mem : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z₂ ∈ Subgroup.zpowers x₂) :
    ∃ E : Subgroup G, E ≤ D.M ∧ CFSG.Open.IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      E ≤ Subgroup.centralizer ({a} : Set G) ∧ E ≤ barPreimage D.M Dbar := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  have hz₂ne : z₂ ≠ 1 := fun h => hz₂_not (h ▸ Subgroup.one_mem (Subgroup.zpowers z₁))
  have hz₁_ord : orderOf z₁ = q := orderOf_eq_prime hz₁q hz₁ne
  have hz₂_ord : orderOf z₂ = q := orderOf_eq_prime hz₂q hz₂ne
  have hcomm : ∀ x ∈ Subgroup.zpowers z₁, x * z₂ = z₂ * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute z₁ z₂ from hz₂z₁.symm).zpow_left n).eq
  obtain ⟨hEb_el, hEb_card⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (X := Subgroup.zpowers z₁)
      (v := z₂) (by rw [Nat.card_zpowers, hz₁_ord]) hz₂_ord hz₂_not hcomm
  have hEbC : Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ ≤
      Subgroup.centralizer ({⟨a, haM⟩} : Set ↥D.M) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hz₁a))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hz₂a))
  have hEb_le := map_sup_zpowers_le_barPreimage D hEbarD hx₁E hx₂E hz₁mem hz₂mem
  refine ⟨(Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂).map D.M.subtype, Subgroup.map_subtype_le _,
    hEb_el.map D.M.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective D.M.subtype_injective, hEb_card]
  · rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hEbC hy)))
  · rintro x ⟨y, hy, rfl⟩
    exact uc22p21c_mem_barPreimage.2
      ⟨Subgroup.map_subtype_le _ ⟨y, hy, rfl⟩,
        hEb_le (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hy)⟩

private theorem exists_elemAbelian_lift (D : Data G) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {a : G} (haM : a ∈ D.M) (har : orderOf a = r) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDbar_ne : Dbar ≠ ⊥) (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hQcent : Dbar ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)} : Set (Bar2 D.M))) :
    ∃ E : Subgroup G, E ≤ D.M ∧ CFSG.Open.IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      E ≤ Subgroup.centralizer ({a} : Set G) ∧ E ≤ barPreimage D.M Dbar := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let N : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
  let a' : ↥D.M := ⟨a, haM⟩
  obtain ⟨Ebar, x₁, x₂, hEbarD, hEbare, hEbarc, hx₁E, hx₂E, hx₁ne, hx₁ord, hx₂ord, hx₂not⟩ :=
    exists_elemAbelian_basis D hq hq2 hDbar_ne hDq hDexp hDnc
  have ha'ord : orderOf a' = r := by rw [Subgroup.orderOf_mk]; exact har
  have hx₁a : QuotientGroup.mk' N a' * x₁ = x₁ * QuotientGroup.mk' N a' :=
    (Subgroup.mem_centralizer_iff.mp (hQcent (hEbarD hx₁E)))
      (QuotientGroup.mk' N a') (Set.mem_singleton _)
  have hx₂a : QuotientGroup.mk' N a' * x₂ = x₂ * QuotientGroup.mk' N a' :=
    (Subgroup.mem_centralizer_iff.mp (hQcent (hEbarD hx₂E)))
      (QuotientGroup.mk' N a') (Set.mem_singleton _)
  have hx₂ne : x₂ ≠ 1 :=
    fun h => hx₂not (h ▸ Subgroup.one_mem (Subgroup.zpowers x₁))
  obtain ⟨z₁, hz₁a, hz₁q, hz₁ne, hz₁mem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar (M := D.M) (b := a')
      (by rw [ha'ord]; exact hr.odd_of_ne_two hr2)
      hq hq2 hx₁ne (hEbare.2 x₁ hx₁E) hx₁a
  obtain ⟨y₂, hy₂a, hy₂q, hy₂ne, hy₂mem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar (M := D.M) (b := a')
      (by rw [ha'ord]; exact hr.odd_of_ne_two hr2)
      hq hq2 hx₂ne (hEbare.2 x₂ hx₂E) hx₂a
  obtain ⟨y, hya, hyz, hymk, hyqN, hymk_ne⟩ := exists_central_lift D hq hq2 haM hEbare
    hx₁E hx₂E hz₁a hz₁q hz₁ne hz₁mem hy₂a hy₂q hy₂ne hy₂mem
  have hymem : QuotientGroup.mk' N y ∈ Subgroup.zpowers x₂ := by rw [hymk]; exact hy₂mem
  obtain ⟨z₂, hz₂a, hz₂z₁, hz₂q, hz₂mem, hz₂mk_ne⟩ := exists_pow_of_central_lift D hq hq2
    haM hya hyz hyqN hymem hymk_ne hx₂ord
  have hz₂_not : z₂ ∉ Subgroup.zpowers z₁ :=
    not_mem_zpowers_second_lift D hq hx₁ord hx₂ord hx₂not hz₁mem hz₂mem hz₂mk_ne
  exact exists_elemAbelian_map_of_sup D hq haM hEbarD hx₁E hx₂E hz₁a hz₂a hz₂z₁ hz₁q hz₁ne
    hz₂q hz₂_not hz₁mem hz₂mem

private theorem rankThreeGamma_one_le_of_barPreimage (D : Data G) (Ch : Choice2011 G)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) {E : Subgroup G} (hEel : CFSG.Open.IsElemAbelian q E)
    (hEP : E ≤ barPreimage D.M Dbar) :
    rankThreeGamma 1 q E ≤ D.M := by
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro F hFE hF
  have hFne : F ≠ ⊥ := by
    obtain ⟨x, hx, hxq⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hq hF
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, orderOf_one] at hxq
    exact hq.ne_one hxq.symm
  exact normalizer_le_of_mem_uniqueSet D.maxLocal
    (c.mem_uniqueSet_of_le_barPreimage' h1930 h6 hsp h71 hsig hq hq2 hDn hDq hDnc hDexp hDcl
      hFne (hEel.isPGroup.to_le hFE) (hFE.trans hEP))

private theorem exists_bar_of_pCore_not_cyclic (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hnc : ¬ IsCyclic ↥(CFSG.pCore q (Bar2 D.M))) :
    ∃ Dbar : Subgroup (Bar2 D.M), Dbar.Normal ∧ IsPGroup q ↥Dbar ∧ Dbar ≠ ⊥ ∧
      ¬ IsCyclic ↥Dbar ∧ (∀ y ∈ Dbar, y ^ q = 1) ∧ ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Dbar, hDbar_le, hDbar_ne, hDbar_nc, hDbar_exp, hDbar_cl, hDbar_norm⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized (G := Bar2 D.M) (p := q)
      hq2 (CFSG.pCore_isPGroup (p := q)) hnc
  have hDn : Dbar.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp ?_
    rw [eq_top_iff]
    calc (⊤ : Subgroup (Bar2 D.M)) =
        Subgroup.normalizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) :=
          (Subgroup.normalizer_eq_top_iff.mpr CFSG.pCore_normal).symm
      _ ≤ Subgroup.normalizer (Dbar : Set (Bar2 D.M)) := hDbar_norm
  exact ⟨Dbar, hDn, (CFSG.pCore_isPGroup (p := q)).to_le hDbar_le, hDbar_ne, hDbar_nc,
    hDbar_exp, hDbar_cl⟩

private theorem isCyclic_pCore_of_torus (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (hP : 2 ≤ CFSG.Open.pRank 2 D.Z)
    {r : ℕ} {a b t : G} (hT : Ctx23L.OmegaPlusTorus c r a b t) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty) (h67 : UC6.R6_7 D)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    IsCyclic ↥(CFSG.pCore q (Bar2 D.M)) := by
  classical
  by_contra hnc
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Dbar, hDn, hDq, hDbar_ne, hDbar_nc, hDbar_exp, hDbar_cl⟩ :=
    exists_bar_of_pCore_not_cyclic D hq hq2 hnc
  rcases eq_or_ne q r with hqr | hqr
  · exact (false_of_eq_torus_prime D Ch h4 h1930 c hT h6 hsp h71 hsig hq hq2 hqr hDn hDq
      hDbar_ne hDbar_nc hDbar_exp hDbar_cl).elim
  · have hQcent := centralizer_bar_of_noncyclic_pCore D Ch h4 h1930 c hT h6 hsp h71 hsig hq
      hq2 hqr hDn hDq hDbar_nc hDbar_exp hDbar_cl
    obtain ⟨E, hEM, hEel, hEcard, hEcent, hEP⟩ :=
      exists_elemAbelian_lift D hT.r_prime hT.r_ne_two
        (Ctx23L.mem_M_of_torus c h1930 h4 hT) hT.a_order hq hq2 hDn hDq hDbar_ne hDbar_nc
        hDbar_exp hQcent
    have hΓ : rankThreeGamma 1 q E ≤ D.M :=
      rankThreeGamma_one_le_of_barPreimage D Ch h1930 c h6 hsp h71 hsig hq hq2 hDn hDq hDbar_nc
        hDbar_exp hDbar_cl hEel hEP
    let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers a : Set G)
    have hEH : E ≤ H := hEcent.trans
      (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers a)
    have hHne : H ≠ ⊤ :=
      normalizer_zpowers_ne_top_of_torus hT D.standing.simple D.standing.nonab
    have hHnotM : ¬ H ≤ D.M := normalizer_zpowers_not_le_of_torus D hT
    obtain ⟨hZle, hcore_ne⟩ := z_le_pCoreOf_normalizer_inf_and_ne_bot D Ch h4 h1930 c hT hP
    obtain ⟨-, t', ht'ord, hcore, -⟩ :=
      h67 (by rw [h6 h1930 c]) q hq hq2 E hEM hEel hEcard hΓ H hEH hHne hcore_ne hHnotM
    have hrank : CFSG.Open.pRank 2 D.Z ≤ 1 := by
      have h1 : CFSG.Open.pRank 2 D.Z ≤ CFSG.Open.pRank 2 (Subgroup.zpowers t') :=
        CFSG.SectionRank.pRank_mono (by norm_num : 1 < 2) (hcore ▸ hZle)
      exact h1.trans (CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_two
        (Subgroup.isCyclic_zpowers t'))
    omega

theorem s23_22Fitting_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) :
    S23_22Fitting D Ch := by
  intro h1930 c hP r a b t hT h6 hsp h71 hsig h67
  refine UCK.isCyclic_fittingSubgroup_of_isCyclic_pCore (X := Bar2 D.M) fun p hp => ?_
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [uc22p20c_pCore_quotient_pCore (H := ↥D.M) (p := 2)]
    infer_instance
  · exact isCyclic_pCore_of_torus D Ch h4 h1930 c hP hT h6 hsp h71 hsig h67 hp hp2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
