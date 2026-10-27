module

public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.CentralQuotientCoprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC6S846 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_mem_bar2_orderOf_of_quotInf {M K : Subgroup G} (hK : K ∈ calC M)
    {r : ℕ} (hr : r.Prime) (hrZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 K)))
    {xbar : BarInf K ⧸ Subgroup.center (BarInf K)} (hxord : orderOf xbar = r) :
    ∃ x : ↥K, orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) = r ∧
      piBarInf K x = xbar := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  let e := quotInfEquivBar2 hq
  let z : Bar2 K ⧸ Subgroup.center (Bar2 K) := e xbar
  have hzord : orderOf z = r := by
    rw [show z = e xbar from rfl, MulEquiv.orderOf_eq, hxord]
  obtain ⟨x1, hx1⟩ := QuotientGroup.mk_surjective z
  have hx1' : (QuotientGroup.mk' (Subgroup.center (Bar2 K))) x1 = z := by
    simpa [QuotientGroup.mk'_apply] using hx1
  have hmemZ : x1 ^ r ∈ Subgroup.center (Bar2 K) := by
    rw [← QuotientGroup.eq_one_iff,
      ← QuotientGroup.mk'_apply (N := Subgroup.center (Bar2 K)) (x1 ^ r)]
    rw [map_pow, hx1', ← hzord, pow_orderOf_eq_one]
  have hm : (x1 ^ r) ^ Nat.card (Subgroup.center (Bar2 K)) = 1 := by
    have h := pow_card_eq_one' (x := (⟨x1 ^ r, hmemZ⟩ : Subgroup.center (Bar2 K)))
    exact congrArg Subtype.val h
  have hcop : Nat.Coprime (Nat.card (Subgroup.center (Bar2 K))) r := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hr).mpr hrZ
  obtain ⟨k, hkmap, hkord⟩ :=
    exists_pow_orderOf_eq_of_coprime_map
      (φ := QuotientGroup.mk' (Subgroup.center (Bar2 K))) (x := x1) hr
      (by rw [hx1']; exact hzord) hm hcop
  obtain ⟨xK, hxK⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) (x1 ^ k)
  have hxK' : QuotientGroup.mk xK = x1 ^ k := by
    rw [← QuotientGroup.mk'_apply (N := CFSG.pCore 2 ↥K) xK, hxK]
  refine ⟨xK, by rw [hxK, hkord], ?_⟩
  apply e.injective
  rw [quotInfEquivBar2_piBarInf]
  change QuotientGroup.mk (QuotientGroup.mk xK) = e xbar
  rw [hxK', ← QuotientGroup.mk'_apply (N := Subgroup.center (Bar2 K)) (x1 ^ k), hkmap]
  exact hx1'



private theorem rhoL_piBarInf_fix_of_orderOf {K : Subgroup G} {b : G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) {r : ℕ} (hr : r.Prime)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 K)))
    {x : ↥K} (hxord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) = r)
    (hfix : inducedQuotInfAut K b hb (piBarInf K x) = piBarInf K x) :
    rhoL K ⟨b, hb⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) x := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let u : Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) x
  let xc : ↥K :=
    ⟨b * (x : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb x).mp x.2⟩
  let v : Bar2 K := rhoL K ⟨b, hb⟩ u
  have hclass : (QuotientGroup.mk' (Subgroup.center (Bar2 K))) (QuotientGroup.mk xc) =
      (QuotientGroup.mk' (Subgroup.center (Bar2 K))) (QuotientGroup.mk x) := by
    have h1 := congrArg (quotInfEquivBar2 hq) hfix
    rw [quotInfEquivBar2_inducedQuotInfAut_piBarInf, quotInfEquivBar2_piBarInf] at h1
    simpa [xc] using h1
  have hrho : v = QuotientGroup.mk xc := by
    show rhoL K ⟨b, hb⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) = _
    rw [QuotientGroup.mk'_apply, rhoL_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    rw [rhoL_mk_coe]
  have hclass' : (QuotientGroup.mk' (Subgroup.center (Bar2 K))) v =
      (QuotientGroup.mk' (Subgroup.center (Bar2 K))) u := by
    rw [hrho]
    simpa [u, QuotientGroup.mk'_apply] using hclass
  have hvord : orderOf v = r := by
    rw [show v = rhoL K ⟨b, hb⟩ u from rfl, MulEquiv.orderOf_eq, hxord]
  have hv1 : v ^ r = 1 := by rw [← hvord]; exact pow_orderOf_eq_one v
  have hu1 : u ^ r = 1 := by rw [← hxord]; exact pow_orderOf_eq_one u
  have hcopZ : Nat.Coprime r (Nat.card (Subgroup.center (Bar2 K))) :=
    (hr.coprime_iff_not_dvd).mpr hrZ
  have hvu := CFSG.GroupTheory.eq_of_mk_eq_of_pow_eq_one_of_coprime
    (Z := Subgroup.center (Bar2 K)) le_rfl hcopZ hv1 hu1 hclass'
  simpa [v, u] using hvu

private theorem exists_mem_centralizer_of_bar2_orderOf {M K : Subgroup G} (hK : K ∈ calC M)
    {b : G} (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 K)))
    {x : ↥K} (hxord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) = r)
    (hfix : inducedQuotInfAut K b hb (piBarInf K x) = piBarInf K x) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧
      orderOf (y : G) = r ∧ piBarInf K y = piBarInf K x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hfixBar := rhoL_piBarInf_fix_of_orderOf hq hb hr hrZ hxord hfix
  have hfixP4 : b * (x : G) * b⁻¹ * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    refine (rhoL_fix_iff K ⟨b, hb⟩ x).mp ?_
    simpa [QuotientGroup.mk'_apply] using hfixBar
  obtain ⟨y, hyC, hyord, hyimage⟩ :=
    exists_mem_inf_centralizer_of_bar_fixed (K := K) (b := b) (x := (x : G))
      hb hbodd x.2 hfixP4 hr hr2 hxord
  refine ⟨y, hyC, hyord, ?_⟩
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical ↥K) y =
      QuotientGroup.mk' (CFSG.solvableRadical ↥K) x := by
    exact QuotientGroup.eq_iff_div_mem.mpr
      (CFSG.pCore_le_solvableRadical 2 ↥K (QuotientGroup.eq_iff_div_mem.mp hyimage))
  change (QuotientGroup.mk' (Subgroup.center (BarInf K)))
    (QuotientGroup.mk' (CFSG.solvableRadical ↥K) y) =
    (QuotientGroup.mk' (Subgroup.center (BarInf K)))
      (QuotientGroup.mk' (CFSG.solvableRadical ↥K) x)
  rw [hmk]

theorem exists_mem_centralizer_of_quotInf_fixed {M K : Subgroup G} (hK : K ∈ calC M) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 K)))
    {xbar : BarInf K ⧸ Subgroup.center (BarInf K)} (hxord : orderOf xbar = r)
    (hfix : inducedQuotInfAut K b hb xbar = xbar) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧ orderOf (y : G) = r ∧
      piBarInf K y = xbar := by
  obtain ⟨x, hxord, hxbar⟩ := exists_mem_bar2_orderOf_of_quotInf hK hr hrZ hxord
  obtain ⟨y, hyC, hyord, hypi⟩ :=
    exists_mem_centralizer_of_bar2_orderOf hK hb hbodd hr hr2 hrZ hxord
      (by rw [hxbar]; exact hfix)
  exact ⟨y, hyC, hyord, hypi.trans hxbar⟩

private theorem conj_mem_pCoreOf_of_piBarInf_fixed {K : Subgroup G} {b : G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥)
    (hb : b ∈ Subgroup.normalizer (K : Set G)) {x : ↥K}
    (hfix : inducedQuotInfAut K b hb (piBarInf K x) = piBarInf K x) :
    b * (x : G) * b⁻¹ * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  classical
  let xc : ↥K :=
    ⟨b * (x : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb x).mp x.2⟩
  have h1 := congrArg (quotCenterEquivBar2 hq hc) hfix
  rw [quotCenterEquivBar2_inducedQuotInfAut_piBarInf, quotCenterEquivBar2_piBarInf] at h1
  rw [← QuotientGroup.mk'_apply (N := CFSG.pCore 2 ↥K) xc,
    ← QuotientGroup.mk'_apply (N := CFSG.pCore 2 ↥K) x] at h1
  have hquot : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) xc =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) x := h1
  have hmem : xc / x ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq_iff_div_mem.mp hquot
  have h2 : ((xc / x : ↥K) : G) ∈ CFSG.Open.pCoreOf 2 K :=
    Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  simpa [xc, Subgroup.coe_div, div_eq_mul_inv] using h2
private theorem exists_mul_mem_inf_centralizer_of_pCoreOf {K : Subgroup G} {b x : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hxK : x ∈ K) (hfix : b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    ∃ n ∈ CFSG.Open.pCoreOf 2 K,
      x * n ∈ K ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := CFSG.Open.pCoreOf 2 K
  let R : Subgroup G := Subgroup.zpowers b
  have hNX : N ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  haveI hchar : (CFSG.pCore 2 ↥K).Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic 2
  have hNnormal : (N.subgroupOf K).Normal := by
    rw [show N = CFSG.Open.pCoreOf 2 K from rfl, CFSG.openPCoreOf_subgroupOf]
    infer_instance
  have hRnorm : R ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.zpowers_le]
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 ↥K)) hb
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  haveI : Group.IsNilpotent ↥N := hN2.isNilpotent
  have hsolv : Group.IsSolvable ↥N := inferInstance
  have hcop : Nat.Coprime (Nat.card N) (Nat.card R) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk, Nat.card_zpowers]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hbodd)
  have hxR : ∀ r ∈ R, ⁅x, r⁆ ∈ N := by
    refine commutator_zpowers_mem_of_conj_mem (N := N) ?_ ?_
    · exact hRnorm (Subgroup.mem_zpowers b)
    · simpa [N] using hfix
  obtain ⟨n, hnN, hyinf⟩ :=
    CFSG.GroupTheory.exists_mul_mem_inf_centralizer_of_commutator_mem
      (X := K) (N := N) (R := R) hNX hNnormal hRnorm hsolv hcop hxK hxR
  exact ⟨n, hnN, by simpa [R] using hyinf⟩

private theorem exists_mem_centralizer_of_pCoreOf {K : Subgroup G} {b x : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hxK : x ∈ K) (hfix : b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) y =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hxK⟩ : ↥K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := CFSG.Open.pCoreOf 2 K
  have hNX : N ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  obtain ⟨n, hnN, hyinf⟩ := exists_mul_mem_inf_centralizer_of_pCoreOf hb hbodd hxK hfix
  have hncore : (⟨n, hNX hnN⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) ⟨n, hNX hnN⟩).mp (by simpa [N] using hnN)
  let y : ↥K := ⟨x * n, (Subgroup.mem_inf.mp hyinf).1⟩
  refine ⟨y, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyinf).2) b
      (Subgroup.mem_zpowers b)).symm
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    have hconj : (⟨x, hxK⟩ : ↥K) * ⟨n, hNX hnN⟩ * (⟨x, hxK⟩ : ↥K)⁻¹ ∈
        CFSG.pCore 2 ↥K :=
      (CFSG.pCore_normal (G := ↥K)).conj_mem _ hncore _
    convert hconj using 1
    ext
    simp [y, div_eq_mul_inv, mul_assoc]

private theorem exists_mem_centralizer_of_piBarInf_fixed {K : Subgroup G} {b : G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥)
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b)) {x : ↥K}
    (hfix : inducedQuotInfAut K b hb (piBarInf K x) = piBarInf K x) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧
      piBarInf K y = piBarInf K x := by
  obtain ⟨y, hyC, hyimage⟩ :=
    exists_mem_centralizer_of_pCoreOf hb hbodd x.2
      (conj_mem_pCoreOf_of_piBarInf_fixed hq hc hb hfix)
  refine ⟨y, hyC, ?_⟩
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical ↥K) y =
      QuotientGroup.mk' (CFSG.solvableRadical ↥K) x := by
    exact QuotientGroup.eq_iff_div_mem.mpr
      (CFSG.pCore_le_solvableRadical 2 ↥K (QuotientGroup.eq_iff_div_mem.mp hyimage))
  change (QuotientGroup.mk' (Subgroup.center (BarInf K)))
    (QuotientGroup.mk' (CFSG.solvableRadical ↥K) y) =
    (QuotientGroup.mk' (Subgroup.center (BarInf K)))
      (QuotientGroup.mk' (CFSG.solvableRadical ↥K) x)
  rw [hmk]

private noncomputable def sylowPreimage (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K))) : Subgroup ↥K :=
  (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))).comap (piBarInf K) ⊓
    (Subgroup.centralizer ({b} : Set G)).comap K.subtype

private noncomputable def sylowPreimageMap (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K))) :
    ↥(sylowPreimage K b P) →* ↥(P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) :=
  ((piBarInf K).comp (sylowPreimage K b P).subtype).codRestrict
    (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) (fun y => y.2.1)

private theorem map_sylowPreimage (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hc : Subgroup.center (Bar2 K) = ⊥)
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hfix : ∀ x ∈ (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))),
      inducedQuotInfAut K b hb x = x) :
    (sylowPreimage K b P).map (piBarInf K) =
      (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hy.1
  · intro x hx
    obtain ⟨y, rfl⟩ := piBarInf_surjective K x
    obtain ⟨y', hy'C, hy'pi⟩ :=
      exists_mem_centralizer_of_piBarInf_fixed hq hc hb hbodd (hfix _ hx)
    refine ⟨y', ?_, hy'pi⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap, hy'pi]
      exact hx
    · rw [Subgroup.mem_comap]
      exact hy'C

private theorem surjective_sylowPreimageMap (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hc : Subgroup.center (Bar2 K) = ⊥)
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hfix : ∀ x ∈ (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))),
      inducedQuotInfAut K b hb x = x) :
    Function.Surjective (sylowPreimageMap K b P) := by
  intro p
  have hp : (p : BarInf K ⧸ Subgroup.center (BarInf K)) ∈
      (sylowPreimage K b P).map (piBarInf K) := by
    rw [map_sylowPreimage K b P hq hc hb hbodd hfix]
    exact p.2
  obtain ⟨y, hy, hyp⟩ := hp
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change piBarInf K y = (p : BarInf K ⧸ Subgroup.center (BarInf K))
  exact hyp


private theorem isPGroup_two_ker_sylowPreimageMap (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hc : Subgroup.center (Bar2 K) = ⊥) :
    IsPGroup 2 (sylowPreimageMap K b P).ker := by
  classical
  have hO : CFSG.solvableRadical ↥K = CFSG.pCore 2 ↥K :=
    solvableRadical_eq_pCore_of_center_bar2_eq_bot hq hc
  let g : (sylowPreimageMap K b P).ker →* ↥(CFSG.pCore 2 ↥K) :=
    { toFun := fun y =>
        ⟨(y.1.1 : ↥K), by
          have hy1 : sylowPreimageMap K b P y = 1 := y.2
          have hpi : piBarInf K y.1.1 = 1 := by
            have h := congrArg
              (fun z : ↥(P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) =>
                (z : BarInf K ⧸ Subgroup.center (BarInf K))) hy1
            have hcoe : ((sylowPreimageMap K b P y :
                ↥(P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K)))) :
                BarInf K ⧸ Subgroup.center (BarInf K)) = piBarInf K y.1.1 := rfl
            rw [hcoe] at h
            simpa using h
          have hker : y.1.1 ∈ (piBarInf K).ker := MonoidHom.mem_ker.mpr hpi
          rw [piBarInf_ker hq] at hker
          exact hO ▸ hker⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => (z : ↥K)) hab
  exact IsPGroup.of_injective (p := 2) CFSG.pCore_isPGroup g hg

private theorem exists_isPGroup_le_sylowPreimage (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hc : Subgroup.center (Bar2 K) = ⊥)
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hfix : ∀ x ∈ (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))),
      inducedQuotInfAut K b hb x = x) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ Q : Subgroup ↥(sylowPreimage K b P), IsPGroup r Q ∧
      Q.map (sylowPreimageMap K b P) = ⊤ ∧
      Nat.card Q = Nat.card (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsPGroup r ↥(P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) :=
    P.isPGroup'
  have hf := surjective_sylowPreimageMap K b P hq hc hb hbodd hfix
  have hker2 := isPGroup_two_ker_sylowPreimageMap K b P hq hc
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup (sylowPreimageMap K b P) hf hker2 hr hr2
      (⊤ : Subgroup ↥(P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))))
      ((P.isPGroup').to_subgroup ⊤)
  have hcard := CFSG.card_map_eq_card_of_inf_ker_eq_bot
    (sylowPreimageMap K b P) (J := Q) (disjoint_iff.mp hQdisj)
  rw [hQmap] at hcard
  exact ⟨Q, hQp, hQmap, by simpa using hcard.symm⟩

private theorem exists_sylow_le_of_isPGroup_le_sylowPreimage (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hc : Subgroup.center (Bar2 K) = ⊥)
    {Q : Subgroup ↥(sylowPreimage K b P)} (hQ : IsPGroup r Q)
    (hcardQ : Nat.card Q =
      Nat.card (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))))
    (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ S : Sylow r ↥K, (S : Subgroup ↥K) ≤ sylowPreimage K b P := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hQ'p : IsPGroup r (Q.map (sylowPreimage K b P).subtype) := hQ.map _
  have hcardQ' : Nat.card (Q.map (sylowPreimage K b P).subtype) =
      Nat.card (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) := by
    rw [Subgroup.card_map_of_injective (sylowPreimage K b P).subtype_injective, hcardQ]
  obtain ⟨QK⟩ : Nonempty (Sylow r ↥K) := inferInstance
  have hdisjKer : (QK : Subgroup ↥K) ⊓ (piBarInf K).ker = ⊥ := by
    rw [piBarInf_ker hq, solvableRadical_eq_pCore_of_center_bar2_eq_bot hq hc]
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨a, ha⟩ := QK.isPGroup'.exists_card_eq
    obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
    rw [ha, hc]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
  have hcardMapQK : Nat.card ((QK : Subgroup ↥K).map (piBarInf K)) = Nat.card QK :=
    CFSG.card_map_eq_card_of_inf_ker_eq_bot (piBarInf K) hdisjKer
  obtain ⟨P₁, hP₁⟩ := (QK.isPGroup'.map (piBarInf K)).exists_le_sylow
  have hcardP₁ : Nat.card P₁ = Nat.card P := Nat.card_congr (Sylow.equiv P₁ P).toEquiv
  have hle1 : Nat.card QK ≤ Nat.card P := by
    rw [← hcardMapQK, ← hcardP₁]
    exact Subgroup.card_le_of_le hP₁
  obtain ⟨R, hR⟩ := hQ'p.exists_le_sylow
  have hcardR : Nat.card R = Nat.card QK := Nat.card_congr (Sylow.equiv R QK).toEquiv
  have hle2 : Nat.card (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) ≤
      Nat.card QK := by
    rw [← hcardQ', ← hcardR]
    exact Subgroup.card_le_of_le hR
  have hcardP_eq : Nat.card (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))) =
      Nat.card QK := le_antisymm hle2 hle1
  refine ⟨Sylow.ofCard (Q.map (sylowPreimage K b P).subtype)
    (hcardQ'.trans (hcardP_eq.trans (Sylow.card_eq_multiplicity QK))), ?_⟩
  rw [Sylow.coe_ofCard]
  calc Q.map (sylowPreimage K b P).subtype ≤
      (⊤ : Subgroup ↥(sylowPreimage K b P)).map (sylowPreimage K b P).subtype :=
      Subgroup.map_mono le_top
    _ = sylowPreimage K b P := by rw [Subgroup.map_top, Subgroup.range_subtype]





private theorem exists_sylow_le_sylowPreimage (K : Subgroup G) (b : G) {r : ℕ}
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hc : Subgroup.center (Bar2 K) = ⊥)
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hfix : ∀ x ∈ (P : Subgroup (BarInf K ⧸ Subgroup.center (BarInf K))),
      inducedQuotInfAut K b hb x = x) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ S : Sylow r ↥K, (S : Subgroup ↥K) ≤ sylowPreimage K b P := by
  obtain ⟨Q, hQ, -, hcardQ⟩ :=
    exists_isPGroup_le_sylowPreimage K b P hq hc hb hbodd hfix hr hr2
  exact exists_sylow_le_of_isPGroup_le_sylowPreimage K b P hq hc hQ hcardQ hr hr2

theorem exists_conj_le_centralizer_of_sylow_fixed {M K : Subgroup G} (hK : K ∈ calC M)
    (hc : Subgroup.center (Bar2 K) = ⊥) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (P : Sylow r (BarInf K ⧸ Subgroup.center (BarInf K)))
    (hfix : ∀ x ∈ (P : Subgroup _), inducedQuotInfAut K b hb x = x)
    {X : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup r X) :
    ∃ k ∈ K, X.map (MulAut.conj k).toMonoidHom ≤ Subgroup.centralizer ({b} : Set G) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  obtain ⟨S', hS'Y⟩ :=
    exists_sylow_le_sylowPreimage K b P hq hc hb hbodd hfix hr hr2
  have hW : IsPGroup r (X.subgroupOf K) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  obtain ⟨c, -, hcS⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (H := ↥K) (K := ⊤) S' le_top (X.subgroupOf K) le_top hW
  refine ⟨(c : ↥K), c.2, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxK : x ∈ K := hXK hx
  have hmem : (MulAut.conj c (⟨x, hxK⟩ : ↥K)) ∈
      (X.subgroupOf K).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map_of_mem (K := X.subgroupOf K) (x := (⟨x, hxK⟩ : ↥K))
      (MulAut.conj c).toMonoidHom (Subgroup.mem_subgroupOf.mpr hx)
  have hSY : MulAut.conj c (⟨x, hxK⟩ : ↥K) ∈ sylowPreimage K b P := hS'Y (hcS hmem)
  have hcent : (((MulAut.conj c) (⟨x, hxK⟩ : ↥K) : ↥K) : G) ∈
      Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hSY).2
  simpa [MulAut.conj_apply] using hcent

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
