module

public import CFSG.Walter.Defs
public import CFSG.Walter.Bender1970.S1.Rank
public import CFSG.Walter.Bender1970.S1.GLTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.Open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {G : Type*} [Group G] [Finite G]

theorem generalizedFitting_le_qCoreOf_sup_pResidualOf (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    generalizedFittingSubgroupOf H ≤
      qCoreOf H p ⊔ pResidualOf (generalizedFittingSubgroupOf H) p := by
  set F := generalizedFittingSubgroupOf H
  set K := pResidualOf F p
  have hFitF : _root_.CFSG.fittingSubgroupOf H ≤ F := le_sup_left
  rw [show F = _root_.CFSG.fittingSubgroupOf H ⊔ componentLayerOf H from rfl]
  refine sup_le ?_ ?_
  · rw [show _root_.CFSG.fittingSubgroupOf H = CFSG.GorensteinWalter.fittingSubgroupOf H from rfl,
    fittingSubgroupOf_eq_iSup_qCoreOf H]
    refine iSup_le fun q => ?_
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      exact le_sup_left
    · refine le_sup_of_le_right fun x hx => ?_
      have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have : Fact q.1.1.Prime := ⟨hq⟩
      have hxF : x ∈ F := hFitF (qCoreOf_le_fittingSubgroupOf H q.1.1 hq hx)
      apply mem_pResidualOf_of_order_coprime F p hp hxF
      obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H q.1.1) ⟨x, hx⟩
      have hdvd : orderOf x ∣ q.1.1 ^ k := by
        have := orderOf_dvd_of_pow_eq_one hk
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hq).1 hdvd
      rw [hm]
      exact Nat.Coprime.pow_right m
        ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
  · exact le_sup_of_le_right (perfect_le_pResidualOf_local F (componentLayerOf H) p hp
      le_sup_right (componentLayerOf_isPerfect H))

@[expose] def pTorsionOfComm (p : ℕ) (A : Subgroup G) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Subgroup G where
  carrier := {x | x ∈ A ∧ ∃ n : ℕ, x ^ (p ^ n) = 1}
  mul_mem' := by
    rintro x y ⟨hx, m, hm⟩ ⟨hy, n, hn⟩
    refine ⟨A.mul_mem hx hy, m + n, ?_⟩
    rw [(Commute.mul_pow (hA x hx y hy) _), pow_add, pow_mul, hm, one_pow, mul_comm (p ^ m),
      pow_mul, hn, one_pow, one_mul]
  one_mem' := ⟨A.one_mem, 0, one_pow _⟩
  inv_mem' := by
    rintro x ⟨hx, n, hn⟩
    exact ⟨A.inv_mem hx, n, by rw [inv_pow, hn, inv_one]⟩

theorem le_qCoreOf_of_centralizes (H : Subgroup G) {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hPH : P ≤ H) (hP : IsPGroup p P)
    (hP₀ : P ≤ Subgroup.centralizer (qCoreOf H p : Set G))
    (hK : P ≤ Subgroup.centralizer (pResidualOf (generalizedFittingSubgroupOf H) p : Set G)) :
    P ≤ qCoreOf H p := by
  set F := generalizedFittingSubgroupOf H
  set Z := F ⊓ Subgroup.centralizer (F : Set G)
  have hPF : P ≤ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact (generalizedFitting_le_qCoreOf_sup_pResidualOf H hp).trans
      (sup_le (Subgroup.le_centralizer_iff.mp hP₀) (Subgroup.le_centralizer_iff.mp hK))
  have hPZ : P ≤ Z := fun x hx =>
    ⟨centralizer_intersection_fstar_le_fstar H ⟨hPF hx, hPH hx⟩, hPF hx⟩
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  set Zp := pTorsionOfComm p Z hZcomm
  have hFH : F ≤ H := generalizedFittingSubgroupOf_le H
  have hZpH : Zp ≤ H := fun x hx => hFH hx.1.1
  have hFn := generalizedFittingSubgroupOf_isNormalIn H
  have hZpn : IsNormalIn Zp H := by
    refine ⟨hZpH, fun h hh x hx => ?_⟩
    obtain ⟨⟨hxF, hxC⟩, n, hn⟩ := hx
    refine ⟨⟨hFn.2 h hh x hxF, ?_⟩, n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩
    show h * x * h⁻¹ ∈ Subgroup.centralizer (F : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : h⁻¹ * y * h ∈ F := by
      simpa using hFn.2 h⁻¹ (H.inv_mem hh) y hy
    have hc := Subgroup.mem_centralizer_iff.mp hxC _ hy'
    calc y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * y := by group
  have hZpp : IsPGroup p Zp := fun x => by
    obtain ⟨-, n, hn⟩ := x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hPZp : P ≤ Zp := fun x hx => by
    obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
    exact ⟨hPZ hx, n, by simpa using congrArg Subtype.val hn⟩
  exact hPZp.trans (le_qCoreOf_of_isNormalIn_pGroup H Zp p hp hZpH hZpn hZpp)

theorem le_qCoreOf_of_pPrime_central (H : Subgroup G) {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hMH : IsNormalIn M H)
    (hcent : ∀ y ∈ M, Nat.Coprime p (orderOf y) → ∀ m ∈ M, m * y = y * m)
    {P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup p P) : P ≤ qCoreOf H p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.center M
  have hsylow : ∀ (q : ℕ) [Fact q.Prime], q ≠ p → ∀ Q : Sylow q M, (Q : Subgroup M) ≤ C := by
    intro q hq hqp Q x hx
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hx⟩
    have hdvd : orderOf (x : G) ∣ q ^ k := by
      have := orderOf_dvd_of_pow_eq_one hk
      rw [Subgroup.orderOf_mk] at this
      rw [Subgroup.orderOf_coe]
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq.out).1 hdvd
    have hcop : Nat.Coprime p (orderOf (x : G)) := by
      rw [hj]
      exact Nat.Coprime.pow_right j ((Nat.coprime_primes hp hq.out).2 (Ne.symm hqp))
    exact Subtype.ext (hcent x x.2 hcop m m.2)
  have hidx : ∃ k : ℕ, C.index = p ^ k := by
    refine exists_pow_of_primeFactors_subset_singleton (Subgroup.index_ne_zero_of_finite) ?_
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have : Fact r.Prime := ⟨hrp⟩
    by_contra hrne
    obtain ⟨Q⟩ : Nonempty (Sylow r M) := inferInstance
    have hdvd : C.index ∣ (Q : Subgroup M).index := Subgroup.index_dvd_of_le (hsylow r hrne Q)
    exact Q.not_dvd_index ((Nat.dvd_of_mem_primeFactors hr).trans hdvd)
  have hquot : IsPGroup p (M ⧸ C) := by
    obtain ⟨k, hk⟩ := hidx
    exact IsPGroup.of_card (by rw [← Subgroup.index_eq_card, hk])
  have : Group.IsNilpotent (M ⧸ C) := hquot.isNilpotent
  have hnil : Group.IsNilpotent M :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' C) (by rw [QuotientGroup.ker_mk'])
  have hPsub : IsPGroup p (P.subgroupOf M) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  obtain ⟨S, hS⟩ := hPsub.exists_le_sylow
  have hSnorm : (S : Subgroup M).Normal := inferInstance
  have hSle : (S : Subgroup M) ≤ pCore p M := le_sSup ⟨hSnorm, S.isPGroup'⟩
  have hPq : P ≤ qCoreOf M p := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hPM hx⟩, hSle (hS hx), rfl⟩
  exact hPq.trans (qCoreOf_le_qCoreOf_of_isNormalIn M H p hMH)

theorem le_centralizer_twoCore_of_hasAbelianSylowTwo {H : Subgroup G}
    (hH : HasAbelianSylowTwo H) {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    P ≤ Subgroup.centralizer (qCoreOf H 2 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPsub : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨S, hS⟩ := hPsub.exists_le_sylow
  have hScomm := hH S
  have hcore : pCore 2 H ≤ (S : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2) (G := H)) S
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have hxS : (⟨x, hPH hx⟩ : H) ∈ (S : Subgroup H) := hS hx
  have hyS : y' ∈ (S : Subgroup H) := hcore hy'
  have h := congrArg (fun z : (S : Subgroup H) => ((z : H) : G))
    (hScomm.is_comm.comm ⟨y', hyS⟩ ⟨⟨x, hPH hx⟩, hxS⟩)
  exact h

theorem bender1970_1_4 {H : Subgroup G} (hH : HasAbelianSylowTwo H) {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup p P) (hrank : rank (qCoreOf H p) ≤ 2)
    (hcomm : ⁅P, pResidualOf (generalizedFittingSubgroupOf H) p⁆ = ⊥) :
    P ≤ qCoreOf H p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set F := generalizedFittingSubgroupOf H with hFdef
  set K := pResidualOf F p with hKdef
  set P₀ := qCoreOf H p with hP₀def
  have hPK : P ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  by_cases hp2 : p = 2
  · subst hp2
    exact le_qCoreOf_of_centralizes H hp hPH hP
      (le_centralizer_twoCore_of_hasAbelianSylowTwo hH hPH hP) hPK
  by_cases hP₀ : P₀ = ⊥
  · refine le_qCoreOf_of_centralizes H hp hPH hP ?_ hPK
    rw [← hP₀def, hP₀]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  have hP₀n : IsNormalIn P₀ H := qCoreOf_normal_in H p
  have hHP₀ : H ≤ Subgroup.normalizer (P₀ : Set G) := le_normalizer_of_isNormalIn hP₀n
  have hP₀p : IsPGroup p P₀ := qCoreOf_isPGroup H p
  have : Nontrivial P₀ := (Subgroup.nontrivial_iff_ne_bot P₀).mpr hP₀
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := supercritical_witness hp2 hP₀p
  have hDp : IsPGroup p D := hP₀p.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hexpD : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hDexp x x.2)
  have hrankD : pRank p (⊤ : Subgroup D) ≤ 2 := by
    let ι : D →* G := P₀.subtype.comp D.subtype
    have hι : Function.Injective ι := P₀.subtype_injective.comp D.subtype_injective
    have hle : (⊤ : Subgroup D).map ι ≤ P₀ := by
      rintro _ ⟨x, -, rfl⟩
      exact (x : P₀).2
    calc pRank p (⊤ : Subgroup D) ≤ pRank p ((⊤ : Subgroup D).map ι) :=
          pRank_le_map hp.one_lt ι hι ⊤
      _ ≤ pRank p P₀ := pRank_mono hp.one_lt hle
      _ = rank P₀ := (rank_eq_pRank_of_isPGroup hp hP₀p).symm
      _ ≤ 2 := hrank
  have hWcard : Nat.card (D ⧸ frattini D) ≤ p ^ 2 :=
    (rank_two_exponent_prime_order_bound hDp hexpD hrankD).2
  let _ : MulDistribMulAction H P₀ := Subgroup.conjMulDistribMulActionOfLeNormalizer H P₀ hHP₀
  let ρ₀ : H →* MulAut P₀ := MulDistribMulAction.toMulAut H P₀
  have hρ₀ : ∀ (h : H) (x : P₀), ((ρ₀ h x : P₀) : G) = (h : G) * x * (h : G)⁻¹ :=
    fun _ _ => rfl
  let ρ : H →* MulAut (D ⧸ frattini D) := (frattiniAction D).comp ρ₀
  set Y := H ⊓ Subgroup.centralizer (K : Set G) with hYdef
  set Ysub : Subgroup H := Y.subgroupOf H with hYsubdef
  let ρY : Ysub →* MulAut (D ⧸ frattini D) := ρ.comp Ysub.subtype
  set X := ρY.range with hXdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : BenderSuzuki.HasAbelianSylow 2 X :=
    ((show BenderSuzuki.HasAbelianSylow 2 H from hH).subgroup Ysub).mapSurjective
      ρY.rangeRestrict ρY.rangeRestrict_surjective
  have hρX : ∀ h : H, h ∈ Ysub → ρ h ∈ X := fun h hh => ⟨⟨h, hh⟩, rfl⟩
  let Mx : Subgroup H :=
    { carrier := {h | h ∈ Ysub ∧ IsPElement p (ρ h)}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨Ysub.mul_mem ha hb, ?_⟩
        rw [map_mul]
        exact isPElement_mul_of_le_mulAut hp2 hWcomm hWpow hWcard hX (hρX a ha) (hρX b hb)
          hap hbp
      one_mem' := ⟨Ysub.one_mem, 0, by rw [map_one, orderOf_one, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, n, hn⟩
        exact ⟨Ysub.inv_mem ha, n, by rw [map_inv, orderOf_inv, hn]⟩ }
  set M := Mx.map H.subtype with hMdef
  have hMY : ∀ m ∈ M, m ∈ Y := by
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hm.1
  have hKn : IsNormalIn K H := pResidualOf_generalizedFitting_isNormalIn H p
  have hYconj : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y := by
    intro h hh y hy
    refine ⟨H.mul_mem (H.mul_mem hh hy.1) (H.inv_mem hh), ?_⟩
    show h * y * h⁻¹ ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : h⁻¹ * k * h ∈ K := by
      simpa using hKn.2 h⁻¹ (H.inv_mem hh) k hk
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 _ hk'
    calc k * (h * y * h⁻¹) = h * ((h⁻¹ * k * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * k * h)) * h⁻¹ := by rw [hc]
      _ = h * y * h⁻¹ * k := by group
  have hMH : IsNormalIn M H := by
    refine ⟨Subgroup.map_subtype_le Mx, ?_⟩
    rintro h hh _ ⟨m, ⟨hmY, hmp⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.mpr (hYconj h hh m (Subgroup.mem_subgroupOf.mp hmY))
    · obtain ⟨n, hn⟩ := hmp
      refine ⟨n, ?_⟩
      have hconj : ρ (⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹) = MulAut.conj (ρ ⟨h, hh⟩) (ρ m) := by
        rw [map_mul, map_mul, map_inv, MulAut.conj_apply]
      rw [hconj, MulEquiv.orderOf_eq, hn]
  have hPM : P ≤ M := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hPH hx⟩, ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨hPH hx, hPK hx⟩
    · obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
      have hdvd : orderOf (ρ ⟨x, hPH hx⟩) ∣ p ^ n := by
        refine (orderOf_map_dvd ρ _).trans ?_
        rw [Subgroup.orderOf_mk]
        have := orderOf_dvd_of_pow_eq_one hn
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      exact ⟨m, hm⟩
  have hcent : ∀ y ∈ M, Nat.Coprime p (orderOf y) → ∀ m ∈ M, m * y = y * m := by
    rintro _ ⟨y, ⟨hyY, hyp⟩, rfl⟩ hcop m hm
    have hcop' : Nat.Coprime p (orderOf y) := by
      rwa [orderOf_injective H.subtype H.subtype_injective y] at hcop
    have hρy : ρ y = 1 := by
      obtain ⟨j, hj⟩ := hyp
      have hdvd : orderOf (ρ y) ∣ orderOf y := orderOf_map_dvd ρ y
      rw [hj] at hdvd
      have hj0 : j = 0 := by
        by_contra hj0
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop' ((dvd_pow_self p hj0).trans hdvd))
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    have hρ₀y : ρ₀ y = 1 := by
      have hmem : ρ₀ y ∈ (frattiniAction D).ker := hρy
      obtain ⟨i, hi⟩ := hker ⟨ρ₀ y, hmem⟩
      have hdvd1 : orderOf (ρ₀ y) ∣ p ^ i := by
        have := orderOf_dvd_of_pow_eq_one hi
        rwa [Subgroup.orderOf_mk] at this
      have hdvd2 : orderOf (ρ₀ y) ∣ orderOf y := orderOf_map_dvd ρ₀ y
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd1
      have hk0 : k = 0 := by
        by_contra hk0
        rw [hk] at hdvd2
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop' ((dvd_pow_self p hk0).trans hdvd2))
      rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    have hyP₀ : (y : G) ∈ Subgroup.centralizer (P₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun α : MulAut P₀ => ((α ⟨x, hx⟩ : P₀) : G)) hρ₀y
      simp only [hρ₀, MulAut.one_apply] at h
      calc x * (y : G) = (y : G) * x * (y : G)⁻¹ * y := by rw [h]
        _ = (y : G) * x := by group
    have hyK : (y : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_subgroupOf.mp hyY).2
    have hyF : (y : G) ∈ Subgroup.centralizer (F : Set G) := by
      have hle : (Subgroup.zpowers (y : G)) ≤ Subgroup.centralizer (F : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        refine (generalizedFitting_le_qCoreOf_sup_pResidualOf H hp).trans (sup_le ?_ ?_)
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hyP₀
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hyK
      exact hle (Subgroup.mem_zpowers _)
    have hyFF : (y : G) ∈ F := centralizer_intersection_fstar_le_fstar H ⟨hyF, y.2⟩
    have hyKK : (y : G) ∈ K := by
      apply mem_pResidualOf_of_order_coprime F p hp hyFF
      rw [Subgroup.orderOf_coe]
      exact hcop'
    exact (Subgroup.mem_centralizer_iff.mp (hMY m hm).2 _ hyKK).symm
  exact le_qCoreOf_of_pPrime_central H hp hMH hcent hPM hP

theorem bender1970_1_4_top (hG : HasAbelianSylowTwo G) {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p P) (hrank : rank (qCoreOf (⊤ : Subgroup G) p) ≤ 2)
    (hcomm : ⁅P, pResidualOf (generalizedFittingSubgroupOf (⊤ : Subgroup G)) p⁆ = ⊥) :
    P ≤ qCoreOf (⊤ : Subgroup G) p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : HasAbelianSylowTwo (⊤ : Subgroup G) :=
    (show BenderSuzuki.HasAbelianSylow 2 G from hG).subgroup ⊤
  exact bender1970_1_4 hH hp le_top hP hrank hcomm

end CFSG.Walter
