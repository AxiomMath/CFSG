module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaBasic
public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.CharacterTheory.Wreathed.OddNormalQuotientInvolutions

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem cor2Beta_wclSet_lift {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N))
    {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1) {y' : G ⧸ N}
    (hy' : y' ∈ CFSG.LargeExtraspecial.S11.wclSet (QuotientGroup.mk' N t)) :
    ∃ y ∈ CFSG.LargeExtraspecial.S11.wclSet t, QuotientGroup.mk' N y = y' := by
  obtain ⟨m', hm', hcomm⟩ := hy'
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective m'
  have ht : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  set u : G := m * t * m⁻¹ with hu
  have hu2 : orderOf u = 2 := by
    rw [hu]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj m) t).trans ht
  have hmku : QuotientGroup.mk' N u = y' := by
    rw [hm']
    simp [hu]
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have hoddker : Odd (Nat.card (QuotientGroup.mk' N).ker) := by rw [hker]; exact hN
  have hy2 : orderOf y' = 2 := by
    rw [← hmku]
    exact CFSG.Wreathed.OddNormalQuotientInvolutions.quotient_involution N hN u hu2
  obtain ⟨lift, hlift, hcom⟩ :=
    CFSG.OrderReductions.OddKernelInvolutions.exists_commuting_involution_lift
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hoddker ⟨t, ht⟩ ⟨y', hy2⟩
      (by
        show Commute (QuotientGroup.mk' N t) y'
        exact (show y' * QuotientGroup.mk' N t = QuotientGroup.mk' N t * y' from hcomm).symm)
  obtain ⟨r, hr⟩ :=
    CFSG.Wreathed.OddNormalQuotientInvolutions.exists_kernel_conjugator N hN u lift.val hu2
      lift.property (by rw [hlift, hmku])
  refine ⟨lift.val, ⟨(r : G) * m, ?_, hcom.symm.eq⟩, hlift⟩
  rw [← hr, hu]
  group

theorem cor2Beta_commute_of_wclSet {u v : G} (hu2 : u * u = 1)
    (hab : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl u))
    (hv : v ∈ CFSG.LargeExtraspecial.S11.wclSet u) {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) {n : G} (hn : n ∈ N) (hnu : n * u = u * n) : n * v = v * n := by
  obtain ⟨m, hvm, hvu⟩ := hv
  have hv2 : v * v = 1 := by
    rw [hvm]
    calc m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hnu' : n⁻¹ * u = u * n⁻¹ := (Commute.inv_left (show Commute n u from hnu)).eq
  have hw : n⁻¹ * v * n ∈ CFSG.LargeExtraspecial.S11.wclSet u := by
    refine ⟨n⁻¹ * m, by rw [hvm]; group, ?_⟩
    calc n⁻¹ * v * n * u = n⁻¹ * v * (n * u) := by group
      _ = n⁻¹ * v * (u * n) := by rw [hnu]
      _ = n⁻¹ * (v * u) * n := by group
      _ = n⁻¹ * (u * v) * n := by rw [hvu]
      _ = (n⁻¹ * u) * v * n := by group
      _ = (u * n⁻¹) * v * n := by rw [hnu']
      _ = u * (n⁻¹ * v * n) := by group
  have hvW : v ∈ CFSG.LargeExtraspecial.S11.wcl u :=
    CFSG.LargeExtraspecial.S11.subset_wcl u ⟨m, hvm, hvu⟩
  have hwW : n⁻¹ * v * n ∈ CFSG.LargeExtraspecial.S11.wcl u :=
    CFSG.LargeExtraspecial.S11.subset_wcl u hw
  have hcomm : (n⁻¹ * v * n) * v = v * (n⁻¹ * v * n) :=
    congrArg Subtype.val (hab.is_comm.comm ⟨_, hwW⟩ ⟨_, hvW⟩)
  set c : G := v * n⁻¹ * v⁻¹ * n with hcdef
  have hcN : c ∈ N := by
    have h1 : v * n⁻¹ * v⁻¹ ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) v
    exact N.mul_mem h1 hn
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hc1 : c = v * (n⁻¹ * v * n) := by
    rw [hcdef, hvinv]; group
  have hc2 : c⁻¹ = (n⁻¹ * v * n) * v := by
    calc c⁻¹ = n⁻¹ * v * n * v⁻¹ := by rw [hcdef]; group
      _ = (n⁻¹ * v * n) * v := by rw [hvinv]
  have hcc : c * c = 1 := by
    calc c * c = c * c⁻¹⁻¹ := by rw [inv_inv]
      _ = c * ((n⁻¹ * v * n) * v)⁻¹ := by rw [hc2]
      _ = c * (v * (n⁻¹ * v * n))⁻¹ := by rw [hcomm]
      _ = c * c⁻¹ := by rw [← hc1]
      _ = 1 := mul_inv_cancel c
  have hc : c = 1 := cor2Beta_eq_one_of_odd hN hcN hcc
  have : n⁻¹ * v * n = v := by
    have h1 : v * (n⁻¹ * v * n) = 1 := by rw [← hc1]; exact hc
    calc n⁻¹ * v * n = v⁻¹ * (v * (n⁻¹ * v * n)) := by group
      _ = v⁻¹ := by rw [h1]; group
      _ = v := hvinv
  calc n * v = n * (n⁻¹ * v * n) := by rw [this]
    _ = v * n := by group

theorem cor2Beta_wcl_abelian_conj {t : G}
    (hab : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl t)) (m : G) :
    IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl (m * t * m⁻¹)) := by
  have key : ∀ x ∈ CFSG.LargeExtraspecial.S11.wcl (m * t * m⁻¹),
      m⁻¹ * x * m ∈ CFSG.LargeExtraspecial.S11.wcl t := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, hc⟩ := hx
      refine CFSG.LargeExtraspecial.S11.subset_wcl t ⟨m⁻¹ * k * m, ?_, ?_⟩
      · rw [hk]; group
      · calc m⁻¹ * x * m * t = m⁻¹ * (x * (m * t * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * t * m⁻¹) * x) * m := by rw [hc]
          _ = t * (m⁻¹ * x * m) := by group
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      have e : m⁻¹ * (x * y) * m = (m⁻¹ * x * m) * (m⁻¹ * y * m) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : m⁻¹ * x⁻¹ * m = (m⁻¹ * x * m)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := congrArg Subtype.val
    (hab.is_comm.comm ⟨_, key a.1 a.2⟩ ⟨_, key b.1 b.2⟩)
  simp only [Subgroup.coe_mul] at h ⊢
  calc (a : G) * b = m * (m⁻¹ * a * m * (m⁻¹ * b * m)) * m⁻¹ := by group
    _ = m * (m⁻¹ * b * m * (m⁻¹ * a * m)) * m⁻¹ := by rw [h]
    _ = (b : G) * a := by group

theorem cor2Beta_commute_mul_wclSet {S : Sylow 2 G} {t : G} (hs : ShultSetup S t)
    {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) {y : G}
    (hy : y ∈ CFSG.LargeExtraspecial.S11.wclSet t) : ∀ n ∈ N, (t * y) * n = n * (t * y) := by
  by_cases hyt : y = t
  · intro n hn
    subst hyt
    rw [hs.sq, one_mul, mul_one]
  obtain ⟨m, hym, hyc⟩ := hy
  have hy2 : y * y = 1 := by
    rw [hym]
    calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
      _ = 1 := by rw [hs.sq]; group
  have hab_y : IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl y) := by
    rw [hym]
    exact cor2Beta_wcl_abelian_conj hs.abelian m
  have ht_in : t ∈ CFSG.LargeExtraspecial.S11.wclSet y :=
    ⟨m⁻¹, by rw [hym]; group, hyc.symm⟩
  have h1 : ∀ n ∈ N, n * t = t * n → n * y = y * n := fun n hn hnt =>
    cor2Beta_commute_of_wclSet hs.sq hs.abelian ⟨m, hym, hyc⟩ hN hn hnt
  have h2 : ∀ n ∈ N, n * y = y * n → n * t = t * n := fun n hn hny =>
    cor2Beta_commute_of_wclSet hy2 hab_y ht_in hN hn hny
  have hNn : ∀ g : G, g ∈ normalizer (N : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    trivial
  have hle : N ≤ Subgroup.centralizer ({t * y} : Set G) := by
    refine CFSG.Holt.StarLemma26.le_of_forall_commute_mem hN hs.sq hy2 hyc.symm (hNn t) (hNn y)
      ?_
    intro w hw n hn hwn
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hw with rfl | rfl | rfl
    · have hny := h1 n hn hwn.symm
      calc n * (w * y) = (n * w) * y := by group
        _ = (w * n) * y := by rw [hwn.symm]
        _ = w * (n * y) := by group
        _ = w * (y * n) := by rw [hny]
        _ = (w * y) * n := by group
    · have hnt := h2 n hn hwn.symm
      calc n * (t * w) = (n * t) * w := by group
        _ = (t * n) * w := by rw [hnt]
        _ = t * (n * w) := by group
        _ = t * (w * n) := by rw [← hwn]
        _ = (t * w) * n := by group
    · exact hwn.symm
  intro n hn
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hn)
  exact this.symm

end CFSG.RankThree.GF2n.Tim77
