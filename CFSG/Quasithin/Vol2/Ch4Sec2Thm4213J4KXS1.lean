module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXE9
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXSN
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQT
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs
public import CFSG.Quasithin.Background.VolII31Three
public import CFSG.Quasithin.Background.GoldschmidtTDE68CovBase
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXE

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open CFSG.Quasithin

theorem step1_normalizer
    {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.evenRank G ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hBM : CFSG.Quasithin.H13.Ch4.InspBM22Cover)
    (hsimp : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {KX : Subgroup G} (hKX : CFSG.IsQuasisimple ↥KX)
    (hKXz : Nat.card ↥(Subgroup.center ↥KX) = 6)
    (hKXM : CFSG.Quasithin.IsSporadic .M22 (↥KX ⧸ Subgroup.center ↥KX))
    (h36 : CFSG.QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    {x r v : G} (hx : orderOf x = 3)
    (hKXx : KX ≤ Subgroup.centralizer ({x} : Set G))
    (hKXr : KX ≤ Subgroup.centralizer ({r} : Set G))
    (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hxr : x ∈ Subgroup.centralizer ({r} : Set G))
    (hN : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({r} : Set G) ≤
      Subgroup.normalizer (KX : Set G))
    (hv1 : v ≠ 1) (hv2 : v * v = 1)
    (hKXv : KX ≤ Subgroup.centralizer ({v} : Set G))
    (hvx : v ∈ Subgroup.centralizer ({x} : Set G))
    (hrv : r ∈ Subgroup.centralizer ({v} : Set G)) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (KX : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)
    with hHdef
  have hrx : r ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hxr).symm
  have hrH : r ∈ H := ⟨hrx, hrv⟩
  have hKH : KX ≤ H := le_inf (fun k hk => (hKXx hk)) (hKXv)
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hC : Subgroup.centralizer ({x} : Set G) = ⊤ :=
      top_le_iff.mp (htop ▸ inf_le_left)
    have hxc : x ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by rw [hC]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · have hx1 : x = 1 := by
        have := hxc
        rw [hb, Subgroup.mem_bot] at this
        exact this
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    · obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have ha : a ∈ Subgroup.center G := by rw [ht]; exact Subgroup.mem_top a
      have hb' : b ∈ Subgroup.center G := by rw [ht]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb' a
  have hzex : ∃ zc : ↥(Subgroup.center ↥KX), orderOf zc = 2 := by
    apply exists_prime_orderOf_dvd_card' 2
    rw [hKXz]
    norm_num
  obtain ⟨zc, hzc⟩ := hzex
  set zK : ↥KX := (zc : ↥KX) with hzKdef
  set z : G := zK.1 with hzdef
  have hzKX : z ∈ KX := zK.2
  have hz2 : z * z = 1 := by
    have h2 : zc ^ 2 = 1 := by rw [← hzc]; exact pow_orderOf_eq_one zc
    have h := congrArg (fun y : ↥(Subgroup.center ↥KX) => (y : G)) h2
    simpa [pow_two, hzdef, hzKdef] using h
  have hz1 : z ≠ 1 := by
    intro h
    have hzc1 : zc = 1 := Subtype.ext (Subtype.ext (by simpa [hzdef, hzKdef] using h))
    rw [hzc1, orderOf_one] at hzc
    norm_num at hzc
  have hKXz' : KX ≤ Subgroup.centralizer ({z} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp zc.2 ⟨k, hk⟩))
  have hpz : CFSG.Open.pRank 3 KX ≤ 2 :=
    (pRank_mono 3 (by norm_num) hKXz').trans
      (pRank_le_two_centralizer hG hz2 hz1 Nat.prime_three (by norm_num))
  have hpge : 2 ≤ CFSG.Open.pRank 3 KX := by
    obtain ⟨E0, hE0, hE0c⟩ := exists_e9_of_isSporadic_M22 hKXM
    obtain ⟨E, hE, hEc⟩ := exists_e9_of_quotient (Subgroup.center ↥KX) E0 hE0 hE0c
    have hinj : Function.Injective KX.subtype := KX.subtype_injective
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hEG : IsElemAbelian 3 (E.map KX.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
        obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← hax, ← hby]
        exact congrArg Subtype.val (hEcomm a ha b hb)
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
        rw [← map_pow, hE.2 a ha, map_one]
    have hEGc : Nat.card (E.map KX.subtype) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective hinj, hEc]
      norm_num
    have hEGle : E.map KX.subtype ≤ KX := Subgroup.map_subtype_le E
    exact le_pRank_of_elemAbelian_card hEGle hEG hEGc
  have hpr : CFSG.Open.pRank 3 KX = 2 := le_antisymm hpz hpge
  have hKXeven : 2 ∣ Nat.card ↥KX := by
    have h6 : Nat.card ↥(Subgroup.center ↥KX) ∣ Nat.card ↥KX :=
      Subgroup.card_subgroup_dvd_card _
    rw [hKXz] at h6
    exact (by norm_num : 2 ∣ 6).trans h6
  have hodd : Odd (Nat.card (CFSG.oddCore ↥KX)) := CFSG.ABGTheoremB.odd_card_oddCore ↥KX
  have hKXnotodd : ¬ Odd (Nat.card ↥KX) := fun h => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hKXeven)
  have hoddne : CFSG.oddCore ↥KX ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top] at hodd
    exact hKXnotodd hodd
  have hoddle : CFSG.oddCore ↥KX ≤ Subgroup.center ↥KX := by
    rcases normal_le_center_or_top hKX (CFSG.oddCore ↥KX) with h | h
    · exact h
    · exact absurd h hoddne
  have hqKX : CFSG.IsQuasisimple (↥KX ⧸ CFSG.oddCore ↥KX) :=
    isQuasisimple_quot_of_le_center hKX (CFSG.oddCore ↥KX) hoddle
  set P : Subgroup G := Subgroup.zpowers r with hPdef
  set X : Subgroup G := H ⊓ Subgroup.centralizer (P : Set G) with hXdef
  have hPH : P ≤ H := by
    refine Subgroup.zpowers_le.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hrx)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hrv)
  have hKXX : KX ≤ X := by
    refine le_inf hKH ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hcomm : Commute r k := (Subgroup.mem_centralizer_singleton_iff.mp (hKXr hk)).symm
    exact (hcomm.zpow_left n).eq
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({r} : Set G) := by
    intro g hg
    refine ⟨hg.1.1, ?_⟩
    have hgr := Subgroup.mem_centralizer_iff.mp hg.2 r (Subgroup.mem_zpowers r)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hgr.symm
  have hKXnorm : (KX.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKXX]
    intro k g hk hg
    exact (Subgroup.mem_normalizer_iff.mp (hN (hXC hg)) k).mp hk
  have hLcomp : CFSG.QuasithinUnique.Id2519.IsTwoComponentIn KX X :=
    ⟨quasithinIsCComponent_of_normal hKX hKXX hKXnorm, hqKX⟩
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [hPdef, Nat.card_zpowers, hord, pow_one])
  have hSQT : CFSG.IsStronglyQuasithin ↥H := by
    intro p hp hp2
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (pRank_mono p hp.two_le (inf_le_right : H ≤ Subgroup.centralizer ({v} : Set G))).trans
      (pRank_le_two_centralizer hG hv2 hv1 hp hp2)
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥H := ⟨hSQT, isKGroupCat_of_proper hK hHtop⟩
  obtain ⟨K', hK'2, hKK', hK'n, -, hqK'⟩ :=
    CFSG.Quasithin.VolI.as_I_3_1_three_of h36 h38 G H P KX hsqtk hPH hP2 hLcomp hpr
  have hK'H : K' ≤ H := CFSG.Quasithin.le_of_mem_cComp hK'2.1
  have hK'ne : K' ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hK'H))
  have hKG' : CFSG.SectionRank.IsKGroupCat ↥K' := isKGroupCat_of_proper hK hK'ne
  have hK'C : K' ≤ Subgroup.centralizer ({r} : Set G) := by
    by_contra hnot
    set Y : Subgroup ↥H := K'.subgroupOf H with hYdef
    set r' : ↥H := ⟨r, hrH⟩ with hr'def
    have eY : ↥Y ≃* ↥K' := Subgroup.subgroupOfEquivOfLe hK'H
    have hYq : CFSG.IsQuasisimple ↥Y := CFSG.Quasithin.E6.Inn.isQuasisimple_of_mulEquiv eY.symm hqK'
    have hYqt : CFSG.Quasithin.IsQuasithin ↥Y :=
      isQuasithin_of_injective hG (H.subtype.comp Y.subtype)
        (H.subtype_injective.comp Y.subtype_injective)
    have hYkg : CFSG.SectionRank.IsKGroupCat ↥Y := CFSG.SectionRank.IsKGroupCat.of_mulEquiv hKG' eY
    have hYr2 : r' ^ 2 = 1 := Subtype.ext (by simp [hr'def, pow_two, hr2])
    have hYnot : ¬ Y ≤ Subgroup.centralizer ({r'} : Set ↥H) := by
      intro hY
      apply hnot
      intro k hk
      have hkY : (⟨k, hK'H hk⟩ : ↥H) ∈ Y := Subgroup.mem_subgroupOf.mpr hk
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hY hkY)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
    set C : Subgroup ↥H := KX.subgroupOf H with hCdef
    have hCYC : C ≤ Y ⊓ Subgroup.centralizer ({r'} : Set ↥H) := by
      intro c hc
      have hcG : (c : G) ∈ KX := Subgroup.mem_subgroupOf.mp hc
      refine ⟨Subgroup.mem_subgroupOf.mpr (hKK' hcG), ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
      have := Subgroup.mem_centralizer_singleton_iff.mp (hKXr hcG)
      simpa [hr'def] using this
    set X'' : Subgroup ↥H := Y ⊓ Subgroup.centralizer ({r'} : Set ↥H) with hX''def
    have hCX'' : C ≤ X'' := hCYC
    have hgG : ∀ g ∈ X'', (g : G) ∈ Subgroup.normalizer (KX : Set G) := by
      intro g hg
      have hgr : (g : G) * r = r * (g : G) := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
        simpa [hr'def] using congrArg Subtype.val this
      exact hN ⟨g.2.1, Subgroup.mem_centralizer_singleton_iff.mpr hgr⟩
    have hCnormal : (C.subgroupOf X'').Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCX'']
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro c
      have hgN := hgG g hg
      have key := Subgroup.mem_normalizer_iff.mp hgN (c : G)
      constructor
      · intro hc
        have hcG : (c : G) ∈ KX := Subgroup.mem_subgroupOf.mp hc
        have := (key.mp hcG)
        exact Subgroup.mem_subgroupOf.mpr (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this)
      · intro hc
        have hc' : ((g * c * g⁻¹ : ↥H) : G) ∈ KX := Subgroup.mem_subgroupOf.mp hc
        have := key.mpr (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hc')
        exact Subgroup.mem_subgroupOf.mpr this
    have hCsub : (C.subgroupOf X'').IsSubnormal := by
      have hnorm' : ((C.subgroupOf X'').subgroupOf ⊤).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
        exact (Subgroup.normalizer_eq_top_iff.mpr hCnormal).ge
      exact CFSG.Quasithin.A3.subnormal_top_iff.mp
        (IsSubnormal.step le_top hnorm' (IsSubnormal.refl ⊤))
    have hCqs : CFSG.IsQuasisimple ↥C :=
      CFSG.Quasithin.E6.Inn.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hKX
    have hcnot := hBM ↥H Y r' hK'n hYq hYqt hYkg hYr2 hYnot C hCYC hCsub hCqs
    have eC : ↥C ≃* ↥KX := Subgroup.subgroupOfEquivOfLe hKH
    have eQ : (↥C ⧸ Subgroup.center ↥C) ≃* (↥KX ⧸ Subgroup.center ↥KX) :=
      QuotientGroup.congr _ _ eC (Subgroup.map_center_eq eC)
    exact hcnot (CFSG.Quasithin.IsSporadic.of_mulEquiv eQ.symm hKXM)
  have hK'N : K' ≤ Subgroup.normalizer (KX : Set G) := fun k hk =>
    hN ⟨(hK'H hk).1, hK'C hk⟩
  have hnormKK' : (KX.subgroupOf K').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKK').mpr hK'N
  have hKeq : KX = K' := subgroup_eq_of_normal_quasisimple hqK' hKX hKK' hnormKK'
  rw [← hKeq] at hK'n
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hK'n

end CFSG.Quasithin.H13.Ch4.J4KX

end
