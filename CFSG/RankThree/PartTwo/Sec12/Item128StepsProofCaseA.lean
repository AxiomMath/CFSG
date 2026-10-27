module

public import CFSG.RankThree.PartTwo.Sec12.Item125TC
public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSLEnd
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagBasic

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item128StepsProof

open Item125BarTC

variable {G : Type} [Group G] [Finite G]

theorem mk_pow_three_mem_center {L : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (L : Set G)) (he3 : e ^ 3 = 1)
    {xb : L ⧸ aschbacherSolvableCore 3 L} (h : thetaBarAct L ⟨e, heN⟩ = MulAut.conj xb) :
    xb ^ 3 ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
  have h1 : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using he3)
  have h2 := congrArg (thetaBarAct L) h1
  rw [map_pow, map_one, h, ← map_pow] at h2
  exact mem_center_of_conj_eq_one h2

theorem mk_pow_three_eq_one_of_cube {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hcube : ∀ x : L ⧸ aschbacherSolvableCore 3 L,
      x ^ 3 ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) → x ^ 3 = 1)
    {e : G} (he : e ∈ lcBar c L) (he3 : e ^ 3 = 1) (l : G) (hl : l ∈ L) {z : G}
    (hz : z ∈ Sec4.thetaQuotCentralizer L) (hlz : e = l * z) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩ ^ 3 = 1 :=
  hcube _ (mk_pow_three_mem_center (lcBar_le_normalizer hL he) he3
    (thetaBarAct_eq_conj hl hz hlz (lcBar_le_normalizer hL he)))

theorem exists_decomp_of_mk_pow {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    {e : G} (he : e ∈ lcBar c L) (he3 : e ^ 3 = 1) {l₀ : G} (hl₀ : l₀ ∈ L) {z₀ : G}
    (hz₀ : z₀ ∈ Sec4.thetaQuotCentralizer L) (hlz : e = l₀ * z₀)
    (hxb3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l₀, hl₀⟩ ^ 3 = 1) :
    ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L, e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l := by
  have heN := lcBar_le_normalizer hL he
  have hφ := thetaBarAct_eq_conj hl₀ hz₀ hlz heN
  set xb := QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l₀, hl₀⟩ with hxb
  have hE'3 : IsPGroup 3 (Subgroup.zpowers e) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one he3) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hE'N : Subgroup.zpowers e ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr heN
  have hfix : ∀ d (hd : d ∈ Subgroup.zpowers e), thetaBarAct L ⟨d, hE'N hd⟩ xb = xb := by
    intro d hd
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have h1 : (⟨e ^ n, hE'N hd⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, heN⟩ ^ n :=
      Subtype.ext (by simp)
    rw [h1, map_zpow, hφ, ← map_zpow, MulAut.conj_apply,
      (Commute.zpow_left (Commute.refl xb) n).eq, mul_inv_cancel_right]
  obtain ⟨l, hlπ, hl3, hlc⟩ := exists_lift_pow_three hE'3 hE'N xb hxb3 hfix
  have hzN : (l : G)⁻¹ * e ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer l.2)) heN
  refine ⟨l, l.2, (l : G)⁻¹ * e, ?_, by group, hl3, ?_⟩
  · rw [mem_thetaQuotCentralizer_iff_thetaBarAct hzN]
    have h1 : (⟨(l : G)⁻¹ * e, hzN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨l, Subgroup.le_normalizer l.2⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨e, heN⟩ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_inv, thetaBarAct_of_mem l.2, hφ]
    have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨(l : G), l.2⟩ = xb := hlπ
    rw [h2, inv_mul_cancel]
  · have hle := hlc e (Subgroup.mem_zpowers e)
    calc (l : G) * ((l : G)⁻¹ * e) = (l : G)⁻¹ * (l * e) := by group
      _ = (l : G)⁻¹ * (e * l) := by rw [hle]
      _ = (l : G)⁻¹ * e * l := by group

theorem false_of_isE27_le_of {L F : Subgroup G}
    (hm3 : ∀ S : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsMulCommutative S →
      (∀ x ∈ S, x ^ 3 = 1) → Nat.card S ≤ 9)
    (hF : Late.IsE27 F) (hFL : F ≤ L) : False := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set F' : Subgroup L := F.subgroupOf L with hF'
  have hF'27 : Nat.card F' = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv).trans hF.2
  have hF'3 : IsPGroup 3 F' := IsPGroup.of_card (n := 3) (by rw [hF'27]; norm_num)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hF'3
  have hS27 : Nat.card (F'.map π) = 27 := by
    rw [← hF'27]
    change Nat.card (↑(F'.map π) : Set (L ⧸ aschbacherSolvableCore 3 L)) = Nat.card (F' : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  have hle := hm3 (F'.map π) ⟨⟨fun u v => by
      obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
      obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
      apply Subtype.ext
      change (u : L ⧸ aschbacherSolvableCore 3 L) * v = v * u
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      congr 1
      have h := hF.1.1.is_comm.comm (⟨u', Subgroup.mem_subgroupOf.mp hu'⟩ : F)
        ⟨v', Subgroup.mem_subgroupOf.mp hv'⟩
      exact Subtype.ext (congrArg Subtype.val h : (u' : G) * v' = v' * u')⟩⟩
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hF.1.2 _ (Subgroup.mem_subgroupOf.mp hu))
      rw [this, map_one])
  rw [hS27] at hle
  norm_num at hle

theorem false_of_card_inf_L_eq_nine_of {c : G} {L : Subgroup G}
    (hm3 : ∀ S : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsMulCommutative S →
      (∀ x ∈ S, x ^ 3 = 1) → Nat.card S ≤ 9)
    (hL : L ∈ thetaComponentsAt 3 c) (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    {E : Subgroup G} (hE : Late.IsE27 E) (hEL : E ≤ lcBar c L) (hcE : c ∈ E)
    (hx : ∀ e ∈ E, ∀ (l : G) (hl : l ∈ L), ∀ z ∈ Sec4.thetaQuotCentralizer L, e = l * z →
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩ ^ 3 = 1)
    (hB3 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3)
    (hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEL.trans (lcBar_le_normalizer hL)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpE c hcE) hc1
  set T := E ⊓ L with hTdef
  have hTe : CFSG.Assembly.IsElemAbelian 3 T :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hexpE x hx.1⟩
  have hcT : c ∈ T := ⟨hcE, hcL⟩
  obtain ⟨hTbe, hTb9, -⟩ :=
    Gap125NonCentralBar.thetaImage_facts hL hcL hc1 hZ hTe hEL9 inf_le_right hcT
  set Tb := (T.subgroupOf L).map π with hTbdef
  have hBc : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (show c ∈ E ⊓ _ from
      ⟨hcE, mem_thetaQuotCentralizer_of_central hcL hLc⟩))
      (by rw [hB3, Nat.card_zpowers, hc3])).symm
  obtain ⟨e, heE, heL⟩ : ∃ e ∈ E, e ∉ L := by
    by_contra hcon
    push Not at hcon
    have h1 : E ⊓ L = E := inf_eq_left.mpr hcon
    rw [hTdef, h1, hE.2] at hEL9
    norm_num at hEL9
  obtain ⟨l, hl, z, hz, hlz⟩ := exists_mul_of_mem_lcBar hL (hEL heE)
  set xb : L ⧸ N := π ⟨l, hl⟩ with hxb
  have hφe : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj xb :=
    thetaBarAct_eq_conj hl hz hlz (hEN heE)
  have hx3 : xb ^ 3 = 1 := hx e heE l hl z hz hlz
  have hxc : xb ∈ Subgroup.centralizer (Tb : Set (L ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have htE : (t : G) ∈ E := (Subgroup.mem_subgroupOf.mp ht).1
    have h1 : thetaBarAct L ⟨e, hEN heE⟩ (π t) = π t := by
      rw [thetaBarAct_mk]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, hcommE e heE _ htE, mul_inv_cancel_right]
    rw [hφe, MulAut.conj_apply] at h1
    calc π t * xb = (xb * π t * xb⁻¹) * xb := by rw [h1]
      _ = xb * π t := by group
  have hxT : xb ∉ Tb := by
    rintro ⟨t, ht, htx⟩
    have htE : (t : G) ∈ E := (Subgroup.mem_subgroupOf.mp ht).1
    have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer t.2
    have hetN : e * (t : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (hEN heE) (inv_mem htN)
    have hetC : e * (t : G)⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
      rw [mem_thetaQuotCentralizer_iff_thetaBarAct hetN]
      have h1 : (⟨e * (t : G)⁻¹, hetN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨e, hEN heE⟩ * (⟨t, htN⟩ : Subgroup.normalizer (L : Set G))⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_inv, hφe, thetaBarAct_of_mem t.2]
      have h2 : QuotientGroup.mk' N ⟨(t : G), t.2⟩ = xb := htx
      rw [h2, mul_inv_cancel]
    have h1 : e * (t : G)⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hBc]
      exact ⟨E.mul_mem heE (E.inv_mem htE), hetC⟩
    have h2 : e * (t : G)⁻¹ ∈ L := Subgroup.zpowers_le.mpr hcL h1
    apply heL
    have : e = e * (t : G)⁻¹ * t := by group
    rw [this]
    exact L.mul_mem h2 t.2
  have hxo : orderOf xb = 3 := orderOf_eq_prime hx3 fun h1 => hxT (h1 ▸ Tb.one_mem)
  obtain ⟨hScard, hSc, hSe⟩ := card_sup_zpowers_of_disjoint hxc hTbe.1 hTbe.2 hxo
    (inf_zpowers_eq_bot_of_not_mem hxo hxT)
  have hle := hm3 _ hSc hSe
  rw [hScard, hTb9] at hle
  norm_num at hle

theorem false_of_card_inf_L_eq_three_of_pow_ne (hKT : KS125TypeCInvol)
    (hFE : partTwoF G = partTwoE G) {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hcL : c ∈ L) (hc1 : c ≠ 1) (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {E : Subgroup G} (hE : Late.IsE27 E) (hEL : E ≤ lcBar c L) (hcE : c ∈ E)
    (hB3 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3)
    (hEL3 : Nat.card (E ⊓ L : Subgroup G) = 3) {e : G} (heE : e ∈ E) {l : G} (hl : l ∈ L)
    {z : G} (hz : z ∈ Sec4.thetaQuotCentralizer L) (hlz : e = l * z)
    (hx3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩ ^ 3 ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hexpE x x.2)⟩
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEL.trans (lcBar_le_normalizer hL)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpE c hcE) hc1
  have hZ := card_center_eq_three_of_isSLThreePi hSL
  have hZ3 : ∀ y ∈ Subgroup.center (L ⧸ N), y ^ 3 = 1 := by
    intro y hy
    have h0 := pow_card_eq_one' (x := (⟨y, hy⟩ : Subgroup.center (L ⧸ N)))
    rw [hZ] at h0
    exact congrArg Subtype.val h0
  have hBc : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcE, hcC⟩))
      (by rw [hB3, Nat.card_zpowers, hc3])).symm
  have hELc : E ⊓ L = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcE, hcL⟩))
      (by rw [hEL3, Nat.card_zpowers, hc3])).symm
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hEN hcE
  have hφc : thetaBarAct L ⟨c, hcN⟩ = 1 := (mem_thetaQuotCentralizer_iff_thetaBarAct hcN).mp hcC
  set xb : L ⧸ N := π ⟨l, hl⟩ with hxb
  have hφe : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj xb :=
    thetaBarAct_eq_conj hl hz hlz (hEN heE)
  have hx3Z : xb ^ 3 ∈ Subgroup.center (L ⧸ N) :=
    mk_pow_three_mem_center (hEN heE) (hexpE e heE) hφe
  have hZx : Subgroup.center (L ⧸ N) = Subgroup.zpowers (xb ^ 3) := by
    have ho : orderOf (xb ^ 3) = 3 := orderOf_eq_prime (hZ3 _ hx3Z) hx3
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx3Z)
      (by rw [hZ, Nat.card_zpowers, ho])).symm
  have hec : e ∉ Subgroup.zpowers c := by
    intro hmem
    apply hx3
    have h1 : e ∈ E ⊓ Sec4.thetaQuotCentralizer L := by rw [hBc]; exact hmem
    have h2 := (mem_thetaQuotCentralizer_iff_thetaBarAct (hEN heE)).mp h1.2
    rw [hφe] at h2
    exact hZ3 _ (mem_center_of_conj_eq_one h2)
  have hW9 : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
    rw [sup_comm]
    exact Sec4.card_zpowers_sup_zpowers (hexpE e heE) hc3 hec (hEc e heE c hcE)
  have hWE : Subgroup.zpowers e ⊔ Subgroup.zpowers c ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr heE) (Subgroup.zpowers_le.mpr hcE)
  obtain ⟨e₁, he₁E, he₁W⟩ : ∃ e₁ ∈ E, e₁ ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers c from hcon)
    rw [hE.2, hW9] at h1
    omega
  obtain ⟨l₁, hl₁, z₁, hz₁, hlz₁⟩ := exists_mul_of_mem_lcBar hL (hEL he₁E)
  set ub : L ⧸ N := π ⟨l₁, hl₁⟩ with hub
  have hφ₁ : thetaBarAct L ⟨e₁, hEN he₁E⟩ = MulAut.conj ub :=
    thetaBarAct_eq_conj hl₁ hz₁ hlz₁ (hEN he₁E)
  have hcomm : thetaBarAct L ⟨e₁, hEN he₁E⟩ * thetaBarAct L ⟨e, hEN heE⟩ =
      thetaBarAct L ⟨e, hEN heE⟩ * thetaBarAct L ⟨e₁, hEN he₁E⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc e₁ he₁E e heE)
  rw [hφ₁, hφe] at hcomm
  have hux : ub * xb * ub⁻¹ * xb⁻¹ ∈ Subgroup.center (L ⧸ N) := by
    apply mem_center_of_conj_eq_one
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hux' := conj_eq_of_mul_inv_mem_center hSL hx3Z hx3 hux
  have hcux : Commute ub xb := by
    change ub * xb = xb * ub
    calc ub * xb = ub * xb * ub⁻¹ * ub := by group
      _ = xb * ub := by rw [hux']
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp
    (hZx ▸ mk_pow_three_mem_center (hEN he₁E) (hexpE e₁ he₁E) hφ₁ :
      ub ^ 3 ∈ Subgroup.zpowers (xb ^ 3))
  set wb : L ⧸ N := ub * xb ^ (-r) with hwb
  have hw3 : wb ^ 3 = 1 := by
    rw [hwb, (hcux.zpow_right (-r)).mul_pow, ← hr, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add]
    rw [show ((3 : ℕ) : ℤ) * r + -r * (3 : ℕ) = 0 by push_cast; ring, zpow_zero]
  have he₁r : e₁ * e ^ (-r) ∈ E := E.mul_mem he₁E (E.zpow_mem heE _)
  have hφw : thetaBarAct L ⟨e₁ * e ^ (-r), hEN he₁r⟩ = MulAut.conj wb := by
    have h1 : (⟨e₁ * e ^ (-r), hEN he₁r⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨e₁, hEN he₁E⟩ * (⟨e, hEN heE⟩ : Subgroup.normalizer (L : Set G)) ^ (-r) :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_zpow, hφ₁, hφe, ← map_zpow, ← map_mul]
  have hwZ : wb ∉ Subgroup.center (L ⧸ N) := by
    intro hwZ
    apply he₁W
    have h1 : e₁ * e ^ (-r) ∈ E ⊓ Sec4.thetaQuotCentralizer L := by
      refine ⟨he₁r, (mem_thetaQuotCentralizer_iff_thetaBarAct (hEN he₁r)).mpr ?_⟩
      rw [hφw]
      exact conj_eq_one_of_mem_center hwZ
    rw [hBc] at h1
    have h2 : e₁ = e₁ * e ^ (-r) * e ^ r := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers e r))
  have hcw : Commute xb wb := by
    rw [hwb]
    exact (hcux.symm.mul_right (Commute.zpow_right (Commute.refl xb) (-r)))
  have hcw₁ : Commute ub wb := by
    rw [hwb]
    exact (Commute.refl ub).mul_right (hcux.zpow_right (-r))
  have heF : e ∈ Item125Diag.fixer L wb := by
    rw [Item125Diag.mem_fixer_iff]
    refine ⟨hEN heE, ?_⟩
    rw [hφe, MulAut.conj_apply, hcw.eq, mul_inv_cancel_right]
  have he₁F : e₁ ∈ Item125Diag.fixer L wb := by
    rw [Item125Diag.mem_fixer_iff]
    refine ⟨hEN he₁E, ?_⟩
    rw [hφ₁, MulAut.conj_apply, hcw₁.eq, mul_inv_cancel_right]
  have hcF : c ∈ Item125Diag.fixer L wb := by
    rw [Item125Diag.mem_fixer_iff]
    exact ⟨hcN, by rw [hφc, MulAut.one_apply]⟩
  have hEF : E ⊓ Item125Diag.fixer L wb = E :=
    eq_of_card_nine_lt hE.2 inf_le_left
      (le_inf hWE (sup_le (Subgroup.zpowers_le.mpr heF) (Subgroup.zpowers_le.mpr hcF))) hW9
      (show e₁ ∈ E ⊓ Item125Diag.fixer L wb from ⟨he₁E, he₁F⟩) he₁W
  have hfix : ∀ d (hd : d ∈ E), thetaBarAct L ⟨d, hEN hd⟩ wb = wb := by
    intro d hd
    have hd' : d ∈ E ⊓ Item125Diag.fixer L wb := by rw [hEF]; exact hd
    obtain ⟨hg, hgx⟩ := Item125Diag.mem_fixer_iff.mp hd'.2
    exact hgx
  obtain ⟨w, hwπ, hw3', hwE⟩ := exists_lift_pow_three hEp hEN wb hw3 hfix
  have hwN : (w : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer w.2
  have hφw' : thetaBarAct L ⟨w, hwN⟩ = MulAut.conj wb := by
    rw [← hwπ]
    exact thetaBarAct_of_mem w.2
  have hwE' : (w : G) ∉ E := by
    intro hmem
    apply hwZ
    have h1 : (w : G) ∈ E ⊓ L := ⟨hmem, w.2⟩
    rw [hELc] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : w = (⟨c, hcL⟩ : L) ^ k := Subtype.ext (by simp [hk])
    rw [← hwπ, h2, map_zpow]
    exact Subgroup.zpow_mem _ (mk_mem_center_of_mem_thetaQuotCentralizer (x := ⟨c, hcL⟩) hcC) k
  have hwo : orderOf (w : G) = 3 := orderOf_eq_prime hw3' fun h1 => hwE' (h1 ▸ E.one_mem)
  have hwc : (w : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hwE
  obtain ⟨hF81, hFc, hFe⟩ := card_sup_zpowers_of_disjoint hwc hE.1.1 hexpE hwo
    (inf_zpowers_eq_bot_of_not_mem hwo hwE')
  set t : G := e₁ * e ^ (-r) * (w : G)⁻¹ with ht
  have htN : t ∈ Subgroup.normalizer (L : Set G) := mul_mem (hEN he₁r) (inv_mem hwN)
  have htC : t ∈ Sec4.thetaQuotCentralizer L := by
    rw [mem_thetaQuotCentralizer_iff_thetaBarAct htN]
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨e₁ * e ^ (-r), hEN he₁r⟩ * (⟨w, hwN⟩ : Subgroup.normalizer (L : Set G))⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_inv, hφw, hφw', mul_inv_cancel]
  have htc : t ∉ Subgroup.zpowers c := by
    intro hmem
    apply hwE'
    have h1 : (w : G) = t⁻¹ * (e₁ * e ^ (-r)) := by rw [ht]; group
    rw [h1]
    exact E.mul_mem (E.inv_mem (Subgroup.zpowers_le.mpr hcE hmem)) he₁r
  exact Item125Diag.false_of_E81 hKT hFE hL hZ hSL (F := E ⊔ Subgroup.zpowers (w : G))
    ⟨hFc, hFe⟩ (by rw [hF81, hE.2]) (sup_le hEN (Subgroup.zpowers_le.mpr hwN)) (y := w)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (by rw [hwπ]; exact hwZ) hw3'
    (Subgroup.mem_sup_left hcE) hcC hc3 (z := t)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left he₁r)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))) htC htc

end Item128StepsProof

end CFSG.RankThree.PartTwo.Sec12
