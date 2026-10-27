module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.GroupTheory.PGroup.ExistsNeOneCommute
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_mem_uniqueSet_of_inverted (D : Data G)
    (hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G))
    {d t : G} (hdM : d ∈ D.M) (hd : Odd (orderOf d))
    (hdZ : d ∉ Subgroup.centralizer (D.Z : Set G)) (ht : t * d * t⁻¹ = d⁻¹)
    {q : ℕ} (hq : q.Prime) {X : Subgroup G} (hXq : IsPGroup q ↥X)
    (hXd : X ≤ Subgroup.centralizer ({d} : Set G)) : X ∉ uniqueSet D.M := by
  intro hXU
  have hMs : Subgroup.normalizer (D.M : Set G) = D.M :=
    UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hXU' : UC6.InU D.M X :=
    ⟨hXU.1, fun g hg => hXU.2 g⁻¹ hg⟩
  have hcent : Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute d x from hx.symm).zpow_left n).eq
  have hXA : X ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    hXd.trans (hcent.trans (Subgroup.centralizer_le_normalizer _))
  have ht' : ∀ a ∈ Subgroup.zpowers d, t * a * t⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hconj : (MulAut.conj t) d = d⁻¹ := by
      simpa [MulAut.conj_apply] using ht
    calc t * d ^ n * t⁻¹ = (MulAut.conj t) (d ^ n) := by simp [MulAut.conj_apply]
      _ = ((MulAut.conj t) d) ^ n := map_zpow _ d n
      _ = (d⁻¹) ^ n := by rw [hconj]
      _ = (d ^ n)⁻¹ := inv_zpow d n
  obtain ⟨m, hmM, hm⟩ := uc22p21b_core hMs hq hXq hXA hXU' ht'
  obtain ⟨y, hyM, hyZ, hyinv⟩ := uc22s23_exists_two_element hZM hmM
  have hbm : y * d * y⁻¹ = d⁻¹ := hyinv d (hm d (Subgroup.mem_zpowers d))
  exact hdZ (CFSG.GroupTheory.mem_centralizer_of_inverted hd hbm
    (fun a ha => (Subgroup.mem_centralizer_iff.mp hyZ a ha).symm)
    (hZM hdM))

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem mem_uniqueSet_of_le_barPreimage' (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) {X : Subgroup G} (hXne : X ≠ ⊥)
    (hXq : IsPGroup q ↥X) (hXP : X ≤ barPreimage D.M Dbar) :
    X ∈ uniqueSet D.M := by
  by_cases hqsig : q ∈ D.sig
  · have hq1 : q ∈ D.sig1 := by
      rw [← h6 h1930 c]
      exact hqsig
    exact mem_uniqueSet_of_isStronglyPEmbedded hq (hsp q hq1)
      (hXP.trans (uc22p21c_barPreimage_le D.M Dbar)) hXne hXq
  · obtain ⟨p, hp⟩ := hsig
    exact mem_uniqueSet_of_le_barPreimage c h1930 h71 hp hq hq2 hqsig hDn hDq hDnc hDexp
      hDcl hXne hXq hXP

private theorem exists_qSubgroup_le_barPreimage_of_commute {D : Data G} {d : G}
    (hdM : d ∈ D.M) (hd : Odd (orderOf d)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {x : Bar2 D.M} (hx1 : x ≠ 1) (hxq : x ^ q = 1)
    (hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M) * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M))
    {Y : Subgroup (Bar2 D.M)} (hxY : x ∈ Y) :
    ∃ X : Subgroup G, X ≠ ⊥ ∧ IsPGroup q ↥X ∧
      X ≤ Subgroup.centralizer ({d} : Set G) ∧ X ≤ barPreimage D.M Y := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hbodd : Odd (orderOf (⟨d, hdM⟩ : ↥D.M)) := by
    rw [← Subgroup.orderOf_coe]
    exact hd
  obtain ⟨z, hzd, hzq, hzne, hzmem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar hbodd hq hq2 hx1 hxq hxb
  have hXne : Subgroup.zpowers (z : G) ≠ ⊥ := by
    intro hbot
    have hmem : (z : G) ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers (z : G)
    exact hzne (Subtype.ext (by simpa using hmem))
  have hXq : IsPGroup q (Subgroup.zpowers (z : G)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    simpa using orderOf_dvd_of_pow_eq_one hzq
  have hXd : Subgroup.zpowers (z : G) ≤ Subgroup.centralizer ({d} : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hzd
  have hXY : Subgroup.zpowers (z : G) ≤ barPreimage D.M Y := by
    refine Subgroup.zpowers_le.mpr ?_
    exact uc22p21c_mem_barPreimage.2 ⟨z.2, (Subgroup.zpowers_le.mpr hxY) hzmem⟩
  exact ⟨Subgroup.zpowers (z : G), hXne, hXq, hXd, hXY⟩

private theorem exists_mem_pCore_pow_eq_prime_of_commute {M : Subgroup G} {p : ℕ}
    (hp : p.Prime) {b x : Bar2 M} (hxP : x ∈ CFSG.pCore p (Bar2 M)) (hx1 : x ≠ 1)
    (hxb : b * x = x * b) :
    ∃ y ∈ CFSG.pCore p (Bar2 M), y ≠ 1 ∧ y ^ p = 1 ∧ b * y = y * b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ orderOf x := by
    simpa only [Subgroup.orderOf_mk] using
      (CFSG.pCore_isPGroup (p := p) (G := Bar2 M)).dvd_orderOf
        (g := (⟨x, hxP⟩ : ↥(CFSG.pCore p (Bar2 M))))
        (fun h => hx1 (congrArg Subtype.val h))
  let y : Bar2 M := x ^ (orderOf x / p)
  have hyord : orderOf y = p := orderOf_pow_orderOf_div (orderOf_pos x).ne' hpdvd
  have hyfacts := (orderOf_eq_prime_iff (x := y) (p := p)).mp hyord
  have hyP : y ∈ CFSG.pCore p (Bar2 M) := by
    dsimp only [y]
    exact Subgroup.pow_mem _ hxP _
  refine ⟨y, hyP, hyfacts.2, hyfacts.1, ?_⟩
  exact (Commute.pow_right (show Commute b x from hxb) _).eq

theorem inf_centralizer_bar_eq_bot_of_inverted (c : Ctx23L D Ch)
    (hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G)) (h1930 : H1930 D)
    (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h71 : S23_7_1 D Ch) (hsig : D.sig.Nonempty)
    {d t : G} (hdM : d ∈ D.M) (hd : Odd (orderOf d))
    (hdZ : d ∉ Subgroup.centralizer (D.Z : Set G)) (ht : t * d * t⁻¹ = d⁻¹)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hDq : IsPGroup q ↥Dbar)
    (hDnc : ¬ IsCyclic ↥Dbar) (hDexp : ∀ y ∈ Dbar, y ^ q = 1)
    (hDcl : ⁅⁅Dbar, Dbar⁆, Dbar⁆ = ⊥) :
    Dbar ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M)} :
        Set (Bar2 D.M)) = ⊥ := by
  classical
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M) * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M) :=
    (Subgroup.mem_centralizer_iff.mp hx.2) _ (Set.mem_singleton _)
  obtain ⟨X, hXne, hXq, hXd, hXP⟩ :=
    exists_qSubgroup_le_barPreimage_of_commute hdM hd hq hq2 hx1 (hDexp x hx.1) hxb hx.1
  exact not_mem_uniqueSet_of_inverted D hZM hdM hd hdZ ht hq hXq hXd
    (c.mem_uniqueSet_of_le_barPreimage' h1930 h6 hsp h71 hsig hq hq2 hDn hDq hDnc hDexp
      hDcl hXne hXq hXP)

theorem pCore_inf_centralizer_bar_eq_bot_of_inverted (c : Ctx23L D Ch)
    (hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G)) (h1930 : H1930 D)
    (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {d t : G} (hdM : d ∈ D.M) (hd : Odd (orderOf d))
    (hdZ : d ∉ Subgroup.centralizer (D.Z : Set G)) (ht : t * d * t⁻¹ = d⁻¹)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpsig : p ∈ D.sig) :
    CFSG.pCore p (Bar2 D.M) ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M)} :
        Set (Bar2 D.M)) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hp1 : p ∈ D.sig1 := by
    rw [← h6 h1930 c]
    exact hpsig
  have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M) * x =
      x * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨d, hdM⟩ : ↥D.M) :=
    (Subgroup.mem_centralizer_iff.mp hx.2) _ (Set.mem_singleton _)
  obtain ⟨y, hyP, hyne, hypow, hyb⟩ :=
    exists_mem_pCore_pow_eq_prime_of_commute hp hx.1 hx1 hxb
  obtain ⟨X, hXne, hXq, hXd, hXP⟩ :=
    exists_qSubgroup_le_barPreimage_of_commute hdM hd hp hp2 hyne hypow hyb hyP
  have hXM : X ≤ D.M := hXP.trans (uc22p21c_barPreimage_le D.M _)
  have hXU : X ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded hp (hsp p hp1) hXM hXne hXq
  exact not_mem_uniqueSet_of_inverted D hZM hdM hd hdZ ht hp hXq hXd hXU

end Ctx23L

theorem not_mem_sig_of_normalizer_not_le (D : Data G) (Ch : Choice2011 G)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {r : ℕ} (hr : r.Prime) {x : G} (hxM : x ∈ D.M) (hxr : orderOf x = r)
    (hN : ¬ Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M) :
    r ∉ D.sig := by
  intro hrsig
  have hr1 : r ∈ D.sig1 := by
    rw [← h6 h1930 c]
    exact hrsig
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxr
    exact hr.ne_one hxr.symm
  refine hN (normalizer_le_of_mem_uniqueSet D.maxLocal ?_)
  refine mem_uniqueSet_of_isStronglyPEmbedded hr (hsp r hr1) (Subgroup.zpowers_le.mpr hxM) ?_ ?_
  · intro hbot
    exact hx1 (Subgroup.zpowers_eq_bot.mp hbot)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxr, pow_one])

end CFSG.LocalAnalysis.UniquenessCase.UC22

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

private theorem inf_centralizer_zpow_le_centralizer_of_prime_order
    {K : Type*} [Group K] {r : ℕ} [Fact r.Prime] {x : K} (hx : orderOf x = r)
    (i : ℤ) (hzi : x ^ i ≠ 1) (Q : Subgroup K) :
    Q ⊓ Subgroup.centralizer ({x ^ i} : Set K) ≤ Subgroup.centralizer ({x} : Set K) := by
  intro q hq
  obtain ⟨-, hqC⟩ := Subgroup.mem_inf.mp hq
  rw [Subgroup.mem_centralizer_singleton_iff] at hqC ⊢
  have hr := Fact.out (p := r.Prime)
  have hzpx : Subgroup.zpowers (x ^ i) = Subgroup.zpowers x :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers hr
      (by rw [← hx]; exact pow_orderOf_eq_one x) hzi
      (Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩)
  have hxC : x ∈ Subgroup.zpowers (x ^ i) := by
    rw [hzpx]
    exact Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxC
  calc q * x = q * (x ^ i) ^ m := by rw [hm]
    _ = (x ^ i) ^ m * q := (Commute.zpow_right hqC m).eq
    _ = x * q := by rw [hm]

private theorem inf_centralizer_le_centralizer_of_mem_sup
    {K : Type*} [Group K] [Finite K] {r : ℕ} [Fact r.Prime] {x y : K} {Q : Subgroup K}
    (hx : orderOf x = r) (hy : orderOf y = r) (hxy : x * y = y * x)
    (hsemi : ∀ i j : ℤ, ¬ (r : ℤ) ∣ j →
      Q ⊓ Subgroup.centralizer ({x ^ i * y ^ j} : Set K) = ⊥)
    {e : K} (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) (he1 : e ≠ 1) :
    Q ⊓ Subgroup.centralizer ({e} : Set K) ≤
      Subgroup.centralizer ({x} : Set K) := by
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute x y from hxy).zpow_left n).zpow_right m |>.eq
  obtain ⟨a, ha, b, hb, hab⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := Subgroup.zpowers x)
      (B := Subgroup.zpowers y) hcomm he
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hab]
  by_cases hj : (r : ℤ) ∣ j
  · have hyj : y ^ j = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hy]
      exact hj
    have hsum : x ^ i * y ^ j = x ^ i := by rw [hyj, mul_one]
    have hzi : x ^ i ≠ 1 := by
      intro h
      exact he1 (by rw [← hab, hsum, h])
    rw [hsum]
    exact inf_centralizer_zpow_le_centralizer_of_prime_order hx i hzi Q
  · rw [hsemi i j hj]
    exact bot_le

theorem le_centralizer_of_rank_two {K : Type*} [Group K] [Finite K] {r : ℕ} [Fact r.Prime]
    {x y : K} {Q : Subgroup K} (hx : orderOf x = r) (hy : orderOf y = r)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x)
    (hxQ : x ∈ Subgroup.normalizer (Q : Set K))
    (hyQ : y ∈ Subgroup.normalizer (Q : Set K))
    (hcop : Nat.Coprime r (Nat.card Q))
    (hsemi : ∀ i j : ℤ, ¬ (r : ℤ) ∣ j →
      Q ⊓ Subgroup.centralizer ({x ^ i * y ^ j} : Set K) = ⊥) :
    Q ≤ Subgroup.centralizer ({x} : Set K) := by
  have hr := Fact.out (p := r.Prime)
  have hxcard : Nat.card (Subgroup.zpowers x) = r := by rw [Nat.card_zpowers, hx]
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute x y from hxy).zpow_left n).eq
  have hE := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (X := Subgroup.zpowers x) (v := y) hxcard hy hyx hcomm
  have hEN : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      Subgroup.normalizer (Q : Set K) :=
    sup_le (Subgroup.zpowers_le.mpr hxQ) (Subgroup.zpowers_le.mpr hyQ)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    (p := r) hr hE.1 (by rw [hE.2]) hEN hcop
  rw [← hgen]
  exact iSup_le fun e => iSup_le fun he => iSup_le fun he1 =>
    inf_centralizer_le_centralizer_of_mem_sup hx hy hxy hsemi he he1

theorem exists_ne_one_commute_of_isPGroup {q : ℕ} [Fact q.Prime] {Q : Subgroup G}
    [Finite Q] (hQ : IsPGroup q Q) (hQ1 : Q ≠ ⊥) {y : G} (hy : y ^ q = 1)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ x ∈ Q, x ≠ 1 ∧ x * y = y * x := by
  have hYq : IsPGroup q (Subgroup.zpowers y) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hy
  have hYn : ∀ g ∈ Subgroup.zpowers y, ∀ o ∈ Q, g * o * g⁻¹ ∈ Q := by
    intro g hg o ho
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hyQ hg) o).mp ho
  obtain ⟨o, hoQ, ho1, hcomm⟩ :=
    CFSG.GroupTheory.exists_ne_one_commute_of_normalizes hYq hQ hQ1 hYn
  exact ⟨o, hoQ, ho1, (hcomm y (Subgroup.mem_zpowers y)).symm⟩

end CFSG.GroupTheory

end
