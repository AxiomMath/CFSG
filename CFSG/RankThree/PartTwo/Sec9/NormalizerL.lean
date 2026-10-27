module

public import CFSG.RankThree.PartTwo.Sec9.Hyp92Never
public import CFSG.RankThree.PartTwo.KFacts.K71Item93b
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section General

variable {G : Type} [Group G]

theorem isElemAbelian_zpowers {x : G} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (H : Set G))
    {z : G} (hz : z ∈ H ⊔ K) : ∃ y ∈ K, ∃ x ∈ H, y * x = z := by
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K H hKN] at hz
  obtain ⟨y, hy, x, hx, rfl⟩ := hz
  exact ⟨y, hy, x, hx, rfl⟩

theorem isElemAbelian_sup {H K : Subgroup G} (hH : CFSG.Assembly.IsElemAbelian 3 H)
    (hK : CFSG.Assembly.IsElemAbelian 3 K) (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    CFSG.Assembly.IsElemAbelian 3 (H ⊔ K) := CFSG.Open.IsElemAbelian.sup_of_commute hH hK hHK

theorem mem_zpowers_of_mem_zpowers_of_ne_one {x y : G} (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : x ∈ Subgroup.zpowers y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  rw [zpow_eq_zpow_emod k hx3'] at hy1 ⊢
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk] at hy1 ⊢
  · exact absurd (zpow_zero x) hy1
  · rw [zpow_one]
    exact Subgroup.mem_zpowers x
  · have h1 : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, hx3', mul_one, zpow_one]
    have h2 : (x ^ (2 : ℤ)) ^ (2 : ℤ) ∈ Subgroup.zpowers (x ^ (2 : ℤ)) :=
      Subgroup.zpow_mem_zpowers _ 2
    rwa [← h1] at h2

theorem disjoint_zpowers_of_not_mem {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxH : x ∉ H) :
    Disjoint H (Subgroup.zpowers x) := by
  rw [Subgroup.disjoint_def]
  intro y hyH hyx
  by_contra hy1
  exact hxH (Subgroup.zpowers_le.mpr hyH (mem_zpowers_of_mem_zpowers_of_ne_one hx3 hyx hy1))

theorem pow_six_mod_nine {m : ℕ} (hm : ¬ 3 ∣ m) : m ^ 6 % 9 = 1 := by
  have h : ∀ r < 9, ¬ 3 ∣ r → r ^ 6 % 9 = 1 := by decide
  rw [Nat.pow_mod]
  exact h _ (Nat.mod_lt _ (by norm_num))
    (fun h3 => hm ((Nat.dvd_mod_iff (by norm_num : 3 ∣ 9)).mp h3))

theorem pow_two_mod_three {m : ℕ} (hm : ¬ 3 ∣ m) : m ^ 2 % 3 = 1 := by
  have h : ∀ r < 3, ¬ 3 ∣ r → r ^ 2 % 3 = 1 := by decide
  rw [Nat.pow_mod]
  exact h _ (Nat.mod_lt _ (by norm_num)) (fun h3 => hm ((Nat.dvd_mod_iff dvd_rfl).mp h3))

theorem exists_odd_pow_two_pow_eq_one [Finite G] (x : G) :
    ∃ q s : ℕ, Odd q ∧ (x ^ q) ^ 2 ^ s = 1 := by
  obtain ⟨s, q, hq, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨q, s, hq, ?_⟩
  rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]

theorem exists_commute_of_mk_commute {C : Type*} [Group C] [Finite C] {P : Subgroup C}
    (hP : IsPGroup 3 P) {y : C}
    (hy : ∀ p ∈ P, (p : C ⧸ aschbacherSolvableCore 3 C) * (y : C ⧸ aschbacherSolvableCore 3 C) =
      (y : C ⧸ aschbacherSolvableCore 3 C) * (p : C ⧸ aschbacherSolvableCore 3 C)) :
    ∃ y' : C, (y' : C ⧸ aschbacherSolvableCore 3 C) = (y : C ⧸ aschbacherSolvableCore 3 C) ∧
      ∀ p ∈ P, p * y' = y' * p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : P →* MulAut C := MulAut.conj.comp P.subtype
  have hN : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 C) :=
    (solvable_prime_complement_core_characterization (H := C) Nat.prime_three).2.2.1
  obtain ⟨y', hy'q, hy'fix⟩ := KFacts.exists_fixed_of_coprime hP φ (aschbacherSolvableCore 3 C)
    hN (fun g n hn => (inferInstance : (aschbacherSolvableCore 3 C).Normal).conj_mem n hn g) y
    (fun g => by
      change (((g : C) * y * (g : C)⁻¹ : C) : C ⧸ aschbacherSolvableCore 3 C) = _
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hy g g.2, QuotientGroup.mk_inv,
        mul_inv_cancel_right])
  refine ⟨y', hy'q, fun p hp => ?_⟩
  have h1 : p * y' * p⁻¹ = y' := hy'fix ⟨p, hp⟩
  calc p * y' = p * y' * p⁻¹ * p := by group
    _ = y' * p := by rw [h1]


theorem isPGroup_zpowers_of_pow {p k : ℕ} {x : G} (h : x ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  intro y
  refine ⟨k, Subtype.ext ?_⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp y.2
  rw [Subgroup.coe_pow, ← hi, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h, one_zpow]

theorem mk_commute_iff {C : Type*} [Group C] (N : Subgroup C) [N.Normal] (x y : C) :
    (x : C ⧸ N) * (y : C ⧸ N) = (y : C ⧸ N) * (x : C ⧸ N) ↔ x * y * x⁻¹ * y⁻¹ ∈ N := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm]

end General

section Core

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G} {n : ℕ}

theorem Hyp92.false_of_map_conj_ne (h : Hyp92 G A c L a R n) (hcL : c ∈ L)
    (hcZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))
    (hc1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ≠ 1) {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hne : L.map (MulAut.conj g).toMonoidHom ≠ L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := h.one_le
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hc3 : c ^ 3 = 1 := hAel.2 c h.mem_A
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 h.ne_one
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set Θ := inSubgroup (aschbacherSolvableCore 3) C with hΘ
  set θC := aschbacherSolvableCore 3 C with hθC
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hLC : L ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hCc : ∀ x ∈ C, x * c = c * x := fun x hx => Subgroup.mem_centralizer_singleton_iff.mp hx
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzc : Subgroup.zpowers ((MulAut.conj g) c) = Subgroup.zpowers c := by
    have h1 : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [MonoidHom.map_zpowers] at h1
    exact h1
  have hL'c : L' ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt
    rw [thetaComponentsAt_eq_thetaComponentsIn,
      Sec10.centralizer_singleton_eq_of_zpowers_eq hzc] at h1
    exact h1
  have hL'C : L' ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hL'c
  have hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y * x⁻¹ * y⁻¹ ∈ Θ := fun x hx y hy =>
    Sec10.commutator_mem_theta_of_ne h.mem_thetaComponentsAt hL'c (fun h1 => hne h1.symm) hx hy
  have hθL := Sec6.theta_eq_inf_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hmemΘ : ∀ (x : G) (hx : x ∈ C), x ∈ Θ ↔ (⟨x, hx⟩ : C) ∈ θC := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h1
      exact ⟨_, h1, rfl⟩
  have hQ : ∀ (x : G) (hx : x ∈ L) (y : G) (hy : y ∈ L'),
      ((⟨x, hLC hx⟩ : C) : C ⧸ θC) * ((⟨y, hL'C hy⟩ : C) : C ⧸ θC) =
        ((⟨y, hL'C hy⟩ : C) : C ⧸ θC) * ((⟨x, hLC hx⟩ : C) : C ⧸ θC) := by
    intro x hx y hy
    rw [mk_commute_iff, ← hmemΘ]
    exact hcomm x hx y hy
  have hcen : ∀ (x : G) (hx : x ∈ L) (y : G) (hy : y ∈ L'),
      ((⟨x, hLC hx⟩ : C) : C ⧸ θC) = ((⟨y, hL'C hy⟩ : C) : C ⧸ θC) →
        π ⟨x, hx⟩ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    intro x hx y hy hxy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) z
    have h1 := hQ l l.2 y hy
    rw [← hxy] at h1
    rw [mk_commute_iff, ← hmemΘ] at h1
    have h2 : (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [hθL]
      exact ⟨L.mul_mem (L.mul_mem (L.mul_mem l.2 hx) (L.inv_mem l.2)) (L.inv_mem hx), h1⟩
    obtain ⟨s, hs, hse⟩ := h2
    have e : l * ⟨x, hx⟩ * l⁻¹ * (⟨x, hx⟩ : L)⁻¹ = s := Subtype.ext hse.symm
    have h3 : π (l * ⟨x, hx⟩ * l⁻¹ * (⟨x, hx⟩ : L)⁻¹) = 1 := by
      rw [e, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hs
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
      commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  obtain ⟨ub, vb, tb, hub3, hvb3, hubvb, hind, htb1, htb2, htbvb⟩ :=
    KFacts.exists_uvt_of_isSLThreePiAt hn h.isSLThreePiAt hcZ hc1
  have hcL3 : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcbar3 : π ⟨c, hcL⟩ ^ 3 = 1 := by rw [← map_pow, hcL3, map_one]
  have hvb9 : vb ^ 3 ^ 2 = 1 := by
    rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, hvb3, hcbar3]
  have hY3 : IsPGroup 3 ↥(Subgroup.zpowers ub ⊔ Subgroup.zpowers vb) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow (k := 1) (by simpa using hub3))
      (isPGroup_zpowers_of_pow hvb9)
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun w hw => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
          exact (Commute.zpow_left (show Commute vb ub from hubvb.symm) k).eq)))
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hcL
  have hρc : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨c, hcN⟩) = 1 :=
    KFacts.thetaQuotMulAut_compAction_eq_one hcN (fun w hw => (hCc w (hLC hw)).symm)
  have hYbar : Subgroup.zpowers ub ⊔ Subgroup.zpowers vb ≤
      Sec8.barCentralizer (Subgroup.zpowers c) L := by
    intro w _
    rw [KFacts.mem_barCentralizer_zpowers_iff hcN, hρc, MulAut.one_apply]
  obtain ⟨E₀, hE₀L, -, hE₀3, hE₀im, -, hE₀inj⟩ :=
    KFacts.exists_lift_of_le_barCentralizer hcN ⟨1, by simpa using hc3⟩ hY3 hYbar
  have hmemim : ∀ z ∈ Subgroup.zpowers ub ⊔ Subgroup.zpowers vb,
      ∃ w : L, (w : G) ∈ E₀ ∧ π w = z := by
    intro z hz
    rw [← hE₀im] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    exact ⟨w, Subgroup.mem_subgroupOf.mp hw, hwz⟩
  obtain ⟨x, hxE, hxu⟩ := hmemim ub (Subgroup.mem_sup_left (Subgroup.mem_zpowers ub))
  obtain ⟨y, hyE, hyv⟩ := hmemim vb (Subgroup.mem_sup_right (Subgroup.mem_zpowers vb))
  have hx3 : x ^ 3 = 1 := hE₀inj _ (by rw [Subgroup.coe_pow]; exact E₀.pow_mem hxE 3)
    (by rw [map_pow, hxu, hub3])
  have hxy : x * y = y * x := by
    have h1 := hE₀inj (x * y * x⁻¹ * y⁻¹) (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact E₀.mul_mem (E₀.mul_mem (E₀.mul_mem hxE hyE) (E₀.inv_mem hxE)) (E₀.inv_mem hyE))
      (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxu, hyv, ← commutatorElement_def,
          commutatorElement_eq_one_iff_mul_comm]
        exact hubvb)
    rwa [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
  have hyc : (y : G) ^ 3 = c := by
    obtain ⟨k, hk⟩ := hE₀3 ⟨y, hyE⟩
    have hyk : y ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hyc' : Commute y (⟨c, hcL⟩ : L) := Subtype.ext (hCc y (hLC y.2))
    have h1 : y ^ 3 * (⟨c, hcL⟩ : L)⁻¹ ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, map_pow, ← hπ,
        hyv, hvb3, mul_inv_cancel]
    have h2 : (y ^ 3 * (⟨c, hcL⟩ : L)⁻¹) ^ 3 ^ (k + 1) = 1 := by
      have hc' : Commute (y ^ 3) (⟨c, hcL⟩ : L)⁻¹ := (hyc'.pow_left 3).inv_right
      rw [hc'.mul_pow, ← pow_mul, show 3 * 3 ^ (k + 1) = 3 ^ k * 9 by ring, pow_mul, hyk,
        one_pow, one_mul, inv_pow, show 3 ^ (k + 1) = 3 * 3 ^ k by ring, pow_mul, hcL3, one_pow,
        inv_one]
    have h3 := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow h1 h2
    have h4 : y ^ 3 = ⟨c, hcL⟩ := mul_inv_eq_one.mp h3
    simpa using congrArg Subtype.val h4
  have hind' : ∀ i j : ℕ, π x ^ i * π y ^ j ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) →
      3 ∣ i ∧ 3 ∣ j := fun i j h1 => hind i j (by rwa [hxu, hyv] at h1)
  have hyN : (y : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer y.2
  have hy9 : (y : G) ^ 3 ^ 2 = 1 := by
    rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, hyc, hc3]
  have htbfix : tb ∈ Sec8.barCentralizer (Subgroup.zpowers (y : G)) L := by
    rw [KFacts.mem_barCentralizer_zpowers_iff hyN,
      KFacts.thetaQuotMulAut_compAction_of_mem y.2 hyN, MulAut.conj_apply]
    change π y * tb * (π y)⁻¹ = tb
    rw [hyv, ← htbvb, mul_inv_cancel_right]
  rw [← KFacts.imageModTheta_centralizer_eq hyN ⟨2, hy9⟩] at htbfix
  obtain ⟨t₀, ht₀, ht₀e⟩ := htbfix
  have ht₀y : (t₀ : G) * y = y * t₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp ht₀).2
  obtain ⟨q, s, hq, hts⟩ := exists_odd_pow_two_pow_eq_one t₀
  set t₂ := t₀ ^ q with ht₂
  have ht₂tb : π t₂ = tb := by
    obtain ⟨r, rfl⟩ := hq
    rw [ht₂, map_pow, ht₀e, pow_succ, pow_mul, htb2, one_pow, one_mul]
  have ht₂y : (t₂ : G) * y = y * t₂ := by
    rw [ht₂, Subgroup.coe_pow]
    exact (Commute.pow_left ht₀y q).eq
  have ht₂Θ : (t₂ : G) ∉ Θ := by
    intro hmem
    have h1 : (t₂ : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [hθL]
      exact ⟨t₂.2, hmem⟩
    obtain ⟨s', hs', hs'e⟩ := h1
    have e : t₂ = s' := Subtype.ext hs'e.symm
    apply htb1
    rw [← ht₂tb, e, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hs'
  obtain ⟨lam, hlam⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hg c).mp (Subgroup.mem_zpowers c))
  have hlam3 : ¬ (3 : ℤ) ∣ lam := by
    rintro ⟨k, rfl⟩
    apply h.ne_one
    have h1 : g * c * g⁻¹ = 1 := by
      rw [← hlam, zpow_mul, show c ^ (3 : ℤ) = 1 by exact_mod_cast hc3, one_zpow]
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  set u' := g * (x : G) * g⁻¹ with hu'
  set v' := g * (y : G) * g⁻¹ with hv'
  have hu'L' : u' ∈ L' := ⟨x, x.2, rfl⟩
  have hv'L' : v' ∈ L' := ⟨y, y.2, rfl⟩
  have hu'3 : u' ^ 3 = 1 := by
    rw [hu', conj_pow, ← Subgroup.coe_pow, hx3, Subgroup.coe_one, mul_one, mul_inv_cancel]
  have hv'3 : v' ^ 3 = c ^ lam := by rw [hv', conj_pow, hyc, hlam]
  have hu'v' : u' * v' = v' * u' := by
    have e : (x : G) * y = y * x := congrArg Subtype.val hxy
    calc u' * v' = g * ((x : G) * y) * g⁻¹ := by rw [hu', hv']; group
      _ = g * ((y : G) * x) * g⁻¹ := by rw [e]
      _ = v' * u' := by rw [hu', hv']; group
  have hcL' : c ∈ L' := by
    have h1 : g * c * g⁻¹ ∈ L' := ⟨c, hcL, rfl⟩
    have h2 : g * c * g⁻¹ ∈ Subgroup.zpowers c := ⟨lam, hlam⟩
    have h3 : g * c * g⁻¹ ≠ 1 := by
      intro h4
      apply h.ne_one
      calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
        _ = 1 := by rw [h4]; group
    exact Subgroup.zpowers_le.mpr h1 (mem_zpowers_of_mem_zpowers_of_ne_one hc3 h2 h3)
  have hm3 : ¬ 3 ∣ Nat.card θC :=
    (solvable_prime_complement_core_characterization (H := C) Nat.prime_three).2.2.1
  set m := Nat.card θC with hm
  have hθCpow : ∀ z : C, z ∈ θC → z ^ m = 1 := by
    intro z hz
    have h1 := pow_card_eq_one' (G := θC) (x := ⟨z, hz⟩)
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have hcentC : ∀ (z : C) (k : ℤ), Commute z ⟨c ^ k, C.zpow_mem hcC k⟩ := fun z k =>
    Subtype.ext ((show Commute (z : G) c from hCc z z.2).zpow_right k)
  have hc3C : (⟨c ^ lam, C.zpow_mem hcC lam⟩ : C) ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show c ^ ((3 : ℕ) : ℤ) = 1 by exact_mod_cast hc3, one_zpow])
  set u'C : C := ⟨u', hL'C hu'L'⟩ with hu'C
  set v'C : C := ⟨v', hL'C hv'L'⟩ with hv'C
  have hP₁ : IsPGroup 3 (E₀.subgroupOf C) := hE₀3.comap_subtype
  obtain ⟨v₁, hv₁q, hv₁c⟩ := exists_commute_of_mk_commute hP₁ (y := v'C) (fun p hp =>
    hQ p (hE₀L (Subgroup.mem_subgroupOf.mp hp)) v' hv'L')
  have hv'C3 : v'C ^ 3 = ⟨c ^ lam, C.zpow_mem hcC lam⟩ := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hv'3)
  have hv'C9 : v'C ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hv'C3, hc3C]
  set vt := v₁ ^ (m ^ 6) with hvt
  have hvtq : (vt : C ⧸ θC) = (v'C : C ⧸ θC) := by
    rw [hvt, QuotientGroup.mk_pow, hv₁q, ← QuotientGroup.mk_pow, pow_eq_pow_mod (m ^ 6) hv'C9,
      pow_six_mod_nine hm3, pow_one]
  have hv₁9 : v₁ ^ 9 ∈ θC := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hv₁q, ← QuotientGroup.mk_pow, hv'C9,
      QuotientGroup.mk_one]
  have hvt9 : vt ^ 9 = 1 := by
    rw [hvt, ← pow_mul, show m ^ 6 * 9 = 9 * m * m ^ 5 by ring, pow_mul, pow_mul,
      hθCpow _ hv₁9, one_pow]
  have hvt3 : vt ^ 3 = ⟨c ^ lam, C.zpow_mem hcC lam⟩ := by
    have h1 : vt ^ 3 * (⟨c ^ lam, C.zpow_mem hcC lam⟩ : C)⁻¹ ∈ θC := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_pow, hvtq, ← QuotientGroup.mk_pow, hv'C3, mul_inv_cancel]
    have h2 : (vt ^ 3 * (⟨c ^ lam, C.zpow_mem hcC lam⟩ : C)⁻¹) ^ 3 ^ 1 = 1 := by
      have hc' : Commute (vt ^ 3) (⟨c ^ lam, C.zpow_mem hcC lam⟩ : C)⁻¹ :=
        ((hcentC vt lam).pow_left 3).inv_right
      rw [pow_one, hc'.mul_pow, ← pow_mul, show 3 * 3 = 9 from rfl, hvt9, one_mul, inv_pow, hc3C,
        inv_one]
    exact mul_inv_eq_one.mp (KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow h1 h2)
  have hvtE : ∀ p ∈ E₀, p * (vt : G) = (vt : G) * p := by
    intro p hp
    have h1 : (⟨p, hLC (hE₀L hp)⟩ : C) * v₁ = v₁ * ⟨p, hLC (hE₀L hp)⟩ :=
      hv₁c ⟨p, hLC (hE₀L hp)⟩ (Subgroup.mem_subgroupOf.mpr hp)
    have h2 : (⟨p, hLC (hE₀L hp)⟩ : C) * vt = vt * ⟨p, hLC (hE₀L hp)⟩ := by
      rw [hvt]
      exact (Commute.pow_right h1 _).eq
    exact congrArg Subtype.val h2
  have hvtP : IsPGroup 3 (Subgroup.zpowers vt) :=
    isPGroup_zpowers_of_pow (k := 2) (by rw [show 3 ^ 2 = 9 by norm_num]; exact hvt9)
  have hP₁N : E₀.subgroupOf C ≤ Subgroup.normalizer (Subgroup.zpowers vt : Set C) := fun p hp =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : Commute p vt := Subtype.ext (hvtE p (Subgroup.mem_subgroupOf.mp hp))
      exact (h1.symm.zpow_left k).eq)
  have hP₂ : IsPGroup 3 ↥(E₀.subgroupOf C ⊔ Subgroup.zpowers vt) :=
    IsPGroup.to_sup_of_normal_right' hP₁ hvtP hP₁N
  have hu'C3 : u'C ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hu'3)
  have hu'v'C : u'C * v'C = v'C * u'C := Subtype.ext hu'v'
  obtain ⟨u₁, hu₁q, hu₁c⟩ := exists_commute_of_mk_commute hP₂ (y := u'C) (by
    intro p hp
    have hle : E₀.subgroupOf C ⊔ Subgroup.zpowers vt ≤
        (Subgroup.centralizer {(u'C : C ⧸ θC)}).comap (QuotientGroup.mk' θC) := by
      refine sup_le (fun p' hp' => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply]
        exact hQ p' (hE₀L (Subgroup.mem_subgroupOf.mp hp')) u' hu'L'
      · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply,
          hvtq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hu'v'C]
    have h1 := hle hp
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply] at h1
    exact h1)
  set ut := u₁ ^ (m ^ 2) with hut
  have hutq : (ut : C ⧸ θC) = (u'C : C ⧸ θC) := by
    rw [hut, QuotientGroup.mk_pow, hu₁q, ← QuotientGroup.mk_pow, pow_eq_pow_mod (m ^ 2) hu'C3,
      pow_two_mod_three hm3, pow_one]
  have hut3 : ut ^ 3 = 1 := by
    have h1 : u₁ ^ 3 ∈ θC := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu₁q, ← QuotientGroup.mk_pow, hu'C3,
        QuotientGroup.mk_one]
    rw [hut, ← pow_mul, show m ^ 2 * 3 = 3 * m * m by ring, pow_mul, pow_mul, hθCpow _ h1,
      one_pow]
  have hutE : ∀ p ∈ E₀, p * (ut : G) = (ut : G) * p := by
    intro p hp
    have h1 : (⟨p, hLC (hE₀L hp)⟩ : C) * u₁ = u₁ * ⟨p, hLC (hE₀L hp)⟩ :=
      hu₁c _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hp))
    have h2 : (⟨p, hLC (hE₀L hp)⟩ : C) * ut = ut * ⟨p, hLC (hE₀L hp)⟩ := by
      rw [hut]
      exact (Commute.pow_right h1 _).eq
    exact congrArg Subtype.val h2
  have hutvt : (vt : G) * ut = ut * vt := by
    have h1 : vt * u₁ = u₁ * vt := hu₁c vt (Subgroup.mem_sup_right (Subgroup.mem_zpowers vt))
    have h2 : vt * ut = ut * vt := by
      rw [hut]
      exact (Commute.pow_right h1 _).eq
    exact congrArg Subtype.val h2
  set v₀ := (y : G) ^ lam with hv₀
  have hv₀E : v₀ ∈ E₀ := E₀.zpow_mem hyE lam
  have hv₀L : v₀ ∈ L := L.zpow_mem y.2 lam
  have hv₀3 : v₀ ^ 3 = c ^ lam := by
    rw [hv₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyc]
  set w := (vt : G) * v₀⁻¹ with hw
  have hvtv₀ : Commute (vt : G) v₀ := (hvtE v₀ hv₀E).symm
  have hvt3G : (vt : G) ^ 3 = c ^ lam := by rw [← Subgroup.coe_pow, hvt3]
  have hw3 : w ^ 3 = 1 := by
    rw [hw, (hvtv₀.inv_right).mul_pow, inv_pow, hv₀3, hvt3G, mul_inv_cancel]
  have hutC : (ut : G) ∈ C := ut.2
  have hwC : w ∈ C := C.mul_mem vt.2 (C.inv_mem (hLC hv₀L))
  have hut3G : (ut : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hut3, Subgroup.coe_one]
  have hcut : Commute c (ut : G) := (hCc _ hutC).symm
  have hcw : Commute c w := (hCc _ hwC).symm
  have hutw : Commute (ut : G) w := by
    rw [hw]
    exact (show Commute (ut : G) vt from hutvt.symm).mul_right
      (Commute.inv_right (hutE v₀ hv₀E).symm)
  have hxy' : Commute (x : G) y := congrArg Subtype.val hxy
  have hxut : Commute (x : G) ut := hutE x hxE
  have hxv₀ : Commute (x : G) v₀ := by
    rw [hv₀]
    exact hxy'.zpow_right lam
  have hxw : Commute (x : G) w := by
    rw [hw]
    exact (show Commute (x : G) vt from hvtE x hxE).mul_right hxv₀.inv_right
  have hxc : Commute (x : G) c := hCc x (hLC x.2)
  set E₁ := Subgroup.zpowers c ⊔ Subgroup.zpowers (ut : G) with hE₁
  set E := E₁ ⊔ Subgroup.zpowers w with hE
  have hE₁el : CFSG.Assembly.IsElemAbelian 3 E₁ :=
    isElemAbelian_sup (isElemAbelian_zpowers hc3) (isElemAbelian_zpowers hut3G)
      (fun a' ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (hcut.zpow_zpow i j).eq)
  have hE₁cw : E₁ ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      rw [Subgroup.mem_centralizer_iff] <;> intro b hb <;>
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    · exact (hcw.symm.zpow_left j).eq
    · exact (hutw.symm.zpow_left j).eq
  have hEel : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_sup hE₁el (isElemAbelian_zpowers hw3) (fun a' ha b hb =>
      ((Subgroup.mem_centralizer_iff.mp (hE₁cw ha)) b hb).symm)
  have hutN : Subgroup.zpowers (ut : G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Subgroup.zpowers_le.mpr (Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [hCc _ hutC, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c))
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (E₁ : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun e he =>
        ((Subgroup.mem_centralizer_iff.mp (hE₁cw he)) w (Subgroup.mem_zpowers w)).symm))
  have hgC : g ∈ Subgroup.normalizer (C : Set G) := by
    apply Sec11.mem_normalizer_of_forall_conj_mem
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : z * c ^ lam = c ^ lam * z := (Commute.zpow_right (hCc z hz) lam).eq
    rw [hlam] at h1
    calc g⁻¹ * z * g * c = g⁻¹ * (z * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * z) * g := by rw [h1]
      _ = c * (g⁻¹ * z * g) := by group
  have hgΘ : g⁻¹ ∈ Subgroup.normalizer (Θ : Set G) :=
    Subgroup.inv_mem _ (Sec6.normalizer_le_normalizer_theta C hgC)
  have hutc : (ut : G) ∉ Subgroup.zpowers c := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ((⟨c ^ k, C.zpow_mem hcC k⟩ : C) : C ⧸ θC) = (u'C : C ⧸ θC) := by
      rw [← hutq]
      congr 1
      exact Subtype.ext hk
    rw [QuotientGroup.eq] at h1
    have h2 : (c ^ k)⁻¹ * u' ∈ Θ := ⟨_, h1, rfl⟩
    have h3 := (Subgroup.mem_normalizer_iff.mp hgΘ _).mp h2
    have hd : g⁻¹ * (c ^ k)⁻¹ * g⁻¹⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp
        (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers c k))
    have e : g⁻¹ * ((c ^ k)⁻¹ * u') * g⁻¹⁻¹ = (g⁻¹ * (c ^ k)⁻¹ * g⁻¹⁻¹) * x := by
      rw [hu']
      group
    rw [e] at h3
    set d := g⁻¹ * (c ^ k)⁻¹ * g⁻¹⁻¹ with hd'
    have hdL : d ∈ L := Subgroup.zpowers_le.mpr hcL hd
    have h4 : d * x ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [hθL]
      exact ⟨L.mul_mem hdL x.2, h3⟩
    obtain ⟨s', hs', hs'e⟩ := h4
    have h5 : π (⟨d, hdL⟩ * x) = 1 := by
      have e2 : (⟨d, hdL⟩ : L) * x = s' := Subtype.ext hs'e.symm
      rw [e2, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hs'
    rw [map_mul] at h5
    have h6 : π x = (π ⟨d, hdL⟩)⁻¹ := eq_inv_of_mul_eq_one_right h5
    have h7 : π ⟨d, hdL⟩ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hd
      have e3 : (⟨d, hdL⟩ : L) = ⟨c, hcL⟩ ^ j :=
        Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj.symm)
      rw [e3, map_zpow]
      exact Subgroup.zpow_mem _ hcZ j
    have h8 := hind' 1 0 (by
      rw [pow_one, pow_zero, mul_one, h6]
      exact Subgroup.inv_mem _ h7)
    exact absurd h8.1 (by norm_num)
  have hut1 : (ut : G) ≠ 1 := fun h1 => hutc (h1 ▸ Subgroup.one_mem _)
  have hutO : orderOf (ut : G) = 3 := orderOf_eq_prime hut3G hut1
  have hE₁card : Nat.card E₁ = 9 := by
    rw [hE₁, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hutN
      (disjoint_zpowers_of_not_mem hut3G hutc), Nat.card_zpowers, Nat.card_zpowers, hco, hutO]
  set A' : Subgroup (C ⧸ θC) := (L'.subgroupOf C).map (QuotientGroup.mk' θC) with hA'
  have hA'mem : ∀ (z : G) (hz : z ∈ L'), ((⟨z, hL'C hz⟩ : C) : C ⧸ θC) ∈ A' :=
    fun z hz => ⟨⟨z, hL'C hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have hE₁A' : E₁ ≤ (A'.comap (QuotientGroup.mk' θC)).map C.subtype := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨⟨c, hcC⟩, hA'mem c hcL', rfl⟩)
      (Subgroup.zpowers_le.mpr ⟨ut, ?_, rfl⟩)
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply, hutq]
    exact hA'mem u' hu'L'
  have hπy9 : π y ^ (9 : ℤ) = 1 := by
    have h1 : vb ^ 9 = 1 := by simpa using hvb9
    rw [hyv, show (9 : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, h1]
  have hzpow : ∀ k : ℤ, π y ^ k = π y ^ (k % 9).toNat := by
    intro k
    rw [zpow_eq_zpow_emod k hπy9, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
  have hdvd : ∀ k : ℤ, 3 ∣ (k % 9).toNat → (3 : ℤ) ∣ k := by
    intro k hk
    have h1 : (((k % 9).toNat : ℕ) : ℤ) = k % 9 :=
      Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
    have h2 : (3 : ℤ) ∣ (((k % 9).toNat : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hk
    rw [h1] at h2
    omega
  have hwE₁ : w ∉ E₁ := by
    intro hmem
    obtain ⟨wC, hwC', hwCe⟩ := hE₁A' hmem
    have e1 : wC = vt * (⟨v₀, hLC hv₀L⟩ : C)⁻¹ := Subtype.ext hwCe
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply, e1, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hvtq] at hwC'
    have h2 : ((⟨v₀, hLC hv₀L⟩ : C) : C ⧸ θC) ∈ A' := by
      have h3 := A'.mul_mem (A'.inv_mem hwC') (hA'mem v' hv'L')
      rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h3
    obtain ⟨z, hz, hze⟩ := h2
    have h4 := hcen v₀ hv₀L z (Subgroup.mem_subgroupOf.mp hz) hze.symm
    have e2 : (⟨v₀, hv₀L⟩ : L) = y ^ lam := Subtype.ext (by rw [Subgroup.coe_zpow])
    rw [e2, map_zpow, hzpow] at h4
    have h5 := hind' 0 _ (by rwa [pow_zero, one_mul])
    exact hlam3 (hdvd lam h5.2)
  have hw1 : w ≠ 1 := fun h1 => hwE₁ (h1 ▸ Subgroup.one_mem _)
  have hwO : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hEcard : Nat.card E = 27 := by
    rw [hE, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hwN
      (disjoint_zpowers_of_not_mem hw3 hwE₁), hE₁card, Nat.card_zpowers, hwO]
  have hEC : E ≤ C := sup_le (sup_le (Subgroup.zpowers_le.mpr hcC) (Subgroup.zpowers_le.mpr hutC))
    (Subgroup.zpowers_le.mpr hwC)
  have hwCe : (⟨w, hwC⟩ : C) = vt * (⟨v₀, hLC hv₀L⟩ : C)⁻¹ := Subtype.ext rfl
  have hv₀t₂ : Commute v₀ (t₂ : G) := by
    rw [hv₀]
    exact (show Commute (y : G) t₂ from ht₂y.symm).zpow_left lam
  have hESt : E ≤ ((Subgroup.centralizer {((⟨t₂, hLC t₂.2⟩ : C) : C ⧸ θC)}).comap
      (QuotientGroup.mk' θC)).map C.subtype := by
    refine sup_le (sup_le (Subgroup.zpowers_le.mpr ⟨⟨c, hcC⟩, ?_, rfl⟩)
      (Subgroup.zpowers_le.mpr ⟨ut, ?_, rfl⟩)) (Subgroup.zpowers_le.mpr ⟨⟨w, hwC⟩, ?_, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
        QuotientGroup.mk'_apply]
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hCc _ (hLC t₂.2)).symm
    · rw [hutq]
      exact (hQ t₂ t₂.2 u' hu'L').symm
    · rw [hwCe, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hvtq]
      have h1 : Commute (v'C : C ⧸ θC) ((⟨t₂, hLC t₂.2⟩ : C) : C ⧸ θC) :=
        (hQ t₂ t₂.2 v' hv'L').symm
      have h2 : Commute ((⟨v₀, hLC hv₀L⟩ : C) : C ⧸ θC) ((⟨t₂, hLC t₂.2⟩ : C) : C ⧸ θC) :=
        (show Commute (⟨v₀, hLC hv₀L⟩ : C) ⟨t₂, hLC t₂.2⟩ from Subtype.ext hv₀t₂).map
          (QuotientGroup.mk' θC)
      exact (h1.mul_left h2.inv_left).eq
  have hP₃ : IsPGroup 3 (E.subgroupOf C) := by
    intro p
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hEel.2 _ (Subgroup.mem_subgroupOf.mp p.2)
  obtain ⟨t₃, ht₃q, ht₃c⟩ := exists_commute_of_mk_commute hP₃ (y := ⟨t₂, hLC t₂.2⟩) (by
    intro p hp
    obtain ⟨p', hp', hp'e⟩ := hESt (Subgroup.mem_subgroupOf.mp hp)
    have e : p' = p := Subtype.ext hp'e
    rw [e, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      QuotientGroup.mk'_apply] at hp'
    exact hp')
  obtain ⟨q', s', hq', ht₃s⟩ := exists_odd_pow_two_pow_eq_one t₃
  set t₄ := t₃ ^ q' with ht₄
  have ht₂C2 : (⟨t₂, hLC t₂.2⟩ : C) ^ 2 ^ s = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using congrArg Subtype.val hts)
  have ht₄1 : (t₄ : G) ≠ 1 := by
    intro h1
    have h2 : t₄ = 1 := Subtype.ext h1
    have h3 : ((⟨t₂, hLC t₂.2⟩ : C) : C ⧸ θC) ^ q' = 1 := by
      rw [← ht₃q, ← QuotientGroup.mk_pow, ← ht₄, h2, QuotientGroup.mk_one]
    have h4 : ((⟨t₂, hLC t₂.2⟩ : C) : C ⧸ θC) ^ 2 ^ s = 1 := by
      rw [← QuotientGroup.mk_pow, ht₂C2, QuotientGroup.mk_one]
    have h5 : orderOf ((⟨t₂, hLC t₂.2⟩ : C) : C ⧸ θC) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right s hq'.coprime_two_right)
        (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h4)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h5
    exact ht₂Θ ((hmemΘ _ (hLC t₂.2)).mpr h5)
  have ht₄2 : (t₄ : G) ^ 2 ^ s' = 1 := by
    have h1 := congrArg Subtype.val ht₃s
    simpa [ht₄] using h1
  have hU2 : IsPGroup 2 (Subgroup.zpowers (t₄ : G)) := isPGroup_zpowers_of_pow ht₄2
  have hU1 : Subgroup.zpowers (t₄ : G) ≠ ⊥ := by
    intro h1
    apply ht₄1
    rw [← Subgroup.mem_bot, ← h1]
    exact Subgroup.mem_zpowers _
  have hEU : E ≤ Subgroup.normalizer (Subgroup.zpowers (t₄ : G) : Set G) := by
    intro e he
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have h1 : (⟨e, hEC he⟩ : C) * t₃ = t₃ * ⟨e, hEC he⟩ :=
      ht₃c _ (Subgroup.mem_subgroupOf.mpr he)
    have h2 : (⟨e, hEC he⟩ : C) * t₄ = t₄ * ⟨e, hEC he⟩ := by
      rw [ht₄]
      exact (Commute.pow_right h1 q').eq
    have h3 : e * (t₄ : G) = t₄ * e := congrArg Subtype.val h2
    rw [h3, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _
  have hEmem : E ∈ partTwoE G := ⟨hEel, hEcard, _, hU1, hU2, hEU⟩
  have hEF : E ∈ partTwoF G := by
    rw [← h.partTwoE_eq h.card_eq]
    exact hEmem
  have hExc : E ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact hxc.symm.eq
    · exact hxut.symm.eq
    · exact hxw.symm.eq
  have hx3G : (x : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  have hxE' : (x : G) ∈ E := mem_of_commute_of_maximal hEF.1 hEF.2.1 hx3G
    (fun e he => (Subgroup.mem_centralizer_singleton_iff.mp (hExc he)).symm)
  set W : Subgroup (C ⧸ θC) := A' ⊔ Subgroup.zpowers (((⟨y, hLC y.2⟩ : C)) : C ⧸ θC) with hW
  have hEW : E ≤ (W.comap (QuotientGroup.mk' θC)).map C.subtype := by
    refine sup_le (hE₁A'.trans (Subgroup.map_mono (Subgroup.comap_mono le_sup_left)))
      (Subgroup.zpowers_le.mpr ⟨⟨w, hwC⟩, ?_, rfl⟩)
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply, hwCe, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hvtq]
    refine W.mul_mem (Subgroup.mem_sup_left (hA'mem v' hv'L'))
      (W.inv_mem (Subgroup.mem_sup_right ?_))
    have e : (⟨v₀, hLC hv₀L⟩ : C) = ⟨y, hLC y.2⟩ ^ lam := Subtype.ext (by rw [Subgroup.coe_zpow])
    rw [e, QuotientGroup.mk_zpow]
    exact Subgroup.zpow_mem_zpowers _ lam
  obtain ⟨xC, hxC, hxCe⟩ := hEW hxE'
  rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply] at hxC
  have hyA'N : Subgroup.zpowers (((⟨y, hLC y.2⟩ : C)) : C ⧸ θC) ≤
      Subgroup.normalizer (A' : Set (C ⧸ θC)) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (hQ y y.2 z (Subgroup.mem_subgroupOf.mp hz)).symm
  obtain ⟨b, hb, a'', ha'', hba⟩ := exists_mul_of_mem_sup hyA'N hxC
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  obtain ⟨z, hz, rfl⟩ := ha''
  have e1 : xC = ⟨x, hLC x.2⟩ := Subtype.ext hxCe
  have hyjx : (y : G) ^ (-j) * x ∈ L := L.mul_mem (L.zpow_mem y.2 _) x.2
  have hX : ((⟨(y : G) ^ (-j) * x, hLC hyjx⟩ : C) : C ⧸ θC) =
      ((⟨z, hL'C (Subgroup.mem_subgroupOf.mp hz)⟩ : C) : C ⧸ θC) := by
    have e2 : (⟨(y : G) ^ (-j) * x, hLC hyjx⟩ : C) = ⟨y, hLC y.2⟩ ^ (-j) * ⟨x, hLC x.2⟩ :=
      Subtype.ext (by simp)
    rw [e2, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← e1, ← hba, ← mul_assoc, ← zpow_add,
      neg_add_cancel, zpow_zero, one_mul]
    rfl
  have h1 := hcen _ hyjx z (Subgroup.mem_subgroupOf.mp hz) hX
  have e3 : (⟨(y : G) ^ (-j) * x, hyjx⟩ : L) = y ^ (-j) * x := Subtype.ext (by simp)
  rw [e3, map_mul, map_zpow] at h1
  have hxyQ : Commute (π x) (π y) := (show Commute x y from hxy).map π
  have h2 : π x * π y ^ ((-j) % 9).toNat ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [← hzpow, (hxyQ.zpow_right (-j)).eq]
    exact h1
  have h3 := hind' 1 _ (by rwa [pow_one])
  exact absurd h3.1 (by norm_num)

theorem apply_eq_self_of_card_center {X : Type*} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3) {τ : MulAut X} (hτ : τ ^ 3 = 1) {z : X}
    (hz : z ∈ Subgroup.center X) : τ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hz3 : z ^ 3 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center X)
    rw [hZ, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hzp : Subgroup.zpowers z = Subgroup.center X := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hZ, Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  have hτz : τ z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    have h1 := hz (τ.symm w)
    calc w * τ z = τ (τ.symm w) * τ z := by rw [MulEquiv.apply_symm_apply]
      _ = τ (τ.symm w * z) := by rw [map_mul]
      _ = τ (z * τ.symm w) := by rw [h1]
      _ = τ z * w := by rw [map_mul, MulEquiv.apply_symm_apply]
  rw [← hzp] at hτz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτz
  have hz3' : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  rw [zpow_eq_zpow_emod k hz3'] at hk
  have hk' : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk' with hk' | hk' | hk' <;> rw [hk'] at hk
  · exfalso
    apply hz1
    rw [zpow_zero] at hk
    exact τ.injective (by rw [← hk, map_one])
  · rw [zpow_one] at hk
    exact hk.symm
  · exfalso
    have e1 : τ z = z ^ 2 := by rw [← hk]; norm_cast
    have e2 : τ (τ z) = z := by
      rw [e1, map_pow, e1, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz3, one_mul,
        pow_one]
    have e3 : (τ ^ 3) z = τ (τ (τ z)) := by
      rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply]
    rw [hτ, MulAut.one_apply, e2, e1] at e3
    apply hz1
    have e4 : z * z = z * 1 := by rw [mul_one, ← pow_two]; exact e3.symm
    exact mul_left_cancel e4

end Core

theorem Hyp92.exists_mem_center (h45 : Sec4.Item4_5) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G} {n : ℕ}
    (h : Hyp92 G A c L a R n) :
    ∃ hcL : c ∈ L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := h.one_le
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hAmax := h.mem_partTwoF.2.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAel.2
  have hcA := h.mem_A
  have hc3 := hexp c hcA
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAel hcA h.ne_one L
      h.mem_thetaComponentsAt
  have hZ3 := KFacts.card_center_of_isSLThreePiAt hn h.isSLThreePiAt
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L), z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [h1, Subgroup.card_bot] at hZ3
    norm_num at hZ3
  have hz3 : z ^ 3 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨z, hzZ⟩ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))
    rw [hZ3, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hzfix : ∀ y (hy : y ∈ A), Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨y, hAL hy⟩) z = z := by
    intro y hy
    refine apply_eq_self_of_card_center hZ3 ?_ hzZ
    have h1 : (⟨y, hAL hy⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hexp y hy)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨d, hdL, hdA, hdz⟩ := KFacts.exists_mem_of_fixed_of_pow_three hAel hAmax hAL hz3 hzfix
  have hdN := hAL hdA
  have hd1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) = 1 := by
    rw [KFacts.thetaQuotMulAut_compAction_of_mem hdL hdN, hdz]
    ext w
    rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.mp hzZ w),
      mul_inv_cancel_right]
  have hdc : d ∈ Subgroup.zpowers c := h.mem_zpowers_of_eq_one hdA hdN hd1
  have hd1' : d ≠ 1 := by
    rintro rfl
    exact hz1 (hdz.symm.trans (map_one _))
  have hcd : c ∈ Subgroup.zpowers d := mem_zpowers_of_mem_zpowers_of_ne_one hc3 hdc hd1'
  have hcL : c ∈ L := Subgroup.zpowers_le.mpr hdL hcd
  have hcZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcd
    have e : (⟨c, hcL⟩ : L) = ⟨d, hdL⟩ ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [e, map_zpow, hdz]
    exact Subgroup.zpow_mem _ hzZ k
  have hc1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow h1 (j := 1)
      (Subtype.ext (by simpa using hc3))
    exact h.ne_one (congrArg Subtype.val h2)
  exact ⟨hcL, hcZ, hc1⟩

theorem hyp92NormalizerL_of (h45 : Sec4.Item4_5) : Hyp92NormalizerL := by
  intro G _ _ A c L a R n h g hg
  obtain ⟨hcL, hcZ, hc1⟩ := h.exists_mem_center h45
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  exact h.false_of_map_conj_ne hcL hcZ hc1 hg hne

theorem transferExtremal : TransferExtremal := fun _ _ _ _ _ P _ habel _ hx hxN hxp hfus =>
  Sec8.commutator_ne_top_of_extremal P habel hx hxN hxp hfus

theorem hyp92InvTwo_of (h45 : Sec4.Item4_5) : Hyp92InvTwo := fun _ _ _ _ _ L _ _ h =>
  KFacts.not_invTwoBarNontrivial_of_hyp92_one h
    (Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 h.mem_A
      h.ne_one L h.mem_thetaComponentsAt)

theorem hyp92FixedCore_of (h45 : Sec4.Item4_5) : Hyp92FixedCore :=
  fun _ _ _ _ _ L _ _ h _ heA hec he N hNc hN3 hNn =>
    KFacts.eq_bot_of_hyp92_one h
      (Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1
        h.mem_A h.ne_one L h.mem_thetaComponentsAt) heA hec he N hNc hN3 hNn

theorem item93_of_item45 (h45 : Sec4.Item4_5) : Item93 :=
  item93_of h45 (hyp92InvTwo_of h45) (hyp92FixedCore_of h45) (hyp92NormalizerL_of h45)

theorem hyp92Never_of_item45 (h95 : Item95) (h45 : Sec4.Item4_5) (hK1 : SLPiInndiag)
    (hK2 : SLPiSylowFixed) (hK3 : SLPiFieldSylowFixed) : Hyp92Never :=
  hyp92Never_of h95 (hyp92NormalizerL_of h45) hK1 hK2 hK3 transferExtremal

end CFSG.RankThree.PartTwo.Sec9
