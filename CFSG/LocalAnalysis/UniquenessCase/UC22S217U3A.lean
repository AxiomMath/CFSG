module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.UCKP898A
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217u3a_two_pow_mod_five {m : ℕ} (hm : 4 ∣ m) : 2 ^ m % 5 = 1 := by
  obtain ⟨t, rfl⟩ := hm
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem uc22s217u3a_pow_two_cases {n : ℕ} (hn : IsPowTwo n) (hn2 : 2 ≤ n) : n = 2 ∨ 4 ∣ n := by
  obtain ⟨k, rfl⟩ := hn
  rcases k with _ | _ | k
  · norm_num at hn2
  · left
    norm_num
  · right
    exact ⟨2 ^ k, by ring⟩

theorem uc22s217u3a_eq_two_of_five_dvd {n : ℕ} (hn : IsPowTwo n) (hn2 : 2 ≤ n)
    (h5 : 5 ∣ 2 ^ n + 1) : n = 2 := by
  rcases uc22s217u3a_pow_two_cases hn hn2 with h | h
  · exact h
  · have := uc22s217u3a_two_pow_mod_five h
    omega

theorem uc22s217u3a_not_dvd_card {n s r : ℕ} (hn : IsPowTwo n) (hs : Odd s) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) :
    ¬ r ∣ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  haveI : Fact (2 < r) := ⟨by omega⟩
  obtain ⟨k, rfl⟩ := hn
  have h2s : (2 : ZMod r) ^ s = 1 := by
    have h1 : ((2 ^ s - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrs
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] at h1
    exact h1
  have hs2 : Nat.Coprime 2 s := Nat.coprime_two_left.2 hs
  intro hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  ·
    rw [← pow_mul] at h
    have h2n : (2 : ZMod r) ^ (2 ^ k * 2) = 1 := by
      have h1 : ((2 ^ (2 ^ k * 2) - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        sub_eq_zero] at h1
      exact h1
    have hg : Nat.gcd s (2 ^ k * 2) = 1 := by
      rw [Nat.Coprime.gcd_mul_right_cancel_right _ hs2]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hs)
    have h21 : (2 : ZMod r) ^ Nat.gcd s (2 ^ k * 2) = 1 := pow_gcd_eq_one.2 ⟨h2s, h2n⟩
    rw [hg, pow_one] at h21
    have h10 : (1 : ZMod r) = 0 := by linear_combination h21
    exact one_ne_zero h10
  ·
    rw [← pow_mul] at h
    have h3n : (2 : ZMod r) ^ (2 ^ k * 3) = -1 := by
      have h1 : ((2 ^ (2 ^ k * 3) + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h1
      linear_combination h1
    have h6n : (2 : ZMod r) ^ (2 ^ k * 3 * 2) = 1 := by
      rw [pow_mul, h3n]
      norm_num
    have h21 : (2 : ZMod r) ^ Nat.gcd s (2 ^ k * 3 * 2) = 1 := pow_gcd_eq_one.2 ⟨h2s, h6n⟩
    rw [Nat.Coprime.gcd_mul_right_cancel_right _ hs2] at h21
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right s (2 ^ k * 3)
    have h31 : (2 : ZMod r) ^ (2 ^ k * 3) = 1 := by
      rw [ht, pow_mul, h21, one_pow]
    rw [h3n] at h31
    exact ZMod.neg_one_ne_one h31

theorem uc22s217u3a_not_dvd_card_of (hCen : UCK.U3Center) {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSU3 X n) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hrn : ¬ r ∣ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))) : ¬ r ∣ Nat.card X := by
  intro h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)] at h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · exact hrn (h.trans (Dvd.intro _ (StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
      (CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2))))
  · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (h.trans (hCen X n hX)))

theorem uc22s217u3a_exists_card_eq {K : Subgroup G} {n : ℕ} (hX : IsSU3 (Bar2 K) n) {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (hrn : r ∣ (2 ^ n) ^ 2 - 1) :
    ∃ X₀ : Subgroup G, X₀ ≤ K ∧ Nat.card X₀ = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h1 : r ∣ Nat.card (Bar2 K ⧸ center (Bar2 K)) * Nat.gcd 3 (2 ^ n + 1) := by
    rw [StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
      (CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2)]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hrn _) _
  have hcop : Nat.Coprime r (Nat.gcd 3 (2 ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _)
      ((Nat.coprime_primes hr Nat.prime_three).2 hr3)
  have h2 : r ∣ Nat.card ↥K :=
    ((hcop.dvd_of_dvd_mul_right h1).trans (Subgroup.card_quotient_dvd_card _)).trans
      (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r h2
  refine ⟨zpowers (x : G), Subgroup.zpowers_le.2 x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

theorem uc22s217u3a_inner {K : Subgroup G} {n : ℕ} (hX : IsSU3 (Bar2 K) n) (hn : IsPowTwo n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) {y : G}
    (hyN : y ∈ normalizer (K : Set G)) (hyr : orderOf y = r) :
    rhoL K ⟨y, hyN⟩ ^ r = 1 ∧
      rhoL K ⟨y, hyN⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  have hαr : rhoL K ⟨y, hyN⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) ^ r = 1 :=
      Subtype.ext (by simpa using (hyr ▸ pow_orderOf_eq_one y))
    rw [this, map_one]
  refine ⟨hαr, ?_⟩
  by_contra hα
  obtain ⟨_, _, _, _, _, _, -, hrn, -⟩ := UCK.u3_prime_descent hX hr hr2 hr3 hαr hα
  obtain ⟨k, rfl⟩ := hn
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hrn))

theorem uc22s217u3a_fix (hCen : UCK.U3Center) {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSU3 X n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrq : 2 ^ n % r = 1)
    {α : MulAut X} (hαr : α ^ r = 1) (hα : α ∈ (MulAut.conj : X →* MulAut X).range) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) : ∃ z : X, orderOf z = q ∧ α z = z := by
  have hn2 : 2 ≤ n := UCK.u3Range X n hX
  have hZ3 : ∀ z ∈ center X, z ^ 3 = 1 := fun z hz =>
    UCK.pow_three_eq_one_of_mem_center (hCen X n hX) hz
  have hcop : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3)
  have hr3' : 3 ≤ r := by
    have := hr.two_le
    omega
  obtain ⟨x, hx, hxr⟩ := UCK.exists_inner_gen_pow_eq_one hZ3 hr.one_lt hcop hαr hα
  have hxbar : (QuotientGroup.mk x : X ⧸ center X) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow, hxr, QuotientGroup.mk_one]
  obtain ⟨zb, hzb, hzbx⟩ := UCK.fixed_inner_of_isU3 hn2 hX.2 hr hr3' hrq hxbar hq hq3 hqn
  obtain ⟨z, hz, hzmk⟩ := UCK.exists_prime_order_lift hZ3 hq hq3 hzb
  refine ⟨z, hz, ?_⟩
  have hzq : z ^ q = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  rw [← hx, MulAut.conj_apply]
  exact UCK.conj_eq_of_commute_mod_center hZ3 hq hq3 hzq (by rw [hzmk]; exact hzbx)

theorem uc22s217u3a_centralizesBar (hCen : UCK.U3Center) {K : Subgroup G} {n : ℕ}
    (hX : IsSU3 (Bar2 K) n) (hn : IsPowTwo n) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrn : ¬ r ∣ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))) {y : G}
    (hyN : y ∈ normalizer (K : Set G)) (hyr : orderOf y = r) : CentralizesBar y K := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  obtain ⟨hαr, hα⟩ := uc22s217u3a_inner hX hn hr hr2 hr3 hyN hyr
  have hZ3 : ∀ z ∈ center (Bar2 K), z ^ 3 = 1 := fun z hz =>
    UCK.pow_three_eq_one_of_mem_center (hCen (Bar2 K) n hX) hz
  have hcop : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3)
  obtain ⟨x, hx, hxr⟩ := UCK.exists_inner_gen_pow_eq_one hZ3 hr.one_lt hcop hαr hα
  have hx1 : x = 1 := by
    by_contra hx1
    have hxo : orderOf x = r := orderOf_eq_prime hxr hx1
    exact uc22s217u3a_not_dvd_card_of hCen hX hr hr3 hrn (hxo ▸ orderOf_dvd_natCard x)
  have hρ : rhoL K ⟨y, hyN⟩ = 1 := by rw [← hx, hx1, map_one]
  refine ⟨hyN, fun l hl => ?_⟩
  exact (rhoL_fix_iff K ⟨y, hyN⟩ ⟨l, hl⟩).1 (by rw [hρ]; rfl)

theorem uc22s217u3a_le_conjClosure {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    K ≤ conjClosure M L :=
  le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) K hK le_rfl

theorem uc22s217u3a_sig (D : Data G) (hSg : SigmaStd D) (hCen : UCK.U3Center) (hSyl : UCK.U3Syl)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ}
    (hX : IsSU3 (Bar2 L) n) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) :
    q ∈ D.sig ∧ IsStronglyPEmbedded q D.M ∧ 2 ≤ CFSG.Open.pRank q (conjClosure D.M L) := by
  have hq2 : q ≠ 2 := by omega
  have hZq : ¬ q ∣ Nat.card (center (Bar2 L)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (hCen _ n hX))
    omega
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  obtain ⟨E, hEL, hEel, hEc⟩ := exists_elemAbelian_sq_of_isSU3 hSyl hX hq hq3 hqn
  have h4 := calCRankTwice D.M L hL hnN' q hq hq2 hZq E hEL hEel 2 hEc
  have hqσ : q ∈ D.sig := hSg.four_mem q hq hq2 (by omega)
  exact ⟨hqσ, sp_of_mem_sig hSg (not_solvable_of_mem_calC hL) hqσ,
    le_pRank' hq (hEL.trans (uc22s217u3a_le_conjClosure ⟨1, D.M.one_mem, by ext; simp⟩)) hEel
      hEc⟩

theorem uc22s217u3a_two_pow_twelve_dvd (hCen : UCK.U3Center) {M L : Subgroup G}
    (hL : L ∈ calC M) (hnN : ¬ (L.subgroupOf M).Normal) (hX : IsSU3 (Bar2 L) 2) :
    2 ^ 12 ∣ Nat.card (Bar2 (conjClosure M L)) := by
  classical
  have hLM : L ≤ M := hL.1.le
  have hnN' : ¬ M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h)
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN'
  let f : MulAut G := MulAut.conj m
  have hMf : M.map f.toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hL' : L.map f.toMonoidHom ∈ calC M := calC_map M f hMf hL
  have hne : L ≠ L.map f.toMonoidHom := fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he.symm)
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  set X := conjClosure M L with hXdef
  have hLX : L ≤ X := uc22s217u3a_le_conjClosure ⟨1, M.one_mem, by ext; simp⟩
  have hL'X : L.map f.toMonoidHom ≤ X := uc22s217u3a_le_conjClosure ⟨m, hmM, rfl⟩
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set F₀ : Subgroup (Bar2 M) := (L.subgroupOf M).map π with hF₀
  set F₁ : Subgroup (Bar2 M) := ((L.map f.toMonoidHom).subgroupOf M).map π with hF₁
  have hcomm : ∀ a ∈ F₀, ∀ b ∈ F₁, a * b = b * a := uc22p22l_barImage_commute hL hL' hne
  obtain ⟨hsn₀, -, -, hcen₀⟩ := calC_subgroupOf hL
  obtain ⟨hsn₁, -, -, -⟩ := calC_subgroupOf hL'
  have hcard₀ : Nat.card F₀ = Nat.card (Bar2 L) :=
    Nat.card_congr ((barIso hsn₀).symm.trans (bar2Equiv (Subgroup.subgroupOfEquivOfLe hLM))).toEquiv
  have hcard₁ : Nat.card F₁ = Nat.card (Bar2 L) :=
    Nat.card_congr (((barIso hsn₁).symm.trans
      (bar2Equiv (Subgroup.subgroupOfEquivOfLe hL'.1.le))).trans
        (bar2Equiv (Subgroup.equivMapOfInjective L f.toMonoidHom f.injective)).symm).toEquiv
  have h62400 : Nat.card (Bar2 L ⧸ center (Bar2 L)) = 62400 := by
    have h := StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
      (CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2)
    norm_num at h
    exact h
  have h64 : 2 ^ 6 ∣ Nat.card (Bar2 L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Bar2 L)), h62400]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hint : Nat.card ↥(F₁ ⊓ F₀) ∣ 3 := by
    have hle : (F₁ ⊓ F₀).subgroupOf F₀ ≤ center ↥F₀ := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y.1 y.2 z.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hz)).1)
    have h1 : Nat.card ↥((F₁ ⊓ F₀).subgroupOf F₀) = Nat.card ↥(F₁ ⊓ F₀) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h2 : Nat.card (center ↥F₀) = Nat.card (center (Bar2 L)) := by
      rw [← hcen₀]
      exact (Nat.card_congr (Subgroup.centerCongr (barIso hsn₀)).toEquiv).symm
    rw [← h1]
    exact (Subgroup.card_dvd_of_le hle).trans (by rw [h2]; exact hCen (Bar2 L) 2 hX)
  have hF₀N : F₀ ≤ normalizer (F₁ : Set (Bar2 M)) :=
    le_trans (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
      (centralizer_le_normalizer _)
  have hsupc := PartTwo.card_sup_mul_card_inf_of_le_normalizer hF₀N
  have h12 : 2 ^ 12 ∣ Nat.card ↥(F₀ ⊔ F₁) := by
    have h1 : 2 ^ 12 ∣ Nat.card ↥(F₀ ⊔ F₁) * Nat.card ↥(F₁ ⊓ F₀) := by
      rw [hsupc, hcard₀, hcard₁, show (2 : ℕ) ^ 12 = 2 ^ 6 * 2 ^ 6 by norm_num]
      exact Nat.mul_dvd_mul h64 h64
    have hcop : Nat.Coprime (2 ^ 12) (Nat.card ↥(F₁ ⊓ F₀)) :=
      Nat.Coprime.coprime_dvd_right hint (by norm_num)
    exact hcop.dvd_of_dvd_mul_right h1
  let ψ : ↥X →* Bar2 M := π.comp (Subgroup.inclusion hXM)
  have hsup : F₀ ⊔ F₁ ≤ ψ.range := by
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨a, hLX (Subgroup.mem_subgroupOf.1 ha)⟩, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨a, hL'X (Subgroup.mem_subgroupOf.1 ha)⟩, rfl⟩
  have hsubX : IsSubnormal X M := CFSG.Quasithin.A3.subnormal_of_normal hXM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX)
  have hO : pCoreOf 2 X ≤ pCoreOf 2 M := uc22p22r_pCoreOf_le_of_isSubnormal hsubX
  have hker : CFSG.pCore 2 ↥X ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show π (Subgroup.inclusion hXM x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hO ⟨x, hx, rfl⟩
    have : y = Subgroup.inclusion hXM x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hXbar : Nat.card ψ.range ∣ Nat.card (Bar2 X) := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  exact h12.trans ((Subgroup.card_dvd_of_le hsup).trans hXbar)

theorem uc22s217u3a_false_of_sp (D : Data G) (Ch : Choice2011 G) (hH : H1930 D) (c : Ctx21 D Ch)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ c.n - 1) (hsp : IsStronglyPEmbedded p D.M) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpB : p ∣ Nat.card c.B0 := by
    have : p ∈ piSet c.B0 := by rw [c.hpi]; exact ⟨hp, hpn⟩
    exact this.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p hpB
  have hAB : zpowers (b : G) ≤ c.B0 := Subgroup.zpowers_le.2 b.2
  have hAc : Nat.card (zpowers (b : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hb]
  have hA1 : zpowers (b : G) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hAc
    exact hp.one_lt.ne hAc
  exact s21_2 D Ch hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers (b : G)) hAB
    (hsp.normalizer_le hA1 (IsPGroup.of_card (n := 1) (by rw [hAc, pow_one])) (hAB.trans c.hBM))

end CFSG.LocalAnalysis.UniquenessCase.UC22
