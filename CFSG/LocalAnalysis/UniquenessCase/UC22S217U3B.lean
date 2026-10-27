module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S898g
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC6S846
  CFSG.LocalAnalysis.UniquenessCase.UC6S898
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s217u3b_exists_sr {n : ℕ} (hn0 : n ≠ 0) (hn : ¬ IsPowTwo n) :
    ∃ s r : ℕ, Odd s ∧ s ∣ n ∧ r.Prime ∧ r ∣ 2 ^ s - 1 ∧ ¬ r ∣ n := by
  classical
  have hPne : (n.primeFactors.filter Odd).Nonempty := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, hk⟩ | ⟨p, hp, hpn, hpo⟩
    · exact absurd ⟨k, hk⟩ hn
    · exact ⟨p, Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpn, hn0⟩, hpo⟩⟩
  set s := (n.primeFactors.filter Odd).max' hPne with hsdef
  obtain ⟨hsf, hso⟩ : s ∈ n.primeFactors ∧ Odd s := Finset.mem_filter.1 (Finset.max'_mem _ hPne)
  obtain ⟨hsp, hsn, -⟩ := Nat.mem_primeFactors.1 hsf
  have hs3 : 3 ≤ s := by
    obtain ⟨k, hk⟩ := hso
    have := hsp.two_le
    omega
  have h8 : 2 ^ 3 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (n := 2 ^ s - 1) (by omega)
  refine ⟨s, r, hso, hsn, hr, hrs, fun hrn => ?_⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hr5 : 5 ≤ r := prime_ne_two_three_of_dvd hr hso hrs
  have h2s : (2 : ZMod r) ^ s = 1 := by
    have h1 : ((2 ^ s - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrs
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] at h1
    exact h1
  have h20 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod r) = 0 := by rw [Nat.cast_ofNat]; exact h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h1)
    omega
  have hord : orderOf (2 : ZMod r) = s := by
    rcases (Nat.dvd_prime hsp).1 (orderOf_dvd_of_pow_eq_one h2s) with h | h
    · exfalso
      have h21 : ((2 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
        rw [Nat.cast_ofNat, Nat.cast_one]
        exact orderOf_eq_one_iff.1 h
      have h3 := (ZMod.natCast_eq_natCast_iff' 2 1 r).1 h21
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
      omega
    · exact h
  have hsr : s ∣ r - 1 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one h20
  have hrP : r ∈ n.primeFactors.filter Odd :=
    Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hr, hrn, hn0⟩, hr.odd_of_ne_two (by omega)⟩
  have hrle : r ≤ s := Finset.le_max' _ r hrP
  have := Nat.le_of_dvd (by omega) hsr
  omega

theorem uc22s217u3b_inner (hFF : UCK.U3FixField) {K : Subgroup G} {n : ℕ}
    (hX : IsSU3 (Bar2 K) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) (hrn : ¬ r ∣ n) {y : G} (hyN : y ∈ normalizer (K : Set G))
    (hyr : orderOf y = r) :
    rhoL K ⟨y, hyN⟩ ^ r = 1 ∧
      rhoL K ⟨y, hyN⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  have hαr : rhoL K ⟨y, hyN⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) ^ r = 1 :=
      Subtype.ext (by simpa using (hyr ▸ pow_orderOf_eq_one y))
    rw [this, map_one]
  refine ⟨hαr, ?_⟩
  by_contra hα
  obtain ⟨m, hnm, -⟩ := hFF (Bar2 K) n hX s hs hsn r hr hrs _ hαr hα
  exact hrn ⟨m, hnm⟩

theorem uc22s217u3b_lift {K : Subgroup G} {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) {y : G} (hyN : y ∈ normalizer (K : Set G)) (hyr : orderOf y = r)
    (Eb : Subgroup (Bar2 K)) (hEb : IsPGroup q Eb) (hfix : ∀ e ∈ Eb, rhoL K ⟨y, hyN⟩ e = e) :
    ∃ A : Subgroup G, A ≤ K ∧ A ≤ centralizer (zpowers y : Set G) ∧
      (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≤ Eb ∧
        Nat.card A = Nat.card Eb ∧ (IsElemAbelian q Eb → IsElemAbelian q A) := by
  have hBN : zpowers y ≤ normalizer (K : Set G) := Subgroup.zpowers_le.2 hyN
  have hyp : IsPGroup r (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyr, pow_one])
  have hgen : ∀ b ∈ zpowers y, ∃ k : ℕ, y ^ k = b := fun b hb => mem_powers_iff_mem_zpowers.2 hb
  exact exists_lift_fixed hr hr2 hq hq2 hBN hyp Eb hEb (rho_fix_of_generator hyN hBN hgen hfix)

theorem uc22s217u3b_lift_elem {K : Subgroup G} {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) {y : G} (hyN : y ∈ normalizer (K : Set G)) (hyr : orderOf y = r)
    {z : Bar2 K} (hzo : orderOf z = q) (hz : rhoL K ⟨y, hyN⟩ z = z) :
    ∃ A : Subgroup G, A ≤ K ∧ A ≤ centralizer (zpowers y : Set G) ∧ Nat.card A = q := by
  have hzc : Nat.card (zpowers z) = q := by rw [Nat.card_zpowers, hzo]
  obtain ⟨A, hAK, hAc, -, hAcard, -⟩ := uc22s217u3b_lift hr hr2 hq hq2 hyN hyr (zpowers z)
    (IsPGroup.of_card (n := 1) (by rw [hzc, pow_one])) (fun e he => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      rw [map_zpow, hz])
  exact ⟨A, hAK, hAc, hAcard.trans hzc⟩

theorem uc22s217u3b_exists_lift_cent {M : Subgroup G} {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) {y : G} (hyM : y ∈ M) (hyr : orderOf y = r)
    {W : Subgroup (Bar2 M)} (hW : IsElemAbelian q W) {k : ℕ} (hWc : Nat.card W = q ^ k)
    (hWy : ∀ w ∈ W, Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩) w) :
    ∃ A : Subgroup G, A ≤ M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q A ∧
      Nat.card A = q ^ k := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 W hW.isPGroup
  have hQel : IsElemAbelian q Q :=
    isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hW)
  have hQc : Nat.card Q = q ^ k := by rw [← card_map_of_disjoint_ker π Q hQdisj, hQmap, hWc]
  have hOM : pCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf M)
  have hyz : zpowers y ≤ M := Subgroup.zpowers_le.2 hyM
  have hyp : IsPGroup r (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyr, pow_one])
  have hcomm : ∀ e ∈ zpowers y, ∀ a ∈ Q.map M.subtype, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
    rintro e he _ ⟨a, haQ, rfl⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hπa : π a ∈ W := by rw [← hQmap]; exact ⟨a, haQ, rfl⟩
    have hc := ((hWy _ hπa).zpow_left j).eq
    have h1 : π ((⟨y, hyM⟩ : ↥M) ^ j * a * ((⟨y, hyM⟩ : ↥M) ^ j)⁻¹ * a⁻¹) = 1 := by
      simp only [map_mul, map_inv, map_zpow]
      rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    refine ⟨_, (QuotientGroup.eq_one_iff _).1 h1, ?_⟩
    simp
  obtain ⟨A, hAc, hAle, ⟨e⟩⟩ := exists_centralizing_copy hr hr2 hq hq2 (pCoreOf 2 M)
    (Q.map M.subtype) (zpowers y) (isPGroup_pCoreOf M) ((Subgroup.map_subtype_le Q).trans hMO)
    (hyz.trans hMO) (hQp.map _) hyp hcomm
  refine ⟨A, le_inf (hAle.trans (sup_le (Subgroup.map_subtype_le Q) hOM)) hAc,
    isElemAbelian_of_mulEquiv e (hQel.map _), ?_⟩
  rw [Nat.card_congr e.toEquiv, Subgroup.card_map_of_injective M.subtype_injective, hQc]

theorem uc22s217u3b_two_cent {M K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ calC M) (hK₁ : K₁ ∈ calC M)
    (hne : K₀ ≠ K₁) {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 K₀))) {y : G} (hyM : y ∈ M) (hyr : orderOf y = r)
    {A₀ A₁ : Subgroup G} (hA₀ : A₀ ≤ K₀) (hA₁ : A₁ ≤ K₁)
    (hA₀c : A₀ ≤ centralizer (zpowers y : Set G)) (hA₁c : A₁ ≤ centralizer (zpowers y : Set G))
    (hA₀q : Nat.card A₀ = q) (hA₁q : Nat.card A₁ = q) :
    ∃ W : Subgroup G, W ≤ M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q W ∧
      Nat.card W = q ^ 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have himg : ∀ {A K : Subgroup G}, A ≤ K → K ≤ M → Nat.card A = q →
      A ≤ centralizer (zpowers y : Set G) →
      (A.subgroupOf M).map π ≤ (K.subgroupOf M).map π ∧ IsElemAbelian q ((A.subgroupOf M).map π) ∧
        Nat.card ((A.subgroupOf M).map π) = q ^ 1 ∧
          ∀ w ∈ (A.subgroupOf M).map π, Commute (π ⟨y, hyM⟩) w := by
    intro A K hAK hKM hAq hAc
    have hAM : A ≤ M := hAK.trans hKM
    have hAp : IsPGroup q (A.subgroupOf M) :=
      (IsPGroup.of_card (n := 1) (by rw [hAq, pow_one]) : IsPGroup q A).comap_subtype
    have hdisj : Disjoint (A.subgroupOf M) π.ker := Subgroup.disjoint_def.2 fun hx hk =>
      eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hAp hker hx hk
    have hc : Nat.card ((A.subgroupOf M).map π) = q := by
      rw [card_map_of_disjoint_ker π _ hdisj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hAq]
    refine ⟨Subgroup.map_mono (fun a ha => hAK ha), isElemAbelian_of_card_prime hq hc,
      by rw [hc, pow_one], ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have h1 : y * (a : G) = (a : G) * y :=
      Subgroup.mem_centralizer_iff.1 (hAc ha) y (Subgroup.mem_zpowers y)
    have h2 : (⟨y, hyM⟩ : ↥M) * a = a * ⟨y, hyM⟩ := Subtype.ext h1
    show π ⟨y, hyM⟩ * π a = π a * π ⟨y, hyM⟩
    rw [← map_mul, ← map_mul, h2]
  obtain ⟨hF₀K, hF₀el, hF₀c, hF₀y⟩ := himg hA₀ hK₀.1.le hA₀q hA₀c
  obtain ⟨hF₁K, hF₁el, hF₁c, hF₁y⟩ := himg hA₁ hK₁.1.le hA₁q hA₁c
  have hcomm : ∀ a ∈ (A₀.subgroupOf M).map π, ∀ b ∈ (A₁.subgroupOf M).map π, a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hK₀ hK₁ hne a (hF₀K ha) b (hF₁K hb)
  obtain ⟨hsn, -, -, hcen⟩ := calC_subgroupOf hK₀
  have hcen' : ¬ q ∣ Nat.card (center ↥((K₀.subgroupOf M).map π)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr (barIso hsn)).toEquiv, hcen]
    exact hZ
  have hint : (A₀.subgroupOf M).map π ⊓ (A₁.subgroupOf M).map π = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact eq_one_of_central_of_pow_eq_one hq hcen' (hF₀K hz.1)
      (fun b hb => uc22p22l_barImage_commute hK₀ hK₁ hne b hb z (hF₁K hz.2)) (hF₀el.2 z hz.1)
  obtain ⟨W, hWle, hWel, hWc⟩ :=
    exists_elemAbelian_le_sup_of_commute hq hF₀el hF₁el hF₀c hF₁c hcomm hint
  have hC : ∀ {F : Subgroup (Bar2 M)}, (∀ w ∈ F, Commute (π ⟨y, hyM⟩) w) →
      F ≤ centralizer ({π ⟨y, hyM⟩} : Set (Bar2 M)) := fun hF w hw =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hF w hw
  have hle := sup_le (hC hF₀y) (hC hF₁y)
  exact uc22s217u3b_exists_lift_cent hr hr2 hq hq2 hyM hyr hWel hWc fun w hw =>
    Subgroup.mem_centralizer_iff.1 (hle (hWle hw)) _ (Set.mem_singleton _)

theorem uc22s217u3b_exists_partner {K : Subgroup G} {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hZ3 : ∀ z ∈ center (Bar2 K), z ^ 3 = 1) {X₀ : Subgroup G} (hX₀K : X₀ ≤ K)
    (hX₀c : Nat.card X₀ = r) {x : G} (hxN : x ∈ normalizer (K : Set G)) (hxr : orderOf x = r)
    (hαr : rhoL K ⟨x, hxN⟩ ^ r = 1)
    (hα : rhoL K ⟨x, hxN⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range) :
    ∃ A : Subgroup G, A ≤ K ∧ A ≤ centralizer (zpowers x : Set G) ∧ Nat.card A = r := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hcop : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).2 (by omega)
  obtain ⟨b, hb, hbr⟩ := UCK.exists_inner_gen_pow_eq_one hZ3 hr.one_lt hcop hαr hα
  obtain ⟨Eb, hEbp, hEbc, hEbfix⟩ : ∃ Eb : Subgroup (Bar2 K), IsPGroup r Eb ∧ Nat.card Eb = r ∧
      ∀ e ∈ Eb, rhoL K ⟨x, hxN⟩ e = e := by
    by_cases hb1 : b = 1
    · let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
      have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
      have hX₀p : IsPGroup r (X₀.subgroupOf K) :=
        (IsPGroup.of_card (n := 1) (by rw [hX₀c, pow_one]) : IsPGroup r X₀).comap_subtype
      have hdisj : Disjoint (X₀.subgroupOf K) π.ker := Subgroup.disjoint_def.2 fun hx hk =>
        eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hX₀p hker hx hk
      refine ⟨(X₀.subgroupOf K).map π, hX₀p.map _, ?_, fun e _ => ?_⟩
      · rw [card_map_of_disjoint_ker π _ hdisj,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀K).toEquiv, hX₀c]
      · rw [← hb, hb1, map_one]
        rfl
    · have hbo : orderOf b = r := orderOf_eq_prime hbr hb1
      refine ⟨zpowers b, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one]),
        by rw [Nat.card_zpowers, hbo], fun e he => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      rw [← hb, MulAut.conj_apply, (Commute.self_zpow b j).eq, mul_inv_cancel_right]
  obtain ⟨A, hAK, hAc, -, hAcard, -⟩ := uc22s217u3b_lift hr hr2 hr hr2 hxN hxr Eb hEbp hEbfix
  exact ⟨A, hAK, hAc, hAcard.trans hEbc⟩

theorem uc22s217u3b_sup_elemAbelian {K : Subgroup G} {r : ℕ} (hr : r.Prime) {x : G}
    (hxr : orderOf x = r) (hxK : x ∉ K) {A : Subgroup G} (hAK : A ≤ K)
    (hAc : A ≤ centralizer (zpowers x : Set G)) (hAr : Nat.card A = r) :
    IsElemAbelian r (zpowers x ⊔ A) ∧ Nat.card ↥(zpowers x ⊔ A) = r ^ 2 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hxc : Nat.card (zpowers x) = r := by rw [Nat.card_zpowers, hxr]
  have hint : zpowers x ⊓ A = ⊥ := by
    have hdvd : Nat.card ↥(zpowers x ⊓ A) ∣ r := hxc ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : zpowers x ⊓ A = zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hxc])
      have hx : x ∈ zpowers x ⊓ A := by rw [heq]; exact Subgroup.mem_zpowers x
      exact hxK (hAK hx.2)
  have hcard : Nat.card ↥(zpowers x ⊔ A) = r ^ 2 := by
    have h := PartTwo.card_sup_mul_card_inf_of_le_normalizer
      (hAc.trans (centralizer_le_normalizer _))
    rw [hint, Subgroup.card_bot, mul_one, hxc, hAr] at h
    rw [sup_comm, h, sq]
  have hcomm : ∀ a ∈ zpowers x, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hAc hb) a ha
  obtain ⟨W, hWle, hWel, hWc⟩ := exists_elemAbelian_le_sup_of_commute hr
    (isElemAbelian_of_card_prime hr hxc) (isElemAbelian_of_card_prime hr hAr)
    (by rw [hxc, pow_one]) (by rw [hAr, pow_one]) hcomm hint
  have hWeq : W = zpowers x ⊔ A := Subgroup.eq_of_le_of_card_ge hWle (by rw [hcard, hWc])
  exact ⟨hWeq ▸ hWel, hcard⟩

theorem uc22s217u3b_exists_cent_sup {M K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ calC M)
    (hK₁ : K₁ ∈ calC M) (hne : K₀ ≠ K₁) {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) {x : G} (hxN : x ∈ normalizer (K₁ : Set G)) {z : Bar2 K₁} (hzo : orderOf z = q)
    (hxz : rhoL K₁ ⟨x, hxN⟩ z = z) {A : Subgroup G} (hAK : A ≤ K₀)
    (hEr : IsPGroup r ↥(zpowers x ⊔ A)) :
    ∃ Q : Subgroup G, Q ≤ K₁ ∧ Q ≤ centralizer ((zpowers x ⊔ A : Subgroup G) : Set G) ∧
      Nat.card Q = q := by
  classical
  have hAN : A ≤ normalizer (K₁ : Set G) :=
    hAK.trans (PartTwo.calC_le_normalizer_of_ne hK₁ hK₀ hne.symm)
  have hEN : zpowers x ⊔ A ≤ normalizer (K₁ : Set G) := sup_le (Subgroup.zpowers_le.2 hxN) hAN
  let S : Subgroup G :=
    ((MulAction.stabilizer (MulAut (Bar2 K₁)) z).comap (rhoL K₁)).map
      (normalizer (K₁ : Set G)).subtype
  have hmemS : ∀ g (hg : g ∈ normalizer (K₁ : Set G)), rhoL K₁ ⟨g, hg⟩ z = z → g ∈ S :=
    fun g hg h => ⟨⟨g, hg⟩, h, rfl⟩
  have hSfix : ∀ g ∈ S, ∀ hg : g ∈ normalizer (K₁ : Set G), rhoL K₁ ⟨g, hg⟩ z = z := by
    rintro _ ⟨g', hg', rfl⟩ hg
    exact hg'
  have hAS : A ≤ S := fun a ha => hmemS a (hAN ha) (by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective z
    rw [← hk]
    refine (rhoL_fix_iff K₁ ⟨a, hAN ha⟩ k).2 ?_
    have h1 : ⁅a, (k : G)⁆ ∈ ⁅K₀, K₁⁆ := Subgroup.commutator_mem_commutator (hAK ha) k.2
    have h2 := (PartTwo.calC_commutator_le_of_ne hK₀ hK₁ hne h1).2
    rw [commutatorElement_def] at h2
    exact h2)
  have hES : zpowers x ⊔ A ≤ S := sup_le (Subgroup.zpowers_le.2 (hmemS x hxN hxz)) hAS
  have hzc : Nat.card (zpowers z) = q := by rw [Nat.card_zpowers, hzo]
  obtain ⟨Q, hQK, hQc, -, hQcard, -⟩ := exists_lift_fixed hr hr2 hq hq2 hEN hEr (zpowers z)
    (IsPGroup.of_card (n := 1) (by rw [hzc, pow_one])) (fun b hb e he => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      rw [map_zpow, hSfix b (hES hb) (hEN hb)])
  exact ⟨Q, hQK, hQc, hQcard.trans hzc⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
