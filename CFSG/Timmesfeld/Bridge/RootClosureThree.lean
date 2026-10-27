module

public import CFSG.Timmesfeld.Bridge.RootClosureMain

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.BenderSuzuki

@[expose] def RootThreeL2Stmt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (D : Set K), IsRootInvolutionSet D →
    (∀ g : K, ∀ f ∈ D, g * f * g⁻¹ ∈ D) →
    ∀ x ∈ D, ∀ a ∈ D, ∀ b ∈ rootSet D a, a * b ∈ D → orderOf (a * x) = 3 → IsConj a b →
      IsConj a (a * b) → Subgroup.closure {x, a, b} = ⊤ →
      ∀ (N : Subgroup K) [N.Normal], IsPGroup 2 N → ∀ n : ℕ, 2 ≤ n →
        Nonempty (K ⧸ N ≃* PSL2Model n) → N = ⊥

private theorem two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem not_three_dvd_card_szModel {n : ℕ} (hn : 1 ≤ n) : ¬ 3 ∣ Nat.card (SzModel n) := by
  have hpi : ∀ x : GaloisField 2 (2 * n + 1),
      iterateFrobeniusEquiv (GaloisField 2 (2 * n + 1)) 2 (n + 1) x = x ^ 2 ^ (n + 1) :=
    fun x => by rw [iterateFrobeniusEquiv_def]
  have hcard := (External.huppert_blackburn_XI_3_3 n hn _ hpi).2.2.2.2.2.2.1
  rw [szModel_eq_suzukiMatrixGroup, hcard]
  set q := 2 ^ (2 * n + 1) with hq
  have h3 : q % 3 = 2 := two_pow_odd_mod_three n
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h'' | h''
    · omega
    · omega
  · omega

section CentralQuotient

variable {H : Type*} [Group H]

private theorem orderOf_conj' (g x : H) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem mem_zpowers_of_mul_self_eq_one {z g : H} (hz : z * z = 1) :
    g ∈ Subgroup.zpowers z ↔ g = 1 ∨ g = z := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
    rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [← two_mul, zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers g

theorem isPGroup_zpowers_of_mul_self_eq_one {z : H} (hz : z * z = 1) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  show g ^ 2 ^ 1 = 1
  rcases (mem_zpowers_of_mul_self_eq_one hz).1 hg with rfl | rfl
  · rw [one_pow]
  · rw [pow_one, sq, hz]

@[expose] def quotSet (F : Set H) (z : H) : Set (H ⧸ Subgroup.zpowers z) :=
  (fun c : H => (c : H ⧸ Subgroup.zpowers z)) '' {c | c ∈ F ∧ c ≠ z}

variable {F : Set H} {z : H}

theorem mk_eq_one_iff_of_mul_self (hz : z * z = 1) [(Subgroup.zpowers z).Normal] {g : H} :
    (g : H ⧸ Subgroup.zpowers z) = 1 ↔ g = 1 ∨ g = z := by
  rw [QuotientGroup.eq_one_iff, mem_zpowers_of_mul_self_eq_one hz]

theorem isRootInvolutionSet_quotSet (hF : IsRootInvolutionSet F) (hz2 : z * z = 1)
    [(Subgroup.zpowers z).Normal] : IsRootInvolutionSet (quotSet F z) := by
  have key : ∀ g : H, (g : H ⧸ Subgroup.zpowers z) = 1 → orderOf g ∣ 2 := by
    intro g hg
    rcases (mk_eq_one_iff_of_mul_self hz2).1 hg with rfl | rfl
    · rw [orderOf_one]
      exact one_dvd 2
    · exact orderOf_dvd_of_pow_eq_one (by rw [sq, hz2])
  have hdvd : ∀ g : H, orderOf (g : H ⧸ Subgroup.zpowers z) ∣ orderOf g := fun g =>
    orderOf_map_dvd (QuotientGroup.mk' _) g
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, ⟨hc, hcz⟩, rfl⟩
    have hc2 := hF.1 c hc
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hc2, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      rcases (mk_eq_one_iff_of_mul_self hz2).1 h1 with h | h
      · rw [h, orderOf_one] at hc2
        exact absurd hc2 (by norm_num)
      · exact hcz h
  · rintro _ ⟨c, ⟨hc, -⟩, rfl⟩ _ ⟨c', ⟨hc', -⟩, rfl⟩
    rw [← QuotientGroup.mk_mul]
    rcases hF.2.1 c hc c' hc' with h2 | h4 | ho
    · have h := hdvd (c * c')
      rw [h2] at h
      rcases (Nat.dvd_prime Nat.prime_two).1 h with h | h
      · right; right
        rw [h]
        exact odd_one
      · left
        exact h
    · have h := hdvd (c * c')
      rw [h4] at h
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 2 from h)
      interval_cases i
      · exfalso
        rw [pow_zero, orderOf_eq_one_iff] at hi'
        have h' := key _ hi'
        rw [h4] at h'
        exact absurd h' (by norm_num)
      · left
        simpa using hi'
      · right; left
        simpa using hi'
    · right; right
      exact ho.of_dvd_nat (hdvd _)
  · rintro _ ⟨c, ⟨hc, -⟩, rfl⟩ _ ⟨c', ⟨hc', -⟩, rfl⟩ h4
    rw [← QuotientGroup.mk_mul] at h4 ⊢
    have h4' : orderOf (c * c') = 4 := by
      rcases hF.2.1 c hc c' hc' with h2 | h4' | ho
      · have h := hdvd (c * c')
        rw [h2, h4] at h
        exact absurd h (by norm_num)
      · exact h4'
      · have h := ho.of_dvd_nat (hdvd (c * c'))
        rw [h4] at h
        exact absurd h (by decide)
    refine ⟨(c * c') ^ 2, ⟨hF.2.2 c hc c' hc' h4', ?_⟩, QuotientGroup.mk_pow _ _ _⟩
    intro hz'
    have h1 : ((c * c' : H) : H ⧸ Subgroup.zpowers z) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, hz', (mk_eq_one_iff_of_mul_self hz2).2 (Or.inr rfl)]
    have h := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h
    exact absurd h (by norm_num)

theorem conj_mem_quotSet (hFn : ∀ g : H, ∀ f ∈ F, g * f * g⁻¹ ∈ F)
    (hz : z ∈ Subgroup.center H) [(Subgroup.zpowers z).Normal] (k : H ⧸ Subgroup.zpowers z)
    {f : H ⧸ Subgroup.zpowers z} (hf : f ∈ quotSet F z) : k * f * k⁻¹ ∈ quotSet F z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  obtain ⟨c, ⟨hc, hcz⟩, rfl⟩ := hf
  refine ⟨g * c * g⁻¹, ⟨hFn g c hc, ?_⟩, by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  intro h
  apply hcz
  calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
    _ = g⁻¹ * (z * g) := by rw [h, mul_assoc]
    _ = z := by rw [← Subgroup.mem_center_iff.1 hz g, ← mul_assoc, inv_mul_cancel, one_mul]

theorem commute_of_commute_mk (hF : IsRootInvolutionSet F)
    (hFn : ∀ g : H, ∀ f ∈ F, g * f * g⁻¹ ∈ F) (hz : z ∈ Subgroup.center H) (hz2 : z * z = 1)
    [(Subgroup.zpowers z).Normal] {f c h : H} (hf : f ∈ F) (hc : c ∈ F) (hh : h ∈ F)
    (hhf : ¬ Commute h f) (hodd : Odd (orderOf (h * f)))
    (hfc : Commute (f : H ⧸ Subgroup.zpowers z) (c : H ⧸ Subgroup.zpowers z)) :
    Commute f c := by
  have hzc := Subgroup.mem_center_iff.1 hz
  have hf2 := hF.mul_self_eq_one hf
  have hc2 := hF.mul_self_eq_one hc
  have h1 : ((f * c * (c * f)⁻¹ : H) : H ⧸ Subgroup.zpowers z) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      hfc.eq, mul_inv_cancel]
  rcases (mk_eq_one_iff_of_mul_self hz2).1 h1 with h1 | h1
  · exact mul_inv_eq_one.1 h1
  have hinv : (c * f)⁻¹ = f * c := by rw [mul_inv_rev, hF.inv_eq hf, hF.inv_eq hc]
  rw [hinv] at h1
  by_cases hz1 : z = 1
  · rw [hz1] at h1
    exact (commute_iff_mul_sq_eq_one hf2 hc2).2 (by rw [sq]; exact h1)
  exfalso
  have h4 : orderOf (f * c) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := f * c)
      (by rw [pow_one, sq, h1]; exact hz1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq (f * c), h1, sq, hz2])
    simpa using h
  have hzF : z ∈ F := by
    rw [← h1, ← sq]
    exact hF.2.2 f hf c hc h4
  have hfzF : f * z ∈ F := by
    have h := hFn c f hf
    rwa [show c * f * c⁻¹ = f * z by
      rw [← h1, hF.inv_eq hc, show f * (f * c * (f * c)) = f * f * (c * f * c) by group, hf2,
        one_mul]] at h
  have h' := Moufang.eq_of_collinear_of_odd hF hzF (hzc f) hfzF hh (hzc h) hodd
  apply hhf
  rw [eq_inv_of_mul_eq_one_left h']
  exact (Commute.refl f).inv_left

end CentralQuotient

section Main

variable {G : Type} [Group G] {D : Set G}

theorem isRootInvolutionSet_subtype (hD : IsRootInvolutionSet D) (X : Subgroup G) :
    IsRootInvolutionSet {c : X | (c : G) ∈ D} := by
  refine ⟨fun c hc => ?_, fun c hc c' hc' => ?_, fun c hc c' hc' h4 => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hD.1 _ hc
  · rw [← Subgroup.orderOf_coe]
    exact hD.2.1 _ hc _ hc'
  · rw [← Subgroup.orderOf_coe] at h4
    exact hD.2.2 _ hc _ hc' h4

theorem false_of_thirdKindThree (h120 : RootGenQuotientStmt) (hL2 : RootThreeL2Stmt)
    (h : Hyp G D) (IH : RootIHStruct G) (hNI : Closure.NoCommonCentral D) {d a b y : G}
    (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b)
    (hnD : a * b ∉ D) (hy : y ∈ D) (hay : orderOf (a * y) = 3) {m : ℕ} (hm : Odd m)
    (hym : orderOf (y * (a * b)) = 2 * m) : False := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  have hN : ∀ g c : G, c ∈ D → g * c * g⁻¹ ∈ D := fun g c hc => conj_mem_of_isClass hclass g hc
  obtain ⟨hdy, hoddy⟩ := opposite_of_orderOf_eq_three hD hd ha hy hay (mem_rootSet_self hd)
  obtain ⟨hay', hodday⟩ := opposite_of_orderOf_eq_three hD hd ha hy hay ha
  obtain ⟨hby, hoddby⟩ := opposite_of_orderOf_eq_three hD hd ha hy hay hb
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact orderOf_mul_ne_two hD hd ha hb hab hy hdy hoddy (by rw [hym])
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  set z := (y * (a * b)) ^ m with hz
  obtain ⟨hzy, -, -⟩ := Closure.third_kind (hD.mul_self_eq_one hy) hu2 hm hym
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_add, ← two_mul, ← hym, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hym] at hdvd
    have := Nat.le_of_dvd hm.pos hdvd
    have := hm.pos
    omega
  have hzE : z ∉ rootGroup D d := fun hzE => hz1 (hNI d hd y hy hdy hoddy z hzE hzy)
  have hzY : ∀ g ∈ Subgroup.closure (insert y (rootSet D d)), Commute z g := fun g hg =>
    commute_of_mem_closure_of_twoOdd h hd ha hb hab hy hdy hoddy hm hym hg
  set U := Subgroup.closure ({y, a, b} : Set G) with hU
  have hUY : U ≤ Subgroup.closure (insert y (rootSet D d)) := by
    rw [hU]
    refine Subgroup.closure_mono ?_
    rintro g (rfl | rfl | rfl)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ha
    · exact Set.mem_insert_of_mem _ hb
  have hyU : y ∈ U := Subgroup.subset_closure (by simp)
  have haU : a ∈ U := Subgroup.subset_closure (by simp)
  have hbU : b ∈ U := Subgroup.subset_closure (by simp)
  have huU : a * b ∈ U := U.mul_mem haU hbU
  have hzU : z ∈ U := U.pow_mem (U.mul_mem hyU huU) m
  have heD : a * b * z ∈ D := (mem_of_twoOdd hclass hD hd ha hb hy hab hm hym).1
  have heU : a * b * z ∈ U := U.mul_mem huU hzU
  have hez : a * b * z ≠ z := by
    intro h1
    apply hab
    have h2 : a * b = 1 := mul_eq_right.1 h1
    rw [eq_inv_of_mul_eq_one_left h2, hD.inv_eq hb.1]
  have hoddye : Odd (orderOf (y * (a * b * z))) := by
    have hpow : (y * (a * b * z)) ^ m = 1 := by
      have h1 : y * (a * b * z) = (y * (a * b)) ^ (m + 1) := by
        rw [pow_succ']
        exact (mul_assoc _ _ _).symm
      obtain ⟨k, hk⟩ := hm
      rw [h1, ← pow_mul, show (m + 1) * m = 2 * m * (k + 1) by rw [hk]; ring, pow_mul, ← hym,
        pow_orderOf_eq_one, one_pow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  have hclU : ∀ t ∈ rootSet D d, t ∈ U → t ∈ classIn U y := fun t ht htU =>
    mem_classIn_of_odd hD hy ht.1 hyU htU (by
      rw [orderOf_mul_comm_eq]
      exact (odd_orderOf_mul_iff_of_mem_rootSet hD hd ht hy hdy).2 hoddy)
  have hecl : a * b * z ∈ classIn U y := mem_classIn_of_odd hD hy heD hyU heU hoddye
  have hne : U ≠ ⊤ := closure_ne_top_of_twoOdd h hd ha hb hab hy hdy hoddy hm hym
    (S := {a, b}) (by rintro g (rfl | rfl); exacts [ha, hb])
  have hSa : ({a, b} : Set G) ⊆ rootSet D a := by
    rw [rootSet_eq_of_mem ha]
    rintro g (rfl | rfl)
    exacts [ha, hb]
  have hshape := rankOneShape_quotient h120 h IH ha.1 hy hay' hodday hSa (by simp) hne
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥U) with hπ
  set yU : ↥U := ⟨y, hyU⟩ with hyUdef
  set aU : ↥U := ⟨a, haU⟩ with haUdef
  set bU : ↥U := ⟨b, hbU⟩ with hbUdef
  set zU : ↥U := ⟨z, hzU⟩ with hzUdef
  have hcU : ∀ g g' : ↥U, Commute g g' ↔ Commute (g : G) (g' : G) := fun g g' =>
    ⟨fun hc => congrArg Subtype.val hc, fun hc => Subtype.ext hc⟩
  have hP2 : IsPGroup 2 (CFSG.pCore 2 ↥U) := CFSG.pCore_isPGroup
  have hodd' : ∀ g : ↥U, Odd (orderOf (g : G)) → orderOf (π g) = orderOf (g : G) :=
    fun g hg => by
      rw [hπ, orderOf_mk_eq_of_odd hP2 ((Subgroup.orderOf_coe g) ▸ hg), Subgroup.orderOf_coe]
  have hay3 : orderOf (π (aU * yU)) = 3 :=
    (hodd' (aU * yU) (by rw [show ((aU * yU : ↥U) : G) = a * y from rfl, hay]; decide)).trans
      hay
  have himg1 : ∀ g : ↥U, ¬ Commute (g : G) y → Odd (orderOf ((g : G) * y)) → π g ≠ 1 := by
    intro g hgy hodd h1
    have h2 := hodd' (g * yU) hodd
    rw [map_mul, h1, one_mul] at h2
    have h3 : orderOf (π yU) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [sq, ← map_mul, show yU * yU = 1 from Subtype.ext (hD.mul_self_eq_one hy), map_one])
    rw [h2] at h3
    have h4 := Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 hodd) h3
    rw [orderOf_eq_one_iff] at h4
    apply hgy
    rw [eq_inv_of_mul_eq_one_left h4]
    exact (Commute.refl y).inv_left
  have haU1 : π aU ≠ 1 := himg1 aU hay' hodday
  have hbU1 : π bU ≠ 1 := himg1 bU hby hoddby
  have hu1 : π ⟨a * b, huU⟩ ≠ 1 := by
    intro h1
    set w : ↥U := (yU * ⟨a * b, huU⟩) ^ 2 with hw
    have hwo : orderOf w = m := by
      rw [hw, ← Subgroup.orderOf_coe]
      simp only [Subgroup.coe_pow, Subgroup.coe_mul]
      rw [orderOf_pow' _ two_ne_zero, hym, Nat.gcd_mul_right_left m 2,
        Nat.mul_div_cancel_left _ two_pos]
    have hw1 : π w = 1 := by
      rw [hw, map_pow, map_mul, h1, mul_one, ← map_pow, sq,
        show yU * yU = 1 from Subtype.ext (hD.mul_self_eq_one hy), map_one]
    have := orderOf_mk_eq_of_odd hP2 (hwo ▸ hm)
    rw [← hπ, hw1, orderOf_one, hwo] at this
    exact hm1 this.symm
  obtain ⟨n, hn, ⟨eU⟩⟩ :
      ∃ n, 2 ≤ n ∧ Nonempty ((↥U ⧸ CFSG.pCore 2 ↥U) ≃* PSL2Model n) := by
    rcases hshape with h1 | ⟨n, hn, ⟨eS⟩⟩ | ⟨s, t, hst, hs, ht, ho⟩
    · exact h1
    · exfalso
      apply not_three_dvd_card_szModel hn
      rw [← Nat.card_congr eS.toEquiv, ← hay3]
      exact orderOf_dvd_natCard _
    · exfalso
      have hs2 : s * s = 1 := by
        have := pow_orderOf_eq_one s
        rwa [hs, sq] at this
      have ht2 : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rwa [ht, sq] at this
      have hsqU : ∀ g : ↥U, (g : G) * g = 1 → π g * π g = 1 := fun g hg2 => by
        rw [← map_mul, show g * g = 1 from Subtype.ext hg2, map_one]
      have hcomm : Commute (π aU) (π bU) :=
        ((hcU aU bU).2 (commute_of_mem_rootSet hd ha hb)).map π
      rcases eq_of_commute_of_closure_pair hs2 ht2 ho hst (hsqU aU (hD.mul_self_eq_one ha.1))
          (hsqU bU (hD.mul_self_eq_one hb.1)) hcomm with h1 | h1 | h1
      · exact haU1 h1
      · exact hbU1 h1
      · apply hu1
        rw [show (⟨a * b, huU⟩ : ↥U) = aU * bU from rfl, map_mul, ← h1,
          hsqU aU (hD.mul_self_eq_one ha.1)]
  have hKB : IsBenderGroup (↥U ⧸ CFSG.pCore 2 ↥U) := .isPSL2 n hn eU
  have hzc : zU ∈ Subgroup.center ↥U := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzY g (hUY g.2)).symm.eq
  have hzU2 : zU * zU = 1 := Subtype.ext hz2
  have hZc : Subgroup.zpowers zU ≤ Subgroup.center ↥U := by
    rw [Subgroup.zpowers_le]
    exact hzc
  have hZn : (Subgroup.zpowers zU).Normal := Subgroup.normal_of_le_center hZc
  have hZ2 : IsPGroup 2 (Subgroup.zpowers zU) := isPGroup_zpowers_of_mul_self_eq_one hzU2
  have hZQ : Subgroup.zpowers zU ≤ CFSG.pCore 2 ↥U := le_sSup ⟨hZn, hZ2⟩
  set F : Set ↥U := {c | (c : G) ∈ D} with hF
  have hFroot : IsRootInvolutionSet F := isRootInvolutionSet_subtype hD U
  have hFn : ∀ g : ↥U, ∀ f ∈ F, g * f * g⁻¹ ∈ F := fun g f hf => hN (g : G) f hf
  have hyF : yU ∈ F := hy
  have haF : aU ∈ F := ha.1
  have hbF : bU ∈ F := hb.1
  have heF : (⟨a * b * z, heU⟩ : ↥U) ∈ F := heD
  have hmemQ : ∀ c : ↥U, c ∈ F → c ≠ zU →
      (c : ↥U ⧸ Subgroup.zpowers zU) ∈ quotSet F zU := fun c hc hcz => ⟨c, ⟨hc, hcz⟩, rfl⟩
  have hne_z : ∀ c w : ↥U, ¬ Commute (c : G) (w : G) → c ≠ zU := by
    intro c w hcw hcz
    apply hcw
    rw [show (c : G) = z from congrArg Subtype.val hcz]
    exact hzY w (hUY w.2)
  have hyz : yU ≠ zU := hne_z yU aU (fun hc => hay' hc.symm)
  have haz : aU ≠ zU := hne_z aU yU hay'
  have hbz : bU ≠ zU := hne_z bU yU hby
  have hez' : (⟨a * b * z, heU⟩ : ↥U) ≠ zU := fun h1 => hez (congrArg Subtype.val h1)
  have hconjU : ∀ c : G, ∀ hc : c ∈ U, c ∈ classIn U y → IsConj yU ⟨c, hc⟩ := by
    rintro c hc ⟨g, hg, rfl⟩
    exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext rfl⟩
  have hyaU : IsConj yU aU := hconjU a haU (hclU a ha haU)
  have hybU : IsConj yU bU := hconjU b hbU (hclU b hb hbU)
  have hyeU : IsConj yU ⟨a * b * z, heU⟩ := hconjU _ heU hecl
  have habU : IsConj aU bU := hyaU.symm.trans hybU
  have haeU : IsConj aU ⟨a * b * z, heU⟩ := hyaU.symm.trans hyeU
  have hmkab : (aU : ↥U ⧸ Subgroup.zpowers zU) * (bU : ↥U ⧸ Subgroup.zpowers zU) =
      ((⟨a * b * z, heU⟩ : ↥U) : ↥U ⧸ Subgroup.zpowers zU) := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    convert Subgroup.mem_zpowers zU using 1
    exact Subtype.ext (show (a * b)⁻¹ * (a * b * z) = z by group)
  have hay3Q : orderOf ((aU : ↥U ⧸ Subgroup.zpowers zU) * (yU : ↥U ⧸ Subgroup.zpowers zU)) =
      3 := by
    rw [← QuotientGroup.mk_mul]
    have h1 := orderOf_mk_eq_of_odd hZ2 (g := aU * yU) (by
      rw [← Subgroup.orderOf_coe, show ((aU * yU : ↥U) : G) = a * y from rfl, hay]
      decide)
    rw [QuotientGroup.mk'_apply] at h1
    rw [h1, ← Subgroup.orderOf_coe]
    exact hay
  have hyb' : ¬ Commute yU bU := fun hc => hby ((hcU yU bU).1 hc).symm
  have hya' : ¬ Commute yU aU := fun hc => hay' ((hcU yU aU).1 hc).symm
  have hoddyb' : Odd (orderOf (yU * bU)) := by
    rw [← Subgroup.orderOf_coe, show ((yU * bU : ↥U) : G) = y * b from rfl,
      orderOf_mul_comm_eq]
    exact hoddby
  have hoddya' : Odd (orderOf (yU * aU)) := by
    rw [← Subgroup.orderOf_coe, show ((yU * aU : ↥U) : G) = y * a from rfl,
      orderOf_mul_comm_eq]
    exact hodday
  have hbroot : (bU : ↥U ⧸ Subgroup.zpowers zU) ∈
      rootSet (quotSet F zU) (aU : ↥U ⧸ Subgroup.zpowers zU) := by
    refine ⟨hmemQ bU hbF hbz, ?_⟩
    rintro _ ⟨c, ⟨hc, -⟩, rfl⟩
    have hbac : Commute b (c : G) ↔ Commute a (c : G) := (hb.2 _ hc).trans (ha.2 _ hc).symm
    constructor
    · intro hbc
      have h1 : Commute bU c := commute_of_commute_mk hFroot hFn hzc hzU2 hbF hc hyF hyb'
        hoddyb' hbc
      exact ((hcU aU c).2 (hbac.1 ((hcU bU c).1 h1))).map (QuotientGroup.mk' _)
    · intro hac
      have h1 : Commute aU c := commute_of_commute_mk hFroot hFn hzc hzU2 haF hc hyF hya'
        hoddya' hac
      exact ((hcU bU c).2 (hbac.2 ((hcU aU c).1 h1))).map (QuotientGroup.mk' _)
  have hgenU : Subgroup.closure ({yU, aU, bU} : Set ↥U) = ⊤ := by
    have h1 := Subgroup.closure_closure_coe_preimage (k := ({y, a, b} : Set G))
    convert h1 using 2
    ext c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
    rfl
  have hgenQ : Subgroup.closure ({(yU : ↥U ⧸ Subgroup.zpowers zU),
      (aU : ↥U ⧸ Subgroup.zpowers zU), (bU : ↥U ⧸ Subgroup.zpowers zU)} :
      Set (↥U ⧸ Subgroup.zpowers zU)) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.zpowers zU))) hgenU
    rw [MonoidHom.map_closure,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    rw [← h1]
    simp only [Set.image_insert_eq, Set.image_singleton, QuotientGroup.mk'_apply]
  have hNbot := hL2 (↥U ⧸ Subgroup.zpowers zU) (quotSet F zU)
    (isRootInvolutionSet_quotSet hFroot hzU2) (fun k f hf => conj_mem_quotSet hFn hzc k hf)
    _ (hmemQ yU hyF hyz) _ (hmemQ aU haF haz) _ hbroot
    (by rw [hmkab]; exact hmemQ _ heF hez') hay3Q
    ((QuotientGroup.mk' (Subgroup.zpowers zU)).map_isConj habU)
    (by rw [hmkab]; exact (QuotientGroup.mk' (Subgroup.zpowers zU)).map_isConj haeU) hgenQ
    ((CFSG.pCore 2 ↥U).map (QuotientGroup.mk' (Subgroup.zpowers zU))) (hP2.map _) n hn
    ⟨(QuotientGroup.quotientQuotientEquivQuotient _ _ hZQ).trans eU⟩
  have hQZ : CFSG.pCore 2 ↥U = Subgroup.zpowers zU := by
    refine le_antisymm (fun q hq => ?_) hZQ
    have h1 : QuotientGroup.mk' (Subgroup.zpowers zU) q ∈
        (CFSG.pCore 2 ↥U).map (QuotientGroup.mk' (Subgroup.zpowers zU)) := ⟨q, hq, rfl⟩
    rw [hNbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hBZ : IsBenderGroup (↥U ⧸ Subgroup.zpowers zU) :=
    .isPSL2 n hn ((QuotientGroup.quotientMulEquivOfEq hQZ.symm).trans eU)
  have hS : Asc72.Setup ↥U {g | IsConj yU g} := by
    refine ⟨⟨yU, rfl⟩, ⟨?_, ?_⟩, ?_⟩
    · intro c hc
      obtain ⟨g, rfl⟩ := isConj_iff.1 hc
      rw [orderOf_conj', ← Subgroup.orderOf_coe]
      exact hD.1 y hy
    · intro f hf g hg
      obtain ⟨c₁, hc₁⟩ := isConj_iff.1 hf
      obtain ⟨c₂, hc₂⟩ := isConj_iff.1 hg
      have hfD : (f : G) ∈ D := by
        rw [← hc₁]
        exact hN _ _ hy
      have hgD : (g : G) ∈ D := by
        rw [← hc₂]
        exact hN _ _ hy
      have hfg : orderOf (f * g) = orderOf ((f : G) * (g : G)) :=
        (Subgroup.orderOf_coe (f * g)).symm
      rw [hfg]
      rcases hD.2.1 _ hfD _ hgD with h2 | h4 | ho
      · left
        rw [h2]
      · exfalso
        have hfg4 : (f * g) ^ 2 ^ 2 = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one, hfg, h4]
          norm_num
        have hw4 : (π (f * g)) ^ 2 ^ 2 = 1 := by rw [← map_pow, hfg4, map_one]
        have hp : IsPGroup 2 (Subgroup.zpowers (π (f * g))) :=
          isPGroup_iff_orderOf_dvd_pow.2 fun k => ⟨2, by
            rw [← Subgroup.orderOf_coe]
            exact (orderOf_dvd_of_mem_zpowers k.2).trans (orderOf_dvd_of_pow_eq_one hw4)⟩
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
        have hwQ : π (f * g) ∈ Q := hQ (Subgroup.mem_zpowers _)
        have hw2 : π (f * g) * π (f * g) = 1 :=
          Asc72.IsBenderGroup.mul_self_eq_one_of_commute hKB Q hwQ
            (fun q hq => Asc72.IsBenderGroup.commute_of_psl2 hn eU Q _ hwQ _ hq)
        have hww : f * g * (f * g) ∈ Subgroup.zpowers zU := by
          rw [← hQZ, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul]
          exact hw2
        rcases (mem_zpowers_of_mul_self_eq_one hzU2).1 hww with h1 | h1
        · have h' : orderOf (f * g) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h1])
          rw [hfg, h4] at h'
          exact absurd h' (by norm_num)
        ·
          have hzz : (f : G) * g * ((f : G) * g) = z := congrArg Subtype.val h1
          have hzD : z ∈ D := by
            rw [← hzz, ← sq]
            exact hD.2.2 _ hfD _ hgD h4
          have hf2 : (f : G) * f = 1 := hD.mul_self_eq_one hfD
          have hfzD : (f : G) * z ∈ D := by
            have h' := hN (g : G) f hfD
            rwa [show (g : G) * f * (g : G)⁻¹ = (f : G) * z by
              rw [← hzz, hD.inv_eq hgD, show (f : G) * ((f : G) * g * ((f : G) * g)) =
                (f : G) * f * ((g : G) * f * g) by group, hf2, one_mul]] at h'
          have hfz : Commute (f : G) z := (hzY _ (hUY f.2)).symm
          have hhD : ((c₁ * aU * c₁⁻¹ : ↥U) : G) ∈ D := hN _ _ ha.1
          have hhz : Commute ((c₁ * aU * c₁⁻¹ : ↥U) : G) z :=
            (hzY _ (hUY (c₁ * aU * c₁⁻¹).2)).symm
          have hho : orderOf (((c₁ * aU * c₁⁻¹ : ↥U) : G) * (f : G)) = 3 := by
            rw [show ((c₁ * aU * c₁⁻¹ : ↥U) : G) * (f : G) =
              ((c₁ * aU * c₁⁻¹ * f : ↥U) : G) from rfl, Subgroup.orderOf_coe, ← hc₁,
              show c₁ * aU * c₁⁻¹ * (c₁ * yU * c₁⁻¹) = c₁ * (aU * yU) * c₁⁻¹ by group,
              orderOf_conj', ← Subgroup.orderOf_coe]
            exact hay
          have h' := Moufang.eq_of_collinear_of_odd hD hzD hfz hfzD hhD hhz
            (by rw [hho]; decide)
          rw [h', orderOf_one] at hho
          exact absurd hho (by norm_num)
      · right
        exact ho
    · rw [eq_top_iff, ← hgenU]
      refine Subgroup.closure_mono ?_
      rintro c (rfl | rfl | rfl)
      · exact IsConj.refl _
      · exact hyaU
      · exact hybU
  have hinf := Asc72.inf_commutator_eq_bot_of_isBenderGroup hS hZc hZ2 hBZ
  have hsup := Asc72.sup_commutator_eq_top_of_isBenderGroup hS hZc hZ2 hBZ
  have hyX : yU ∉ commutator ↥U := by
    intro hyX
    have hconjX : ∀ g : ↥U, IsConj yU g → g ∈ commutator ↥U := by
      intro g hg
      obtain ⟨c, rfl⟩ := isConj_iff.1 hg
      exact (inferInstance : (commutator ↥U).Normal).conj_mem _ hyX c
    have htop : commutator ↥U = ⊤ := by
      rw [eq_top_iff, ← hgenU, Subgroup.closure_le]
      rintro c (rfl | rfl | rfl)
      · exact hyX
      · exact hconjX _ hyaU
      · exact hconjX _ hybU
    rw [htop, inf_top_eq] at hinf
    apply hz1
    have h1 : zU ∈ Subgroup.zpowers zU := Subgroup.mem_zpowers zU
    rw [hinf, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hcX : ∀ g : ↥U, IsConj yU g → g ∉ commutator ↥U := by
    intro g hg hgX
    obtain ⟨c, rfl⟩ := isConj_iff.1 hg
    apply hyX
    have h1 := (inferInstance : (commutator ↥U).Normal).conj_mem _ hgX c⁻¹
    convert h1 using 1
    group
  have hdec : ∀ g : ↥U, g ∈ commutator ↥U ∨ g * zU ∈ commutator ↥U := by
    intro g
    have hg : g ∈ Subgroup.zpowers zU ⊔ commutator ↥U := by
      rw [hsup]
      exact Subgroup.mem_top g
    obtain ⟨w, hw, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
    rcases (mem_zpowers_of_mul_self_eq_one hzU2).1 hw with rfl | rfl
    · left
      rwa [one_mul]
    · right
      have h1 : zU * x * zU = x := by
        rw [← Subgroup.mem_center_iff.1 hzc x, mul_assoc, hzU2, mul_one]
      rw [h1]
      exact hx
  have hXequiv : ↥(commutator ↥U) ≃* ↥U ⧸ Subgroup.zpowers zU := by
    refine MulEquiv.ofBijective
      ((QuotientGroup.mk' (Subgroup.zpowers zU)).comp (commutator ↥U).subtype) ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro g hg
      have h1 : (g : ↥U) ∈ Subgroup.zpowers zU ⊓ commutator ↥U :=
        ⟨(QuotientGroup.eq_one_iff _).1 hg, g.2⟩
      rw [hinf, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    · intro k
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers zU) k
      rcases hdec g with hg | hg
      · exact ⟨⟨g, hg⟩, rfl⟩
      · refine ⟨⟨g * zU, hg⟩, ?_⟩
        show QuotientGroup.mk' (Subgroup.zpowers zU) (g * zU) =
          QuotientGroup.mk' (Subgroup.zpowers zU) g
        rw [map_mul, show QuotientGroup.mk' (Subgroup.zpowers zU) zU = 1 from
          (QuotientGroup.eq_one_iff zU).2 (Subgroup.mem_zpowers zU), mul_one]
  have hXB : IsBenderGroup ↥(commutator ↥U) :=
    .isPSL2 n hn (hXequiv.trans ((QuotientGroup.quotientMulEquivOfEq hQZ.symm).trans eU))
  have hroot4 : ∀ j : G, j ∈ rootGroup D d → ∀ hjU : j ∈ U,
      (⟨j, hjU⟩ : ↥U) ∉ commutator ↥U → j ∈ rootSet D d := by
    intro j hjE hjU hjX
    have hj2 : j * j = 1 := mul_self_eq_one_of_mem_rootGroup hD hd hjE
    have hjz : j ≠ z := fun h1 => hzE (h1 ▸ hjE)
    have hjzX := (hdec ⟨j, hjU⟩).resolve_left hjX
    have hazX := (hdec aU).resolve_left (hcX aU hyaU)
    have hinvol : ∀ c : G, ∀ hc : c ∈ U, c * c = 1 → c ≠ z →
        ∀ hcX : (⟨c, hc⟩ : ↥U) * zU ∈ commutator ↥U,
          orderOf (⟨(⟨c, hc⟩ : ↥U) * zU, hcX⟩ : ↥(commutator ↥U)) = 2 := by
      intro c hc hc2 hcz hcX
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe]
      apply orderOf_eq_prime
      · show (c * z) ^ 2 = 1
        rw [(hzY c (hUY hc)).symm.mul_pow, sq, sq, hc2, hz2, one_mul]
      · intro h1
        apply hcz
        rw [eq_inv_of_mul_eq_one_left (show c * z = 1 from h1),
          inv_eq_of_mul_eq_one_right hz2]
    obtain ⟨g, hg⟩ := isConj_iff.1 (Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hXB
      (hinvol a haU (hD.mul_self_eq_one ha.1) (fun h1 => haz (Subtype.ext h1)) hazX)
      (hinvol j hjU hj2 hjz hjzX))
    set g' : G := ((g : ↥U) : G) with hg'
    have hga : g' * (a * z) * g'⁻¹ = j * z := by
      have h1 := congrArg (fun k : ↥(commutator ↥U) => ((k : ↥U) : G)) hg
      simpa [hg', mul_assoc] using h1
    have hgz : g' * z * g'⁻¹ = z := by
      rw [← (hzY _ (hUY (g : ↥U).2)).eq, mul_inv_cancel_right]
    have hja : g' * a * g'⁻¹ = j := by
      have h1 : g' * (a * z) * g'⁻¹ = g' * a * g'⁻¹ * (g' * z * g'⁻¹) := by group
      rw [h1, hgz] at hga
      exact mul_right_cancel hga
    have hjD : j ∈ D := hja ▸ hN _ _ ha.1
    exact mem_rootSet_of_mem_rootGroup hclass hd hjD hjE
  have hTX : ∀ t ∈ rootSet D d, ∀ htU : t ∈ U, (⟨t, htU⟩ : ↥U) ∉ commutator ↥U :=
    fun t ht htU => hcX _ (hconjU t htU (hclU t ht htU))
  have hplusU : ∀ t ∈ rootSet D a, t ∈ U → ∀ g ∈ rootGroup D a, g ∈ U →
      g ∉ rootSet D a → t * g ∈ rootSet D a := by
    rw [rootGroup_eq_of_mem ha, rootSet_eq_of_mem ha]
    intro t ht htU g hgE hgU hgT
    have hgX : (⟨g, hgU⟩ : ↥U) ∈ commutator ↥U := by
      by_contra hgX
      exact hgT (hroot4 g hgE hgU hgX)
    refine hroot4 (t * g) ((rootGroup D d).mul_mem (rootSet_subset_rootGroup D d ht) hgE)
      (U.mul_mem htU hgU) ?_
    intro htgX
    apply hTX t ht htU
    have h1 := (commutator ↥U).mul_mem htgX ((commutator ↥U).inv_mem hgX)
    convert h1 using 1
    exact Subtype.ext (by simp)
  exact false_of_isBenderGroup h ha.1 haU hy hyU hay' hodday hKB (u := a * b)
    (by rw [rootGroup_eq_of_mem ha]; exact mul_mem_rootGroup ha hb) huU
    (by rw [rootSet_eq_of_mem ha]; exact fun hmem => hnD hmem.1) hu1 hplusU

theorem thirdKindThreeStep_of (h120 : RootGenQuotientStmt) (hT : Moufang.Tim75Thm31)
    (hL2 : RootThreeL2Stmt) : ThirdKindThreeStep := by
  intro G _ D hH IH _ d hd a ha b hb hab hnD y hy hay m hm hym
  exact false_of_thirdKindThree h120 hL2 hH IH (noCommonCentral_of_tim75 hT hH) hd ha hb hab
    hnD hy hay hm hym

theorem thirdKindStep_of_rootThreeL2 (h18 : CommonNeighbourStmt) (hT : Moufang.Tim75Thm31)
    (hL2 : RootThreeL2Stmt) : ThirdKindStep :=
  thirdKindStep_of_commonNeighbour h18 hT
    (thirdKindThreeStep_of (rootGenQuotientStmt_of h18) hT hL2)

end Main

end CFSG.Timmesfeld.Bridge.RootClosure
