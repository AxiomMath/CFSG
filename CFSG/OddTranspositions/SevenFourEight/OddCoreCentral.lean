module

public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.ClaimC1
import CFSG.OddTranspositions.SevenFourEight.PrimeOrder
import CFSG.OddTranspositions.SevenThreeConclusion
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseCore

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem commSet_DstarH_eq_of_mem (hC : HypothesisC D)
    (hW1 : ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b v : ↥(Halpha D hC.alpha)}
    (hb : (b : G) ∈ β) (hv : (v : G) ∈ β) :
    commSet (DstarH hC) b = commSet (DstarH hC) v := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff'.mp hβ.1
  have hβb : IsBlock D β := hg ▸ hC.isBlock_alpha.conj hC.setup.normal g
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hW1β : ∀ x ∈ β, ∀ y ∈ β, Commute x y → x = y := by
    intro x hx y hy hxy
    rw [hk] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    have e : ∀ z : G, k⁻¹ * (k * z * k⁻¹) * k⁻¹⁻¹ = z := fun z => by group
    have h := hxy.conj k⁻¹
    rw [e, e] at h
    rw [hW1 x hx y hy h]
  ext e
  show e ∈ DstarH hC ∧ Commute e b ∧ e ≠ b ↔ e ∈ DstarH hC ∧ Commute e v ∧ e ≠ v
  refine and_congr_right fun he => ?_
  by_cases heβ : (e : G) ∈ β
  · exact iff_of_false
      (fun h => h.2 (Subtype.ext (hW1β _ heβ _ hb (Submonoid.commute_coe_coe.mpr h.1))))
      (fun h => h.2 (Subtype.ext (hW1β _ heβ _ hv (Submonoid.commute_coe_coe.mpr h.1))))
  · have heD : (e : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp he)
    have key : ∀ x y : ↥(Halpha D hC.alpha), (x : G) ∈ β → (y : G) ∈ β → Commute e x →
        Commute e y := fun x y hx hy hex => Submonoid.commute_coe_coe.mp
      (commute_of_mem_block hC.setup.normal hC.setup.oddT hβb hx heD heβ
        (Submonoid.commute_coe_coe.mpr hex).symm _ hy)
    exact and_congr ⟨key b v hb hv, key v b hv hb⟩
      (iff_of_true (fun h => heβ (by rw [h]; exact hb)) (fun h => heβ (by rw [h]; exact hv)))

private theorem exists_not_commute_mk_ne (hC : HypothesisC D)
    (hA : ∃ x ∈ DalphaStar D hC.alpha, ∃ y ∈ DalphaStar D hC.alpha, x ≠ y ∧ Commute x y)
    {v : ↥(Halpha D hC.alpha)} (hv : v ∈ DstarH hC) :
    ∃ c ∈ DstarH hC, ¬ Commute c v ∧
      (c : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) ≠ v := by
  set K := CFSG.oddCore ↥(Halpha D hC.alpha)
  by_contra hcon
  have hcv : ∀ c ∈ DstarH hC, ¬ Commute c v → (c : ↥(Halpha D hC.alpha) ⧸ K) = v :=
    fun c hc hnc => by_contra fun hne => hcon ⟨c, hc, hnc, hne⟩
  have hcent : ∀ h : ↥(Halpha D hC.alpha), (h : ↥(Halpha D hC.alpha) ⧸ K) * v = v * h := by
    have hle : Subgroup.closure (DstarH hC) ≤
        (Subgroup.centralizer {(v : ↥(Halpha D hC.alpha) ⧸ K)}).comap (QuotientGroup.mk' K) := by
      rw [Subgroup.closure_le]
      intro c hc
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
        QuotientGroup.mk'_apply]
      by_cases hc' : Commute c v
      · exact (hc'.map (QuotientGroup.mk' K)).eq
      · rw [hcv c hc hc']
    intro h
    have hh := hle (by rw [DstarH_closure_eq_top hC]; exact Subgroup.mem_top h)
    rwa [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      QuotientGroup.mk'_apply] at hh
  have himg : ∀ x ∈ DstarH hC, (x : ↥(Halpha D hC.alpha) ⧸ K) = v := by
    intro x hx
    obtain ⟨h, rfl⟩ := DstarH_transitive hC hv hx
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcent h,
      mul_inv_cancel_right]
  obtain ⟨x, hx, y, hy, hxy, hc⟩ := hA
  have hx' : (⟨x, Subgroup.subset_closure hx⟩ : ↥(Halpha D hC.alpha)) ∈ DstarH hC := hx
  have hy' : (⟨y, Subgroup.subset_closure hy⟩ : ↥(Halpha D hC.alpha)) ∈ DstarH hC := hy
  have hxyK : (⟨x, Subgroup.subset_closure hx⟩ : ↥(Halpha D hC.alpha)) *
      ⟨y, Subgroup.subset_closure hy⟩ ∈ K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, himg _ hx', himg _ hy',
      ← QuotientGroup.mk_mul, (DstarH_isOddTransp hC).mul_self_eq_one hv, QuotientGroup.mk_one]
  have h2 := (DstarH_isOddTransp hC).orderOf_mul_eq_two hx' hy'
    (fun h => hxy (congrArg Subtype.val h)) (Submonoid.commute_coe_coe.mp hc)
  have hdvd := K.orderOf_dvd_natCard hxyK
  rw [h2] at hdvd
  obtain ⟨m, hm⟩ : Odd (Nat.card K) :=
    CFSG.EvenSporadicStandard.RuStd.S2.Close.odd_card_oddCore _
  omega

private theorem orderOf_mul_eq_three_of_mem_DstarH (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (h3 : ∀ x ∈ DstarH hC, ∀ y ∈ DstarH hC,
      orderOf ((x : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) *
        (y : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha))) ∈
          ({1, 2, 3} : Set ℕ))
    {a b d : ↥(Halpha D hC.alpha)} (ha : a ∈ DstarH hC) (hb : b ∈ DstarH hC)
    (hd : d ∈ DstarH hC)
    (hne : (a : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) ≠ b)
    (hab : ¬ Commute a b) (had : Commute a d) (hda : a ≠ d) (hdb : ¬ Commute d b) :
    orderOf ((a : G) * (b : G)) = 3 := by
  set K := CFSG.oddCore ↥(Halpha D hC.alpha)
  have hΘ := DstarH_isOddTransp hC
  have hD := hC.setup.oddT
  have hKodd : Odd (Nat.card K) := CFSG.EvenSporadicStandard.RuStd.S2.Close.odd_card_oddCore _
  have hK1 : ∀ x ∈ K, x * x = 1 → x = 1 := fun x hx hxx =>
    OddTransp.eq_one_of_mul_self_of_odd hxx (hKodd.of_dvd_nat (K.orderOf_dvd_natCard hx))
  have ha2 := hΘ.mul_self_eq_one ha
  have hb2 := hΘ.mul_self_eq_one hb
  have ho3 : orderOf ((a : ↥(Halpha D hC.alpha) ⧸ K) * (b : ↥(Halpha D hC.alpha) ⧸ K)) = 3 := by
    have hmem := h3 a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exfalso
      apply hne
      have h1 := eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.mp h)
      rwa [← QuotientGroup.mk_inv, hΘ.inv_eq hb] at h1
    · exfalso
      apply hab
      have hc : Commute (a : ↥(Halpha D hC.alpha) ⧸ K) (b : ↥(Halpha D hC.alpha) ⧸ K) := by
        rw [CFSG.Timmesfeld.commute_iff_mul_sq_eq_one
          (by rw [← QuotientGroup.mk_mul, ha2, QuotientGroup.mk_one])
          (by rw [← QuotientGroup.mk_mul, hb2, QuotientGroup.mk_one]), ← h]
        exact pow_orderOf_eq_one _
      exact commute_of_commute_of_ne (M := K) hΘ ha hb hne hc
    · exact h
  have hzK : (a * b) ^ 3 ∈ K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul, ← ho3]
    exact pow_orderOf_eq_one _
  have haD : (a : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp ha)
  have hbD : (b : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hb)
  have hdD : (d : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hd)
  have htri : IsTriangle D (a : G) (b : G) (d : G) :=
    ⟨haD, hdD, hbD, fun h => hda (Subtype.ext h), Submonoid.commute_coe_coe.mpr had,
      fun h => hab (Submonoid.commute_coe_coe.mp h), fun h => hdb (Submonoid.commute_coe_coe.mp h)⟩
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({(a : G), (b : G)} : Set G) →
      IsTriangle D (a : G) x (d : G) → ¬ IsThirdKind (a : G) x (d : G) := by
    rintro x - - hx ⟨n, hn, -, hord⟩
    rw [hsecond _ _ _ hx] at hord
    obtain ⟨m, rfl⟩ := hn
    omega
  have SK := OddTransp.secondKind_structure hD hC.setup.normal htri (hsecond _ _ _ htri) hno
  have hzX : ((a : G) * (b : G)) ^ 3 ∈ Subgroup.closure ({(a : G), (b : G), (d : G)} : Set G) :=
    pow_mem (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 3
  have hadQ : (a : G) * (d : G) ∈
      conjClosure (Subgroup.closure ({(a : G), (b : G)} : Set G)) ((a : G) * (d : G)) :=
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hcQ := mul_mem (SK.normal _ hzX _ hadQ) (inv_mem hadQ)
  have hcK : (a * b) ^ 3 * (a * d) * ((a * b) ^ 3)⁻¹ * (a * d)⁻¹ ∈ K := by
    rw [show (a * b) ^ 3 * (a * d) * ((a * b) ^ 3)⁻¹ * (a * d)⁻¹ =
      (a * b) ^ 3 * ((a * d) * ((a * b) ^ 3)⁻¹ * (a * d)⁻¹) by group]
    exact K.mul_mem hzK ((inferInstance : K.Normal).conj_mem _ (K.inv_mem hzK) _)
  have hc1 : (a * b) ^ 3 * (a * d) * ((a * b) ^ 3)⁻¹ * (a * d)⁻¹ = 1 := by
    refine hK1 _ hcK (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Subgroup.coe_one]
    exact SK.sq _ hcQ
  have hzc : Commute ((a * b) ^ 3) (a * d) := by
    have h := mul_inv_eq_one.mp hc1
    rw [commute_iff_eq]
    calc (a * b) ^ 3 * (a * d) = (a * b) ^ 3 * (a * d) * ((a * b) ^ 3)⁻¹ * (a * b) ^ 3 := by
          group
      _ = a * d * (a * b) ^ 3 := by rw [h]
  have hza : Commute ((a * b) ^ 3) a :=
    commute_of_mem_odd_normal hΘ (fun g x hx => DstarH_conj_mem hC (h := g) hx) hKodd ha hd hda
      had hzK hzc
  have hinv : a * (a * b) ^ 3 * a⁻¹ = ((a * b) ^ 3)⁻¹ := by
    have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
      rw [mul_inv_rev, hΘ.inv_eq ha, hΘ.inv_eq hb, ← mul_assoc, ha2, one_mul]
    rw [← conj_pow, h1, inv_pow]
  have hz1 : (a * b) ^ 3 = 1 := by
    refine hK1 _ hzK ?_
    have hzz : ((a * b) ^ 3)⁻¹ = (a * b) ^ 3 := by
      rw [← hinv, ← hza.eq, mul_inv_cancel_right]
    calc (a * b) ^ 3 * (a * b) ^ 3 = (a * b) ^ 3 * ((a * b) ^ 3)⁻¹ := by rw [hzz]
      _ = 1 := mul_inv_cancel _
  have hpow : ((a : G) * (b : G)) ^ 3 = 1 := by
    have h := congrArg Subtype.val hz1
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] at h
    exact h
  refine orderOf_eq_prime hpow fun h1 => ?_
  obtain rfl : a = b := Subtype.ext (hD.eq_of_mul_eq_one haD h1)
  exact hab (Commute.refl a)

private theorem orderOf_mul_ne_three_of_mem_Dalpha
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {v c : G} (hv : v ∈ β) (hc : c ∈ D)
    (hcβ : c ∉ β) (hvc : ¬ Commute v c) : orderOf (v * c) ≠ 3 := by
  intro h3
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hvα : k⁻¹ * v * k ∈ hC.alpha := by
    rw [hk] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    rwa [show k⁻¹ * (k * x * k⁻¹) * k = x by group]
  obtain ⟨h, hh⟩ := isConj_iff.mp (hC.setup.isConj hC.hd (hC.isBlock_alpha.subset hvα))
  have hhN : h ∈ Subgroup.normalizer hC.alpha := by
    by_contra hn
    exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hn) hvα
      ⟨hC.d, hC.d_mem_alpha, hh⟩
  have hgu : k * h * hC.d * (k * h)⁻¹ = v := by
    rw [show k * h * hC.d * (k * h)⁻¹ = k * (h * hC.d * h⁻¹) * k⁻¹ by group, hh]
    group
  have hwα : (k * h)⁻¹ * c * (k * h) ∉ hC.alpha := by
    intro hw
    apply hcβ
    rw [hk]
    refine ⟨k⁻¹ * c * k, ?_, show k * (k⁻¹ * c * k) * k⁻¹ = c by group⟩
    have h' := (Subgroup.mem_set_normalizer_iff.mp hhN _).mp hw
    rwa [show h * ((k * h)⁻¹ * c * (k * h)) * h⁻¹ = k⁻¹ * c * k by group] at h'
  have hwD : (k * h)⁻¹ * c * (k * h) ∈ D := by
    have h' := hC.setup.normal (k * h)⁻¹ c hc
    rwa [inv_inv] at h'
  have hwu : ¬ Commute ((k * h)⁻¹ * c * (k * h)) hC.d := by
    intro hcomm
    have h' := hcomm.conj (k * h)
    rw [hgu, show k * h * ((k * h)⁻¹ * c * (k * h)) * (k * h)⁻¹ = c by group] at h'
    exact hvc h'.symm
  have hwA : (k * h)⁻¹ * c * (k * h) ∈ AalphaStar D hC.alpha := by
    rw [hC.AalphaStar_eq_diff_alpha]
    exact ⟨⟨hwD, hwu⟩, hwα⟩
  have hord : orderOf (hC.d * ((k * h)⁻¹ * c * (k * h))) = 3 := by
    rw [← h3, show hC.d * ((k * h)⁻¹ * c * (k * h)) = (k * h)⁻¹ * (v * c) * (k * h) by
      rw [← hgu]; group]
    exact (SemiconjBy.orderOf_eq (k * h)⁻¹ (by unfold SemiconjBy; group)).symm
  obtain ⟨p, -, hpA⟩ := exists_prime_orderOf_eq_AalphaStar hC hsecond
  have hp3 : p = 3 := (hpA _ hwA).symm.trans hord
  obtain ⟨w', hw', hw'3⟩ := sevenThree hC hrad (fun _ _ x y t _ _ _ h => hsecond x y t h)
    (fun w hw => (hpA w hw).trans hp3) hnot3
  exact hw'3 ((hpA w' hw').trans hp3)

theorem oddCore_le_center_Halpha_of_widthTwo
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hA : ∃ x ∈ DalphaStar D hC.alpha, ∃ y ∈ DalphaStar D hC.alpha, x ≠ y ∧ Commute x y)
    (hB : ¬ CFSG.oddCore ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha) →
      ∀ x ∈ DstarH hC, ∀ y ∈ DstarH hC,
        orderOf ((x : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) *
          (y : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha))) ∈
            ({1, 2, 3} : Set ℕ)) :
    CFSG.oddCore ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha) := by
  by_contra hK
  have h3 := hB hK
  have hW1 : ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c :=
    sixSeven hC (QZ.faithfulOnBlocks_of_localSecond hC hrad
      (fun _ _ x y t _ _ _ h => hsecond x y t h)) (fun u _ v _ w h => hsecond u w v h)
  have hC1 : ∀ c ∈ DstarH hC, ∀ v ∈ DstarH hC,
      commSet (DstarH hC) c = commSet (DstarH hC) v →
        (c : ↥(Halpha D hC.alpha) ⧸ CFSG.oddCore ↥(Halpha D hC.alpha)) = v := by
    intro c hc v hv hcv
    obtain ⟨r, hr, rfl⟩ := exists_conj_of_commSet_eq
      ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩
      (CFSG.EvenSporadicStandard.RuStd.S2.Close.odd_card_oddCore _)
      (CFSG.EvenSporadicStandard.RuStd.S2.Close.oddCore_quotient_eq_bot _) h3 hc hv hcv
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff r).mpr hr, one_mul, inv_one, mul_one]
  obtain ⟨v, hv⟩ := DstarH_nonempty hC
  obtain ⟨β, hβ, hvβ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hv)
  obtain ⟨c, hc, hcv, hcimg⟩ := exists_not_commute_mk_ne hC hA hv
  have hvD : (v : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hv)
  have hcD : (c : G) ∈ D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hc)
  have hcβ : (c : G) ∉ β := fun h =>
    hcimg (hC1 c hc v hv (commSet_DstarH_eq_of_mem hC hW1 hβ h hvβ))
  obtain ⟨d, hd⟩ : ∃ d, ¬ (d ∈ commSet (DstarH hC) c ↔ d ∈ commSet (DstarH hC) v) :=
    not_forall.mp fun h => hcimg (hC1 c hc v hv (Set.ext h))
  have hdΘ : d ∈ DstarH hC := by
    by_contra h
    exact hd (iff_of_false (fun h' => h h'.1) (fun h' => h h'.1))
  have hdv : d ≠ v := by
    rintro rfl
    exact hd (iff_of_false (fun h' => hcv h'.2.1.symm) (fun h' => h'.2.2 rfl))
  have hdc : d ≠ c := by
    rintro rfl
    exact hd (iff_of_false (fun h' => h'.2.2 rfl) (fun h' => hcv h'.2.1))
  have hord : orderOf ((v : G) * (c : G)) = 3 := by
    by_cases hdcomm : Commute d v
    · have hdc' : ¬ Commute d c := fun h =>
        hd ⟨fun _ => ⟨hdΘ, hdcomm, hdv⟩, fun _ => ⟨hdΘ, h, hdc⟩⟩
      exact orderOf_mul_eq_three_of_mem_DstarH hC hsecond h3 hv hc hdΘ (Ne.symm hcimg)
        (fun h => hcv h.symm) hdcomm.symm (Ne.symm hdv) hdc'
    · have hdc' : Commute d c := by
        by_contra h
        exact hd (iff_of_false (fun h' => h h'.2.1) (fun h' => hdcomm h'.2.1))
      have h := orderOf_mul_eq_three_of_mem_DstarH hC hsecond h3 hc hv hdΘ hcimg hcv
        hdc'.symm (Ne.symm hdc) hdcomm
      rwa [show (v : G) * (c : G) = ((c : G) * (v : G))⁻¹ by
        rw [mul_inv_rev, hC.setup.oddT.inv_eq hvD, hC.setup.oddT.inv_eq hcD], orderOf_inv]
  exact orderOf_mul_ne_three_of_mem_Dalpha hC hrad hsecond hnot3 hβ hvβ hcD hcβ
    (fun h => hcv (Submonoid.commute_coe_coe.mp h.symm)) hord

end CFSG.OddTranspositions

end
