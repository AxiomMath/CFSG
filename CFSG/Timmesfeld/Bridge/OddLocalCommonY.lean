module

public import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

@[expose] def CNBelow (m : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (E : Set H), Nat.card H < m → Asc72.Setup H E →
    (∀ a ∈ E, ∀ b ∈ E, Reach E a b) → OddTransp.MeetsSq E →
    ∀ d ∈ E, ∀ x ∈ E, ¬ Commute d x → ∃ e ∈ E, Commute e d ∧ Commute e x

@[expose] def NPCDischarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.Setup G D → commutator G = ⊤ →
    CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G) → NoPerfectCentralExt G (CFSG.pCore 2 G)

namespace OddLocal

variable {G : Type} [Group G] {D : Set G}

section Subgroup

variable (hD : IsOddTransp D) (hN : IsNormalSet D) {H : Subgroup G} {y : G} (hyH : y ∈ H)
  (hyD : y ∈ D) (hgen : H ≤ Subgroup.closure (hClass H y))
include hD hN hyH hyD hgen

omit hD hN hyD hgen in
theorem conn_preimage (hconn : ∀ a ∈ hClass H y, ∀ b ∈ hClass H y, Reach (hClass H y) a b) :
    ∀ a ∈ ((↑) : H → G) ⁻¹' hClass H y, ∀ b ∈ ((↑) : H → G) ⁻¹' hClass H y,
      Reach (((↑) : H → G) ⁻¹' hClass H y) a b := fun _ ha _ hb =>
  (reach_preimage_iff (hClass_subset_subgroup hyH)).mpr (hconn _ ha _ hb)

omit hD hN hyD hgen in
theorem meetsSq_preimage (hsq : ∃ u ∈ hClass H y, ∃ v ∈ hClass H y, u ≠ v ∧ Commute u v ∧
    u * v ∈ hClass H y) : OddTransp.MeetsSq (((↑) : H → G) ⁻¹' hClass H y) := by
  obtain ⟨u, hu, v, hv, huv, hc, huvC⟩ := hsq
  have hsub := hClass_subset_subgroup hyH
  exact ⟨⟨u, hsub hu⟩, hu, ⟨v, hsub hv⟩, hv, fun h => huv (congrArg Subtype.val h),
    Subtype.ext hc.eq, huvC⟩

theorem exists_common_of_cnBelow [Finite G] {m : ℕ} (IH : CNBelow m) (hcard : Nat.card H < m)
    (hconn : ∀ a ∈ hClass H y, ∀ b ∈ hClass H y, Reach (hClass H y) a b)
    (hsq : ∃ u ∈ hClass H y, ∃ v ∈ hClass H y, u ≠ v ∧ Commute u v ∧ u * v ∈ hClass H y)
    {d x : G} (hd : d ∈ hClass H y) (hx : x ∈ hClass H y) (hdx : ¬ Commute d x) :
    ∃ e ∈ hClass H y, Commute e d ∧ Commute e x := by
  have hsub := hClass_subset_subgroup hyH
  obtain ⟨e, he, hed, hex⟩ := IH H _ hcard (setup_hClass hD hN hyH hyD hgen)
    (conn_preimage hyH hconn) (meetsSq_preimage hyH hsq)
    ⟨d, hsub hd⟩ hd ⟨x, hsub hx⟩ hx (fun h => hdx (h.map H.subtype))
  exact ⟨e, he, hed.map H.subtype, hex.map H.subtype⟩

theorem isBender_of_not_conn [Finite G] (h16 : OddTranspZStar)
    (hconn : ¬ ∀ a ∈ hClass H y, ∀ b ∈ hClass H y, Reach (hClass H y) a b)
    (hsq : ∃ u ∈ hClass H y, ∃ v ∈ hClass H y, u ≠ v ∧ Commute u v ∧ u * v ∈ hClass H y) :
    CFSG.BenderSuzuki.IsBenderGroup (H ⧸ zStar H) := by
  have hS' := setup_hClass hD hN hyH hyD hgen
  have hsub := hClass_subset_subgroup hyH
  refine h16 H _ hS'.oddT hS'.normal hS'.gen (meetsSq_preimage hyH hsq) ?_
  push Not at hconn
  obtain ⟨a, ha, b, hb, hab⟩ := hconn
  exact ⟨⟨a, hsub ha⟩, ha, ⟨b, hsub hb⟩, hb, fun h => hab
    ((reach_preimage_iff hsub).mp h)⟩

end Subgroup

@[expose] def yGroup (D : Set G) (S : Sylow 2 G) (y : G) : Subgroup G :=
  Subgroup.closure (insert y (D ∩ (S : Set G)))

theorem mem_yGroup_left (D : Set G) (S : Sylow 2 G) (y : G) : y ∈ yGroup D S y :=
  Subgroup.subset_closure (Set.mem_insert y _)

theorem mem_yGroup_of_mem {S : Sylow 2 G} {y e : G} (he : e ∈ D) (heS : e ∈ S) :
    e ∈ yGroup D S y :=
  Subgroup.subset_closure (Set.mem_insert_of_mem y ⟨he, heS⟩)

theorem exists_sylow_of_commute [Finite G] {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) :
    ∃ S : Sylow 2 G, a ∈ S ∧ b ∈ S ∧ c ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpair : ∀ u ∈ ({a, b, c} : Set G), ∀ v ∈ ({a, b, c} : Set G), Commute u v := by
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl)
    all_goals first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  have h2 : ∀ u ∈ ({a, b, c} : Set G), u * u = 1 := by
    rintro u (rfl | rfl | rfl) <;> assumption
  have hP : IsPGroup 2 (Subgroup.closure ({a, b, c} : Set G)) :=
    isPGroup_two_of_mul_self fun g hg => mul_self_eq_one_of_mem_closure hpair h2 hg
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact ⟨S, hS (Subgroup.subset_closure (by simp)), hS (Subgroup.subset_closure (by simp)),
    hS (Subgroup.subset_closure (by simp))⟩

section Conf

variable (hS : Setup G D) {d x y : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
  (hy : y ∈ D) (hyc : y ∈ Subgroup.closure {d, x}) (hdy : ¬ Commute d y)
  (hno : ∀ e ∈ D, Commute e d → Commute e x → False)
include hS hd hx hdx hy hyc hdy hno

theorem not_commute_pair {e : G} (he : e ∈ D) (hed : Commute e d) (hey : Commute e y) : False :=
  hno e he hed (commute_of_commute_of_mem_closure hS.oddT hd hx hdx hy hyc hdy he hed hey)

theorem not_commute_of_mem_sylow {S : Sylow 2 G} (hdS : d ∈ S) {e : G} (he : e ∈ D)
    (heS : e ∈ S) : ¬ Commute e y := fun hey =>
  not_commute_pair hS hd hx hdx hy hyc hdy hno he
    (hS.oddT.commute_of_isPGroup S.isPGroup' he hd heS hdS) hey

theorem mem_hClass_of_mem_sylow {S : Sylow 2 G} (hdS : d ∈ S) {e : G} (he : e ∈ D)
    (heS : e ∈ S) : e ∈ hClass (yGroup D S y) y := by
  have hey := not_commute_of_mem_sylow hS hd hx hdx hy hyc hdy hno hdS he heS
  obtain ⟨g, hg, hge⟩ := hS.oddT.exists_conj hy he (fun h => hey h.symm)
  have hle : Subgroup.closure ({y, e} : Set G) ≤ yGroup D S y := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact mem_yGroup_left D S w
    · exact mem_yGroup_of_mem he heS
  exact ⟨g, hle hg, hge.symm⟩

theorem yGroup_le_closure_hClass {S : Sylow 2 G} (hdS : d ∈ S) :
    yGroup D S y ≤ Subgroup.closure (hClass (yGroup D S y) y) := by
  rw [yGroup, Subgroup.closure_le]
  rintro w (rfl | ⟨hw, hwS⟩)
  · exact Subgroup.subset_closure (self_mem_hClass _ w)
  · exact Subgroup.subset_closure (mem_hClass_of_mem_sylow hS hd hx hdx hy hyc hdy hno hdS hw hwS)

theorem setup_yClass {S : Sylow 2 G} (hdS : d ∈ S) :
    Setup (yGroup D S y) (((↑) : yGroup D S y → G) ⁻¹' hClass (yGroup D S y) y) :=
  setup_hClass hS.oddT hS.normal (mem_yGroup_left D S y) hy
    (yGroup_le_closure_hClass hS hd hx hdx hy hyc hdy hno hdS)

theorem meetsSq_yClass [Finite G] (hsq : OddTransp.MeetsSq D) {S : Sylow 2 G} (hdS : d ∈ S) :
    ∃ u ∈ hClass (yGroup D S y) y, ∃ v ∈ hClass (yGroup D S y) y, u ≠ v ∧ Commute u v ∧
      u * v ∈ hClass (yGroup D S y) y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, v, hv, huv, hc, huvD⟩ := hsq
  obtain ⟨T, huT, hvT, -⟩ := exists_sylow_of_commute (hS.oddT.mul_self_eq_one hu)
    (hS.oddT.mul_self_eq_one hv) (hS.oddT.mul_self_eq_one hu) hc (Commute.refl u) hc.symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hconjS : ∀ {w : G}, w ∈ T → g * w * g⁻¹ ∈ S := by
    intro w hw
    rw [← hg, ← SetLike.mem_coe, Sylow.coe_smul]
    exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  have hmem : ∀ {w : G}, w ∈ D → w ∈ T → g * w * g⁻¹ ∈ hClass (yGroup D S y) y :=
    fun hw hwT => mem_hClass_of_mem_sylow hS hd hx hdx hy hyc hdy hno hdS (hS.normal g _ hw)
      (hconjS hwT)
  refine ⟨g * u * g⁻¹, hmem hu huT, g * v * g⁻¹, hmem hv hvT, fun h => huv (by simpa using h),
    (Commute.conj_iff g).mpr hc, ?_⟩
  have := hmem huvD (T.mul_mem huT hvT)
  simpa [mul_assoc] using this

section Third

variable [Finite G] (hcenter : Subgroup.center G = ⊥) {d₁ : G} {n : ℕ}
  (htri : IsTriangle D d y d₁) (hn : Odd n) (hord : orderOf (d * d₁ * y) = 2 * n)
include hcenter htri hn hord

omit hcenter hx hdx hno [Finite G] in
theorem yGroup_le_centralizer {S : Sylow 2 G} (hdS : d ∈ S) (hd₁S : d₁ ∈ S)
    (hzS : (d * d₁ * y) ^ n ∈ S) :
    (d * d₁ * y) ^ n ∈ yGroup D S y ∧
      yGroup D S y ≤ Subgroup.centralizer {(d * d₁ * y) ^ n} := by
  obtain ⟨hzz, -, hzd, hzd₁, hzy, hw⟩ := htri.third_kind hS.oddT hS.normal hn hord
  set z := (d * d₁ * y) ^ n
  have hd₁ := htri.2.1
  have hdd₁ : Commute d d₁ := htri.2.2.2.2.1
  have hwS : d * d₁ * z ∈ S := S.mul_mem (S.mul_mem hdS hd₁S) hzS
  have hdd2 : d * d₁ * (d * d₁) = 1 := htri.uv_mul_self hS.oddT
  have hzeq : z = d * d₁ * (d * d₁ * z) := by rw [← mul_assoc, hdd2, one_mul]
  refine ⟨?_, ?_⟩
  · rw [hzeq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_yGroup_of_mem hd hdS)
      (mem_yGroup_of_mem hd₁ hd₁S)) (mem_yGroup_of_mem hw hwS)
  · rw [yGroup, Subgroup.closure_le]
    rintro e (rfl | ⟨he, heS⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzy.eq.symm
    · have hc : ∀ f ∈ D, f ∈ S → Commute e f := fun f hf hfS =>
        hS.oddT.commute_of_isPGroup S.isPGroup' he hf heS hfS
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hzeq]
      exact (((hc d hd hdS).mul_right (hc d₁ hd₁ hd₁S)).mul_right (hc _ hw hwS)).eq

omit hx hdx hno in
theorem card_yGroup_lt {S : Sylow 2 G} (hdS : d ∈ S) (hd₁S : d₁ ∈ S)
    (hzS : (d * d₁ * y) ^ n ∈ S) : Nat.card (yGroup D S y) < Nat.card G := by
  obtain ⟨-, hz1, -, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  obtain ⟨-, hle⟩ := yGroup_le_centralizer hS hd hy hyc hdy htri hn hord hdS hd₁S hzS
  have hlt : yGroup D S y < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hz1 ?_
    have hzc : (d * d₁ * y) ^ n ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (htop ▸ Subgroup.mem_top g))
    rw [hcenter, Subgroup.mem_bot] at hzc
    exact hzc
  have := Subgroup.card_lt_of_lt hlt
  rwa [Subgroup.card_top] at this

structure YData (D : Set G) (d d₁ y : G) (n : ℕ) where
  S : Sylow 2 G
  a : G
  d_memS : d ∈ S
  d₁_memS : d₁ ∈ S
  z_memS : (d * d₁ * y) ^ n ∈ S
  a_mem : a ∈ hClass (yGroup D S y) y
  a_memS : a ∈ S
  a_ne : a ≠ d
  a_comm : Commute a d
  mul_not_mem : d * a ∉ D
  sq : ∃ u ∈ hClass (yGroup D S y) y, ∃ v ∈ hClass (yGroup D S y) y, u ≠ v ∧ Commute u v ∧
    u * v ∈ hClass (yGroup D S y) y
  third : ∀ e₀ ∈ D, e₀ ∈ S → ∃ f ∈ hClass (yGroup D S y) y, ∃ z' ∈ yGroup D S y,
    (∀ g ∈ yGroup D S y, Commute z' g) ∧ d * e₀ * a = f * z'

theorem exists_yData (hn1 : 1 < n) (h14 : OddTranspThirdKind) (h16 : OddTranspZStar)
    (hnpc : NPCDischarge) (IH : CNBelow (Nat.card G)) (hsq : OddTransp.MeetsSq D) :
    Nonempty (YData D d d₁ y n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzz, hz1, hzd, hzd₁, hzy, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  have hd₁ : d₁ ∈ D := htri.2.1
  have hdd₁ : Commute d d₁ := htri.2.2.2.2.1
  obtain ⟨S, hdS, hd₁S, hzS⟩ := exists_sylow_of_commute (hS.oddT.mul_self_eq_one hd)
    (hS.oddT.mul_self_eq_one hd₁) hzz hdd₁ hzd.symm hzd₁.symm
  set Y := yGroup D S y with hYdef
  obtain ⟨hzY, hYc⟩ := yGroup_le_centralizer hS hd hy hyc hdy htri hn hord hdS hd₁S hzS
  have hcard := card_yGroup_lt hS hd hy hyc hdy hcenter htri hn hord hdS hd₁S hzS
  have hgenY := yGroup_le_closure_hClass hS hd hx hdx hy hyc hdy hno hdS
  have hsqY := meetsSq_yClass hS hd hx hdx hy hyc hdy hno hsq hdS
  have hmemE : ∀ {e : G}, e ∈ D → e ∈ S → e ∈ hClass Y y := fun he heS =>
    mem_hClass_of_mem_sylow hS hd hx hdx hy hyc hdy hno hdS he heS
  have hdE : d ∈ hClass Y y := hmemE hd hdS
  have hd₁E : d₁ ∈ hClass Y y := hmemE hd₁ hd₁S
  have hyE : y ∈ hClass Y y := self_mem_hClass _ _
  have hyY : y ∈ Y := mem_yGroup_left D S y
  have hnconn : ¬ ∀ a ∈ hClass Y y, ∀ b ∈ hClass Y y, Reach (hClass Y y) a b := by
    intro hconn
    obtain ⟨e, he, hed, hey⟩ := exists_common_of_cnBelow hS.oddT hS.normal hyY hy hgenY IH
      hcard hconn hsqY hdE hyE hdy
    exact not_commute_pair hS hd hx hdx hy hyc hdy hno (hClass_subset hS.normal hy he) hed hey
  have hB := isBender_of_not_conn hS.oddT hS.normal hyY hy hgenY h16 hnconn hsqY
  have hSY := setup_yClass hS hd hx hdx hy hyc hdy hno hdS
  have hsqY' := meetsSq_preimage hyY hsqY
  have hperf : commutator Y = ⊤ := OddTransp.commutator_eq_top hSY hsqY'
  have hnpcY := hnpc Y _ hSY hperf hB
  set P := CFSG.pCore 2 Y with hPdef
  have hPn : P.Normal := CFSG.BaerSuzuki.Helpers.pCore_normal 2
  have hP2 : IsPGroup 2 P := CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2
  set z' : Y := ⟨(d * d₁ * y) ^ n, hzY⟩ with hz'
  have hz'c : z' ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hYc g.2))
  have hz'P : z' ∈ P := by
    have hz'2 : z' * z' = 1 := Subtype.ext hzz
    have hle : Subgroup.zpowers z' ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr hz'c
    have hP' : IsPGroup 2 (Subgroup.zpowers z') := by
      refine isPGroup_two_of_mul_self fun g hg => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz'2, one_zpow]
    exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (Subgroup.normal_of_le_center hle)
      hP' (Subgroup.mem_zpowers z')
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  set d' : Y := ⟨d, mem_yGroup_of_mem hd hdS⟩ with hd'
  obtain ⟨q, hqP, hqd⟩ : ∃ q ∈ P, ¬ Commute q d' := by
    by_contra h
    push Not at h
    have hPc : ∀ q ∈ P, ∀ g : Y, Commute q g := by
      intro q hq
      have hle : (⊤ : Subgroup Y) ≤ Subgroup.centralizer {q} := by
        rw [← hSY.gen, Subgroup.closure_le]
        intro k hk
        obtain ⟨c, rfl⟩ := isConj_iff.mp (hSY.isConj (x := d') hdE hk)
        have hcq := h (c⁻¹ * q * c⁻¹⁻¹) (hPn.conj_mem q hq c⁻¹)
        have h2 : Commute q (c * d' * c⁻¹) := by
          have := hcq.conj c
          rwa [show c * (c⁻¹ * q * c⁻¹⁻¹) * c⁻¹ = q by group] at this
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact h2.symm.eq
      exact fun g => (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))).symm
    have hcomm : ⁅P, (⊤ : Subgroup Y)⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hPc g₁ h₁ g₂
    have hbot := hnpcY ⊥ Subgroup.normal_bot bot_le hcomm
    rw [hperf, inf_top_eq] at hbot
    exact hz'1 (Subgroup.mem_bot.mp (hbot hz'P))
  set a' : Y := q * d' * q⁻¹ with ha'
  set a : G := (a' : G) with ha
  have hd'2 : d' * d' = 1 := Subtype.ext (hS.oddT.mul_self_eq_one hd)
  have hd'i : d'⁻¹ = d' := inv_eq_of_mul_eq_one_right hd'2
  have hda'P : d' * a' ∈ P := by
    have e : d' * a' = (d' * q * d'⁻¹) * q⁻¹ := by rw [ha', hd'i]; group
    rw [e]
    exact P.mul_mem (hPn.conj_mem q hqP d') (P.inv_mem hqP)
  have haE : a ∈ hClass Y y := by
    obtain ⟨h, hh, hdh⟩ := hdE
    refine ⟨(q : G) * h, Y.mul_mem q.2 hh, ?_⟩
    simp only [ha, ha', Subgroup.coe_mul, Subgroup.coe_inv, hd', hdh]
    group
  have haD : a ∈ D := hClass_subset hS.normal hy haE
  have hane : a ≠ d := by
    intro h
    apply hqd
    have h1 : a' = d' := Subtype.ext h
    rw [ha'] at h1
    show q * d' = d' * q
    calc q * d' = q * d' * q⁻¹ * q := by group
      _ = d' * q := by rw [h1]
  have hacomm : Commute a d := by
    by_contra h
    have hodd := hS.oddT.odd_of_not_commute hd haD (fun h' => h h'.symm)
    have h1 := eq_one_of_odd_of_mem_pCore hda'P (by
      rw [← Subgroup.orderOf_coe]
      exact hodd)
    exact hane (hS.oddT.eq_of_mul_eq_one hd (congrArg Subtype.val h1)).symm
  have hdaD : d * a ∉ D := by
    intro hf
    have hfy : Commute (d * a) y := by
      by_contra hfy
      set y' : Y := ⟨y, hyY⟩
      have hy'2 : y' * y' = 1 := Subtype.ext (hS.oddT.mul_self_eq_one hy)
      have hsqP : (d' * a' * y') * (d' * a' * y') ∈ P := by
        have e : (d' * a' * y') * (d' * a' * y') = (d' * a') * (y' * (d' * a') * y'⁻¹) := by
          rw [inv_eq_of_mul_eq_one_right hy'2]
          group
        rw [e]
        exact P.mul_mem hda'P (hPn.conj_mem _ hda'P y')
      have hodd := hS.oddT.odd_of_not_commute hf hy hfy
      have hodd' : Odd (orderOf (d' * a' * y')) := by
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_mul]
        exact hodd
      have hodd2 : Odd (orderOf ((d' * a' * y') * (d' * a' * y'))) := by
        rw [← pow_two, orderOf_pow' _ (by norm_num)]
        exact Odd.of_dvd_nat hodd' (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      have h1 := eq_one_of_odd_of_mem_pCore hsqP hodd2
      have h2 : orderOf (d * a * y) ∣ 2 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [pow_two]
        exact congrArg Subtype.val h1
      have h3 : orderOf (d * a * y) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
        · exact h'
        · rw [h'] at hodd
          exact absurd hodd (by decide)
      rw [orderOf_eq_one_iff] at h3
      have h4 := hS.oddT.eq_of_mul_eq_one hf h3
      apply hdy
      rw [← h4]
      exact (Commute.refl d).mul_right hacomm.symm
    exact not_commute_pair hS hd hx hdx hy hyc hdy hno hf
      ((Commute.refl d).mul_left hacomm) hfy
  have hSY2 : IsPGroup 2 ((S : Subgroup G).subgroupOf Y) :=
    S.isPGroup'.comap_of_injective Y.subtype Subtype.coe_injective
  obtain ⟨SY, hSSY⟩ := hSY2.exists_le_sylow
  have hPSY : P ≤ SY := hP2.le_sylow_of_normal SY
  have hmemSY : ∀ {e : G} (he : e ∈ Y), e ∈ S → (⟨e, he⟩ : Y) ∈ SY := fun he heS =>
    hSSY (Subgroup.mem_subgroupOf.mpr heS)
  obtain ⟨Sst, hSst⟩ := (SY.isPGroup'.map Y.subtype).exists_le_sylow
  have haSst : a ∈ Sst := by
    have : a' ∈ SY := SY.mul_mem (SY.mul_mem (hPSY hqP) (hmemSY _ hdS)) (SY.inv_mem (hPSY hqP))
    exact hSst ⟨a', this, rfl⟩
  have haS : a ∈ S := by
    refine mem_sylow_of_commute hS S haD fun f hf hfS => ?_
    have hfSst : f ∈ Sst := hSst ⟨⟨f, mem_yGroup_of_mem hf hfS⟩,
      hmemSY (mem_yGroup_of_mem hf hfS) hfS, rfl⟩
    exact hS.oddT.commute_of_isPGroup Sst.isPGroup' haD hf haSst hfSst
  set y' : Y := ⟨y, hyY⟩ with hy'
  set d₁' : Y := ⟨d₁, mem_yGroup_of_mem hd₁ hd₁S⟩ with hd₁'
  have htriY : IsTriangle (((↑) : Y → G) ⁻¹' hClass Y y) d' y' d₁' :=
    ⟨hdE, hd₁E, hyE, fun h => htri.2.2.2.1 (congrArg Subtype.val h),
      Subtype.ext hdd₁.eq, fun h => hdy (h.map Y.subtype),
      fun h => htri.2.2.2.2.2.2 (h.map Y.subtype)⟩
  have hordY : orderOf (d' * d₁' * y') = 2 * n := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hord
  have hzY' : (d' * d₁' * y') ^ n = z' := Subtype.ext (by simp [hd', hd₁', hy', hz'])
  have hgenY' : Subgroup.closure (insert y' ((((↑) : Y → G) ⁻¹' hClass Y y) ∩ (SY : Set Y))) =
      ⊤ := by
    apply eq_top_of_le_map
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro w (rfl | ⟨hw, hwS⟩)
    · exact Subgroup.subset_closure ⟨y', Set.mem_insert _ _, rfl⟩
    · exact Subgroup.subset_closure ⟨⟨w, mem_yGroup_of_mem hw hwS⟩, Set.mem_insert_of_mem _
        ⟨hmemE hw hwS, hmemSY _ hwS⟩, rfl⟩
  have hTK : ThirdKindHyp Y (((↑) : Y → G) ⁻¹' hClass Y y) SY d' y' d₁' n :=
    ⟨hSY, htriY, hn, hn1, hordY, hmemSY _ hdS, hmemSY _ hd₁S, hzY' ▸ hmemSY _ hzS, hgenY',
      hnpcY⟩
  have h14Y := (h14 Y _ SY d' y' d₁' n hTK).2
  have had'P : a' * d'⁻¹ ∈ P := by
    rw [hd'i]
    have : Commute a' d' := Subtype.ext hacomm.eq
    rw [this.eq]
    exact hda'P
  refine ⟨⟨S, a, hdS, hd₁S, hzS, haE, haS, hane, hacomm, hdaD, hsqY, ?_⟩⟩
  intro e₀ he₀ he₀S
  obtain ⟨⟨f', z''⟩, hf', hz'', heq⟩ := (h14Y d' ⟨hdE, hmemSY _ hdS⟩
    ⟨e₀, mem_yGroup_of_mem he₀ he₀S⟩ ⟨hmemE he₀ he₀S, hmemSY _ he₀S⟩ a' haE had'P).exists
  refine ⟨f', hf', z'', z''.2, fun g hg => ?_, congrArg Subtype.val heq⟩
  have := Subgroup.mem_center_iff.mp hz''.2 ⟨g, hg⟩
  exact (congrArg Subtype.val this).symm

end Third

end Conf

end OddLocal

end CFSG.Timmesfeld.Bridge
