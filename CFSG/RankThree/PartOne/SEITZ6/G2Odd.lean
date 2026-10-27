module

public import CFSG.RankThree.PartOne.SEITZ6.G2Cent
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxGold
public import CFSG.Dihedral.FourgroupFixedOrder
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
  CFSG.DihedralBlueprint

theorem odd_normalized_trivial_sub {D : Type*} [Group D] [Finite D] (Q A C : Subgroup D)
    [Q.Normal] (hQ : IsPGroup 2 Q) [hAs : IsSimpleGroup A] (hA2 : ¬ IsPGroup 2 A)
    (hAe : Even (Nat.card A))
    (hD : ∀ d : D, ∃ q ∈ Q, ∃ a ∈ A, d = q * a) (hC : Odd (Nat.card C))
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C) : C = ⊥ := by
  classical
  let π : D →* D ⧸ Q := QuotientGroup.mk' Q
  have hAQ : ∀ a ∈ A, a ∈ Q → a = 1 := by
    intro a ha haQ
    have hn : ((A ⊓ Q).subgroupOf A).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : D) ∈ Q := (Subgroup.mem_inf.1 hn).2
      exact Subgroup.mem_inf.2 ⟨A.mul_mem (A.mul_mem g.2 n.2) (A.inv_mem g.2),
        Subgroup.Normal.conj_mem ‹_› _ hn' _⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ Q).subgroupOf A) with h | h
    · have : (⟨a, ha⟩ : A) ∈ (A ⊓ Q).subgroupOf A := Subgroup.mem_inf.2 ⟨ha, haQ⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hA2
      have hAle : A ≤ Q := fun a ha => by
        have : (⟨a, ha⟩ : A) ∈ (A ⊓ Q).subgroupOf A := by rw [h]; trivial
        exact (Subgroup.mem_inf.1 this).2
      exact IsPGroup.to_le hQ hAle
  let ρ : A →* D ⧸ Q := π.comp A.subtype
  have hρinj : Function.Injective ρ := by
    intro a a' h
    have h1 : (a : D)⁻¹ * a' ∈ Q := QuotientGroup.eq.1 h
    have h2 : (a : D)⁻¹ * a' = 1 := hAQ _ (A.mul_mem (A.inv_mem a.2) a'.2) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hπA : ∀ x : D ⧸ Q, ∃ a ∈ A, π a = x := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, a, ha, rfl⟩ := hD d
    refine ⟨a, ha, ?_⟩
    show ((a : D) : D ⧸ Q) = ((q * a : D) : D ⧸ Q)
    rw [QuotientGroup.eq]
    have := ‹Q.Normal›.conj_mem q hq (a : D)⁻¹
    simpa [mul_assoc] using this
  have hρsurj : Function.Surjective ρ := fun x => by
    obtain ⟨a, ha, rfl⟩ := hπA x
    exact ⟨⟨a, ha⟩, rfl⟩
  let e : A ≃* D ⧸ Q := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have : IsSimpleGroup (D ⧸ Q) := MulEquiv.isSimpleGroup e.symm
  have hcard : Nat.card (D ⧸ Q) = Nat.card A := (Nat.card_congr e.toEquiv).symm
  have hCn : (C.map π).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hn
    obtain ⟨a, ha, rfl⟩ := hπA g
    exact ⟨a * c * a⁻¹, hAC a ha c hc, by simp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map π) with h | h
  · have hCQ : C ≤ Q := by
      have := (Subgroup.map_eq_bot_iff C).1 h
      rwa [QuotientGroup.ker_mk'] at this
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hQ ⟨c, hCQ hc⟩
    have hk' : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf c ∣ Nat.card C := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
      simpa [Subgroup.orderOf_mk] using this
    have h3 : Odd (orderOf c) := Odd.of_dvd_nat hC h2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hi0 : i = 0 := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exact h0
      · exfalso
        rw [hi] at h3
        exact (Nat.not_odd_iff_even.2 ((Nat.even_pow' h0.ne').2 even_two)) h3
    rw [hi0, pow_zero] at hi
    exact orderOf_eq_one_iff.1 hi
  · exfalso
    have h1 : Nat.card (D ⧸ Q) ∣ Nat.card C := by
      have := Subgroup.card_map_dvd C π
      rwa [h, Subgroup.card_top] at this
    have h2 : Odd (Nat.card (D ⧸ Q)) := Odd.of_dvd_nat hC h1
    rw [hcard] at h2
    exact (Nat.not_even_iff_odd.2 h2) hAe

theorem odd_normalized_trivial {G : Type*} [Group G] [Finite G] (D Q A C : Subgroup G)
    (hQD : Q ≤ D) (hAD : A ≤ D) (hCD : C ≤ D)
    (hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hQ : IsPGroup 2 Q)
    (hAs : IsSimpleGroup A) (hA2 : ¬ IsPGroup 2 A) (hAe : Even (Nat.card A))
    (hD : ∀ d ∈ D, ∃ q ∈ Q, ∃ a ∈ A, d = q * a)
    (hC : Odd (Nat.card C)) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C) : C = ⊥ := by
  have hQn' : (Q.subgroupOf D).Normal := ⟨fun n hn g => hQn g.1 g.2 n.1 hn⟩
  have eQ : Q.subgroupOf D ≃* Q := Subgroup.subgroupOfEquivOfLe hQD
  have eA : A.subgroupOf D ≃* A := Subgroup.subgroupOfEquivOfLe hAD
  have eC : C.subgroupOf D ≃* C := Subgroup.subgroupOfEquivOfLe hCD
  have : IsSimpleGroup (A.subgroupOf D) := MulEquiv.isSimpleGroup eA
  have hQ' : IsPGroup 2 (Q.subgroupOf D) := IsPGroup.of_equiv hQ eQ.symm
  have hA2' : ¬ IsPGroup 2 (A.subgroupOf D) := fun h => hA2 (IsPGroup.of_equiv h eA)
  have hAe' : Even (Nat.card (A.subgroupOf D)) := by rwa [Nat.card_congr eA.toEquiv]
  have hC' : Odd (Nat.card (C.subgroupOf D)) := by rwa [Nat.card_congr eC.toEquiv]
  have hD' : ∀ d : D, ∃ q ∈ Q.subgroupOf D, ∃ a ∈ A.subgroupOf D, d = q * a := by
    intro d
    obtain ⟨q, hq, a, ha, hqa⟩ := hD d.1 d.2
    exact ⟨⟨q, hQD hq⟩, hq, ⟨a, hAD ha⟩, ha, Subtype.ext hqa⟩
  have hAC' : ∀ a ∈ A.subgroupOf D, ∀ c ∈ C.subgroupOf D, a * c * a⁻¹ ∈ C.subgroupOf D :=
    fun a ha c hc => hAC a.1 ha c.1 hc
  have h := odd_normalized_trivial_sub (Q.subgroupOf D) (A.subgroupOf D) (C.subgroupOf D) hQ' hA2'
    hAe' hD' hC' hAC'
  rw [eq_bot_iff]
  intro c hc
  have : (⟨c, hCD hc⟩ : D) ∈ C.subgroupOf D := hc
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

variable {K : Type} [Field K]

theorem ordProd_mem_Ug (c : ℕ → K) : ordProd c ∈ Ug K := by
  have h : ∀ p ∈ posList, ∀ x : K, xp p x ∈ Ug K := fun p hp x =>
    (le_iSup₂_of_le (f := fun p (_ : p ∈ posList) => Xp K p) p hp le_rfl)
      (xp_mem_Xp p (lt_twelve_of_mem_posList hp) x)
  unfold ordProd
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h 0 (by simp [posList]) _)
    (h 1 (by simp [posList]) _)) (h 4 (by simp [posList]) _)) (h 8 (by simp [posList]) _))
    (h 3 (by simp [posList]) _)) (h 7 (by simp [posList]) _)

theorem card_Ug [CharP K 2] : Nat.card (Ug K) = Nat.card K ^ 6 := by
  let f : (Fin 6 → K) → Ug K := fun v =>
    ⟨ordProd (mk6 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)), ordProd_mem_Ug _⟩
  have hfv : ∀ v, (f v : adjointGroup .G2 K) =
      xp 0 (v 0) * xp 1 (v 1) * xp 4 (v 2) * xp 8 (v 3) * xp 3 (v 4) * xp 7 (v 5) :=
    fun v => ordProd_mk6 _ _ _ _ _ _
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h' := congrArg Subtype.val h
      rw [hfv, hfv] at h'
      obtain ⟨h0, h1, h4, h8, h3, h7⟩ := six_inj h'
      funext i
      fin_cases i <;> simpa
    · intro u
      obtain ⟨c, hc⟩ := exists_ordProd u.2
      refine ⟨![c 0, c 1, c 4, c 8, c 3, c 7], Subtype.ext ?_⟩
      rw [hfv, hc]
      unfold ordProd
      simp
  have h6 : Nat.card (Fin 6) = 6 := by simp
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, h6]

theorem Ug_isPGroup [CharP K 2] [Finite K] : IsPGroup 2 (Ug K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  exact ⟨6 * m, by rw [card_Ug, Nat.card_eq_fintype_card, hm, ← pow_mul, mul_comm]⟩


theorem cent_conj_Qg [CharP K 2] {g : adjointGroup .G2 K} {d : K} (hd : d ≠ 0)
    (hg : g * xp 7 d * g⁻¹ = xp 7 d) {u : adjointGroup .G2 K} (hu : u ∈ Qg K) :
    g * u * g⁻¹ ∈ Qg K := by
  have hg' : g * xp 7 d * g⁻¹ ∈ Up K := by
    rw [hg]
    exact mem_Up_iff.2 ⟨d, 0, by simp [xp_zero]⟩
  rcases bruhat_stab_h hd hg' with hB | ⟨b, hb, a1, rfl⟩
  · exact borel_conj_Qg hB hu
  · have h1 := X1_conj_Qg a1 hu
    have h2 := n1_conj_Qg h1
    have h3 := borel_conj_Qg hb h2
    rwa [show b * (weylElement .G2 K e1 * (xp 1 a1 * u * (xp 1 a1)⁻¹) *
        (weylElement .G2 K e1)⁻¹) * b⁻¹ =
        b * weylElement .G2 K e1 * xp 1 a1 * u * (b * weylElement .G2 K e1 * xp 1 a1)⁻¹ by
      group] at h3

theorem psiA_range_simple [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (psiA K).range := by
  have := isSimpleGroup_SL2 (F := K) h4
  exact MulEquiv.isSimpleGroup (MonoidHom.ofInjective (psiA_injective (K := K))).symm

theorem card_psiA_range [CharP K 2] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (psiA K).range = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (psiA_injective (K := K))).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]

theorem psiA_range_not_pGroup [CharP K 2] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    ¬ IsPGroup 2 (psiA K).range := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h
  rw [card_psiA_range hK] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (three_dvd_two_pow_sq_sub_one n).mul_left _
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem psiA_range_even [CharP K 2] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Even (Nat.card (psiA K).range) := by
  rw [card_psiA_range hK]
  exact (Nat.even_pow' (by omega)).2 even_two |>.mul_right _

theorem cent_R_trivial [CharP K 2] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {H : Subgroup (adjointGroup .G2 K)} (hL : Lp K ≤ H) {R : Subgroup (adjointGroup .G2 K)}
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hodd : Odd (Nat.card R)) {d : K} (hd : d ≠ 0) :
    R ⊓ Subgroup.centralizer ({xp 7 d} : Set (adjointGroup .G2 K)) = ⊥ := by
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact four_le_two_pow hn
  set D := Subgroup.centralizer ({xp 7 d} : Set (adjointGroup .G2 K)) with hDdef
  have hmemD : ∀ g : adjointGroup .G2 K, g ∈ D ↔ g * xp 7 d * g⁻¹ = xp 7 d := by
    intro g
    rw [hDdef, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      have := h (xp 7 d) (Set.mem_singleton _)
      rw [← this]
      group
    · intro h x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      calc xp 7 d * g = (g * xp 7 d * g⁻¹) * g := by rw [h]
        _ = g * xp 7 d := by group
  have hAD := psiA_range_le_cent (K := K) d
  have hQD : Qg K ≤ D := fun g hg => (hmemD g).2 (by
    rw [(Ug_comm_xp7 (Qg_le_Ug hg) d)]
    group)
  refine odd_normalized_trivial D (Qg K) (psiA K).range (R ⊓ D) hQD hAD inf_le_right
    (fun g hg q hq => cent_conj_Qg hd ((hmemD g).1 hg) hq)
    (IsPGroup.to_le Ug_isPGroup Qg_le_Ug) (psiA_range_simple h4) (psiA_range_not_pGroup hK)
    (psiA_range_even (by omega) hK) (fun g hg => cent_decomp hd ((hmemD g).1 hg))
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)) ?_
  intro a ha c hc
  exact ⟨hRn a (hL (psiA_range_le_Lp ha)) c hc.1,
    D.mul_mem (D.mul_mem (hAD ha) hc.2) (D.inv_mem (hAD ha))⟩

theorem xp7_isInvolution [CharP K 2] {c : K} (hc : c ≠ 0) :
    CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (xp 7 c : adjointGroup .G2 K) :=
  ⟨xp_ne_one (by norm_num) hc, by rw [pow_two, xp_mul_self]⟩

theorem odd_core_trivial [CharP K 2] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {H : Subgroup (adjointGroup .G2 K)} (hL : Lp K ≤ H) {R : Subgroup (adjointGroup .G2 K)}
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hodd : Odd (Nat.card R)) :
    R = ⊥ := by
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact four_le_two_pow hn
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_one (K := K) h4
  have hab : (xp 7 (1 : K) : adjointGroup .G2 K) ≠ xp 7 t := fun h =>
    ht1 (xPar_injective (F := rootOperatorFamily .G2) (K := K) (isRoot_rt (by norm_num : 7 < 12))
      h).symm
  have hcomm : Commute (xp 7 (1 : K) : adjointGroup .G2 K) (xp 7 t) := by
    show xp 7 (1 : K) * xp 7 t = xp 7 t * xp 7 1
    rw [← xp_add, ← xp_add, add_comm]
  obtain ⟨V, hVH, hV, haV, hbV⟩ :=
    CFSG.GorensteinWalter.exists_kleinFour_of_commuting_involutions_le H _ _
    (xp7_isInvolution one_ne_zero) (xp7_isInvolution ht0) hab hcomm (hL (xp7_mem_Lp 1))
    (hL (xp7_mem_Lp t))
  have hnorm : NormalizedBy R V := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hRn v (hVH hv) r hr, fun hr => ?_⟩
    have := hRn v⁻¹ (H.inv_mem (hVH hv)) _ hr
    rwa [show v⁻¹ * (v * r * v⁻¹) * v⁻¹⁻¹ = r by group] at this
  have hsolv : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hab1 : (xp 7 (1 : K) : adjointGroup .G2 K) * xp 7 t = xp 7 (1 + t) := (xp_add 7 1 t).symm
  have h1t : (1 : K) + t ≠ 0 := fun h => ht1 (CharTwo.add_eq_zero.1 h).symm
  have hw := ambient_fourgroup_fixed_order_identity V R hV hodd hsolv hnorm (xp 7 1) (xp 7 t)
    haV hbV (xp_ne_one (by norm_num) one_ne_zero) (xp_ne_one (by norm_num) ht0) hab
  rw [hab1, cent_R_trivial hn hK hL hRn hodd one_ne_zero, cent_R_trivial hn hK hL hRn hodd ht0,
    cent_R_trivial hn hK hL hRn hodd h1t] at hw
  simp only [Subgroup.card_bot, mul_one] at hw
  exact Subgroup.card_eq_one.1 (Nat.eq_one_of_mul_eq_one_right hw)

end CFSG.RankThree.PartOne.SEITZ6
