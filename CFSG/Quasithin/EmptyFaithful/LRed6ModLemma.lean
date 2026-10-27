module

public import CFSG.Quasithin.EmptyFaithful.LRed6Cnt
public import CFSG.Quasithin.EmptyFaithful.LRed6Fix
public import CFSG.Quasithin.EmptyFaithful.LRed6D7
public import CFSG.Quasithin.EmptyFaithful.LRed6G2
public import CFSG.Quasithin.EmptyFaithful.LRed6Hat
public import CFSG.Quasithin.EmptyFaithful.LRed6Orders
public import CFSG.Quasithin.EmptyFaithful.LRed4Irr

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank EmptyFaithfulMultiple.FFL
open scoped commutatorElement

namespace LRed6

section Helpers

theorem pow_index_of_sup_two {G : Type*} [Group G] [Finite G] {H L T : Subgroup G} (hLH : L ≤ H)
    (hT : IsPGroup 2 ↥T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hHT : H = L ⊔ T) :
    ∃ j : ℕ, Nat.card ↥H = 2 ^ j * Nat.card ↥L := by
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hHT]
    exact sup_le Subgroup.le_normalizer hTL
  have hNn : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  have hTH : T ≤ H := hHT ▸ le_sup_right
  let f : ↥T →* ↥H ⧸ L.subgroupOf H :=
    (QuotientGroup.mk' (L.subgroupOf H)).comp (Subgroup.inclusion hTH)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : G) ∈ L ⊔ T := hHT ▸ x.2
    obtain ⟨l, hl, t, ht, hlt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).1 hx
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk (⟨t, hTH ht⟩ : ↥H) : ↥H ⧸ L.subgroupOf H) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    show (⟨t, hTH ht⟩ : ↥H)⁻¹ * x ∈ L.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((⟨t, hTH ht⟩ : ↥H)⁻¹ * x : ↥H) = (t⁻¹ * l * t : G) := by
      show t⁻¹ * (x : G) = t⁻¹ * l * t
      rw [hlt]
      group
    show (((⟨t, hTH ht⟩ : ↥H)⁻¹ * x : ↥H) : G) ∈ L
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l).mp hl |> fun h => by
      simpa using h
  have hQ : IsPGroup 2 (↥H ⧸ L.subgroupOf H) := hT.of_surjective f hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hQ
  refine ⟨j, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf H)
  rw [hj, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv] at h1
  exact h1

theorem mem_of_pow_three {G : Type*} [Group G] [Finite G] {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hj : ∃ j : ℕ, Nat.card ↥H = 2 ^ j * Nat.card ↥L)
    {a : G} (haH : a ∈ H) (ha3 : a ^ 3 = 1) : a ∈ L := by
  obtain ⟨j, hj⟩ := hj
  have hNn : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf H)
  have h2 : Nat.card ↥(L.subgroupOf H) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hQ : Nat.card (↥H ⧸ L.subgroupOf H) = 2 ^ j := by
    rw [h2, hj] at h1
    exact (Nat.eq_of_mul_eq_mul_right hLpos h1).symm
  set x : ↥H ⧸ L.subgroupOf H := QuotientGroup.mk ⟨a, haH⟩ with hx
  have h3 : x ^ 3 = 1 := by
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨a, haH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this]
    rfl
  have h4 : x ^ (2 ^ j) = 1 := by
    rw [← hQ]
    exact pow_card_eq_one'
  have h5 : x ^ Nat.gcd 3 (2 ^ j) = 1 := pow_gcd_eq_one.mpr ⟨h3, h4⟩
  have hg : Nat.gcd 3 (2 ^ j) = 1 := Nat.Coprime.pow_right j (by norm_num)
  rw [hg, pow_one] at h5
  have h6 := (QuotientGroup.eq_one_iff (⟨a, haH⟩ : ↥H)).mp h5
  exact Subgroup.mem_subgroupOf.mp h6

theorem card_eq_of_faithful {V : Type*} [CommGroup V] {D : FFModel} (hD : D.Faithful)
    {L : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π) :
    Nat.card ↥L = Nat.card D.Gam :=
  (Nat.card_congr (Equiv.ofBijective π ⟨FFC.injective_of_faithful_sec hD h, h.1⟩)).symm

theorem not_naturalList2_of_card_1080
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hL : Nat.card ↥L = 1080) : ¬ B51NaturalList2 L U Z := by
  have hS : InS (Nat.card ↥L) := Or.inr (Or.inl hL)
  rintro (⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨F, _, _, hF, π, hπ⟩ | ⟨F, _, _, hF, π, hπ⟩)
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hF] at hc
    exact sl2_num hS hc.symm
  · have hc := card_eq_of_nat_realizes1527d hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX : Nat.card ↥(StatedSp 2 F) =
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
      rw [hI, Finset.prod_pair (by norm_num)]
    rw [hX] at hc
    exact sp4_num hS hc.symm
  · have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
      have := FFC.charP_two_of_card_pow hF
      exact (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hF, hF] at hcard
    exact g2_num hS hcard.symm
  · have h1 : Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 6)) :=
      Nat.card_le_card_of_surjective π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  · have h1 : Nat.card ↥L ∣ Nat.card ↥(alternatingGroup (Fin 8)) :=
      Subgroup.card_dvd_of_surjective hπ.1
    rw [card_alternatingGroup1527d 8 (by norm_num), hL] at h1
    norm_num [Nat.factorial] at h1
  · have hF2 : Nat.card F = 2 := by simpa using hF
    have h1 : Nat.card ↥L ∣ Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
      Subgroup.card_dvd_of_surjective hπ.1
    rw [card_commutator_quasithinG2 hF2, hL] at h1
    norm_num at h1
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hF] at hc
    exact sl3_num hS hc.symm

theorem padicValNat_two_pow_mul {m c : ℕ} (hc : ¬ 2 ∣ c) (hc0 : c ≠ 0) :
    padicValNat 2 (2 ^ m * c) = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) hc0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hc,
    add_zero]

theorem pv_360 : padicValNat 2 360 = 3 :=
  padicValNat_two_pow_mul (m := 3) (c := 45) (by norm_num) (by norm_num)

theorem pv_2520 : padicValNat 2 2520 = 3 :=
  padicValNat_two_pow_mul (m := 3) (c := 315) (by norm_num) (by norm_num)

theorem pv_6048 : padicValNat 2 6048 = 5 :=
  padicValNat_two_pow_mul (m := 5) (c := 189) (by norm_num) (by norm_num)

theorem exists_ne_one_of_card {G : Type*} [Group G] {S : Subgroup G} (h : 1 < Nat.card ↥S) :
    ∃ x : ↥S, x ≠ 1 := by
  have : Finite ↥S := Nat.finite_of_card_ne_zero (by omega)
  have := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

end Helpers

section Main

variable {V₀ : Type} [CommGroup V₀] [Finite V₀]

theorem b51RemMod
    (h56 : AsB56) (hG2 : G2FixBound) (hV : ∀ v : V₀, v ^ 2 = 1)
    (Γ H : Subgroup (MulAut V₀)) (hHΓ : H ≤ Γ) (k : ℕ)
    (hΓH : Nat.card ↥Γ = 2 ^ k * Nat.card ↥H) (hH1 : H ≠ ⊥) (hB : B53Hyp H) (hcomm : commV H = ⊤)
    (hI : IsInspList ↥H) (hS3 : ¬ Nonempty (↥H ≃* Equiv.Perm (Fin 3)))
    (hL3 : ¬ Nonempty (↥H ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2))))
    (W : Subgroup V₀) (hW : Nat.card ↥W = 16) (a : MulAut V₀) (ha : a ∈ H) (ha3 : a ^ 3 = 1)
    (haW : ∀ w ∈ W, a w ∈ W) (haC : ∀ w ∈ W, a w = w → w = 1)
    (R : Subgroup (MulAut V₀)) (hRΓ : R ≤ Γ) (hRW : ∀ r ∈ R, ∀ w ∈ W, r w = w)
    (hR : 2 ^ padicValNat 2 (Nat.card ↥Γ) ≤ 4 * Nat.card ↥R) :
    F6.IsHatAlt 6 ↥H ∧ Nat.card V₀ = 2 ^ 6 := by
  classical
  have h1 : B56Case1 H := by
    rcases h56 V₀ hV H hH1 hB with h1 | h2 | h3 | h4 | h5
    · exact h1
    · exact (hS3 h2.1).elim
    · exact (LRed4.not_case3 hI h3).elim
    · exact (LRed4.not_case4 hI h4).elim
    · exact (LRed4.not_case5 hI h5).elim
  obtain ⟨hqL, ⟨⟨-, hcases⟩, hP2, -, -, -, -⟩, hQL⟩ := h1
  have hi : B51Case1i H (CFSG.Open.quasithinGenFitting H) := by
    rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
    · exact hi
    · exact (hL3 (LRed4.case1ii_conclusion hI hii)).elim
    · exact (LRed4.case1iii_false hI hiii).elim
    · exact (LRed4.case1iv_false hI hiv).elim
  obtain ⟨hirr, hB42, hsyl⟩ := hi
  set L : Subgroup (MulAut V₀) := CFSG.Open.quasithinGenFitting H with hLdef
  have hLH : L ≤ H := quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V₀)) := le_normalizer_quasithinGenFitting H
  have hNn : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf H
  have hidx : (∃ j : ℕ, Nat.card ↥H = 2 ^ j * Nat.card ↥L) ∧ commV L = ⊤ := by
    rcases hsyl T hT with hHL | ⟨hHT, -⟩
    · refine ⟨⟨0, ?_⟩, ?_⟩
      · rw [pow_zero, one_mul, hHL]
      · rw [← hHL]
        exact hcomm
    · have hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V₀)) := hT.1.trans hHN
      refine ⟨pow_index_of_sup_two hLH hT.2.1 hTL hHT, ?_⟩
      have hc' : commV (L ⊔ T) = ⊤ := by
        rw [← hHT]
        exact hcomm
      exact LRed4.commV_eq_top_of_sup_two hV hT.2.1 hTL hc'
  obtain ⟨hj, hLtop⟩ := hidx
  have hInS : InS (Nat.card ↥L) := inS_of_inspList hI hL3 hLH hNn hqL hj
  have haL : a ∈ L := mem_of_pow_three hLH hHN hj ha ha3
  have hWZ : W ⊓ (fixV L ⊓ ⊤) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwW, hwZ⟩
    exact Subgroup.mem_bot.mpr (haC w hwW (hwZ.1 a haL))
  rw [hLtop] at hB42
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, L.relIndex Γ = 2 ^ m := by
    obtain ⟨j, hj'⟩ := hj
    refine ⟨k + j, ?_⟩
    have h1 : L.relIndex Γ * Nat.card ↥L = Nat.card ↥Γ := by
      have := Subgroup.relIndex_mul_card (H := L) (K := Γ)
      rwa [inf_eq_left.mpr (hLH.trans hHΓ)] at this
    have h2 : L.relIndex Γ * Nat.card ↥L = 2 ^ (k + j) * Nat.card ↥L := by
      rw [h1, hΓH, hj', pow_add, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right hLpos h2
  have hcnt := card_inf_ge (hLH.trans hHΓ) hRΓ hm hR
  have hRfix : ∀ x ∈ R ⊓ L, ∀ w ∈ W, x w = w := fun x hx w hw => hRW x hx.1 w hw
  rcases modelShape_of_card hInS hB42 with hA6 | hA7 | hA7F | hHat | hG2'
  ·
    exfalso
    obtain ⟨π, hπ⟩ := hA6
    have hc : Nat.card ↥L = 360 := by
      rw [card_eq_of_faithful (FFC.altDn_faithful (by norm_num)) hπ]
      show Nat.card ↥(alternatingGroup (Fin 6)) = 360
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial]
    rw [hc, pv_360] at hcnt
    obtain ⟨x, hx1⟩ := exists_ne_one_of_card (S := R ⊓ L) (by omega)
    exact hx1 (Subtype.ext (alt6_fix ⟨π, hπ⟩ le_top hWZ hW x.2.2 (hRfix x x.2)))
  ·
    exfalso
    obtain ⟨π, hπ⟩ := hA7
    have hc : Nat.card ↥L = 2520 := by
      rw [card_eq_of_faithful (FFC.altDn_faithful (by norm_num)) hπ]
      show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    rw [hc, pv_2520] at hcnt
    obtain ⟨x, hx1⟩ := exists_ne_one_of_card (S := R ⊓ L) (by omega)
    exact hx1 (Subtype.ext (alt7_fix ⟨π, hπ⟩ le_top hWZ hW haL ha3 haW haC x.2.2
      (hRfix x x.2)))
  ·
    exfalso
    obtain ⟨α, π, hπ⟩ := hA7F
    have hc : Nat.card ↥L = 2520 := by
      rw [card_eq_of_faithful (FFC.a7Four_faithful α) hπ]
      show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    rw [hc, pv_2520] at hcnt
    obtain ⟨x, hx1⟩ := exists_ne_one_of_card (S := R ⊓ L) (by omega)
    exact hx1 (Subtype.ext (a7Four_fix ⟨α, π, hπ⟩ le_top hWZ hW x.2.2 (hRfix x x.2)))
  ·
    obtain ⟨K, hK, hKf, Γ₀, hK4, hdet, hhat, hsc, π, hπ⟩ := hHat
    have hc : Nat.card ↥L = 1080 := by
      have h1 := card_eq_of_faithful (FFModel.nat_faithful _) hπ
      rw [h1]
      have : Finite ↥Γ₀ := inferInstance
      show Nat.card ↥Γ₀ = 1080
      exact card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
    have hdirect : IsIntDirect (commV L) (fixV L) ⊤ := by
      by_contra hnd
      have h2 := (hP2.2 hnd).2
      rw [hLtop] at h2
      exact not_naturalList2_of_card_1080 hc h2
    have hZbot : fixV L ⊓ ⊤ = ⊥ := by
      have h3 := hdirect.2
      rw [hLtop, top_inf_eq] at h3
      rw [inf_top_eq]
      exact h3
    have hTrip : TripleA6Six L ⊤ ⊥ := by
      rw [← hZbot]
      exact ⟨K, hK, hKf, Γ₀, hK4, hdet, hhat, hsc, π, hπ⟩
    obtain ⟨hatL, hcardV⟩ := hat_conclusion hTrip
    refine ⟨?_, hcardV⟩
    have hHL : H = L := by
      obtain ⟨j, hj'⟩ := hj
      have hmem := (LRed4.inspList_facts hI).1
      rw [hj', hc] at hmem
      simp only [LRed4.inspOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
      have hj0 : j = 0 := by
        rcases Nat.lt_or_ge j 4 with hj4 | hj4
        · interval_cases j <;> omega
        · have : 16 ≤ 2 ^ j := by
            calc 16 = 2 ^ 4 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4
          omega
      subst hj0
      refine (Subgroup.eq_of_le_of_card_ge hLH ?_).symm
      rw [hj', hc]
      omega
    exact Insp9.isHatAlt_of_mulEquiv (MulEquiv.subgroupCongr hHL.symm) hatL
  ·
    exfalso
    have hG2'' := hG2'
    obtain ⟨F, _, _, hF, π, hπ⟩ := hG2'
    have hF2 : Nat.card F = 2 := by simpa using hF
    have hcp : CharP F 2 := FFC.charP_two_of_card_pow hF
    have hle : ⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ≤ CFSG.Open.quasithinG2 F :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact (CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem
          ((CFSG.Open.quasithinG2 F).mul_mem ha hb) ((CFSG.Open.quasithinG2 F).inv_mem ha))
          ((CFSG.Open.quasithinG2 F).inv_mem hb)
    have hc : Nat.card ↥L = 6048 := by
      have h1 := card_eq_of_faithful (FFC.zornQ_faithful _ hle) hπ
      rw [h1]
      exact card_commutator_quasithinG2 hF2
    rw [hc, pv_6048] at hcnt
    have hbound := g2_card_le hG2 hG2'' (le_top : W ≤ ⊤) hWZ hW
    have hinj : Nat.card ↥(R ⊓ L) ≤ Nat.card {x : ↥L // ∀ w ∈ W, ((x : ↥L) : MulAut V₀) w = w} := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨⟨x.1, x.2.2⟩, fun w hw => hRfix x.1 x.2 w hw⟩ :
          {x : ↥L // ∀ w ∈ W, ((x : ↥L) : MulAut V₀) w = w})) ?_
      intro x y hxy
      have hxy' := congrArg (fun z : {x : ↥L // ∀ w ∈ W, ((x : ↥L) : MulAut V₀) w = w} => (z.1 : MulAut V₀)) hxy
      exact Subtype.ext hxy'
    omega

end Main

end LRed6

end CFSG.Quasithin
