module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofLStar
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofCases
public import CFSG.RankThree.PartTwo.Sec21.Item2113Proof
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2113ChoiceHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (lBar L ≃* NativeSporadic.J2) →
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) → Nat.card (A ⊓ L : Subgroup G) = 9

@[expose] def KF2113ExcCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    (∃ n : ℕ, 0 < n ∧ Even n ∧ (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
        ChevalleyExceptionalModel (lBar L) .trialityD4 2 n)) →
    ∀ R : Subgroup G, R ≤ L → IsPGroup 3 R → (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) →
      ∀ d ∈ R, d ≠ 1 → d ^ 3 = 1 → (∀ r ∈ R, r * d = d * r) → IsCentral218 L d

namespace Item2113Res2Proof

open Subgroup
open Item2113Proof (commGroupOf map_subtype_zpowers)

variable {G : Type} [Group G]

theorem exists_R [Finite G] {A L : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {u : G} (huA : u ∈ normalizer (A : Set G))
    (huL : u ∈ L) (hu3 : ∃ k : ℕ, u ^ (3 ^ k) = 1) (huA' : u ∉ A) {d : G} (hdA : d ∈ A)
    (hdL : d ∈ L) (hud : u * d * u⁻¹ = d) {b : G} (hbA : b ∈ A) (hbL : b ∈ L)
    (hub : u * b * u⁻¹ ≠ b) :
    ∃ R : Subgroup G, R ≤ L ∧ IsPGroup 3 R ∧ (∃ j : ℕ, 3 ≤ j ∧ Nat.card R = 3 ^ j) ∧ d ∈ R ∧
      (∀ r ∈ R, r * d = d * r) ∧ (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := (A ⊓ L) ⊔ zpowers u with hR
  have hAL3 : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hzu3 : IsPGroup 3 (zpowers u) := by
    obtain ⟨k, hk⟩ := hu3
    have hdvd : Nat.card (zpowers u) ∣ 3 ^ k := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hj
  have hnorm : zpowers u ≤ normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hA, hL⟩
      exact ⟨(mem_normalizer_iff.mp huA h).mp hA,
        L.mul_mem (L.mul_mem huL hL) (L.inv_mem huL)⟩
    · rintro ⟨hA, hL⟩
      refine ⟨(mem_normalizer_iff.mp huA h).mpr hA, ?_⟩
      have h' := L.mul_mem (L.mul_mem (L.inv_mem huL) hL) huL
      simpa [mul_assoc] using h'
  have hRp : IsPGroup 3 R := IsPGroup.to_sup_of_normal_left' hAL3 hzu3 hnorm
  have huR : u ∈ R := (le_sup_right : zpowers u ≤ R) (mem_zpowers u)
  have hALR : A ⊓ L ≤ R := le_sup_left
  have hdR : d ∈ R := hALR ⟨hdA, hdL⟩
  have hbR : b ∈ R := hALR ⟨hbA, hbL⟩
  refine ⟨R, sup_le inf_le_right (zpowers_le.mpr huL), hRp, ?_, hdR, ?_, ⟨u, huR, b, hbR, ?_⟩⟩
  · obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hRp
    refine ⟨j, ?_, hj⟩
    have hdvd : 3 ^ 2 ∣ 3 ^ j := by
      rw [← hj, show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact card_dvd_of_le hALR
    have h2 : 2 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hne : j ≠ 2 := by
      rintro rfl
      have heq : A ⊓ L = R := eq_of_le_of_card_ge hALR (by rw [hj, h9]; norm_num)
      exact huA' (heq ▸ huR).1
    omega
  · intro r hr
    have hle : R ≤ centralizer ({d} : Set G) := by
      refine sup_le ?_ ?_
      · rintro x ⟨hxA, -⟩
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hxA⟩ ⟨d, hdA⟩)
      · rw [zpowers_le, mem_centralizer_singleton_iff]
        calc u * d = u * d * u⁻¹ * u := by group
          _ = d * u := by rw [hud]
    exact mem_centralizer_singleton_iff.mp (hle hr)
  · intro h
    apply hub
    rw [h, mul_inv_cancel_right]

theorem mem_inf_subgroupOf {A L : Subgroup G} {x : A} :
    x ∈ (A ⊓ L).subgroupOf A ↔ (x : G) ∈ L :=
  ⟨fun h => (mem_subgroupOf.mp h).2, fun h => mem_subgroupOf.mpr ⟨x.2, h⟩⟩

theorem card_inf_subgroupOf (A L : Subgroup G) :
    Nat.card ((A ⊓ L).subgroupOf A) = Nat.card (A ⊓ L : Subgroup G) :=
  Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv

section Choice


theorem pair_data [Finite G] (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) :
    c ∈ A ∧ c ≠ 1 ∧ L ≤ centralizer ({c} : Set G) ∧ A ≤ normalizer (L : Set G) ∧ c ∉ L := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  exact ⟨hcA, hc1, Sec6.le_centralizer_of_mem_thetaComponentsAt hLc,
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp
      hpair.mem_S.1.1 hcA hc1 L hLc, Item2113Proof.not_mem_of_isList218 hpair hL⟩

theorem exists_transvection_R [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    {σ₀ : MulAut A} (hσ₀ : σ₀ ∈ starOf A L) (hσ₀3 : σ₀ ^ 3 = 1) (hσ₀1 : σ₀ ≠ 1)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    ∃ σ ∈ starOf A L, IsTransvectionOn σ ∧ ∃ d ∈ A, d ≠ 1 ∧
      (commOf σ).map A.subtype = zpowers d ∧
      ∃ R : Subgroup G, R ≤ L ∧ IsPGroup 3 R ∧ (∃ j : ℕ, 3 ≤ j ∧ Nat.card R = 3 ^ j) ∧ d ∈ R ∧
        (∀ r ∈ R, r * d = d * r) ∧ (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) := by
  obtain ⟨hcA, hc1, hLc, hAL, hcL⟩ := pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  let _ : CommGroup A := commGroupOf hAe
  have h3 : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hAe.2 x x.2)
  set B : Subgroup A := (A ⊓ L).subgroupOf A with hB
  have hcB : (⟨c, hcA⟩ : A) ∉ B := fun h => hcL (mem_inf_subgroupOf.mp h)
  have hc1' : (⟨c, hcA⟩ : A) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨u, huL, hu3, hσL, hσ3, hσ1⟩ := exists_three_element hσ₀ hσ₀3 hσ₀1
  set σ := A.normalizerMonoidHom u with hσ
  have hσc : σ ⟨c, hcA⟩ = ⟨c, hcA⟩ := apply_eq_of_mem_starOf hcA hLc hσL
  have hσB : ∀ x, x⁻¹ * σ x ∈ B := fun x => mem_inf_subgroupOf.mpr
    (coe_inv_mul_apply_mem hAL hσL x)
  obtain ⟨dA, hd1, hdB, hσd, hcomm⟩ :=
    exists_transvection_of_cube h3 h27 hc1' hcB hσc hσB hσ3 hσ1
  have hB9 : Nat.card B = 9 := by rw [hB, card_inf_subgroupOf, h9]
  obtain ⟨b, hbB, hσb⟩ : ∃ b ∈ B, σ b ≠ b := by
    by_contra hcon
    have hfix : ∀ b ∈ B, σ b = b := fun b hb => not_not.mp fun h => hcon ⟨b, hb, h⟩
    apply hσ1
    apply eq_one_of_forall_fix
    intro x
    have htop := Item2113Proof.sup_zpowers_eq_top h27 hB9 hcB
    have hle : B ⊔ zpowers (⟨c, hcA⟩ : A) ≤ Item2113Proof.fixSub σ := by
      refine sup_le (fun y hy => hfix y hy) ?_
      rw [zpowers_le]
      exact hσc
    exact hle (htop ▸ mem_top x)
  have huA' : (u : G) ∉ A := by
    intro huA
    apply hσ1
    apply eq_one_of_forall_fix
    intro x
    apply Subtype.ext
    rw [hσ, normalizerMonoidHom_apply_apply_coe]
    have hcomm' : (u : G) * x = x * u :=
      congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, huA⟩ x)
    rw [hcomm', mul_inv_cancel_right]
  have hud : (u : G) * dA * (u : G)⁻¹ = dA := by
    have h := congrArg Subtype.val hσd
    rwa [hσ, normalizerMonoidHom_apply_apply_coe] at h
  have hub : (u : G) * b * (u : G)⁻¹ ≠ b := by
    intro h
    apply hσb
    apply Subtype.ext
    rw [hσ, normalizerMonoidHom_apply_apply_coe]
    exact h
  obtain ⟨R, hRL, hR3, hRj, hdR, hdc, hnab⟩ := exists_R hAe h9 u.2 huL hu3 huA' dA.2
    (mem_inf_subgroupOf.mp hdB) hud b.2 (mem_inf_subgroupOf.mp hbB) hub
  refine ⟨σ, hσL, isTransvectionOn_of_eq_zpowers h3 hd1 hσd hcomm, dA, dA.2,
    fun h => hd1 (Subtype.ext h), ?_, R, hRL, hR3, hRj, hdR, hdc, hnab⟩
  rw [hcomm, map_subtype_zpowers]

theorem card_nine_and_inv_of_central [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    {σ₀ : MulAut A} (hσ₀ : σ₀ ∈ starOf A L) (hσ₀3 : σ₀ ^ 3 = 1) (hσ₀1 : σ₀ ≠ 1)
    {ζ : MulAut A} (hζ : ζ ∈ starOf A L) (hζ2 : ζ ^ 2 = 1) (hζ1 : ζ ≠ 1)
    (hζc : ∀ τ ∈ starOf A L, ζ * τ = τ * ζ) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ ∀ x : A, (x : G) ∈ L → ζ x = x⁻¹ := by
  obtain ⟨hcA, hc1, hLc, hAL, hcL⟩ := pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  let _ : CommGroup A := commGroupOf hAe
  have h3 : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hAe.2 x x.2)
  set B : Subgroup A := (A ⊓ L).subgroupOf A with hB
  have hcB : (⟨c, hcA⟩ : A) ∉ B := fun h => hcL (mem_inf_subgroupOf.mp h)
  have hc1' : (⟨c, hcA⟩ : A) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hσc : σ₀ ⟨c, hcA⟩ = ⟨c, hcA⟩ := apply_eq_of_mem_starOf hcA hLc hσ₀
  have hσB : ∀ x, x⁻¹ * σ₀ x ∈ B := fun x => mem_inf_subgroupOf.mpr
    (coe_inv_mul_apply_mem hAL hσ₀ x)
  obtain ⟨dA, hd1, hdB, hσd, hcomm⟩ :=
    exists_transvection_of_cube h3 h27 hc1' hcB hσc hσB hσ₀3 hσ₀1
  have hζcc : ζ ⟨c, hcA⟩ = ⟨c, hcA⟩ := apply_eq_of_mem_starOf hcA hLc hζ
  have hζB : ∀ x, x⁻¹ * ζ x ∈ B := fun x => mem_inf_subgroupOf.mpr
    (coe_inv_mul_apply_mem hAL hζ x)
  obtain ⟨hB9, hinv⟩ := card_eq_nine_and_inv_of_comm h3 h27 hc1' hcB hσc hσ₀1 hd1 hdB hσd
    hcomm hζcc hζB hζ2 hζ1 (hζc σ₀ hσ₀)
  refine ⟨by rw [← card_inf_subgroupOf, ← hB, hB9], fun x hx => hinv x ?_⟩
  exact mem_inf_subgroupOf.mpr hx

theorem item2113Choice_of (h211 : Item211) (h45 : Sec4.Item4_5) (hHJ : Item2113ChoiceHJ)
    (hKF : KF2113ExcCentral) : Item2113Choice := by
  intro G _ _ A E U c L hpair hL
  have hAe := hpair.mem_S.1.1
  have fin : ∀ {σ₀ : MulAut A}, σ₀ ∈ starOf A L → σ₀ ^ 3 = 1 → σ₀ ≠ 1 →
      Nat.card (A ⊓ L : Subgroup G) = 9 →
      (¬ 81 ∣ Nat.card L ∨ ∃ n : ℕ, 0 < n ∧ Even n ∧
        (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
          ChevalleyExceptionalModel (lBar L) .trialityD4 2 n)) →
      ∃ d ∈ A, d ≠ 1 ∧ IsCentral218 L d ∧ ∃ t ∈ starOf A L, IsTransvectionOn t ∧
        (commOf t).map A.subtype = zpowers d := by
    intro σ₀ hσ₀ hσ₀3 hσ₀1 h9 hcase
    obtain ⟨σ, hσL, hσt, d, hdA, hd1, hdσ, R, hRL, hR3, ⟨j, hj3, hRj⟩, hdR, hdc, hnab⟩ :=
      exists_transvection_R h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 h9
    refine ⟨d, hdA, hd1, ?_, σ, hσL, hσt, hdσ⟩
    rcases hcase with h81 | hexc
    · have hR27 : Nat.card R = 27 := by
        have hdvd : Nat.card R ∣ Nat.card L := Subgroup.card_dvd_of_le hRL
        have hj : j = 3 := by
          by_contra hj
          apply h81
          have h81R : 81 ∣ Nat.card R := by
            rw [hRj, show (81 : ℕ) = 3 ^ 4 by norm_num]
            exact Nat.pow_dvd_pow 3 (by omega)
          exact h81R.trans hdvd
        rw [hRj, hj]; norm_num
      refine ⟨R, isSylowOf_of_card hRL hR27 h81, ?_⟩
      exact mem_map.mpr ⟨⟨d, hdR⟩, mem_center_iff.mpr fun g =>
        Subtype.ext (hdc g g.2), rfl⟩
    · exact hKF G L hexc R hRL hR3 hnab d hdR hd1 (hAe.2 d hdA) hdc
  rcases starOf_cases_of_isList218 h211 hpair hL with ⟨hspor, hS⟩ | ⟨hexc, hS⟩ | ⟨hJ, hS⟩
  · have h81 : ¬ 81 ∣ Nat.card L := by
      refine not_dvd_card_of_sporadic ?_
      rcases hspor with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    rcases hS with hS | hS
    · obtain ⟨e⟩ := hS
      obtain ⟨h3, h1, -⟩ := dihedral_six_data
      obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
      obtain ⟨-, -, hz2, hz1, -⟩ := dihedral_six_data
      obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 dihedral_six_central
      obtain ⟨h9, -⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
        hζc
      exact fin hσ₀ hσ₀3 hσ₀1 h9 (Or.inl h81)
    · obtain ⟨e⟩ := hS
      obtain ⟨h3, h1, hz2, hz1, -⟩ := gl_two_three_data
      obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
      obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 gl_two_three_central
      obtain ⟨h9, -⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
        hζc
      exact fin hσ₀ hσ₀3 hσ₀1 h9 (Or.inl h81)
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1, hz2, hz1, -⟩ := dihedral_six_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 dihedral_six_central
    obtain ⟨h9, -⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
      hζc
    exact fin hσ₀ hσ₀3 hσ₀1 h9 (Or.inr hexc)
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1⟩ := perm_three_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    have h9 := hHJ G A E U c L hpair hJ ⟨e⟩
    exact fin hσ₀ hσ₀3 hσ₀1 h9 (Or.inl (not_dvd_card_of_sporadic (Or.inr (Or.inr (Or.inl hJ)))))

theorem exists_inv_of_isList218 [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    (hS : Nonempty (starOf A L ≃* DihedralGroup 6) ∨
      Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3))) :
    ∃ ℓ ∈ L, ∀ x ∈ A ⊓ L, ℓ * x * ℓ⁻¹ = x⁻¹ := by
  have key : ∀ {ζ : MulAut A}, ζ ∈ starOf A L → (∀ x : A, (x : G) ∈ L → ζ x = x⁻¹) →
      ∃ ℓ ∈ L, ∀ x ∈ A ⊓ L, ℓ * x * ℓ⁻¹ = x⁻¹ := by
    rintro _ ⟨w, hwL, rfl⟩ hinv
    refine ⟨w, mem_subgroupOf.mp hwL, fun x ⟨hxA, hxL⟩ => ?_⟩
    have h := congrArg Subtype.val (hinv ⟨x, hxA⟩ hxL)
    rwa [normalizerMonoidHom_apply_apply_coe] at h
  rcases hS with hS | hS
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1, hz2, hz1, -⟩ := dihedral_six_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 dihedral_six_central
    obtain ⟨-, hinv⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
      hζc
    exact key hζ hinv
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1, hz2, hz1, -⟩ := gl_two_three_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 gl_two_three_central
    obtain ⟨-, hinv⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
      hζc
    exact key hζ hinv

end Choice

end Item2113Res2Proof

end CFSG.RankThree.PartTwo.Sec21
