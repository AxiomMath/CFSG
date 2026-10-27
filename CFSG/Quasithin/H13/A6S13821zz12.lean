module

public import CFSG.Quasithin.H13.A6S13821zz9

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank

theorem natural_sl3_of_pair {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} (hp : B42ModulePair L U Z) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    ∃ m, 2 ≤ m ∧ BinaryNaturalSL L U Z 3 m := by
  classical
  set q := 2 ^ n with hqdef
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  set z := Nat.card (Subgroup.center ↥L) with hz
  set r := (q ^ 2 - 1) * (q ^ 3 - 1) with hr
  have hz1 : 1 ≤ z := hodd.pos
  have hrodd : Odd r := by
    have e2 : q ^ 2 = 2 ^ (2 * n) := by rw [hqdef, ← pow_mul, mul_comm]
    have e3 : q ^ 3 = 2 ^ (3 * n) := by rw [hqdef, ← pow_mul, mul_comm]
    rw [hr, e2, e3]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  have hLc : Nat.card ↥L = q ^ 3 * r * z := by
    rw [← hcard, hz]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hq3 : q ^ 3 = 2 ^ (n * 3) := by rw [hqdef, ← pow_mul]
  have hL2 : Nat.card ↥L = 2 ^ (n * 3) * (r * z) := by rw [hLc, hq3, mul_assoc]
  have hrz : Odd (r * z) := hrodd.mul hodd
  have hlow : 16482816 ≤ Nat.card ↥L := by
    have h1 := le_card_sl3_of_three_le hn
    rw [hLc]
    calc 16482816 ≤ q ^ 3 * r := by rw [hr, mul_assoc] at *; exact h1
      _ ≤ q ^ 3 * r * z := Nat.le_mul_of_pos_right _ hz1
  have small : ∀ {M : ℕ}, Nat.card ↥L ≤ M → M < 16482816 → False := fun h1 h2 => by omega
  have one_le : ∀ {K : Type} [Field K] [Finite K] {m : ℕ}, Nat.card K = 2 ^ m → 1 ≤ m := by
    intro K _ _ m hK
    by_contra h
    have h0 : m = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  rcases hp with ⟨m, F, _, _, hFc, π, hR⟩ | ⟨m, hnat⟩ | ⟨m, F, _, _, hFc, π, hR⟩ |
      ⟨m, F, _, _, hFc, π, hR⟩ | ⟨F, _, _, hFc, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩ |
      ⟨α, π, hR⟩ | ⟨F, _, _, Γ₀, hF4, -, -, -, π, hR⟩ | ⟨F, _, _, hFc, π, hR⟩ |
      ⟨F, _, _, hFc, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩
  ·
    exfalso
    have e : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hR, hR.1⟩
    have h1m := one_le hFc
    have h1 : Nat.card ↥L = 2 ^ m * (4 ^ m - 1) := by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_two_pow hFc]
    have hodd' : Odd (4 ^ m - 1) := by
      rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hL2)
    have h4 : q ^ 6 = 4 ^ m := by
      rw [hm3, hqdef, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    refine false_of_sl2_sl3_eq hq4 (z := z) ?_
    rw [h4, hodd2, hr]
  ·
    obtain ⟨F, _, _, hFc, π, hR⟩ := hnat
    have e : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hR, hR.1⟩
    have h1m := one_le hFc
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · exfalso
      have hm1 : m = 1 := by omega
      subst hm1
      refine small (M := 168) (le_of_eq ?_) (by norm_num)
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_three_pow hFc]
      norm_num
    · exact ⟨m, h2, F, inferInstance, inferInstance, hFc, π, hR⟩
  ·
    exfalso
    have e : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hR, hR.1⟩
    have h1m := one_le hFc
    have h1 : Nat.card ↥L = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow hFc]
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      exact small (M := 720) (le_of_eq (by rw [h1]; norm_num)) (by norm_num)
    · have hodd' : Odd ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) :=
        (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
      obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hL2)
      set s := 2 ^ m with hs
      have e2 : (2 : ℕ) ^ (2 * m) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
      have e4 : (2 : ℕ) ^ (4 * m) = s ^ 4 := by rw [hs, ← pow_mul, mul_comm]
      have hqs : s ^ 4 = q ^ 3 := by rw [hq3, ← e4, hm3]
      rw [e2, e4] at hodd2
      exact false_of_sp4_sl3_eq hq4 hz1 hqs hodd2
  ·
    exfalso
    have := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFc
    have e : ↥(quasithinG2 F) ≃* ↥L := MulEquiv.ofBijective π
      ⟨G64.RealizesVia.injective_of_faithful' (FFC.zornQ_faithful _ le_rfl) hR, hR.1⟩
    have h1m := one_le hFc
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      refine small (M := 12096) (le_of_eq ?_) (by norm_num)
      rw [← Nat.card_congr e.toEquiv, U3.card_quasithinG2_two (by rw [hFc]; norm_num)]
    · set s := 2 ^ m with hs
      have h1 : Nat.card ↥L = 2 ^ (6 * m) * ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
        rw [← Nat.card_congr e.toEquiv, card_quasithinG2_1527d hFc, hFc, hs, ← pow_mul,
          mul_comm m 6]
      have e6 : (2 : ℕ) ^ (6 * m) = s ^ 6 := by rw [hs, ← pow_mul, mul_comm]
      have e2 : (2 : ℕ) ^ (2 * m) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
      have hodd' : Odd ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
        rw [← e6, ← e2]
        exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
      obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hL2)
      have hqs : s ^ 6 = q ^ 3 := by rw [hq3, ← e6, hm3]
      exact false_of_g2_sl3_eq hq4 hz1 hqs hodd2
  ·
    exfalso
    refine small (M := 12096) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ :=
          Nat.card_le_card_of_surjective _ hR.1
      _ ≤ Nat.card ↥(quasithinG2 F) := Subgroup.card_le_of_le (Subgroup.commutator_le_self _)
      _ = 12096 := U3.card_quasithinG2_two (by rw [hFc]; norm_num)
  ·
    exfalso
    refine small (M := 60) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 5)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 60 := by rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  ·
    exfalso
    refine small (M := 360) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 6)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 360 := by rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  ·
    exfalso
    refine small (M := 2520) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 2520 := by rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  ·
    exfalso
    refine small (M := 2520) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 2520 := by rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  ·
    exfalso
    refine small (M := 262144) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective _ hR.1
      _ ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) := Subgroup.card_le_card_group _
      _ ≤ Nat.card (Matrix (Fin 3) (Fin 3) F) :=
          Nat.card_le_card_of_injective (fun g => (g : Matrix (Fin 3) (Fin 3) F))
            (fun a b h => Units.ext h)
      _ = 262144 := by
          show Nat.card (Fin 3 → Fin 3 → F) = 262144
          rw [Nat.card_fun, Nat.card_fun, hF4, Nat.card_fin]
          norm_num
  ·
    exfalso
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    refine small (M := 20160) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 20160 := by
        rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_four_of_two hF2]
  ·
    exfalso
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    refine small (M := 9999360) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 F) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 9999360 := by
        rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_five_of_two hF2]
  ·
    exfalso
    refine small (M := 20160) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 20160 := by
        rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_four_of_two (by simp)]
  ·
    exfalso
    refine small (M := 9999360) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 9999360 := by
        rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_five_of_two (by simp)]

open scoped commutatorElement in
theorem commutator_eq_of_faithful {Y : Type} [Group Y] {L A : Subgroup Y}
    (hq : CFSG.IsQuasisimple ↥L) (hAL : A ≤ Subgroup.normalizer (L : Set Y))
    (hfaith : ∀ a ∈ A, (∀ l ∈ L, a * l = l * a) → a = 1) (hA : A ≠ ⊥) : ⁅L, A⁆ = L := by
  classical
  have hLA : ⁅L, A⁆ ≤ L := Subgroup.commutator_le.mpr fun l hl a ha => by
    have h1 : a * l⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAL ha) _).mp (L.inv_mem hl)
    have e : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem hl h1
  by_contra hne
  have hconj : ∀ l ∈ L, ∀ m ∈ ⁅L, A⁆, l * m * l⁻¹ ∈ ⁅L, A⁆ := by
    intro l hl m hm
    rw [Subgroup.commutator_def] at hm ⊢
    induction hm using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
      have e : l * ⁅g₁, g₂⁆ * l⁻¹ = ⁅l * g₁, g₂⁆ * ⁅l, g₂⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, L.mul_mem hl hg₁, g₂, hg₂, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨l, hl, g₂, hg₂, rfl⟩))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  have hN : ((⁅L, A⁆).subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj _ g.2 _ hn⟩
  have hNt : (⁅L, A⁆).subgroupOf L ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hLA fun l hl => ?_
    have : (⟨l, hl⟩ : ↥L) ∈ (⁅L, A⁆).subgroupOf L := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp hq.1
  have hc := le_center_of_normal_ne_top hperf hq.2.1 hNt
  have hZ : ∀ z ∈ ⁅L, A⁆, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    have h1 := hc (Subgroup.mem_subgroupOf.mpr hz : (⟨z, hLA hz⟩ : ↥L) ∈ _)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨l, hl⟩
    exact (congrArg Subtype.val h2).symm
  apply hA
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine hfaith a ha (B5.commute_of_comm_central (B5.commutator_L_perfect' hq)
    (fun l hl => (Subgroup.mem_normalizer_iff.mp (hAL ha) l).mp hl) hZ fun l hl => ?_)
  have h1 : ⁅l, a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator hl ha
  have e : ⁅a, l⁆ = ⁅l, a⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.inv_mem _ h1

theorem fixProp_of_b51 {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {Xr Kr : Subgroup (MulAut V)} (hc : B51Conclusion Xr Kr) [Nontrivial ↥Kr] {X : Type}
    [Group X] [Finite X] (κ : X →* ↥Kr) (hκ : Function.Surjective κ) (N : Subgroup X)
    [N.Normal] (hperf : commutator (X ⧸ N) = ⊤)
    (hs : IsSimpleGroup ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N))) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N)) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (hoddZ : Odd (Nat.card (Subgroup.center (X ⧸ N)))) {T₀ : Subgroup X}
    (hsyl : IsSylowTwoOf T₀ ⊤) (hNT : N ≤ T₀) (hO : ∀ x ∈ N, κ x = 1) :
    S1565.FixProp (Kr.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X)) ⊥ ⊤ := by
  classical
  obtain ⟨⟨-, hcases⟩, -, -, -, -, -⟩ := hc
  have hker' : N ≤ κ.ker := fun x hx => hO x hx
  have hκqs : Function.Surjective (QuotientGroup.lift N κ hker') := fun y => by
    obtain ⟨x, rfl⟩ := hκ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  obtain ⟨hcardK, hdvd⟩ := card_quot_center_of_surjective hperf hs hκqs
  have hoddK : Odd (Nat.card (Subgroup.center ↥Kr)) := Odd.of_dvd_nat hoddZ hdvd
  have hcardK' := hcardK.trans hcard
  have hlow : 16482816 ≤ Nat.card ↥Kr := by
    have h1 := le_card_sl3_of_three_le hn
    have h2 : Nat.card ↥Kr = Nat.card (↥Kr ⧸ Subgroup.center ↥Kr) *
        Nat.card (Subgroup.center ↥Kr) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [h2, hcardK']
    exact h1.trans (Nat.le_mul_of_pos_right _ hoddK.pos)
  have hker : ∀ x ∈ κ.ker, x ∈ Subgroup.normalizer (T₀ : Set X) :=
    fun x hx => mem_normalizer_of_mem_ker N hperf hs hNT κ hκ hO hx
  have hBodd : Odd (Subgroup.normalizer (T₀ : Set X)).index := by
    have h1 : (Subgroup.normalizer (T₀ : Set X)).index ∣ T₀.index :=
      Subgroup.index_dvd_of_le Subgroup.le_normalizer
    have h2 : ¬ 2 ∣ T₀.index := by
      have h3 : ¬ 2 ∣ T₀.relIndex ⊤ := hsyl.2.2
      rwa [Subgroup.relIndex_top_right] at h3
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (h.trans h1))
  have hbot : S1565.InvSub (Kr.subtype.comp κ) (⊥ : Subgroup V) := fun x a ha => by
    have ha' : a = 1 := ha
    show (Kr.subtype.comp κ) x a ∈ (⊥ : Subgroup V)
    rw [ha', map_one]
    exact Subgroup.one_mem _
  have htop : S1565.FixProp (Kr.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X)) (commV Kr) ⊤ :=
    fun w _ _ x _ => Subgroup.subset_closure ⟨_, (κ x).2, w, rfl⟩
  rcases hcases with h1 | h2 | ⟨m, h3⟩ | h4
  ·
    obtain ⟨-, hpair, -⟩ := h1
    obtain ⟨m, hm, hnat⟩ := natural_sl3_of_pair hpair hn hcardK' hoddK
    obtain ⟨k, hkN, hkfix⟩ := exists_fpf_of_natural_sl3 hnat hm κ hκ hsyl hker
    have hZ : S1565.FixProp (Kr.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X)) ⊥
        (fixV Kr ⊓ commV Kr) := fun w hw _ x _ => by
      show (κ x : MulAut V) w * w⁻¹ ∈ (⊥ : Subgroup V)
      rw [hw.1 _ (κ x).2, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hZinv : S1565.InvSub (Kr.subtype.comp κ) (fixV Kr ⊓ commV Kr) := fun x a ha => by
      have h1 : (Kr.subtype.comp κ) x a = a := ha.1 _ (κ x).2
      rw [h1]
      exact ha
    have hUZ : S1565.FixProp (Kr.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X))
        (fixV Kr ⊓ commV Kr) (commV Kr) :=
      S1565.fixProp_of_chiefFactor hZinv (Or.inr fun u hu huB => hkfix u hu (huB k hkN))
    exact S1565.fixProp_compose _ hV2 _ hBodd hbot bot_le
      (S1565.fixProp_compose _ hV2 _ hBodd hbot bot_le hZ hUZ) htop
  ·
    obtain ⟨-, m, F, _, _, hFc, I, π, hind, hsup, hR, -, -⟩ := h2
    have hnat : ∀ i, BinaryNaturalSL Kr (I i) ⊥ 3 m := fun i =>
      ⟨F, inferInstance, inferInstance, hFc, π, hR i⟩
    have hm : 2 ≤ m := by
      have e : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* ↥Kr := MulEquiv.ofBijective π
        ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hR 0), (hR 0).1⟩
      by_contra hlt
      have h1 : 1 ≤ m := by
        by_contra h0
        have := Finite.one_lt_card (α := F)
        rw [hFc, show m = 0 by omega] at this
        norm_num at this
      have hm1 : m = 1 := by omega
      subst hm1
      have h168 : Nat.card ↥Kr = 168 := by
        rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
          Vol2.Ch10.SecA.card_SL_three_pow hFc]
        norm_num
      omega
    obtain ⟨k₀, hk₀N, hk₀⟩ := exists_fpf_of_natural_sl3 (hnat 0) hm κ hκ hsyl hker
    obtain ⟨k₁, hk₁N, hk₁⟩ := exists_fpf_of_natural_sl3 (hnat 1) hm κ hκ hsyl hker
    have hdisj : I 0 ⊓ I 1 = ⊥ :=
      disjoint_iff.mp (hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
    have hsup' : commV Kr ≤ I 0 ⊔ I 1 := by
      rw [← hsup]
      exact iSup_le fun i => by fin_cases i <;> simp
    have hinv : ∀ i, ∀ g : ↥Kr, ∀ v ∈ I i, (g : MulAut V) v ∈ I i := fun i => (hR i).2.2.2.1
    have hUfix : S1565.FixProp (Kr.subtype.comp κ) (Subgroup.normalizer (T₀ : Set X)) ⊥
        (commV Kr) := by
      intro u hu huB x _
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hsup' hu)
      have hfixab : ∀ y ∈ Subgroup.normalizer (T₀ : Set X),
          (κ y : MulAut V) a * a⁻¹ = 1 ∧ (κ y : MulAut V) b * b⁻¹ = 1 := by
        intro y hy
        have h1 : (κ y : MulAut V) (a * b) * (a * b)⁻¹ = 1 := huB y hy
        have e : (κ y : MulAut V) a * a⁻¹ = ((κ y : MulAut V) b * b⁻¹)⁻¹ := by
          rw [map_mul] at h1
          apply Additive.ofMul.injective
          have h2 := congrArg Additive.ofMul h1
          simp only [ofMul_mul, ofMul_inv, ofMul_one] at h2 ⊢
          rw [← sub_eq_zero]
          rw [← h2]
          abel
        have hmem : (κ y : MulAut V) a * a⁻¹ ∈ I 0 ⊓ I 1 := by
          refine ⟨(I 0).mul_mem (hinv 0 (κ y) a ha) ((I 0).inv_mem ha), ?_⟩
          rw [e]
          exact (I 1).inv_mem ((I 1).mul_mem (hinv 1 (κ y) b hb) ((I 1).inv_mem hb))
        rw [hdisj, Subgroup.mem_bot] at hmem
        refine ⟨hmem, ?_⟩
        rw [hmem] at e
        have := congrArg (·⁻¹) e
        simpa using this.symm
      have ha1 : a = 1 := Subgroup.mem_bot.mp
        (hk₀ a ha (by rw [(hfixab k₀ hk₀N).1]; exact Subgroup.one_mem _))
      have hb1 : b = 1 := Subgroup.mem_bot.mp
        (hk₁ b hb (by rw [(hfixab k₁ hk₁N).2]; exact Subgroup.one_mem _))
      show (κ x : MulAut V) (a * b) * (a * b)⁻¹ ∈ (⊥ : Subgroup V)
      rw [ha1, hb1, one_mul, map_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    exact S1565.fixProp_compose _ hV2 _ hBodd hbot bot_le hUfix htop
  ·
    exfalso
    obtain ⟨-, hm45, π, U₁, U₂, -, hR1, -⟩ := h3
    have h1 : Nat.card ↥Kr ≤ 9999360 := by
      calc Nat.card ↥Kr ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) :=
            Nat.card_le_card_of_surjective _ hR1.1
        _ ≤ 9999360 := by
          rw [Vol2.Ch10.SecA.card_statedSL]
          rcases hm45 with rfl | rfl
          · rw [Vol2.Ch10.SecA.card_SL_four_of_two (by simp)]; norm_num
          · rw [Vol2.Ch10.SecA.card_SL_five_of_two (by simp)]
    omega
  ·
    exfalso
    obtain ⟨-, m, hm45, k, hk1, -, I, π, -, -, -, hR⟩ := h4
    have h1 : Nat.card ↥Kr ≤ 9999360 := by
      calc Nat.card ↥Kr ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) :=
            Nat.card_le_card_of_surjective _ (hR ⟨0, by omega⟩).1
        _ ≤ 9999360 := by
          rw [Vol2.Ch10.SecA.card_statedSL]
          rcases hm45 with rfl | rfl
          · rw [Vol2.Ch10.SecA.card_SL_four_of_two (by simp)]; norm_num
          · rw [Vol2.Ch10.SecA.card_SL_five_of_two (by simp)]
    omega

end CFSG.Quasithin.H13.A6.A6S20
