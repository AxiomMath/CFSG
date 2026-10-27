module

public import CFSG.Quasithin.EmptyFaithful.S1469Six
public import CFSG.Quasithin.EmptyFaithful.Der6AGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.exists_mul_of_mem_M (S : Setting146 G T M) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) {m : G} (hm : m ∈ M) :
    ∃ l ∈ yOfL22 T M, ∃ g ∈ M ⊓ mcOf T, m = l * g := by
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hz
  have hw : m * z * m⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hm) z).mp hzV
  have hw1 : m * z * m⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  obtain ⟨l, hlL, hl⟩ := S.hyp1281.exists_conj_eq hzV hw hz1 hw1
  refine ⟨l, hlL, l⁻¹ * m, ⟨M.mul_mem (M.inv_mem (S.hyp1281.le hlL)) hm, ?_⟩, by group⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  by_cases hy1 : y = 1
  · simp [hy1]
  · have hyz : y = z := S.Z_eq_of_iff hy hz ⟨fun h => absurd h hy1, fun h => absurd h hz1⟩
    subst hyz
    calc y * (l⁻¹ * m) = l⁻¹ * (l * y * l⁻¹) * m := by group
      _ = l⁻¹ * (m * y * m⁻¹) * m := by rw [hl]
      _ = (l⁻¹ * m) * y := by group

theorem Setting146.le_normalizer_L_sup_Q1 (S : Setting146 G T M) :
    M ≤ Subgroup.normalizer ((yOfL22 T M ⊔ pCoreOf 2 (mcOf T) : Subgroup G) : Set G) := by
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  intro m hm
  obtain ⟨l, hlL, g, hg, rfl⟩ := S.exists_mul_of_mem_M hzZ hz1' hm
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.mem_sup_left hlL)) ?_
  refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, ?_⟩
  · exact S.hyp1281.normal hg.1
  · exact le_normalizer_pCoreOf 2 (mcOf T) hg.2

theorem Setting146.exists_mem_not_centralizer_V (S : Setting146 G T M) {u : G}
    (hL : yOfL22 T M =
      ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆) :
    ∃ a ∈ pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G),
      a ∉ Subgroup.centralizer (VZ T M : Set G) := by
  by_contra hno
  push Not at hno
  apply S.hyp1281.not_le_centralizer_L
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  rw [hL]
  refine Subgroup.commutator_le.mpr fun l hl b hb => ?_
  have hlM : l ∈ M := S.hyp1281.le hl
  have hbC : b ∈ Subgroup.centralizer (VZ T M : Set G) := hno b hb
  have hlb : l * b * l⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 : l⁻¹ * v * l ∈ VZ T M := by
      have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hlM)) v).mp hv
      simpa using this
    have h2 : (l⁻¹ * v * l) * b = b * (l⁻¹ * v * l) := Subgroup.mem_centralizer_iff.mp hbC _ h1
    calc v * (l * b * l⁻¹) = l * ((l⁻¹ * v * l) * b) * l⁻¹ := by group
      _ = l * (b * (l⁻¹ * v * l)) * l⁻¹ := by rw [h2]
      _ = (l * b * l⁻¹) * v := by group
  have : ⁅l, b⁆ = (l * b * l⁻¹) * b⁻¹ := commutatorElement_def _ _
  rw [this]
  exact Subgroup.mul_mem _ hlb (Subgroup.inv_mem _ hbC)

omit [Finite G] in
theorem exists_pow_mul_eq_of_normalizer {L : Subgroup G} {l q : G} (hl : l ∈ L)
    (hq : q ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    ∃ l' ∈ L, (l * q) ^ n = l' * q ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hqn : q ^ n ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hq n
    have h1 : q ^ n * l * (q ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hqn l).mp hl
    refine ⟨l' * (q ^ n * l * (q ^ n)⁻¹), L.mul_mem hl' h1, ?_⟩
    rw [pow_succ, h]
    group

omit [Finite G] in
theorem mem_of_odd_orderOf_of_sup_pGroup {L Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ L ⊔ Q)
    (hodd : Odd (orderOf y)) : y ∈ L := by
  have hy' : y ∈ ((L ⊔ Q : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L Q hQL] at hy'
  obtain ⟨l, hl, q, hq, hyq⟩ := hy'
  have hyq' : y = l * q := hyq.symm
  subst hyq'
  obtain ⟨l', hl', h⟩ := exists_pow_mul_eq_of_normalizer hl (hQL hq) (orderOf (l * q))
  rw [pow_orderOf_eq_one] at h
  have hqm : q ^ orderOf (l * q) ∈ L := by
    have : q ^ orderOf (l * q) = l'⁻¹ := by
      calc q ^ orderOf (l * q) = l'⁻¹ * (l' * q ^ orderOf (l * q)) := by group
        _ = l'⁻¹ := by rw [← h]; group
    rw [this]; exact L.inv_mem hl'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨q, hq⟩
  have hqk : q ^ (2 ^ k) = 1 := by
    have := pow_orderOf_eq_one (⟨q, hq⟩ : Q)
    rw [hk] at this
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (orderOf (l * q)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_comm.mp
      (Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat))
  have hbez : (orderOf (l * q) : ℤ) * Nat.gcdA (orderOf (l * q)) (2 ^ k) +
      ((2 ^ k : ℕ) : ℤ) * Nat.gcdB (orderOf (l * q)) (2 ^ k) = 1 := by
    have := Nat.gcd_eq_gcd_ab (orderOf (l * q)) (2 ^ k)
    rw [hcop.gcd_eq_one] at this
    push_cast at this ⊢
    linarith
  have hqL : q ∈ L := by
    have : q = (q ^ orderOf (l * q)) ^ Nat.gcdA (orderOf (l * q)) (2 ^ k) *
        (q ^ (2 ^ k)) ^ Nat.gcdB (orderOf (l * q)) (2 ^ k) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hbez, zpow_one]
    rw [this, hqk, one_zpow, mul_one]
    exact L.zpow_mem hqm _
  exact L.mul_mem hl hqL

theorem inf_pCoreOf_sup_le (L T : Subgroup G) :
    L ⊓ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 L := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_right)
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
    le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hg)⟩

theorem perm3_odd_order_fact : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → τ ^ 3 = 1 → τ ≠ 1 →
    σ = 1 ∨ σ = τ ∨ σ = τ ^ 2 := by decide

omit [Finite G] in
theorem eq_one_of_mem_isPGroup_of_odd_orderOf {P : Subgroup G} (hP : IsPGroup 2 P) {y : G} (hy : y ∈ P)
    (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_coe (⟨y, hy⟩ : P)).trans hk
  rw [hk'] at hodd
  have hk0 : k = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, h⟩)
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem Setting146.L_eq_lI_sup_of_odd (S : Setting146 G T M) {I : Subgroup G} {y : G}
    (hyL : y ∈ yOfL22 T M) (hyI : y ∈ I) (hodd : Odd (orderOf y)) (hy1 : y ≠ 1) :
    yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) := by
  obtain ⟨φ⟩ := S.hyp1281.sThree
  set L := yOfL22 T M with hLdef
  have hLT : ∀ x ∈ L, x ∈ L ⊔ T := fun x hx => Subgroup.mem_sup_left hx
  have hy_LT : y ∈ L ⊔ T := hLT y hyL
  have hyO : y ∉ pCoreOf 2 (L ⊔ T) := fun h =>
    hy1 (eq_one_of_mem_isPGroup_of_odd_orderOf (pCoreOf_isPGroup 2 (L ⊔ T)) h hodd)
  have hc1 : Der6A.piS3 φ ⟨y, hy_LT⟩ ≠ 1 := fun h => hyO ((Der6A.piS3_eq_one_iff φ hy_LT).mp h)
  have hcube : ∀ (x : G) (hx : x ∈ L ⊔ T), Odd (orderOf x) → (Der6A.piS3 φ ⟨x, hx⟩) ^ 3 = 1 := by
    intro x hx hxodd
    have h1 : orderOf (Der6A.piS3 φ ⟨x, hx⟩) ∣ orderOf x := by
      have := orderOf_map_dvd (Der6A.piS3 φ) (⟨x, hx⟩ : ↥(L ⊔ T))
      have e : orderOf (⟨x, hx⟩ : ↥(L ⊔ T)) = orderOf x :=
        (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(L ⊔ T))).symm
      rwa [e] at this
    have h2 : orderOf (Der6A.piS3 φ ⟨x, hx⟩) ∣ 3 * 2 := by
      have := orderOf_dvd_natCard (Der6A.piS3 φ ⟨x, hx⟩)
      have hc : Nat.card (Equiv.Perm (Fin 3)) = 3 * 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
      rwa [hc] at this
    have h3 : Nat.Coprime (orderOf (Der6A.piS3 φ ⟨x, hx⟩)) 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr (Odd.of_dvd_nat hxodd h1).not_two_dvd_nat).symm
    exact orderOf_dvd_iff_pow_eq_one.mp (h3.dvd_of_dvd_mul_right h2)
  have hlI : y ∈ lI T M I := Subgroup.subset_closure ⟨⟨hyL, hyI⟩, hodd⟩
  have hkey : ∀ x ∈ L, Odd (orderOf x) → x ∈ lI T M I ⊔ pCoreOf 2 L := by
    intro x hx hxodd
    have hx_LT := hLT x hx
    have hσ3 := hcube x hx_LT hxodd
    have hc3 := hcube y hy_LT hodd
    have hmain : ∀ k : ℕ, Der6A.piS3 φ ⟨x, hx_LT⟩ = Der6A.piS3 φ ⟨y, hy_LT⟩ ^ k → x ∈ lI T M I ⊔ pCoreOf 2 L := by
      intro k hk
      have hyk : y ^ k ∈ L := L.pow_mem hyL k
      have hykLT : (y ^ k)⁻¹ * x ∈ L ⊔ T :=
        (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ((L ⊔ T).pow_mem hy_LT k)) hx_LT
      have h1 : Der6A.piS3 φ ⟨(y ^ k)⁻¹ * x, hykLT⟩ = 1 := by
        have e : (⟨(y ^ k)⁻¹ * x, hykLT⟩ : ↥(L ⊔ T)) =
            (⟨y, hy_LT⟩ ^ k)⁻¹ * ⟨x, hx_LT⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, map_pow, ← hk, inv_mul_cancel]
      have h2 : (y ^ k)⁻¹ * x ∈ pCoreOf 2 L :=
        (inf_pCoreOf_sup_le L T ⟨L.mul_mem (L.inv_mem hyk) hx,
          (Der6A.piS3_eq_one_iff φ hykLT).mp h1⟩)
      have e2 : x = y ^ k * ((y ^ k)⁻¹ * x) := by group
      rw [e2]
      exact Subgroup.mul_mem_sup ((lI T M I).pow_mem hlI k) h2
    rcases perm3_odd_order_fact _ _ hσ3 hc3 hc1 with h | h | h
    · exact hmain 0 (by rw [h, pow_zero])
    · exact hmain 1 (by rw [h, pow_one])
    · exact hmain 2 h
  have hres : oTwoUpper L = L := S.hyp1281.residual
  refine le_antisymm ?_ (sup_le ((oTwoUpper_le _).trans inf_le_left) (pCoreOf_le 2 _))
  calc L = oTwoUpper L := hres.symm
    _ ≤ lI T M I ⊔ pCoreOf 2 L := (Subgroup.closure_le _).mpr fun x hx => hkey x hx.1 hx.2

theorem Setting146.exists_fixed_of_isPGroup (S : Setting146 G T M) {Y : Subgroup G} (hYM : Y ≤ M)
    (hY : IsPGroup 2 Y) : ∃ v ∈ VZ T M, v ≠ 1 ∧ ∀ y ∈ Y, y * v * y⁻¹ = v := by
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction Y (VZ T M) :=
    { smul := fun y v => ⟨y * v * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hMV (hYM y.2)) v).mp v.2⟩
      one_smul := fun v => Subtype.ext (by
        show ((1 : Y) : G) * (v : G) * ((1 : Y) : G)⁻¹ = v
        simp)
      mul_smul := fun a b v => Subtype.ext (by
        show ((a * b : Y) : G) * (v : G) * ((a * b : Y) : G)⁻¹ =
          (a : G) * ((b : G) * (v : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hcard : 2 ∣ Nat.card (VZ T M) := by rw [S.hyp.rank_two]; norm_num
  have h1 : (1 : VZ T M) ∈ MulAction.fixedPoints Y (VZ T M) := fun y => Subtype.ext (by
    show (y : G) * 1 * (y : G)⁻¹ = 1
    simp)
  obtain ⟨b, hb, hb1⟩ := hY.exists_fixed_point_of_prime_dvd_card_of_fixed_point (VZ T M) hcard h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun y hy => ?_⟩
  exact congrArg Subtype.val (hb ⟨y, hy⟩)


theorem mem_centralizer_of_commute_two {V : Subgroup G} (hV : Nat.card V = 4)
    (hV2 : ∀ u ∈ V, u * u = 1) {z0 v s : G} (hz0 : z0 ∈ V) (hv : v ∈ V) (hz01 : z0 ≠ 1)
    (hv1 : v ≠ 1) (hne : v ≠ z0) (hs0 : s * z0 = z0 * s) (hsv : s * v = v * s) :
    s ∈ Subgroup.centralizer (V : Set G) := by
  set C := V ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hmemC : ∀ g ∈ V, s * g = g * s → g ∈ C := fun g hg h =>
    ⟨hg, Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
      rw [Set.mem_singleton_iff.mp hh']; exact h⟩
  have hz0C : z0 ∈ C := hmemC z0 hz0 hs0
  have hvC : v ∈ C := hmemC v hv hsv
  have hz2 : z0 ^ 2 = 1 := by rw [pow_two]; exact hV2 z0 hz0
  have hord : orderOf z0 = 2 := orderOf_eq_prime hz2 hz01
  have hcardz : Nat.card (Subgroup.zpowers z0) = 2 := by rw [Nat.card_zpowers, hord]
  have hzC : Subgroup.zpowers z0 ≤ C := Subgroup.zpowers_le.mpr hz0C
  have hdvd : Nat.card C ∣ 4 := hV ▸ Subgroup.card_dvd_of_le (inf_le_left : C ≤ V)
  have hdvd2 : 2 ∣ Nat.card C := hcardz ▸ Subgroup.card_dvd_of_le hzC
  have hne2 : Nat.card C ≠ 2 := by
    intro h2
    have heq : Subgroup.zpowers z0 = C := Subgroup.eq_of_le_of_card_ge hzC (by rw [hcardz, h2])
    have hvz : v ∈ Subgroup.zpowers z0 := heq ▸ hvC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvz
    have hk' : z0 ^ (k % 2) = v := by
      have h := zpow_mod_orderOf z0 k
      rw [hord] at h
      push_cast at h
      rw [h, hk]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk'
      exact hv1 hk'.symm
    · rw [h1, zpow_one] at hk'
      exact hne hk'.symm
  have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h4 : Nat.card C = 4 := by
    interval_cases hc : Nat.card C <;> first | rfl | omega
  have hCV : C = V := Subgroup.eq_of_le_of_card_ge (inf_le_left) (by rw [h4, hV])
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  have hu' : u ∈ C := hCV ▸ hu
  exact (Subgroup.mem_centralizer_iff.mp hu'.2 s rfl).symm

theorem Setting146.exists_odd_mem_L_inf_I (S : Setting146 G T M) {u : G} {I : Subgroup G}
    (hTuI : tU T u ≤ I)
    (hL : yOfL22 T M =
      ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆)
    (hX : ¬ I ⊓ M ≤ mcOf T) :
    ∃ y ∈ yOfL22 T M ⊓ I, Odd (orderOf y) ∧ y ≠ 1 := by
  obtain ⟨a, haB, haV⟩ := S.exists_mem_not_centralizer_V hL
  obtain ⟨x₁, hx₁, hx₁G⟩ := IsConcreteLE.not_le_iff_exists.mp hX
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hsq : ∀ w ∈ VZ T M, w * w = 1 := by
    obtain ⟨hVred, -⟩ := S.hyp1281.isTwoReducedIn
    intro w hw
    simpa [sq] using hVred.2.2.1.2 w hw
  have haQ : a ∈ pCoreOf 2 (mcOf T) := haB.1
  have haT : a ∈ T := hQ1T haQ
  have haI : a ∈ I := hTuI ((S146T.mem_tU_iff).mpr ⟨haT,
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp haB.2 u rfl).symm⟩)
  have hza : z * a = a * z := Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ haQ) z hzZ
  have hNM : yOfL22 T M ⊔ pCoreOf 2 (mcOf T) ≤ M := sup_le S.hyp1281.le (hQ1T.trans hTM)
  have haN : a ∈ yOfL22 T M ⊔ pCoreOf 2 (mcOf T) := Subgroup.mem_sup_right haQ
  have hx₁M : x₁ ∈ M := hx₁.2
  have hβN : x₁ * a * x₁⁻¹ ∈ yOfL22 T M ⊔ pCoreOf 2 (mcOf T) :=
    (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_L_sup_Q1 hx₁M) a).mp haN
  have hβI : x₁ * a * x₁⁻¹ ∈ I := I.mul_mem (I.mul_mem hx₁.1 haI) (I.inv_mem hx₁.1)
  by_cases hY2 : IsPGroup 2 ((yOfL22 T M ⊔ pCoreOf 2 (mcOf T)) ⊓ I : Subgroup G)
  · exfalso
    obtain ⟨v, hvV, hv1, hvfix⟩ := S.exists_fixed_of_isPGroup (inf_le_left.trans hNM) hY2
    have hav : a * v = v * a := by
      calc a * v = (a * v * a⁻¹) * a := by group
        _ = v * a := by rw [hvfix a ⟨haN, haI⟩]
    have hβv : (x₁ * a * x₁⁻¹) * v = v * (x₁ * a * x₁⁻¹) := by
      calc (x₁ * a * x₁⁻¹) * v
          = ((x₁ * a * x₁⁻¹) * v * (x₁ * a * x₁⁻¹)⁻¹) * (x₁ * a * x₁⁻¹) := by group
        _ = v * (x₁ * a * x₁⁻¹) := by rw [hvfix _ ⟨hβN, hβI⟩]
    have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
    have hvz : v = z := by
      by_contra hne
      exact haV (mem_centralizer_of_commute_two hV4 hsq hzV hvV hz1' hv1 hne hza.symm hav)
    have hz₁V : x₁ * z * x₁⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hx₁M) z).mp hzV
    have hz₁1 : x₁ * z * x₁⁻¹ ≠ 1 := by
      intro h
      apply hz1'
      calc z = x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by group
        _ = 1 := by rw [h]; group
    have hvz₁ : v = x₁ * z * x₁⁻¹ := by
      by_contra hne
      have hβz₁ : (x₁ * a * x₁⁻¹) * (x₁ * z * x₁⁻¹) = (x₁ * z * x₁⁻¹) * (x₁ * a * x₁⁻¹) := by
        calc (x₁ * a * x₁⁻¹) * (x₁ * z * x₁⁻¹) = x₁ * (a * z) * x₁⁻¹ := by group
          _ = x₁ * (z * a) * x₁⁻¹ := by rw [hza]
          _ = (x₁ * z * x₁⁻¹) * (x₁ * a * x₁⁻¹) := by group
      have hβC := mem_centralizer_of_commute_two hV4 hsq hz₁V hvV hz₁1 hv1 hne hβz₁ hβv
      apply haV
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have hw' : x₁ * w * x₁⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hx₁M) w).mp hw
      have h1 := Subgroup.mem_centralizer_iff.mp hβC _ hw'
      have e1 : x₁ * (w * a) * x₁⁻¹ = x₁ * (a * w) * x₁⁻¹ := by
        calc x₁ * (w * a) * x₁⁻¹ = (x₁ * w * x₁⁻¹) * (x₁ * a * x₁⁻¹) := by group
          _ = (x₁ * a * x₁⁻¹) * (x₁ * w * x₁⁻¹) := h1
          _ = x₁ * (a * w) * x₁⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e1)
    have hzz : x₁ * z * x₁⁻¹ = z := by rw [← hvz₁, hvz]
    apply hx₁G
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    by_cases hy1 : y = 1
    · simp [hy1]
    · have hyz : y = z := S.Z_eq_of_iff hy hzZ ⟨fun h => absurd h hy1, fun h => absurd h hz1'⟩
      subst hyz
      calc y * x₁ = (x₁ * y * x₁⁻¹) * x₁ := by rw [hzz]
        _ = x₁ * y := by group
  · have hpos : Nat.card ((yOfL22 T M ⊔ pCoreOf 2 (mcOf T)) ⊓ I : Subgroup G) ≠ 0 := Nat.card_pos.ne'
    obtain ⟨p, hp, hpd, hp2⟩ : ∃ p, p.Prime ∧ p ∣
        Nat.card ((yOfL22 T M ⊔ pCoreOf 2 (mcOf T)) ⊓ I : Subgroup G) ∧ p ≠ 2 := by
      by_contra hno
      push Not at hno
      apply hY2
      exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {d} hd hdd =>
        hno d hd hdd)
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyG : orderOf (y : G) = p := (Subgroup.orderOf_coe y).trans hy
    have hodd : Odd (orderOf (y : G)) := by rw [hyG]; exact hp.odd_of_ne_two hp2
    have hQL : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (yOfL22 T M : Set G) := fun q hq =>
      S.hyp1281.normal (hTM (hQ1T hq))
    have hyL : (y : G) ∈ yOfL22 T M :=
      mem_of_odd_orderOf_of_sup_pGroup (pCoreOf_isPGroup 2 (mcOf T)) hQL y.2.1 hodd
    refine ⟨y, ⟨hyL, y.2.2⟩, hodd, fun h1 => ?_⟩
    rw [h1, orderOf_one] at hyG
    exact hp.one_lt.ne hyG


theorem perm3_square_fact : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 2 = 1 → τ ^ 2 = 1 → (σ * τ) ^ 2 = 1 →
    σ = 1 ∨ τ = 1 ∨ σ = τ := by decide

omit [Finite G] in
theorem piS3_sq_eq_one {X : Subgroup G} (φ : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : G} (hx : x ∈ X)
    {k : ℕ} (hk : orderOf x = 2 ^ k) : (Der6A.piS3 φ ⟨x, hx⟩) ^ 2 = 1 := by
  have h1 : orderOf (Der6A.piS3 φ ⟨x, hx⟩) ∣ 2 ^ k := by
    have := orderOf_map_dvd (Der6A.piS3 φ) (⟨x, hx⟩ : ↥X)
    have e : orderOf (⟨x, hx⟩ : ↥X) = orderOf x := (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥X)).symm
    rw [e, hk] at this
    exact this
  have h2 : orderOf (Der6A.piS3 φ ⟨x, hx⟩) ∣ 3 * 2 := by
    have := orderOf_dvd_natCard (Der6A.piS3 φ ⟨x, hx⟩)
    have hc : Nat.card (Equiv.Perm (Fin 3)) = 3 * 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
    rwa [hc] at this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hj2
    have h46 : 2 ^ 2 ∣ 3 * 2 := h4.trans (hj' ▸ h2)
    norm_num at h46
  refine orderOf_dvd_iff_pow_eq_one.mp ?_
  rw [hj']
  calc 2 ^ j ∣ 2 ^ 1 := pow_dvd_pow 2 hj1
    _ = 2 := by norm_num

theorem Setting146.LT_eq_of_L_eq (S : Setting146 G T M) {u : G} {I : Subgroup G}
    (hTuI : tU T u ≤ I)
    (hL : yOfL22 T M =
      ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆)
    (hLeq : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M)) :
    yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) := by
  obtain ⟨φ⟩ := S.hyp1281.sThree
  obtain ⟨a, haB, haV⟩ := S.exists_mem_not_centralizer_V hL
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTM : T ≤ M := S.hyp1281.inM.2
  have haT : a ∈ T := S.pCoreOf_mcOf_le haB.1
  have haI : a ∈ I := hTuI ((S146T.mem_tU_iff).mpr ⟨haT,
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp haB.2 u rfl).symm⟩)
  have hLT : yOfL22 T M ⊔ T ≤ M := sup_le S.hyp1281.le hTM
  have hOC : pCoreOf 2 (yOfL22 T M ⊔ T) ≤ Subgroup.centralizer (VZ T M : Set G) := by
    rw [← S.hyp1281.centralizer]; exact inf_le_right
  have haO : a ∉ pCoreOf 2 (yOfL22 T M ⊔ T) := fun h => haV (hOC h)
  have haLT : a ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_right haT
  have hlIle : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  refine le_antisymm ?_ (sup_le (sup_le (hlIle.trans le_sup_left) (inf_le_left.trans le_sup_right))
    (pCoreOf_le 2 _))
  set R := (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) with hR
  have hOR : pCoreOf 2 (yOfL22 T M ⊔ T) ≤ R := le_sup_right
  have hlR : lI T M I ≤ R := le_sup_left.trans le_sup_left
  have haR : a ∈ R := Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨haT, haI⟩)
  refine sup_le ?_ ?_
  ·
    have hO2 : pCoreOf 2 (yOfL22 T M) ≤ pCoreOf 2 (yOfL22 T M ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
        ((pCoreOf_isPGroup 2 (yOfL22 T M)))
      exact hLT.trans (S.hyp1281.normal.trans (normalizer_le_normalizer_pCoreOf 2 _))
    rw [hLeq]
    exact sup_le hlR (hO2.trans hOR)
  ·
    intro t ht
    have ht_LT : t ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_right ht
    have hsq : ∀ x (hx : x ∈ T), (Der6A.piS3 φ ⟨x, (Subgroup.mem_sup_right hx : x ∈ yOfL22 T M ⊔ T)⟩) ^ 2 = 1 := by
      intro x hx
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨x, hx⟩
      exact piS3_sq_eq_one φ _ ((Subgroup.orderOf_coe (⟨x, hx⟩ : T)).trans hk)
    have hta : t * a ∈ T := T.mul_mem ht haT
    have hmul : Der6A.piS3 φ ⟨t, ht_LT⟩ * Der6A.piS3 φ ⟨a, haLT⟩ =
        Der6A.piS3 φ ⟨t * a, (Subgroup.mem_sup_right hta : t * a ∈ yOfL22 T M ⊔ T)⟩ := by
      rw [← map_mul]; rfl
    have hca : Der6A.piS3 φ ⟨a, haLT⟩ ≠ 1 := fun h => haO ((Der6A.piS3_eq_one_iff φ haLT).mp h)
    rcases perm3_square_fact _ _ (hsq t ht) (hsq a haT) (hmul ▸ hsq (t * a) hta) with h | h | h
    · exact hOR ((Der6A.piS3_eq_one_iff φ ht_LT).mp h)
    · exact absurd h hca
    · have hta' : t * a⁻¹ ∈ yOfL22 T M ⊔ T :=
        (yOfL22 T M ⊔ T).mul_mem ht_LT ((yOfL22 T M ⊔ T).inv_mem haLT)
      have h1 : Der6A.piS3 φ ⟨t * a⁻¹, hta'⟩ = 1 := by
        have e : (⟨t * a⁻¹, hta'⟩ : ↥(yOfL22 T M ⊔ T)) = ⟨t, ht_LT⟩ * (⟨a, haLT⟩)⁻¹ :=
          Subtype.ext (by simp)
        rw [e, map_mul, map_inv, h, mul_inv_cancel]
      have h2 : t * a⁻¹ ∈ pCoreOf 2 (yOfL22 T M ⊔ T) := (Der6A.piS3_eq_one_iff φ hta').mp h1
      have e2 : t = (t * a⁻¹) * a := by group
      rw [e2]
      exact R.mul_mem (hOR h2) haR

theorem stage1466_three_of (h3 : Stage1463Three) : Stage1466Three := by
  intro G _ _ T M H u S hH hu I hI hX
  have hL := (h3 G T M S H hH u hu).2.1
  obtain ⟨y, hy, hodd, hy1⟩ := S.exists_odd_mem_L_inf_I hI.1.1.1 hL hX
  have hLeq := S.L_eq_lI_sup_of_odd hy.1 hy.2 hodd hy1
  exact ⟨hLeq, S.LT_eq_of_L_eq hI.1.1.1 hL hLeq⟩

end CFSG.Quasithin
