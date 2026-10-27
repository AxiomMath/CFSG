module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4B

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace NoJ4

theorem center_eq_bot_of_m24
    {X : Type} [Group X] (h : IsSporadic .M24 X) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have e' : X ≃* CFSG.Blueprint.NativeSporadic.M24 := e
  have h1 := center_map_mulEquiv e'
  rw [CFSG.Sporadic.Schreier.m24_center_eq_bot'] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1

theorem center_eq_bot_of_l52 {X : Type} [Group X] (h : IsPSL 5 2 1 X) :
    Subgroup.center X = ⊥ := by
  have hcard := F420.card_of_l52 h
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨-, F, hF, hFf, hFc, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 5 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hsX : IsSimpleGroup X :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 F).symm
      ).isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a
    let _ : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
    rw [hcard] at hp
    norm_num at hp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem modO2_center_eq_bot
    {T M L I H K : Subgroup G}
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) : Subgroup.center (ModO2 (perfectCore (L ⊓ H))) = ⊥ := by
  rcases h6.2.2 with ⟨h, -⟩ | ⟨h, -⟩
  · exact center_eq_bot_of_m24 h
  · exact center_eq_bot_of_l52 h

omit [Finite G] in
theorem mem_E_of
    {T M L I H K : Subgroup G}
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) {l : G} (hl : l ∈ perfectCore (L ⊓ H))
    (hlx : ∀ x ∈ perfectCore (L ⊓ H), l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 (perfectCore (L ⊓ H))) :
    l ∈ pCoreOf 2 (perfectCore (L ⊓ H)) := by
  set LH := perfectCore (L ⊓ H) with hLH
  have hZ := modO2_center_eq_bot h6
  have hp : pCoreOf 2 LH = (CFSG.pCore 2 ↥LH).map LH.subtype := C2A3Orbits.pCoreOf_eq_map_pCore LH
  have hmem : (QuotientGroup.mk (⟨l, hl⟩ : ↥LH) : ModO2 LH) ∈ Subgroup.center (ModO2 LH) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := hlx x x.2
    rw [hp] at h1
    obtain ⟨y, hy, hye⟩ := h1
    have e : (x * ⟨l, hl⟩)⁻¹ * (⟨l, hl⟩ * x) = (x * ⟨l, hl⟩)⁻¹ * y * (x * ⟨l, hl⟩) := by
      apply Subtype.ext
      have hye' : (y : G) = l * (x : G) * l⁻¹ * (x : G)⁻¹ := hye
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hye']
      group
    rw [e]
    exact CFSG.pCore_normal.conj_mem' y hy (x * ⟨l, hl⟩)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  rw [hp]
  exact ⟨_, hmem, rfl⟩

theorem inf_pCoreOf_le (L H : Subgroup G) :
    perfectCore (L ⊓ H) ⊓ pCoreOf 2 L ≤ pCoreOf 2 (perfectCore (L ⊓ H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  have hLHL : LH ≤ L := (perfectCore_le (L ⊓ H)).trans inf_le_left
  have hn : LH ≤ Subgroup.normalizer ((LH ⊓ pCoreOf 2 L : Subgroup G) : Set G) := by
    intro y hy'
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyO := le_normalizer_pCoreOf 2 L (hLHL hy')
    constructor
    · rintro ⟨hzL, hzO⟩
      exact ⟨LH.mul_mem (LH.mul_mem hy' hzL) (LH.inv_mem hy'),
        (Subgroup.mem_normalizer_iff.mp hyO z).mp hzO⟩
    · rintro ⟨hzL, hzO⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hyO z).mpr hzO⟩
      have := LH.mul_mem (LH.mul_mem (LH.inv_mem hy') hzL) hy'
      simpa [mul_assoc] using this
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn ((pCoreOf_isPGroup 2 L).to_le inf_le_right)

theorem eq_one_of_odd
    {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) {y : G} (hyL : y ∈ L) (hyC : ∀ x ∈ perfectCore (L ⊓ H), x * y = y * x)
    (hodd : Odd (orderOf y)) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  set E := pCoreOf 2 LH with hE
  have hLHL : LH ≤ L := (perfectCore_le (L ⊓ H)).trans inf_le_left
  have hLHn : LH ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hLHL.trans (le_normalizer_pCoreOf 2 L)
  obtain ⟨l, hl, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hLHn).mp (c.L_le hyL)
  have hlE : l ∈ E := by
    have h1 : l⁻¹ ∈ E := by
      refine mem_E_of h6 (LH.inv_mem hl) fun x hx => ?_
      have hcx := hyC x hx
      have e1 : o * x * o⁻¹ = l⁻¹ * x * l := by
        calc o * x * o⁻¹ = l⁻¹ * (x * (l * o)) * o⁻¹ := by rw [hcx]; group
          _ = l⁻¹ * x * l := by group
      refine inf_pCoreOf_le L H ⟨?_, ?_⟩
      · rw [show l⁻¹ * x * l⁻¹⁻¹ * x⁻¹ = l⁻¹ * x * l * x⁻¹ by group]
        exact LH.mul_mem (LH.mul_mem (LH.mul_mem (LH.inv_mem hl) hx) hl) (LH.inv_mem hx)
      · rw [show l⁻¹ * x * l⁻¹⁻¹ * x⁻¹ = (l⁻¹ * x * l) * x⁻¹ by group, ← e1,
          show o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) by group]
        exact (pCoreOf 2 L).mul_mem ho
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (hLHL hx)) _).mp
            ((pCoreOf 2 L).inv_mem ho))
    simpa using E.inv_mem h1
  have hEn : E ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := (pCoreOf_le 2 LH).trans hLHn
  have hp : IsPGroup 2 ↥(E ⊔ pCoreOf 2 L) :=
    IsPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 LH) (pCoreOf_isPGroup 2 L) hEn
  have hmem : l * o ∈ E ⊔ pCoreOf 2 L :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hlE) (Subgroup.mem_sup_right ho)
  obtain ⟨k, hk⟩ := hp ⟨l * o, hmem⟩
  have hk' : (l * o) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hj0
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

omit [Finite G] in
theorem mem_of_odd {L T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ L ⊔ T)
    (hodd : Odd (orderOf y)) : y ∈ L := by
  rw [sup_comm] at hy
  obtain ⟨t, ht, l, hl, rfl⟩ := (mem_sup_of_le_normalizer hTL).mp hy
  have key : ∀ n : ℕ, ∃ l' ∈ L, (t * l) ^ n = t ^ n * l' := by
    intro n
    induction n with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', he⟩ := ih
      refine ⟨t⁻¹ * l' * t * l, L.mul_mem ?_ hl, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTL ht)) l').mp hl'
        simpa using this
      · rw [pow_succ, he, pow_succ]
        group
  obtain ⟨c, hc⟩ := hT ⟨t, ht⟩
  have hc' : t ^ 2 ^ c = 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  obtain ⟨l', hl', he⟩ := key (2 ^ c)
  have hpow : (t * l) ^ 2 ^ c ∈ L := by rw [he, hc', one_mul]; exact hl'
  have hcop : Nat.Coprime (2 ^ c) (orderOf (t * l)) :=
    Nat.Coprime.pow_left c ((Nat.coprime_two_left).mpr hodd)
  have hg := Nat.gcd_eq_gcd_ab (2 ^ c) (orderOf (t * l))
  rw [hcop.gcd_eq_one, Nat.cast_one] at hg
  have e : t * l = ((t * l) ^ 2 ^ c) ^ (Nat.gcdA (2 ^ c) (orderOf (t * l))) *
      ((t * l) ^ orderOf (t * l)) ^ (Nat.gcdB (2 ^ c) (orderOf (t * l))) := by
    rw [← zpow_natCast (t * l) (2 ^ c), ← zpow_natCast (t * l) (orderOf (t * l)), ← zpow_mul,
      ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [e, pow_orderOf_eq_one, one_zpow, mul_one]
  exact L.zpow_mem hpow _

theorem isPGroup_inf_centralizer
    {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) (hILT : I ≤ L ⊔ T) :
    IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (K : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 ↥T := c.hyp421.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  rw [IsPGroup.iff_orderOf]
  intro g
  have hyI : (g : G) ∈ I := g.2.1
  have hyC : (g : G) ∈ Subgroup.centralizer (K : Set G) := g.2.2
  rw [← Subgroup.orderOf_coe]
  set y : G := (g : G) with hydef
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hyb : orderOf (y ^ 2 ^ a) = b := by
    rw [orderOf_pow' y (pow_ne_zero a two_ne_zero), hab, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hy1 : y ^ 2 ^ a = 1 := by
    refine eq_one_of_odd c h6 ?_ (fun x hx => ?_) (hyb ▸ hb)
    · exact mem_of_odd hT hTL (hILT (I.pow_mem hyI _)) (hyb ▸ hb)
    · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyC _) x (c.LH_le hx))
  refine ⟨a, ?_⟩
  have hdvd := orderOf_dvd_of_pow_eq_one hy1
  rw [hab] at hdvd ⊢
  have hb1 : b = 1 := by
    have h2 : 2 ^ a * b ∣ 2 ^ a * 1 := by rw [mul_one]; exact hdvd
    exact Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos a) h2)
  rw [hb1, mul_one]

end NoJ4

end CFSG.Quasithin.H13.Ch4
