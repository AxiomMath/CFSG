module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113A7FF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_four_m4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    L = ⁅L, thompsonJ T⁆ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
      Nat.card ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
        conjClosure Kh₁ T⁆ ≠ 2 ^ 6

@[expose] def Stmt5_1_13_four_ZL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    L = ⁅L, thompsonJ T⁆ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n → ⁅quasithinOmegaOneCenter T, L⁆ ≠ ⊥

theorem sl2_mul_self_eq_one_of_fixed {K : Type} [Field K] [CharP K 2]
    {A : Matrix (Fin 2) (Fin 2) K} (hdet : A.det = 1) {x : Fin 2 → K} (hx : x ≠ 0)
    (hAx : A.mulVec x = x) : A * A = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (A - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨x, hx, by rw [Matrix.sub_mulVec, hAx, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hdet h1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at h1
  have hsum : A 0 0 + A 1 1 = 0 := by linear_combination -h1 + hdet + h2
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    linear_combination -hdet + A 0 0 * hsum - h2
  have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by linear_combination A 0 1 * hsum
  have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by linear_combination A 1 0 * hsum
  have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by
    linear_combination -hdet + A 1 1 * hsum - h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]

section Natural

variable {G : Type} [Group G]

theorem IsNatQuotCh5.mem_centralizer_of_conj_eq {L V : Subgroup G} {n : ℕ}
    (h : IsNatQuotCh5 L V n) {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hdV : d ∉ Subgroup.centralizer (V : Set G)) {v : G} (hv : v ∈ V)
    (hdv : d * v * d⁻¹ = v) : v ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hLV, hc, K, hKf, hKfin, hK, π, hπs, -, hks, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  by_contra hvL
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  set a : ↥(autOn L V) := ⟨A4.actionOn V L hLV ⟨d, hdL⟩,
    (A4.mem_autOn_iff hLV).mpr ⟨⟨d, hdL⟩, rfl⟩⟩ with ha
  obtain ⟨γ, hγ⟩ := hπs a
  set u : ↥(⊤ : Subgroup ↥V) := ⟨⟨v, hv⟩, Subgroup.mem_top _⟩ with hu
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hu' : ((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V) ∈ (⊤ : Subgroup ↥V) :=
    Subgroup.mem_top _
  have he := hβe γ u m hu' (Subgroup.mem_top _) hm.symm
  have hfix : (⟨((π γ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V), hu'⟩ : ↥(⊤ : Subgroup ↥V)) = u := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hγ]
    show ((A4.actionOn V L hLV ⟨d, hdL⟩ ⟨v, hv⟩ : ↥V) : G) = v
    rw [A4.actionOn_apply_coe]
    exact hdv
  rw [hfix, ← hm, QuotientGroup.eq] at he
  have hm1 : m ≠ 1 := by
    intro hm1
    apply hvL
    have h1 : β u = 1 := by rw [← hm, hm1]; rfl
    have h2 := (hβk u).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  obtain ⟨x, hx⟩ : ∃ x : Multiplicative (Fin 2 → K), x = m.1 := ⟨m.1, rfl⟩
  have hfixm : natAct (Assembly.LowTwoRank.StatedSL 2 K) γ x = x := by
    have h2 := Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp he)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one] at h2
    rw [hx]
    exact h2.symm
  have hmv : ((Subtype.val γ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd x) = Multiplicative.toAdd x :=
    congrArg Multiplicative.toAdd hfixm
  have hm0 : Multiplicative.toAdd x ≠ 0 := by
    intro h0
    apply hm1
    apply Subtype.ext
    rw [← hx]
    exact toAdd_eq_zero.mp h0
  have hdet := Vol2.Ch10.SecA.det_eq_one_of_mem_statedSL (Subtype.prop γ)
  have hsq := sl2_mul_self_eq_one_of_fixed hdet hm0 hmv
  have hγ2 : γ * γ = 1 := Subtype.ext (Units.ext hsq)
  have ha2 : a * a = 1 := by rw [← hγ, ← map_mul, hγ2, map_one]
  have hd2 : d * d ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : A4.actionOn V L hLV (⟨d, hdL⟩ * ⟨d, hdL⟩) = 1 := by
      rw [map_mul]
      exact congrArg Subtype.val ha2
    exact (A4.actionOn_eq_one_iff hLV _).mp h1
  apply hdV
  have h4 : d = (d * d) * (d * d) := by
    have h5 : d ^ 3 = d * d * d := by rw [pow_succ, pow_two]
    calc d = d ^ 3 * d := by rw [hd3, one_mul]
      _ = (d * d) * (d * d) := by rw [h5]; simp only [mul_assoc]
  rw [h4]
  exact Subgroup.mul_mem _ hd2 hd2

end Natural

section Pack

variable {G : Type} [Group G] [Finite G]

structure A7Pack (T K Kh W : Subgroup G) (e : O2Q Kh ≃* alternatingGroup (Fin 7)) : Prop where
  red : IsTwoReducedIn (Kh ⊔ T) W
  le_T : W ≤ T
  dec : ⁅W, Kh⁆ ⊔ (W ⊓ Subgroup.centralizer (Kh : Set G)) = W
  inf_eq : ⁅W, Kh⁆ ⊓ Subgroup.centralizer (Kh : Set G) = ⊥
  irr : ∀ J : Subgroup G, J ≤ ⁅W, Kh⁆ → Kh ≤ Subgroup.normalizer (J : Set G) →
    J = ⊥ ∨ J = ⁅W, Kh⁆
  card : Nat.card ↥⁅W, Kh⁆ = 2 ^ 4 ∨ Nat.card ↥⁅W, Kh⁆ = 2 ^ 6
  perf : ⁅Kh, Kh⁆ = Kh
  simple : IsSimpleGroup (O2Q Kh)
  T_le : T ≤ Subgroup.normalizer (Kh : Set G)
  sylow : IsSylowTwoOf T (Kh ⊔ T)
  K_le : K ≤ Kh
  T_le_K : T ≤ Subgroup.normalizer (K : Set G)
  five : 5 ∣ Nat.card K
  r0 : (modO2Image Kh K).map e.toMonoidHom = A7Std.r0
  p0 : (modO2Image Kh (T ⊓ Kh)).map e.toMonoidHom = A7Std.p0

namespace A7Pack

variable {T K Kh W : Subgroup G} {e : O2Q Kh ≃* alternatingGroup (Fin 7)}

omit [Finite G] in
theorem U_le (pk : A7Pack T K Kh W e) : ⁅W, Kh⁆ ≤ W :=
  A7ZK.commutator_le_left_of_le_normalizer (le_sup_left.trans pk.red.2.1)

omit [Finite G] in
theorem le_normalizer (pk : A7Pack T K Kh W e) :
    Kh ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) :=
  A7ZK.le_normalizer_commutator (le_sup_left.trans pk.red.2.1) Subgroup.le_normalizer

omit [Finite G] in
theorem T_le_normalizer (pk : A7Pack T K Kh W e) :
    T ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) :=
  A7ZK.le_normalizer_commutator (le_sup_right.trans pk.red.2.1) pk.T_le

omit [Finite G] in
theorem elemAbelian (pk : A7Pack T K Kh W e) : IsElemAbelian 2 ⁅W, Kh⁆ :=
  A7ZK.isElemAbelian_of_le pk.U_le pk.red.2.2.1

omit [Finite G] in
theorem not_le_centralizer (pk : A7Pack T K Kh W e) :
    ¬ Kh ≤ Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := by
  intro hle
  have h1 : ⁅W, Kh⁆ = ⊥ := by
    rw [eq_bot_iff, ← pk.inf_eq]
    exact le_inf le_rfl (Subgroup.le_centralizer_iff.mp hle)
  rcases pk.card with h | h <;> rw [h1, Subgroup.card_bot] at h <;> norm_num at h

theorem pCoreOf_le (pk : A7Pack T K Kh W e) :
    pCoreOf 2 Kh ≤ Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans ?_ (Subgroup.centralizer_le fun x hx => pk.U_le hx)
  refine pk.red.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (pk.T_le.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
    fun d hd => ?_
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kh ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have h1 : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem exists_mul_eq (pk : A7Pack T K Kh W e) {z : G} (hzW : z ∈ W)
    (hzT : z ∈ Subgroup.centralizer (T : Set G)) :
    ∃ u ∈ ⁅W, Kh⁆, u ∈ Subgroup.centralizer (T : Set G) ∧
      ∃ c ∈ W ⊓ Subgroup.centralizer (Kh : Set G), z = u * c := by
  have hWc := pk.red.2.2.1.1
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hWc.is_comm.comm (⟨a, ha⟩ : ↥W) ⟨b, hb⟩)
  have hUN : ⁅W, Kh⁆ ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (Kh : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hxc : ∀ c ∈ W, x * c * x⁻¹ = c := fun c hc => by
      rw [hcomm x (pk.U_le hx) c hc, mul_inv_cancel_right]
    constructor
    · intro hc
      rw [hxc c hc.1]
      exact hc
    · intro hc
      have h1 : x * c * x⁻¹ ∈ W := hc.1
      have h2 : c ∈ W := by
        have h3 := W.mul_mem (W.mul_mem (W.inv_mem (pk.U_le hx)) h1) (pk.U_le hx)
        simpa [mul_assoc] using h3
      rw [hxc c h2] at hc
      exact hc
  have hz : z ∈ ((⁅W, Kh⁆ ⊔ (W ⊓ Subgroup.centralizer (Kh : Set G)) : Subgroup G) : Set G) := by
    rw [pk.dec]
    exact hzW
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN] at hz
  obtain ⟨u, hu', c, hc', huc⟩ := hz
  have hu : u ∈ ⁅W, Kh⁆ := hu'
  have hc : c ∈ W ⊓ Subgroup.centralizer (Kh : Set G) := hc'
  have huc' : z = u * c := huc.symm
  refine ⟨u, hu, ?_, c, hc, huc'⟩
  subst huc'
  have hcK : c ∈ Subgroup.centralizer (Kh : Set G) := (Subgroup.mem_inf.mp hc).2
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htu : t * u * t⁻¹ ∈ ⁅W, Kh⁆ :=
    (Subgroup.mem_normalizer_iff.mp (pk.T_le_normalizer ht) u).mp hu
  have htcK : t * c * t⁻¹ ∈ Subgroup.centralizer (Kh : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : t⁻¹ * k * t ∈ Kh := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (pk.T_le (T.inv_mem ht)) k).mp hk
      simpa using h1
    have h1 : (t⁻¹ * k * t) * c = c * (t⁻¹ * k * t) :=
      Subgroup.mem_centralizer_iff.mp hcK _ hk'
    calc k * (t * c * t⁻¹) = t * ((t⁻¹ * k * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * k * t)) * t⁻¹ := by rw [h1]
      _ = t * c * t⁻¹ * k := by group
  have hzt : t * (u * c) * t⁻¹ = u * c := by
    rw [Subgroup.mem_centralizer_iff.mp hzT t ht, mul_inv_cancel_right]
  have h1 : (t * u * t⁻¹) * (t * c * t⁻¹) = u * c := by
    rw [← hzt]
    group
  have h2 : u⁻¹ * (t * u * t⁻¹) ∈ ⁅W, Kh⁆ ⊓ Subgroup.centralizer (Kh : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) htu, ?_⟩
    have h3 : u⁻¹ * (t * u * t⁻¹) = c * (t * c * t⁻¹)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h1]
    rw [h3]
    exact Subgroup.mul_mem _ hcK (Subgroup.inv_mem _ htcK)
  rw [pk.inf_eq, Subgroup.mem_bot, inv_mul_eq_one] at h2
  calc t * u = t * u * t⁻¹ * t := by group
    _ = u * t := by rw [← h2]

end A7Pack

theorem Main513.exists_a7Pack {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}
    (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hc5 : Case5_512 T H X Kh₁) (hmax : quasithinIsMaximalLocal T (conjClosure Kh₁ T))
    (hZ : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hA : Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7))) :
    ∃ e : O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7),
      A7Pack T (oTwoUpper H) (conjClosure Kh₁ T)
        (conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T)) e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨e⟩ := hA
  have hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)) := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  obtain ⟨hW, hKhW, hJWc⟩ := m.commutator_thompsonJ_ne_bot h5171 hmax hs hZ
  have hKhperf : ⁅conjClosure Kh₁ T, conjClosure Kh₁ T⁆ = conjClosure Kh₁ T :=
    A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1)
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    le_normalizer_conjClosure Kh₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) := fun hle => hJWc (by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle)
  obtain ⟨hdec, hCU, hirr, hcardU⟩ := factA7FF_of h51 G (conjClosure Kh₁ T) T _ hKhperf ⟨e⟩ hTY
    hTKh (InternalSec.sqtkGroup_of_localSQTK hloc hmax.1.2.2.2) hW hKhW hJW
  have hWT : conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) ≤ T :=
    (MinParabolic.le_pCoreOf_of_isTwoReduced hW).trans (F7.isSylowTwoOf_pCoreOf_le hTY)
  have hKKh : oTwoUpper H ≤ conjClosure Kh₁ T := m.lt.le
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have h60 : Nat.card (O2Q (oTwoUpper H)) = 60 :=
    (card_of_lieModel_L2 (n := 2) (by norm_num) hc5.1).trans (by norm_num)
  have hcK : Nat.card (oTwoUpper H) = 60 * Nat.card (CFSG.pCore 2 ↥(oTwoUpper H)) := by
    rw [← h60]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(oTwoUpper H)))
  have hKb : Nat.card (oTwoUpper H) =
      Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) * Nat.card (barMap hKKh).ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (barMap hKKh).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (barMap_surjective hKKh)).toEquiv] at h1
    exact h1
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (isPGroup_ker_barMap hKKh)
  have hnum : Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) * 2 ^ b = 60 * 2 ^ a := by
    rw [← hb, ← ha, ← hcK, hKb]
  have h15 : 15 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) := by
    have h1 : 15 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) * 2 ^ b :=
      hnum ▸ Dvd.dvd.mul_right (by norm_num) _
    exact (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 15 2)).dvd_of_dvd_mul_right h1
  have h7 : ¬ 7 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) := fun hd => by
    have h1 : 7 ∣ 60 * 2 ^ a := hnum ▸ Dvd.dvd.mul_right hd _
    have h2 := (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 7 2)).dvd_of_dvd_mul_right h1
    norm_num at h2
  have h9 : ¬ 9 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) := fun hd => by
    have h1 : 9 ∣ 60 * 2 ^ a := hnum ▸ Dvd.dvd.mul_right hd _
    have h2 := (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h1
    norm_num at h2
  have h5K : 5 ∣ Nat.card (oTwoUpper H) := hcK ▸ Dvd.dvd.mul_right (by norm_num) _
  have hcR : Nat.card ((modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom) =
      Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) :=
    Subgroup.card_map_of_injective e.injective
  have hRperf : ⁅(modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom,
      (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom⁆ =
        (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom := by
    have : Group.IsPerfect ↥(oTwoUpper H) := Subgroup.isPerfect_iff.mpr hKperf
    have : Group.IsPerfect ↥(modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) :=
      Group.IsPerfect.ofSurjective (barMap_surjective hKKh)
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp this]
  have hTsyl : IsSylowTwoOf (T ⊓ conjClosure Kh₁ T) (conjClosure Kh₁ T) :=
    A4.isSylowTwoOf_inf_normal hTY le_sup_left (sup_le Subgroup.le_normalizer hTKh)
  have hS : IsSylowTwoOf ((modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)).map
      e.toMonoidHom) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_map_of_surjective
      (isSylowTwoOf_top_subgroupOf hTsyl) _ (QuotientGroup.mk'_surjective _)) _ e.surjective
  have hSR : (modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)).map e.toMonoidHom ≤
      Subgroup.normalizer (((modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) :=
    (Subgroup.map_mono (Vol2.Ch11.SecS.modO2Image_le_normalizer (inf_le_left.trans hTK))).trans
      (Subgroup.le_normalizer_map _)
  obtain ⟨g, hgR, hgS⟩ :=
    A7Std.exists_conj_eq_r0_p0 hRperf (hcR ▸ h15) (hcR ▸ h7) (hcR ▸ h9) hS hSR
  refine ⟨e.trans (MulAut.conj g), hW, hWT, hdec, hCU, hirr, hcardU, hKhperf, hs, hTKh, hTY,
    hKKh, hTK, h5K, ?_, ?_⟩
  · rw [← hgR, Subgroup.map_map]
    rfl
  · rw [← hgS, Subgroup.map_map]
    rfl

end Pack

theorem stmt5_1_13_four_CZ_of (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51)
    (hm4 : Stmt5_1_13_four_m4) (hZL : Stmt5_1_13_four_ZL) : Stmt5_1_13_four_CZ := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hm4' := hm4 G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hnat
  have hZL' := hZL G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hnat
  obtain ⟨e, pk⟩ := m.exists_a7Pack h5171 h51 hc5 hmax hZ hA
  have h16 : Nat.card ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆ = 2 ^ 4 := pk.card.resolve_right hm4'
  have hZW : quasithinOmegaOneCenter T ≤
      conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) := le_conjClosure _ _
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    fun z hz => (mem_quasithinOmegaOneCenter_iff.mp hz).2.1
  have hCK := A7ZK.inf_centralizer_eq_bot_of_card_sixteen pk.perf pk.simple pk.le_normalizer
    pk.not_le_centralizer pk.K_le pk.five (by rw [h16]; norm_num)
  obtain ⟨-, -, D₃, hD₃, hD₃3, -, -, -⟩ := ty
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hD₃3])
  have hd3 : (d : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hd, pow_orderOf_eq_one, Subgroup.coe_one]
  have hdKh : (d : G) ∈ conjClosure Kh₁ T := (hD₃ d.2).2
  have hdL : (d : G) ∈ L := (m.nota.2.1.1 (hD₃ d.2).1).1
  have hLV' : L ≤ Subgroup.normalizer (V' : Set G) := hnat.1
  have hLV'c : ¬ L ≤ Subgroup.centralizer (V' : Set G) := fun hle =>
    hV'.2.2 (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hle))
  have hdV : (d : G) ∉ Subgroup.centralizer (V' : Set G) := by
    intro hdc
    have hO := A7ZK.inf_centralizer_le_pCoreOf h.maximal.1.2.1.2.1
      (isSimpleGroup_of_lieModel_PSL2 h.lie) hLV' hLV'c ⟨hdL, hdc⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hO⟩
    have h1 : (d : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : orderOf (d : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hd] at h2
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    norm_num at h3
  have hP4 : ∀ z ∈ quasithinOmegaOneCenter T, (d : G) * z * (d : G)⁻¹ = z →
      z ∈ Subgroup.centralizer (L : Set G) := fun z hz hdz =>
    hnat.mem_centralizer_of_conj_eq hdL hd3 hdV (hZV' hz) hdz
  obtain ⟨j, hj, Ψ, hΨ0, hΨ⟩ := A7ZK.exists_four_equiv e pk.le_normalizer pk.elemAbelian
    pk.pCoreOf_le pk.irr pk.not_le_centralizer h16
  have hyT : ∀ x ∈ A7Std.p0, ∃ y : ↥(conjClosure Kh₁ T), (y : G) ∈ T ∧
      e (QuotientGroup.mk y) = x := by
    intro x hx
    rw [← pk.p0] at hx
    obtain ⟨q, ⟨y, hy, rfl⟩, hq⟩ := hx
    exact ⟨y, (Subgroup.mem_subgroupOf.mp hy).1, hq⟩
  obtain ⟨ya, hyaT, hya⟩ := hyT _ A7ZK.eval7_p0aWord_mem
  obtain ⟨yb, hybT, hyb⟩ := hyT _ A7ZK.eval7_p0bWord_mem
  have huniq : ∀ u₁ ∈ ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆, u₁ ∈ Subgroup.centralizer (T : Set G) → u₁ ≠ 1 →
      ∀ u₂ ∈ ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
        conjClosure Kh₁ T⁆, u₂ ∈ Subgroup.centralizer (T : Set G) → u₂ ≠ 1 → u₁ = u₂ := by
    intro u₁ hu₁ hu₁T hu₁1 u₂ hu₂ hu₂T hu₂1
    have hfix : ∀ (y : ↥(conjClosure Kh₁ T)), (y : G) ∈ T → ∀ (u : G) (hu : u ∈
        ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T), conjClosure Kh₁ T⁆),
        u ∈ Subgroup.centralizer (T : Set G) →
        A7ZK.conjAut pk.le_normalizer y ⟨u, hu⟩ = ⟨u, hu⟩ := by
      intro y hy u hu huT
      apply Subtype.ext
      rw [A7ZK.coe_conjAut]
      have h1 : (y : G) * u = u * y := Subgroup.mem_centralizer_iff.mp huT _ hy
      show (y : G) * u * (y : G)⁻¹ = u
      rw [h1, mul_inv_cancel_right]
    have h1 := A7ZK.eq_of_fixed_p0 hj hΨ0 hΨ hya hyb (hfix ya hyaT u₁ hu₁ hu₁T)
      (hfix yb hybT u₁ hu₁ hu₁T) (hfix ya hyaT u₂ hu₂ hu₂T) (hfix yb hybT u₂ hu₂ hu₂T)
      (fun h1 => hu₁1 (congrArg Subtype.val h1)) (fun h1 => hu₂1 (congrArg Subtype.val h1))
    exact congrArg Subtype.val h1
  have hb : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) := by
    intro z hzm
    obtain ⟨hz, hzK⟩ := Subgroup.mem_inf.mp hzm
    refine Subgroup.mem_inf.mpr ⟨hz, ?_⟩
    obtain ⟨u, hu, -, c, hc, rfl⟩ := pk.exists_mul_eq (hZW hz) (hZT hz)
    have hcK : c ∈ Subgroup.centralizer (oTwoUpper H : Set G) :=
      Subgroup.centralizer_le (fun x hx => pk.K_le hx) (Subgroup.mem_inf.mp hc).2
    have huK : u ∈ Subgroup.centralizer (oTwoUpper H : Set G) := by
      have h1 := Subgroup.mul_mem _ hzK (Subgroup.inv_mem _ hcK)
      rwa [mul_inv_cancel_right] at h1
    have hu1 : u = 1 := by
      have h1 : u ∈ ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
          conjClosure Kh₁ T⁆ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := ⟨hu, huK⟩
      rwa [hCK, Subgroup.mem_bot] at h1
    rw [hu1, one_mul]
    exact hc.2
  refine ⟨le_antisymm ?_ ?_, fun h0 => eq_bot_iff.mpr (hb.trans h0.le)⟩
  ·
    intro z hzm
    obtain ⟨hz, hzL⟩ := Subgroup.mem_inf.mp hzm
    refine Subgroup.mem_inf.mpr ⟨hz, ?_⟩
    obtain ⟨u, hu, huT, c, hc, rfl⟩ := pk.exists_mul_eq (hZW hz) (hZT hz)
    have hdc : (d : G) * c * (d : G)⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc.2 _ hdKh, mul_inv_cancel_right]
    have hdu : (d : G) * u * (d : G)⁻¹ = u := by
      have h1 : (d : G) * (u * c) * (d : G)⁻¹ = u * c := by
        rw [Subgroup.mem_centralizer_iff.mp hzL _ hdL, mul_inv_cancel_right]
      have h2 : (d : G) * (u * c) * (d : G)⁻¹ =
          ((d : G) * u * (d : G)⁻¹) * ((d : G) * c * (d : G)⁻¹) := by group
      rw [h2, hdc] at h1
      exact mul_right_cancel h1
    by_cases hu1 : u = 1
    · rw [hu1, one_mul]
      exact hc.2
    ·
      exfalso
      apply hZL'
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z' hz'
      obtain ⟨u', hu', hu'T, c', hc', rfl⟩ := pk.exists_mul_eq (hZW hz') (hZT hz')
      have hdu' : (d : G) * u' * (d : G)⁻¹ = u' := by
        by_cases hu'1 : u' = 1
        · rw [hu'1, mul_one, mul_inv_cancel]
        · rw [huniq u' hu' hu'T hu'1 u hu huT hu1]
          exact hdu
      have hdc' : (d : G) * c' * (d : G)⁻¹ = c' := by
        rw [Subgroup.mem_centralizer_iff.mp hc'.2 _ hdKh, mul_inv_cancel_right]
      refine hP4 _ hz' ?_
      calc (d : G) * (u' * c') * (d : G)⁻¹ =
            ((d : G) * u' * (d : G)⁻¹) * ((d : G) * c' * (d : G)⁻¹) := by group
        _ = u' * c' := by rw [hdu', hdc']
  ·
    intro z hzm
    obtain ⟨hz, hzK⟩ := Subgroup.mem_inf.mp hzm
    refine Subgroup.mem_inf.mpr ⟨hz, hP4 z hz ?_⟩
    rw [Subgroup.mem_centralizer_iff.mp hzK _ hdKh, mul_inv_cancel_right]

end CFSG.Quasithin.H13
