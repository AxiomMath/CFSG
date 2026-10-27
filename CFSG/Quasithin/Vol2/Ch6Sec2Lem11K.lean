module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem three_subgroups_mod_ch611 {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

omit [Finite G] in
theorem exists_pow_mul_ch611 {N L : Subgroup G} (hNL : L ≤ Subgroup.normalizer (N : Set G))
    {a b : G} (ha : a ∈ N) (hb : b ∈ L) (m : ℕ) : ∃ a' ∈ N, (a * b) ^ m = a' * b ^ m := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨a', ha', h1⟩ := ih
    refine ⟨a' * (b ^ m * a * (b ^ m)⁻¹), N.mul_mem ha'
      ((Subgroup.mem_normalizer_iff.mp (hNL (L.pow_mem hb m)) a).mp ha), ?_⟩
    rw [pow_succ, h1]
    group

theorem coord_unique_ch611 {K : Type} [Field K] {v₀ w₀ : Fin 2 → K} (hdet : det2 v₀ w₀ ≠ 0)
    {a b a' b' : K} (he : a • v₀ + b • w₀ = a' • v₀ + b' • w₀) : a = a' ∧ b = b' := by
  have h1 := congrArg (det2 v₀) he
  have h2 := congrArg (fun x => det2 x w₀) he
  simp only [det2_add_right_ch625, det2_add_left_ch625, det2_smul_right_ch625,
    det2_smul_left_ch625, det2_self_ch625, mul_zero, zero_add, add_zero] at h1 h2
  exact ⟨mul_right_cancel₀ hdet h2, mul_right_cancel₀ hdet h1⟩

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem mem_centralizer_V_of_comm_ch611 {u : G} (huN : u ∈ Subgroup.normalizer (V : Set G))
    (huZ : u ∈ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hcomm : ∀ ℓ ∈ L, u * ℓ * u⁻¹ * ℓ⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    u ∈ Subgroup.centralizer (V : Set G) := by
  have hK := h.card_K_ch625
  obtain ⟨v₀, hv₀⟩ := h.exists_isLine625_ZS
  obtain ⟨w₀, hw₀⟩ : ∃ w : Fin 2 → h.data.K, det2 v₀ w ≠ 0 := by
    by_cases h0 : v₀ 0 = 0
    · have h1 : v₀ 1 ≠ 0 := by
        intro h1
        apply hv₀.1
        funext i
        fin_cases i <;> simp [h0, h1]
      exact ⟨![1, 0], by simp [det2, h0, h1]⟩
    · exact ⟨![0, 1], by simp [det2, h0]⟩
  have hdet : det2 w₀ v₀ = det2 v₀ w₀ := by rw [det2_comm_ch625, neg_eq_ch625 hK]
  obtain ⟨l, hlL, hlv, hlw⟩ := h.exists_L_basis_ch625 hw₀ hdet
  have hlin := (h.isLin625_and_det_of_mem_L l hlL).1
  set uu : Subgroup.normalizer (V : Set G) := ⟨u, huN⟩ with huu
  have hfix0 : ∀ c : h.data.K, h.data.conj uu (c • v₀) = c • v₀ := fun c =>
    h.conj_fix_of_mem_centralizer huN huZ ((hv₀.2 _).mpr ⟨c, rfl⟩)
  have hcl : ∀ w, h.data.conj uu (h.data.conj l w) = h.data.conj l (h.data.conj uu w) := by
    intro w
    have hc : ((uu * l * uu⁻¹ * l⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈
        Subgroup.centralizer (V : Set G) := hcomm l hlL
    have h1 := h.data.conj_eq_of_mem_centralizer _ hc (h.data.conj l (h.data.conj uu w))
    rw [h.data.conj_mul, h.data.conj_mul, h.data.conj_mul, h.conj_inv_conj_ch625,
      h.conj_inv_conj_ch625] at h1
    exact h1
  have hfix1 : ∀ c : h.data.K, h.data.conj uu (c • w₀) = c • w₀ := by
    intro c
    rw [← hlv, ← hlin, hcl, hfix0]
  refine h.data.mem_centralizer_of_conj_eq uu fun w => ?_
  rw [eq_add_of_det2_ne_zero hw₀ w, map_add, hfix0, hfix1]

theorem commutator_eq_L_ch611 {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hXZ : X ≤ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXV : ¬ X ≤ Subgroup.centralizer (V : Set G)) : ⁅L, X⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := h.card_K_ch625
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.toHyp611Nat.two_dvd_card_K
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) h.data.K) :=
    isSimpleGroup_sl2_of_charTwo (by rw [hK])
  set N := ⁅L, X⁆ with hN
  have hNL : N ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hXL
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_left L X
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set Nρ := (N.subgroupOf L).map h.data.rho with hNρ
  have hNρn : Nρ.Normal := hNn.map _ h.data.rho_surjective
  rcases hNρn.eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply hXV
    intro x hx
    apply h.mem_centralizer_V_of_comm_ch611 (hXN hx) (hXZ hx)
    intro ℓ hℓ
    have hmem : x * ℓ * x⁻¹ * ℓ⁻¹ ∈ N := by
      rw [hN, Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator hx hℓ
      rwa [commutatorElement_def] at this
    have hL' : x * ℓ * x⁻¹ * ℓ⁻¹ ∈ L := hNL hmem
    refine (h.data.mem_ker_rho_iff ⟨_, hL'⟩).mp ?_
    have h1 : h.data.rho ⟨_, hL'⟩ ∈ Nρ := ⟨⟨_, hL'⟩, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩
    rw [hbot] at h1
    exact Subgroup.mem_bot.mp h1
  · refine h.faithful.2.1 N hNL hNn fun ℓ hℓ => ?_
    have h1 : h.data.rho ⟨ℓ, hℓ⟩ ∈ Nρ := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnρ⟩ := h1
    set o : G := (n : G)⁻¹ * ℓ with ho
    have hoL : o ∈ L := L.mul_mem (L.inv_mem n.2) hℓ
    have hoρ : h.data.rho ⟨o, hoL⟩ = 1 := by
      have e : (⟨o, hoL⟩ : ↥L) = n⁻¹ * ⟨ℓ, hℓ⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hnρ, inv_mul_cancel]
    have hoO := h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨o, hoL⟩) hoρ
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨o, hoO⟩
    have hk' : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨a', ha', h2⟩ := exists_pow_mul_ch611 hLN (Subgroup.mem_subgroupOf.mp hn) hoL (2 ^ k)
    refine ⟨k, ?_⟩
    have e : ℓ = (n : G) * o := by rw [ho]; group
    rw [e, h2, hk', mul_one]
    exact ha'

theorem commutator_pCore_le_ch611 {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hLX : ⁅L, X⁆ = L)
    (hRX : ⁅ch6Q T V, X⁆ ≤ V) : ⁅ch6Q T V, L⁆ ≤ V := by
  set R := ch6Q T V with hR
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := fun l hl => h.toHyp611.L_le_normalizer hl
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    fun r hr => h.toHyp611.T_le_normalizer hr.1
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR, h.toHyp611.centralizer_eq]
    exact le_sup_left.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hVL : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have h1 : ⁅⁅X, R⁆, L⁆ ≤ V := by
    rw [Subgroup.commutator_comm X R]
    exact (Subgroup.commutator_mono hRX le_rfl).trans hVL
  have h2 : ⁅⁅R, L⁆, X⁆ ≤ V :=
    (Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp hLR)
      le_rfl).trans hRX
  have h3 := three_subgroups_mod_ch611 hXN hRV hLV h1 h2
  rw [hLX, Subgroup.commutator_comm] at h3
  exact h3

theorem relIndex_TL_ch611 : (Subgroup.centralizer (V : Set G)).relIndex (T ⊓ L) = 4 := by
  have hker : (Subgroup.centralizer (V : Set G)).comap L.subtype = h.data.rho.ker := by
    ext ℓ
    rw [Subgroup.mem_comap, h.data.mem_ker_rho_iff]
    rfl
  have h1 := Subgroup.relIndex_comap (H := Subgroup.centralizer (V : Set G)) L.subtype
    ((T ⊓ L).subgroupOf L)
  rw [hker, Subgroup.relIndex_ker, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
  obtain ⟨v, hv, hlev⟩ := h.toHyp611Nat.exists_line
  have hc : Nat.card ↥h.toHyp611Nat.rhoTL = 4 := by
    rw [h.toHyp611Nat.rhoTL_eq_stab hv hlev, card_sl2Stab hv, h.data.card]
    norm_num
  rw [← h1]
  exact hc

theorem pCoreOf_L_le_T_ch611 : pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal L (L ⊔ T) :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        h.toHyp5_0_1.sup_le_normalizer) (IsSubnormal.refl _)
  exact (A4.pCoreOf_le_of_subnormal 2 hsub).trans
    (F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right))

theorem mem_T_of_mem_L_ch611 {x : G} (hxL : x ∈ L)
    (hxZ : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) : x ∈ T := by
  obtain ⟨v, hv, hlev⟩ := h.toHyp611Nat.exists_line
  have hstab := h.toHyp611Nat.rhoTL_eq_stab hv hlev
  have hvZ : h.vec625 v ∈ ch6ZS T L V :=
    (h.toHyp611Nat.mem_ZS_iff_line hv hlev (h.data.E.symm (Multiplicative.ofAdd v))).mpr
      ⟨1, by simp⟩
  have hfix : h.data.rho ⟨x, hxL⟩ ∈ sl2Stab v := by
    rw [mem_sl2Stab, ← h.data.conj_eq_rho]
    exact h.conj_fix_of_mem_centralizer (h.data.le_normalizer hxL) hxZ hvZ
  rw [← hstab] at hfix
  obtain ⟨t, ht, hρ⟩ := Subgroup.mem_map.mp hfix
  have hk : h.data.rho (t⁻¹ * ⟨x, hxL⟩) = 1 := by rw [map_mul, map_inv, hρ, inv_mul_cancel]
  have hO := h.pCoreOf_L_le_T_ch611 (h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one hk)
  have htT : (t : G) ∈ T := (Subgroup.mem_subgroupOf.mp ht).1
  have e : x = (t : G) * ((t⁻¹ * ⟨x, hxL⟩ : ↥L) : G) := by simp
  rw [e]
  exact T.mul_mem htT hO

theorem exists_mem_TL_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {t : G} (htT : t ∈ T)
    (htZ : t ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) :
    ∃ t' ∈ T ⊓ L, t'⁻¹ * t ∈ Subgroup.centralizer (V : Set G) := by
  set R := ch6Q T V with hRdef
  set A := T ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hAdef
  have hRA : R ≤ A := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Subgroup.mem_centralizer_iff.mp hx.2 z hz.1⟩
  have hTLA : T ⊓ L ≤ A := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm⟩
  have hAT : A ≤ T := inf_le_left
  have h8 : R.relIndex T = 8 := h.relIndex_Q_T h331 h615
  have h4 : R.relIndex (T ⊓ L) = 4 := by
    have e : R.subgroupOf (T ⊓ L) = (Subgroup.centralizer (V : Set G)).subgroupOf (T ⊓ L) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, hRdef, Subgroup.mem_inf]
      exact ⟨fun hx => hx.2, fun hx => ⟨x.2.1, hx⟩⟩
    rw [Subgroup.relIndex, e]
    exact h.relIndex_TL_ch611
  have hA1 : A.relIndex T ≠ 1 := by
    intro h1
    have hTA : T ≤ A := Subgroup.relIndex_eq_one.mp h1
    have hle : ch6ZS T L V ≤ quasithinOmegaOneCenter T := fun x hx =>
      Subgroup.subset_closure ⟨⟨h.toHyp611.le_T hx.1, Subgroup.mem_centralizer_iff.mpr
        fun y hy => (Subgroup.mem_centralizer_iff.mp (hTA hy).2 x hx).symm⟩,
        h.toHyp611.isElemAbelian.2 x hx.1⟩
    have := Subgroup.card_le_of_le hle
    rw [h.card_omega h331 h432 h512 h614 h615, h.toHyp611Nat.card_ZS] at this
    norm_num at this
  have hA0 : A.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.relIndex_mul_relIndex R A T hRA hAT
  rw [h8] at hmul
  have hRA4 : R.relIndex A ≤ 4 := by
    by_contra hcon
    have : 2 ≤ A.relIndex T := by omega
    nlinarith
  set B := (T ⊓ L) ⊔ R with hBdef
  have hRB : R ≤ B := le_sup_right
  have hBA : B ≤ A := sup_le hTLA hRA
  have hRB4 : 4 ≤ R.relIndex B := h4 ▸ Subgroup.relIndex_le_of_le_right le_sup_left
    Subgroup.index_ne_zero_of_finite
  have hmul2 := Subgroup.relIndex_mul_relIndex R B A hRB hBA
  have hBA1 : B.relIndex A = 1 := by
    have hpos : B.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra hne
    have : 2 ≤ B.relIndex A := by omega
    nlinarith
  have htB : t ∈ B := Subgroup.relIndex_eq_one.mp hBA1 ⟨htT, htZ⟩
  have hTLR : T ⊓ L ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxV := h.toHyp611.T_le_normalizer hx.1
    constructor
    · rintro ⟨hyT, hyV⟩
      refine ⟨T.mul_mem (T.mul_mem hx.1 hyT) (T.inv_mem hx.1), ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun v hv => by
        have h1 : x⁻¹ * v * x ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) v).mp hv
          simpa using this
        have h2 := Subgroup.mem_centralizer_iff.mp hyV _ h1
        calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
          _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [h2]
          _ = x * y * x⁻¹ * v := by group
    · rintro ⟨hyT, hyV⟩
      have hyT' : y ∈ T := by
        have := T.mul_mem (T.mul_mem (T.inv_mem hx.1) hyT) hx.1
        simpa [mul_assoc] using this
      refine ⟨hyT', Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
      have h2 := Subgroup.mem_centralizer_iff.mp hyV _ h1
      calc v * y = x⁻¹ * ((x * v * x⁻¹) * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * y * x⁻¹) * (x * v * x⁻¹)) * x := by rw [h2]
        _ = y * v := by group
  have hBmul : (B : Set G) = (T ⊓ L : Subgroup G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTLR
  have htB' : t ∈ ((T ⊓ L : Subgroup G) : Set G) * (R : Set G) := hBmul ▸ htB
  obtain ⟨a, ha, r, hr, hart⟩ := htB'
  refine ⟨a, ha, ?_⟩
  rw [← hart, inv_mul_cancel_left]
  exact hr.2

theorem exists_coord_ch611 {v₀ w₀ : Fin 2 → h.data.K} (hw₀ : det2 v₀ w₀ ≠ 0)
    (w : Fin 2 → h.data.K) : ∃ a b : h.data.K, w = a • v₀ + b • w₀ :=
  ⟨_, _, eq_add_of_det2_ne_zero hw₀ w⟩

theorem vec625_neg_ch611 (w : Fin 2 → h.data.K) : h.vec625 (-w) = (h.vec625 w)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← h.vec625_add, neg_add_cancel, h.vec625_zero]

theorem diag_props_ch611 {v₀ w₀ : Fin 2 → h.data.K} (hv₀ : h.IsLine625 (ch6ZS T L V) v₀)
    (hw₀ : det2 v₀ w₀ ≠ 0) {d : G} (hdL : d ∈ L) {μ : h.data.K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (hμ3 : μ ^ 3 = 1)
    (hdv : h.data.conj ⟨d, h.data.le_normalizer hdL⟩ v₀ = μ • v₀)
    (hdw : h.data.conj ⟨d, h.data.le_normalizer hdL⟩ w₀ = μ⁻¹ • w₀) :
    d ∈ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
    d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
    (∀ x ∈ V, d * x * d⁻¹ = x → x = 1) ∧
    (∀ v ∈ V, d * v * d⁻¹ * v⁻¹ ∈ ch6ZS T L V → v ∈ ch6ZS T L V) ∧
    (∀ t ∈ T ⊓ L, d * t * d⁻¹ * t⁻¹ ∈ Subgroup.centralizer (V : Set G) →
      t ∈ Subgroup.centralizer (V : Set G)) := by
  set dd : Subgroup.normalizer (V : Set G) := ⟨d, h.data.le_normalizer hdL⟩ with hdd
  have hlin := (h.isLin625_and_det_of_mem_L dd hdL).1
  have hconj : ∀ a b : h.data.K,
      h.data.conj dd (a • v₀ + b • w₀) = (a * μ) • v₀ + (b * μ⁻¹) • w₀ := by
    intro a b
    rw [map_add, hlin, hlin, hdv, hdw, smul_smul, smul_smul]
  have hμi : μ⁻¹ ≠ 1 := fun h1 => hμ1 (by rw [← inv_inv μ, h1, inv_one])
  have hμ2 : μ * μ ≠ 1 := by
    intro h2
    apply hμ1
    calc μ = μ * (μ * μ) := by rw [h2, mul_one]
      _ = μ ^ 3 := by ring
      _ = 1 := hμ3
  have hfix : ∀ c e : h.data.K, e ≠ 1 → c * e = c → c = 0 := by
    intro c e he hce
    by_contra hc
    exact he (mul_left_cancel₀ hc (hce.trans (mul_one c).symm))
  have hZS : ∀ w, h.vec625 w ∈ ch6ZS T L V ↔ ∃ c : h.data.K, w = c • v₀ := hv₀.2
  have hZSV : ch6ZS T L V ≤ V := inf_le_left
  have hN : d ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨w, rfl⟩ := h.exists_vec625_eq (hZSV hx)
      obtain ⟨c, rfl⟩ := (hZS w).mp hx
      rw [show d = (dd : G) from rfl, h.conj_vec625, hlin, hdv, smul_smul]
      exact (hZS _).mpr ⟨c * μ, rfl⟩
    · intro hx
      have hxV : x ∈ V := by
        have h1 := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem _ (h.data.le_normalizer hdL)) _).mp (hZSV hx)
        simpa [mul_assoc] using h1
      obtain ⟨w, rfl⟩ := h.exists_vec625_eq hxV
      obtain ⟨a, b, rfl⟩ := h.exists_coord_ch611 hw₀ w
      rw [show d = (dd : G) from rfl, h.conj_vec625, hconj] at hx
      obtain ⟨c, hc⟩ := (hZS _).mp hx
      have hc' : (a * μ) • v₀ + (b * μ⁻¹) • w₀ = c • v₀ + (0 : h.data.K) • w₀ := by
        rw [hc, zero_smul, add_zero]
      have hb := (coord_unique_ch611 hw₀ hc').2
      have hb0 : b = 0 := by
        rcases mul_eq_zero.mp hb with hb | hb
        · exact hb
        · exact absurd hb (inv_ne_zero hμ0)
      exact (hZS _).mpr ⟨a, by rw [hb0, zero_smul, add_zero]⟩
  refine ⟨hN, ?_, ?_, ?_, ?_⟩
  ·
    have hNC := F7.normalizer_le_normalizer_centralizer (ch6ZS T L V) hN
    have hTLC : ∀ t ∈ T ⊓ L, t ∈ Subgroup.centralizer (ch6ZS T L V : Set G) :=
      fun t ht => Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_iff.mp hz.2 t ht).symm
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have hL : d * t * d⁻¹ ∈ L := L.mul_mem (L.mul_mem hdL ht.2) (L.inv_mem hdL)
      exact ⟨h.mem_T_of_mem_L_ch611 hL ((Subgroup.mem_normalizer_iff.mp hNC t).mp (hTLC t ht)),
        hL⟩
    · intro ht
      have hL : t ∈ L := by
        have h1 := L.mul_mem (L.mul_mem (L.inv_mem hdL) ht.2) hdL
        simpa [mul_assoc] using h1
      exact ⟨h.mem_T_of_mem_L_ch611 hL ((Subgroup.mem_normalizer_iff.mp hNC t).mpr (hTLC _ ht)),
        hL⟩
  ·
    intro x hx hdx
    obtain ⟨w, rfl⟩ := h.exists_vec625_eq hx
    obtain ⟨a, b, rfl⟩ := h.exists_coord_ch611 hw₀ w
    rw [show d = (dd : G) from rfl, h.conj_vec625] at hdx
    have h1 := h.vec625_injective hdx
    rw [hconj] at h1
    obtain ⟨ha, hb⟩ := coord_unique_ch611 hw₀ h1
    rw [hfix a μ hμ1 ha, hfix b μ⁻¹ hμi hb, zero_smul, zero_smul, add_zero, h.vec625_zero]
  ·
    intro v hv hdv'
    obtain ⟨w, rfl⟩ := h.exists_vec625_eq hv
    obtain ⟨a, b, rfl⟩ := h.exists_coord_ch611 hw₀ w
    rw [show d = (dd : G) from rfl, h.conj_vec625, ← h.vec625_neg_ch611, ← h.vec625_add,
      hconj] at hdv'
    obtain ⟨c, hc⟩ := (hZS _).mp hdv'
    have hc' : (a * μ - a) • v₀ + (b * μ⁻¹ - b) • w₀ = c • v₀ + (0 : h.data.K) • w₀ := by
      rw [← hc, zero_smul, add_zero, sub_smul, sub_smul, neg_add]
      abel
    have hb := (coord_unique_ch611 hw₀ hc').2
    have hb0 : b = 0 := hfix b μ⁻¹ hμi (sub_eq_zero.mp hb)
    exact (hZS _).mpr ⟨a, by rw [hb0, zero_smul, add_zero]⟩
  ·
    intro t ht hdt
    set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.data.le_normalizer ht.2⟩ with htt
    obtain ⟨hlint, hdett⟩ := h.isLin625_and_det_of_mem_L tt ht.2
    have htZ : t ∈ Subgroup.centralizer (ch6ZS T L V : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => (Subgroup.mem_centralizer_iff.mp hz.2 t ht).symm
    have htv : h.data.conj tt v₀ = v₀ :=
      h.conj_fix_of_mem_centralizer tt.2 htZ ((hZS v₀).mpr ⟨1, (one_smul _ _).symm⟩)
    obtain ⟨a, b, hab⟩ := h.exists_coord_ch611 hw₀ (h.data.conj tt w₀)
    have hb1 : b = 1 := by
      have h1 := h.det2_conj_lin_ch625 hlint v₀ w₀
      rw [hdett, mul_one, htv, hab, det2_add_right_ch625, det2_smul_right_ch625,
        det2_smul_right_ch625, det2_self_ch625, mul_zero, zero_add] at h1
      exact mul_right_cancel₀ hw₀ (h1.trans (one_mul _).symm)
    have hdi : h.data.conj dd⁻¹ w₀ = μ • w₀ := by
      have h1 : h.data.conj dd (μ • w₀) = w₀ := by
        rw [hlin, hdw, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      calc h.data.conj dd⁻¹ w₀ = h.data.conj dd⁻¹ (h.data.conj dd (μ • w₀)) := by rw [h1]
        _ = μ • w₀ := h.conj_inv_conj_ch625 dd (μ • w₀)
    have hdtd : h.data.conj (dd * tt * dd⁻¹) w₀ = (μ * a * μ) • v₀ + (μ * μ⁻¹) • w₀ := by
      rw [h.data.conj_mul, h.data.conj_mul, hdi, hlint, hab, hb1, smul_add, smul_smul,
        one_smul, ← hconj]
    have hcomm : h.data.conj (dd * tt * dd⁻¹) w₀ = h.data.conj tt w₀ := by
      have hc : ((dd * tt * dd⁻¹ * tt⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈
          Subgroup.centralizer (V : Set G) := hdt
      have h1 := h.data.conj_eq_of_mem_centralizer _ hc (h.data.conj tt w₀)
      rw [h.data.conj_mul, h.conj_inv_conj_ch625] at h1
      exact h1
    rw [hdtd, hab, hb1] at hcomm
    have ha := (coord_unique_ch611 hw₀ hcomm).1
    have ha0 : a = 0 := by
      apply hfix a (μ * μ) hμ2
      calc a * (μ * μ) = μ * a * μ := by ring
        _ = a := ha
    apply h.data.mem_centralizer_of_conj_eq tt
    intro w
    obtain ⟨p, q, rfl⟩ := h.exists_coord_ch611 hw₀ w
    rw [map_add, hlint, hlint, htv, hab, ha0, hb1, zero_smul, zero_add, one_smul]

theorem exists_diag_ch611 : ∃ d ∈ L, d ^ 3 = 1 ∧
    d ∈ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
    d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
    (∀ x ∈ V, d * x * d⁻¹ = x → x = 1) ∧
    (∀ v ∈ V, d * v * d⁻¹ * v⁻¹ ∈ ch6ZS T L V → v ∈ ch6ZS T L V) ∧
    (∀ t ∈ T ⊓ L, d * t * d⁻¹ * t⁻¹ ∈ Subgroup.centralizer (V : Set G) →
      t ∈ Subgroup.centralizer (V : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := h.card_K_ch625
  obtain ⟨v₀, hv₀⟩ := h.exists_isLine625_ZS
  obtain ⟨w₀, hw₀⟩ : ∃ w : Fin 2 → h.data.K, det2 v₀ w ≠ 0 := by
    by_cases h0 : v₀ 0 = 0
    · have h1 : v₀ 1 ≠ 0 := by
        intro h1
        apply hv₀.1
        funext i
        fin_cases i <;> simp [h0, h1]
      exact ⟨![1, 0], by simp [det2, h0, h1]⟩
    · exact ⟨![0, 1], by simp [det2, h0]⟩
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 hK
  have hω3 : ω ^ 3 = 1 := pow_three_ch625 hK hω0
  have hdet : det2 (ω • v₀) (ω⁻¹ • w₀) = det2 v₀ w₀ := by
    rw [det2_smul_left_ch625, det2_smul_right_ch625, ← mul_assoc, mul_inv_cancel₀ hω0, one_mul]
  obtain ⟨l, hlL, hlv, hlw⟩ := h.exists_L_basis_ch625 hw₀ hdet
  have hpow : ∀ k : ℕ, h.data.conj (l ^ k) v₀ = (ω ^ k) • v₀ ∧
      h.data.conj (l ^ k) w₀ = (ω⁻¹ ^ k) • w₀ := by
    intro k
    induction k with
    | zero => simp [h.conj_one_ch625]
    | succ k ih =>
      have hlk : ((l ^ k : Subgroup.normalizer (V : Set G)) : G) ∈ L := by
        rw [Subgroup.coe_pow]; exact L.pow_mem hlL k
      have hlin := (h.isLin625_and_det_of_mem_L _ hlk).1
      have e : l ^ (k + 1) = l ^ k * l := pow_succ l k
      rw [e, h.data.conj_mul, h.data.conj_mul, hlv, hlw, hlin, hlin, ih.1, ih.2,
        smul_smul, smul_smul, ← pow_succ', ← pow_succ']
      exact ⟨rfl, rfl⟩
  have hl3L : ((l ^ 3 : Subgroup.normalizer (V : Set G)) : G) ∈ L := by
    rw [Subgroup.coe_pow]; exact L.pow_mem hlL 3
  have hl3C : ((l ^ 3 : Subgroup.normalizer (V : Set G)) : G) ∈
      Subgroup.centralizer (V : Set G) := by
    apply h.data.mem_centralizer_of_conj_eq
    intro w
    obtain ⟨a, b, rfl⟩ := h.exists_coord_ch611 hw₀ w
    have hlin := (h.isLin625_and_det_of_mem_L _ hl3L).1
    rw [map_add, hlin, hlin, (hpow 3).1, (hpow 3).2, hω3, inv_pow, hω3, inv_one, one_smul,
      one_smul]
  have hρ : h.data.rho ⟨_, hl3L⟩ = 1 := by
    rw [← MonoidHom.mem_ker, h.data.mem_ker_rho_iff]
    exact hl3C
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one hρ⟩
  have hk' : ((l : G) ^ 3) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa [Subgroup.coe_pow] using this
  set d : G := (l : G) ^ 2 ^ k with hd
  have hdL : d ∈ L := L.pow_mem hlL _
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← pow_mul, mul_comm, pow_mul, hk']
  set μ : h.data.K := ω ^ 2 ^ k with hμ
  have hμ0 : μ ≠ 0 := pow_ne_zero _ hω0
  have hμ1 : μ ≠ 1 := by
    intro h1
    have h2 : orderOf ω ∣ 3 := orderOf_dvd_of_pow_eq_one hω3
    have h3 : orderOf ω ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h4 : orderOf ω = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
    exact hω1 (orderOf_eq_one_iff.mp h4)
  have hμ3 : μ ^ 3 = 1 := pow_three_ch625 hK hμ0
  have hdd : (⟨d, h.data.le_normalizer hdL⟩ : Subgroup.normalizer (V : Set G)) = l ^ 2 ^ k :=
    Subtype.ext (by rw [Subgroup.coe_pow])
  have hdv : h.data.conj ⟨d, h.data.le_normalizer hdL⟩ v₀ = μ • v₀ := by
    rw [hdd, (hpow _).1]
  have hdw : h.data.conj ⟨d, h.data.le_normalizer hdL⟩ w₀ = μ⁻¹ • w₀ := by
    rw [hdd, (hpow _).2, hμ, inv_pow]
  exact ⟨d, hdL, hd3, h.diag_props_ch611 hv₀ hw₀ hdL hμ0 hμ1 hμ3 hdv hdw⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
