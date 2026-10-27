module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Cfg

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

omit [Finite G] in
theorem exists_centralizer_conjSub_eq {X : Subgroup G}
    (htr : ∀ a ∈ X, ∀ b ∈ X, a ≠ 1 → b ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (X : Set G), m * a * m⁻¹ = b)
    {z g : G} (hz : z ∈ X) (hz1 : z ≠ 1) (hzg : z ∈ conjSub g X) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub g X = conjSub c X := by
  have h1 : g⁻¹ * z * g ∈ X := mem_conjSub.mp hzg
  have h2 : g⁻¹ * z * g ≠ 1 := by
    intro h0
    apply hz1
    have := congrArg (fun x => g * x * g⁻¹) h0
    simpa [mul_assoc] using this
  obtain ⟨m, hm, hmz⟩ := htr z hz _ h1 hz1 h2
  refine ⟨g * m, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have : m * z = g⁻¹ * z * g * m := by rw [← hmz]; group
    calc g * m * z = g * (m * z) := by group
      _ = g * (g⁻¹ * z * g * m) := by rw [this]
      _ = z * (g * m) := by group
  · rw [conjSub_mul, conjSub_eq_of_mem_normalizer' hm]

omit [Finite G] in
theorem inv_mul_mem_of_relIndex_two {A B : Subgroup G} (hA : A.relIndex B = 2) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) (hxA : x ∉ A) (hyA : y ∉ A) : x⁻¹ * y ∈ A := by
  have hidx : (A.subgroupOf B).index = 2 := hA
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : ↥B)⁻¹)
    (b := ⟨y, hy⟩)).mpr
  have hx' : (⟨x, hx⟩ : ↥B)⁻¹ ∉ A.subgroupOf B := by
    rw [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
    exact hxA
  have hy' : (⟨y, hy⟩ : ↥B) ∉ A.subgroupOf B := by
    rw [Subgroup.mem_subgroupOf]
    exact hyA
  have := key (iff_of_false hx' hy')
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem mem_pCoreOf_of_commutator_mem {X : Subgroup G} (hX : CharTwo X) {z : G}
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) (hz2 : z ^ 2 = 1) {x : G} (hx : x ∈ X)
    (hcomm : ∀ q ∈ pCoreOf 2 X, x * q * x⁻¹ * q⁻¹ ∈ Subgroup.zpowers z) :
    x ∈ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : ∀ a ∈ Subgroup.zpowers z, ∀ w ∈ X, w * a = a * w := by
    intro a ha w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hwz : w * z = z * w := (Subgroup.mem_centralizer_singleton_iff.mp (hXz hw))
    exact ((Commute.zpow_right (show Commute w z from hwz) k)).eq
  have hzsq : ∀ a ∈ Subgroup.zpowers z, a * a = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hzz : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz2]
    rw [← zpow_add, ← two_mul, zpow_mul, hzz, one_zpow]
  have hQX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  let C : Subgroup G :=
    { carrier := {w | w ∈ X ∧ ∀ q ∈ pCoreOf 2 X, w * q * w⁻¹ * q⁻¹ ∈ Subgroup.zpowers z}
      one_mem' := ⟨X.one_mem, fun q _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
        refine ⟨X.mul_mem ha hb, fun q hq => ?_⟩
        have hbq : b * q * b⁻¹ ∈ pCoreOf 2 X :=
          (Subgroup.mem_normalizer_iff.mp (hXN hb) q).mp hq
        have e1 := hca _ hbq
        have e2 := hcb q hq
        have : a * b * q * (a * b)⁻¹ * q⁻¹ =
            (a * (b * q * b⁻¹) * a⁻¹ * (b * q * b⁻¹)⁻¹) * (b * q * b⁻¹ * q⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ e1 e2
      inv_mem' := by
        rintro a ⟨ha, hca⟩
        refine ⟨X.inv_mem ha, fun q hq => ?_⟩
        have e := hca q hq
        have h2 : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a := by group
        rw [h2]
        have hcm := hzc _ (Subgroup.inv_mem _ e) a ha
        rw [mul_assoc, ← hcm, ← mul_assoc, inv_mul_cancel, one_mul]
        exact Subgroup.inv_mem _ e }
  have hCX : C ≤ X := fun w hw => hw.1
  have hCN : X ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨hw, hcw⟩
      refine ⟨X.mul_mem (X.mul_mem hg hw) (X.inv_mem hg), fun q hq => ?_⟩
      have hq' : g⁻¹ * q * g ∈ pCoreOf 2 X := by
        have := (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem hg)) q).mp hq
        simpa using this
      have e := hcw _ hq'
      have h1 : g * w * g⁻¹ * q * (g * w * g⁻¹)⁻¹ * q⁻¹ =
          g * (w * (g⁻¹ * q * g) * w⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
      rw [h1, hzc _ e g hg, mul_assoc, mul_inv_cancel, mul_one]
      exact e
    · rintro ⟨hw, hcw⟩
      have hw' : w ∈ X := by
        have := X.mul_mem (X.mul_mem (X.inv_mem hg) hw) hg
        simpa [mul_assoc] using this
      refine ⟨hw', fun q hq => ?_⟩
      have hq' : g * q * g⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp (hXN hg) q).mp hq
      have e := hcw _ hq'
      have h1 : w * q * w⁻¹ * q⁻¹ =
          g⁻¹ * (g * w * g⁻¹ * (g * q * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * q * g⁻¹)⁻¹) * g := by
        group
      rw [h1, hzc _ e g⁻¹ (X.inv_mem hg), mul_assoc, inv_mul_cancel, mul_one]
      exact e
  have hC2 : IsPGroup 2 C := by
    refine isPGroup_of_forall_pow fun w hw => ?_
    have hw2 : w ^ 2 ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine ⟨X.pow_mem hw.1 2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have hwq : w * q * w⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp (hXN hw.1) q).mp hq
      obtain ⟨a, ha, hqa⟩ : ∃ a ∈ Subgroup.zpowers z, w * q * w⁻¹ = a * q :=
        ⟨_, hw.2 q hq, by group⟩
      obtain ⟨b, hb, hqb⟩ : ∃ b ∈ Subgroup.zpowers z, w * (w * q * w⁻¹) * w⁻¹ =
          b * (w * q * w⁻¹) := ⟨_, hw.2 _ hwq, by group⟩
      have hab : b = a := by
        have h3 : w * (w * q * w⁻¹) * w⁻¹ = a * (w * q * w⁻¹) := by
          calc w * (w * q * w⁻¹) * w⁻¹ = w * (a * q) * w⁻¹ := by rw [hqa]
            _ = (w * a) * q * w⁻¹ := by group
            _ = (a * w) * q * w⁻¹ := by rw [hzc a ha w hw.1]
            _ = a * (w * q * w⁻¹) := by group
        rw [h3] at hqb
        exact (mul_right_cancel hqb).symm
      have h4 : w ^ 2 * q = q * w ^ 2 := by
        have h5 : w * (w * q * w⁻¹) * w⁻¹ = q := by
          rw [hqb, hab, hqa, ← mul_assoc, hzsq a ha, one_mul]
        rw [pow_two]
        calc w * w * q = w * (w * q * w⁻¹) * w⁻¹ * (w * w) := by group
          _ = q * (w * w) := by rw [h5]
      exact h4.symm
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨w ^ 2, hX hw2⟩
    refine ⟨k + 1, ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [pow_succ', pow_mul]
    exact this
  have hCle : C ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCX hCN hC2
  exact hCle ⟨hx, hcomm⟩

omit [Finite G] in
theorem centralizer_zpowers_eq (z : G) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

namespace Hyp611Nat

theorem exists_conj_eq_ZS (h : Hyp611Nat G T M L V n) {z z' : G} (hz : z ∈ ch6ZS T L V)
    (hz' : z' ∈ ch6ZS T L V) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) :
    ∃ g ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G), g * z * g⁻¹ = z' := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  have hzV : z ∈ V := hz.1
  have hzV' : z' ∈ V := hz'.1
  obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hzV⟩).mp hz
  obtain ⟨c', hc'⟩ := (h.mem_ZS_iff_line hv hle ⟨z', hzV'⟩).mp hz'
  have hne : ∀ {x : G} (hx : x ∈ V) {a : h.data.K},
      Multiplicative.toAdd (h.data.E ⟨x, hx⟩) = a • v → x ≠ 1 → a ≠ 0 := by
    intro x hx a ha hx1 ha0
    apply hx1
    rw [ha0, zero_smul] at ha
    have h1 : h.data.E ⟨x, hx⟩ = 1 := ha
    have := congrArg Subtype.val ((MulEquiv.map_eq_one_iff h.data.E).mp h1)
    simpa using this
  have hc0 := hne hzV hc hz1
  have hc0' := hne hzV' hc' hz1'
  obtain ⟨u, -, htor⟩ := exists_torus h.two_dvd_card_K hv
  obtain ⟨D, -, hDv, -⟩ := htor (c' / c) (div_ne_zero hc0' hc0)
  obtain ⟨g, hg⟩ := h.data.rho_surjective D
  have hgN := h.mem_normalizer_ZS_of_rho hv hle g (div_ne_zero hc0' hc0) (by rw [hg]; exact hDv)
  refine ⟨g, ⟨g.2, hgN⟩, ?_⟩
  have hcc : c * (c' / c) = c' := by field_simp
  have hconj : Multiplicative.toAdd (h.data.E
      (conjAct V (⟨g, h.data.le_normalizer g.2⟩ : Subgroup.normalizer (V : Set G)) ⟨z, hzV⟩)) =
      Multiplicative.toAdd (h.data.E ⟨z', hzV'⟩) := by
    rw [← h.data.conj_apply, h.data.conj_eq_rho g, hg, hc, Matrix.mulVec_smul, hDv, smul_smul,
      hcc, hc']
  have h1 := h.data.E.injective (Multiplicative.toAdd.injective hconj)
  have h2 := congrArg Subtype.val h1
  rw [conjAct_apply_coe] at h2
  exact h2

theorem exists_conjSub_T_le_centralizer (h : Hyp611Nat G T M L V n) {z : G}
    (hz : z ∈ ch6ZS T L V) (hz1 : z ≠ 1) :
    ∃ d ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G),
      conjSub d⁻¹ T ≤ Subgroup.centralizer ({z} : Set G) := by
  have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
    B2F.isElemAbelian_mono inf_le_left h.toHyp611.isElemAbelian
  have hZT : ch6ZS T L V ≤ T := inf_le_left.trans h.toHyp611.le_T
  have hne := inf_omegaOneCenter_ne_bot h.sylow.1 hZel hZT h.T_le_normalizer_ZS h.ZS_ne_bot
  obtain ⟨⟨z₀, hz₀Z, hz₀Ω⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hz₀1' : z₀ ≠ 1 := fun h0 => hz₀1 (Subtype.ext h0)
  have hz₀C : z₀ ∈ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr (fun x hx => hx.1.2) hz₀Ω
  obtain ⟨g, hg, hgz⟩ := h.exists_conj_eq_ZS hz hz₀Z hz1 hz₀1'
  refine ⟨g, hg, fun x hx => ?_⟩
  have hx' : g * x * g⁻¹ ∈ T := by
    have := mem_conjSub.mp hx
    simpa using this
  have hcomm : g * x * g⁻¹ * z₀ = z₀ * (g * x * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hz₀C _ hx'
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← hgz] at hcomm
  have : g * (x * z) * g⁻¹ = g * (z * x) * g⁻¹ := by
    calc g * (x * z) * g⁻¹ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := hcomm
      _ = g * (z * x) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel this)

theorem transitive_V (h : Hyp611Nat G T M L V n) :
    ∀ a ∈ V, ∀ b ∈ V, a ≠ 1 → b ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (V : Set G), m * a * m⁻¹ = b := by
  intro a ha b hb ha1 hb1
  obtain ⟨g, hg, hgab⟩ := h.natural.exists_conj_eq ha hb ha1 hb1
  exact ⟨g, h.toHyp611.L_le_normalizer hg, hgab⟩

theorem transitive_ZS (h : Hyp611Nat G T M L V n) :
    ∀ a ∈ ch6ZS T L V, ∀ b ∈ ch6ZS T L V, a ≠ 1 → b ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (ch6ZS T L V : Set G), m * a * m⁻¹ = b := by
  intro a ha b hb ha1 hb1
  obtain ⟨g, hg, hgab⟩ := h.exists_conj_eq_ZS ha hb ha1 hb1
  exact ⟨g, hg.2, hgab⟩

end Hyp611Nat

namespace Cfg619

omit [Finite G] in
theorem ZS_le_B (c : Cfg619 T L V H n y) :
    ch6ZS T L V ≤ conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G) := by
  refine le_inf ((inf_le_left : ch6ZS T L V ≤ V).trans (le_conjClosure V H)) ?_
  have : ch6ZS T L V ≤ Subgroup.centralizer (conjSub y V : Set G) :=
    Subgroup.le_centralizer_iff.mp c.le_centralizer
  exact this.trans (Subgroup.centralizer_le_normalizer _)

variable (h : Hyp6116 G T M L V n) (c : Cfg619 T L V H n y)
include h c

theorem commutator_VB_F :
    ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
        conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ =
      ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) ∧
    Nat.card ↥(ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := c.n_eq
  have hZcard : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS, hn]; norm_num
  have hVcard : Nat.card V = 16 := by
    rw [h.toHyp611Nat.natural.card_eq, hn]; norm_num
  have hZE : Nat.card (conjSub y (ch6ZS T L V)) = 4 := by rw [card_conjSub', hZcard]
  have hZVB : ch6ZS T L V ≤ V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)) :=
    le_inf inf_le_left c.ZS_le_B
  have h1 : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ ≤ ch6ZS T L V := by
    rw [← c.commutator_VF]
    exact Subgroup.commutator_mono inf_le_left le_rfl
  have h2 : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ ≤ conjSub y (ch6ZS T L V) := by
    rw [← c.commutator_EB, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono inf_le_left inf_le_right
  have hlt : Nat.card ↥(ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) ≤ 2 := by
    have hdvd : Nat.card ↥(ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) ∣ 4 :=
      hZcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) ≠ 4 := by
      intro h4
      apply c.ne
      have h5 := Subgroup.eq_of_le_of_card_ge
        (inf_le_left : ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) ≤ ch6ZS T L V) (by rw [h4, hZcard])
      have hle : ch6ZS T L V ≤ conjSub y (ch6ZS T L V) := fun x hx => (h5.ge hx).2
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, hZE])).symm
    have h4 : Nat.card ↥(ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hk : Nat.card ↥(ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) <;> simp_all
  have hFV : ¬ conjSub y V ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.centralizer (V : Set G) := by
    intro hle
    apply h.toHyp611Nat.ZS_ne_bot
    rw [← c.commutator_VF]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
  obtain ⟨f, hfF, hfV⟩ := Set.not_subset.mp hFV
  have hfE : f ∈ conjSub y V := hfF.1
  have hf2 : f ^ 2 ^ 1 = 1 := by
    have h3 := h.toHyp611.isElemAbelian.2 _ (mem_conjSub.mp hfE)
    have e : (y⁻¹ * f * y) ^ 2 = y⁻¹ * f ^ 2 * y := by rw [pow_two, pow_two]; group
    rw [e] at h3
    have h4 : f ^ 2 = y * (y⁻¹ * f ^ 2 * y) * y⁻¹ := by group
    rw [pow_one, h4, h3]
    group
  have hfst := h.toHyp611Nat.commutator_of_two (b := f)
    ⟨hfF.2, c.le_centralizer hfE⟩ ⟨1, hf2⟩ hfV
  have hVB2 : (V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G))).relIndex V =
      2 := by
    have hle2 : (V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G))).relIndex V ≤
        2 := by
      rw [Subgroup.inf_relIndex_left, ← c.relIndex_B]
      exact Subgroup.relIndex_le_of_le_right (le_conjClosure V H) (by rw [c.relIndex_B]; norm_num)
    have hne1 : (V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G))).relIndex V ≠
        1 := by
      intro h1'
      have hVVB := Subgroup.relIndex_eq_one.mp h1'
      have h3 : ch6ZS T L V ≤ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) :=
        le_inf le_rfl (c.commutator_VF.ge.trans ((Subgroup.commutator_mono hVVB le_rfl).trans h2))
      have := Subgroup.card_le_of_le h3
      omega
    have h0 := relIndex_ne_zero' V
      (V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)))
    omega
  have hcardVB : Nat.card ↥(V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G))) =
      8 := by
    have := card_mul_relIndex_of_le
      (inf_le_left : V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)) ≤ V)
    rw [hVB2, hVcard] at this
    omega
  have hcf := hfst.2 _ hZVB inf_le_left
  rw [hcardVB, hZcard] at hcf
  have hcf2 : Nat.card ↥⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      Subgroup.zpowers f⁆ = 2 := by omega
  have hle : ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
      Subgroup.zpowers f⁆ ≤ ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
        conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hfF)
  have hle' := le_inf h1 h2
  have heq := Subgroup.eq_of_le_of_card_ge (hle.trans hle') (by rw [hcf2]; exact hlt)
  refine ⟨le_antisymm hle' (heq ▸ hle), ?_⟩
  rw [← heq, hcf2]

theorem exists_z :
    ∃ z : G, z ≠ 1 ∧ z ^ 2 = 1 ∧
      Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) ∧
      ⁅V ⊓ (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)),
        conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = Subgroup.zpowers z := by
  obtain ⟨hcomm, hcard⟩ := c.commutator_VB_F h
  have hne : ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hz1' : z ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hz2 : z ^ 2 = 1 := h.toHyp611.isElemAbelian.2 z hzmem.1.1
  have hzle : Subgroup.zpowers z ≤ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) :=
    Subgroup.zpowers_le.mpr hzmem
  have hord : 2 ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers]
    have h0 : orderOf z ≠ 0 := (isOfFinOrder_of_finite z).orderOf_pos.ne'
    have h1 : orderOf z ≠ 1 := fun h1 => hz1' (orderOf_eq_one_iff.mp h1)
    omega
  have heq : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hcard]; exact hord)
  exact ⟨z, hz1', hz2, heq, hcomm.trans heq.symm⟩

end Cfg619
end CFSG.Quasithin.H13
