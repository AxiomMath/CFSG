module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6B
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.Quasithin.Vol2.Ch12Sec4N6L3

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

@[expose] def OddAt (c : Vec) (g : Γ) : Prop := g * g * g ∉ AS {0, c}

instance (c : Vec) (g : Γ) : Decidable (OddAt c g) := by
  unfold OddAt
  infer_instance

theorem odd_of_two : ∀ c : Vec, ∀ g : Γ, (c ≠ 0 ∧ act g c = c ∧
    (g * g) * (g * g) * ((g * g) * (g * g)) = 1 ∧ g ∉ AS {0, c}) → OddAt c g := by
  decide +kernel

@[expose] def CubeT (c : Vec) (g : Γ) : Prop :=
  ∀ v, act (g * g * g) v - v = 0 ∨ act (g * g * g) v - v = c

instance (c : Vec) (g : Γ) : Decidable (CubeT c g) := by
  unfold CubeT
  infer_instance

theorem oddAt_iff (c : Vec) (g : Γ) : OddAt c g ↔ ¬ CubeT c g := by
  unfold OddAt AS CubeT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]

theorem cubeT_conj (x g : Γ) (c : Vec) : CubeT (act x c) g ↔ CubeT c (x⁻¹ * g * x) := by
  unfold CubeT
  have e : x⁻¹ * g * x * (x⁻¹ * g * x) * (x⁻¹ * g * x) = x⁻¹ * (g * g * g) * x := by group
  have key : ∀ v, act (x⁻¹ * (g * g * g) * x) v - v =
      act x⁻¹ (act (g * g * g) (act x v) - act x v) := fun v => by
    rw [act_sub, act_mul (x⁻¹ * (g * g * g)) x, act_mul x⁻¹ (g * g * g), act_inv_act]
  rw [e]
  constructor
  · intro H v
    rw [key]
    rcases H (act x v) with h | h <;> rw [h]
    · exact Or.inl (act_zero _)
    · exact Or.inr (act_inv_act _ _)
  · intro H w
    have hw := H (act x⁻¹ w)
    rw [key, act_act_inv] at hw
    rcases hw with h | h
    · left
      rw [← act_act_inv x (act (g * g * g) w - w), h, act_zero]
    · right
      rw [← act_act_inv x (act (g * g * g) w - w), h]

@[expose] def cBase : Vec := ![1, 0, 0]

theorem cBase_ne : cBase ≠ 0 := by decide

theorem not_odd_mul_base : ∀ g : Γ, act g cBase = cBase → ¬ CubeT cBase g →
    ∀ k : Γ, act k cBase = cBase → ¬ CubeT cBase (g * k) → CubeT cBase k := by
  decide +kernel

theorem not_odd_mul : ∀ c : Vec, ∀ g h : Γ,
    (c ≠ 0 ∧ act g c = c ∧ act h c = c ∧ OddAt c g ∧ OddAt c h) → ¬ OddAt c (g⁻¹ * h) := by
  rintro c g h ⟨hc, hg, hh, og, oh⟩
  obtain ⟨x, rfl⟩ := act_trans cBase c cBase_ne hc
  have hfix : ∀ y : Γ, act y (act x cBase) = act x cBase → act (x⁻¹ * y * x) cBase = cBase :=
    fun y hy => by rw [act_mul, act_mul, hy, act_inv_act]
  have hg' := hfix g hg
  have hgi : act (x⁻¹ * g * x)⁻¹ cBase = cBase := by
    calc _ = act (x⁻¹ * g * x)⁻¹ (act (x⁻¹ * g * x) cBase) := by rw [hg']
      _ = cBase := act_inv_act _ _
  have hk : act ((x⁻¹ * g * x)⁻¹ * (x⁻¹ * h * x)) cBase = cBase := by
    rw [act_mul, hfix h hh, hgi]
  rw [oddAt_iff, cubeT_conj] at og oh ⊢
  rw [show x⁻¹ * (g⁻¹ * h) * x = (x⁻¹ * g * x)⁻¹ * (x⁻¹ * h * x) by group, not_not]
  refine not_odd_mul_base _ hg' og _ hk ?_
  rwa [mul_inv_cancel_left]

@[expose] def ProdThree (c : Vec) (g : Γ) : Prop :=
  ∃ x : Γ, act x c = c ∧ x * x * x = 1 ∧ (x⁻¹ * g) * (x⁻¹ * g) * (x⁻¹ * g) = 1

instance (c : Vec) (g : Γ) : Decidable (ProdThree c g) := by
  unfold ProdThree
  infer_instance

theorem prodThree_of_not_odd : ∀ c : Vec, ∀ g : Γ,
    (c ≠ 0 ∧ act g c = c ∧ ¬ OddAt c g) → ProdThree c g := by
  decide +kernel

section Coord

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}

@[expose] noncomputable def bv (D : L3Data H ⊤ Z) (u : W) : Vec :=
  Multiplicative.toAdd (D.β ⟨u, Subgroup.mem_top u⟩)

theorem bv_mul (D : L3Data H ⊤ Z) (u u' : W) : bv D (u * u') = bv D u + bv D u' := by
  have : (⟨u * u', Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
      ⟨u, Subgroup.mem_top _⟩ * ⟨u', Subgroup.mem_top _⟩ := rfl
  simp only [bv, this, map_mul, toAdd_mul]

theorem bv_inv (D : L3Data H ⊤ Z) (u : W) : bv D u⁻¹ = - bv D u := by
  have : (⟨u⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = (⟨u, Subgroup.mem_top _⟩)⁻¹ := rfl
  show Multiplicative.toAdd (D.β ⟨u⁻¹, Subgroup.mem_top _⟩) = _
  rw [this, map_inv, toAdd_inv]
  rfl

theorem bv_rho (D : L3Data H ⊤ Z) (γ : Γ) (u : W) : bv D (D.rho γ u) = act γ (bv D u) := by
  have h := D.β_rho γ u (Subgroup.mem_top u) (Subgroup.mem_top _)
  show Multiplicative.toAdd (D.β ⟨D.rho γ u, Subgroup.mem_top _⟩) = _
  rw [h, toAdd_ofAdd]
  rfl

theorem bv_eq_zero_iff (D : L3Data H ⊤ Z) (u : W) : bv D u = 0 ↔ u ∈ Z := by
  rw [← D.ker_β ⟨u, Subgroup.mem_top u⟩]
  constructor
  · intro h
    exact Multiplicative.toAdd.injective (by simpa [bv] using h)
  · intro h
    simp [bv, h]

end Coord

theorem conjAct_coe {G : Type*} [Group G] (V : Subgroup G)
    (g : ↥(Subgroup.normalizer (V : Set G))) (u : ↥V) :
    ((conjAct V g u : ↥V) : G) = g * u * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g u

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem autOn_sup_le : autOn (L ⊔ T) V ≤ autOn L V := by
  have h : autOn (L ⊔ T) V = autOn L V ⊔ autOn T V := by
    unfold autOn
    rw [Subgroup.subgroupOf_sup c.f.normalizes c.f.T_le, Subgroup.map_sup]
  rw [h, c.Tbar]
  exact sup_le le_rfl c.Tsyl.1

theorem LT_le_NV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le c.f.normalizes c.f.T_le

theorem CV_le_Q : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.cx.hyp
  obtain ⟨e⟩ := c.q3
  have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := (isSimpleGroup_sl_zmod_two (m := 3) le_rfl).1
    exact e.isSimpleGroup
  have hO2 : pCoreOf 2 (autOn L V) = ⊥ :=
    pCoreOf_eq_bot_of_simple c.simple (fun hp => by
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [c.card168] at hn
      have h8 : n < 8 :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hn]; norm_num)
      interval_cases n <;> norm_num at hn)
  have hker := InternalSec.isPGroup_ker_of_simple c.f.normalizes hs3 hO2 c.f.notCent
  have hp : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    intro x
    obtain ⟨k, hk⟩ := L1286.exists_two_pow_mem_of_mem_sup hyp.sylow.1 hyp.normalizes x.2.1
    have hk' : (x : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hk, Subgroup.pow_mem _ x.2.2 _⟩
    obtain ⟨m, hm⟩ := hker ⟨_, hk'⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_add, pow_mul]
    exact h1
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hp
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ h ∈ L ⊔ T, ∀ y ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G),
      h * y * h⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    intro h hh y hy
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hy.1) (Subgroup.inv_mem _ hh), ?_⟩
    have hhN := c.LT_le_NV hh
    exact (Subgroup.mem_normalizer_iff.1
      (F7.normalizer_le_normalizer_centralizer V hhN) y).1 hy.2
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] [IsMulCommutative ↥V] c in
theorem exists_of_mem_autOn {a : MulAut ↥V} (ha : a ∈ autOn L V) :
    ∃ l ∈ L, ∃ hl : l ∈ Subgroup.normalizer (V : Set G), conjAct V ⟨l, hl⟩ = a := by
  obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := Subgroup.mem_map.1 ha
  exact ⟨l, Subgroup.mem_subgroupOf.1 hlL, hlN, rfl⟩

noncomputable abbrev cv (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) : Vec :=
  bv D (⟨v, c.EV c.vE⟩ : ↥V)

theorem mem_fixV_iff {u : ↥V} :
    u ∈ fixV (autOn L V) ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [fixV_autOn_eq c.f.normalizes, Subgroup.mem_subgroupOf]

theorem bv_eq_zero_iff' (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) (u : ↥V) :
    bv D u = 0 ↔ (u : G) ∈ Subgroup.zpowers z := by
  rw [bv_eq_zero_iff, c.mem_fixV_iff, ← c.f.zV]
  exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩

theorem cv_ne (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) : c.cv D ≠ 0 := by
  intro h
  rw [cv, c.bv_eq_zero_iff'] at h
  rw [← c.f.zV] at h
  exact c.vL h.2

theorem mem_E_iff (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) (u : ↥V) :
    (u : G) ∈ E ↔ bv D u = 0 ∨ bv D u = c.cv D := by
  constructor
  · intro hu
    rcases c.mem_E hu with h | h | h | h
    · left
      rw [c.bv_eq_zero_iff', h]
      exact Subgroup.one_mem _
    · left
      rw [c.bv_eq_zero_iff', h]
      exact Subgroup.mem_zpowers z
    · right
      rw [cv]
      congr 1
      exact Subtype.ext h
    · right
      have hz : bv D (⟨z, c.f.mem_zV.1⟩ : ↥V) = 0 := by
        rw [c.bv_eq_zero_iff']
        exact Subgroup.mem_zpowers z
      have : u = (⟨v, c.EV c.vE⟩ : ↥V) * ⟨z, c.f.mem_zV.1⟩ := Subtype.ext h
      rw [this, bv_mul, hz, add_zero]
  · rintro (h | h)
    · rw [c.bv_eq_zero_iff'] at h
      exact (Subgroup.zpowers_le.2 c.facts4.1) h
    · have h1 : bv D (u * (⟨v, c.EV c.vE⟩ : ↥V)⁻¹) = 0 := by
        rw [bv_mul, bv_inv, h]
        exact add_neg_cancel _
      rw [c.bv_eq_zero_iff'] at h1
      have h2 : (u : G) = ((u * (⟨v, c.EV c.vE⟩ : ↥V)⁻¹ : ↥V) : G) * v := by
        simp
      rw [h2]
      exact E.mul_mem ((Subgroup.zpowers_le.2 c.facts4.1) h1) c.vE

theorem rho_mem_E (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {γ : Γ}
    (hγ : act γ (c.cv D) = c.cv D) {u : ↥V} (hu : (u : G) ∈ E) : ((D.rho γ u : ↥V) : G) ∈ E := by
  rw [c.mem_E_iff D] at hu ⊢
  rw [bv_rho]
  rcases hu with h | h
  · left; rw [h, act_zero]
  · right; rw [h, hγ]

theorem conj_mem_E (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) {γ : Γ} (hγx : D.rho γ = conjAct V ⟨x, hxN⟩)
    (hγ : act γ (c.cv D) = c.cv D) {e : G} (he : e ∈ E) : x * e * x⁻¹ ∈ E := by
  have h1 := c.rho_mem_E D hγ (u := ⟨e, c.EV he⟩) he
  rw [hγx, conjAct_coe] at h1
  exact h1

theorem mem_normalizer_E (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) {γ : Γ} (hγx : D.rho γ = conjAct V ⟨x, hxN⟩)
    (hγ : act γ (c.cv D) = c.cv D) : x ∈ Subgroup.normalizer (E : Set G) := by
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hxN
  have hγx' : D.rho γ⁻¹ = conjAct V ⟨x⁻¹, hxN'⟩ := by
    rw [map_inv, hγx, ← map_inv]
    rfl
  have hγ' : act γ⁻¹ (c.cv D) = c.cv D := by
    conv_lhs => rw [← hγ]
    exact act_inv_act γ _
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨c.conj_mem_E D hxN hγx hγ, fun he => ?_⟩
  have := c.conj_mem_E D hxN' hγx' hγ' he
  simpa [mul_assoc] using this

theorem act_cv_of_normalizes (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hxE : x ∈ Subgroup.normalizer (E : Set G))
    {γ : Γ} (hγx : D.rho γ = conjAct V ⟨x, hxN⟩) : act γ (c.cv D) = c.cv D := by
  have h1 : x * v * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hxE v).1 c.vE
  have h2 : ((D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) : ↥V) : G) ∈ E := by
    rw [hγx, conjAct_coe]
    exact h1
  rw [c.mem_E_iff D, bv_rho] at h2
  rcases h2 with h | h
  · exfalso
    apply c.cv_ne D
    have := congrArg (act γ⁻¹) h
    rwa [act_inv_act, act_zero] at this
  · exact h

theorem rho_v_cases (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {γ : Γ}
    (hγ : act γ (c.cv D) = c.cv D) :
    ((D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) : ↥V) : G) = v ∨
      ((D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) : ↥V) : G) = v * z := by
  have h1 : bv D (D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) * (⟨v, c.EV c.vE⟩ : ↥V)⁻¹) = 0 := by
    rw [bv_mul, bv_inv, bv_rho, hγ]
    exact add_neg_cancel _
  rw [c.bv_eq_zero_iff'] at h1
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf c.f.order h1 with h | h
  · left
    have : D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩ := by
      have h' : D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) * (⟨v, c.EV c.vE⟩ : ↥V)⁻¹ = 1 := Subtype.ext h
      exact mul_inv_eq_one.mp h'
    rw [this]
  · right
    have h' : ((D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) * (⟨v, c.EV c.vE⟩ : ↥V)⁻¹ : ↥V) : G) = z := h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    calc ((D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) : ↥V) : G) =
        ((D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) : ↥V) : G) * v⁻¹ * v := by group
      _ = z * v := by rw [h']
      _ = v * z := c.zv_comm

theorem rho_z (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) (γ : Γ) :
    D.rho γ (⟨z, c.f.mem_zV.1⟩ : ↥V) = ⟨z, c.f.mem_zV.1⟩ :=
  (c.mem_fixV_iff.2 c.f.mem_zV.2) _ (D.rho_mem γ)

theorem rho_v_of_three (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {y : Γ}
    (hy : act y (c.cv D) = c.cv D) (hy3 : y * y * y = 1) :
    D.rho y (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩ := by
  rcases c.rho_v_cases D hy with h | h
  · exact Subtype.ext h
  · exfalso
    set w : ↥V := ⟨v, c.EV c.vE⟩ with hw
    set zz : ↥V := ⟨z, c.f.mem_zV.1⟩ with hzz
    have hvz : D.rho y w = w * zz := Subtype.ext h
    have hzfix := c.rho_z D y
    have hz2 : zz * zz = 1 := Subtype.ext c.z_sq
    have h2 : D.rho (y * y) w = w := by
      rw [map_mul, MulAut.mul_apply, hvz, map_mul, hvz, hzfix, mul_assoc, hz2, mul_one]
    have h3 : D.rho (y * y * y) w = w * zz := by
      rw [map_mul, MulAut.mul_apply, hvz, map_mul, h2, c.rho_z D (y * y)]
    rw [hy3, map_one, MulAut.one_apply] at h3
    apply c.z_ne_one
    have := congrArg Subtype.val (mul_eq_left.mp h3.symm)
    exact this

theorem mem_AS_of_fix (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {γ : Γ}
    (hγ : act γ (c.cv D) = c.cv D) (h8 : (γ * γ) * (γ * γ) * ((γ * γ) * (γ * γ)) = 1)
    (hfix : D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩) : γ ∈ AS {0, c.cv D} := by
  by_contra hAS
  have hodd := odd_of_two _ γ ⟨c.cv_ne D, hγ, h8, hAS⟩
  obtain ⟨t₀, ht₀, ht₀v⟩ := c.exists_t0
  have ht₀N : t₀ ∈ Subgroup.normalizer (V : Set G) := c.f.T_le ht₀
  have ht₀L : conjAct V ⟨t₀, ht₀N⟩ ∈ autOn L V := by
    have : conjAct V ⟨t₀, ht₀N⟩ ∈ autOn T V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht₀)
    rw [c.Tbar] at this
    exact c.Tsyl.1 this
  obtain ⟨τ, hτ⟩ := D.exists_rho ht₀L
  have hτc : act τ (c.cv D) = c.cv D := c.act_cv_of_normalizes D ht₀N (c.TE ht₀) hτ
  have hτv : D.rho τ (⟨v, c.EV c.vE⟩ : ↥V) ≠ ⟨v, c.EV c.vE⟩ := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [hτ, conjAct_coe] at h1
    exact c.vz_ne_v (ht₀v.symm.trans h1)
  have hτodd : OddAt (c.cv D) τ := by
    by_contra hτo
    obtain ⟨x, hxc, hx3, hx3'⟩ := prodThree_of_not_odd _ τ ⟨c.cv_ne D, hτc, hτo⟩
    have hxc' : act (x⁻¹ * τ) (c.cv D) = c.cv D := by
      rw [act_mul, hτc]
      conv_lhs => rw [← hxc]
      exact act_inv_act x _
    apply hτv
    have : τ = x * (x⁻¹ * τ) := by group
    rw [this, map_mul, MulAut.mul_apply, c.rho_v_of_three D hxc' hx3', c.rho_v_of_three D hxc hx3]
  have heven := not_odd_mul _ τ γ ⟨c.cv_ne D, hτc, hγ, hτodd, hodd⟩
  have hτγc : act (τ⁻¹ * γ) (c.cv D) = c.cv D := by
    rw [act_mul, hγ]
    conv_lhs => rw [← hτc]
    exact act_inv_act τ _
  obtain ⟨x, hxc, hx3, hx3'⟩ := prodThree_of_not_odd _ (τ⁻¹ * γ) ⟨c.cv_ne D, hτγc, heven⟩
  have hxc' : act (x⁻¹ * (τ⁻¹ * γ)) (c.cv D) = c.cv D := by
    rw [act_mul, hτγc]
    conv_lhs => rw [← hxc]
    exact act_inv_act x _
  have hfix' : D.rho (τ⁻¹ * γ) (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩ := by
    have : τ⁻¹ * γ = x * (x⁻¹ * (τ⁻¹ * γ)) := by group
    rw [this, map_mul, MulAut.mul_apply, c.rho_v_of_three D hxc' hx3',
      c.rho_v_of_three D hxc hx3]
  apply hτv
  have : γ = τ * (τ⁻¹ * γ) := by group
  rw [this, map_mul, MulAut.mul_apply, hfix'] at hfix
  exact hfix

theorem mem_AS_of_R1 (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {r : G} (hr : r ∈ c.R1) :
    ∃ γ ∈ AS {0, c.cv D}, D.rho γ = conjAct V ⟨r, c.R1_le_NV hr⟩ := by
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := c.R1_le_NV hr
  have hrT : conjAct V ⟨r, hrN⟩ ∈ autOn T V :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hr.1)
  have hrL : conjAct V ⟨r, hrN⟩ ∈ autOn L V := by
    have h := hrT
    rw [c.Tbar] at h
    exact c.Tsyl.1 h
  obtain ⟨γ, hγ⟩ := D.exists_rho hrL
  refine ⟨γ, ?_, hγ⟩
  have hγc : act γ (c.cv D) = c.cv D := c.act_cv_of_normalizes D hrN (c.TE hr.1) hγ
  have h8 : (γ * γ) * (γ * γ) * ((γ * γ) * (γ * γ)) = 1 := by
    have hpow : (⟨_, hrT⟩ : ↥(autOn T V)) ^ 8 = 1 := by
      rw [← c.card_autOn_T]
      exact pow_card_eq_one'
    have h1 : D.rho (γ ^ 8) = 1 := by
      rw [map_pow, hγ]
      exact congrArg Subtype.val hpow
    have h2 : γ ^ 8 = 1 := D.rho_injective (h1.trans (map_one _).symm)
    have e8 : γ ^ 8 = (γ * γ) * (γ * γ) * ((γ * γ) * (γ * γ)) := by
      rw [show (8 : ℕ) = 2 + 2 + (2 + 2) from rfl, pow_add, pow_add, pow_two]
    rw [← e8, h2]
  have hfix : D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩ := by
    apply Subtype.ext
    rw [hγ, conjAct_coe]
    have := Subgroup.mem_centralizer_iff.1 hr.2 v c.vE
    simp only
    rw [← this, mul_inv_cancel_right]
  exact c.mem_AS_of_fix D hγc h8 hfix

theorem card_autOn_R1 : Nat.card (autOn c.R1 V) = 4 := by
  rw [card_autOn_eq_relIndex c.R1_le_NV]
  have hR : c.R1 ⊓ Subgroup.centralizer (V : Set G) = T ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_antisymm (inf_le_inf_right _ c.R1_le_T) (le_inf (inf_le_inf_left T ?_) inf_le_right)
    exact Subgroup.centralizer_le c.EV
  rw [hR]
  have h8 := c.card_autOn_T
  rw [card_autOn_eq_relIndex c.f.T_le] at h8
  have h2 := c.R1_facts.2
  have hle : T ⊓ Subgroup.centralizer (V : Set G) ≤ c.R1 :=
    inf_le_inf_left T (Subgroup.centralizer_le c.EV)
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle c.R1_le_T
  rw [h8, h2] at hmul
  omega

theorem autOn_R1_eq (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) :
    autOn c.R1 V = (ASsub (c.cv D) (c.cv_ne D)).map D.rho := by
  have hle : autOn c.R1 V ≤ (ASsub (c.cv D) (c.cv_ne D)).map D.rho := by
    intro a ha
    obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨γ, hγ, hγr⟩ := c.mem_AS_of_R1 D (Subgroup.mem_subgroupOf.1 hrR)
    exact ⟨γ, hγ, hγr⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [c.card_autOn_R1, Subgroup.card_map_of_injective D.rho_injective, card_ASsub]

theorem mem_R1_of_image {x : G} (hx : x ∈ L ⊔ T)
    (hxim : conjAct V ⟨x, c.LT_le_NV hx⟩ ∈ autOn c.R1 V) : x ∈ c.R1 := by
  obtain ⟨⟨r, hrN⟩, hrR, hr⟩ := Subgroup.mem_map.1 hxim
  have hrR' : r ∈ c.R1 := Subgroup.mem_subgroupOf.1 hrR
  have hrx : r⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    have hN : r⁻¹ * x ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hrN) (c.LT_le_NV hx)
    have h1 : conjAct V ⟨r⁻¹ * x, hN⟩ = 1 := by
      have : (⟨r⁻¹ * x, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          (⟨r, hrN⟩)⁻¹ * ⟨x, c.LT_le_NV hx⟩ := rfl
      rw [this, map_mul, map_inv, hr, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.1 h1
  have hrLT : r ∈ L ⊔ T := (le_sup_right : T ≤ L ⊔ T) (c.R1_le_T hrR')
  have hQ : r⁻¹ * x ∈ pCoreOf 2 (L ⊔ T) :=
    c.CV_le_Q ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hrLT) hx, hrx⟩
  have : x = r * (r⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem _ hrR' (c.Q_le_R1 hQ)

abbrev Hp (_ : Ctx T L V E z v) : Subgroup G := (L ⊔ T) ⊓ Subgroup.normalizer (E : Set G)

theorem T_le_Hp : T ≤ c.Hp := le_inf le_sup_right c.TE

theorem pCore_Hp_eq (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) : pCoreOf 2 c.Hp = c.R1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.cx.hyp
  have hR₁Hp : c.R1 ≤ c.Hp := c.R1_le_T.trans c.T_le_Hp
  have himg : ∀ (h : G) (hh : h ∈ c.Hp), ∃ η : Γ, act η (c.cv D) = c.cv D ∧
      D.rho η = conjAct V ⟨h, c.LT_le_NV hh.1⟩ := by
    intro h hh
    obtain ⟨η, hη⟩ := D.exists_rho (c.autOn_sup_le (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.2 hh.1) : conjAct V ⟨h, c.LT_le_NV hh.1⟩ ∈ autOn (L ⊔ T) V))
    exact ⟨η, c.act_cv_of_normalizes D (c.LT_le_NV hh.1) hh.2 hη, hη⟩
  refine le_antisymm ?_ ?_
  ·
    intro x hx
    have hxH : x ∈ c.Hp := CFSG.LieType.BorelTits.pCoreOf_le 2 c.Hp hx
    obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo c.sylow
    have hxT : x ∈ T := by
      have := pCoreOf_two_le_sylow c.Hp S (hS ▸ c.T_le_Hp) hx
      rwa [hS] at this
    obtain ⟨γ, hγc, hγ⟩ := himg x hxH
    apply c.mem_R1_of_image hxH.1
    rw [c.autOn_R1_eq D]
    refine ⟨γ, ?_, hγ⟩
    show γ ∈ AS {0, c.cv D}
    by_contra hAS
    have hxTim : conjAct V ⟨x, c.LT_le_NV hxH.1⟩ ∈ autOn T V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxT)
    have h8 : (γ * γ) * (γ * γ) * ((γ * γ) * (γ * γ)) = 1 := by
      have hpow : (⟨_, hxTim⟩ : ↥(autOn T V)) ^ 8 = 1 := by
        rw [← c.card_autOn_T]
        exact pow_card_eq_one'
      have h1 : D.rho (γ ^ 8) = 1 := by
        rw [map_pow, hγ]
        exact congrArg Subtype.val hpow
      have h2 : γ ^ 8 = 1 := D.rho_injective (h1.trans (map_one _).symm)
      have e8 : γ ^ 8 = (γ * γ) * (γ * γ) * ((γ * γ) * (γ * γ)) := by
        rw [show (8 : ℕ) = 2 + 2 + (2 + 2) from rfl, pow_add, pow_add, pow_two]
      rw [← e8, h2]
    obtain ⟨η, hηc, hδ3, hδ1⟩ := stab_two _ γ ⟨c.cv_ne D, hγc, hAS, h8⟩
    obtain ⟨l, hlL, hlN, hl⟩ := N1246.Ctx.exists_of_mem_autOn (D.rho_mem η)
    have hlE : l ∈ Subgroup.normalizer (E : Set G) := c.mem_normalizer_E D hlN hl.symm hηc
    have hlH : l ∈ c.Hp := ⟨(le_sup_left : L ≤ L ⊔ T) hlL, hlE⟩
    have hyO : x * (l * x⁻¹ * l⁻¹) ∈ pCoreOf 2 c.Hp := by
      refine Subgroup.mul_mem _ hx ?_
      have hn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.Hp hlH
      exact (Subgroup.mem_normalizer_iff.1 hn _).1 (Subgroup.inv_mem _ hx)
    have hyN : x * (l * x⁻¹ * l⁻¹) ∈ Subgroup.normalizer (V : Set G) :=
      c.LT_le_NV (CFSG.LieType.BorelTits.pCoreOf_le 2 c.Hp hyO).1
    have hyim : conjAct V ⟨x * (l * x⁻¹ * l⁻¹), hyN⟩ = D.rho (γ * (η * γ⁻¹ * η⁻¹)) := by
      have : (⟨x * (l * x⁻¹ * l⁻¹), hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, c.LT_le_NV hxH.1⟩ * (⟨l, hlN⟩ * (⟨x, c.LT_le_NV hxH.1⟩)⁻¹ * (⟨l, hlN⟩)⁻¹) := rfl
      rw [this]
      simp only [map_mul, map_inv, hγ, hl]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.Hp) ⟨_, hyO⟩
    have hk' : (x * (l * x⁻¹ * l⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hδ2 : D.rho (γ * (η * γ⁻¹ * η⁻¹)) ^ 2 ^ k = 1 := by
      rw [← hyim, ← map_pow]
      have : (⟨x * (l * x⁻¹ * l⁻¹), hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk')
      rw [this, map_one]
    have hδ3' : D.rho (γ * (η * γ⁻¹ * η⁻¹)) ^ 3 = 1 := by
      rw [← map_pow, pow_three, ← mul_assoc, hδ3, map_one]
    have hord : orderOf (D.rho (γ * (η * γ⁻¹ * η⁻¹))) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hδ3') (orderOf_dvd_of_pow_eq_one hδ2)
    have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hδ1 (D.rho_injective (hord.trans (map_one _).symm))
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR₁Hp ?_
      (hyp.sylow.1.to_le c.R1_le_T)
    have key : ∀ h ∈ c.Hp, ∀ r ∈ c.R1, h * r * h⁻¹ ∈ c.R1 := by
      intro h hh r hr
      obtain ⟨η, hηc, hη⟩ := himg h hh
      obtain ⟨γ, hγ, hγr⟩ := c.mem_AS_of_R1 D hr
      have hhr : h * r * h⁻¹ ∈ L ⊔ T :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hh.1 ((le_sup_right : T ≤ L ⊔ T) hr.1))
          (Subgroup.inv_mem _ hh.1)
      apply c.mem_R1_of_image hhr
      rw [c.autOn_R1_eq D]
      refine ⟨η * γ * η⁻¹, as_normal _ (c.cv_ne D) η hηc γ hγ, ?_⟩
      have : (⟨h * r * h⁻¹, c.LT_le_NV hhr⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨h, c.LT_le_NV hh.1⟩ * ⟨r, c.R1_le_NV hr⟩ * (⟨h, c.LT_le_NV hh.1⟩)⁻¹ := rfl
      rw [this]
      simp only [map_mul, map_inv, hη, hγr]
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => key h hh r hr, fun hr => ?_⟩
    have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hr
    simpa [mul_assoc] using this

theorem Hp_lt : c.Hp < L ⊔ T := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  refine lt_of_le_of_ne inf_le_left fun h => ?_
  have hLE : L ≤ Subgroup.normalizer (E : Set G) := fun l hl => by
    have : l ∈ c.Hp := h ▸ (le_sup_left : L ≤ L ⊔ T) hl
    exact this.2
  obtain ⟨γ, hγ⟩ := act_nofix (c.cv D) (c.cv_ne D)
  obtain ⟨l, hlL, hlN, hl⟩ := N1246.Ctx.exists_of_mem_autOn (D.rho_mem γ)
  exact hγ (c.act_cv_of_normalizes D hlN (hLE hlL) hl.symm)

theorem Hp_odd : ¬ 2 ∣ c.Hp.relIndex (L ⊔ T) := by
  have hT := isSylowTwoOf_of_quasithinIsSylowTwo c.sylow (le_sup_right : T ≤ L ⊔ T)
  intro h2
  apply hT.2.2
  have h1 := Subgroup.relIndex_mul_relIndex T c.Hp (L ⊔ T) c.T_le_Hp inf_le_left
  have : 2 ∣ T.relIndex (L ⊔ T) := by rw [← h1]; exact Dvd.dvd.mul_left h2 _
  exact this

end Ctx

end N1246

end CFSG.Quasithin.H13
