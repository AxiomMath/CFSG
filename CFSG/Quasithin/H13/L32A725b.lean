module

public import CFSG.Quasithin.H13.L32A725a
public import CFSG.Quasithin.H13.L32AS4d

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

@[expose] def secFix {W₁ W₂ : Subgroup G} (hW : IsElemSection W₁ W₂) (X : Subgroup G) :
    Subgroup G where
  carrier := {w | w ∈ W₁ ∧ ∀ x ∈ X, x * w * x⁻¹ * w⁻¹ ∈ W₂}
  one_mem' := ⟨one_mem _, fun _ _ => by simp⟩
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, fun x hx => ?_⟩
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact mul_mem (ha.2 x hx) (hW.conj_mem ha.1 (hb.2 x hx))
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, fun x hx => ?_⟩
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact hW.conj_mem (inv_mem ha.1) (inv_mem (ha.2 x hx))

omit [Finite G] in
theorem le_secFix {W₁ W₂ : Subgroup G} (hW : IsElemSection W₁ W₂) (X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (W₂ : Set G)) : W₂ ≤ secFix hW X := fun w hw =>
  ⟨hW.le hw, fun _ hx =>
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hX hx) w).mp hw) (inv_mem hw)⟩

omit [Finite G] in
theorem le_normalizer_secFix {W₁ W₂ : Subgroup G} (hW : IsElemSection W₁ W₂) (X : Subgroup G)
    {K : Subgroup G}
    (h₁ : K ≤ Subgroup.normalizer (W₁ : Set G)) (h₂ : K ≤ Subgroup.normalizer (W₂ : Set G))
    (hK : K ≤ Subgroup.normalizer (X : Set G)) :
    K ≤ Subgroup.normalizer ((secFix hW X : Subgroup G) : Set G) := fun y hy =>
  mem_normalizer_of_forall_conj (Q := K) (fun k hk w hw => by
    refine ⟨(Subgroup.mem_normalizer_iff.mp (h₁ hk) w).mp hw.1, fun x hx => ?_⟩
    have hx' : k⁻¹ * x * k ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hK hk)) x).mp hx
      simpa using this
    have e : x * (k * w * k⁻¹) * x⁻¹ * (k * w * k⁻¹)⁻¹ =
        k * ((k⁻¹ * x * k) * w * (k⁻¹ * x * k)⁻¹ * w⁻¹) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h₂ hk) _).mp (hw.2 _ hx')) hy

structure Case2 (T L V H W₁ W₂ : Subgroup G) : Prop where
  u_le : fsuU T V ≤ W₂
  le : W₂ ≤ W₁
  le_pc : W₁ ≤ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G)
  norm₁ : H ≤ Subgroup.normalizer (W₁ : Set G)
  norm₂ : H ≤ Subgroup.normalizer (W₂ : Set G)
  idx : W₂.relIndex W₁ = 64
  elem : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₂ ∧ x ^ 2 ∈ W₂
  irred : ∀ X : Subgroup G, W₂ ≤ X → X ≤ W₁ → oTwoUpper H ≤ Subgroup.normalizer (X : Set G) →
    X = W₂ ∨ X = W₁
  faithful : ∀ x ∈ H, (∀ w ∈ W₁, x * w * x⁻¹ * w⁻¹ ∈ W₂) → x ∈ pCoreOf 2 H
  comm₂ : ⁅W₂, oTwoUpper H⁆ ≤ fsuU T V
  comm₁ : ⁅H ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper H⁆ ≤ W₁

namespace Case2

variable {W₁ W₂ : Subgroup G}

omit [Finite G] in
theorem isElemSection (h : Case2 T L V H W₁ W₂) : IsElemSection W₁ W₂ := ⟨h.le, h.elem⟩

theorem le_q (C : Ctx722 G T L V H γ γ' g k) (h : Case2 T L V H W₁ W₂) :
    W₁ ≤ pCoreOf 2 (L ⊔ T) := by
  rw [← C.hypF98.toHypF91.cT]
  intro w hw
  refine ⟨pCoreOf_le_of_le C.setting.hyp (t_le_h C) (p_le_qh (h.le_pc hw).1), ?_⟩
  exact Subgroup.centralizer_le (le_conjClosure V _) (h.le_pc hw).2

theorem qh_trivial (h : Case2 T L V H W₁ W₂) :
    ∀ x ∈ pCoreOf 2 H, ∀ w ∈ W₁, x * w * x⁻¹ * w⁻¹ ∈ W₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW := h.isElemSection
  have hQN : pCoreOf 2 H ≤ Subgroup.normalizer (W₂ : Set G) := (pCoreOf_le 2 H).trans h.norm₂
  set F := secFix hW (pCoreOf 2 H) with hF
  have hKF : oTwoUpper H ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_secFix hW _ ((oTwoUpper_le H).trans h.norm₁)
      ((oTwoUpper_le H).trans h.norm₂) ((oTwoUpper_le H).trans (le_normalizer_pCoreOf (r := 2) H))
  have hne : W₂ ≠ W₁ := by
    intro he
    have h1 := h.idx
    rw [he, Subgroup.relIndex_self] at h1
    norm_num at h1
  have hW₁p : IsPGroup 2 ↥W₁ :=
    (pCoreOf_isPGroup 2 (oTwoUpper H)).to_le fun w hw => (h.le_pc hw).1
  have hW₁N : W₁ ≤ Subgroup.normalizer (W₂ : Set G) := fun w hw =>
    mem_normalizer_of_forall_conj (Q := W₁) (fun a ha y hy => hW.conj_mem ha hy) hw
  obtain ⟨m, hmW₁, hmW₂, hmQ⟩ := exists_mem_fix_mod h.le hne (pCoreOf_isPGroup 2 H) hW₁p
    ((pCoreOf_le 2 H).trans h.norm₁) hQN hW₁N
  rcases h.irred F (le_secFix hW _ hQN) (fun w hw => hw.1) hKF with hF2 | hF1
  · have : m ∈ F := ⟨hmW₁, hmQ⟩
    rw [hF2] at this
    exact absurd this hmW₂
  · intro x hx w hw
    have : w ∈ F := by rw [hF1]; exact hw
    exact this.2 x hx

theorem fpf_l1 (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (h : Case2 T L V H W₁ W₂) :
    ∀ w ∈ W₁, (∀ l ∈ L32A.l1 T L V, l * w * l⁻¹ * w⁻¹ ∈ W₂) → w ∈ W₂ := by
  have hW := h.isElemSection
  have hLN : L32A.l1 T L V ≤ Subgroup.normalizer (W₂ : Set G) := (l1_le_h C).trans h.norm₂
  set F := secFix hW (L32A.l1 T L V) with hF
  have hKF : oTwoUpper H ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_secFix hW _ ((oTwoUpper_le H).trans h.norm₁)
      ((oTwoUpper_le H).trans h.norm₂) ((oTwoUpper_le H).trans C.l1_normal)
  rcases h.irred F (le_secFix hW _ hLN) (fun w hw => hw.1) hKF with hF2 | hF1
  · intro w hw hfix
    have : w ∈ F := ⟨hw, hfix⟩
    rwa [hF2] at this
  · exfalso
    refine c_not_mem_p (H := H) D ?_
    have hcQ : c ∈ pCoreOf 2 H := h.faithful c (c_mem_h C D) fun w hw => by
      have : w ∈ F := by rw [hF1]; exact hw
      exact this.2 c D.c_mem
    have hle : pCoreOf 2 H ⊓ L32A.l1 T L V ≤ pCoreOf 2 (L32A.l1 T L V) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact le_pCoreOf_of_le_normalizer inf_le_right
        (F7.le_normalizer_inf ((l1_le_h C).trans (le_normalizer_pCoreOf (r := 2) H))
          Subgroup.le_normalizer) ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    rw [C.o2_l1] at hle
    exact hle ⟨hcQ, D.c_mem⟩

theorem fpf_c (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (h : Case2 T L V H W₁ W₂) :
    ∀ w ∈ W₁, c * w * c⁻¹ * w⁻¹ ∈ W₂ → w ∈ W₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW := h.isElemSection
  have hcH := c_mem_h C D
  have hW₂p : IsPGroup 2 ↥W₂ := (pCoreOf_isPGroup 2 (oTwoUpper H)).to_le
    fun w hw => (h.le_pc (h.le hw)).1
  have hW₁N : W₁ ≤ Subgroup.normalizer (W₂ : Set G) := fun w hw =>
    mem_normalizer_of_forall_conj (Q := W₁) (fun a ha y hy => hW.conj_mem ha hy) hw
  have hF := mem_cfix_sup_iff D.c3 h.le (not_three_dvd_card hW₂p)
    (fun y hy => (Subgroup.mem_normalizer_iff.mp (h.norm₂ hcH) y).mp hy) hW₁N
  have hqh := qh_trivial h
  have hKF : oTwoUpper H ≤ Subgroup.normalizer
      ((cfix c W₁ ⊔ W₂ : Subgroup G) : Set G) := by
    intro y hy
    refine mem_normalizer_of_forall_conj (Q := oTwoUpper H) (fun y hy s hs => ?_) hy
    obtain ⟨hsW, hcs⟩ := (hF s).mp hs
    have hyH : y ∈ H := oTwoUpper_le H hy
    rw [hF]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (h.norm₁ hyH) s).mp hsW, ?_⟩
    set p := y⁻¹ * c * y * c⁻¹ with hp
    have hpP : p ∈ pCoreOf 2 (oTwoUpper H) := by
      have := comm_c_mem_p C D (inv_mem hy)
      simpa [hp] using this
    have hpH : p ∈ H := (pCoreOf_le 2 _).trans (oTwoUpper_le H) hpP
    have e : c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹ =
        y * ((p * (c * s * c⁻¹ * s⁻¹) * p⁻¹) * (p * s * p⁻¹ * s⁻¹)) * y⁻¹ := by
      rw [hp]; group
    rw [e]
    refine (Subgroup.mem_normalizer_iff.mp (h.norm₂ hyH) _).mp (mul_mem ?_
      (hqh p (p_le_qh hpP) s hsW))
    exact (Subgroup.mem_normalizer_iff.mp (h.norm₂ hpH) _).mp hcs
  rcases h.irred _ le_sup_right (sup_le (fun x hx => (mem_cfix.mp hx).1) h.le) hKF with
    hF2 | hF1
  · intro w hw hcw
    have := (hF w).mpr ⟨hw, hcw⟩
    rwa [hF2] at this
  · exfalso
    refine c_not_mem_p (H := H) D ?_
    have hcQ : c ∈ pCoreOf 2 H := h.faithful c hcH fun w hw => by
      have : w ∈ cfix c W₁ ⊔ W₂ := by rw [hF1]; exact hw
      exact ((hF w).mp this).2
    have hle : pCoreOf 2 H ⊓ L32A.l1 T L V ≤ pCoreOf 2 (L32A.l1 T L V) :=
      le_pCoreOf_of_le_normalizer inf_le_right
        (F7.le_normalizer_inf ((l1_le_h C).trans (le_normalizer_pCoreOf (r := 2) H))
          Subgroup.le_normalizer) ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    rw [C.o2_l1] at hle
    exact hle ⟨hcQ, D.c_mem⟩

theorem _root_.CFSG.Quasithin.H13.S4.comm_q_l1_mem_p (C : Ctx722 G T L V H γ γ' g k)
    (D : Data T L V θ c) {y l : G} (hy : y ∈ pCoreOf 2 (L ⊔ T)) (hl : l ∈ L32A.l1 T L V) :
    y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyH : y ∈ H := (pCoreOf_sup_le C.setting.hyp).trans (t_le_h C) hy
  have hLQ : L32A.l1 T L V ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := fun x hx =>
    le_normalizer_pCoreOf_sup T L (l1_le_l D hx)
  have hle : pCoreOf 2 (L ⊔ T) ⊓ L32A.l1 T L V ≤ pCoreOf 2 (L32A.l1 T L V) :=
    le_pCoreOf_of_le_normalizer inf_le_right (F7.le_normalizer_inf hLQ Subgroup.le_normalizer)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  rw [C.o2_l1] at hle
  refine hle (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have h1 : l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hLQ hl) _).mp (inv_mem hy)
    have e : y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem hy h1
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (C.l1_normal hyH) l).mp hl) (inv_mem hl)

theorem relIndex_le (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (h : Case2 T L V H W₁ W₂) :
    (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₂).relIndex
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) ≤ 4 := by
  have hW := h.isElemSection
  set R := conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L with hR
  set ρ := SecW.act hW H h.norm₁ h.norm₂ with hρ
  have hqh := qh_trivial h
  have hcH := c_mem_h C D
  obtain ⟨y, hyQ, hy2, hy4⟩ := exists_y C D
  have hyH : y ∈ H := (pCoreOf_sup_le C.setting.hyp).trans (t_le_h C) hyQ
  have hρQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → ρ x = 1 := fun x hx =>
    (SecW.act_eq_one_iff hW x).mpr fun w hw => hqh x hx w hw
  have hρc3 : ρ ⟨c, hcH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using D.c3)
    rw [this, map_one]
  have hfpf : ∀ w : SecW W₁ W₂ hW, ρ ⟨c, hcH⟩ w = w → w = 1 := by
    intro w hw
    obtain ⟨x, rfl⟩ := SecW.mk_surjective hW w
    rw [SecW.act_mk_eq_mk_iff] at hw
    exact (SecW.mk_eq_one_iff hW x).mpr (fpf_c C D h x x.2 hw)
  have hyc : ρ ⟨y, hyH⟩ * ρ ⟨c, hcH⟩ = ρ ⟨c, hcH⟩ * ρ ⟨y, hyH⟩ := by
    rw [← map_mul, ← map_mul]
    have h1 : ρ ((⟨y, hyH⟩ * ⟨c, hcH⟩) * (⟨c, hcH⟩ * ⟨y, hyH⟩)⁻¹) = 1 := by
      refine hρQ _ (p_le_qh ?_)
      have e : (((⟨y, hyH⟩ : ↥H) * ⟨c, hcH⟩) * (⟨c, hcH⟩ * ⟨y, hyH⟩)⁻¹ : ↥H) =
          ⟨y * c * y⁻¹ * c⁻¹, by
            exact mul_mem (mul_mem (mul_mem hyH hcH) (inv_mem hyH)) (inv_mem hcH)⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
      rw [e]
      exact comm_q_l1_mem_p C D hyQ D.c_mem
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hy4' : ρ ⟨y, hyH⟩ ^ 4 = 1 := by
    rw [← map_pow]
    exact hρQ _ (by simpa using hy4)
  have hy2' : ρ ⟨y, hyH⟩ ^ 2 ≠ 1 := by
    intro h1
    rw [← map_pow] at h1
    apply hy2
    have := h.faithful (y ^ 2) (pow_mem hyH 2) fun w hw =>
      (SecW.act_eq_one_iff hW _).mp h1 w hw
    simpa using this
  have hcard : Nat.card (SecW W₁ W₂ hW) = 64 := (SecW.card hW).trans h.idx
  have hfix := card_fixSub_le_four (SecW.mul_self hW) hρc3 hfpf hyc hy4' hy2' hcard
  have hle : R ⊓ W₁ ≤ SecW.pre hW (fixSub (ρ ⟨y, hyH⟩)) := by
    intro x hx
    rw [SecW.mem_pre]
    refine ⟨(Subgroup.mem_inf.mp hx).2, ?_⟩
    rw [mem_fixSub, SecW.act_mk_eq_mk_iff]
    have h1 := Subgroup.commutator_mem_commutator hyQ (Subgroup.mem_inf.mp hx).1
    rw [Subgroup.commutator_comm, C.rq, commutatorElement_def] at h1
    exact h.u_le (le_conjClosure V _ h1)
  have h4 : W₂.relIndex (SecW.pre hW (fixSub (ρ ⟨y, hyH⟩))) ≤ 4 := by
    rw [SecW.relIndex_pre]
    exact hfix
  have e1 : (R ⊓ W₂).relIndex (R ⊓ W₁) = W₂.relIndex (R ⊓ W₁) := by
    have : R ⊓ W₂ = W₂ ⊓ (R ⊓ W₁) := le_antisymm
      (fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2,
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, h.le (Subgroup.mem_inf.mp hx).2⟩⟩)
      (fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1,
        (Subgroup.mem_inf.mp hx).1⟩)
    rw [this, Subgroup.inf_relIndex_right]
  rw [e1]
  refine (Subgroup.relIndex_le_of_le_right hle ?_).trans h4
  show (W₂.subgroupOf _).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_mem (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (h : Case2 T L V H W₁ W₂) :
    ∃ x ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁, x ∉ W₂ := by
  by_contra hall
  push Not at hall
  have hUαQ : conjSub (k : G) (F8.Uγ V H (g : G)) ≤ pCoreOf 2 H := by
    intro a ha
    have haH : a ∈ H := s_le_h C D (ualpha_le_s C ha)
    refine h.faithful a haH fun w hw => ?_
    have hx : w * a * w⁻¹ * a⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁ := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 := Subgroup.commutator_mem_commutator (le_q C h hw) (ualpha_le_s C ha)
        rw [Subgroup.commutator_comm, C.sq, commutatorElement_def] at h1
        exact h1
      · have h1 : a * w⁻¹ * a⁻¹ ∈ W₁ :=
          (Subgroup.mem_normalizer_iff.mp (h.norm₁ haH) _).mp (inv_mem hw)
        have e : w * a * w⁻¹ * a⁻¹ = w * (a * w⁻¹ * a⁻¹) := by group
        rw [e]
        exact mul_mem hw h1
    have h2 := hall _ hx
    have e : a * w * a⁻¹ * w⁻¹ = (w * a * w⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h2
  have h1 := C.card_ualpha
  rw [sup_eq_right.mpr hUαQ, Subgroup.relIndex_self] at h1
  norm_num at h1

theorem nu_r (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) (h : Case2 T L V H W₁ W₂) :
    (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V).relIndex
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) = 4 *
    (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) ⊔
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₂)).relIndex
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) := by
  set R := conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L with hR
  set E := ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ with hE
  have hcH := c_mem_h C D
  have hRp := isPGroup_r C D
  have hVE : V ≤ E := C.v_le_e
  have hER : E ≤ R := le_conjClosure _ L
  have hEW₂ : E ≤ R ⊓ W₂ := le_inf hER ((e_le_u C D).trans h.u_le)
  have hW₂W₁ : R ⊓ W₂ ≤ R ⊓ W₁ := inf_le_inf_left R h.le
  have hRN : ∀ X : Subgroup G, X ≤ R → R ≤ Subgroup.normalizer (X : Set G) := fun X hX =>
    le_normalizer_of_comm hX fun a ha b hb => r_comm C D ha hb
  have hcfix : ∀ X : Subgroup G, X ≤ R → cfix c X ≤ R := fun X hX x hx => hX (mem_cfix.mp hx).1
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := le_normalizer_r D.c_L
  have hcRW : ∀ {W : Subgroup G}, H ≤ Subgroup.normalizer (W : Set G) →
      ∀ y ∈ R ⊓ W, c * y * c⁻¹ ∈ R ⊓ W := fun hW y hy =>
    Subgroup.mem_inf.mpr ⟨conj_mem_of_mem_normalizer hcR (Subgroup.mem_inf.mp hy).1,
      conj_mem_of_mem_normalizer (hW hcH) (Subgroup.mem_inf.mp hy).2⟩
  have hUR : fsuU T V ⊓ R = E := by rw [hR, hE]; exact u_inf_r C D
  have m1 := relIndex_cfix_sup_mul c (Y := V) (Z := R ⊓ W₁) (X := R)
    (hVE.trans (hEW₂.trans hW₂W₁)) inf_le_left ((hcfix R le_rfl).trans
      (hRN V (hVE.trans hER))) ((hcfix R le_rfl).trans (hRN _ inf_le_left))
  have m2 := relIndex_cfix_sup_mul c (Y := V) (Z := R ⊓ W₂) (X := R ⊓ W₁)
    (hVE.trans hEW₂) hW₂W₁ ((hcfix _ inf_le_left).trans (hRN V (hVE.trans hER)))
    ((hcfix _ inf_le_left).trans (hRN _ inf_le_left))
  have m3 := relIndex_cfix_sup_mul c (Y := V) (Z := E) (X := R ⊓ W₂) hVE hEW₂
    ((hcfix _ inf_le_left).trans (hRN V (hVE.trans hER)))
    ((hcfix _ inf_le_left).trans (hRN E hER))
  have v1 : cfix c R ⊔ (R ⊓ W₁) = R := by
    refine cfix_sup_eq_of_comm_le D.c3 inf_le_left (not_three_dvd_card (hRp.to_le inf_le_left))
      (hcRW h.norm₁) (hRN _ inf_le_left) fun r hr => Subgroup.mem_inf.mpr ⟨mul_mem
        (conj_mem_of_mem_normalizer hcR hr) (inv_mem hr), ?_⟩
    have h1 := h.comm₁ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_inf.mpr ⟨s_le_h C D (r_le_s C D hr), r_le_centralizer_u C hr⟩) (c_mem_k C D))
    rw [commutatorElement_def] at h1
    have e : c * r * c⁻¹ * r⁻¹ = (r * c * r⁻¹ * c⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have v3 : cfix c (R ⊓ W₂) ⊔ E = R ⊓ W₂ := by
    refine cfix_sup_eq_of_comm_le D.c3 hEW₂ (not_three_dvd_card (hRp.to_le hER))
      (fun y hy => conj_c_mem_e D hy) (fun x hx => hRN E hER (Subgroup.mem_inf.mp hx).1)
      fun x hx => ?_
    have hxR := (Subgroup.mem_inf.mp hx).1
    have hxW := (Subgroup.mem_inf.mp hx).2
    have h1 := h.comm₂ (Subgroup.commutator_mem_commutator hxW (c_mem_k C D))
    rw [commutatorElement_def] at h1
    have e : c * x * c⁻¹ * x⁻¹ = (x * c * x⁻¹ * c⁻¹)⁻¹ := by group
    have h2 : c * x * c⁻¹ * x⁻¹ ∈ fsuU T V ⊓ R := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [e]; exact inv_mem h1
      · exact mul_mem (conj_mem_of_mem_normalizer hcR hxR) (inv_mem hxR)
    rw [hUR] at h2
    exact h2
  have v4 : cfix c E ⊔ V = V := by
    refine cfix_sup_eq_of_fpf' fun e he hce => ?_
    exact mem_of_comm_mem C D (X := V) inf_le_left (le_conjClosure V _)
      (fun v hv => conj_mem_of_mem_normalizer ((le_sup_left.trans D.norm_v) D.c_L) hv)
      (e_le_u C D he) hce
  have h4 : (cfix c E ⊔ V).relIndex E = 4 := by rw [v4, C.relIndex_ve]
  rw [m1, v1, Subgroup.relIndex_self, one_mul, m2, m3, v3, Subgroup.relIndex_self, one_mul, h4,
    mul_comm]

theorem isoMod_core_r (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (h : Case2 T L V H W₁ W₂)
    [(V.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)).Normal] :
    ∃ ρ : Γ →* AddMonoid.End
        (Additive (↥(conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⧸
          V.subgroupOf (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L))),
      (∀ (l : ↥L) (s : ↥(conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L)),
        ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
          Additive.ofMul (QuotientGroup.mk ((secMod_r C D).conjX l s))) ∧ IsoMod ρ ρCore := by
  obtain ⟨ρ, hρ, hcases⟩ := lemma14_7_22 C D
  refine ⟨ρ, hρ, ?_⟩
  have hν := nu_r C D h
  have hcH := c_mem_h C D
  have hRp := isPGroup_r C D
  have hhi : (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) ⊔
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₂)).relIndex
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) ≤ 4 :=
    (relIndex_le_of_le le_sup_right (sup_le (fun x hx => (mem_cfix.mp hx).1)
      (inf_le_inf_left _ h.le))).trans (relIndex_le C D h)
  have hlo : 1 < (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) ⊔
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₂)).relIndex
      (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) := by
    obtain ⟨x, hx, hxW⟩ := exists_mem C D h
    have hRN : conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁ ≤ Subgroup.normalizer
        ((conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₂ : Subgroup G) : Set G) :=
      fun y hy => le_normalizer_of_comm inf_le_left (fun a ha b hb => r_comm C D ha hb)
        (Subgroup.mem_inf.mp hy).1
    have hF := mem_cfix_sup_iff D.c3 (inf_le_inf_left _ h.le)
      (not_three_dvd_card (hRp.to_le inf_le_left))
      (fun y hy => Subgroup.mem_inf.mpr ⟨conj_mem_of_mem_normalizer (le_normalizer_r D.c_L)
        (Subgroup.mem_inf.mp hy).1, conj_mem_of_mem_normalizer (h.norm₂ hcH)
          (Subgroup.mem_inf.mp hy).2⟩) hRN
    refine lt_of_le_of_ne (Nat.pos_of_ne_zero ?_) fun h1 => hxW ?_
    · show ((cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁) ⊔
        (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₂)).subgroupOf
          (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ W₁)).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    · have hxF := Subgroup.relIndex_eq_one.mp h1.symm hx
      exact Case2.fpf_c C D h x (Subgroup.mem_inf.mp hx).2
        (Subgroup.mem_inf.mp ((hF x).mp hxF).2).2
  have hmul := Subgroup.relIndex_mul_relIndex V
    (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V)
    (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) le_sup_right
    (sup_le (fun x hx => (mem_cfix.mp hx).1) (C.v_le_e.trans (le_conjClosure _ L)))
  have hne : V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V) ≠ 0 := by
    show (Subgroup.subgroupOf _ _).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have key : ∀ n : ℕ, V.relIndex (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) =
      n * V.relIndex (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V) →
      (cfix c (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) ⊔ V).relIndex
        (conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) = n := by
    intro n hn
    rw [← hmul, mul_comm n] at hn
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hn
  rcases hcases with ⟨-, h1⟩ | ⟨hiso, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
  · have := key 4 h1; omega
  · exact hiso
  · have := key 64 h1; omega
  · have := key 256 h1; omega
  · have := key 1024 h1; omega

end Case2

end CFSG.Quasithin.H13.S4
