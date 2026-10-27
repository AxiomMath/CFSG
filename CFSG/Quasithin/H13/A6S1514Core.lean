module

public import CFSG.Quasithin.H13.A6S13710e
public import CFSG.Quasithin.H13.A6S1515b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def C3L5 : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 1 2, swap 0 2 * swap 2 1, swap 0 1 * swap 1 3, swap 0 3 * swap 3 1,
    swap 0 1 * swap 1 4, swap 0 4 * swap 4 1, swap 0 2 * swap 2 3, swap 0 3 * swap 3 2,
    swap 0 2 * swap 2 4, swap 0 4 * swap 4 2, swap 0 3 * swap 3 4, swap 0 4 * swap 4 3,
    swap 1 2 * swap 2 3, swap 1 3 * swap 3 2, swap 1 2 * swap 2 4, swap 1 4 * swap 4 2,
    swap 1 3 * swap 3 4, swap 1 4 * swap 4 3, swap 2 3 * swap 3 4, swap 2 4 * swap 4 3]

theorem c3L5_facts : ∀ τ ∈ C3L5, τ 5 = 5 ∧ Perm.sign τ = 1 ∧ τ ^ 3 = 1 := by
  decide +kernel

theorem stab5_prod : ∀ σ : Perm (Fin 6), σ 5 = 5 → Perm.sign σ = 1 →
    ∃ τ₁ ∈ C3L5, ∃ τ₂ ∈ C3L5, σ = τ₁ * τ₂ := by
  decide +kernel

theorem stab5_O2 : ∀ σ : Perm (Fin 6), σ 5 = 5 → σ ≠ 1 →
    ∃ τ ∈ C3L5, (σ * τ * σ⁻¹ * τ⁻¹) ^ 4 ≠ 1 := by
  decide +kernel

@[expose] def C3L4 : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 1 2, swap 0 2 * swap 2 1, swap 0 1 * swap 1 3, swap 0 3 * swap 3 1,
    swap 0 2 * swap 2 3, swap 0 3 * swap 3 2, swap 1 2 * swap 2 3, swap 1 3 * swap 3 2]

theorem c3L4_facts : ∀ τ ∈ C3L4, τ 4 = 4 ∧ τ 5 = 5 ∧ Perm.sign τ = 1 ∧ τ ^ 3 = 1 := by
  decide +kernel

theorem alt4_prod : ∀ σ : Perm (Fin 6), σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 →
    ∃ τ₁ ∈ C3L4, ∃ τ₂ ∈ C3L4, σ = τ₁ * τ₂ := by
  decide +kernel

@[expose] def K4MaxAt5 (σ : Perm (Fin 6)) : Prop :=
  σ 5 = 5 → Perm.sign σ = 1 → σ ^ 4 = 1 → (∀ k ∈ K4L, (σ * k) ^ 4 = 1) → σ ∈ K4L

instance (σ : Perm (Fin 6)) : Decidable (K4MaxAt5 σ) := by unfold K4MaxAt5; infer_instance

theorem k4MaxAt5_all : ∀ σ : Perm (Fin 6), K4MaxAt5 σ := by
  decide +kernel

theorem fix4_of_e0123 : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → σ 5 = 5 → σ 4 = 4 := by
  decide +kernel

theorem s0145_apply : (swap (0 : Fin 6) 1 * swap 4 5 : Perm (Fin 6)) 4 = 5 ∧
    (swap (0 : Fin 6) 1 * swap 4 5 : Perm (Fin 6))⁻¹ 5 = 4 := by
  decide

@[expose] def fix5 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ 5 = 5}
  mul_mem' := fun {σ τ} hσ hτ => by
    show (σ * τ) 5 = 5
    rw [Perm.mul_apply, show τ 5 = 5 from hτ, show σ 5 = 5 from hσ]
  one_mem' := rfl
  inv_mem' := fun {σ} hσ => Perm.inv_eq_iff_eq.2 (show σ 5 = 5 from hσ).symm

@[expose] def restrFn (σ : Perm (Fin 6)) (i : Fin 5) : Fin 5 :=
  ⟨(σ (Fin.castSucc i)).val % 5, Nat.mod_lt _ (by norm_num)⟩

theorem castSucc_restrFn {σ : Perm (Fin 6)} (h : σ 5 = 5) (i : Fin 5) :
    Fin.castSucc (restrFn σ i) = σ (Fin.castSucc i) := by
  have hi : Fin.castSucc i ≠ 5 := fun h' => by
    have := congrArg Fin.val h'
    simp at this
    omega
  have hne : σ (Fin.castSucc i) ≠ 5 := fun h' => hi (σ.injective (h'.trans h.symm))
  have hlt : (σ (Fin.castSucc i)).val < 5 := by
    have h1 := (σ (Fin.castSucc i)).isLt
    have h2 : (σ (Fin.castSucc i)).val ≠ 5 := fun h'' => hne (Fin.ext h'')
    omega
  ext
  simp [restrFn, Nat.mod_eq_of_lt hlt]

theorem inv_five {σ : Perm (Fin 6)} (h : σ 5 = 5) : σ⁻¹ 5 = 5 :=
  Perm.inv_eq_iff_eq.2 h.symm

@[expose] def restr5 (σ : Perm (Fin 6)) (h : σ 5 = 5) : Perm (Fin 5) where
  toFun := restrFn σ
  invFun := restrFn σ⁻¹
  left_inv := fun i => Fin.castSucc_injective _ (by
    rw [castSucc_restrFn (inv_five h), castSucc_restrFn h]
    exact σ.symm_apply_apply _)
  right_inv := fun i => Fin.castSucc_injective _ (by
    rw [castSucc_restrFn h, castSucc_restrFn (inv_five h)]
    exact σ.apply_symm_apply _)

theorem sign_restr5 : ∀ σ : Perm (Fin 6), ∀ h : σ 5 = 5, Perm.sign (restr5 σ h) = Perm.sign σ := by
  decide +kernel

theorem eq_one_of_restrFn : ∀ σ : Perm (Fin 6), σ 5 = 5 → (∀ i, restrFn σ i = i) → σ = 1 := by
  decide +kernel

theorem exists_restrFn : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 →
    ∃ σ : Perm (Fin 6), σ 5 = 5 ∧ Perm.sign σ = 1 ∧ ∀ i, restrFn σ i = τ i := by
  decide +kernel

@[expose] def w4ToEv (x : P6) : Fin 5 → ZMod 2 := fun i => Multiplicative.toAdd x (Fin.castSucc i)

theorem w4ToEv_mem : ∀ x : P6, InW4 x → w4ToEv x ∈ A5Model.Ev := by
  decide +kernel

theorem w4ToEv_inj : ∀ x y : P6, InW4 x → InW4 y → (∀ i : Fin 5, w4ToEv x i = w4ToEv y i) →
    ∀ j : Fin 6, Multiplicative.toAdd x j = Multiplicative.toAdd y j := by
  decide +kernel

theorem w4ToEv_surj : ∀ v : Fin 5 → ZMod 2, v ∈ A5Model.Ev → ∃ x : P6, InW4 x ∧ w4ToEv x = v := by
  decide +kernel

theorem w4ToEv_act : ∀ σ : Perm (Fin 6), σ 5 = 5 → ∀ x : P6, InW4 x → ∀ i : Fin 5,
    w4ToEv (act4f σ x) i = w4ToEv x (restrFn σ⁻¹ i) := by
  decide +kernel

@[expose] def w4ToW5 : ↥W4 →* A5Model.W5 where
  toFun x := Multiplicative.ofAdd ⟨w4ToEv (x : P6), w4ToEv_mem _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem w4ToW5_bijective : Function.Bijective w4ToW5 := by
  refine ⟨fun x y h => Subtype.ext (Multiplicative.toAdd.injective (funext
    (w4ToEv_inj _ _ x.2 y.2 fun i => ?_))), fun v => ?_⟩
  · have := congrArg (fun w : A5Model.W5 => ((Multiplicative.toAdd w : ↥A5Model.Ev) :
      Fin 5 → ZMod 2) i) h
    exact this
  · obtain ⟨x, hx, hxv⟩ := w4ToEv_surj ((Multiplicative.toAdd v : ↥A5Model.Ev) : Fin 5 → ZMod 2)
      (Multiplicative.toAdd v).2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hxv

@[expose] noncomputable def w4EquivW5 : ↥W4 ≃* A5Model.W5 :=
  MulEquiv.ofBijective w4ToW5 w4ToW5_bijective

@[expose] def S5L : List (Perm (Fin 6)) :=
  [1, swap 0 4 * swap 1 2, swap 1 4 * swap 0 2, swap 2 4 * swap 0 1, swap 3 4 * swap 0 1]

theorem s5L_facts : ∀ τ ∈ S5L, τ 5 = 5 ∧ Perm.sign τ = 1 := by
  decide +kernel

theorem gen_e0123 : ∀ y : P6, InW4 y → y = 1 ∨ (∃ τ ∈ S5L, act4f τ e0123 = y) ∨
    ∃ τ₁ ∈ S5L, ∃ τ₂ ∈ S5L, act4f τ₁ e0123 * act4f τ₂ e0123 = y := by
  decide +kernel

@[expose] def StmtG248CoreProv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V V₁ L T H : Subgroup G),
    IsElemAbelian 2 V → V₁ ≠ ⊥ → V₁ ≤ V → L = oTwoUpper L → V ≤ T →
    T ≤ Subgroup.normalizer (V₁ : Set G) → T ≤ Subgroup.normalizer (V : Set G) →
    T ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf T (L ⊔ T) →
    H ≤ Subgroup.normalizer (V₁ : Set G) → lOne L V₁ ⊔ T ≤ H → CharTwo H →
    IsA5ModuleFor L (pCoreOf 2 (L ⊔ T)) (conjClosure V₁ L) → Nat.card V₁ = 2 →
    V = ⁅conjClosure V₁ L, lOne L V₁⁆ → ¬ conjClosure V H ≤ pCoreOf 2 (L ⊔ T) →
    T ≤ H → IsPGroup 2 T → G22Conclusion V V₁ T H →
    ⁅conjClosure V H, lOne L V₁⁆ ⊔ V₁ = conjClosure V H →
    pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 H →
    ∀ g ∈ L, g ∉ Subgroup.normalizer (V₁ : Set G) →
      conjClosure V H ⊔ rconj (conjClosure V H) g = L ∧ IsShort2 L ∧ IsAltType L 5 ∧
        pCoreOf 2 L = conjClosure V₁ L ∧ conjClosure V H = pCoreOf 2 (lOne L V₁) ∧
        IsQ8Sq ↥(conjClosure V H)

theorem conjSub_eq_self_of_normalizes {G : Type} [Group G] {g : G} {X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : conjSub g X = X := by
  ext y
  rw [mem_conjSub]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).symm
  simpa using this

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

@[expose] noncomputable def fix5V : Subgroup G :=
  (fix5.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype

theorem mem_fix5V {x : G} : x ∈ S.fix5V ↔
    ∃ hx : x ∈ Subgroup.normalizer (V : Set G), S.frame.ρ ⟨x, hx⟩ 5 = 5 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

@[expose] noncomputable def L5 : Subgroup G := oTwoRes (L ⊓ S.fix5V)

@[expose] noncomputable def T5 : Subgroup G := T ⊓ S.fix5V

theorem L5_le_L : S.L5 ≤ L := (oTwoRes_le _).trans inf_le_left

theorem L5_le_fix5V : S.L5 ≤ S.fix5V := (oTwoRes_le _).trans inf_le_right

theorem L5_le_NV : S.L5 ≤ Subgroup.normalizer (V : Set G) := S.L5_le_L.trans S.frame.L_le

theorem T5_le_T : S.T5 ≤ T := inf_le_left

theorem isPGroup_T5 : IsPGroup 2 S.T5 := S.h13.sylow.1.to_le S.T5_le_T

theorem oTwoUpper_L5 : S.L5 = oTwoUpper S.L5 := by
  rw [← oTwoRes_eq_oTwoUpper, L5, oTwoRes_oTwoRes]

theorem rho_L5 {x : ↥(Subgroup.normalizer (V : Set G))} (hx : (x : G) ∈ S.L5) :
    S.frame.ρ x 5 = 5 ∧ Perm.sign (S.frame.ρ x) = 1 := by
  obtain ⟨_, h5⟩ := S.mem_fix5V.1 (S.L5_le_fix5V hx)
  exact ⟨h5, Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨x, S.L5_le_L hx, rfl⟩)⟩

theorem exists_L5_three (hhat : ¬ IsHatA6 L) {τ : Perm (Fin 6)}
    (h5 : τ 5 = 5) (hs : Perm.sign τ = 1) (h3 : τ ^ 3 = 1) :
    ∃ x : ↥(Subgroup.normalizer (V : Set G)), (x : G) ∈ S.L5 ∧ S.frame.ρ x = τ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L τ).2 (Perm.mem_alternatingGroup.2 hs)
  have hl3 : ((l ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      L ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨by simpa using L.pow_mem hlL 3, (S.rho_eq_one_iff _).1 ?_⟩
    rw [map_pow, hρl, h3]
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, S.inf_centralizer_le_pCoreOf hhat hl3⟩
  have hk' : ((l : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hρx : S.frame.ρ (l ^ 4 ^ k) = τ := by
    rw [map_pow, hρl, pow_four_pow_of_cube h3]
  refine ⟨l ^ 4 ^ k, ?_, hρx⟩
  have hxL : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := by
    simpa using L.pow_mem hlL (4 ^ k)
  have hx3 : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) ^ 3 = 1 := by
    have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]
  have hx5 : ((l ^ 4 ^ k : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.fix5V :=
    S.mem_fix5V.2 ⟨(l ^ 4 ^ k).2, by rw [Subtype.coe_eta, hρx]; exact h5⟩
  exact Subgroup.subset_closure ⟨⟨hxL, hx5⟩, 3, by decide, hx3⟩

theorem exists_L5_rho (hhat : ¬ IsHatA6 L) {σ : Perm (Fin 6)}
    (h5 : σ 5 = 5) (hs : Perm.sign σ = 1) :
    ∃ x : ↥(Subgroup.normalizer (V : Set G)), (x : G) ∈ S.L5 ∧ S.frame.ρ x = σ := by
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, rfl⟩ := stab5_prod σ h5 hs
  obtain ⟨h₁5, h₁s, h₁3⟩ := c3L5_facts τ₁ hτ₁
  obtain ⟨h₂5, h₂s, h₂3⟩ := c3L5_facts τ₂ hτ₂
  obtain ⟨x₁, hx₁, hρ₁⟩ := S.exists_L5_three hhat h₁5 h₁s h₁3
  obtain ⟨x₂, hx₂, hρ₂⟩ := S.exists_L5_three hhat h₂5 h₂s h₂3
  exact ⟨x₁ * x₂, S.L5.mul_mem hx₁ hx₂, by rw [map_mul, hρ₁, hρ₂]⟩

theorem L1_le_L5 : S.L1 ≤ S.L5 := by
  have h1 : S.L1 ≤ L ⊓ S.fix5V := fun x hx => by
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hx)
    exact ⟨S.L1_le_L hx, S.mem_fix5V.2 ⟨hxN, (S.rho_L1 (g := ⟨x, hxN⟩) hx).2.1⟩⟩
  calc S.L1 = oTwoRes S.L1 := (oTwoRes_oTwoRes _).symm
    _ ≤ S.L5 := Subgroup.closure_mono fun y hy => ⟨h1 hy.1, hy.2⟩

theorem lOne_L5 : lOne S.L5 (fsuV1 T V) = S.L1 := by
  rw [lOne_eq_L₁Of]
  apply le_antisymm
  · exact Subgroup.closure_mono fun y hy =>
      ⟨⟨S.L5_le_L hy.1.1, hy.1.2⟩, hy.2⟩
  · calc S.L1 = oTwoRes S.L1 := (oTwoRes_oTwoRes _).symm
      _ ≤ L₁Of S.L5 (fsuV1 T V) := Subgroup.closure_mono fun y hy =>
        ⟨⟨S.L1_le_L5 hy.1, (S.L1_le hy.1).2⟩, hy.2⟩

theorem T5_le_normalizer_L5 : S.T5 ≤ Subgroup.normalizer (S.L5 : Set G) := by
  refine A5.le_normalizer_oTwoRes_of_le_normalizer
    (A5.le_normalizer_of_forall_conj_mem fun t ht y hy => ?_)
  obtain ⟨htN, ht5⟩ := S.mem_fix5V.1 ht.2
  obtain ⟨hyN, hy5⟩ := S.mem_fix5V.1 hy.2
  have hN : t * y * t⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hyN) (Subgroup.inv_mem _ htN)
  refine ⟨(Subgroup.mem_normalizer_iff.mp (S.T_le_NL ht.1) y).mp hy.1, S.mem_fix5V.2 ⟨hN, ?_⟩⟩
  have e : (⟨t * y * t⁻¹, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨t, htN⟩ * ⟨y, hyN⟩ * ⟨t, htN⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply,
    Perm.inv_eq_iff_eq.2 ht5.symm, hy5, ht5]

theorem V_le_T5 : V ≤ S.T5 := fun v hv =>
  ⟨S.V_le_T hv, S.mem_fix5V.2 ⟨S.frame.T_le (S.V_le_T hv),
    by rw [(S.rho_eq_one_iff _).2 (S.V_le_centralizer_V hv)]; rfl⟩⟩

theorem T5_le_NV1 : S.T5 ≤ Subgroup.normalizer (fsuV1 T V : Set G) := S.T5_le_T.trans S.T_le_NV1

theorem T5_le_NV3 : S.T5 ≤ Subgroup.normalizer (S.V3 : Set G) :=
  S.T5_le_T.trans S.T_le_normalizer_V3

theorem inf_centralizer_le_T5 (hhat : ¬ IsHatA6 L) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ S.T5 := fun c hc =>
  ⟨S.pCoreOf_L_le_T (S.inf_centralizer_le_pCoreOf hhat hc),
    S.mem_fix5V.2 ⟨S.frame.L_le hc.1, by rw [(S.rho_eq_one_iff _).2 hc.2]; rfl⟩⟩

theorem pCoreOf_L1_le_T : pCoreOf 2 S.L1 ≤ T :=
  (pCoreOf_le_pCoreOf_sup S.T_le_normalizer_L1).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)

theorem isSylowTwoOf_T5_inf (hhat : ¬ IsHatA6 L) :
    IsSylowTwoOf (S.T5 ⊓ S.L5) S.L5 := by
  have hO2 : ∀ u ∈ pCoreOf 2 S.L1, u ∈ S.T5 ⊓ S.L5 := fun u hu => by
    have huL1 := pCoreOf_le 2 S.L1 hu
    have huN : u ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L huL1)
    exact ⟨⟨S.pCoreOf_L1_le_T hu, S.mem_fix5V.2 ⟨huN, (S.rho_L1 (g := ⟨u, huN⟩) huL1).2.1⟩⟩,
      S.L1_le_L5 huL1⟩
  have hsurj : ∀ k ∈ K4L, ∃ u ∈ pCoreOf 2 S.L1, ∃ hu : u ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨u, hu⟩ = k := by
    intro k hk
    have hk' : k ∈ S.rhoO2L1.range := by rw [S.rho_O2L1_eq_K4 hhat]; exact hk
    obtain ⟨u, rfl⟩ := hk'
    exact ⟨u, u.2, _, rfl⟩
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨inf_le_right, S.isPGroup_T5.to_le inf_le_left, fun R hRL hR hTR => ?_⟩
  intro r hr
  have hrL := hRL hr
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := S.L5_le_NV hrL
  obtain ⟨hr5, hrs⟩ := S.rho_L5 (x := ⟨r, hrN⟩) hrL
  have hpow : ∀ x ∈ R, ∀ hx : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ ^ 4 = 1 := by
    intro x hxR hx
    obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hρr : S.frame.ρ ⟨r, hrN⟩ ∈ K4L := by
    refine k4MaxAt5_all _ hr5 hrs (hpow r hr hrN) fun k hk => ?_
    obtain ⟨u, hu, huN, hρu⟩ := hsurj k hk
    have huR : u ∈ R := hTR (hO2 u hu)
    have := hpow (r * u) (R.mul_mem hr huR) (Subgroup.mul_mem _ hrN huN)
    have e : (⟨r * u, Subgroup.mul_mem _ hrN huN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨r, hrN⟩ * ⟨u, huN⟩ := rfl
    rwa [e, map_mul, hρu] at this
  obtain ⟨u, hu, huN, hρu⟩ := hsurj _ hρr
  have hc : S.frame.ρ (⟨u, huN⟩⁻¹ * ⟨r, hrN⟩) = 1 := by
    rw [map_mul, map_inv, hρu, inv_mul_cancel]
  have hcL : u⁻¹ * r ∈ L :=
    L.mul_mem (L.inv_mem (S.L5_le_L (hO2 u hu).2)) (S.L5_le_L hrL)
  have hcT := S.inf_centralizer_le_T5 hhat ⟨hcL, (S.rho_eq_one_iff _).1 hc⟩
  have hrT : r ∈ S.T5 := by
    have := S.T5.mul_mem (hO2 u hu).1 hcT
    simpa using this
  exact ⟨hrT, hrL⟩

theorem isSylowTwoOf_T5 (hhat : ¬ IsHatA6 L) :
    IsSylowTwoOf S.T5 (S.L5 ⊔ S.T5) :=
  isSylowTwoOf_sup_of_inf S.isPGroup_T5 S.T5_le_normalizer_L5 (S.isSylowTwoOf_T5_inf hhat)

theorem rho_L5' (x : ↥S.L5) :
    S.frame.ρ ⟨x, S.L5_le_NV x.2⟩ 5 = 5 ∧ Perm.sign (S.frame.ρ ⟨x, S.L5_le_NV x.2⟩) = 1 :=
  S.rho_L5 x.2

theorem L5T5_le_fix5V : S.L5 ⊔ S.T5 ≤ S.fix5V := sup_le S.L5_le_fix5V inf_le_right

theorem L5T5_le_NV : S.L5 ⊔ S.T5 ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.L5_le_NV (S.T5_le_T.trans S.frame.T_le)

theorem pCoreOf_L5T5_le_centralizer (hhat : ¬ IsHatA6 L) :
    pCoreOf 2 (S.L5 ⊔ S.T5) ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro d hd
  have hdX : d ∈ S.L5 ⊔ S.T5 := pCoreOf_le 2 _ hd
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := S.L5T5_le_NV hdX
  obtain ⟨_, hd5⟩ := S.mem_fix5V.1 (S.L5T5_le_fix5V hdX)
  refine (S.rho_eq_one_iff ⟨d, hdN⟩).1 ?_
  by_contra hne
  obtain ⟨τ, hτ, hτ4⟩ := stab5_O2 _ hd5 hne
  obtain ⟨h5, hs, h3⟩ := c3L5_facts τ hτ
  obtain ⟨x, hxL, hρx⟩ := S.exists_L5_three hhat h5 hs h3
  have hxX : (x : G) ∈ S.L5 ⊔ S.T5 := (le_sup_left : S.L5 ≤ S.L5 ⊔ S.T5) hxL
  have hk : d * x * d⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 (S.L5 ⊔ S.T5) := by
    have h1 : (x : G) * d⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 (S.L5 ⊔ S.T5) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hxX) _).mp
        (Subgroup.inv_mem _ hd)
    have := Subgroup.mul_mem _ hd h1
    simpa [mul_assoc] using this
  obtain ⟨k, hk'⟩ := pCoreOf_isPGroup 2 _ ⟨_, hk⟩
  apply hτ4
  have hkN : d * x * d⁻¹ * (x : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hdN x.2) (Subgroup.inv_mem _ hdN))
      (Subgroup.inv_mem _ x.2)
  have hρk : (S.frame.ρ ⟨_, hkN⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨_, hkN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk')
    rw [this, map_one]
  have h4 := pow_four_of_pow_two_pow hρk
  have e : (⟨d * x * d⁻¹ * (x : G)⁻¹, hkN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨d, hdN⟩ * x * ⟨d, hdN⟩⁻¹ * x⁻¹ := rfl
  rwa [e, map_mul, map_mul, map_mul, map_inv, map_inv, hρx] at h4

theorem inf_centralizer_le_pCoreOf_L5T5 (hhat : ¬ IsHatA6 L) :
    S.L5 ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (S.L5 ⊔ S.T5) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) (sup_le ?_ ?_) ?_
  · exact F7.le_normalizer_inf Subgroup.le_normalizer
      (S.L5_le_NV.trans (A5.normalizer_le_normalizer_centralizer' V))
  · exact F7.le_normalizer_inf S.T5_le_normalizer_L5
      ((S.T5_le_T.trans S.frame.T_le).trans (A5.normalizer_le_normalizer_centralizer' V))
  · exact (pCoreOf_isPGroup 2 L).to_le fun c hc =>
      S.inf_centralizer_le_pCoreOf hhat ⟨S.L5_le_L hc.1, hc.2⟩

theorem mem_pCoreOf_L5T5_iff (hhat : ¬ IsHatA6 L) {x : G}
    (hx : x ∈ S.L5) :
    x ∈ pCoreOf 2 (S.L5 ⊔ S.T5) ↔ x ∈ Subgroup.centralizer (V : Set G) :=
  ⟨fun h => S.pCoreOf_L5T5_le_centralizer hhat h,
    fun h => S.inf_centralizer_le_pCoreOf_L5T5 hhat ⟨hx, h⟩⟩

@[expose] noncomputable def theta5 : ↥S.L5 →* alternatingGroup (Fin 5) where
  toFun x := ⟨restr5 (S.frame.ρ ⟨x, S.L5_le_NV x.2⟩) (S.rho_L5' x).1, by
    rw [Perm.mem_alternatingGroup, sign_restr5]
    exact (S.rho_L5' x).2⟩
  map_one' := by
    apply Subtype.ext
    refine Equiv.ext fun i => Fin.castSucc_injective _ ?_
    show Fin.castSucc (restrFn (S.frame.ρ ⟨((1 : ↥S.L5) : G), S.L5_le_NV (1 : ↥S.L5).2⟩) i) =
      Fin.castSucc i
    rw [castSucc_restrFn (S.rho_L5' 1).1]
    have e : (⟨((1 : ↥S.L5) : G), S.L5_le_NV (1 : ↥S.L5).2⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = 1 := rfl
    rw [e, map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    refine Equiv.ext fun i => Fin.castSucc_injective _ ?_
    show Fin.castSucc (restrFn (S.frame.ρ ⟨((x * y : ↥S.L5) : G), S.L5_le_NV (x * y).2⟩) i) =
      Fin.castSucc (restrFn (S.frame.ρ ⟨x, S.L5_le_NV x.2⟩)
        (restrFn (S.frame.ρ ⟨y, S.L5_le_NV y.2⟩) i))
    rw [castSucc_restrFn (S.rho_L5' (x * y)).1, castSucc_restrFn (S.rho_L5' x).1,
      castSucc_restrFn (S.rho_L5' y).1]
    have e : (⟨((x * y : ↥S.L5) : G), S.L5_le_NV (x * y).2⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = ⟨x, S.L5_le_NV x.2⟩ * ⟨y, S.L5_le_NV y.2⟩ := rfl
    rw [e, map_mul, Perm.mul_apply]

theorem theta5_apply (x : ↥S.L5) (i : Fin 5) :
    ((S.theta5 x : Perm (Fin 5)) i) = restrFn (S.frame.ρ ⟨x, S.L5_le_NV x.2⟩) i := rfl

theorem theta5_surjective (hhat : ¬ IsHatA6 L) :
    Function.Surjective S.theta5 := by
  intro τ
  obtain ⟨σ, h5, hs, hσ⟩ := exists_restrFn τ (Perm.mem_alternatingGroup.1 τ.2)
  obtain ⟨x, hxL, hρx⟩ := S.exists_L5_rho hhat h5 hs
  refine ⟨⟨x, hxL⟩, Subtype.ext (Equiv.ext fun i => ?_)⟩
  rw [theta5_apply]
  have e : (⟨(x : G), S.L5_le_NV hxL⟩ : ↥(Subgroup.normalizer (V : Set G))) = x := rfl
  rw [e, hρx, hσ]

theorem theta5_ker (hhat : ¬ IsHatA6 L) :
    S.theta5.ker = (pCoreOf 2 (S.L5 ⊔ S.T5)).subgroupOf S.L5 := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, S.mem_pCoreOf_L5T5_iff hhat x.2]
  have key := S.rho_eq_one_iff ⟨x, S.L5_le_NV x.2⟩
  constructor
  · intro h
    refine key.1 (eq_one_of_restrFn _ (S.rho_L5' x).1 fun i => ?_)
    have := congrArg (fun τ : alternatingGroup (Fin 5) => (τ : Perm (Fin 5)) i) h
    exact this
  · intro h
    refine Subtype.ext (Equiv.ext fun i => Fin.castSucc_injective _ ?_)
    rw [theta5_apply, castSucc_restrFn (S.rho_L5' x).1, key.2 h]
    rfl

@[expose] noncomputable def rawData5_L5 (hhat : ¬ IsHatA6 L) :
    RawData5 S.L5 (pCoreOf 2 (S.L5 ⊔ S.T5)) V where
  hnorm := S.L5_le_NV
  θ := S.theta5
  ψ := S.frame.ψ.trans w4EquivW5
  surj := S.theta5_surjective hhat
  ker_eq := S.theta5_ker hhat
  equiv := fun a v => by
    show w4EquivW5 (S.frame.ψ (conjAct V ⟨a, S.L5_le_NV a.2⟩ v)) =
      A5Model.pact (S.theta5 a : Perm (Fin 5)) (w4EquivW5 (S.frame.ψ v))
    rw [S.frame.equiv]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact w4ToEv_act _ (S.rho_L5' a).1 _ (S.frame.ψ v).2 i

theorem conjClosure_V1_L5 (hhat : ¬ IsHatA6 L) :
    conjClosure (fsuV1 T V) S.L5 = V := by
  apply le_antisymm
  · refine conjClosure_le fun h hh x hx => ?_
    exact (Subgroup.mem_normalizer_iff.mp (S.L5_le_NV hh) x).mp
      ((S.V1_le_V2.trans S.V2_le_V) hx)
  · intro v hv
    have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
    have hconj : ∀ τ ∈ S5L, ∃ w ∈ conjClosure (fsuV1 T V) S.L5, ∃ hw : w ∈ V,
        (S.frame.ψ ⟨w, hw⟩ : P6) = act4f τ e0123 := by
      intro τ hτ
      obtain ⟨h5, hs⟩ := s5L_facts τ hτ
      obtain ⟨x, hxL, hρx⟩ := S.exists_L5_rho hhat h5 hs
      refine ⟨x * S.z * (x : G)⁻¹, mem_conjClosure hxL hz,
        (Subgroup.mem_normalizer_iff.mp x.2 _).mp S.z_mem_V, ?_⟩
      rw [S.psi_conj x ⟨S.z, S.z_mem_V⟩, S.psi_z, hρx]
      rfl
    have hinj : ∀ (u w : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ w : P6) → (u : G) = w := by
      intro u w h
      exact congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
    rcases gen_e0123 _ (S.frame.ψ ⟨v, hv⟩).2 with h1 | ⟨τ, hτ, hτv⟩ |
        ⟨τ₁, hτ₁, τ₂, hτ₂, hτv⟩
    · have : v = ((1 : ↥V) : G) := hinj ⟨v, hv⟩ 1 (by rw [map_one]; exact h1)
      rw [this]
      exact Subgroup.one_mem _
    · obtain ⟨w, hw, hwV, hψw⟩ := hconj τ hτ
      have : v = w := hinj ⟨v, hv⟩ ⟨w, hwV⟩ (by rw [hψw, hτv])
      rw [this]
      exact hw
    · obtain ⟨w₁, hw₁, hw₁V, hψ₁⟩ := hconj τ₁ hτ₁
      obtain ⟨w₂, hw₂, hw₂V, hψ₂⟩ := hconj τ₂ hτ₂
      have : v = ((⟨w₁, hw₁V⟩ * ⟨w₂, hw₂V⟩ : ↥V) : G) := hinj ⟨v, hv⟩ (⟨w₁, hw₁V⟩ * ⟨w₂, hw₂V⟩)
        (by rw [map_mul, Subgroup.coe_mul, hψ₁, hψ₂, hτv])
      rw [this]
      exact Subgroup.mul_mem _ hw₁ hw₂

theorem isA5ModuleFor_L5 (hhat : ¬ IsHatA6 L) :
    IsA5ModuleFor S.L5 (pCoreOf 2 (S.L5 ⊔ S.T5)) (conjClosure (fsuV1 T V) S.L5) := by
  rw [S.conjClosure_V1_L5 hhat]
  exact ⟨S.rawData5_L5 hhat⟩

theorem V3_eq_commutator_L5 (hhat : ¬ IsHatA6 L) :
    S.V3 = ⁅conjClosure (fsuV1 T V) S.L5, lOne S.L5 (fsuV1 T V)⁆ := by
  rw [S.conjClosure_V1_L5 hhat, S.lOne_L5]
  exact S.commutator_V_L1.symm

theorem not_UH_le_pCoreOf_L5T5 (hhat : ¬ IsHatA6 L)
    {H : Subgroup G} (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    ¬ conjClosure S.V3 H ≤ pCoreOf 2 (S.L5 ⊔ S.T5) := fun h =>
  hna (S.isElemAbelian_UH_of_le (h.trans (S.pCoreOf_L5T5_le_centralizer hhat)))

theorem H_le_NV1 {H : Subgroup G} (hH : H ∈ S.Hz) :
    H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hH.2.1.trans S.G1_le_normalizer_V1

theorem lOne_T5_le_H {H : Subgroup G} (hH : H ∈ S.Hz) : lOne S.L5 (fsuV1 T V) ⊔ S.T5 ≤ H := by
  rw [S.lOne_L5]
  exact sup_le (le_sup_left.trans hH.1.1) (S.T5_le_T.trans (le_sup_right.trans hH.1.1))

theorem T5_le_H {H : Subgroup G} (hH : H ∈ S.Hz) : S.T5 ≤ H :=
  S.T5_le_T.trans (le_sup_right.trans hH.1.1)

theorem charTwo_H {H : Subgroup G} (hH : H ∈ S.Hz) : CharTwo H :=
  S.charTwo_of_inH ⟨le_sup_right.trans hH.1.1, hH.1.2⟩

theorem g22_T5 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hle : conjClosure S.V3 H ≤ S.L1) : G22Conclusion S.V3 (fsuV1 T V) S.T5 H := by
  have hg := (S.hypF91 hNS h13315 h1356two hH).almostSpecialHyp.g22
  refine ⟨hg.one, hg.two, ⟨fun u hu => ⟨hg.three.1 hu, ?_⟩, S.T5_le_T.trans hg.three.2⟩, hg.four⟩
  have huN : u ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L (hle hu))
  exact S.mem_fix5V.2 ⟨huN, (S.rho_L1 (g := ⟨u, huN⟩) (hle hu)).2.1⟩

theorem pCoreOf_LT_le_T5 : pCoreOf 2 (L ⊔ T) ≤ S.T5 := by
  rw [← S.cT]
  exact fun q hq => ⟨hq.1, S.mem_fix5V.2 ⟨S.frame.T_le hq.1,
    by rw [(S.rho_eq_one_iff _).2 hq.2]; rfl⟩⟩

theorem oTwoRes_pCoreOf_sup_L5 :
    oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.L5) = S.L5 := by
  have hQT5 := S.pCoreOf_LT_le_T5
  have hQN : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (S.L5 : Set G) :=
    hQT5.trans S.T5_le_normalizer_L5
  have hQ2 : IsPGroup 2 (pCoreOf 2 (L ⊔ T)) := S.isPGroup_T5.to_le hQT5
  apply le_antisymm
  · rw [oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    rw [sup_comm] at hy
    have hmul : ((S.L5 ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) =
        (S.L5 : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left S.L5 _ hQN
    have hy' : y ∈ (S.L5 : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) := by
      rw [← hmul]
      exact hy
    obtain ⟨l, hl, q, hq, rfl⟩ := Set.mem_mul.mp hy'
    obtain ⟨l', hl', hpow⟩ := pow_mul_mem_of_normalizes hl (hQN hq) m
    rw [hym] at hpow
    have hqm : q ^ m ∈ S.L5 := by
      have e : q ^ m = l'⁻¹ := eq_inv_of_mul_eq_one_right hpow.symm
      rw [e]
      exact S.L5.inv_mem hl'
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : m.Coprime (orderOf q) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
      rw [hj]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hm)
    obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
    have hqL : q ∈ S.L5 := by
      rw [← hn]
      exact S.L5.pow_mem hqm n
    exact S.L5.mul_mem hl hqL
  · calc S.L5 = oTwoRes S.L5 := (oTwoRes_oTwoRes _).symm
      _ ≤ oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.L5) :=
        Subgroup.closure_mono fun y hy => ⟨(le_sup_right : S.L5 ≤ _) hy.1, hy.2⟩

theorem g248_L5 (hG : StmtG248CoreProv)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L) {x : G}
    (hx : x ∈ S.L5) (hxN : x ∉ Subgroup.normalizer (fsuV1 T V : Set G)) :
    conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) x = S.L5 ∧ IsShort2 S.L5 ∧
      IsAltType S.L5 5 ∧ pCoreOf 2 S.L5 = V ∧ conjClosure S.V3 H = pCoreOf 2 S.L1 ∧
      IsQ8Sq ↥(conjClosure S.V3 H) := by
  have hle := S.UH_le_L1_six hNS h13315 h1356two hH hn hna
  have hA := S.toA5Sit hNS h13315 h1356two hH hna
  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have := S.card_V1
    rw [h, Subgroup.card_bot] at this
    omega
  have hV1U : fsuV1 T V ≤ conjClosure S.V3 H :=
    (S.V1_le_V2.trans S.V2_le_V3).trans (le_conjClosure _ _)
  have hcomm : ⁅conjClosure S.V3 H, lOne S.L5 (fsuV1 T V)⁆ ⊔ fsuV1 T V = conjClosure S.V3 H := by
    rw [S.lOne_L5, hA.commutator_UH_L1 hn]
    exact sup_eq_left.2 hV1U
  have hO2 : pCoreOf 2 (lOne S.L5 (fsuV1 T V)) ≤ pCoreOf 2 H := by
    rw [S.lOne_L5]
    exact hA.pCoreOf_L1_le hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG G S.V3 (fsuV1 T V) S.L5 S.T5 H
    (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) hV1 (S.V1_le_V2.trans S.V2_le_V3)
    S.oTwoUpper_L5 (S.V3_le_V.trans S.V_le_T5) S.T5_le_NV1 S.T5_le_NV3 S.T5_le_normalizer_L5
    (S.isSylowTwoOf_T5 hhat) (S.H_le_NV1 hH) (S.lOne_T5_le_H hH) (S.charTwo_H hH)
    (S.isA5ModuleFor_L5 hhat) S.card_V1 (S.V3_eq_commutator_L5 hhat)
    (S.not_UH_le_pCoreOf_L5T5 hhat hna) (S.T5_le_H hH) S.isPGroup_T5
    (S.g22_T5 hNS h13315 h1356two hH hle) hcomm hO2 x hx hxN
  rw [S.conjClosure_V1_L5 hhat] at h4
  rw [S.lOne_L5] at h5
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem mem_L1T_of_fix (hhat : ¬ IsHatA6 L)
    {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (h5 : S.frame.ρ l 5 = 5)
    (h4 : S.frame.ρ l 4 = 4) : (l : G) ∈ S.L1 ⊔ T := by
  have hs : Perm.sign (S.frame.ρ l) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨l, hlL, rfl⟩)
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hτ⟩ := alt4_prod _ h4 h5 hs
  obtain ⟨h₁4, h₁5, h₁s, h₁3⟩ := c3L4_facts τ₁ hτ₁
  obtain ⟨h₂4, h₂5, h₂s, h₂3⟩ := c3L4_facts τ₂ hτ₂
  obtain ⟨a₁, ha₁, hρ₁⟩ := S.exists_L1_rho hhat h₁s h₁4 h₁5 h₁3
  obtain ⟨a₂, ha₂, hρ₂⟩ := S.exists_L1_rho hhat h₂s h₂4 h₂5 h₂3
  have hc : S.frame.ρ ((a₁ * a₂)⁻¹ * l) = 1 := by
    rw [map_mul, map_inv, map_mul, hρ₁, hρ₂, ← hτ, inv_mul_cancel]
  have hcL : ((a₁ * a₂)⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) ∈
      (L ⊓ Subgroup.centralizer (V : Set G)).comap (Subgroup.normalizer (V : Set G)).subtype :=
    ⟨L.mul_mem (L.inv_mem (L.mul_mem (S.L1_le_L ha₁) (S.L1_le_L ha₂))) hlL,
      (S.rho_eq_one_iff _).1 hc⟩
  have hcT : (((a₁ * a₂)⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ T :=
    S.T5_le_T (S.inf_centralizer_le_T5 hhat hcL)
  have e : (l : G) = ((a₁ * a₂ : ↥(Subgroup.normalizer (V : Set G))) : G) *
      (((a₁ * a₂)⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) : G) := by
    push_cast
    group
  rw [e]
  exact Subgroup.mul_mem_sup (S.L1.mul_mem ha₁ ha₂) hcT

theorem obl_five (hG : StmtG248CoreProv)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L)
    {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hlT : (l : G) ∉ S.L1 ⊔ T)
    (h5 : S.frame.ρ l 5 = 5) :
    S.KH H l = S.L5 ∧ IsShort2 S.L5 ∧ IsAltType S.L5 5 ∧ pCoreOf 2 S.L5 = V ∧
      conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H) := by
  have hs : Perm.sign (S.frame.ρ l) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨l, hlL, rfl⟩)
  obtain ⟨x, hxL5, hρx⟩ := S.exists_L5_rho hhat h5 hs
  have hxN : (x : G) ∉ Subgroup.normalizer (fsuV1 T V : Set G) := by
    intro hxN
    have hfix := S.fix_e0123 x (S.conj_z_of_normalizes hxN)
    rw [hρx] at hfix
    exact hlT (S.mem_L1T_of_fix hhat hlL h5 (fix4_of_e0123 _ hfix h5))
  obtain ⟨hK, hsh, halt, hO2, hU, hQ8⟩ :=
    S.g248_L5 hG hNS h13315 h1356two hH hn hna hhat hxL5 hxN
  have hc : S.frame.ρ (x⁻¹ * l) = 1 := by rw [map_mul, map_inv, hρx, inv_mul_cancel]
  have hcT5 : ((x⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.T5 :=
    S.inf_centralizer_le_T5 hhat ⟨L.mul_mem (L.inv_mem (S.L5_le_L hxL5)) hlL,
      (S.rho_eq_one_iff _).1 hc⟩
  set c : G := ((x⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) : G) with hcdef
  have hlc : (l : G) = x * c := by
    rw [hcdef]
    simp
  have hcH : c⁻¹ ∈ H := H.inv_mem (S.T5_le_H hH hcT5)
  have hUc : conjSub c⁻¹ (conjClosure S.V3 H) = conjClosure S.V3 H :=
    conjSub_eq_self_of_normalizes (le_normalizer_conjClosure _ _ hcH)
  have hL5c : conjSub c⁻¹ S.L5 = S.L5 :=
    conjSub_eq_self_of_normalizes (S.T5_le_normalizer_L5 (S.T5.inv_mem hcT5))
  have hKH : S.KH H l = S.L5 := by
    have e1 : S.KH H l = conjClosure S.V3 H ⊔ conjSub (l : G)⁻¹ (conjClosure S.V3 H) := rfl
    have e2 : rconj (conjClosure S.V3 H) x = conjSub (x : G)⁻¹ (conjClosure S.V3 H) := rfl
    rw [e2] at hK
    rw [e1, hlc, mul_inv_rev, conjSub_mul]
    nth_rewrite 1 [← hUc]
    rw [← conjSub_sup, hK, hL5c]
  exact ⟨hKH, hsh, halt, hO2, hU, hQ8⟩

theorem obl_four (hG : StmtG248CoreProv)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L)
    {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hlT : (l : G) ∉ S.L1 ⊔ T)
    (h4 : S.frame.ρ l 4 = 4) :
    oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) = S.KH H l ∧ IsShort2 (S.KH H l) ∧
      IsAltType (S.KH H l) 5 ∧ pCoreOf 2 (S.KH H l) = V ∧
      conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H) := by
  obtain ⟨t, htT, hρt⟩ :=
    S.frame.DA_T _ s0145_facts.1 (Perm.mem_alternatingGroup.2 s0145_facts.2.1)
  have hl'L : ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (S.T_le_NL htT) l).mp hlL
  have h5 : S.frame.ρ (t * l * t⁻¹) 5 = 5 := by
    rw [map_mul, map_mul, map_inv, hρt, Perm.mul_apply, Perm.mul_apply, s0145_apply.2, h4,
      s0145_apply.1]
  have htT' : (t : G) ∈ S.L1 ⊔ T := Subgroup.mem_sup_right htT
  have hl'T : ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∉ S.L1 ⊔ T := by
    intro h
    apply hlT
    have e : (l : G) =
        (t : G)⁻¹ * ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * t := by
      push_cast
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htT') h) htT'
  obtain ⟨hKH, hsh, halt, hO2, hU, hQ8⟩ :=
    S.obl_five hG hNS h13315 h1356two hH hn hna hhat hl'L hl'T h5
  have htH : (t : G) ∈ H := (le_sup_right.trans hH.1.1) htT
  have hUt : ∀ g ∈ H, conjSub g (conjClosure S.V3 H) = conjClosure S.V3 H := fun g hg =>
    conjSub_eq_self_of_normalizes (le_normalizer_conjClosure _ _ hg)
  have hconj : S.KH H (t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) =
      conjSub (t : G) (S.KH H l) := by
    have e1 : ∀ k : G, S.KH H k = conjClosure S.V3 H ⊔ conjSub k⁻¹ (conjClosure S.V3 H) :=
      fun k => rfl
    rw [e1, e1, conjSub_sup, hUt _ htH]
    congr 1
    have e2 : ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ =
        (t : G) * ((l : G)⁻¹ * (t : G)⁻¹) := by
      push_cast
      group
    rw [e2, conjSub_mul, conjSub_mul, hUt _ (H.inv_mem htH)]
  rw [hconj] at hKH
  have hK : S.KH H l = conjSub (t : G)⁻¹ S.L5 := by
    rw [← hKH, conjSub_conjSub_inv]
  have htQ : conjSub (t : G)⁻¹ (pCoreOf 2 (L ⊔ T)) = pCoreOf 2 (L ⊔ T) :=
    conjSub_eq_self_of_normalizes (le_normalizer_pCoreOf 2 _
      ((le_sup_right : T ≤ L ⊔ T) (T.inv_mem htT)))
  have htV : conjSub (t : G)⁻¹ V = V :=
    conjSub_eq_self_of_normalizes (S.frame.T_le (T.inv_mem htT))
  refine ⟨?_, ?_, ?_, ?_, hU, hQ8⟩
  · rw [hK]
    nth_rewrite 1 [← htQ]
    rw [← conjSub_sup, ← conjSub_oTwoRes, S.oTwoRes_pCoreOf_sup_L5]
  · rw [hK]
    exact (Lin2.isShort2_map_equiv_iff (MulAut.conj (t : G)⁻¹) S.L5).2 hsh
  · rw [hK]
    exact L238.IsAltType.map_equiv halt (MulAut.conj (t : G)⁻¹)
  · rw [hK, pCoreOf_conjSub, hO2, htV]

end Setting4

theorem obl13_5_14Six_of (hG : StmtG248CoreProv)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) : Obl13_5_14Six := by
  intro G _ _ T L V S H l hNS hH hn hna hhat hl hlL hlT h45
  rcases h45 with h4 | h5
  · exact S.obl_four hG hNS h13315 h1356two hH hn hna hhat (l := ⟨l, hl⟩) hlL hlT h4
  · obtain ⟨hKH, hsh, halt, hO2, hU, hQ8⟩ :=
      S.obl_five hG hNS h13315 h1356two hH hn hna hhat (l := ⟨l, hl⟩) hlL hlT h5
    have hKH' : conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l = S.L5 := hKH
    rw [hKH']
    exact ⟨S.oTwoRes_pCoreOf_sup_L5, hsh, halt, hO2, hU, hQ8⟩

end CFSG.Quasithin.H13.A6
