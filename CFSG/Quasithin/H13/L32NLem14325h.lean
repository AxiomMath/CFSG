module

public import CFSG.Quasithin.H13.L32NLem14325d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

theorem s3_gen : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → τ * τ = 1 → τ ≠ 1 →
    ∀ π : Equiv.Perm (Fin 3), π = 1 ∨ π = σ ∨ π = σ * σ ∨ π = τ ∨ π = σ * τ ∨ π = σ * σ * τ := by
  decide +kernel

theorem s3_conj_three : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 →
    ∃ ρ ∈ [Equiv.swap (0 : Fin 3) 1, Equiv.swap 1 2], (τ * (ρ * τ * ρ⁻¹)) ^ 3 = 1 ∧
      τ * (ρ * τ * ρ⁻¹) ≠ 1 := by
  decide +kernel

theorem s3_inv : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → τ * τ = 1 → τ ≠ 1 →
    τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

theorem s3_comm : ∀ τ₁ τ₂ : Equiv.Perm (Fin 3), τ₁ * τ₁ = 1 ∧ τ₁ ≠ 1 ∧ τ₂ * τ₂ = 1 ∧ τ₂ ≠ 1 ∧
    τ₁ * τ₂ = τ₂ * τ₁ → τ₁ = τ₂ := by
  decide +kernel

theorem s3_cent : ∀ τ π : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → π * τ = τ * π →
    π = 1 ∨ π = τ := by
  decide +kernel

theorem s3_elem : ∀ π : Equiv.Perm (Fin 3), π ^ 3 = 1 ∨ π * π = 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

abbrev kI (T V : Subgroup G) (g : G) : Subgroup G :=
  conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V)

structure CtxI (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) : Prop where
  ctx : Ctx14325 G T L V V₂ g D
  dim : Module.finrank (ZMod 2) D.V = 4
  zd : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) = D.img (l32nH T V) ⊓
    fixingSubgroup (D.V ≃ₗ[ZMod 2] D.V) (D.hat V : Set D.V)
  card_zd : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 2
  iso : Nonempty (↥(D.img (kI T V g)) ≃* Equiv.Perm (Fin 3))
  sup : D.img (kI T V g) ⊔ D.img (lOne L (fsuV1 T V)) ⊔ D.img T = D.img (l32nH T V)
  not_le : ¬ kI T V g ≤ Subgroup.normalizer (L : Set G)
  l1_normal : D.img (l32nH T V) ≤
    Subgroup.normalizer (D.img (lOne L (fsuV1 T V)) : Set (D.V ≃ₗ[ZMod 2] D.V))
  LT_V : L ⊔ T ≤ Subgroup.normalizer (V : Set G)
  zgU : ∀ z ∈ CFSG.conjugate (centerOf (fsuU T V)) g, z ∈ l32nCHat T V → z ∈ fsuU T V
  relIdx :
    (centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g).relIndex (centerOf (fsuU T V)) = 2
  hi : Case14323i T L V g D
  sq : ∀ u ∈ fsuU T V, u * u ∈ fsuV1 T V
  comm : ∀ u ∈ fsuU T V, ∀ w ∈ fsuU T V, u * w * u⁻¹ * w⁻¹ ∈ fsuV1 T V

theorem exists_ctxI (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12810 : Lemma12_8_10)
    (C : Ctx14325 G T L V V₂ g D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hi : Case14323i T L V g D) : CtxI G T L V V₂ g D := by
  obtain ⟨hzd, hcard, hiso, hsup, hKM⟩ := hi.zU C.zUg_ne
  obtain ⟨-, -, hLTV, -, -⟩ := stmtL32NModule_of_inputs h1332 h1334 G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨-, -, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  obtain ⟨e1, e2, e3, -, -, -⟩ := h6
  obtain ⟨hsq, hcomm⟩ := L14332.sq_mem_and_comm_mem C.U2
    (display12_8_frattini h1222 h12213 G T L V 3 (fsuV1 T V) V₂ C.setting).le
  refine ⟨C, hd, hzd, hcard, hiso, hsup, hKM, hi.l1_normal, hLTV, fun z hz hzE => ?_, ?_,
    hi, hsq, fun u hu w hw => by simpa [commutatorElement_def] using hcomm u hu w hw⟩
  · have h1 : z ∈ CFSG.conjugate (zU128 V (fsuV1 T V)) g ⊓
        centralizerMod (zU128 V (fsuV1 T V)) (Subgroup.normalizer (fsuV1 T V : Set G))
          (u128 V (fsuV1 T V)) := ⟨hz, hzE⟩
    rw [e1, e2, e3] at h1
    exact h1.2
  · rw [C.relIndex_inf_conj h12810, hcard]

def stabV : Subgroup (D.V ≃ₗ[ZMod 2] D.V) where
  carrier := {γ | ∀ w ∈ D.hat V, γ w ∈ D.hat V}
  mul_mem' {γ δ} hγ hδ w hw := hγ _ (hδ w hw)
  one_mem' w hw := hw
  inv_mem' {γ} hγ := by
    intro w hw
    have := Finite.of_injective (fun v : ↥(D.hat V) => (v : D.V)) Subtype.val_injective
    let f : ↥(D.hat V) → ↥(D.hat V) := fun v => ⟨γ v, hγ v v.2⟩
    have hf : Function.Injective f := fun v v' h => Subtype.ext (γ.injective (congrArg
      Subtype.val h))
    obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
    have hv' : γ v = w := congrArg Subtype.val hv
    have e1 : γ⁻¹ w = v := by
      rw [← hv', ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rw [e1]
    exact v.2

omit [Finite G] in
theorem le_normalizer_centralizer {X : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) :
    h ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h⁻¹ * w * h⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hh) w).mp hw
    have hc := Subgroup.mem_centralizer_iff.mp hk _ hw'
    rw [inv_inv] at hc
    calc w * (h * k * h⁻¹) = h * ((h⁻¹ * w * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * w * h)) * h⁻¹ := by rw [hc]
      _ = h * k * h⁻¹ * w := by group
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h * w * h⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hh w).mp hw
    have hc := Subgroup.mem_centralizer_iff.mp hk _ hw'
    calc w * k = h⁻¹ * ((h * w * h⁻¹) * (h * k * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * k * h⁻¹) * (h * w * h⁻¹)) * h := by rw [hc]
      _ = k * w := by group

namespace CtxI

variable (C : CtxI G T L V V₂ g D)
include C

theorem card_V : Nat.card D.V = 16 := Ctx14325.card_V_of_dim C.dim

theorem T_V : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans C.LT_V

omit [Finite G] C in
theorem lOne_le : lOne L (fsuV1 T V) ≤ L ⊓ l32nH T V :=
  oTwoUpper_le _

omit [Finite G] C in
theorem zUg_le_kI : CFSG.conjugate (centerOf (fsuU T V)) g ≤ kI T V g := le_conjClosure _ _

theorem kI_le : kI T V g ≤ l32nH T V :=
  conjClosure_le fun _ hh _ hz => (l32nH T V).mul_mem ((l32nH T V).mul_mem hh
    (C.ctx.zUg_le hz)) ((l32nH T V).inv_mem hh)

omit [Finite G] C in
theorem le_normalizer_kI : l32nH T V ≤ Subgroup.normalizer (kI T V g : Set G) :=
  le_normalizer_conjClosure _ _

theorem false_of_maps (h : D.img (l32nH T V) ≤ stabV (D := D)) : False := by
  have hU : ∀ u ∈ fsuU T V, D.π u ∈ D.hat V := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hy
      have hkN := L14332.l32nH_le_normalizer_fsuU T V hk
      rw [← D.ρ_π ⟨k, hkN⟩ v (C.ctx.V_U hv)]
      exact h (L128A.HatU.rho_mem_img D hk hkN) _
        (L128A.HatU.π_mem_hat D hv (C.ctx.V_U hv))
    | one => rw [L128A.HatU.π_one]; exact Submodule.zero_mem _
    | mul y y' hy hy' ih ih' =>
      rw [D.π_mul y hy y' hy']
      exact Submodule.add_mem _ ih ih'
    | inv y hy ih =>
      rw [L128A.HatU.π_inv D hy]
      exact Submodule.neg_mem _ ih
  have htop : D.hat V = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    exact hU u hu
  have h1 := C.ctx.card_hatV
  rw [htop] at h1
  have h2 : Nat.card ↥(⊤ : Submodule (ZMod 2) D.V) = Nat.card D.V :=
    Nat.card_congr (Submodule.topEquiv.toEquiv)
  rw [h2, C.card_V] at h1
  omega

theorem zd_le_stabV : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≤ stabV (D := D) := by
  intro γ hγ w hw
  rw [C.zd] at hγ
  have h1 : γ w = w := hγ.2 ⟨w, hw⟩
  rw [h1]
  exact hw

theorem img_le_stabV {X : Subgroup G} (hXL : X ≤ l32nH T V)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) : D.img X ≤ stabV (D := D) := by
  intro γ hγ w hw
  obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact C.ctx.rho_mem_hatV_of_normalizer (hXL hx) (hXV hx) hw

theorem false_of_three {γ : D.V ≃ₗ[ZMod 2] D.V} (hγK : γ ∈ D.img (kI T V g)) (hγ3 : γ ^ 3 = 1)
    (hγ1 : γ ≠ 1) (hγS : γ ∈ stabV (D := D)) : False := by
  obtain ⟨e⟩ := C.iso
  obtain ⟨⟨τ, hτZ⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp C.ctx.zUg_ne
  have hτ1' : τ ≠ 1 := fun h => hτ1 (Subtype.ext h)
  have hτK : τ ∈ D.img (kI T V g) := by
    obtain ⟨z, hz, hzN, rfl⟩ := (L128A.HatU.mem_img D).mp hτZ
    exact L128A.HatU.rho_mem_img D (zUg_le_kI hz) hzN
  have hτ2 : τ * τ = 1 := by
    have h2 := pow_card_eq_one' (G := ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)))
      (x := ⟨τ, hτZ⟩)
    rw [C.card_zd, pow_two] at h2
    exact congrArg Subtype.val h2
  have hτS : τ ∈ stabV (D := D) := C.zd_le_stabV hτZ
  have hKS : D.img (kI T V g) ≤ stabV (D := D) := by
    intro π hπ
    have hσ3 : e ⟨γ, hγK⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨γ, hγK⟩ : ↥(D.img (kI T V g))) ^ 3 = 1 := Subtype.ext (by simpa using hγ3)
      rw [this, map_one]
    have hσ1 : e ⟨γ, hγK⟩ ≠ 1 := by
      rw [Ne, MulEquiv.map_eq_one_iff]
      exact fun h => hγ1 (congrArg Subtype.val h)
    have hτ2' : e ⟨τ, hτK⟩ * e ⟨τ, hτK⟩ = 1 := by
      rw [← map_mul]
      have : (⟨τ, hτK⟩ : ↥(D.img (kI T V g))) * ⟨τ, hτK⟩ = 1 := Subtype.ext hτ2
      rw [this, map_one]
    have hτ1'' : e ⟨τ, hτK⟩ ≠ 1 := by
      rw [Ne, MulEquiv.map_eq_one_iff]
      exact fun h => hτ1' (congrArg Subtype.val h)
    set S' : Subgroup ↥(D.img (kI T V g)) := (stabV (D := D)).comap (D.img (kI T V g)).subtype
      with hS'
    have hσS : e ⟨γ, hγK⟩ ∈ S'.map e.toMonoidHom := ⟨⟨γ, hγK⟩, hγS, rfl⟩
    have hτS' : e ⟨τ, hτK⟩ ∈ S'.map e.toMonoidHom := ⟨⟨τ, hτK⟩, hτS, rfl⟩
    have hmem : e ⟨π, hπ⟩ ∈ S'.map e.toMonoidHom := by
      rcases s3_gen _ _ hσ3 hσ1 hτ2' hτ1'' (e ⟨π, hπ⟩) with h | h | h | h | h | h <;> rw [h]
      · exact one_mem _
      · exact hσS
      · exact mul_mem hσS hσS
      · exact hτS'
      · exact mul_mem hσS hτS'
      · exact mul_mem (mul_mem hσS hσS) hτS'
    obtain ⟨q, hq, hqe⟩ := hmem
    have hq' : q = ⟨π, hπ⟩ := e.injective hqe
    rw [hq'] at hq
    exact hq
  apply C.false_of_maps
  rw [← C.sup]
  refine sup_le (sup_le hKS (C.img_le_stabV (lOne_le.trans inf_le_right) ?_))
    (C.img_le_stabV C.ctx.T_le C.T_V)
  exact (lOne_le.trans inf_le_left).trans (le_sup_left.trans C.LT_V)

theorem mem_cHat_of_three {S : Subgroup G} (hS : l32nH T V ≤ Subgroup.normalizer (S : Set G))
    (h3 : ∀ y ∈ kI T V g, y ∈ S → ∀ hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨y, hyN⟩ ^ 3 = 1 → D.ρ ⟨y, hyN⟩ ≠ 1 → False)
    {k : G} (hk : k ∈ kI T V g) (hkS : k ∈ S) : k ∈ l32nCHat T V := by
  obtain ⟨e⟩ := C.iso
  have hkH : k ∈ l32nH T V := C.kI_le hk
  have hkN := L14332.l32nH_le_normalizer_fsuU T V hkH
  by_contra hkE
  have hρ1 : D.ρ ⟨k, hkN⟩ ≠ 1 := fun h1 => hkE ((L14332.rho_eq_one_iff_mem hkH hkN).mp h1)
  have hρK : D.ρ ⟨k, hkN⟩ ∈ D.img (kI T V g) := L128A.HatU.rho_mem_img D hk hkN
  set σ := e ⟨_, hρK⟩ with hσ
  have hσ1 : σ ≠ 1 := by
    rw [hσ, Ne, MulEquiv.map_eq_one_iff]
    exact fun h => hρ1 (congrArg Subtype.val h)
  rcases s3_elem σ with h3' | h2
  · refine h3 k hk hkS hkN ?_ hρ1
    have : (⟨_, hρK⟩ : ↥(D.img (kI T V g))) ^ 3 = 1 := e.injective (by rw [map_pow, ← hσ,
      h3', map_one])
    simpa using congrArg Subtype.val this
  · obtain ⟨ρ', -, hρ'3, hρ'1⟩ := s3_conj_three σ h2 hσ1
    obtain ⟨⟨γ', hγ'⟩, hγ'e⟩ := e.surjective ρ'
    obtain ⟨k₁, hk₁, hk₁N, hk₁γ⟩ := (L128A.HatU.mem_img D).mp hγ'
    have hk₁H : k₁ ∈ l32nH T V := C.kI_le hk₁
    set k₂ := k * (k₁ * k * k₁⁻¹) with hk₂
    have hk₂K : k₂ ∈ kI T V g := (kI T V g).mul_mem hk ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_kI hk₁H) k).mp hk)
    have hk₂N : k₂ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
      L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hk₂K)
    have hk₂S : k₂ ∈ S := S.mul_mem hkS ((Subgroup.mem_normalizer_iff.mp (hS hk₁H) k).mp hkS)
    have hρk₂ : D.ρ ⟨k₂, hk₂N⟩ = D.ρ ⟨k, hkN⟩ * (γ' * D.ρ ⟨k, hkN⟩ * γ'⁻¹) := by
      rw [← hk₁γ, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have hρk₂K : D.ρ ⟨k₂, hk₂N⟩ ∈ D.img (kI T V g) := L128A.HatU.rho_mem_img D hk₂K hk₂N
    have he : e ⟨_, hρk₂K⟩ = σ * (ρ' * σ * ρ'⁻¹) := by
      rw [← hγ'e, hσ, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hρk₂
    refine h3 k₂ hk₂K hk₂S hk₂N ?_ ?_
    · have : (⟨_, hρk₂K⟩ : ↥(D.img (kI T V g))) ^ 3 = 1 := e.injective (by
        rw [map_pow, he, hρ'3, map_one])
      simpa using congrArg Subtype.val this
    · intro h1
      apply hρ'1
      rw [← he]
      have : (⟨_, hρk₂K⟩ : ↥(D.img (kI T V g))) = 1 := Subtype.ext h1
      rw [this, map_one]

theorem mem_cHat_of_mem_centralizer {k : G} (hk : k ∈ kI T V g)
    (hkc : k ∈ Subgroup.centralizer (vH T L V : Set G)) : k ∈ l32nCHat T V :=
  C.mem_cHat_of_three (fun _ hh => le_normalizer_centralizer (le_normalizer_conjClosure _ _ hh))
    (fun _ hy hyc hyN hy3 hy1 => C.false_of_three (L128A.HatU.rho_mem_img D hy hyN) hy3 hy1
      (fun _ hw => C.ctx.rho_mem_hatV (C.kI_le hy) hyc hw)) hk hkc

end CtxI

end L14325

end CFSG.Quasithin.H13
