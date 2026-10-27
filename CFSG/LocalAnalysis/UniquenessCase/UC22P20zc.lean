module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Basic

variable {X Γ : Type} [Group X] [Group Γ]

theorem uc22pwt_apply_inv_apply (ρ : Γ →* MulAut X) (g : Γ) (x : X) : ρ g (ρ g⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem uc22pwt_apply_mul (ρ : Γ →* MulAut X) (g g' : Γ) (x : X) : ρ (g * g') x = ρ g (ρ g' x) := by
  rw [map_mul, MulAut.mul_apply]

theorem uc22pwt_apply_conj (ρ : Γ →* MulAut X) (τ g : Γ) (y : X) :
    ρ g (ρ τ y) = ρ τ (ρ (τ⁻¹ * g * τ) y) := by
  have : g * τ = τ * (τ⁻¹ * g * τ) := by group
  rw [← uc22pwt_apply_mul, ← uc22pwt_apply_mul, this]

end Basic

section CtxLemmas

variable {X Γ : Type} [Group X] [Group Γ]

namespace UC22pwtCtx

variable {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} (C : UC22pwtCtx ρ τ U A₁ A₂)

include C

theorem comm' : ∀ a ∈ A₂, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb => (C.comm b hb a ha).symm

theorem mem₂ {x : X} (hx : x ∈ A₁) : ρ τ x ∈ A₂ := (C.swap₁ x).1 hx

theorem mem₁_inv_iff {x : X} : ρ τ⁻¹ x ∈ A₁ ↔ x ∈ A₂ := by
  have := C.swap₁ (ρ τ⁻¹ x)
  rwa [uc22pwt_apply_inv_apply] at this

theorem mem₂_inv_iff {x : X} : ρ τ⁻¹ x ∈ A₂ ↔ x ∈ A₁ := by
  have := C.swap₂ (ρ τ⁻¹ x)
  rwa [uc22pwt_apply_inv_apply] at this

theorem swap_U₁ {x : X} : ρ τ x ∈ U ⊓ A₂ ↔ x ∈ U ⊓ A₁ := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← C.Uinv τ x, ← C.swap₁ x]

theorem swap_U₂_inv {x : X} : ρ τ⁻¹ x ∈ U ⊓ A₁ ↔ x ∈ U ⊓ A₂ := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← C.Uinv τ⁻¹ x, C.mem₁_inv_iff]

theorem stab_ττ : τ * τ ∈ uc22pwtStab2 ρ A₁ A₂ := by
  rw [mem_uc22pwtStab2]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [uc22pwt_apply_mul]
    exact (C.swap₁ x).trans (C.swap₂ (ρ τ x))
  · rw [uc22pwt_apply_mul]
    exact (C.swap₂ x).trans (C.swap₁ (ρ τ x))

theorem stab_conj {g : Γ} (hg : g ∈ uc22pwtStab2 ρ A₁ A₂) : τ⁻¹ * g * τ ∈ uc22pwtStab2 ρ A₁ A₂ := by
  obtain ⟨hg1, hg2⟩ := mem_uc22pwtStab2.1 hg
  rw [mem_uc22pwtStab2]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [uc22pwt_apply_mul, uc22pwt_apply_mul]
    exact (C.swap₁ x).trans ((hg2 _).trans C.mem₁_inv_iff.symm)
  · rw [uc22pwt_apply_mul, uc22pwt_apply_mul]
    exact (C.swap₂ x).trans ((hg1 _).trans C.mem₂_inv_iff.symm)

end UC22pwtCtx

end CtxLemmas

section Generic

variable {X : Type} [Group X]

theorem uc22pwt_mem_normalizer_sup {S T : Subgroup X} {x : X} (hS : x ∈ normalizer (S : Set X))
    (hT : x ∈ normalizer (T : Set X)) : x ∈ normalizer ((S ⊔ T : Subgroup X) : Set X) := by
  have key : ∀ z : X, z ∈ normalizer (S : Set X) → z ∈ normalizer (T : Set X) →
      ∀ y ∈ S ⊔ T, z * y * z⁻¹ ∈ S ⊔ T := by
    intro z hzS hzT
    have hle : S ⊔ T ≤ (S ⊔ T).comap (MulAut.conj z).toMonoidHom := by
      refine sup_le (fun s hs => ?_) (fun t ht => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hzS s).1 hs)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hzT t).1 ht)
    exact fun y hy => hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key x hS hT y hy, fun hy => ?_⟩
  have h1 := key x⁻¹ (inv_mem hS) (inv_mem hT) _ hy
  have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem uc22pwt_mem_normalizer_of_part {U A B : Subgroup X} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hUsplit : U ≤ (U ⊓ A) ⊔ (U ⊓ B)) {x : X} (hxA : x ∈ A)
    (hx : x ∈ normalizer ((U ⊓ A : Subgroup X) : Set X)) : x ∈ normalizer (U : Set X) := by
  have hB : x ∈ normalizer ((U ⊓ B : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · rw [hcomm x hxA y hy.2, mul_inv_cancel_right]
      exact hy
    · have hxz := hcomm x hxA _ hy.2
      have e : x * y * x⁻¹ = y := by
        have h1 : x * (x * y * x⁻¹) = x * y := by
          calc x * (x * y * x⁻¹) = (x * y * x⁻¹) * x := hxz
            _ = x * y := by group
        exact mul_left_cancel h1
      rwa [e] at hy
  have hU : (U ⊓ A) ⊔ (U ⊓ B) = U := le_antisymm (sup_le inf_le_left inf_le_left) hUsplit
  have := uc22pwt_mem_normalizer_sup hx hB
  rwa [hU] at this

theorem uc22pwt_mem_normalizer_aut (φ : MulAut X) {S S' : Subgroup X}
    (hS : ∀ y, y ∈ S ↔ φ y ∈ S') {x : X} (hx : x ∈ normalizer (S : Set X)) :
    φ x ∈ normalizer (S' : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  obtain ⟨y', rfl⟩ : ∃ y', φ y' = y := ⟨φ⁻¹ y, MulAut.apply_inv_self X φ y⟩
  have e : φ x * φ y' * (φ x)⁻¹ = φ (x * y' * x⁻¹) := by simp [map_mul, map_inv]
  rw [e, ← hS, ← hS]
  exact hx y'

theorem uc22pwt_pow_mul_mem {V : Subgroup X} {h : X} (hh : h ∈ normalizer (V : Set X)) (s : ℤ) {v : X}
    (hv : v ∈ V) (k : ℕ) : ∃ v' ∈ V, (h ^ s * v) ^ k = h ^ (s * k) * v' := by
  induction k with
  | zero => exact ⟨1, V.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨v', hv', hk⟩ := ih
    have hs : (h ^ s)⁻¹ ∈ normalizer (V : Set X) := inv_mem (zpow_mem hh s)
    have hc : (h ^ s)⁻¹ * v' * h ^ s ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.1 hs v').1 hv'
      rwa [inv_inv] at h1
    refine ⟨(h ^ s)⁻¹ * v' * h ^ s * v, V.mul_mem hc hv, ?_⟩
    rw [pow_succ, hk]
    have e : h ^ (s * ((k + 1 : ℕ) : ℤ)) = h ^ (s * (k : ℤ)) * h ^ s := by
      rw [← zpow_add]
      congr 1
      push_cast
      ring
    rw [e]
    generalize h ^ (s * (k : ℤ)) = p
    generalize h ^ s = q
    group

@[expose] def uc22pwtFix (U : Subgroup X) (φ : MulAut X) : Subgroup X where
  carrier := {y | y ∈ normalizer (U : Set X) ∧ φ y * y⁻¹ ∈ U}
  mul_mem' := by
    rintro y z ⟨hy, hyU⟩ ⟨hz, hzU⟩
    refine ⟨mul_mem hy hz, ?_⟩
    have e : φ (y * z) * (y * z)⁻¹ = (φ y * y⁻¹) * (y * (φ z * z⁻¹) * y⁻¹) := by
      rw [map_mul]
      group
    rw [e]
    exact U.mul_mem hyU ((Subgroup.mem_normalizer_iff.1 hy _).1 hzU)
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro y ⟨hy, hyU⟩
    refine ⟨inv_mem hy, ?_⟩
    have e : φ y⁻¹ * (y⁻¹)⁻¹ = y⁻¹ * (φ y * y⁻¹)⁻¹ * (y⁻¹)⁻¹ := by
      rw [map_inv]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 (U.inv_mem hyU)

theorem mem_uc22pwtFix {U : Subgroup X} {φ : MulAut X} {y : X} :
    y ∈ uc22pwtFix U φ ↔ y ∈ normalizer (U : Set X) ∧ φ y * y⁻¹ ∈ U :=
  Iff.rfl

end Generic

section GenericFinite

variable {X : Type} [Group X] [Finite X]

theorem uc22pwt_mem_of_mem_oPi {α : Set ℕ} {E : Subgroup X} (hE : IsMulCommutative E) {x : X}
    (hx : x ∈ oPi α E) : x ∈ E ∧ ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ α := by
  haveI := hE
  let P : Subgroup X :=
    { carrier := {y | y ∈ E ∧ ∀ p : ℕ, p.Prime → p ∣ orderOf y → p ∈ α}
      mul_mem' := by
        rintro y z ⟨hy, hyα⟩ ⟨hz, hzα⟩
        refine ⟨E.mul_mem hy hz, fun p hp hpd => ?_⟩
        have hc : Commute y z := mul_comm_of_mem_isMulCommutative E hy hz
        have h1 : orderOf (y * z) ∣ orderOf y * orderOf z := hc.orderOf_mul_dvd_mul_orderOf
        rcases (Nat.Prime.dvd_mul hp).1 (hpd.trans h1) with h2 | h2
        · exact hyα p hp h2
        · exact hzα p hp h2
      one_mem' := ⟨E.one_mem, fun p hp hpd => by
        rw [orderOf_one] at hpd
        exact absurd (Nat.le_of_dvd one_pos hpd) (by have := hp.two_le; omega)⟩
      inv_mem' := by
        rintro y ⟨hy, hyα⟩
        exact ⟨E.inv_mem hy, fun p hp hpd => hyα p hp (by rwa [orderOf_inv] at hpd)⟩ }
  have hle : oPi α E ≤ P := by
    refine iSup₂_le fun N hN => ?_
    intro y hy
    refine ⟨hN.1 hy, fun p hp hpd => ?_⟩
    exact hN.2.2 ⟨hp, hpd.trans (Subgroup.orderOf_dvd_natCard N hy)⟩
  exact hle hx

end GenericFinite

section Gen

variable {X : Type} [Group X]

theorem uc22pwt_gen_comp {U A B : Subgroup X} {w₁ w₂ w : X}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hUsplit : U ≤ (U ⊓ A) ⊔ (U ⊓ B))
    (hw₁ : w₁ ∈ A) (hw₂ : w₂ ∈ B) (hw2 : w₁ ^ 2 = 1) (hw : w = w₁ * w₂)
    (hgen : (normalizer ((U ⊓ A : Subgroup X) : Set X) ⊓ A) ⊔ zpowers w₁ = A)
    (hNC : ∀ K : Subgroup X, K ≤ A → (∀ x ∈ A, ∀ y ∈ K, x * y * x⁻¹ ∈ K) →
      (∀ y ∈ K, ∀ x ∈ A, y * x = x * y) ∨ A ≤ K)
    (hnc : ∃ x ∈ normalizer ((U ⊓ A : Subgroup X) : Set X) ⊓ A, ∃ y ∈ A, x * y ≠ y * x) :
    A ≤ normalizer (U : Set X) ⊔ zpowers w := by
  have hwH : w ∈ normalizer (U : Set X) ⊔ zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  refine uc22pwt_gen_of_normal (N := normalizer ((U ⊓ A : Subgroup X) : Set X) ⊓ A) (w := w₁)
    inf_le_right hw₁ hw2 hgen hNC hnc ?_ ?_
  · intro x hx
    exact Subgroup.mem_sup_left (uc22pwt_mem_normalizer_of_part hcomm hUsplit hx.2 hx.1)
  · intro n hn
    have hnN : n ∈ normalizer (U : Set X) := uc22pwt_mem_normalizer_of_part hcomm hUsplit hn.2 hn.1
    have e : w₁ * n * w₁⁻¹ = w * n * w⁻¹ := by
      have hc : w₂ * n = n * w₂ := (hcomm n hn.2 w₂ hw₂).symm
      rw [hw, mul_inv_rev]
      calc w₁ * n * w₁⁻¹ = w₁ * (n * w₂ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (w₂ * n * w₂⁻¹) * w₁⁻¹ := by rw [hc]
        _ = w₁ * w₂ * n * (w₂⁻¹ * w₁⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwH (Subgroup.mem_sup_left hnN)) (inv_mem hwH)

end Gen

section InvSub

variable {X : Type} [Group X]

@[expose] def uc22pwtInvSub (M : Subgroup X) (hM : IsMulCommutative M) (w : X) : Subgroup X where
  carrier := {x | x ∈ M ∧ w * x * w⁻¹ = x⁻¹}
  mul_mem' := by
    rintro x y ⟨hx, hxw⟩ ⟨hy, hyw⟩
    refine ⟨M.mul_mem hx hy, ?_⟩
    haveI := hM
    have hc : Commute x y := mul_comm_of_mem_isMulCommutative M hx hy
    have e : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
    rw [e, hxw, hyw, mul_inv_rev]
    exact hc.inv_inv.eq
  one_mem' := ⟨M.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxw⟩
    refine ⟨M.inv_mem hx, ?_⟩
    have e : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
    rw [e, hxw]

theorem mem_uc22pwtInvSub {M : Subgroup X} {hM : IsMulCommutative M} {w x : X} :
    x ∈ uc22pwtInvSub M hM w ↔ x ∈ M ∧ w * x * w⁻¹ = x⁻¹ :=
  Iff.rfl

end InvSub

section Transport

variable {X Γ : Type} [Group X] [Group Γ]

namespace UC22pwtCtx

variable {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} (C : UC22pwtCtx ρ τ U A₁ A₂)

include C

theorem gen₂ {w₁ : X}
    (hgen : (normalizer ((U ⊓ A₁ : Subgroup X) : Set X) ⊓ A₁) ⊔ zpowers w₁ = A₁) :
    (normalizer ((U ⊓ A₂ : Subgroup X) : Set X) ⊓ A₂) ⊔ zpowers (ρ τ w₁) = A₂ := by
  have hmapA : A₁.map (ρ τ).toMonoidHom = A₂ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact C.mem₂ hy
    · intro hx
      exact ⟨ρ τ⁻¹ x, C.mem₁_inv_iff.2 hx, uc22pwt_apply_inv_apply ρ τ x⟩
  have hmapN : (normalizer ((U ⊓ A₁ : Subgroup X) : Set X) ⊓ A₁).map (ρ τ).toMonoidHom =
      normalizer ((U ⊓ A₂ : Subgroup X) : Set X) ⊓ A₂ := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyN, hyA⟩, rfl⟩
      exact ⟨uc22pwt_mem_normalizer_aut (ρ τ) (fun z => C.swap_U₁.symm) hyN, C.mem₂ hyA⟩
    · rintro ⟨hxN, hxA⟩
      refine ⟨ρ τ⁻¹ x, ⟨?_, C.mem₁_inv_iff.2 hxA⟩, uc22pwt_apply_inv_apply ρ τ x⟩
      exact uc22pwt_mem_normalizer_aut (ρ τ⁻¹) (fun z => C.swap_U₂_inv.symm) hxN
  calc (normalizer ((U ⊓ A₂ : Subgroup X) : Set X) ⊓ A₂) ⊔ zpowers (ρ τ w₁)
      = (normalizer ((U ⊓ A₁ : Subgroup X) : Set X) ⊓ A₁).map (ρ τ).toMonoidHom ⊔
          (zpowers w₁).map (ρ τ).toMonoidHom := by
        rw [hmapN, MonoidHom.map_zpowers]
        rfl
    _ = ((normalizer ((U ⊓ A₁ : Subgroup X) : Set X) ⊓ A₁) ⊔ zpowers w₁).map (ρ τ).toMonoidHom :=
        (Subgroup.map_sup _ _ _).symm
    _ = A₂ := by rw [hgen, hmapA]

theorem nc₂ (hnc : ∀ K : Subgroup X, K ≤ A₁ → (∀ x ∈ A₁, ∀ y ∈ K, x * y * x⁻¹ ∈ K) →
      (∀ y ∈ K, ∀ x ∈ A₁, y * x = x * y) ∨ A₁ ≤ K) :
    ∀ K : Subgroup X, K ≤ A₂ → (∀ x ∈ A₂, ∀ y ∈ K, x * y * x⁻¹ ∈ K) →
      (∀ y ∈ K, ∀ x ∈ A₂, y * x = x * y) ∨ A₂ ≤ K := by
  intro K hKA hKn
  have hK'A : K.comap (ρ τ).toMonoidHom ≤ A₁ := fun y hy => (C.swap₁ y).2 (hKA hy)
  have hK'n : ∀ x ∈ A₁, ∀ y ∈ K.comap (ρ τ).toMonoidHom,
      x * y * x⁻¹ ∈ K.comap (ρ τ).toMonoidHom := by
    intro x hx y hy
    show ρ τ (x * y * x⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact hKn _ (C.mem₂ hx) _ hy
  rcases hnc _ hK'A hK'n with hc | hle
  · left
    intro y hy x hx
    have hy' : ρ τ⁻¹ y ∈ K.comap (ρ τ).toMonoidHom := by
      show ρ τ (ρ τ⁻¹ y) ∈ K
      rwa [uc22pwt_apply_inv_apply]
    have h1 := hc _ hy' _ (C.mem₁_inv_iff.2 hx)
    have h2 := congrArg (ρ τ) h1
    rwa [map_mul, map_mul, uc22pwt_apply_inv_apply, uc22pwt_apply_inv_apply] at h2
  · right
    intro x hx
    have h3 : ρ τ (ρ τ⁻¹ x) ∈ K := hle (C.mem₁_inv_iff.2 hx)
    rwa [uc22pwt_apply_inv_apply] at h3

end UC22pwtCtx

end Transport

section ElemLemmas

variable {X Γ : Type} [Group X] [Group Γ] [Finite X]

namespace UC22pwtElem

variable {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} {C : UC22pwtCtx ρ τ U A₁ A₂}
  {h w₁ : X} {m a b : ℕ} {α : Set ℕ} (El : UC22pwtElem C h w₁ m a b α)

include El

theorem ord' : orderOf (ρ τ h) = m := by
  rw [MulEquiv.orderOf_eq (ρ τ) h]
  exact El.ord

theorem h_noncentral : ∃ y ∈ A₁, h * y ≠ y * h := by
  by_contra hcon
  have hcon' : ∀ y ∈ A₁, h * y = y * h := fun y hy => by_contra fun hne => hcon ⟨y, hy, hne⟩
  have hcen : (⟨h, El.h_mem⟩ : ↥A₁) ∈ Subgroup.center ↥A₁ := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (hcon' z z.2).symm
  have hdvd : orderOf (⟨h, El.h_mem⟩ : ↥A₁) ∣ Nat.card (Subgroup.center ↥A₁) :=
    Subgroup.orderOf_dvd_natCard _ hcen
  have hord : orderOf (⟨h, El.h_mem⟩ : ↥A₁) = m := by
    rw [← Subgroup.orderOf_coe]
    exact El.ord
  obtain ⟨p, hp, hpm⟩ := El.ex
  have hmdvd : m ∣ Nat.card (Subgroup.center ↥A₁) := by
    rw [← hord]
    exact hdvd
  exact El.Z p hp hpm (hpm.trans hmdvd)

theorem pair : UC22pwtPair h (ρ τ h) m a b α where
  comm := C.comm h El.h_mem _ (C.mem₂ El.h_mem)
  ord := El.ord
  ord' := El.ord'
  disj := by
    intro i j hij
    have hy1 : h ^ i ∈ A₁ := zpow_mem El.h_mem i
    have hy2 : h ^ i ∈ A₂ := hij ▸ zpow_mem (C.mem₂ El.h_mem) j
    have hcen : (⟨h ^ i, hy1⟩ : ↥A₁) ∈ Subgroup.center ↥A₁ := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (C.comm' _ hy2 z z.2).symm
    have hdvd : orderOf (⟨h ^ i, hy1⟩ : ↥A₁) ∣ Nat.card (Subgroup.center ↥A₁) :=
      Subgroup.orderOf_dvd_natCard _ hcen
    have hord : orderOf (⟨h ^ i, hy1⟩ : ↥A₁) = orderOf (h ^ i) :=
      (Subgroup.orderOf_coe (⟨h ^ i, hy1⟩ : ↥A₁)).symm
    have hhm : h ^ m = 1 := by
      rw [← El.ord]
      exact pow_orderOf_eq_one h
    have hm : orderOf (h ^ i) ∣ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hhm, one_zpow]
    by_contra hne
    have hne1 : orderOf (h ^ i) ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.1 h1)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
    exact El.Z p hp (hpd.trans hm) (hpd.trans (hord ▸ hdvd))
  sqf := El.sqf
  odd := El.odd
  ab := El.ab
  cop := El.cop
  pr := El.pr

theorem h_norm₁ : h ∈ normalizer ((U ⊓ A₁ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => (El.hnorm u hu).1, fun hu => ?_⟩
  have h1 := (El.hnorm _ hu).2
  have e : h⁻¹ * (h * u * h⁻¹) * h = u := by group
  rwa [e] at h1

theorem h_norm : h ∈ normalizer (U : Set X) :=
  uc22pwt_mem_normalizer_of_part C.comm C.Usplit El.h_mem El.h_norm₁

theorem h'_norm₂ : ρ τ h ∈ normalizer ((U ⊓ A₂ : Subgroup X) : Set X) :=
  uc22pwt_mem_normalizer_aut (ρ τ) (fun y => C.swap_U₁.symm) El.h_norm₁

theorem h'_norm : ρ τ h ∈ normalizer (U : Set X) :=
  uc22pwt_mem_normalizer_of_part C.comm' (by rw [sup_comm]; exact C.Usplit) (C.mem₂ El.h_mem)
    El.h'_norm₂

theorem inv_pow {g : Γ} (hg : g ∈ uc22pwtStab2 ρ A₁ A₂) (k : ℕ) :
    ρ g (h ^ k) ∈ zpowers (h ^ k) ⊔ (U ⊓ A₁) := by
  obtain ⟨y, hy, u, hu, hyu⟩ := uc22pws_exists_mul_of_mem_sup
    (Subgroup.zpowers_le.2 El.h_norm₁) (El.hinv g hg)
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨u', hu', hk⟩ := uc22pwt_pow_mul_mem El.h_norm₁ s hu k
  rw [map_pow, hyu, hk]
  refine Subgroup.mul_mem_sup ?_ hu'
  exact Subgroup.mem_zpowers_iff.2 ⟨s, by rw [← zpow_natCast, ← zpow_mul, mul_comm]⟩

theorem inv_pow' {g : Γ} (hg : g ∈ uc22pwtStab2 ρ A₁ A₂) (k : ℕ) :
    ρ g ((ρ τ h) ^ k) ∈ zpowers ((ρ τ h) ^ k) ⊔ (U ⊓ A₂) := by
  have h1 := El.inv_pow (C.stab_conj hg) k
  have e : ρ g ((ρ τ h) ^ k) = ρ τ (ρ (τ⁻¹ * g * τ) (h ^ k)) := by
    rw [← map_pow, uc22pwt_apply_conj]
  rw [e]
  have hle : zpowers (h ^ k) ⊔ (U ⊓ A₁) ≤
      (zpowers ((ρ τ h) ^ k) ⊔ (U ⊓ A₂)).comap (ρ τ).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show ρ τ (h ^ k) ∈ zpowers ((ρ τ h) ^ k) ⊔ (U ⊓ A₂)
      rw [map_pow]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · intro u hu
      exact Subgroup.mem_sup_right (C.swap_U₁.2 hu)
  exact hle h1

end UC22pwtElem

end ElemLemmas

theorem uc22pwt_diag_identity {X : Type} [Group X] {P P' Q Q' : X}
    (hc : P * (Q' * Q⁻¹) = (Q' * Q⁻¹) * P) :
    P' * Q' * (P * Q)⁻¹ = (P' * P⁻¹) * (Q' * Q⁻¹) := by
  have h4 : (Q' * Q⁻¹) * P⁻¹ = P⁻¹ * (Q' * Q⁻¹) := by
    calc (Q' * Q⁻¹) * P⁻¹ = P⁻¹ * (P * (Q' * Q⁻¹)) * P⁻¹ := by group
      _ = P⁻¹ * ((Q' * Q⁻¹) * P) * P⁻¹ := by rw [hc]
      _ = P⁻¹ * (Q' * Q⁻¹) := by group
  calc P' * Q' * (P * Q)⁻¹ = P' * ((Q' * Q⁻¹) * P⁻¹) := by group
    _ = P' * (P⁻¹ * (Q' * Q⁻¹)) := by rw [h4]
    _ = P' * P⁻¹ * (Q' * Q⁻¹) := by group

theorem uc22pwt_diag_identity_tau {X : Type} [Group X] {P Q u : X} (hPQ : P * Q = Q * P)
    (hQu : Q * u = u * Q) : Q * (u * P) * (P * Q)⁻¹ = u := by
  have h1 : P * Q⁻¹ = Q⁻¹ * P := by
    calc P * Q⁻¹ = Q⁻¹ * (Q * P) * Q⁻¹ := by group
      _ = Q⁻¹ * (P * Q) * Q⁻¹ := by rw [hPQ]
      _ = Q⁻¹ * P := by group
  calc Q * (u * P) * (P * Q)⁻¹ = Q * u * (P * Q⁻¹) * P⁻¹ := by group
    _ = Q * u * (Q⁻¹ * P) * P⁻¹ := by rw [h1]
    _ = (Q * u) * Q⁻¹ := by group
    _ = (u * Q) * Q⁻¹ := by rw [hQu]
    _ = u := by group

theorem uc22pwt_closure_mul {X Γ : Type} [Group X] [Group Γ] {U : Subgroup X} (ρ : Γ →* MulAut X)
    (hU : ∀ (g : Γ) (x : X), x ∈ U ↔ ρ g x ∈ U) (d : X) {g g' : Γ} (hg : ρ g d * d⁻¹ ∈ U)
    (hg' : ρ g' d * d⁻¹ ∈ U) : ρ (g * g') d * d⁻¹ ∈ U := by
  have e : ρ (g * g') d * d⁻¹ = ρ g (ρ g' d * d⁻¹) * (ρ g d * d⁻¹) := by
    rw [uc22pwt_apply_mul, map_mul (ρ g), map_inv (ρ g)]
    group
  rw [e]
  exact U.mul_mem ((hU g _).1 hg') hg

section Diag

variable {X Γ : Type} [Group X] [Group Γ] [Finite X]

namespace UC22pwtElem

variable {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} {C : UC22pwtCtx ρ τ U A₁ A₂}
  {h w₁ : X} {m a b : ℕ} {α : Set ℕ} (El : UC22pwtElem C h w₁ m a b α)

include El

theorem diag_stab {g : Γ} (hg : g ∈ uc22pwtStab2 ρ A₁ A₂) :
    ρ g (h ^ b * (ρ τ h) ^ b) * (h ^ b * (ρ τ h) ^ b)⁻¹ ∈ U := by
  have h1 := El.halpha g hg
  have h2 := El.halpha _ (C.stab_conj hg)
  have hpow : (ρ τ h) ^ b = ρ τ (h ^ b) := (map_pow (ρ τ) h b).symm
  have h3 : ρ g ((ρ τ h) ^ b) * ((ρ τ h) ^ b)⁻¹ ∈ U ⊓ A₂ := by
    have e : ρ g ((ρ τ h) ^ b) * ((ρ τ h) ^ b)⁻¹ =
        ρ τ (ρ (τ⁻¹ * g * τ) (h ^ b) * (h ^ b)⁻¹) := by
      rw [hpow, uc22pwt_apply_conj, map_mul (ρ τ), map_inv (ρ τ)]
    rw [e]
    exact C.swap_U₁.2 h2
  have hc : h ^ b * (ρ g ((ρ τ h) ^ b) * ((ρ τ h) ^ b)⁻¹) =
      (ρ g ((ρ τ h) ^ b) * ((ρ τ h) ^ b)⁻¹) * h ^ b :=
    C.comm _ (Subgroup.pow_mem _ El.h_mem b) _ h3.2
  have e : ρ g (h ^ b * (ρ τ h) ^ b) * (h ^ b * (ρ τ h) ^ b)⁻¹ =
      (ρ g (h ^ b) * (h ^ b)⁻¹) * (ρ g ((ρ τ h) ^ b) * ((ρ τ h) ^ b)⁻¹) := by
    rw [map_mul]
    exact uc22pwt_diag_identity hc
  rw [e]
  exact U.mul_mem h1.1 h3.1

theorem diag_tau : ρ τ (h ^ b * (ρ τ h) ^ b) * (h ^ b * (ρ τ h) ^ b)⁻¹ ∈ U := by
  have h1 := El.halpha (τ * τ) C.stab_ττ
  have hpow : (ρ τ h) ^ b = ρ τ (h ^ b) := (map_pow (ρ τ) h b).symm
  obtain ⟨u₁, hu₁mem, hu₁⟩ : ∃ u ∈ U ⊓ A₁, ρ (τ * τ) (h ^ b) = u * h ^ b :=
    ⟨_, h1, (inv_mul_cancel_right _ _).symm⟩
  have e : ρ τ (h ^ b * (ρ τ h) ^ b) = (ρ τ h) ^ b * (u₁ * h ^ b) := by
    rw [map_mul, hpow, ← uc22pwt_apply_mul, hu₁, ← hpow]
  rw [e]
  have hPQ : h ^ b * (ρ τ h) ^ b = (ρ τ h) ^ b * h ^ b :=
    C.comm _ (Subgroup.pow_mem _ El.h_mem b) _ (Subgroup.pow_mem _ (C.mem₂ El.h_mem) b)
  have hQu : (ρ τ h) ^ b * u₁ = u₁ * (ρ τ h) ^ b :=
    (C.comm u₁ hu₁mem.2 _ (Subgroup.pow_mem _ (C.mem₂ El.h_mem) b)).symm
  rw [uc22pwt_diag_identity_tau hPQ hQu]
  exact hu₁mem.1

theorem diag_all (g : Γ) : ρ g (h ^ b * (ρ τ h) ^ b) * (h ^ b * (ρ τ h) ^ b)⁻¹ ∈ U := by
  rcases C.perm g with hg | hg
  · exact El.diag_stab hg
  · have e : g = τ * (τ⁻¹ * g) := by group
    rw [e]
    exact uc22pwt_closure_mul ρ C.Uinv _ El.diag_tau (El.diag_stab hg)

theorem invariant (g : Γ) :
    ∀ x ∈ uc22pwtE h (ρ τ h) a b, ρ g x ∈ uc22pwtE h (ρ τ h) a b ⊔ U := by
  set E := uc22pwtE h (ρ τ h) a b with hE
  have hhaE : zpowers (h ^ a) ≤ E := Subgroup.zpowers_le.2 (uc22pwtE_ha_mem _ _ a b)
  have hha'E : zpowers ((ρ τ h) ^ a) ≤ E := Subgroup.zpowers_le.2 (uc22pwtE_ha'_mem _ _ a b)
  have hdE : h ^ b * (ρ τ h) ^ b ∈ E := uc22pwtE_d_mem _ _ a b
  have hgd : ∀ g : Γ, ρ g (h ^ b * (ρ τ h) ^ b) ∈ E ⊔ U := by
    intro g
    have h1 := El.diag_all g
    have e : ρ g (h ^ b * (ρ τ h) ^ b) = (ρ g (h ^ b * (ρ τ h) ^ b) * (h ^ b * (ρ τ h) ^ b)⁻¹) *
        (h ^ b * (ρ τ h) ^ b) := (inv_mul_cancel_right _ _).symm
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hdE)
  have hgen : ∀ g : Γ, (g ∈ uc22pwtStab2 ρ A₁ A₂ ∨ g = τ) → ∀ x ∈ E, ρ g x ∈ E ⊔ U := by
    intro g hg
    have hh : ρ g (h ^ a) ∈ E ⊔ U := by
      rcases hg with hg | hg
      · exact sup_le_sup hhaE inf_le_left (El.inv_pow hg a)
      · rw [hg, map_pow]
        exact Subgroup.mem_sup_left (uc22pwtE_ha'_mem h (ρ τ h) a b)
    have hh' : ρ g ((ρ τ h) ^ a) ∈ E ⊔ U := by
      rcases hg with hg | hg
      · exact sup_le_sup hha'E inf_le_left (El.inv_pow' hg a)
      · rw [hg, ← map_pow (ρ τ) h a, ← uc22pwt_apply_mul]
        exact sup_le_sup hhaE inf_le_left (El.inv_pow C.stab_ττ a)
    have hle : E ≤ (E ⊔ U).comap (ρ g).toMonoidHom :=
      sup_le (sup_le (Subgroup.zpowers_le.2 hh) (Subgroup.zpowers_le.2 hh'))
        (Subgroup.zpowers_le.2 (hgd g))
    exact fun x hx => hle hx
  have hmul : ∀ g g' : Γ, (∀ x ∈ E, ρ g x ∈ E ⊔ U) → (∀ x ∈ E, ρ g' x ∈ E ⊔ U) →
      ∀ x ∈ E, ρ (g * g') x ∈ E ⊔ U := by
    intro g g' hg hg' x hx
    rw [uc22pwt_apply_mul]
    have hF : E ⊔ U ≤ (E ⊔ U).comap (ρ g).toMonoidHom :=
      sup_le (fun y hy => hg y hy) (fun u hu => Subgroup.mem_sup_right ((C.Uinv g u).1 hu))
    exact hF (hg' x hx)
  rcases C.perm g with hg | hg
  · exact hgen g (Or.inl hg)
  · have e : g = τ * (τ⁻¹ * g) := by group
    rw [e]
    exact hmul τ _ (hgen τ (Or.inr rfl)) (hgen _ (Or.inl hg))

theorem alpha_clause (g : Γ) :
    ∀ x ∈ oPi α (uc22pwtE h (ρ τ h) a b), ρ g x * x⁻¹ ∈ U := by
  intro x hx
  obtain ⟨hxE, hxα⟩ := uc22pwt_mem_of_mem_oPi El.pair.isMulCommutative_E hx
  have hxd : x ∈ zpowers (h ^ b * (ρ τ h) ^ b) := El.pair.mem_diag_of_primes hxE hxα
  have hdfix : h ^ b * (ρ τ h) ^ b ∈ uc22pwtFix U (ρ g) :=
    mem_uc22pwtFix.2 ⟨mul_mem (Subgroup.pow_mem _ El.h_norm b) (Subgroup.pow_mem _ El.h'_norm b),
      El.diag_all g⟩
  exact (mem_uc22pwtFix.1 (Subgroup.zpowers_le.2 hdfix hxd)).2

theorem involution : ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ uc22pwtE h (ρ τ h) a b, w * x * w⁻¹ = x⁻¹) ∧
    normalizer (U : Set X) ⊔ Subgroup.zpowers w = ⊤ := by
  have hw₂ : ρ τ w₁ ∈ A₂ := C.mem₂ El.w_mem
  have hc : Commute w₁ (ρ τ w₁) := C.comm w₁ El.w_mem _ hw₂
  have hw₂sq : (ρ τ w₁) ^ 2 = 1 := by rw [← map_pow, El.w_sq, map_one]
  refine ⟨w₁ * ρ τ w₁, ?_, ?_, ?_⟩
  · rw [hc.mul_pow, El.w_sq, hw₂sq, one_mul]
  · have hwh : (w₁ * ρ τ w₁) * h * (w₁ * ρ τ w₁)⁻¹ = h⁻¹ := by
      have hcomm : ρ τ w₁ * h = h * ρ τ w₁ := (C.comm h El.h_mem _ hw₂).symm
      calc (w₁ * ρ τ w₁) * h * (w₁ * ρ τ w₁)⁻¹ = w₁ * (ρ τ w₁ * h) * (ρ τ w₁)⁻¹ * w₁⁻¹ := by group
        _ = w₁ * (h * ρ τ w₁) * (ρ τ w₁)⁻¹ * w₁⁻¹ := by rw [hcomm]
        _ = w₁ * h * w₁⁻¹ := by group
        _ = h⁻¹ := El.w_inv
    have hwh' : (w₁ * ρ τ w₁) * ρ τ h * (w₁ * ρ τ w₁)⁻¹ = (ρ τ h)⁻¹ := by
      have hcomm : Commute w₁ (ρ τ h) := C.comm w₁ El.w_mem _ (C.mem₂ El.h_mem)
      have h2 : ρ τ w₁ * ρ τ h * (ρ τ w₁)⁻¹ = (ρ τ h)⁻¹ := by
        have h3 := congrArg (ρ τ) El.w_inv
        simpa only [map_mul, map_inv] using h3
      calc (w₁ * ρ τ w₁) * ρ τ h * (w₁ * ρ τ w₁)⁻¹
          = w₁ * (ρ τ w₁ * ρ τ h * (ρ τ w₁)⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (ρ τ h)⁻¹ * w₁⁻¹ := by rw [h2]
        _ = (ρ τ h)⁻¹ := by rw [hcomm.inv_right.eq]; group
    have hM : IsMulCommutative ↥(zpowers h ⊔ zpowers (ρ τ h)) := El.pair.isMulCommutative_M
    have hle : zpowers h ⊔ zpowers (ρ τ h) ≤ uc22pwtInvSub (zpowers h ⊔ zpowers (ρ τ h)) hM (w₁ * ρ τ w₁) :=
      sup_le (Subgroup.zpowers_le.2 (mem_uc22pwtInvSub.2
          ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers h), hwh⟩))
        (Subgroup.zpowers_le.2 (mem_uc22pwtInvSub.2
          ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers _), hwh'⟩))
    intro x hx
    exact (mem_uc22pwtInvSub.1 (hle (uc22pwtE_le_M h (ρ τ h) a b hx))).2
  · refine eq_top_iff.2 ?_
    rw [← C.sup]
    have hA₁ : A₁ ≤ normalizer (U : Set X) ⊔ zpowers (w₁ * ρ τ w₁) :=
      uc22pwt_gen_comp (U := U) (A := A₁) (B := A₂) (w₁ := w₁) (w₂ := ρ τ w₁) C.comm C.Usplit
        El.w_mem hw₂ El.w_sq rfl El.w_gen El.nc
        ⟨h, Subgroup.mem_inf.2 ⟨El.h_norm₁, El.h_mem⟩, El.h_noncentral⟩
    have hA₂ : A₂ ≤ normalizer (U : Set X) ⊔ zpowers (w₁ * ρ τ w₁) := by
      refine uc22pwt_gen_comp (U := U) (A := A₂) (B := A₁) (w₁ := ρ τ w₁) (w₂ := w₁) C.comm'
        (by rw [sup_comm]; exact C.Usplit) hw₂ El.w_mem hw₂sq hc.eq (C.gen₂ El.w_gen)
        (C.nc₂ El.nc) ?_
      obtain ⟨y₀, hy₀, hne⟩ := El.h_noncentral
      refine ⟨ρ τ h, Subgroup.mem_inf.2 ⟨El.h'_norm₂, C.mem₂ El.h_mem⟩, ρ τ y₀, C.mem₂ hy₀,
        fun heq => hne ?_⟩
      apply (ρ τ).injective
      rw [map_mul, map_mul]
      exact heq
    exact sup_le hA₁ hA₂

end UC22pwtElem

end Diag

theorem uc22pwt_core (hR1 : uc22pwCartanRankOne) {X : Type} [Group X] [Finite X] {Γ : Type} [Group Γ]
    (hΓ : IsPGroup 2 Γ) (ρ : Γ →* MulAut X) (τ : Γ) {U A₁ A₂ : Subgroup X}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    (hτ₁ : ∀ x, x ∈ A₁ ↔ ρ τ x ∈ A₂) (hτ₂ : ∀ x, x ∈ A₂ ↔ ρ τ x ∈ A₁)
    (hperm : ∀ g : Γ, ((∀ x, x ∈ A₁ ↔ ρ g x ∈ A₁) ∧ (∀ x, x ∈ A₂ ↔ ρ g x ∈ A₂)) ∨
      ((∀ x, x ∈ A₁ ↔ ρ (τ⁻¹ * g) x ∈ A₁) ∧ (∀ x, x ∈ A₂ ↔ ρ (τ⁻¹ * g) x ∈ A₂)))
    (hUinv : ∀ (g : Γ) (x : X), x ∈ U ↔ ρ g x ∈ U) (hUsplit : U ≤ (U ⊓ A₁) ⊔ (U ⊓ A₂))
    (hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ A₁) A₁)
    (hq : CFSG.Open.IsQuasisimple ↥A₁) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz ↥A₁ n ∨ IsL2 ↥A₁ n ∨ IsSU3 ↥A₁ n)
    (hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥A₁))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, E ≤ normalizer (U : Set X) ∧ IsMulCommutative E ∧ Odd (Nat.card E) ∧
      (∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2) ∧
      piSet E = etaSet n ∧ (∀ g : Γ, ∀ x ∈ E, ρ g x ∈ E ⊔ U) ∧
      (∀ g : Γ, ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ρ g x * x⁻¹ ∈ U) ∧
      ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
        normalizer (U : Set X) ⊔ Subgroup.zpowers w = ⊤ := by
  have C : UC22pwtCtx ρ τ U A₁ A₂ := ⟨hcomm, hsup, hτ₁, hτ₂, hperm, hUinv, hUsplit⟩
  obtain ⟨h, w₁, m, a, b, El, hpr⟩ := uc22pwt_elem_of_input hR1 hΓ C hUsyl hq hn hsh hZ hm' hnem
  have P := El.pair
  refine ⟨uc22pwtE h (ρ τ h) a b, ?_, P.isMulCommutative_E, P.odd_card_E, P.rank_E, ?_,
    El.invariant, El.alpha_clause, El.involution⟩
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ El.h_norm a)
    · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ El.h'_norm a)
    · exact Subgroup.zpowers_le.2
        (mul_mem (Subgroup.pow_mem _ El.h_norm b) (Subgroup.pow_mem _ El.h'_norm b))
  · rw [P.piSet_E]
    ext p
    simp only [etaSet, Set.mem_setOf_eq]
    exact ⟨fun hp => ⟨hp.1, (hpr p hp.1).1 hp.2⟩, fun hp => ⟨hp.1, (hpr p hp.1).2 hp.2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
