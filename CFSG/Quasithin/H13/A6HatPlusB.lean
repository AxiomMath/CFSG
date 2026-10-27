module

public import CFSG.Quasithin.H13.U3L15A
public import CFSG.Quasithin.H13.A6HatPlusA
public import CFSG.Quasithin.H13.A6S13721a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def K4pL : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5]

@[expose] def A4pL : List (Perm (Fin 6)) :=
  K4pL ++ K4pL.map (· * U3.a6s3) ++ K4pL.map (· * (U3.a6s3 * U3.a6s3))

@[expose] def invCandL : List (Perm (Fin 6)) :=
  [swap 1 2 * swap 4 5, swap 1 3 * swap 4 5, swap 2 3 * swap 4 5, swap 0 2 * swap 1 3,
    swap 0 3 * swap 1 2, swap 0 4 * swap 1 5, swap 0 5 * swap 1 4, swap 2 4 * swap 3 5,
    swap 2 5 * swap 3 4]

theorem hatK4L_comm : ∀ σ ∈ K4L, ∀ τ ∈ K4L, σ * τ = τ * σ := by decide +kernel

theorem A4_conj_K4L : ∀ κ ∈ K4L, ∀ σ : Perm (Fin 6), σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1 →
    σ * κ * σ⁻¹ ∈ K4L := by
  decide +kernel

theorem A4_cube_K4L : ∀ σ : Perm (Fin 6), σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1 →
    σ ∈ K4L ∨ (σ * σ * σ = 1 ∧ ∃ τ ∈ invCandL, Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹) := by
  decide +kernel

theorem A4_gen_K4L : ∀ σ : Perm (Fin 6), σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1 →
    σ ∈ K4L ∨ σ * (swap 0 1 * swap 1 2)⁻¹ ∈ K4L ∨ σ * (swap 0 1 * swap 1 2) ∈ K4L := by
  decide +kernel

theorem DA6_K4L : ∀ σ : Perm (Fin 6), InD6 σ ∧ Perm.sign σ = 1 →
    (σ ∈ K4L ∨ σ * (swap 0 1 * swap 4 5)⁻¹ ∈ K4L) ∧ σ * σ ∈ K4L := by
  decide +kernel

theorem K4pL_one : (1 : Perm (Fin 6)) ∈ K4pL := List.mem_cons_self

theorem K4pL_mul : ∀ σ ∈ K4pL, ∀ τ ∈ K4pL, σ * τ ∈ K4pL := by decide +kernel

theorem K4pL_inv : ∀ σ ∈ K4pL, σ⁻¹ ∈ K4pL := by decide +kernel

theorem K4pL_sq : ∀ σ ∈ K4pL, σ * σ = 1 := by decide +kernel

theorem K4pL_comm : ∀ σ ∈ K4pL, ∀ τ ∈ K4pL, σ * τ = τ * σ := by decide +kernel

theorem A4pL_one : (1 : Perm (Fin 6)) ∈ A4pL := by decide +kernel

theorem A4pL_mul : ∀ σ ∈ A4pL, ∀ τ ∈ A4pL, σ * τ ∈ A4pL := by decide +kernel

theorem A4pL_inv : ∀ σ ∈ A4pL, σ⁻¹ ∈ A4pL := by decide +kernel

theorem A4pL_conj : ∀ σ ∈ A4pL, ∀ κ ∈ K4pL, σ * κ * σ⁻¹ ∈ K4pL := by decide +kernel

theorem A4pL_cube : ∀ σ ∈ A4pL, σ ∈ K4pL ∨
    (σ * σ * σ = 1 ∧ ∃ τ ∈ invCandL, Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹) := by
  decide +kernel

theorem A4pL_gen : ∀ σ ∈ A4pL, σ ∈ K4pL ∨ σ * U3.a6s3⁻¹ ∈ K4pL ∨ σ * U3.a6s3 ∈ K4pL := by
  decide +kernel

theorem DA6_K4pL : ∀ σ : Perm (Fin 6), InD6 σ ∧ Perm.sign σ = 1 →
    (σ ∈ K4pL ∨ σ * (swap 0 2 * swap 1 3)⁻¹ ∈ K4pL) ∧ σ * σ ∈ K4pL := by
  decide +kernel

theorem stab_W2_facts : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 ∧
    (∀ x : P6, InW2 x → InW2 (act4f σ x)) → σ ^ 12 = 1 ∧ (σ ^ 3 = 1 → σ ∈ A4pL) := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem hat_mk_mem_center {y : ↥L}
    (hy : (y : G) ∈ Subgroup.centralizer (V : Set G)) :
    (y : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨x, hx, hxy⟩ := S.centralizer_le_o2Z ⟨y.2, hy⟩
  have e : x = y := Subtype.ext hxy
  subst e
  exact hx

omit [Finite G] S in
theorem hat_cube_center (hhat : IsHatA6 L) {ζ : ↥L ⧸ CFSG.pCore 2 ↥L}
    (hζ : ζ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) : ζ ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) (x := ⟨ζ, hζ⟩)
  rw [hhat.2.1] at h
  exact congrArg Subtype.val h

omit [Finite G] S in
theorem cube_mem_of_o2Z (hhat : IsHatA6 L) {z : G} (hz : z ∈ o2Z L) : z ^ 3 ∈ pCoreOf 2 L := by
  obtain ⟨z', hz', rfl⟩ := hz
  have h := hat_cube_center hhat hz'
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    mem_pCore_iff] at h
  simpa using h

omit [Finite G] S in
theorem mem_pCoreOf_of_o2Z (hhat : IsHatA6 L) {z : G} (hz : z ∈ o2Z L) {k : ℕ}
    (hk : z ^ 2 ^ k = 1) : z ∈ pCoreOf 2 L := by
  obtain ⟨z', hz', rfl⟩ := hz
  have h3 := hat_cube_center hhat hz'
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) z') ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : z' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by decide)
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) z') ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rwa [hcop.gcd_eq_one] at this
  have h := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff] at h
  exact h

omit S in
theorem hat_mk_comm (S : Setting4 G T L V) (hhat : IsHatA6 L)
    {a b : ↥L} (hab : S.frame.ρ ⟨a, S.frame.L_le a.2⟩ * S.frame.ρ ⟨b, S.frame.L_le b.2⟩ =
      S.frame.ρ ⟨b, S.frame.L_le b.2⟩ * S.frame.ρ ⟨a, S.frame.L_le a.2⟩)
    (ha : S.frame.ρ ⟨a, S.frame.L_le a.2⟩ * S.frame.ρ ⟨a, S.frame.L_le a.2⟩ = 1) :
    (a : ↥L ⧸ CFSG.pCore 2 ↥L) * (b : ↥L ⧸ CFSG.pCore 2 ↥L) =
      (b : ↥L ⧸ CFSG.pCore 2 ↥L) * (a : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  set α : ↥L ⧸ CFSG.pCore 2 ↥L := (a : ↥L ⧸ CFSG.pCore 2 ↥L) with hα
  set β : ↥L ⧸ CFSG.pCore 2 ↥L := (b : ↥L ⧸ CFSG.pCore 2 ↥L) with hβ
  have hcC : ((a * b * a⁻¹ * b⁻¹ : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine (S.rho_eq_one_iff (⟨a, S.frame.L_le a.2⟩ * ⟨b, S.frame.L_le b.2⟩ *
      (⟨a, S.frame.L_le a.2⟩)⁻¹ * (⟨b, S.frame.L_le b.2⟩)⁻¹)).1 ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have haC : ((a * a : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine (S.rho_eq_one_iff (⟨a, S.frame.L_le a.2⟩ * ⟨a, S.frame.L_le a.2⟩)).1 ?_
    rw [map_mul]
    exact ha
  have hγ := S.hat_mk_mem_center hcC
  have hα2 := S.hat_mk_mem_center haC
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hγ hα2
  rw [← hα, ← hβ] at hγ
  rw [← hα] at hα2
  set γ := α * β * α⁻¹ * β⁻¹ with hγdef
  have e1 : α * β * α⁻¹ = γ * β := by rw [hγdef]; group
  have e2 : α * γ = γ * α := (Subgroup.mem_center_iff.mp hγ α)
  have h1 : α * α * β * (α * α)⁻¹ = β := by
    rw [(Subgroup.mem_center_iff.mp hα2 β).symm]
    group
  have h2 : α * α * β * (α * α)⁻¹ = γ * γ * β :=
    calc α * α * β * (α * α)⁻¹ = α * (α * β * α⁻¹) * α⁻¹ := by group
      _ = α * γ * β * α⁻¹ := by rw [e1]; group
      _ = γ * (α * β * α⁻¹) := by rw [e2]; group
      _ = γ * γ * β := by rw [e1]; group
  have hγ2 : γ * γ = 1 := mul_right_cancel ((h2.symm.trans h1).trans (one_mul β).symm)
  have hγ3 : γ ^ 3 = 1 := hat_cube_center hhat hγ
  have hγ1 : γ = 1 := by
    rw [pow_three, hγ2, mul_one] at hγ3
    exact hγ3
  calc α * β = γ * β * α := by rw [hγdef]; group
    _ = β * α := by rw [hγ1, one_mul]

theorem rho_preserves_W2 {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : (g : G) ∈ Subgroup.normalizer (S.V2 : Set G)) :
    ∀ x : P6, InW2 x → InW2 (act4f (S.frame.ρ g) x) := by
  intro x hx
  have hxW : InW4 x := U3.inW4_of_inW2 x hx
  set w : ↥W4 := ⟨x, hxW⟩
  set v : ↥V := S.frame.ψ.symm w
  have hvV2 : (v : G) ∈ S.V2 := S.mem_pre.2 ⟨v.2, by
    show InW2 ((S.frame.ψ ⟨(v : G), v.2⟩ : ↥W4) : P6)
    have : (⟨(v : G), v.2⟩ : ↥V) = v := rfl
    rw [this, MulEquiv.apply_symm_apply]
    exact hx⟩
  have hc := (Subgroup.mem_normalizer_iff.mp hg v).mp hvV2
  obtain ⟨hcV, hcW⟩ := S.mem_pre.1 hc
  have e := S.psi_conj g v
  have e' : (⟨(g : G) * v * (g : G)⁻¹, hcV⟩ : ↥V) =
      ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ := rfl
  rw [e', e, MulEquiv.apply_symm_apply] at hcW
  have h : InW2 ((act4 (S.frame.ρ g) w : ↥W4) : P6) := hcW
  rw [act4_coe] at h
  exact h

section General

variable {W : Subgroup G} (Γ Kp : Perm (Fin 6) → Prop)

theorem hatPlus_le (hhat : IsHatA6 L)
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hρ : ∀ x ∈ L₁Of L W, ∀ hx : x ∈ Subgroup.normalizer (V : Set G), Γ (S.frame.ρ ⟨x, hx⟩))
    (fK1 : Kp 1) (fKmul : ∀ σ τ, Kp σ → Kp τ → Kp (σ * τ)) (fKinv : ∀ σ, Kp σ → Kp σ⁻¹)
    (fKsq : ∀ σ, Kp σ → σ * σ = 1) (fKcomm : ∀ σ τ, Kp σ → Kp τ → σ * τ = τ * σ)
    (fΓ : ∀ σ κ, Γ σ → Kp κ → Kp (σ * κ * σ⁻¹))
    (fcube : ∀ σ, Γ σ → Kp σ ∨ (σ * σ * σ = 1 ∧ ∃ τ, Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹))
    {c : G} (hcX : c ∈ L₁Of L W) (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (fgen : ∀ σ, Γ σ → Kp σ ∨ Kp (σ * (S.frame.ρ ⟨c, hcN⟩)⁻¹) ∨ Kp (σ * S.frame.ρ ⟨c, hcN⟩))
    (fD : ∃ τ₀, ∀ σ, InD6 σ → Perm.sign σ = 1 → Kp σ ∨ Kp (σ * τ₀⁻¹))
    (fD2 : ∀ σ, InD6 σ → Perm.sign σ = 1 → Kp (σ * σ)) :
    oTwoRes ⁅L₁Of L W, T ⊓ L⁆ ⊓ o2Z L ≤ pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L₁Of L W with hXdef
  have hXL : X ≤ L := (oTwoRes_le _).trans inf_le_left
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXL.trans S.frame.L_le
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (fun t ht =>
      mem_normalizer_inf_of (S.T_le_NL ht) (Subgroup.le_normalizer (hTW ht)))
  set O := pCoreOf 2 X with hOdef
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 X
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    hTX.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hXQ : ∀ y ∈ X, y ∈ pCoreOf 2 L → y ∈ O := fun y hy hy' =>
    le_pCoreOf_of_le_normalizer 2 (inf_le_left : X ⊓ pCoreOf 2 L ≤ X)
      (fun x hx => mem_normalizer_inf_of (Subgroup.le_normalizer hx) (hLQ (hXL hx)))
      ((pCoreOf_isPGroup 2 L).to_le inf_le_right) ⟨hy, hy'⟩
  set Zc := X ⊓ o2Z L with hZcdef
  have hZX : Zc ≤ X := inf_le_left
  have hZcent : ∀ z ∈ Zc, ∀ a ∈ X, z * a * z⁻¹ * a⁻¹ ∈ O := by
    intro z hz a ha
    refine hXQ _ (X.mul_mem (X.mul_mem (X.mul_mem hz.1 ha) (X.inv_mem hz.1)) (X.inv_mem ha)) ?_
    exact (mem_o2Z_iff.1 hz.2).2 a (hXL ha)
  have hZ3 : ∀ z ∈ Zc, z ^ 3 ∈ O := fun z hz =>
    hXQ _ (X.pow_mem hz.1 3) (cube_mem_of_o2Z hhat hz.2)
  have hLZ : ∀ s ∈ L, s ∈ Subgroup.normalizer (X : Set G) → ∀ z ∈ Zc,
      s * z * s⁻¹ * z⁻¹ ∈ O := by
    intro s hsL hsX z hz
    have hszs : s * z * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hsX z).mp hz.1
    refine hXQ _ (X.mul_mem hszs (X.inv_mem hz.1)) ?_
    have h1 := (mem_o2Z_iff.1 hz.2).2 s⁻¹ (L.inv_mem hsL)
    have e : s * z * s⁻¹ * z⁻¹ = s * (z * s⁻¹ * z⁻¹ * s⁻¹⁻¹) * s⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLQ hsL) _).mp h1
  let XK : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
        Kp (S.frame.ρ ⟨x, hx⟩)}
      one_mem' := ⟨X.one_mem, Subgroup.one_mem _, by
        have : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (V : Set G))) = 1 := rfl
        rw [this, map_one]
        exact fK1⟩
      mul_mem' := by
        rintro x y ⟨hx, hxN, hxK⟩ ⟨hy, hyN, hyK⟩
        refine ⟨X.mul_mem hx hy, Subgroup.mul_mem _ hxN hyN, ?_⟩
        have : (⟨x * y, Subgroup.mul_mem _ hxN hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
        rw [this, map_mul]
        exact fKmul _ _ hxK hyK
      inv_mem' := by
        rintro x ⟨hx, hxN, hxK⟩
        refine ⟨X.inv_mem hx, Subgroup.inv_mem _ hxN, ?_⟩
        have : (⟨x⁻¹, Subgroup.inv_mem _ hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          (⟨x, hxN⟩)⁻¹ := rfl
        rw [this, map_inv]
        exact fKinv _ hxK }
  have hXKX : XK ≤ X := fun x hx => hx.1
  have hmemXK : ∀ x (hx : x ∈ X), Kp (S.frame.ρ ⟨x, hXN hx⟩) → x ∈ XK := fun x hx h =>
    ⟨hx, hXN hx, h⟩
  have hρXK : ∀ x (hx : x ∈ XK), Kp (S.frame.ρ ⟨x, hXN hx.1⟩) := fun x hx => by
    obtain ⟨-, hxN, hK⟩ := hx
    exact hK
  let E2 : Subgroup G :=
    { carrier := {y | y ∈ XK ∧ y * y ∈ pCoreOf 2 L}
      one_mem' := ⟨XK.one_mem, by rw [one_mul]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h1K, h1O⟩ ⟨h2K, h2O⟩
        refine ⟨XK.mul_mem h1K h2K, ?_⟩
        have hy₁L : y₁ ∈ L := hXL h1K.1
        have hy₂L : y₂ ∈ L := hXL h2K.1
        have hc := S.hat_mk_comm hhat (a := ⟨y₁, hy₁L⟩) (b := ⟨y₂, hy₂L⟩)
          (fKcomm _ _ (hρXK y₁ h1K) (hρXK y₂ h2K)) (fKsq _ (hρXK y₁ h1K))
        have h1 : ((⟨y₁, hy₁L⟩ * ⟨y₁, hy₁L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
          rw [QuotientGroup.eq_one_iff, mem_pCore_iff]
          exact h1O
        have h2 : ((⟨y₂, hy₂L⟩ * ⟨y₂, hy₂L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
          rw [QuotientGroup.eq_one_iff, mem_pCore_iff]
          exact h2O
        rw [QuotientGroup.mk_mul] at h1 h2
        have h : ((⟨y₁, hy₁L⟩ * ⟨y₂, hy₂L⟩ * (⟨y₁, hy₁L⟩ * ⟨y₂, hy₂L⟩) : ↥L) :
            ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
          simp only [QuotientGroup.mk_mul]
          calc ((⟨y₁, hy₁L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * (⟨y₂, hy₂L⟩ : ↥L) *
                (((⟨y₁, hy₁L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * (⟨y₂, hy₂L⟩ : ↥L)) =
                ((⟨y₁, hy₁L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) *
                  (((⟨y₂, hy₂L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * (⟨y₁, hy₁L⟩ : ↥L)) *
                  (⟨y₂, hy₂L⟩ : ↥L) := by group
            _ = ((⟨y₁, hy₁L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * (⟨y₁, hy₁L⟩ : ↥L) *
                  (((⟨y₂, hy₂L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * (⟨y₂, hy₂L⟩ : ↥L)) := by
                rw [← hc]; group
            _ = 1 := by rw [h1, h2, one_mul]
        rw [QuotientGroup.eq_one_iff, mem_pCore_iff] at h
        exact h
      inv_mem' := by
        rintro y ⟨hK, hO⟩
        refine ⟨XK.inv_mem hK, ?_⟩
        have : y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ hO }
  have hE2O : ∀ y, y ∈ XK → y * y ∈ pCoreOf 2 L → y ∈ O := by
    intro y hyK hyO
    have hle : E2 ≤ O := by
      refine le_pCoreOf_of_le_normalizer 2 (fun y hy => hy.1.1) ?_ ?_
      · refine normalizes_of_conj_mem fun l hl y hy => ⟨?_, ?_⟩
        · obtain ⟨⟨hyX, hyN, hyK'⟩, -⟩ := hy
          refine hmemXK _ (X.mul_mem (X.mul_mem hl hyX) (X.inv_mem hl)) ?_
          have : (⟨l * y * l⁻¹, hXN (X.mul_mem (X.mul_mem hl hyX) (X.inv_mem hl))⟩ :
              ↥(Subgroup.normalizer (V : Set G))) = ⟨l, hXN hl⟩ * ⟨y, hyN⟩ * (⟨l, hXN hl⟩)⁻¹ :=
            rfl
          rw [this, map_mul, map_mul, map_inv]
          exact fΓ _ _ (hρ l hl (hXN hl)) hyK'
        · have e : l * y * l⁻¹ * (l * y * l⁻¹) = l * (y * y) * l⁻¹ := by group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp (hLQ (hXL hl)) _).mp hy.2
      · rintro ⟨y, hy⟩
        obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, hy.2⟩
        refine ⟨k + 1, Subtype.ext ?_⟩
        have hk' : (y * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        show y ^ 2 ^ (k + 1) = 1
        rw [pow_succ', pow_mul, ← hk', sq]
    exact hle ⟨hyK, hyO⟩
  have hdecomp : ∀ n ∈ XK, n ^ 4 ∈ Zc ∧ n * (n ^ 4)⁻¹ ∈ O := by
    intro n hn
    have hnX := hn.1
    have hnL := hXL hnX
    have h2C : n * n ∈ Subgroup.centralizer (V : Set G) := by
      refine (S.rho_eq_one_iff (⟨n, hXN hnX⟩ * ⟨n, hXN hnX⟩)).1 ?_
      rw [map_mul]
      exact fKsq _ (hρXK n hn)
    have h2Z : n * n ∈ o2Z L := S.centralizer_le_o2Z ⟨L.mul_mem hnL hnL, h2C⟩
    have h4 : n ^ 4 = (n * n) * (n * n) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    refine ⟨⟨X.pow_mem hnX 4, by rw [h4]; exact (o2Z L).mul_mem h2Z h2Z⟩, ?_⟩
    have e : n * (n ^ 4)⁻¹ = (n ^ 3)⁻¹ := by
      rw [show n ^ 4 = n ^ 3 * n from pow_succ n 3, mul_inv_rev, ← mul_assoc, mul_inv_cancel,
        one_mul]
    rw [e]
    refine hE2O _ (XK.inv_mem (XK.pow_mem hn 3)) ?_
    have e2 : (n ^ 3)⁻¹ * (n ^ 3)⁻¹ = ((n * n) ^ 3)⁻¹ := by
      rw [← mul_inv_rev]
      congr 1
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e2]
    exact Subgroup.inv_mem _ (cube_mem_of_o2Z hhat h2Z)
  have hXKcent : ∀ n ∈ XK, ∀ a ∈ X, n * a * n⁻¹ * a⁻¹ ∈ O := by
    intro n hn a ha
    obtain ⟨hz, ho⟩ := hdecomp n hn
    have e : n * a * n⁻¹ * a⁻¹ = (n * (n ^ 4)⁻¹) * (n ^ 4 * a * (n ^ 4)⁻¹ * a⁻¹) *
        (a * (n * (n ^ 4)⁻¹)⁻¹ * a⁻¹) := by group
    rw [e]
    exact O.mul_mem (O.mul_mem ho (hZcent _ hz a ha))
      ((Subgroup.mem_normalizer_iff.mp (hXO ha) _).mp (O.inv_mem ho))
  have hcube : ∀ x ∈ X, x ^ 3 ∈ O := by
    intro x hx
    have hxL := hXL hx
    have hxN := hXN hx
    have hx3K : x ^ 3 ∈ XK := by
      refine hmemXK _ (X.pow_mem hx 3) ?_
      have : (⟨x ^ 3, hXN (X.pow_mem hx 3)⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, hxN⟩ ^ 3 := rfl
      rw [this, map_pow, pow_three, ← mul_assoc]
      rcases fcube _ (hρ x hx hxN) with h | ⟨h, -⟩
      · rw [fKsq _ h, one_mul]; exact h
      · rw [h]; exact fK1
    refine hE2O _ hx3K ?_
    set Xq : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) with hXq
    suffices h6 : Xq ^ 6 = 1 by
      have h : ((⟨x, hxL⟩ ^ 6 : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
        rw [QuotientGroup.mk_pow, ← hXq, h6]
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff] at h
      have e : x ^ 3 * x ^ 3 = x ^ 6 := by rw [← pow_add]
      rw [e]
      simpa using h
    rcases fcube _ (hρ x hx hxN) with hK | ⟨h3, τ, hτs, hτ⟩
    · have hC : ((⟨x, hxL⟩ * ⟨x, hxL⟩ : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
        refine (S.rho_eq_one_iff (⟨x, hxN⟩ * ⟨x, hxN⟩)).1 ?_
        rw [map_mul]
        exact fKsq _ hK
      have hz := hat_cube_center hhat (S.hat_mk_mem_center hC)
      simp only [QuotientGroup.mk_mul] at hz
      rw [← hXq] at hz
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_two]
      exact hz
    · obtain ⟨g, hgL, hg⟩ := (S.frame.image_L τ).2 (Perm.mem_alternatingGroup.2 hτs)
      set Y : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨(g : G), hgL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) with hY
      have hC3 : ((⟨x, hxL⟩ ^ 3 : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
        refine (S.rho_eq_one_iff (⟨x, hxN⟩ ^ 3)).1 ?_
        rw [map_pow, pow_three, ← mul_assoc]
        exact h3
      have hw := S.hat_mk_mem_center hC3
      simp only [QuotientGroup.mk_pow] at hw
      rw [← hXq] at hw
      have hkC : ((⟨(g : G), hgL⟩ * ⟨x, hxL⟩ * (⟨(g : G), hgL⟩)⁻¹ * ⟨x, hxL⟩ : ↥L) : G) ∈
          Subgroup.centralizer (V : Set G) := by
        refine (S.rho_eq_one_iff (g * ⟨x, hxN⟩ * g⁻¹ * ⟨x, hxN⟩)).1 ?_
        rw [map_mul, map_mul, map_mul, map_inv, hg, hτ, inv_mul_cancel]
      have hκ := S.hat_mk_mem_center hkC
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hκ
      rw [← hXq, ← hY] at hκ
      set κ := Y * Xq * Y⁻¹ * Xq with hκdef
      have e1 : Y * Xq * Y⁻¹ = κ * Xq⁻¹ := by rw [hκdef]; group
      have hκ3 : κ ^ 3 = 1 := hat_cube_center hhat hκ
      have e2 : Y * Xq ^ 3 * Y⁻¹ = (Xq ^ 3)⁻¹ := by
        rw [← conj_pow, e1, (Commute.mul_pow (Subgroup.mem_center_iff.mp hκ Xq⁻¹).symm 3), hκ3,
          one_mul, inv_pow]
      have e3 : Y * Xq ^ 3 * Y⁻¹ = Xq ^ 3 := by
        rw [(Subgroup.mem_center_iff.mp hw Y)]
        group
      have h33 : Xq ^ 3 * Xq ^ 3 = 1 := by
        have h := e3.symm.trans e2
        calc Xq ^ 3 * Xq ^ 3 = (Xq ^ 3)⁻¹ * Xq ^ 3 := by rw [← h]
          _ = 1 := inv_mul_cancel _
      rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add]
      exact h33
  have hab : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ O := by
    refine comm_mod_of_gen hXO hXKX hcX hXKcent fun a ha => ?_
    rcases fgen _ (hρ a ha (hXN ha)) with h | h | h
    · exact Or.inl (hmemXK a ha h)
    · refine Or.inr (Or.inl (hmemXK _ (X.mul_mem ha (X.inv_mem hcX)) ?_))
      have : (⟨a * c⁻¹, hXN (X.mul_mem ha (X.inv_mem hcX))⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = ⟨a, hXN ha⟩ * (⟨c, hcN⟩)⁻¹ := rfl
      rw [this, map_mul, map_inv]
      exact h
    · refine Or.inr (Or.inr (hmemXK _ (X.mul_mem ha hcX) ?_))
      have : (⟨a * c, hXN (X.mul_mem ha hcX)⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨a, hXN ha⟩ * ⟨c, hcN⟩ := rfl
      rw [this, map_mul]
      exact h
  have hSX : T ⊓ L ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have hSO : T ⊓ L ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hTO
  have huni : ∀ s (hs : s ∈ T ⊓ L), Kp (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩) →
      ∀ a ∈ X, s * a * s⁻¹ * a⁻¹ ∈ O := by
    intro s hs hK
    obtain ⟨m, hm⟩ := S.h13.sylow.1 ⟨s, hs.1⟩
    have hs2 : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine conj_mod_trivial_of_two_pow hXO hZX hZ3 (hSX hs) (hSO hs)
      (hLZ s hs.2 (hSX hs)) hs2 fun a ha => ?_
    have hsaX : s * a * s⁻¹ * a⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSX hs) a).mp ha) (X.inv_mem ha)
    have hnK : s * a * s⁻¹ * a⁻¹ ∈ XK := by
      refine hmemXK _ hsaX ?_
      have : (⟨s * a * s⁻¹ * a⁻¹, hXN hsaX⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨s, S.frame.T_le hs.1⟩ * ⟨a, hXN ha⟩ * (⟨s, S.frame.T_le hs.1⟩)⁻¹ *
            (⟨a, hXN ha⟩)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc, mul_assoc]
      refine fKmul _ _ hK ?_
      rw [← mul_assoc]
      exact fΓ _ _ (hρ a ha (hXN ha)) (fKinv _ hK)
    obtain ⟨hz, ho⟩ := hdecomp _ hnK
    exact ⟨_, hz, ho⟩
  have hρS : ∀ s (hs : s ∈ T ⊓ L), InD6 (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩) ∧
      Perm.sign (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩) = 1 := fun s hs =>
    ⟨S.frame.T_D _ hs.1, Perm.mem_alternatingGroup.1 (U3.L15A.rho_mem_alt S hs.2)⟩
  have hmain : ⁅X, T ⊓ L⁆ ⊓ Zc ≤ O := by
    by_cases hex : ∃ t, ∃ ht : t ∈ T ⊓ L, ¬ Kp (S.frame.ρ ⟨t, S.frame.T_le ht.1⟩)
    · obtain ⟨t, ht, htK⟩ := hex
      obtain ⟨τ₀, hτ₀⟩ := fD
      have hDK : ∀ s (hs : s ∈ T ⊓ L) (hst : s * t⁻¹ ∈ T ⊓ L),
          ¬ Kp (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩) →
          Kp (S.frame.ρ ⟨s * t⁻¹, S.frame.T_le hst.1⟩) := by
        intro s hs hst hsK
        have h1 := (hτ₀ _ (hρS s hs).1 (hρS s hs).2).resolve_left hsK
        have h2 := (hτ₀ _ (hρS t ht).1 (hρS t ht).2).resolve_left htK
        have : (⟨s * t⁻¹, S.frame.T_le hst.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨s, S.frame.T_le hs.1⟩ * (⟨t, S.frame.T_le ht.1⟩)⁻¹ := rfl
        rw [this, map_mul, map_inv]
        have e : S.frame.ρ ⟨s, S.frame.T_le hs.1⟩ * (S.frame.ρ ⟨t, S.frame.T_le ht.1⟩)⁻¹ =
            (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩ * τ₀⁻¹) *
              (S.frame.ρ ⟨t, S.frame.T_le ht.1⟩ * τ₀⁻¹)⁻¹ := by group
        rw [e]
        exact fKmul _ _ h1 (fKinv _ h2)
      refine commutator_inf_le_of_acts hXO hab hcube hSX hSO ht (fun s hs => ?_) ?_ ?_
      · by_cases hsK : Kp (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩)
        · exact Or.inl (huni s hs hsK)
        · right
          intro a ha
          have hst : s * t⁻¹ ∈ T ⊓ L := (T ⊓ L).mul_mem hs ((T ⊓ L).inv_mem ht)
          have htaX : t * a * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hSX ht) a).mp ha
          have h := huni _ hst (hDK s hs hst hsK) _ htaX
          have e : s * a * s⁻¹ * (t * a * t⁻¹)⁻¹ =
              s * t⁻¹ * (t * a * t⁻¹) * (s * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹ := by group
          rw [e]
          exact h
      · have htt : t * t ∈ T ⊓ L := (T ⊓ L).mul_mem ht ht
        refine huni _ htt ?_
        have : (⟨t * t, S.frame.T_le htt.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨t, S.frame.T_le ht.1⟩ * ⟨t, S.frame.T_le ht.1⟩ := rfl
        rw [this, map_mul]
        exact fD2 _ (hρS t ht).1 (hρS t ht).2
      · exact hLZ t ht.2 (hSX ht)
    · push Not at hex
      refine commutator_inf_le_of_acts (t := 1) hXO hab hcube hSX hSO (Subgroup.one_mem _)
        (fun s hs => Or.inl (huni s hs (hex s hs))) ?_ ?_
      · intro a _
        simp
      · intro z _
        simp
  rintro y ⟨hyP, hyZ⟩
  have hcomm : ⁅X, T ⊓ L⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro a ha s hs
    rw [commutatorElement_def]
    have e : a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) := by group
    rw [e]
    exact X.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hSX hs) _).mp (X.inv_mem ha))
  have hyK : y ∈ ⁅X, T ⊓ L⁆ := oTwoRes_le _ hyP
  have hyO : y ∈ O := hmain ⟨hyK, hcomm hyK, hyZ⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨y, hyO⟩
  exact mem_pCoreOf_of_o2Z hhat hyZ (k := k) (by simpa using congrArg Subtype.val hk)

end General

theorem hatL1Plus (hhat : IsHatA6 L) :
    l1plus T L V ⊓ o2Z L ≤ pCoreOf 2 L := by
  obtain ⟨c, hcL, hc⟩ := S.exists_L1_c012
  refine S.hatPlus_le (Γ := fun σ => σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1)
    (Kp := fun σ => σ ∈ K4L) hhat S.T_le_NV1 (fun x hx hxN => S.rho_L1 hx) List.mem_cons_self
    (fun σ τ h1 h2 => K4L_mul σ h1 τ h2) (fun σ h => K4L_inv σ h) (fun σ h => K4L_sq σ h)
    (fun σ τ h1 h2 => hatK4L_comm σ h1 τ h2) (fun σ κ h1 h2 => A4_conj_K4L κ h2 σ h1)
    (fun σ h => ?_) hcL c.2 (fun σ h => ?_) ⟨swap 0 1 * swap 4 5, fun σ h1 h2 =>
      (DA6_K4L σ ⟨h1, h2⟩).1⟩ (fun σ h1 h2 => (DA6_K4L σ ⟨h1, h2⟩).2)
  · rcases A4_cube_K4L σ h with h' | ⟨h3, τ, -, hτ⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h3, τ, hτ⟩
  · have : (⟨(c : G), c.2⟩ : ↥(Subgroup.normalizer (V : Set G))) = c := rfl
    rw [this, hc]
    exact A4_gen_K4L σ h

theorem rho_L2_mem {x : G} (hx : x ∈ L₁Of L S.V2)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) : S.frame.ρ ⟨x, hxN⟩ ∈ A4pL := by
  let A4psub : Subgroup (Perm (Fin 6)) :=
    { carrier := {σ | σ ∈ A4pL}
      one_mem' := A4pL_one
      mul_mem' := fun {a b} ha hb => A4pL_mul a ha b hb
      inv_mem' := fun {a} ha => A4pL_inv a ha }
  have hle : L₁Of L S.V2 ≤
      (A4psub.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨hyL, hyV2⟩, m, hm, hym⟩
    have hyN := S.frame.L_le hyL
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    show S.frame.ρ ⟨y, hyN⟩ ∈ A4pL
    have hs := Perm.mem_alternatingGroup.1 (U3.L15A.rho_mem_alt S (g := ⟨y, hyN⟩) hyL)
    obtain ⟨h12, h3⟩ := stab_W2_facts _ ⟨hs, S.rho_preserves_W2 hyV2⟩
    apply h3
    have hm1 : S.frame.ρ ⟨y, hyN⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ m = 1 :=
        Subtype.ext (by simpa using hym)
      rw [this, map_one]
    have hdvd : orderOf (S.frame.ρ ⟨y, hyN⟩) ∣ Nat.gcd m 12 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm1) (orderOf_dvd_of_pow_eq_one h12)
    have hg : Nat.gcd m 12 ∣ 3 := by
      have hc4 : Nat.Coprime 4 m := by
        have := (Nat.coprime_two_left.2 hm).pow_left 2
        norm_num at this
        exact this
      rw [show (12 : ℕ) = 4 * 3 from rfl, Nat.Coprime.gcd_mul_left_cancel_right 3 hc4]
      exact Nat.gcd_dvd_right m 3
    exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans hg)
  obtain ⟨y, hy, hyx⟩ := hle hx
  have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) = y := Subtype.ext hyx.symm
  rw [e]
  exact hy

theorem hatL2Plus (hhat : IsHatA6 L) :
    oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ ⊓ o2Z L ≤ pCoreOf 2 L := by
  obtain ⟨g, hgL, hgV2, hg, -, -⟩ := U3.L15A.exists_lift_s3 S
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  have hcX : (g : G) ^ 4 ^ a ∈ L₁Of L S.V2 := by
    refine Subgroup.subset_closure ⟨⟨L.pow_mem hgL _, Subgroup.pow_mem _ hgV2 _⟩, m, hm, ?_⟩
    have e : ((g : G) ^ 4 ^ a) ^ m = ((g : G) ^ (2 ^ a * m)) ^ 2 ^ a := by
      rw [← pow_mul, ← pow_mul, show (4 : ℕ) ^ a = 2 ^ a * 2 ^ a by
        rw [← mul_pow]; norm_num]
      ring_nf
    rw [e, ← hnm, pow_orderOf_eq_one, one_pow]
  have hcN : (g : G) ^ 4 ^ a ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ g.2 _
  have hρc : S.frame.ρ ⟨(g : G) ^ 4 ^ a, hcN⟩ = U3.a6s3 := by
    have : (⟨(g : G) ^ 4 ^ a, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) = g ^ 4 ^ a := rfl
    rw [this, map_pow, hg]
    exact pow_four_pow_of_cube U3.cert_a6_s3.2.1 a
  refine S.hatPlus_le (Γ := fun σ => σ ∈ A4pL) (Kp := fun σ => σ ∈ K4pL) hhat
    S.T_le_normalizer_V2 (fun x hx hxN => S.rho_L2_mem hx hxN) K4pL_one
    (fun σ τ h1 h2 => K4pL_mul σ h1 τ h2) (fun σ h => K4pL_inv σ h) (fun σ h => K4pL_sq σ h)
    (fun σ τ h1 h2 => K4pL_comm σ h1 τ h2) (fun σ κ h1 h2 => A4pL_conj σ h1 κ h2)
    (fun σ h => ?_) hcX hcN (fun σ h => ?_) ⟨swap 0 2 * swap 1 3, fun σ h1 h2 =>
      (DA6_K4pL σ ⟨h1, h2⟩).1⟩ (fun σ h1 h2 => (DA6_K4pL σ ⟨h1, h2⟩).2)
  · rcases A4pL_cube σ h with h' | ⟨h3, τ, -, hτ⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h3, τ, hτ⟩
  · rw [hρc]
    exact A4pL_gen σ h

end Setting4

open scoped IsMulCommutative in
theorem exists_setting4_of_1332 (h1332 : Stmt13_3_2) {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} (h : QTH13 G T L) (hA6 : A6CentralQuotient L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
      obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLV
      exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
    · exact h6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      exact absurd hc2 (by norm_num)
    · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
    · exfalso
      have h1 := card_of_lieModel_psu33 hu
      obtain ⟨e⟩ := hA6
      have h2 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 360 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        rfl
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      rw [h1, h2] at h3
      omega
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame4 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    a6 := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
    centralQuot := hA6
    frame := F }⟩

theorem u3HatL2Plus_of (h1332 : Stmt13_3_2) :
    U3.U3HatL2Plus := by
  intro G _ _ T L V V₂ hH hV hZV _ hhat hV2
  obtain ⟨S⟩ := exists_setting4_of_1332 h1332 hH hhat.2.2 hV hZV
  have hV2e : V₂ = S.V2 := S.V2_unique hV2
  subst hV2e
  exact S.hatL2Plus hhat

end CFSG.Quasithin.H13.A6
