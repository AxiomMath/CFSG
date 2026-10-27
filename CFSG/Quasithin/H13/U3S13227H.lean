module

public import CFSG.Quasithin.H13.U3S13226
public import CFSG.Quasithin.H13.A6Set14

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_pCoreOf_L_le (S : A6.Setting134 G T L V) :
    pCoreOf 2 L ≤ centralizer (V : Set G) :=
  (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (s134_pCoreOf_LT_le S)

theorem s134_centralizer_le_o2Z (S : A6.Setting134 G T L V) :
    L ⊓ centralizer (V : Set G) ≤ o2Z L :=
  centralizer_le_o2Z_of_isA6On S.frame.L_le (s134_pCoreOf_L_le S) S.fsu.quasisimple
    (s134_isA6On S)

theorem s134_o2Z_le_centralizer (S : A6.Setting134 G T L V) :
    o2Z L ≤ centralizer (V : Set G) := by
  intro y hy
  obtain ⟨hyL, hc⟩ := mem_o2Z_iff.1 hy
  have hyN := S.frame.L_le hyL
  have key : ∀ σ ∈ alternatingGroup (Fin 6), S.frame.ρ ⟨y, hyN⟩ * σ = σ * S.frame.ρ ⟨y, hyN⟩ := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
    have h1 := (s134_rho_eq_one_iff S (⟨y, hyN⟩ * g * (⟨y, hyN⟩)⁻¹ * g⁻¹)).2
      (s134_pCoreOf_L_le S (hc g hgL))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    rw [← hg]
    calc S.frame.ρ ⟨y, hyN⟩ * S.frame.ρ g =
        (S.frame.ρ ⟨y, hyN⟩ * S.frame.ρ g * (S.frame.ρ ⟨y, hyN⟩)⁻¹ * (S.frame.ρ g)⁻¹) *
          (S.frame.ρ g * S.frame.ρ ⟨y, hyN⟩) := by group
      _ = S.frame.ρ g * S.frame.ρ ⟨y, hyN⟩ := by rw [h1, one_mul]
  exact (s134_rho_eq_one_iff S ⟨y, hyN⟩).1 (eq_one_of_comm_three _
    (key _ (Perm.mem_alternatingGroup.2 (by decide)))
    (key _ (Perm.mem_alternatingGroup.2 (by decide)))
    (key _ (Perm.mem_alternatingGroup.2 (by decide))))

theorem s134_exists_TL (S : A6.Setting134 G T L V) {σ : Perm (Fin 6)} (hσD : InD6 σ)
    (hσA : σ ∈ alternatingGroup (Fin 6)) :
    ∃ g : ↥(normalizer (V : Set G)), (g : G) ∈ T ⊓ L ∧ S.frame.ρ g = σ := by
  let F : Frame139 T L V := ⟨S.frame.ρ, S.frame.L_le, S.frame.T_le, s134_rho_eq_one_iff S,
    S.frame.image_L, S.frame.T_D, s134_pres45 S⟩
  exact F.exists_TL (s134_sylow_TL S) hσD hσA

theorem s134_hat_mk_mem_center (S : A6.Setting134 G T L V) {y : ↥L}
    (hy : (y : G) ∈ centralizer (V : Set G)) :
    (y : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨x, hx, hxy⟩ := s134_centralizer_le_o2Z S ⟨y.2, hy⟩
  have e : x = y := Subtype.ext hxy
  subst e
  exact hx

theorem s134_hat_mk_comm (S : A6.Setting134 G T L V) (hhat : IsHatA6 L)
    {a b : ↥L} (hab : S.frame.ρ ⟨a, S.frame.L_le a.2⟩ * S.frame.ρ ⟨b, S.frame.L_le b.2⟩ =
      S.frame.ρ ⟨b, S.frame.L_le b.2⟩ * S.frame.ρ ⟨a, S.frame.L_le a.2⟩)
    (ha : S.frame.ρ ⟨a, S.frame.L_le a.2⟩ * S.frame.ρ ⟨a, S.frame.L_le a.2⟩ = 1) :
    (a : ↥L ⧸ CFSG.pCore 2 ↥L) * (b : ↥L ⧸ CFSG.pCore 2 ↥L) =
      (b : ↥L ⧸ CFSG.pCore 2 ↥L) * (a : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  set α : ↥L ⧸ CFSG.pCore 2 ↥L := (a : ↥L ⧸ CFSG.pCore 2 ↥L) with hα
  set β : ↥L ⧸ CFSG.pCore 2 ↥L := (b : ↥L ⧸ CFSG.pCore 2 ↥L) with hβ
  have hcC : ((a * b * a⁻¹ * b⁻¹ : ↥L) : G) ∈ centralizer (V : Set G) := by
    refine (s134_rho_eq_one_iff S (⟨a, S.frame.L_le a.2⟩ * ⟨b, S.frame.L_le b.2⟩ *
      (⟨a, S.frame.L_le a.2⟩)⁻¹ * (⟨b, S.frame.L_le b.2⟩)⁻¹)).1 ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have haC : ((a * a : ↥L) : G) ∈ centralizer (V : Set G) := by
    refine (s134_rho_eq_one_iff S (⟨a, S.frame.L_le a.2⟩ * ⟨a, S.frame.L_le a.2⟩)).1 ?_
    rw [map_mul]
    exact ha
  have hγ := s134_hat_mk_mem_center S hcC
  have hα2 := s134_hat_mk_mem_center S haC
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hγ hα2
  rw [← hα, ← hβ] at hγ
  rw [← hα] at hα2
  set γ := α * β * α⁻¹ * β⁻¹ with hγdef
  have e1 : α * β * α⁻¹ = γ * β := by rw [hγdef]; group
  have e2 : α * γ = γ * α := (mem_center_iff.mp hγ α)
  have h1 : α * α * β * (α * α)⁻¹ = β := by
    rw [(mem_center_iff.mp hα2 β).symm]
    group
  have h2 : α * α * β * (α * α)⁻¹ = γ * γ * β :=
    calc α * α * β * (α * α)⁻¹ = α * (α * β * α⁻¹) * α⁻¹ := by group
      _ = α * γ * β * α⁻¹ := by rw [e1]; group
      _ = γ * (α * β * α⁻¹) := by rw [e2]; group
      _ = γ * γ * β := by rw [e1]; group
  have hγ2 : γ * γ = 1 := mul_right_cancel ((h2.symm.trans h1).trans (one_mul β).symm)
  have hγ3 : γ ^ 3 = 1 := A6.Setting4.hat_cube_center hhat hγ
  have hγ1 : γ = 1 := by
    rw [pow_three, hγ2, mul_one] at hγ3
    exact hγ3
  calc α * β = γ * β * α := by rw [hγdef]; group
    _ = β * α := by rw [hγ1, one_mul]

section General

variable {W : Subgroup G} (Γ Kp : Perm (Fin 6) → Prop)

theorem s134_hatPlus_le (S : A6.Setting134 G T L V) (hhat : IsHatA6 L)
    (hTW : T ≤ normalizer (W : Set G))
    (hρ : ∀ x ∈ L₁Of L W, ∀ hx : x ∈ normalizer (V : Set G), Γ (S.frame.ρ ⟨x, hx⟩))
    (fK1 : Kp 1) (fKmul : ∀ σ τ, Kp σ → Kp τ → Kp (σ * τ)) (fKinv : ∀ σ, Kp σ → Kp σ⁻¹)
    (fKsq : ∀ σ, Kp σ → σ * σ = 1) (fKcomm : ∀ σ τ, Kp σ → Kp τ → σ * τ = τ * σ)
    (fΓ : ∀ σ κ, Γ σ → Kp κ → Kp (σ * κ * σ⁻¹))
    (fcube : ∀ σ, Γ σ → Kp σ ∨ (σ * σ * σ = 1 ∧ ∃ τ, Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹))
    {c : G} (hcX : c ∈ L₁Of L W) (hcN : c ∈ normalizer (V : Set G))
    (fgen : ∀ σ, Γ σ → Kp σ ∨ Kp (σ * (S.frame.ρ ⟨c, hcN⟩)⁻¹) ∨ Kp (σ * S.frame.ρ ⟨c, hcN⟩))
    (fD : ∃ τ₀, ∀ σ, InD6 σ → Perm.sign σ = 1 → Kp σ ∨ Kp (σ * τ₀⁻¹))
    (fD2 : ∀ σ, InD6 σ → Perm.sign σ = 1 → Kp (σ * σ)) :
    oTwoRes ⁅L₁Of L W, T ⊓ L⁆ ⊓ o2Z L ≤ pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L₁Of L W with hXdef
  have hXL : X ≤ L := (oTwoRes_le _).trans inf_le_left
  have hXN : X ≤ normalizer (V : Set G) := hXL.trans S.frame.L_le
  have hTX : T ≤ normalizer (X : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (fun t ht =>
      mem_normalizer_inf_of (S.T_le_NL ht) (le_normalizer (hTW ht)))
  set O := pCoreOf 2 X with hOdef
  have hXO : X ≤ normalizer (O : Set G) := le_normalizer_pCoreOf 2 X
  have hTO : T ≤ normalizer (O : Set G) :=
    hTX.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hLQ : L ≤ normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hXQ : ∀ y ∈ X, y ∈ pCoreOf 2 L → y ∈ O := fun y hy hy' =>
    le_pCoreOf_of_le_normalizer 2 (inf_le_left : X ⊓ pCoreOf 2 L ≤ X)
      (fun x hx => mem_normalizer_inf_of (le_normalizer hx) (hLQ (hXL hx)))
      ((pCoreOf_isPGroup 2 L).to_le inf_le_right) ⟨hy, hy'⟩
  set Zc := X ⊓ o2Z L with hZcdef
  have hZX : Zc ≤ X := inf_le_left
  have hZcent : ∀ z ∈ Zc, ∀ a ∈ X, z * a * z⁻¹ * a⁻¹ ∈ O := by
    intro z hz a ha
    refine hXQ _ (X.mul_mem (X.mul_mem (X.mul_mem hz.1 ha) (X.inv_mem hz.1)) (X.inv_mem ha)) ?_
    exact (mem_o2Z_iff.1 hz.2).2 a (hXL ha)
  have hZ3 : ∀ z ∈ Zc, z ^ 3 ∈ O := fun z hz =>
    hXQ _ (X.pow_mem hz.1 3) (A6.Setting4.cube_mem_of_o2Z hhat hz.2)
  have hLZ : ∀ s ∈ L, s ∈ normalizer (X : Set G) → ∀ z ∈ Zc,
      s * z * s⁻¹ * z⁻¹ ∈ O := by
    intro s hsL hsX z hz
    have hszs : s * z * s⁻¹ ∈ X := (mem_normalizer_iff.mp hsX z).mp hz.1
    refine hXQ _ (X.mul_mem hszs (X.inv_mem hz.1)) ?_
    have h1 := (mem_o2Z_iff.1 hz.2).2 s⁻¹ (L.inv_mem hsL)
    have e : s * z * s⁻¹ * z⁻¹ = s * (z * s⁻¹ * z⁻¹ * s⁻¹⁻¹) * s⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hLQ hsL) _).mp h1
  let XK : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∃ hx : x ∈ normalizer (V : Set G), Kp (S.frame.ρ ⟨x, hx⟩)}
      one_mem' := ⟨X.one_mem, one_mem _, by
        have : (⟨1, one_mem _⟩ : ↥(normalizer (V : Set G))) = 1 := rfl
        rw [this, map_one]
        exact fK1⟩
      mul_mem' := by
        rintro x y ⟨hx, hxN, hxK⟩ ⟨hy, hyN, hyK⟩
        refine ⟨X.mul_mem hx hy, mul_mem hxN hyN, ?_⟩
        have : (⟨x * y, mul_mem hxN hyN⟩ : ↥(normalizer (V : Set G))) =
          ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
        rw [this, map_mul]
        exact fKmul _ _ hxK hyK
      inv_mem' := by
        rintro x ⟨hx, hxN, hxK⟩
        refine ⟨X.inv_mem hx, inv_mem hxN, ?_⟩
        have : (⟨x⁻¹, inv_mem hxN⟩ : ↥(normalizer (V : Set G))) = (⟨x, hxN⟩)⁻¹ := rfl
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
      one_mem' := ⟨XK.one_mem, by rw [one_mul]; exact one_mem _⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h1K, h1O⟩ ⟨h2K, h2O⟩
        refine ⟨XK.mul_mem h1K h2K, ?_⟩
        have hy₁L : y₁ ∈ L := hXL h1K.1
        have hy₂L : y₂ ∈ L := hXL h2K.1
        have hc := s134_hat_mk_comm S hhat (a := ⟨y₁, hy₁L⟩) (b := ⟨y₂, hy₂L⟩)
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
        exact inv_mem hO }
  have hE2O : ∀ y, y ∈ XK → y * y ∈ pCoreOf 2 L → y ∈ O := by
    intro y hyK hyO
    have hle : E2 ≤ O := by
      refine le_pCoreOf_of_le_normalizer 2 (fun y hy => hy.1.1) ?_ ?_
      · refine normalizes_of_conj_mem fun l hl y hy => ⟨?_, ?_⟩
        · obtain ⟨⟨hyX, hyN, hyK'⟩, -⟩ := hy
          refine hmemXK _ (X.mul_mem (X.mul_mem hl hyX) (X.inv_mem hl)) ?_
          have : (⟨l * y * l⁻¹, hXN (X.mul_mem (X.mul_mem hl hyX) (X.inv_mem hl))⟩ :
              ↥(normalizer (V : Set G))) = ⟨l, hXN hl⟩ * ⟨y, hyN⟩ * (⟨l, hXN hl⟩)⁻¹ :=
            rfl
          rw [this, map_mul, map_mul, map_inv]
          exact fΓ _ _ (hρ l hl (hXN hl)) hyK'
        · have e : l * y * l⁻¹ * (l * y * l⁻¹) = l * (y * y) * l⁻¹ := by group
          rw [e]
          exact (mem_normalizer_iff.mp (hLQ (hXL hl)) _).mp hy.2
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
    have h2C : n * n ∈ centralizer (V : Set G) := by
      refine (s134_rho_eq_one_iff S (⟨n, hXN hnX⟩ * ⟨n, hXN hnX⟩)).1 ?_
      rw [map_mul]
      exact fKsq _ (hρXK n hn)
    have h2Z : n * n ∈ o2Z L := s134_centralizer_le_o2Z S ⟨L.mul_mem hnL hnL, h2C⟩
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
    exact inv_mem (A6.Setting4.cube_mem_of_o2Z hhat h2Z)
  have hXKcent : ∀ n ∈ XK, ∀ a ∈ X, n * a * n⁻¹ * a⁻¹ ∈ O := by
    intro n hn a ha
    obtain ⟨hz, ho⟩ := hdecomp n hn
    have e : n * a * n⁻¹ * a⁻¹ = (n * (n ^ 4)⁻¹) * (n ^ 4 * a * (n ^ 4)⁻¹ * a⁻¹) *
        (a * (n * (n ^ 4)⁻¹)⁻¹ * a⁻¹) := by group
    rw [e]
    exact O.mul_mem (O.mul_mem ho (hZcent _ hz a ha))
      ((mem_normalizer_iff.mp (hXO ha) _).mp (O.inv_mem ho))
  have hcube : ∀ x ∈ X, x ^ 3 ∈ O := by
    intro x hx
    have hxL := hXL hx
    have hxN := hXN hx
    have hx3K : x ^ 3 ∈ XK := by
      refine hmemXK _ (X.pow_mem hx 3) ?_
      have : (⟨x ^ 3, hXN (X.pow_mem hx 3)⟩ : ↥(normalizer (V : Set G))) =
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
    · have hC : ((⟨x, hxL⟩ * ⟨x, hxL⟩ : ↥L) : G) ∈ centralizer (V : Set G) := by
        refine (s134_rho_eq_one_iff S (⟨x, hxN⟩ * ⟨x, hxN⟩)).1 ?_
        rw [map_mul]
        exact fKsq _ hK
      have hz := A6.Setting4.hat_cube_center hhat (s134_hat_mk_mem_center S hC)
      simp only [QuotientGroup.mk_mul] at hz
      rw [← hXq] at hz
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_two]
      exact hz
    · obtain ⟨g, hgL, hg⟩ := (S.frame.image_L τ).2 (Perm.mem_alternatingGroup.2 hτs)
      set Y : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨(g : G), hgL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) with hY
      have hC3 : ((⟨x, hxL⟩ ^ 3 : ↥L) : G) ∈ centralizer (V : Set G) := by
        refine (s134_rho_eq_one_iff S (⟨x, hxN⟩ ^ 3)).1 ?_
        rw [map_pow, pow_three, ← mul_assoc]
        exact h3
      have hw := s134_hat_mk_mem_center S hC3
      simp only [QuotientGroup.mk_pow] at hw
      rw [← hXq] at hw
      have hkC : ((⟨(g : G), hgL⟩ * ⟨x, hxL⟩ * (⟨(g : G), hgL⟩)⁻¹ * ⟨x, hxL⟩ : ↥L) : G) ∈
          centralizer (V : Set G) := by
        refine (s134_rho_eq_one_iff S (g * ⟨x, hxN⟩ * g⁻¹ * ⟨x, hxN⟩)).1 ?_
        rw [map_mul, map_mul, map_mul, map_inv, hg, hτ, inv_mul_cancel]
      have hκ := s134_hat_mk_mem_center S hkC
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hκ
      rw [← hXq, ← hY] at hκ
      set κ := Y * Xq * Y⁻¹ * Xq with hκdef
      have e1 : Y * Xq * Y⁻¹ = κ * Xq⁻¹ := by rw [hκdef]; group
      have hκ3 : κ ^ 3 = 1 := A6.Setting4.hat_cube_center hhat hκ
      have e2 : Y * Xq ^ 3 * Y⁻¹ = (Xq ^ 3)⁻¹ := by
        rw [← conj_pow, e1, (Commute.mul_pow (mem_center_iff.mp hκ Xq⁻¹).symm 3), hκ3,
          one_mul, inv_pow]
      have e3 : Y * Xq ^ 3 * Y⁻¹ = Xq ^ 3 := by
        rw [(mem_center_iff.mp hw Y)]
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
          ↥(normalizer (V : Set G))) = ⟨a, hXN ha⟩ * (⟨c, hcN⟩)⁻¹ := rfl
      rw [this, map_mul, map_inv]
      exact h
    · refine Or.inr (Or.inr (hmemXK _ (X.mul_mem ha hcX) ?_))
      have : (⟨a * c, hXN (X.mul_mem ha hcX)⟩ : ↥(normalizer (V : Set G))) =
          ⟨a, hXN ha⟩ * ⟨c, hcN⟩ := rfl
      rw [this, map_mul]
      exact h
  have hSX : T ⊓ L ≤ normalizer (X : Set G) := inf_le_left.trans hTX
  have hSO : T ⊓ L ≤ normalizer (O : Set G) := inf_le_left.trans hTO
  have huni : ∀ s (hs : s ∈ T ⊓ L), Kp (S.frame.ρ ⟨s, S.frame.T_le hs.1⟩) →
      ∀ a ∈ X, s * a * s⁻¹ * a⁻¹ ∈ O := by
    intro s hs hK
    obtain ⟨m, hm⟩ := S.h13.sylow.1 ⟨s, hs.1⟩
    have hs2 : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine conj_mod_trivial_of_two_pow hXO hZX hZ3 (hSX hs) (hSO hs)
      (hLZ s hs.2 (hSX hs)) hs2 fun a ha => ?_
    have hsaX : s * a * s⁻¹ * a⁻¹ ∈ X :=
      X.mul_mem ((mem_normalizer_iff.mp (hSX hs) a).mp ha) (X.inv_mem ha)
    have hnK : s * a * s⁻¹ * a⁻¹ ∈ XK := by
      refine hmemXK _ hsaX ?_
      have : (⟨s * a * s⁻¹ * a⁻¹, hXN hsaX⟩ : ↥(normalizer (V : Set G))) =
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
    ⟨S.frame.T_D _ hs.1, Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨_, hs.2, rfl⟩)⟩
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
        have : (⟨s * t⁻¹, S.frame.T_le hst.1⟩ : ↥(normalizer (V : Set G))) =
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
          have htaX : t * a * t⁻¹ ∈ X := (mem_normalizer_iff.mp (hSX ht) a).mp ha
          have h := huni _ hst (hDK s hs hst hsK) _ htaX
          have e : s * a * s⁻¹ * (t * a * t⁻¹)⁻¹ =
              s * t⁻¹ * (t * a * t⁻¹) * (s * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹ := by group
          rw [e]
          exact h
      · have htt : t * t ∈ T ⊓ L := (T ⊓ L).mul_mem ht ht
        refine huni _ htt ?_
        have : (⟨t * t, S.frame.T_le htt.1⟩ : ↥(normalizer (V : Set G))) =
            ⟨t, S.frame.T_le ht.1⟩ * ⟨t, S.frame.T_le ht.1⟩ := rfl
        rw [this, map_mul]
        exact fD2 _ (hρS t ht).1 (hρS t ht).2
      · exact hLZ t ht.2 (hSX ht)
    · push Not at hex
      refine commutator_inf_le_of_acts (t := 1) hXO hab hcube hSX hSO (one_mem _)
        (fun s hs => Or.inl (huni s hs (hex s hs))) ?_ ?_
      · intro a _
        simp
      · intro z _
        simp
  rintro y ⟨hyP, hyZ⟩
  have hcomm : ⁅X, T ⊓ L⁆ ≤ X := by
    rw [commutator_le]
    intro a ha s hs
    rw [commutatorElement_def]
    have e : a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) := by group
    rw [e]
    exact X.mul_mem ha ((mem_normalizer_iff.mp (hSX hs) _).mp (X.inv_mem ha))
  have hyK : y ∈ ⁅X, T ⊓ L⁆ := oTwoRes_le _ hyP
  have hyO : y ∈ O := hmain ⟨hyK, hcomm hyK, hyZ⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨y, hyO⟩
  exact A6.Setting4.mem_pCoreOf_of_o2Z hhat hyZ (k := k) (by simpa using congrArg Subtype.val hk)

end General

theorem s134_hatL1Plus (S : A6.Setting134 G T L V) (hhat : IsHatA6 L) :
    l1plus T L V ⊓ o2Z L ≤ pCoreOf 2 L := by
  obtain ⟨c, hcL, hcN, hc⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1 c012_props.2.2
  refine s134_hatPlus_le (Γ := fun σ => σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1)
    (Kp := fun σ => σ ∈ K4L) S hhat (T_le_normalizer_fsuV1 T V)
    (fun x hx hxN => s134_rho_L1 S hxN hx) List.mem_cons_self
    (fun σ τ h1 h2 => K4L_mul σ h1 τ h2) (fun σ h => K4L_inv σ h) (fun σ h => K4L_sq σ h)
    (fun σ τ h1 h2 => hatK4L_comm σ h1 τ h2) (fun σ κ h1 h2 => A4_conj_K4L κ h2 σ h1)
    (fun σ h => ?_) hcL hcN (fun σ h => ?_) ⟨swap 0 1 * swap 4 5, fun σ h1 h2 =>
      (DA6_K4L σ ⟨h1, h2⟩).1⟩ (fun σ h1 h2 => (DA6_K4L σ ⟨h1, h2⟩).2)
  · rcases A4_cube_K4L σ h with h' | ⟨h3, τ, -, hτ⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h3, τ, hτ⟩
  · rw [hc]
    exact A4_gen_K4L σ h

structure S134Plus (S : A6.Setting134 G T L V) (Lp : Subgroup G) : Prop where
  eq : oTwoRes Lp = Lp
  le_L1 : Lp ≤ L₁Of L (fsuV1 T V)
  T_le : T ≤ normalizer (Lp : Set G)
  three : ∀ τ ∈ S14.C3, ∃ x : ↥(normalizer (V : Set G)), (x : G) ∈ Lp ∧ S.frame.ρ x = τ
  cent : Lp ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L

namespace S134Plus

variable {S : A6.Setting134 G T L V} {Lp : Subgroup G} (P : S134Plus S Lp)
include P

theorem le_L : Lp ≤ L := P.le_L1.trans ((oTwoRes_le _).trans inf_le_left)

theorem le_NV : Lp ≤ normalizer (V : Set G) := P.le_L.trans S.frame.L_le

theorem le_NV1 : Lp ≤ normalizer (fsuV1 T V : Set G) :=
  P.le_L1.trans ((oTwoRes_le _).trans inf_le_right)

theorem rho {x : ↥(normalizer (V : Set G))} (hx : (x : G) ∈ Lp) : InA4 (S.frame.ρ x) :=
  s134_rho_L1 S x.2 (P.le_L1 hx)

theorem mem_pCoreOf_of_K4 {x : ↥(normalizer (V : Set G))} (hx : (x : G) ∈ Lp)
    (hK : S.frame.ρ x ∈ K4L) : (x : G) ∈ pCoreOf 2 Lp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G :=
    { carrier := {y | y ∈ Lp ∧ ∃ hy : y ∈ normalizer (V : Set G), S.frame.ρ ⟨y, hy⟩ ∈ K4L}
      one_mem' := ⟨Lp.one_mem, one_mem _, by
        have : (⟨1, one_mem _⟩ : ↥(normalizer (V : Set G))) = 1 := rfl
        rw [this, map_one]
        exact List.mem_cons_self⟩
      mul_mem' := by
        rintro a b ⟨ha, haN, haK⟩ ⟨hb, hbN, hbK⟩
        refine ⟨Lp.mul_mem ha hb, mul_mem haN hbN, ?_⟩
        have : (⟨a * b, mul_mem haN hbN⟩ : ↥(normalizer (V : Set G))) = ⟨a, haN⟩ * ⟨b, hbN⟩ :=
          rfl
        rw [this, map_mul]
        exact K4L_mul _ haK _ hbK
      inv_mem' := by
        rintro a ⟨ha, haN, haK⟩
        refine ⟨Lp.inv_mem ha, inv_mem haN, ?_⟩
        have : (⟨a⁻¹, inv_mem haN⟩ : ↥(normalizer (V : Set G))) = (⟨a, haN⟩)⁻¹ := rfl
        rw [this, map_inv]
        exact K4L_inv _ haK }
  have hKp : IsPGroup 2 K := by
    rintro ⟨y, hyL, hyN, hyK⟩
    have hy2 : y ^ 2 ∈ Lp ⊓ centralizer (V : Set G) := by
      refine ⟨Lp.pow_mem hyL 2, (s134_rho_eq_one_iff S ⟨y ^ 2, pow_mem hyN 2⟩).1 ?_⟩
      have e : (⟨y ^ 2, pow_mem hyN 2⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyN⟩ ^ 2 := rfl
      rw [e, map_pow, pow_two]
      exact K4L_sq _ hyK
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, P.cent hy2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    show y ^ 2 ^ (k + 1) = 1
    rw [pow_succ', pow_mul, hk']
  have hKL : K ≤ Lp := fun y hy => hy.1
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKL ?_ hKp ⟨hx, x.2, hK⟩
  refine A5.le_normalizer_of_forall_conj_mem fun l hl y hy => ?_
  obtain ⟨hyL, hyN, hyK⟩ := hy
  have hlN := P.le_NV hl
  have hN : l * y * l⁻¹ ∈ normalizer (V : Set G) :=
    mul_mem (mul_mem hlN hyN) (inv_mem hlN)
  refine ⟨Lp.mul_mem (Lp.mul_mem hl hyL) (Lp.inv_mem hl), hN, ?_⟩
  have e : (⟨l * y * l⁻¹, hN⟩ : ↥(normalizer (V : Set G))) =
      ⟨l, hlN⟩ * ⟨y, hyN⟩ * ⟨l, hlN⟩⁻¹ := rfl
  obtain ⟨h4, h5, -⟩ := P.rho (x := ⟨l, hlN⟩) hl
  rw [e, map_mul, map_mul, map_inv]
  exact S14.K4_norm _ ⟨h4, h5⟩ _ hyK

theorem pCoreOf_le_T : pCoreOf 2 Lp ≤ T :=
  (A6.pCoreOf_le_pCoreOf_sup P.T_le).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)

theorem sup_inf_centralizer_le_T : (Lp ⊔ T) ⊓ centralizer (V : Set G) ≤ T := by
  rintro x ⟨hx, hxC⟩
  have hmul : ((Lp ⊔ T : Subgroup G) : Set G) = (Lp : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Lp T P.T_le
  have hx' : x ∈ (Lp : Set G) * (T : Set G) := by
    rw [← hmul]
    exact hx
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  have hlN := P.le_NV hl
  have htN := S.frame.T_le ht
  have hρ : S.frame.ρ (⟨l, hlN⟩ * ⟨t, htN⟩) = 1 :=
    (s134_rho_eq_one_iff S (⟨l, hlN⟩ * ⟨t, htN⟩)).2 hxC
  rw [map_mul] at hρ
  have hρl : S.frame.ρ ⟨l, hlN⟩ = (S.frame.ρ ⟨t, htN⟩)⁻¹ := eq_inv_of_mul_eq_one_left hρ
  have hD : InD6 (S.frame.ρ ⟨l, hlN⟩) := by
    rw [hρl, ← map_inv]
    exact S.frame.T_D _ (T.inv_mem ht)
  obtain ⟨h4, h5, hs⟩ := P.rho (x := ⟨l, hlN⟩) hl
  have hlT := P.pCoreOf_le_T (P.mem_pCoreOf_of_K4 hl (S14.D_A4 _ hD h4 h5 hs))
  exact T.mul_mem hlT ht

theorem pCoreOf_eq_r1Of : pCoreOf 2 (Lp ⊔ T) = r1Of T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf T (Lp ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hOT : pCoreOf 2 (Lp ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hPN : Lp ⊔ T ≤ normalizer (V : Set G) := sup_le P.le_NV S.frame.T_le
  have hP1 : ∀ x ∈ Lp ⊔ T, ∀ hx : x ∈ normalizer (V : Set G), InP1 (S.frame.ρ ⟨x, hx⟩) := by
    intro x hx hxN
    have hxV1 : x ∈ normalizer (fsuV1 T V : Set G) :=
      sup_le P.le_NV1 (T_le_normalizer_fsuV1 T V) hx
    exact inP1_of_pres45 _ (s134_pres45 S ⟨x, hxN⟩ hxV1)
  apply le_antisymm
  · intro x hx
    have hxT := hOT hx
    refine (s134_mem_r1Of_iff S).2 ⟨hxT, fun hxN => ?_⟩
    by_contra hK
    have key : ∀ (c : Perm (Fin 6)) (y : ↥(normalizer (V : Set G))), (y : G) ∈ Lp →
        S.frame.ρ y = c → (S.frame.ρ ⟨x, hxN⟩ * (c * S.frame.ρ ⟨x, hxN⟩ * c⁻¹)) ^ 16 = 1 := by
      intro c y hyL hyc
      have hyx : (y : G) * x * (y : G)⁻¹ ∈ pCoreOf 2 (Lp ⊔ T) :=
        (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 _
          (le_sup_left (b := T) hyL)) x).1 hx
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (Lp ⊔ T)
        ⟨x * ((y : G) * x * (y : G)⁻¹), mul_mem hx hyx⟩
      have hk' : (x * ((y : G) * x * (y : G)⁻¹)) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have hN : x * ((y : G) * x * (y : G)⁻¹) ∈ normalizer (V : Set G) :=
        mul_mem hxN (mul_mem (mul_mem y.2 hxN) (inv_mem y.2))
      have e : (⟨x * ((y : G) * x * (y : G)⁻¹), hN⟩ : ↥(normalizer (V : Set G))) =
          ⟨x, hxN⟩ * (y * ⟨x, hxN⟩ * y⁻¹) := rfl
      have h1 : S.frame.ρ ⟨x * ((y : G) * x * (y : G)⁻¹), hN⟩ ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : (⟨x * ((y : G) * x * (y : G)⁻¹), hN⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using hk')
        rw [this, map_one]
      rw [e, map_mul, map_mul, map_mul, map_inv, hyc] at h1
      exact pow_sixteen_of_two_pow h1
    obtain ⟨y₁, hy₁L, hy₁⟩ := P.three c012 (by decide)
    obtain ⟨y₂, hy₂L, hy₂⟩ := P.three c123 (by decide)
    rcases D_wit _ (S.frame.T_D ⟨x, hxN⟩ hxT) hK with h | h
    · exact h (key c012 y₁ hy₁L hy₁)
    · exact h (key c123 y₂ hy₂L hy₂)
  ·
    let K : Subgroup G :=
      { carrier := {y | y ∈ Lp ⊔ T ∧ ∃ hy : y ∈ normalizer (V : Set G),
          S.frame.ρ ⟨y, hy⟩ ∈ K4xList}
        one_mem' := ⟨one_mem _, one_mem _, by
          have : (⟨1, one_mem _⟩ : ↥(normalizer (V : Set G))) = 1 := rfl
          rw [this, map_one]
          exact List.mem_cons_self⟩
        mul_mem' := by
          rintro a b ⟨ha, haN, haK⟩ ⟨hb, hbN, hbK⟩
          refine ⟨mul_mem ha hb, mul_mem haN hbN, ?_⟩
          have : (⟨a * b, mul_mem haN hbN⟩ : ↥(normalizer (V : Set G))) = ⟨a, haN⟩ * ⟨b, hbN⟩ :=
            rfl
          rw [this, map_mul]
          exact K4x_mul _ haK _ hbK
        inv_mem' := by
          rintro a ⟨ha, haN, haK⟩
          refine ⟨inv_mem ha, inv_mem haN, ?_⟩
          have : (⟨a⁻¹, inv_mem haN⟩ : ↥(normalizer (V : Set G))) = (⟨a, haN⟩)⁻¹ := rfl
          rw [this, map_inv]
          exact K4x_inv _ haK }
    have hKp : IsPGroup 2 K := by
      rintro ⟨y, hyP, hyN, hyK⟩
      have hy2 : y ^ 2 ∈ (Lp ⊔ T) ⊓ centralizer (V : Set G) := by
        refine ⟨pow_mem hyP 2, (s134_rho_eq_one_iff S ⟨y ^ 2, pow_mem hyN 2⟩).1 ?_⟩
        have e : (⟨y ^ 2, pow_mem hyN 2⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyN⟩ ^ 2 := rfl
        rw [e, map_pow, pow_two]
        exact K4x_sq _ hyK
      obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨_, P.sup_inf_centralizer_le_T hy2⟩
      refine ⟨k + 1, Subtype.ext ?_⟩
      have hk' : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      show y ^ 2 ^ (k + 1) = 1
      rw [pow_succ', pow_mul, hk']
    have hKO : K ≤ pCoreOf 2 (Lp ⊔ T) := by
      have hKL : K ≤ Lp ⊔ T := fun y hy => hy.1
      refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKL ?_ hKp
      refine A5.le_normalizer_of_forall_conj_mem fun l hl y hy => ?_
      obtain ⟨hyP, hyN, hyK⟩ := hy
      have hlN := hPN hl
      have hN : l * y * l⁻¹ ∈ normalizer (V : Set G) := mul_mem (mul_mem hlN hyN) (inv_mem hlN)
      refine ⟨mul_mem (mul_mem hl hyP) (inv_mem hl), hN, ?_⟩
      have e : (⟨l * y * l⁻¹, hN⟩ : ↥(normalizer (V : Set G))) =
          ⟨l, hlN⟩ * ⟨y, hyN⟩ * ⟨l, hlN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact K4x_normal _ (hP1 l hl hlN) _ hyK
    intro x hx
    obtain ⟨hxT, hxK⟩ := (s134_mem_r1Of_iff S).1 hx
    exact hKO ⟨le_sup_right (a := Lp) hxT, S.frame.T_le hxT, hxK _⟩

end S134Plus

end CFSG.Quasithin.H13.U3
