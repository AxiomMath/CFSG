module

public import CFSG.Quasithin.H13.A6S4L1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def invT (σ : Perm (Fin 6)) : Perm (Fin 6) :=
  if swap 1 2 * swap 4 5 * σ * (swap 1 2 * swap 4 5)⁻¹ = σ⁻¹ then swap 1 2 * swap 4 5
  else if swap 1 3 * swap 4 5 * σ * (swap 1 3 * swap 4 5)⁻¹ = σ⁻¹ then swap 1 3 * swap 4 5
  else swap 2 3 * swap 4 5

@[expose] def HatCubeAt (σ : Perm (Fin 6)) : Prop :=
  σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 →
    σ ∈ K4L ∨ (σ * σ * σ = 1 ∧ Perm.sign (invT σ) = 1 ∧ invT σ * σ * (invT σ)⁻¹ = σ⁻¹)

instance (σ : Perm (Fin 6)) : Decidable (HatCubeAt σ) := by unfold HatCubeAt; infer_instance

theorem hatCubeAt_all : ∀ σ : Perm (Fin 6), HatCubeAt σ := by
  decide +kernel

theorem K4L_comm : ∀ σ ∈ K4L, ∀ τ ∈ K4L, σ * τ = τ * σ := by decide +kernel

theorem one_mem_K4L : (1 : Perm (Fin 6)) ∈ K4L := List.mem_cons_self

theorem cube_mem_K4L {σ : Perm (Fin 6)} (h4 : σ 4 = 4) (h5 : σ 5 = 5) (hs : Perm.sign σ = 1) :
    σ ^ 3 ∈ K4L := by
  rw [pow_three]
  rcases hatCubeAt_all σ h4 h5 hs with h | ⟨h, -⟩
  · rw [K4L_sq σ h, mul_one]
    exact h
  · rw [← mul_assoc, h]
    exact one_mem_K4L

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem cube_mem_pCoreOf_L1 (hhat : ¬ IsHatA6 L) {x : G}
    (hx : x ∈ S.L1) :
    x ^ 3 ∈ pCoreOf 2 S.L1 := by
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hx)
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨x, hxN⟩) hx
  have h := S.mem_pCoreOf_L1_of_K4 hhat (x := ⟨x, hxN⟩ ^ 3) (by simpa using S.L1.pow_mem hx 3)
    (by rw [map_pow]; exact cube_mem_K4L h4 h5 hs)
  simpa using h

theorem mk_mem_center {y : ↥L}
    (hy : (y : G) ∈ Subgroup.centralizer (V : Set G)) :
    (y : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨x, hx, hxy⟩ := S.centralizer_le_o2Z ⟨y.2, hy⟩
  have e : x = y := Subtype.ext hxy
  subst e
  exact hx

omit [Finite G] S in
theorem cube_of_mem_center (hhat : IsHatA6 L) {ζ : ↥L ⧸ CFSG.pCore 2 ↥L}
    (hζ : ζ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) : ζ ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) (x := ⟨ζ, hζ⟩)
  rw [hhat.2.1] at h
  exact congrArg Subtype.val h

theorem mem_centralizer_of_rho {y : G} (g : ↥(Subgroup.normalizer (V : Set G))) (hg : (g : G) = y)
    (h : S.frame.ρ g = 1) : y ∈ Subgroup.centralizer (V : Set G) :=
  hg ▸ (S.rho_eq_one_iff g).1 h

theorem mk_comm_of_K4 (hhat : IsHatA6 L) {a b : ↥L}
    (ha : (a : G) ∈ S.L1K4) (hb : (b : G) ∈ S.L1K4) :
    (a : ↥L ⧸ CFSG.pCore 2 ↥L) * (b : ↥L ⧸ CFSG.pCore 2 ↥L) =
      (b : ↥L ⧸ CFSG.pCore 2 ↥L) * (a : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨haN, haK, -⟩ := S.mem_L1K4.1 ha
  obtain ⟨hbN, hbK, -⟩ := S.mem_L1K4.1 hb
  set α : ↥L ⧸ CFSG.pCore 2 ↥L := (a : ↥L ⧸ CFSG.pCore 2 ↥L) with hα
  set β : ↥L ⧸ CFSG.pCore 2 ↥L := (b : ↥L ⧸ CFSG.pCore 2 ↥L) with hβ
  have hcC : ((a * b * a⁻¹ * b⁻¹ : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine S.mem_centralizer_of_rho (⟨a, haN⟩ * ⟨b, hbN⟩ * (⟨a, haN⟩)⁻¹ * (⟨b, hbN⟩)⁻¹) rfl ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, K4L_comm _ haK _ hbK]
    group
  have haC : ((a * a : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine S.mem_centralizer_of_rho (⟨a, haN⟩ * ⟨a, haN⟩) rfl ?_
    rw [map_mul]
    exact K4L_sq _ haK
  have hγ := S.mk_mem_center hcC
  have hα2 := S.mk_mem_center haC
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
  have hγ3 : γ ^ 3 = 1 := cube_of_mem_center hhat hγ
  have hγ1 : γ = 1 := by
    rw [pow_three, hγ2, mul_one] at hγ3
    exact hγ3
  calc α * β = γ * β * α := by rw [hγdef]; group
    _ = β * α := by rw [hγ1, one_mul]

@[expose] def E2 (hhat : IsHatA6 L) : Subgroup G where
  carrier := {y | y ∈ S.L1K4 ∧ y * y ∈ pCoreOf 2 L}
  mul_mem' := by
    rintro y₁ y₂ ⟨h1K, h1O⟩ ⟨h2K, h2O⟩
    refine ⟨S.L1K4.mul_mem h1K h2K, ?_⟩
    have hy₁L : y₁ ∈ L := S.L1_le_L (S.mem_L1K4.1 h1K).2.2
    have hy₂L : y₂ ∈ L := S.L1_le_L (S.mem_L1K4.1 h2K).2.2
    have hc := S.mk_comm_of_K4 hhat (a := ⟨y₁, hy₁L⟩) (b := ⟨y₂, hy₂L⟩) h1K h2K
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
  one_mem' := ⟨S.L1K4.one_mem, by rw [one_mul]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro y ⟨hK, hO⟩
    refine ⟨S.L1K4.inv_mem hK, ?_⟩
    have : y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hO

theorem E2_le (hhat : IsHatA6 L) : S.E2 hhat ≤ pCoreOf 2 S.L1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 (fun y hy => (S.mem_L1K4.1 hy.1).2.2) ?_ ?_
  · refine A5.le_normalizer_of_forall_conj_mem fun l hl y hy => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (S.L1_le_normalizer_L1K4 hl) y).mp hy.1
    · have e : l * y * l⁻¹ * (l * y * l⁻¹) = l * (y * y) * l⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (S.L1_le_L hl)) _).mp
        hy.2
  · rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, hy.2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (y * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    show y ^ 2 ^ (k + 1) = 1
    rw [pow_succ', pow_mul, ← hk', sq]

theorem cube_mem_pCoreOf_L1_hat (hhat : IsHatA6 L) {x : G}
    (hx : x ∈ S.L1) :
    x ^ 3 ∈ pCoreOf 2 S.L1 := by
  apply S.E2_le hhat
  have hxL : x ∈ L := S.L1_le_L hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hxL
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨x, hxN⟩) hx
  set X : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) with hX
  have hx3N : x ^ 3 ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hxN 3
  have hρ3 : S.frame.ρ ⟨x ^ 3, hx3N⟩ = S.frame.ρ ⟨x, hxN⟩ ^ 3 := by
    rw [← map_pow]
    rfl
  have hx3K : x ^ 3 ∈ S.L1K4 :=
    S.mem_L1K4.2 ⟨hx3N, by rw [hρ3]; exact cube_mem_K4L h4 h5 hs, S.L1.pow_mem hx 3⟩
  refine ⟨hx3K, ?_⟩
  suffices h6 : X ^ 6 = 1 by
    have h : ((⟨x, hxL⟩ ^ 6 : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [QuotientGroup.mk_pow, ← hX, h6]
    rw [QuotientGroup.eq_one_iff, mem_pCore_iff] at h
    have e : x ^ 3 * x ^ 3 = x ^ 6 := by rw [← pow_add]
    rw [e]
    simpa using h
  rcases hatCubeAt_all _ h4 h5 hs with hK | ⟨h3, hτs, hτ⟩
  ·
    have hC : ((⟨x, hxL⟩ * ⟨x, hxL⟩ : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
      refine S.mem_centralizer_of_rho (⟨x, hxN⟩ * ⟨x, hxN⟩) rfl ?_
      rw [map_mul]
      exact K4L_sq _ hK
    have hz := cube_of_mem_center hhat (S.mk_mem_center hC)
    simp only [QuotientGroup.mk_mul] at hz
    rw [← hX] at hz
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_two]
    exact hz
  ·
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L (invT (S.frame.ρ ⟨x, hxN⟩))).2
      (Perm.mem_alternatingGroup.2 hτs)
    set Y : ↥L ⧸ CFSG.pCore 2 ↥L := ((⟨(g : G), hgL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) with hY
    have hC3 : ((⟨x, hxL⟩ ^ 3 : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
      refine S.mem_centralizer_of_rho (⟨x, hxN⟩ ^ 3) (by simp) ?_
      rw [map_pow, pow_three, ← mul_assoc]
      exact h3
    have hw := S.mk_mem_center hC3
    simp only [QuotientGroup.mk_pow] at hw
    rw [← hX] at hw
    have hkC : ((⟨(g : G), hgL⟩ * ⟨x, hxL⟩ * (⟨(g : G), hgL⟩)⁻¹ * ⟨x, hxL⟩ : ↥L) : G) ∈
        Subgroup.centralizer (V : Set G) := by
      refine S.mem_centralizer_of_rho (g * ⟨x, hxN⟩ * g⁻¹ * ⟨x, hxN⟩) rfl ?_
      rw [map_mul, map_mul, map_mul, map_inv, hg, hτ, inv_mul_cancel]
    have hκ := S.mk_mem_center hkC
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hκ
    rw [← hX, ← hY] at hκ
    set κ := Y * X * Y⁻¹ * X with hκdef
    have e1 : Y * X * Y⁻¹ = κ * X⁻¹ := by rw [hκdef]; group
    have hκ3 : κ ^ 3 = 1 := cube_of_mem_center hhat hκ
    have e2 : Y * X ^ 3 * Y⁻¹ = (X ^ 3)⁻¹ := by
      rw [← conj_pow, e1, (Commute.mul_pow (Subgroup.mem_center_iff.mp hκ X⁻¹).symm 3), hκ3,
        one_mul, inv_pow]
    have e3 : Y * X ^ 3 * Y⁻¹ = X ^ 3 := by
      rw [(Subgroup.mem_center_iff.mp hw Y)]
      group
    have h33 : X ^ 3 * X ^ 3 = 1 := by
      have h := e3.symm.trans e2
      calc X ^ 3 * X ^ 3 = (X ^ 3)⁻¹ * X ^ 3 := by rw [← h]
        _ = 1 := inv_mul_cancel _
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add]
    exact h33

end Setting4

end CFSG.Quasithin.H13.A6
