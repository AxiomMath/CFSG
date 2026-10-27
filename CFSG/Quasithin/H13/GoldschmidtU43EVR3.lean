module

public import CFSG.Quasithin.H13.GoldschmidtU43EVR2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem conj_mem_Bg (hAU : (S.A : G) ∈ Uz z) {x b : G} (hx : x ∈ S.Vg) (hb : b ∈ S.Bg r) :
    x * b * x⁻¹ ∈ S.Bg r := by
  have hbV : b ∈ S.Vg := S.Bg_le_Vg r hAU hb
  have hcomm := (S.Vg_comm_mem hAU).2 x⁻¹ (S.Vg.inv_mem hx) b⁻¹ (S.Vg.inv_mem hbV)
  have e : x⁻¹⁻¹ * b⁻¹⁻¹ * x⁻¹ * b⁻¹ = (x * b * x⁻¹) * b⁻¹ := by group
  rw [e] at hcomm
  have hσB : (x * b * x⁻¹) * b⁻¹ ∈ S.Bg r := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm
    rw [← hk]
    exact zpow_mem (S.σ₁_mem_Bg r) k
  have := (S.Bg r).mul_mem hσB hb
  simpa [mul_assoc] using this

theorem Bg_eq_closure :
    S.Bg r = Subgroup.closure ({(S.σ₁ : G), S.rho3 r.ρ, S.rho4 r.ρ} : Set G) := by
  apply le_antisymm
  · rw [Bg, Subgroup.map_le_iff_le_comap, Ag, Subgroup.closure_le]
    have hc : S.a₂G⁻¹ * (S.σ₁ : G) * S.a₂G = (S.σ₁ : G) := by
      have h : S.a₂G * (S.σ₁ : G) = (S.σ₁ : G) * S.a₂G := congrArg Subtype.val S.a₂_comm_σ₁
      calc S.a₂G⁻¹ * (S.σ₁ : G) * S.a₂G = S.a₂G⁻¹ * ((S.σ₁ : G) * S.a₂G) := by group
        _ = S.a₂G⁻¹ * (S.a₂G * (S.σ₁ : G)) := by rw [h]
        _ = (S.σ₁ : G) := by group
    rintro y (rfl | rfl | rfl)
    · show S.a₂G⁻¹ * (S.σ₁ : G) * S.a₂G⁻¹⁻¹ ∈
        Subgroup.closure ({(S.σ₁ : G), S.rho3 r.ρ, S.rho4 r.ρ} : Set G)
      rw [inv_inv, hc]
      exact Subgroup.subset_closure (by simp)
    · show S.a₂G⁻¹ * r.ρ * S.a₂G⁻¹⁻¹ ∈
        Subgroup.closure ({(S.σ₁ : G), S.rho3 r.ρ, S.rho4 r.ρ} : Set G)
      rw [inv_inv]
      exact Subgroup.subset_closure (by simp [rho3])
    · show S.a₂G⁻¹ * S.rho2 r.ρ * S.a₂G⁻¹⁻¹ ∈
        Subgroup.closure ({(S.σ₁ : G), S.rho3 r.ρ, S.rho4 r.ρ} : Set G)
      rw [inv_inv]
      exact Subgroup.subset_closure (by simp [rho4])
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact S.σ₁_mem_Bg r
    · exact S.rho3_mem_Bg r
    · exact S.rho4_mem_Bg r

theorem z_conj_mem_Ag {x : G} (hx : x ∈ S.Ag r) : z * x * z⁻¹ ∈ S.Ag r := by
  have h : S.Ag r ≤ (S.Ag r).comap (MulAut.conj z).toMonoidHom := by
    rw [Ag, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · show z * (S.σ₁ : G) * z⁻¹ ∈ S.Ag r
      have : z * (S.σ₁ : G) * z⁻¹ = (S.σ₁ : G) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (z_comm_H S.σ₁).symm
      rw [this]
      exact S.σ₁_mem_Ag r
    · show z * r.ρ * z⁻¹ ∈ S.Ag r
      rw [r.inv]
      exact (S.Ag r).inv_mem (S.rho_mem_Ag r)
    · show z * S.rho2 r.ρ * z⁻¹ ∈ S.Ag r
      rw [S.z_rho2 r.inv]
      exact (S.Ag r).inv_mem (S.rho2_mem_Ag r)
  exact h hx

theorem a₂_conj_mem_Bg {x : G} (hx : x ∈ S.Ag r) : S.a₂G * x * S.a₂G⁻¹ ∈ S.Bg r := by
  have h : S.Ag r ≤ (S.Bg r).comap (MulAut.conj S.a₂G).toMonoidHom := by
    rw [Ag, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · show S.a₂G * (S.σ₁ : G) * S.a₂G⁻¹ ∈ S.Bg r
      have : S.a₂G * (S.σ₁ : G) * S.a₂G⁻¹ = (S.σ₁ : G) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact congrArg Subtype.val S.a₂_comm_σ₁
      rw [this]
      exact S.σ₁_mem_Bg r
    · show S.a₂G * r.ρ * S.a₂G⁻¹ ∈ S.Bg r
      rw [S.conj_a₂G_rho r.inv]
      exact (S.Bg r).inv_mem (S.rho3_mem_Bg r)
    · show S.a₂G * S.rho2 r.ρ * S.a₂G⁻¹ ∈ S.Bg r
      rw [S.conj_a₂G_rho2 r.inv]
      exact (S.Bg r).inv_mem (S.rho4_mem_Bg r)
  exact h hx

theorem conj_sigma_mem_Bg (hAU : (S.A : G) ∈ Uz z)
    (hμ₁ : (S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹ ∈ S.Ag r)
    (hμ₂ : (S.σ₂ : G) * S.rho4 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho4 r.ρ)⁻¹ ∈ S.Ag r)
    {b : G} (hb : b ∈ S.Bg r) :
    (S.a₂G * (S.σ₂ : G) * b * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ * (S.a₂G * b * S.a₂G⁻¹) ∈ S.Bg r := by
  have hσ₂C : (S.σ₂ : G) ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val S.σ₁σ₂_comm.symm
  have hgC : S.a₂G * (S.σ₂ : G) ∈ S.Cg1 := S.Cg1.mul_mem S.a₂G_mem_Cg1 hσ₂C
  have hσ₂M : (S.σ₂ : G) ∈ S.Mg := S.Tg_le_Mg S.σ₂G_mem_Tg
  have hσ₁s : (S.σ₂ : G) * (S.σ₁ : G) * (S.σ₂ : G)⁻¹ = (S.σ₁ : G) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val S.σ₁σ₂_comm.symm
  have hσ₁a : S.a₂G * (S.σ₁ : G) * S.a₂G⁻¹ = (S.σ₁ : G) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val S.a₂_comm_σ₁
  have hρ : S.a₂G * (S.σ₂ : G) * r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹ = (S.rho3 r.ρ)⁻¹ := by
    have h1 : (S.σ₂ : G) * r.ρ * (S.σ₂ : G)⁻¹ = r.ρ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact S.abelian_Mg _ r.mem_Mg _ hσ₂M |>.symm
    calc S.a₂G * (S.σ₂ : G) * r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹
        = S.a₂G * ((S.σ₂ : G) * r.ρ * (S.σ₂ : G)⁻¹) * S.a₂G⁻¹ := by group
      _ = (S.rho3 r.ρ)⁻¹ := by rw [h1, S.conj_a₂G_rho r.inv]
  have hρ' : S.a₂G * (S.σ₂ : G) * S.rho3 r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹ =
      (S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹) * r.ρ := by
    calc S.a₂G * (S.σ₂ : G) * S.rho3 r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹
        = S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹ *
            (S.a₂G * S.rho3 r.ρ * S.a₂G⁻¹) := by group
      _ = _ := by rw [S.conj_a₂G_rho3]
  have hρ4' : S.a₂G * (S.σ₂ : G) * S.rho4 r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹ =
      (S.a₂G * ((S.σ₂ : G) * S.rho4 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho4 r.ρ)⁻¹) * S.a₂G⁻¹) *
        S.rho2 r.ρ := by
    calc S.a₂G * (S.σ₂ : G) * S.rho4 r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹
        = S.a₂G * ((S.σ₂ : G) * S.rho4 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho4 r.ρ)⁻¹) * S.a₂G⁻¹ *
            (S.a₂G * S.rho4 r.ρ * S.a₂G⁻¹) := by group
      _ = _ := by rw [S.conj_a₂G_rho4]
  have hρ_V : r.ρ ∈ S.Vg := S.rho_mem_Vg hAU r
  have hρ₂_V : S.rho2 r.ρ ∈ S.Vg := S.rho2_mem_Vg hAU r
  have hB₁ : S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹ ∈ S.Bg r :=
    S.a₂_conj_mem_Bg r hμ₁
  have hB₂ : S.a₂G * ((S.σ₂ : G) * S.rho4 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho4 r.ρ)⁻¹) * S.a₂G⁻¹ ∈ S.Bg r :=
    S.a₂_conj_mem_Bg r hμ₂
  have hcV : ∀ b' ∈ S.Bg r, S.a₂G * (S.σ₂ : G) * b' * (S.a₂G * (S.σ₂ : G))⁻¹ ∈ S.Vg := by
    intro b' hb'
    have := S.conj_mem_Vg hgC (S.Bg_le_Vg r hAU hb')
    simpa [mul_assoc] using this
  rw [Bg_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · rw [show S.a₂G * (S.σ₂ : G) * (S.σ₁ : G) * (S.a₂G * (S.σ₂ : G))⁻¹ = (S.σ₁ : G) by
        calc S.a₂G * (S.σ₂ : G) * (S.σ₁ : G) * (S.a₂G * (S.σ₂ : G))⁻¹
            = S.a₂G * ((S.σ₂ : G) * (S.σ₁ : G) * (S.σ₂ : G)⁻¹) * S.a₂G⁻¹ := by group
          _ = (S.σ₁ : G) := by rw [hσ₁s, hσ₁a], hσ₁a]
      simp
    · rw [hρ', S.conj_a₂G_rho3]
      have h := S.conj_mem_Bg r hAU (x := r.ρ⁻¹) (S.Vg.inv_mem hρ_V)
        ((S.Bg r).inv_mem hB₁)
      have e : (S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹ *
          r.ρ)⁻¹ * r.ρ = r.ρ⁻¹ * (S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ *
          (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹)⁻¹ * r.ρ := by group
      rw [e]
      simpa [mul_assoc] using h
    · rw [hρ4', S.conj_a₂G_rho4]
      have h := S.conj_mem_Bg r hAU (x := (S.rho2 r.ρ)⁻¹) (S.Vg.inv_mem hρ₂_V)
        ((S.Bg r).inv_mem hB₂)
      have e : (S.a₂G * ((S.σ₂ : G) * S.rho4 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho4 r.ρ)⁻¹) * S.a₂G⁻¹ *
          S.rho2 r.ρ)⁻¹ * S.rho2 r.ρ = (S.rho2 r.ρ)⁻¹ * (S.a₂G * ((S.σ₂ : G) * S.rho4 r.ρ *
          (S.σ₂ : G)⁻¹ * (S.rho4 r.ρ)⁻¹) * S.a₂G⁻¹)⁻¹ * S.rho2 r.ρ := by group
      rw [e]
      simpa [mul_assoc] using h
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hyB : y ∈ S.Bg r := by rw [Bg_eq_closure]; exact hy
    have hgy := hcV y hyB
    have h1 := S.conj_mem_Bg r hAU (x := (S.a₂G * (S.σ₂ : G) * y * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹)
      (S.Vg.inv_mem hgy) ihx
    have e : (S.a₂G * (S.σ₂ : G) * (x * y) * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ *
        (S.a₂G * (x * y) * S.a₂G⁻¹) =
        ((S.a₂G * (S.σ₂ : G) * y * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ *
          ((S.a₂G * (S.σ₂ : G) * x * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ * (S.a₂G * x * S.a₂G⁻¹)) *
          (S.a₂G * (S.σ₂ : G) * y * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹⁻¹) *
        ((S.a₂G * (S.σ₂ : G) * y * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ * (S.a₂G * y * S.a₂G⁻¹)) := by
      group
    rw [e]
    exact (S.Bg r).mul_mem h1 ihy
  | inv x hx ih =>
    have hxB : x ∈ S.Bg r := by rw [Bg_eq_closure]; exact hx
    have hgx := hcV x hxB
    have h1 := S.conj_mem_Bg r hAU (x := S.a₂G * (S.σ₂ : G) * x * (S.a₂G * (S.σ₂ : G))⁻¹)
      hgx ((S.Bg r).inv_mem ih)
    have e : (S.a₂G * (S.σ₂ : G) * x⁻¹ * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ * (S.a₂G * x⁻¹ * S.a₂G⁻¹) =
        (S.a₂G * (S.σ₂ : G) * x * (S.a₂G * (S.σ₂ : G))⁻¹) *
          ((S.a₂G * (S.σ₂ : G) * x * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ * (S.a₂G * x * S.a₂G⁻¹))⁻¹ *
          (S.a₂G * (S.σ₂ : G) * x * (S.a₂G * (S.σ₂ : G))⁻¹)⁻¹ := by
      group
    rw [e]
    exact h1

theorem comm_sigma2_rho3 (e : S.Nbar ≃* alternatingGroup (Fin 6)) {V₃ : Subgroup G}
    (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z) :
    ∃ m : ℤ, (S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹ = (S.σ₁ : G) ^ m * r.ρ := by
  have hμ₁ := S.comm_sigma2_mem_Ag r hV hAU (S.rho3_mem_V3 hV hAU r) (S.rho3_mem_Ng e hV hAU r)
  have hμ₂ := S.comm_sigma2_mem_Ag r hV hAU (S.rho4_mem_V3 hV hAU r) (S.rho4_mem_Ng e hV hAU r)
  have hP := fun {b : G} (hb : b ∈ S.Bg r) => S.conj_sigma_mem_Bg r hAU hμ₁ hμ₂ hb
  have hσ₂M : (S.σ₂ : G) ∈ S.Mg := S.Tg_le_Mg S.σ₂G_mem_Tg
  have hg3 : S.a₂G * (S.σ₂ : G) * (S.a₂G * (S.σ₂ : G)) * (S.a₂G * (S.σ₂ : G)) = 1 :=
    congrArg Subtype.val S.a₂σ₂_cube
  have hcρ : S.a₂G * (S.σ₂ : G) * r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹ = (S.rho3 r.ρ)⁻¹ := by
    have h1 : (S.σ₂ : G) * r.ρ * (S.σ₂ : G)⁻¹ = r.ρ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (S.abelian_Mg _ r.mem_Mg _ hσ₂M).symm
    calc S.a₂G * (S.σ₂ : G) * r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹
        = S.a₂G * ((S.σ₂ : G) * r.ρ * (S.σ₂ : G)⁻¹) * S.a₂G⁻¹ := by group
      _ = (S.rho3 r.ρ)⁻¹ := by rw [h1, S.conj_a₂G_rho r.inv]
  have hcρ₃ : S.a₂G * (S.σ₂ : G) * S.rho3 r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹ =
      (S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹) * r.ρ := by
    calc S.a₂G * (S.σ₂ : G) * S.rho3 r.ρ * (S.a₂G * (S.σ₂ : G))⁻¹
        = S.a₂G * ((S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹) * S.a₂G⁻¹ *
            (S.a₂G * S.rho3 r.ρ * S.a₂G⁻¹) := by group
      _ = _ := by rw [S.conj_a₂G_rho3]
  set a : G := S.a₂G with ha
  set s : G := (S.σ₂ : G) with hs
  set ρ : G := r.ρ with hρ
  set ρ₃ : G := S.rho3 ρ with hρ₃
  set μ₁ : G := s * ρ₃ * s⁻¹ * ρ₃⁻¹ with hμ₁def
  set g : G := a * s with hg
  set β : G := (a * μ₁ * a⁻¹)⁻¹ with hβ
  have hβB : β ∈ S.Bg r := (S.Bg r).inv_mem (S.a₂_conj_mem_Bg r hμ₁)
  have hfin : g * β * g⁻¹ = ρ₃⁻¹ * ρ := by
    have hρg : g * ρ * g⁻¹ = ρ₃⁻¹ := hcρ
    have hρ₃g : g * ρ₃ * g⁻¹ = (a * μ₁ * a⁻¹) * ρ := hcρ₃
    calc g * β * g⁻¹ = ρ₃⁻¹ * (ρ₃ * (g * β * g⁻¹)) := by group
      _ = ρ₃⁻¹ * (g * (g * (g * ρ * g⁻¹) * g⁻¹) * g⁻¹) := by
          congr 1
          rw [hρg]
          calc ρ₃ * (g * β * g⁻¹) = (g * ρ * g⁻¹)⁻¹ * (g * β * g⁻¹) := by rw [hρg]; group
            _ = g * (ρ⁻¹ * β) * g⁻¹ := by group
            _ = g * (((a * μ₁ * a⁻¹) * ρ)⁻¹) * g⁻¹ := by
                congr 2
                rw [hβ]
                group
            _ = g * (g * ρ₃ * g⁻¹)⁻¹ * g⁻¹ := by rw [hρ₃g]
            _ = g * (g * ρ₃⁻¹ * g⁻¹) * g⁻¹ := by group
      _ = ρ₃⁻¹ * ρ := by
          have : g * (g * (g * ρ * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * ρ * (g * g * g)⁻¹ := by group
          rw [this]
          have h3 : g * g * g = 1 := hg3
          rw [h3]
          group
  have h1 := hP hβB
  rw [hfin] at h1
  set y : G := a * β * a⁻¹ with hy
  have hyz : y = (z * μ₁ * z⁻¹)⁻¹ := by
    have key : ∀ x μ : G, x * (x * μ * x⁻¹)⁻¹ * x⁻¹ = ((x * x) * μ * (x * x)⁻¹)⁻¹ := by
      intro x μ
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [hy, hβ, key a μ₁, S.a₂G_mul_a₂G]
  have hyA : y ∈ S.Ag r := by
    rw [hyz]
    exact (S.Ag r).inv_mem (S.z_conj_mem_Ag r hμ₁)
  have hyV : y ∈ S.Vg := S.Ag_le_Vg r hAU hyA
  have hρ₃B : ρ₃ ∈ S.Bg r := S.rho3_mem_Bg r
  have h2 := S.conj_mem_Bg r hAU (x := y⁻¹) (S.Vg.inv_mem hyV) hρ₃B
  have h3 : ρ⁻¹ * y ∈ S.Bg r := by
    have e : ρ⁻¹ * y = ((ρ₃⁻¹ * ρ)⁻¹ * y) * (y⁻¹ * ρ₃ * y⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact (S.Bg r).mul_mem h1 ((S.Bg r).inv_mem h2)
  have h4 : ρ⁻¹ * y ∈ S.Ag r :=
    (S.Ag r).mul_mem ((S.Ag r).inv_mem (S.rho_mem_Ag r)) hyA
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.Ag_inf_Bg r hAU h4 h3)
  refine ⟨-k, ?_⟩
  have hyk : y = ρ * (S.σ₁ : G) ^ k := by
    rw [hk]
    group
  have hcz : Commute z (S.σ₁ : G) := (z_comm_H S.σ₁).symm
  have hσk : z⁻¹ * (S.σ₁ : G) ^ (-k) * z = (S.σ₁ : G) ^ (-k) := by
    have := (hcz.zpow_right (-k)).eq
    calc z⁻¹ * (S.σ₁ : G) ^ (-k) * z = z⁻¹ * ((S.σ₁ : G) ^ (-k) * z) := by group
      _ = z⁻¹ * (z * (S.σ₁ : G) ^ (-k)) := by rw [this]
      _ = (S.σ₁ : G) ^ (-k) := by group
  have hzρ : z⁻¹ * ρ⁻¹ * z = ρ := by
    have h : z * ρ * z⁻¹ = ρ⁻¹ := r.inv
    have hzi : z⁻¹ = z := S.z_inv
    rw [hzi]
    have h' : z * ρ⁻¹ * z⁻¹ = ρ := by
      calc z * ρ⁻¹ * z⁻¹ = (z * ρ * z⁻¹)⁻¹ := by group
        _ = ρ := by rw [h]; group
    rw [← hzi] at h' ⊢
    simpa [hzi] using h'
  have hμy : z * μ₁ * z⁻¹ = y⁻¹ := by rw [hyz]; group
  calc μ₁ = z⁻¹ * (z * μ₁ * z⁻¹) * z := by group
    _ = z⁻¹ * y⁻¹ * z := by rw [hμy]
    _ = z⁻¹ * ((S.σ₁ : G) ^ (-k) * ρ⁻¹) * z := by
        rw [hyk]
        group
    _ = (z⁻¹ * (S.σ₁ : G) ^ (-k) * z) * (z⁻¹ * ρ⁻¹ * z) := by group
    _ = (S.σ₁ : G) ^ (-k) * ρ := by rw [hσk, hzρ]

end JWSetup

end CFSG.Quasithin.H13.U43
