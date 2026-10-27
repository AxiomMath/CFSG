module

public import CFSG.Quasithin.H13.L32N1449Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.H13.Q1449Cert

open Mat8Cert L1442M S7Cert S8Cert G5Cert O3Cert

theorem permL_one (x : Fin 5 → ZMod 2) : permL 1 x = x := by
  funext i
  simp [permL_apply]

section Cert

variable {c : ℕ}
  {x₀ : GL (Fin 8) (ZMod 2)}

noncomputable def sigF (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (a : ↥(cenA c x₀)) : Equiv.Perm (Fin 5) :=
  Classical.choose (exists_sigma hc hx₀ a.2)

theorem sigF_spec (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (a : ↥(cenA c x₀)) (v : Fin 8 → ZMod 2) :
    betaL c (((a : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      permL (sigF hc hx₀ a) (betaL c v) :=
  Classical.choose_spec (exists_sigma hc hx₀ a.2) v

noncomputable def sigA (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    ↥(cenA c x₀) →* Equiv.Perm (Fin 5) where
  toFun := sigF hc hx₀
  map_one' := sigma_unique hc (sigF_spec hc hx₀ 1) fun v => by
    rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, permL_one]
  map_mul' a b := sigma_unique hc (sigF_spec hc hx₀ (a * b)) fun v => by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, sigF_spec, sigF_spec, permL_mul]

theorem sigA_spec (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (a : ↥(cenA c x₀)) (v : Fin 8 → ZMod 2) :
    betaL c (((a : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      permL (sigA hc hx₀ a) (betaL c v) :=
  sigF_spec hc hx₀ a v

theorem gen_spec (hc : c < 2) {g : GL (Fin 8) (ZMod 2)}
    (hg : colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈
      cenAg c (colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)))) :
    g ∈ gam c ∧ g * x₀ = x₀ * g ∧ g ^ 15 = 1 := by
  obtain ⟨h1, h2, h3⟩ := cenAg_sub hg
  exact ⟨(mem_gam_iff hc g).mpr h1, comm_of_cols h2, eq_one_of_colsOf (by rw [colsOf_pow, h3])⟩

theorem conj_mem_cenA (hc : c < 2) {s : GL (Fin 8) (ZMod 2)} (hs : s ∈ gam c)
    (hsx : s * x₀ = x₀ * s) {a : GL (Fin 8) (ZMod 2)} (ha : a ∈ cenA c x₀) :
    s * a * s⁻¹ ∈ cenA c x₀ := by
  have hsx' : s⁻¹ * x₀ = x₀ * s⁻¹ := by
    calc s⁻¹ * x₀ = s⁻¹ * (x₀ * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * x₀) * s⁻¹ := by rw [hsx]
      _ = x₀ * s⁻¹ := by group
  have hle : genSub (cenAg c (colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)))) ≤
      (cenA c x₀).comap (MulAut.conj s).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    obtain ⟨hgΓ, hgx, hg15⟩ := gen_spec hc hg
    show (MulAut.conj s) g ∈ cenA c x₀
    rw [MulAut.conj_apply]
    refine mem_cenA hc ((gam c).mul_mem ((gam c).mul_mem hs hgΓ) ((gam c).inv_mem hs)) ?_ ?_
    · calc s * g * s⁻¹ * x₀ = s * g * (s⁻¹ * x₀) := by group
        _ = s * g * (x₀ * s⁻¹) := by rw [hsx']
        _ = s * (g * x₀) * s⁻¹ := by group
        _ = s * (x₀ * g) * s⁻¹ := by rw [hgx]
        _ = (s * x₀) * g * s⁻¹ := by group
        _ = (x₀ * s) * g * s⁻¹ := by rw [hsx]
        _ = x₀ * (s * g * s⁻¹) := by group
    · rw [conj_pow, hg15, mul_one, mul_inv_cancel]
  exact hle ha

theorem sign_sigA (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (a : ↥(cenA c x₀)) : Equiv.Perm.sign (sigA hc hx₀ a) = 1 := by
  set f : ↥(cenA c x₀) →* ℤˣ := Equiv.Perm.sign.comp (sigA hc hx₀) with hf
  have hgen : ∀ g : ↥(cenA c x₀), (g : GL (Fin 8) (ZMod 2)) ∈
      {g : GL (Fin 8) (ZMod 2) | colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈
        cenAg c (colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)))} → g ∈ f.ker := by
    intro g hg
    obtain ⟨-, -, hg15⟩ := gen_spec hc hg
    have h1 : g ^ 15 = 1 := Subtype.ext (by simpa using hg15)
    have h2 : f g ^ 15 = 1 := by rw [← map_pow, h1, map_one]
    have h3 : f g ^ 2 = 1 := Int.units_sq (f g)
    rw [MonoidHom.mem_ker]
    calc f g = f g ^ 15 * (f g ^ 2)⁻¹ ^ 7 := by group
      _ = 1 := by rw [h2, h3, inv_one, one_pow, mul_one]
  have htop : Subgroup.closure (((cenA c x₀).subtype) ⁻¹'
      {g : GL (Fin 8) (ZMod 2) | colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈
        cenAg c (colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)))}) = ⊤ :=
    Subgroup.closure_preimage_eq_top _
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact (Subgroup.closure_le _).mpr fun g hg => hgen g hg
  have : a ∈ f.ker := hker ▸ Subgroup.mem_top a
  exact this

@[expose] noncomputable def sigA5 (hc : c < 2)
    (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    ↥(cenA c x₀) →* alternatingGroup (Fin 5) :=
  (sigA hc hx₀).codRestrict (alternatingGroup (Fin 5)) fun a =>
    Equiv.Perm.mem_alternatingGroup.mpr (sign_sigA hc hx₀ a)

theorem coe_sigA5 (hc : c < 2) (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c)
    (a : ↥(cenA c x₀)) : ((sigA5 hc hx₀ a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      sigA hc hx₀ a := rfl

theorem sigA5_bijective (hc : c < 2)
    (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    Function.Bijective (sigA5 hc hx₀) := by
  have hinj : Function.Injective (sigA5 hc hx₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : sigA hc hx₀ a = 1 := by
      have := congrArg Subtype.val ha
      rwa [coe_sigA5] at this
    have h2 : (a : GL (Fin 8) (ZMod 2)) = 1 := eq_one_of_beta hc hx₀ a.2 fun v => by
      rw [sigA_spec hc hx₀, h1, permL_one]
    exact Subtype.ext h2
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_cenA_x0 hc hx₀]
  exact CFSG.QuasithinUnique.A5.Delta5.a5_card.le

end Cert

end CFSG.Quasithin.H13.Q1449Cert
