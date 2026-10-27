module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OPstd

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ} {p : ℕ}

theorem eq_mul_of_add_two_mul {R : Type*} [CommRing R] {a b c : R} (hc : a + 2 * b = 0)
    (hc₂ : 1 + 2 * c = 0) : b = a * c := by
  linear_combination (-c) * hc + b * hc₂

theorem eq_mul_of_two_mul_add {R : Type*} [CommRing R] {a b c : R} (hc : 2 * a + b = 0)
    (hc₃ : 2 + c = 0) : b = a * c := by
  linear_combination hc - a * hc₃

namespace PModel

variable (h : PModel p H M)

@[expose] def s01H : H := ⟨s01GL, h.mono.s01_mem⟩

@[expose] def s12H : H := ⟨s12GL, h.mono.s12_mem⟩

@[expose] def s02H : H := ⟨s02GL, h.mono.s02_mem⟩

variable {ζ : Kˣ} (hζM : ζ ∈ M)

@[expose] noncomputable def xB (c : ℕ) : StatedProj H := proj H (h.ddH hζM 1 c)

@[expose] noncomputable def lineB (c : ℕ) : Subgroup (StatedProj H) :=
  Subgroup.zpowers (h.xB hζM c)

variable (hζ : orderOf ζ = p) [hp : Fact p.Prime]

include h hζM hζ

omit hp in
theorem xB_mem_pstd (c : ℕ) : h.xB hζM c ∈ pstd p H M :=
  mem_pstd.2 ⟨_, dd_mem_omegaP hζM hζ 1 c, rfl⟩

omit hp in
theorem xB_pow_p (c : ℕ) : h.xB hζM c ^ p = 1 := by
  rw [xB, ← map_pow, h.ddH_pow_p hζM hζ, map_one]

omit hp in
theorem lineB_le_pstd (c : ℕ) : h.lineB hζM c ≤ pstd p H M :=
  Subgroup.zpowers_le.2 (h.xB_mem_pstd hζM hζ c)

theorem proj_ddH_eq_pow_xB (c : ℕ) {a b : ℕ} (hb : (b : ZMod p) = a * c) :
    proj H (h.ddH hζM a b) = h.xB hζM c ^ a := by
  rw [xB, ← map_pow, h.ddH_pow hζM]
  congr 1
  exact h.ddH_congr hζM hζ (by simp) (by rw [hb]; push_cast; ring)

variable (hp5 : 5 ≤ p)
include hp5

theorem proj_comm_iff (s : H) (a b : ℕ) :
    proj H s * proj H (h.ddH hζM a b) = proj H (h.ddH hζM a b) * proj H s ↔
      s * h.ddH hζM a b = h.ddH hζM a b * s := by
  constructor
  · intro hc
    exact h.commute_of_proj_commute (by omega) hc (h.ddH_pow_p hζM hζ a b)
  · intro hc
    rw [← map_mul, ← map_mul, hc]

theorem proj_s01H_comm_iff (a b : ℕ) :
    proj H h.s01H * proj H (h.ddH hζM a b) = proj H (h.ddH hζM a b) * proj H h.s01H ↔
      (b : ZMod p) = a := by
  rw [h.proj_comm_iff hζM hζ hp5, ← s01_comm_dd_iff hζ a b, Subtype.ext_iff]
  rfl

theorem proj_s12H_comm_iff (a b : ℕ) :
    proj H h.s12H * proj H (h.ddH hζM a b) = proj H (h.ddH hζM a b) * proj H h.s12H ↔
      (a : ZMod p) + 2 * b = 0 := by
  rw [h.proj_comm_iff hζM hζ hp5, ← s12_comm_dd_iff hζ a b, Subtype.ext_iff]
  rfl

theorem proj_s02H_comm_iff (a b : ℕ) :
    proj H h.s02H * proj H (h.ddH hζM a b) = proj H (h.ddH hζM a b) * proj H h.s02H ↔
      2 * (a : ZMod p) + b = 0 := by
  rw [h.proj_comm_iff hζM hζ hp5, ← s02_comm_dd_iff hζ a b, Subtype.ext_iff]
  rfl

theorem commute_pstd_of_distinct {a b : ℕ} (hab : (a : ZMod p) ≠ b)
    (hbc : (a : ZMod p) + 2 * b ≠ 0) (hac : 2 * (a : ZMod p) + b ≠ 0) {g : H}
    (hg : proj H g * proj H (h.ddH hζM a b) = proj H (h.ddH hζM a b) * proj H g) :
    ∀ y ∈ pstd p H M, proj H g * y = y * proj H g := by
  have hcomm : g * h.ddH hζM a b = h.ddH hζM a b * g :=
    h.commute_of_proj_commute (by omega) hg (h.ddH_pow_p hζM hζ a b)
  have hmat : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      diagonal (fun i => ((![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹] i : Kˣ) : K)) =
      diagonal (fun i => ((![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹] i : Kˣ) : K)) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun z : H => (((z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hcomm
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_ddH, dd, coe_diagHom] using this
  have hdiag : IsDiag3 ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    isDiag3_of_commute_diagonal (injective_dd_entries hζ hab hbc hac) hmat
  have hgT : (g : GL (Fin 3) K) ∈ torus3 M := h.mem_torus3_of_isDiag3 g.2 hdiag
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_pstd.1 hy
  have : g * t = t * g := Subtype.ext (torus3_comm M hgT ht.1)
  rw [← map_mul, ← map_mul, this]

end PModel

end CFSG.Quasithin.H13.NQCore.U3O
