module

public import CFSG.Sporadic.Co1Patterson.RigidSwap
public import CFSG.Sporadic.Co1Patterson.GlueTwist
public import CFSG.Sporadic.Co1Patterson.TwistNativeType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.LargeExtraspecial.S14
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

theorem setting_center_eq {G : Type*} [Group G] (S : Setting G) {x : S.M}
    (hx : ∀ y : S.M, x * y = y * x) : x = 1 ∨ x = S.zM := by
  have hxQ : x ∈ S.Q := S.centralizer_le (mem_centralizer_iff.2 fun y _ => (hx y).symm)
  have hc : (⟨x, hxQ⟩ : S.Q) ∈ center S.Q :=
    mem_center_iff.2 fun y => Subtype.ext (hx y).symm
  rcases S.mem_center_Q_iff.1 hc with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

section Twist

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H : Type} [Group H] (S : ExtraspecialTypeSystem n L act qf bil H) {E : Type*} [Group E]
  {π : E →* L} {ζ : E} (hζ : π ζ = 1)

@[expose] def z1Fib : fibreProd S.φ π := ⟨(S.z, 1), by rw [mem_fibreProd, S.φ_z, map_one]⟩

@[expose] def twZ : Twist S π ζ hζ := QuotientGroup.mk (z1Fib S)

theorem twZ_mem_center : twZ S hζ ∈ center (Twist S π ζ hζ) := by
  refine mem_center_iff.2 fun y => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [twZ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  refine Subtype.ext (Prod.ext (S.z_comm _) ?_)
  show (g : H × E).2 * 1 = 1 * (g : H × E).2
  rw [mul_one, one_mul]

theorem twZ_ne_one (hζc : ∀ e, ζ * e = e * ζ) (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1) :
    twZ S hζ ≠ 1 := by
  intro h
  rw [twZ, ← QuotientGroup.mk_one, mk_eq_mk_iff_twist S hζ hζc hζ2] at h
  rcases h with h | h
  · exact S.z_ne_one (congrArg (fun g : fibreProd S.φ π => (g : H × E).1) h).symm
  · have := congrArg (fun g : fibreProd S.φ π => (g : H × E).2) h
    simp only [OneMemClass.coe_one, Prod.snd_one, Subgroup.coe_mul, Prod.snd_mul] at this
    exact hζ1 (by simpa [zζ, z1Fib] using this.symm)

@[expose] noncomputable def twPhi : Twist S π ζ hζ →* L :=
  QuotientGroup.lift _ (S.φ.comp ((MonoidHom.fst H E).comp (fibreProd S.φ π).subtype))
    (normalClosure_le_normal (by
      rintro _ rfl
      show S.φ S.z = 1
      exact S.φ_z))

theorem twPhi_mk (g : fibreProd S.φ π) :
    twPhi S hζ (QuotientGroup.mk g) = S.φ (g : H × E).1 := rfl

theorem isPGroup_ker_twPhi (hπ : ∀ e, π e = 1 → e = 1 ∨ e = ζ) (hζ2 : ζ * ζ = 1) :
    IsPGroup 2 (twPhi S hζ).ker := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x : Twist S π ζ hζ)
  refine ⟨2, Subtype.ext ?_⟩
  have hq : S.φ (g : H × E).1 = 1 := by
    have := x.2
    rw [MonoidHom.mem_ker, ← hg, twPhi_mk] at this
    exact this
  have he : π (g : H × E).2 = 1 := by rw [← mem_fibreProd.1 g.2, hq]
  have hq4 : (g : H × E).1 ^ 4 = 1 := by
    rcases zmod_two_cases (qf (S.vec (g : H × E).1)) with h0 | h1
    · have := (S.mul_self_eq_one_iff _ hq).2 h0
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, this, one_mul]
    · have := (S.mul_self_eq_z_iff _ hq).2 h1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, this, S.z_mul_self]
  have he4 : (g : H × E).2 ^ 4 = 1 := by
    rcases hπ _ he with h0 | h0
    · rw [h0, one_pow]
    · rw [h0, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hζ2, one_mul]
  rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hg, ← QuotientGroup.mk_pow]
  rw [show (2 ^ 2 : ℕ) = 4 from rfl]
  rw [show g ^ 4 = 1 from Subtype.ext (Prod.ext hq4 he4), QuotientGroup.mk_one]

end Twist

section Transport

variable {X : Type} [Group X] [Finite X] {t : X} {T : Type*} [Group T]

theorem σ_t_eq (h : PattersonCo1Hyp X t) (σ : centralizer ({t} : Set X) ≃* T) {z : T}
    (hz : z ∈ center T) (hz1 : z ≠ 1) :
    σ ⟨t, mem_centralizer_singleton_self t⟩ = z := by
  have hc : ∀ y : centralizer ({t} : Set X), σ.symm z * y = y * σ.symm z := fun y => by
    apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mem_center_iff.1 hz]
  rcases setting_center_eq (setting h) (x := σ.symm z) hc with h1 | h1
  · exact absurd (σ.symm.map_eq_one_iff.1 h1) hz1
  · rw [← σ.apply_symm_apply z]
    exact congrArg σ h1.symm

theorem symm_mem_QG (h : PattersonCo1Hyp X t) (σ : centralizer ({t} : Set X) ≃* T)
    {N : Subgroup T} (hN : N.Normal) (hP : IsPGroup 2 N) {w : T} (hw : w ∈ N) :
    ((σ.symm w : centralizer ({t} : Set X)) : X) ∈ (setting h).QG := by
  have hle := (setting h).le_of_normal (N.comap σ.toMonoidHom) (hN.comap _)
    (hP.comap_of_injective _ σ.injective)
  have hc : σ.symm w ∈ N.comap σ.toMonoidHom := by
    change σ (σ.symm w) ∈ N
    rw [MulEquiv.apply_symm_apply]
    exact hw
  have hmem : σ.symm w ∈ (setting h).Q := hle hc
  exact (setting h).mem_QG_iff.2 ⟨(σ.symm w).2, hmem⟩

end Transport

end CFSG.Sporadic.Co1Patterson.TwistNative
