module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Centre
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

section InnerO

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.exists_inner_order_three_twE6
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) (hp : p = 3) (hf : 1 ≤ f)
    (hZ : Subgroup.center ↥G₀ = ⊥) (act : TwE6Act G₀ B hf)
    (hin : ∀ b : ↥B, (act.lam b : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQEquiv hf).toRingHom) :
    ∃ g ∈ G₀, orderOf g = 3 ∧ (∀ y ∈ G₀, x * y * x⁻¹ = g * y * g⁻¹) ∧
      L ≤ Subgroup.centralizer ({g} : Set X) := by
  classical
  let bx : ↥B := ⟨x, h.d_le h.x_mem⟩
  let cC : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    ⟨(act.lam bx : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hin bx⟩
  obtain ⟨q, hq⟩ := act.θ.surjective cC
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hx3 : x ^ 3 = 1 := by
    have hxp : x ^ p = 1 := h.b_elem.2 x (h.d_le h.x_mem)
    rwa [hp] at hxp
  have hmem : ∀ y : ↥G₀, x * (y : X) * x⁻¹ ∈ G₀ := fun y =>
    (Subgroup.mem_normalizer_iff.mp (h.b_norm (h.d_le h.x_mem)) (y : X)).mp y.2
  have hconj : ∀ y : ↥G₀, x * (y : X) * x⁻¹ = (g₀ : X) * (y : X) * (g₀ : X)⁻¹ := by
    intro y
    let y' : ↥G₀ := ⟨x * (y : X) * x⁻¹, hmem y⟩
    have hact := act.act bx y y' rfl
    have hRHS : ((act.θ (QuotientGroup.mk (g₀ * y * g₀⁻¹)) :
        ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((act.lam bx : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          ((act.θ (QuotientGroup.mk y) :
            ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          (act.lam bx : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      simp only [map_mul, map_inv]
      rw [hq]
      rfl
    have hmk : QuotientGroup.mk y' = QuotientGroup.mk (g₀ * y * g₀⁻¹) :=
      act.θ.injective (Subtype.ext (hact.trans hRHS.symm))
    have hmem2 : y'⁻¹ * (g₀ * y * g₀⁻¹) ∈ Subgroup.center ↥G₀ :=
      QuotientGroup.eq.mp hmk
    rw [hZ, Subgroup.mem_bot] at hmem2
    have hy' : y' = g₀ * y * g₀⁻¹ := inv_mul_eq_one.mp hmem2
    simpa using congrArg Subtype.val hy'
  have hconj' : ∀ y : ↥G₀, (g₀ : X) * (y : X) * (g₀ : X)⁻¹ = x * (y : X) * x⁻¹ :=
    fun y => (hconj y).symm
  have hcent : (g₀ : X) ^ 3 ∈ Subgroup.centralizer (G₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hmem1 : x * (y : X) * x⁻¹ ∈ G₀ := hmem ⟨y, hy⟩
    have hmem2 : x * (x * (y : X) * x⁻¹) * x⁻¹ ∈ G₀ :=
      (Subgroup.mem_normalizer_iff.mp (h.b_norm (h.d_le h.x_mem))
        (x * (y : X) * x⁻¹)).mp hmem1
    have e1 : (g₀ : X) * (y : X) * (g₀ : X)⁻¹ = x * (y : X) * x⁻¹ :=
      hconj' ⟨y, hy⟩
    have e2 : (g₀ : X) * (x * (y : X) * x⁻¹) * (g₀ : X)⁻¹ =
        x * (x * (y : X) * x⁻¹) * x⁻¹ := hconj' ⟨x * (y : X) * x⁻¹, hmem1⟩
    have e3 : (g₀ : X) * (x * (x * (y : X) * x⁻¹) * x⁻¹) * (g₀ : X)⁻¹ =
        x * (x * (x * (y : X) * x⁻¹) * x⁻¹) * x⁻¹ :=
      hconj' ⟨x * (x * (y : X) * x⁻¹) * x⁻¹, hmem2⟩
    have hg3mul : (g₀ : X) ^ 3 = (g₀ : X) * (g₀ : X) * (g₀ : X) := by
      rw [pow_succ, pow_succ, pow_one]
    have hx3mul : x ^ 3 = x * x * x := by
      rw [pow_succ, pow_succ, pow_one]
    have hcalc : (g₀ : X) ^ 3 * (y : X) * ((g₀ : X) ^ 3)⁻¹ = (y : X) := by
      calc (g₀ : X) ^ 3 * (y : X) * ((g₀ : X) ^ 3)⁻¹
          = (g₀ : X) * ((g₀ : X) * ((g₀ : X) * (y : X) * (g₀ : X)⁻¹) *
              (g₀ : X)⁻¹) * (g₀ : X)⁻¹ := by rw [hg3mul]; group
        _ = (g₀ : X) * ((g₀ : X) * (x * (y : X) * x⁻¹) * (g₀ : X)⁻¹) *
              (g₀ : X)⁻¹ := by rw [e1]
        _ = (g₀ : X) * (x * (x * (y : X) * x⁻¹) * x⁻¹) * (g₀ : X)⁻¹ := by rw [e2]
        _ = x * (x * (x * (y : X) * x⁻¹) * x⁻¹) * x⁻¹ := by rw [e3]
        _ = (y : X) := by
              rw [show x * (x * (x * (y : X) * x⁻¹) * x⁻¹) * x⁻¹ =
                (x * x * x) * (y : X) * (x * x * x)⁻¹ by group,
                ← hx3mul, hx3]
              group
    have hcy : (g₀ : X) ^ 3 * (y : X) = (y : X) * (g₀ : X) ^ 3 := by
      have h := congrArg (fun z : X => z * (g₀ : X) ^ 3) hcalc
      simpa [mul_assoc] using h
    exact hcy.symm
  have hcenter : (g₀ : ↥G₀) ^ 3 ∈ Subgroup.center ↥G₀ := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have h := (Subgroup.mem_centralizer_iff.mp hcent) (w : X) w.2
    simpa [Subgroup.coe_mul, Subgroup.coe_pow] using h
  have hg3 : (g₀ : X) ^ 3 = 1 := by
    have hbot : (g₀ : ↥G₀) ^ 3 ∈ (⊥ : Subgroup ↥G₀) := by
      simpa [hZ] using hcenter
    have h1 : (g₀ : ↥G₀) ^ 3 = 1 := Subgroup.mem_bot.mp hbot
    simpa using congrArg Subtype.val h1
  have hg_ne : (g₀ : X) ≠ 1 := by
    intro hg1
    have hx_cent : x ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' := hconj ⟨y, hy⟩
      rw [hg1, one_mul, inv_one, mul_one] at hy'
      have h2 := congrArg (fun z : X => z * x) hy'
      have : x * y = y * x := by simpa [mul_assoc] using h2
      exact this.symm
    have hx_inf : x ∈ B ⊓ Subgroup.centralizer (G₀ : Set X) :=
      Subgroup.mem_inf.mpr ⟨h.d_le h.x_mem, hx_cent⟩
    rw [h.b_faithful, Subgroup.mem_bot] at hx_inf
    exact h.x_ne hx_inf
  have horder : orderOf (g₀ : X) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact orderOf_eq_prime hg3 hg_ne
  have hLcent : L ≤ Subgroup.centralizer ({(g₀ : X)} : Set X) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hl_inf := h.l_comp.1 hl
    have hlG : l ∈ G₀ := (Subgroup.mem_inf.mp hl_inf).1
    have hlx : l * x = x * l :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hl_inf).2
    have hxl : x * l * x⁻¹ = l := by
      rw [hlx.symm]
      group
    have hgcl : (g₀ : X) * l * (g₀ : X)⁻¹ = l := by
      rw [← hconj ⟨l, hlG⟩, hxl]
    have h2 := congrArg (fun z : X => z * (g₀ : X)) hgcl
    have : (g₀ : X) * l = l * (g₀ : X) := by simpa [mul_assoc] using h2
    exact this.symm
  exact ⟨(g₀ : X), g₀.2, horder, (fun y hy => hconj ⟨y, hy⟩), hLcent⟩

end InnerO

end CFSG.StandardType.TableCRes

end
