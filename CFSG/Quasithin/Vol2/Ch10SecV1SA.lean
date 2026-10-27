module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]

@[expose] def mat (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)) (l : ↥L) :
    Matrix (Fin 3) (Fin 3) K :=
  (((φ (QuotientGroup.mk l)).1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

variable (φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K))

theorem mat_mul (l₁ l₂ : ↥L) : mat φ (l₁ * l₂) = mat φ l₁ * mat φ l₂ := by
  simp only [mat, QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, Units.val_mul]

theorem mem_pCore_of_mat {l : ↥L} (h : mat φ l = 1) : l ∈ CFSG.pCore 2 ↥L := by
  have h1 : φ (QuotientGroup.mk l) = 1 := Subtype.ext (Units.ext h)
  exact (QuotientGroup.eq_one_iff l).mp (φ.injective (by rw [h1, map_one]))

theorem eq_one_of_mulVec {M : Matrix (Fin 3) (Fin 3) K} (h : ∀ x, M *ᵥ x = x) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  have h2 : M i j = (Pi.single j 1 : Fin 3 → K) i := this
  rw [h2, Matrix.one_apply, Pi.single_apply]

theorem exists_mat (g : ↥(StatedSL 3 K)) : ∃ l : ↥L, mat φ l = ((g : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨q, hq⟩ := φ.surjective g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, by rw [mat, hq]⟩

structure NatCoord (I : Subgroup H) where
  θ : ↥I ≃* Multiplicative (Fin 3 → K)
  act : ∀ (l : ↥L) (v : ↥I), ∃ v' : ↥I, (v' : H) = (l : H) * (v : H) * (l : H)⁻¹ ∧
    θ v' = Multiplicative.ofAdd (mat φ l *ᵥ Multiplicative.toAdd (θ v))

namespace NatCoord

variable {φ} {I : Subgroup H}

@[expose] noncomputable def cact (c : NatCoord φ I) (g : H)
    (hg : g ∈ Subgroup.normalizer (I : Set H))
    (x : Fin 3 → K) : Fin 3 → K :=
  Multiplicative.toAdd (c.θ ⟨g * (c.θ.symm (Multiplicative.ofAdd x) : H) * g⁻¹,
    (Subgroup.mem_normalizer_iff.mp hg _).mp (c.θ.symm _).2⟩)

theorem cact_add (c : NatCoord φ I)
    (g : H) (hg : g ∈ Subgroup.normalizer (I : Set H)) (x y : Fin 3 → K) :
    c.cact g hg (x + y) = c.cact g hg x + c.cact g hg y := by
  simp only [cact]
  rw [← toAdd_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [ofAdd_add, map_mul, Subgroup.coe_mul]
  group

theorem cact_mul (c : NatCoord φ I) (g₁ g₂ : H) (h₁ : g₁ ∈ Subgroup.normalizer (I : Set H))
    (h₂ : g₂ ∈ Subgroup.normalizer (I : Set H)) (x : Fin 3 → K) :
    c.cact (g₁ * g₂) (Subgroup.mul_mem _ h₁ h₂) x = c.cact g₁ h₁ (c.cact g₂ h₂ x) := by
  simp only [cact, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  congr 2
  apply Subtype.ext
  simp only [mul_inv_rev]
  group

theorem cact_one (c : NatCoord φ I)
    (hg : (1 : H) ∈ Subgroup.normalizer (I : Set H)) (x : Fin 3 → K) :
    c.cact 1 hg x = x := by
  simp only [cact, one_mul, inv_one, mul_one, Subtype.coe_eta, MulEquiv.apply_symm_apply,
    toAdd_ofAdd]

theorem cact_congr (c : NatCoord φ I) {g g' : H} (e : g = g')
    (hg : g ∈ Subgroup.normalizer (I : Set H)) (hg' : g' ∈ Subgroup.normalizer (I : Set H))
    (x : Fin 3 → K) : c.cact g hg x = c.cact g' hg' x := by
  subst e
  rfl

theorem cact_inv_cact (c : NatCoord φ I)
    (g : H) (hg : g ∈ Subgroup.normalizer (I : Set H)) (x : Fin 3 → K) :
    c.cact g⁻¹ (Subgroup.inv_mem _ hg) (c.cact g hg x) = x := by
  rw [← cact_mul, c.cact_congr (inv_mul_cancel g) _ (Subgroup.one_mem _), cact_one]

theorem cact_cact_inv (c : NatCoord φ I)
    (g : H) (hg : g ∈ Subgroup.normalizer (I : Set H)) (x : Fin 3 → K) :
    c.cact g hg (c.cact g⁻¹ (Subgroup.inv_mem _ hg) x) = x := by
  rw [← cact_mul, c.cact_congr (mul_inv_cancel g) _ (Subgroup.one_mem _), cact_one]

theorem le_normalizer (c : NatCoord φ I) : L ≤ Subgroup.normalizer (I : Set H) := by
  have key : ∀ l ∈ L, ∀ v ∈ I, l * v * l⁻¹ ∈ I := fun l hl v hv => by
    obtain ⟨v', hv', -⟩ := c.act ⟨l, hl⟩ ⟨v, hv⟩
    exact hv' ▸ v'.2
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key l hl v, fun h => ?_⟩
  have := key l⁻¹ (L.inv_mem hl) _ h
  rwa [inv_inv, show l⁻¹ * (l * v * l⁻¹) * l = v by group] at this

theorem cact_of_mem (c : NatCoord φ I) (l : ↥L) (x : Fin 3 → K) :
    c.cact l (c.le_normalizer l.2) x = mat φ l *ᵥ x := by
  obtain ⟨v', hv', hθ⟩ := c.act l (c.θ.symm (Multiplicative.ofAdd x))
  have e : v' = ⟨l * (c.θ.symm (Multiplicative.ofAdd x) : H) * (l : H)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (c.le_normalizer l.2) _).mp (c.θ.symm _).2⟩ :=
    Subtype.ext hv'
  rw [e, MulEquiv.apply_symm_apply, toAdd_ofAdd] at hθ
  simp only [cact]
  rw [hθ, toAdd_ofAdd]

theorem mem_pCore_of_cact (c : NatCoord φ I)
    (l : ↥L) (h : ∀ x, c.cact l (c.le_normalizer l.2) x = x) :
    l ∈ CFSG.pCore 2 ↥L :=
  mem_pCore_of_mat φ (eq_one_of_mulVec fun x => by rw [← c.cact_of_mem, h])

end NatCoord

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
