module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisSD
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

open CFSG.Quasithin.G11 CFSG.Open

section Rho

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (B : Module.Basis (Fin 6) (ZMod 2) V)

@[expose] noncomputable def rho : GLV V →* M6 where
  toFun g := LinearMap.toMatrix B B (g : V →ₗ[ZMod 2] V)
  map_one' := by simp
  map_mul' g h := by simp [LinearMap.toMatrix_mul]

theorem rho_apply (g : GLV V) : rho B g = LinearMap.toMatrix B B (g : V →ₗ[ZMod 2] V) := rfl

theorem rho_injective : Function.Injective (rho B) := by
  intro g h hgh
  apply LinearEquiv.toLinearMap_injective
  exact (LinearMap.toMatrix B B).injective hgh

@[expose] noncomputable def ofM (A A' : M6) (h : A * A' = 1) (h' : A' * A = 1) : GLV V :=
  Matrix.toLinOfInv B B h h'

theorem rho_ofM (A A' : M6) (h : A * A' = 1) (h' : A' * A = 1) : rho B (ofM B A A' h h') = A := by
  rw [rho_apply]
  have : ((ofM B A A' h h' : GLV V) : V →ₗ[ZMod 2] V) = Matrix.toLin B B A := rfl
  rw [this, LinearMap.toMatrix_toLin]

end Rho

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_forall {P : Subgroup G} {g : G} (h : ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  have hcard : Nat.card (P.map (MulAut.conj g).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => h p hp, fun hp => ?_⟩
  have : g * p * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hp
  obtain ⟨q, hq, hqp⟩ := this
  have : q = p := (MulAut.conj g).injective hqp
  rw [← this]
  exact hq

end Normalizer

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_semidihedral_normalizer {Pb : Subgroup (GLV V)} {x y z : GLV V} (hxP : x ∈ Pb)
    (hyP : y ∈ Pb) (hzP : z ∈ Pb) (hgen : ∀ g ∈ Pb, g ∈ Subgroup.closure ({x, y} : Set (GLV V)))
    (B : Module.Basis (Fin 6) (ZMod 2) V) (hx : rho B x = mX) (hy : rho B y = mY)
    (hz : rho B z = mZ) :
    ∃ S₀ : Subgroup (GLV V), S₀ ≤ Subgroup.normalizer (Pb : Set (GLV V)) ∧ Nat.card S₀ = 16 ∧
      Nonempty (↥S₀ ≃* SemidihedralGroup 4) := by
  haveI : Finite (GLV V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  have hmA7 : mA * mA ^ 7 = 1 := by rw [← pow_succ']; exact mA_pow_eight
  have hmA7' : mA ^ 7 * mA = 1 := by rw [← pow_succ]; exact mA_pow_eight
  set a : GLV V := ofM B mA (mA ^ 7) hmA7 hmA7' with ha_def
  set b : GLV V := ofM B mB mB mB_mul_self mB_mul_self with hb_def
  have ha : rho B a = mA := rho_ofM B _ _ _ _
  have hb : rho B b = mB := rho_ofM B _ _ _ _
  have ha8 : a ^ 8 = 1 :=
    rho_injective B (by rw [map_pow, ha, map_one]; exact mA_pow_eight)
  have ha4 : a ^ 4 ≠ 1 := fun h => mA_pow_four_ne (by
    have := congrArg (rho B) h
    rwa [map_pow, ha, map_one] at this)
  have hb2 : b ^ 2 = 1 :=
    rho_injective B (by rw [map_pow, hb, map_one, sq]; exact mB_mul_self)
  have hbb : b * b = 1 := by rw [← sq]; exact hb2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbaa : b * a = a ^ 3 * b :=
    rho_injective B (by rw [map_mul, map_mul, map_pow, ha, hb]; exact mB_mul_mA)
  have hab : b * a * b⁻¹ = a ^ 3 := by rw [hbaa, mul_inv_cancel_right]
  have hax : a * x * a⁻¹ = x ^ 1 * y ^ 1 * z ^ 1 := by
    have : a * x = (x ^ 1 * y ^ 1 * z ^ 1) * a :=
      rho_injective B (by simp only [map_mul, map_pow, ha, hx, hy, hz]; exact mA_mul_mX)
    rw [this, mul_inv_cancel_right]
  have hay : a * y * a⁻¹ = x ^ 2 * y ^ 1 * z ^ 0 := by
    have : a * y = (x ^ 2 * y ^ 1 * z ^ 0) * a :=
      rho_injective B (by simp only [map_mul, map_pow, ha, hx, hy, hz]; exact mA_mul_mY)
    rw [this, mul_inv_cancel_right]
  have hbx : b * x * b⁻¹ = x ^ 1 * y ^ 0 * z ^ 2 := by
    have : b * x = (x ^ 1 * y ^ 0 * z ^ 2) * b :=
      rho_injective B (by simp only [map_mul, map_pow, hb, hx, hy, hz]; exact mB_mul_mX)
    rw [this, mul_inv_cancel_right]
  have hby : b * y * b⁻¹ = x ^ 0 * y ^ 2 * z ^ 0 := by
    have : b * y = (x ^ 0 * y ^ 2 * z ^ 0) * b :=
      rho_injective B (by simp only [map_mul, map_pow, hb, hx, hy, hz]; exact mB_mul_mY)
    rw [this, mul_inv_cancel_right]
  have hconj : ∀ g : GLV V, g * x * g⁻¹ ∈ Pb → g * y * g⁻¹ ∈ Pb →
      g ∈ Subgroup.normalizer (Pb : Set (GLV V)) := by
    intro g h1 h2
    refine mem_normalizer_of_forall fun p hp => ?_
    have hle : Subgroup.closure ({x, y} : Set (GLV V)) ≤ Pb.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact h1
      · exact h2
    exact hle (hgen p hp)
  have hpow : ∀ (w : GLV V) (n : ℕ), w ∈ Pb → w ^ n ∈ Pb := fun w n hw => Pb.pow_mem hw n
  have haN : a ∈ Subgroup.normalizer (Pb : Set (GLV V)) := by
    refine hconj a ?_ ?_
    · rw [hax]
      exact Pb.mul_mem (Pb.mul_mem (hpow x 1 hxP) (hpow y 1 hyP)) (hpow z 1 hzP)
    · rw [hay]
      exact Pb.mul_mem (Pb.mul_mem (hpow x 2 hxP) (hpow y 1 hyP)) (hpow z 0 hzP)
  have hbN : b ∈ Subgroup.normalizer (Pb : Set (GLV V)) := by
    refine hconj b ?_ ?_
    · rw [hbx]
      exact Pb.mul_mem (Pb.mul_mem (hpow x 1 hxP) (hpow y 0 hyP)) (hpow z 2 hzP)
    · rw [hby]
      exact Pb.mul_mem (Pb.mul_mem (hpow x 0 hxP) (hpow y 2 hyP)) (hpow z 0 hzP)
  obtain ⟨hcard, hiso⟩ := closure_semidihedral_four ha8 ha4 hb2 hab
  refine ⟨Subgroup.closure {a, b}, ?_, hcard, hiso⟩
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact haN
  · exact hbN

end Main

end SmD6Heis

end CFSG.Quasithin.SzN31
