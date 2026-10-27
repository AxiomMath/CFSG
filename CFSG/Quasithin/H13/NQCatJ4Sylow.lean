module

public import CFSG.Quasithin.H13.NQCatJ4Q
public import CFSG.Sporadic.J4.QTOutAuto
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open scoped commutatorElement Pointwise Matrix

namespace ElevenData

variable {G : Type*} [Group G] {x y : G} (D : ElevenData x y)
include D

theorem map {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f) :
    ElevenData (f x) (f y) where
  hx := by rw [← map_pow, D.hx, map_one]
  hy := by rw [← map_pow, D.hy, map_one]
  hzx := by rw [← map_commutatorElement]; exact D.hzx.map f
  hzy := by rw [← map_commutatorElement]; exact D.hzy.map f
  hxy i hi j hj := by rw [← map_pow, ← map_pow, ← map_mul, ← map_pow, D.hxy i hi j hj, map_one]
  hz := by
    rw [← map_commutatorElement]
    exact fun h => D.hz (hf (h.trans (map_one f).symm))

theorem zpowers_le_of_card [Finite G] {A : Subgroup G} (hA : A ≤ closure ({x, y} : Set G))
    (hcard : Nat.card A = 11 ^ 2) : zpowers ⁅x, y⁆ ≤ A := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  by_contra hzA
  have hAz : A ⊓ zpowers ⁅x, y⁆ = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ zpowers ⁅x, y⁆) ∣ 11 := by
      rw [← D.orderOf_z, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h1 | h11
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hzA
      have he : A ⊓ zpowers ⁅x, y⁆ = zpowers ⁅x, y⁆ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (by rw [h11, Nat.card_zpowers, D.orderOf_z])
      rw [← he]
      exact inf_le_left
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  have hzc : ∀ c ∈ zpowers ⁅x, y⁆, ∀ q ∈ closure ({x, y} : Set G), c * q = q * c := by
    intro c hc q hq
    rw [← D.center_eq] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact congrArg Subtype.val (mem_center_iff.1 hc' ⟨q, hq⟩).symm
  have hzQ : zpowers ⁅x, y⁆ ≤ closure ({x, y} : Set G) := zpowers_le.2 z_mem
  let f : A × zpowers ⁅x, y⁆ → closure ({x, y} : Set G) := fun t =>
    ⟨t.1 * t.2, mul_mem (hA t.1.2) (hzQ t.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    have h1 : (a : G) * c = a' * c' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = c' * (c : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * c) * (c : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * c') * (c : G)⁻¹ := by rw [h1]
        _ = c' * (c : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ A ⊓ zpowers ⁅x, y⁆ :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2,
        h2 ▸ (zpowers ⁅x, y⁆).mul_mem c'.2 ((zpowers ⁅x, y⁆).inv_mem c.2)⟩
    rw [hAz, mem_bot] at h3
    have ha : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    have hc : (c : G) = c' := by
      have := h1
      rw [ha] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hc)
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [D.card_closure, Nat.card_prod, hcard, Nat.card_zpowers, D.orderOf_z]
    norm_num)
  apply D.not_isMulCommutative
  refine ⟨⟨fun q₁ q₂ => ?_⟩⟩
  obtain ⟨⟨a₁, c₁⟩, h₁⟩ := hbij.2 q₁
  obtain ⟨⟨a₂, c₂⟩, h₂⟩ := hbij.2 q₂
  rw [← h₁, ← h₂]
  apply Subtype.ext
  change (a₁ : G) * c₁ * (a₂ * c₂) = a₂ * c₂ * (a₁ * c₁)
  have e1 : (c₁ : G) * (a₂ * c₂) = a₂ * c₂ * c₁ :=
    hzc c₁ c₁.2 _ (mul_mem (hA a₂.2) (hzQ c₂.2))
  have e2 : (c₂ : G) * a₁ = a₁ * c₂ := hzc c₂ c₂.2 _ (hA a₁.2)
  have e3 : (a₁ : G) * a₂ = a₂ * a₁ := hAc a₁ a₁.2 a₂ a₂.2
  calc (a₁ : G) * c₁ * (a₂ * c₂) = a₁ * (c₁ * (a₂ * c₂)) := by group
    _ = a₁ * (a₂ * c₂ * c₁) := by rw [e1]
    _ = a₁ * a₂ * c₂ * c₁ := by group
    _ = a₂ * a₁ * c₂ * c₁ := by rw [e3]
    _ = a₂ * (c₂ * a₁) * c₁ := by rw [e2]; group
    _ = a₂ * c₂ * (a₁ * c₁) := by group

end ElevenData

theorem card_J4J : Nat.card Sporadic.J4.J = 86775571046077562880 :=
  Sporadic.J4.card_J Sporadic.J4.j4Facts

theorem index_j4Q :
    j4Q.index = 65195770883604480 := by
  have h := j4Q.card_mul_index
  rw [j4Data.card_closure, card_J4J] at h
  have h' : (11 ^ 3 : ℕ) * 65195770883604480 = 86775571046077562880 := by norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h.trans h'.symm)

@[expose] noncomputable def j4QSylow :
    Sylow 11 Sporadic.J4.J :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  j4Data.isPGroup.toSylow (by rw [index_j4Q]; norm_num)

theorem coe_j4QSylow
    : (j4QSylow : Subgroup Sporadic.J4.J) = j4Q := rfl

theorem exists_conj_of_sylow
    (P : Sylow 11 Sporadic.J4.J) :
    ∃ g : Sporadic.J4.J, (P : Subgroup Sporadic.J4.J) = j4Q.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sporadic.J4.J j4QSylow P
  exact ⟨g, by rw [← hg, CFSG.LieType.Chevalley.coe_smul_sylow_eq_map, coe_j4QSylow]⟩

theorem exists_le_conj
    {R : Subgroup Sporadic.J4.J} (hR : IsPGroup 11 R) :
    ∃ g : Sporadic.J4.J, R ≤ j4Q.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_of_sylow P
  exact ⟨g, hg ▸ hP⟩

theorem j4DataConj
    (g : Sporadic.J4.J) :
    ElevenData (g * j4x * g⁻¹) (g * j4y * g⁻¹) :=
  j4Data.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem closure_conj
    (g : Sporadic.J4.J) :
    Subgroup.closure ({g * j4x * g⁻¹, g * j4y * g⁻¹} : Set Sporadic.J4.J) =
      j4Q.map (MulAut.conj g).toMonoidHom := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem commutator_conj
    (g : Sporadic.J4.J) :
    ⁅g * j4x * g⁻¹, g * j4y * g⁻¹⁆ = g * j4z * g⁻¹ :=
  (map_commutatorElement (MulAut.conj g).toMonoidHom j4x j4y).symm

theorem fixDim_conj (g u : Sporadic.J4.J) : fixDim (g * u * g⁻¹) = fixDim u := by
  have h1 : jmat g * jmat g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : jmat g⁻¹ * jmat g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let e : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin (jmat g)) (Matrix.mulVecLin (jmat g⁻¹))
      (by rw [← Matrix.mulVecLin_mul, h1, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, h2, Matrix.mulVecLin_one])
  have he : ∀ w, (e : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) w = jmat g *ᵥ w :=
    fun _ => rfl
  have hm : jmat (g * u * g⁻¹) - 1 = jmat g * ((jmat u - 1) * jmat g⁻¹) := by
    rw [map_mul, map_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc,
      h1]
  have hk : LinearMap.ker (Matrix.mulVecLin (jmat (g * u * g⁻¹) - 1)) =
      (LinearMap.ker (Matrix.mulVecLin (jmat u - 1))).map
        (e : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hm, ← Matrix.mulVec_mulVec] at hv
      refine ⟨jmat g⁻¹ *ᵥ v, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
        have h3 := congrArg (fun w => jmat g⁻¹ *ᵥ w) hv
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h3
        rwa [← Matrix.mul_assoc, h2, Matrix.one_mul, ← Matrix.mulVec_mulVec] at h3
      · rw [he, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      rw [he, hm, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  rw [fixDim, fixDim, hk, LinearEquiv.finrank_map_eq]

theorem fixDim_of_mem_conj
    (g : Sporadic.J4.J) {u : Sporadic.J4.J}
    (hu : u ∈ j4Q.map (MulAut.conj g).toMonoidHom) (hu1 : u ≠ 1) :
    (u ∈ (zpowers j4z).map (MulAut.conj g).toMonoidHom → fixDim u = 2) ∧
      (u ∉ (zpowers j4z).map (MulAut.conj g).toMonoidHom → fixDim u = 12) := by
  obtain ⟨q, hq, rfl⟩ := hu
  have hq1 : q ≠ 1 := by
    rintro rfl
    exact hu1 (map_one _)
  obtain ⟨h1, h2⟩ := fixDim_of_mem_j4Q hq hq1
  have hcq : (MulAut.conj g).toMonoidHom q = g * q * g⁻¹ := rfl
  rw [hcq, fixDim_conj]
  refine ⟨fun h => h1 ?_, fun h => h2 fun hz => h ⟨q, hz, rfl⟩⟩
  obtain ⟨r, hr, hrq⟩ := h
  have hrq' : r = q := (MulAut.conj g).injective hrq
  exact hrq' ▸ hr

theorem exists_eq_conj
    (α : MulAut Sporadic.J4.J) :
    ∃ k : Sporadic.J4.J, ∀ x, α x = k * x * k⁻¹ := by
  have hF := Sporadic.J4.j4Facts
  have hM := hF.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 Sporadic.J4.J := Sylow.ofCard Sporadic.J4.QT.P0
    (by rw [Sporadic.J4.QT.card_P0 hM hF, Sporadic.J4.QT.card_J_factorization hF])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Sporadic.J4.J (α • S) S
  have hβ : ∀ x ∈ Sporadic.J4.QT.P0, (MulAut.conj c * α) x ∈ Sporadic.J4.QT.P0 := by
    intro x hx
    have h1 : α x ∈ ((α • S : Sylow 2 _) : Subgroup Sporadic.J4.J) := by
      rw [CFSG.LieType.Chevalley.coe_mulAut_smul_sylow]
      exact ⟨x, hx, rfl⟩
    have h2 : c * α x * c⁻¹ ∈ ((c • (α • S) : Sylow 2 _) : Subgroup Sporadic.J4.J) := by
      rw [CFSG.LieType.Chevalley.coe_smul_sylow_eq_map]
      exact ⟨α x, h1, rfl⟩
    rw [hc] at h2
    exact h2
  obtain ⟨k, hk⟩ := Sporadic.J4.QT.aut_of_maps_P0 hF _ hβ
  refine ⟨c⁻¹ * k, fun x => ?_⟩
  have h := hk x
  rw [MulAut.mul_apply, MulAut.conj_apply] at h
  calc α x = c⁻¹ * (c * α x * c⁻¹) * c := by group
    _ = c⁻¹ * (k * x * k⁻¹) * c := by rw [h]
    _ = c⁻¹ * k * x * (c⁻¹ * k)⁻¹ := by group

end CFSG.Quasithin.H13.NQCat
