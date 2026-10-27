module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Cyclic

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem c_sq : (a * a₁ * a₂) * (a * a₁ * a₂) = z := by
  have hzz := g.z_mul_z
  have hza := g.z_comm_a
  have hza₁ := g.z_comm_a₁
  have hza₂ := g.z_comm_a₂
  have ha := g.a_sq
  have ha₁ := g.a₁_sq
  have ha₂ := g.a₂_sq
  have r01 : a * a₁ = z * (a₁ * a) := g.r01
  have r12 : a₁ * a₂ = z * (a₂ * a₁) := g.r12
  have r20 : a₂ * a = z * (a * a₂) := g.r20
  have r10 : a₁ * a = z * (a * a₁) := by
    calc a₁ * a = z * (z * (a₁ * a)) := by rw [← mul_assoc, hzz, one_mul]
      _ = z * (a * a₁) := by rw [← r01]
  calc (a * a₁ * a₂) * (a * a₁ * a₂) = a * a₁ * (a₂ * a) * a₁ * a₂ := by group
    _ = a * a₁ * (z * (a * a₂)) * a₁ * a₂ := by rw [r20]
    _ = a * (a₁ * z) * (a * a₂) * a₁ * a₂ := by group
    _ = a * (z * a₁) * (a * a₂) * a₁ * a₂ := by rw [hza₁]
    _ = (a * z) * a₁ * (a * a₂) * a₁ * a₂ := by group
    _ = (z * a) * a₁ * (a * a₂) * a₁ * a₂ := by rw [hza]
    _ = z * (a * (a₁ * a) * a₂ * a₁ * a₂) := by group
    _ = z * (a * (z * (a * a₁)) * a₂ * a₁ * a₂) := by rw [r10]
    _ = z * ((a * z) * (a * a₁) * a₂ * a₁ * a₂) := by group
    _ = z * ((z * a) * (a * a₁) * a₂ * a₁ * a₂) := by rw [hza]
    _ = (z * z) * ((a * a) * a₁ * a₂ * a₁ * a₂) := by group
    _ = (a₁ * a₂) * a₁ * a₂ := by rw [hzz, ha]; group
    _ = (z * (a₂ * a₁)) * a₁ * a₂ := by rw [r12]
    _ = z * a₂ * (a₁ * a₁) * a₂ := by group
    _ = z := by rw [ha₁]; calc z * a₂ * 1 * a₂ = z * (a₂ * a₂) := by group
                                              _ = z := by rw [ha₂, mul_one]

end Cyclic


theorem conj_z_mul {p z : D} (hp : z * p = p * z) (y : D) :
    p * (z * y) * p⁻¹ = z * (p * y * p⁻¹) := by
  calc p * (z * y) * p⁻¹ = (p * z) * y * p⁻¹ := by group
    _ = (z * p) * y * p⁻¹ := by rw [← hp]
    _ = z * (p * y * p⁻¹) := by group

section QB

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem card_QB_of_card_T (hT : Nat.card ↥(A ⊓ B) = 64) :
    Nat.card ↥(pCoreOf 2 B) = 32 := by
  have := g.hyp.card_T_QB
  omega

theorem comm3_surjective (hT : Nat.card ↥(A ⊓ B) = 64) :
    Function.Surjective (Gen.comm3 g) := by
  have hmul := Subgroup.card_ker_mul_card_range (Gen.comm3 g)
  have hker : Nat.card (Gen.comm3 g).ker = 4 := by
    have hmap : (Gen.comm3 g).ker.map (pCoreOf 2 B).subtype = kerK B V := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (Gen.mem_ker_comm3 g q).mp hq
      · intro hy
        exact ⟨⟨y, hy.1⟩, (Gen.mem_ker_comm3 g ⟨y, hy.1⟩).mpr hy, rfl⟩
    rw [← g.hyp.card_kerK, ← hmap]
    exact (Subgroup.card_map_of_injective (pCoreOf 2 B).subtype_injective).symm
  have hQ := card_QB_of_card_T g hT
  have hrange : Nat.card (Gen.comm3 g).range = 8 := by
    rw [hker, hQ] at hmul
    omega
  have hcod : Nat.card (↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z)) =
      8 := by
    rw [Nat.card_prod, Nat.card_prod, g.hyp.card_zpowers]
  have htop : (Gen.comm3 g).range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hcod])
  exact MonoidHom.range_eq_top.mp htop

theorem exists_q0 (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ q ∈ pCoreOf 2 B, (a * a₁ * a₂) * q * (a * a₁ * a₂)⁻¹ * q⁻¹ = z := by
  obtain ⟨q, hq⟩ := comm3_surjective g hT
    (⟨z, Subgroup.mem_zpowers z⟩, ⟨z, Subgroup.mem_zpowers z⟩, ⟨z, Subgroup.mem_zpowers z⟩)
  have e₀ : a * (q : D) * a⁻¹ * (q : D)⁻¹ = z :=
    congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) (congrArg Prod.fst hq)
  have e₁ : a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹ = z :=
    congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) (congrArg (fun w => w.2.1) hq)
  have e₂ : a₂ * (q : D) * a₂⁻¹ * (q : D)⁻¹ = z :=
    congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) (congrArg (fun w => w.2.2) hq)
  have f₀ : a * (q : D) * a⁻¹ = z * q := by
    calc a * (q : D) * a⁻¹ = (a * (q : D) * a⁻¹ * (q : D)⁻¹) * q := by group
      _ = z * q := by rw [e₀]
  have f₁ : a₁ * (q : D) * a₁⁻¹ = z * q := by
    calc a₁ * (q : D) * a₁⁻¹ = (a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹) * q := by group
      _ = z * q := by rw [e₁]
  have f₂ : a₂ * (q : D) * a₂⁻¹ = z * q := by
    calc a₂ * (q : D) * a₂⁻¹ = (a₂ * (q : D) * a₂⁻¹ * (q : D)⁻¹) * q := by group
      _ = z * q := by rw [e₂]
  refine ⟨q, q.2, ?_⟩
  have key : (a * a₁ * a₂) * (q : D) * (a * a₁ * a₂)⁻¹ = z * q := by
    calc (a * a₁ * a₂) * (q : D) * (a * a₁ * a₂)⁻¹
        = a * (a₁ * (a₂ * (q : D) * a₂⁻¹) * a₁⁻¹) * a⁻¹ := by group
      _ = a * (a₁ * (z * q) * a₁⁻¹) * a⁻¹ := by rw [f₂]
      _ = a * (z * (a₁ * (q : D) * a₁⁻¹)) * a⁻¹ := by rw [conj_z_mul g.z_comm_a₁]
      _ = a * (z * (z * q)) * a⁻¹ := by rw [f₁]
      _ = z * (a * (z * q) * a⁻¹) := by rw [conj_z_mul g.z_comm_a]
      _ = z * (z * (a * (q : D) * a⁻¹)) := by rw [conj_z_mul g.z_comm_a]
      _ = z * (z * (z * q)) := by rw [f₀]
      _ = z * q := by
        calc z * (z * (z * (q : D))) = (z * z) * (z * q) := by group
          _ = z * q := by rw [g.z_mul_z, one_mul]
  calc (a * a₁ * a₂) * (q : D) * (a * a₁ * a₂)⁻¹ * (q : D)⁻¹ = (z * q) * (q : D)⁻¹ := by rw [key]
    _ = z := by group

end QB

end GoldAmL2T

end F6

end CFSG.Quasithin
