module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofAct
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofLinAlg

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG CFSG.RankThree.PartTwo
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {D : Subgroup G}

structure DData (p : ℕ) (D : Subgroup G) : Prop where
  pgroup : IsPGroup p D
  five_le : 5 ≤ p
  exp : ∀ x : D, x ^ p = 1
  cls : commutator D ≤ Subgroup.center D
  odd : Odd (Nat.card (Subgroup.centralizer (D : Set G)))
  rank : ∀ t : G, orderOf t = 2 →
    CFSG.pRank p (D ⊓ Subgroup.centralizer {t} : Subgroup G) ≤ 2

namespace DData

variable (hD : DData p D)
include hD

omit [Finite G] [Fact p.Prime] in
theorem ne_two : p ≠ 2 := by have := hD.five_le; omega

theorem isElementaryAbelian : IsElementaryAbelian p (D ⧸ frattini D) :=
  (CFSG.GroupTheory.frattini_elementary_quotient hD.pgroup).2.2.2.1

omit [Finite G] in
theorem two_ne_zero' : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod Fact.out hD.ne_two

theorem finrank_fixed [IsElementaryAbelian p (D ⧸ frattini D)] {t : G}
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (ht2 : orderOf t = 2) :
    Module.finrank (ZMod p) (Module.End.eigenspace (frattiniLinN p D ⟨t, ht⟩) 1) ≤ 2 :=
  finrank_fixed_le_two' D hD.pgroup hD.ne_two hD.exp hD.cls
    (by rw [← Subgroup.orderOf_coe]; exact ht2) (hD.rank t ht2)

theorem map_eq_one_of_frattiniLinN_eq_one [IsElementaryAbelian p (D ⧸ frattini D)]
    {Y : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (D : Set G)) {T : Type*} [Group T]
    [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ) (y : Y)
    (hy : frattiniLinN p D (Subgroup.inclusion hYN y) = 1) : ψ y = 1 := by
  set ρY := (frattiniLinN p D).comp (Subgroup.inclusion hYN) with hρY
  set N := ρY.toHomUnits.ker with hN
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hmemN : ∀ x : Y, x ∈ N ↔ frattiniLinN p D (Subgroup.inclusion hYN x) = 1 := by
    intro x
    rw [hN, MonoidHom.mem_ker, ← Units.val_inj]
    rfl
  have hodd : Odd (Nat.card N) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have hx2 : orderOf (Subgroup.inclusion hYN (x : Y)) = 2 := by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_inclusion, Subgroup.orderOf_coe,
        Subgroup.orderOf_coe]
      exact hx
    exact false_of_frattiniLinN_eq_one D hD.pgroup hD.ne_two hD.odd hx2
      ((hmemN x).mp x.2)
  have hbot := hT.map_eq_bot_of_odd ψ hψ hNn hodd
  have : ψ y ∈ N.map ψ := ⟨y, (hmemN y).mpr hy, rfl⟩
  rwa [hbot, Subgroup.mem_bot] at this

end DData

omit [Finite G] in
theorem frattiniLinN_mul_comm [IsElementaryAbelian p (D ⧸ frattini D)]
    {n n' : Subgroup.normalizer (D : Set G)} (h : (n : G) * n' = n' * n) :
    frattiniLinN p D n * frattiniLinN p D n' = frattiniLinN p D n' * frattiniLinN p D n := by
  rw [← map_mul, ← map_mul, show n * n' = n' * n from Subtype.ext h]

theorem mul_self_eq_one_of_orderOf {M : Type*} [Monoid M] {x : M} (h : orderOf x = 2) :
    x * x = 1 := by
  rw [← sq, ← h, pow_orderOf_eq_one]

omit [Finite G] in
theorem orderOf_mul_eq_two {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hne : x ≠ y)
    (hc : x * y = y * x) : orderOf (x * y) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, mul_assoc, ← mul_assoc y x y, ← hc, mul_assoc, mul_self_eq_one_of_orderOf hy,
      mul_one, mul_self_eq_one_of_orderOf hx]
  · intro h
    apply hne
    have hy1 := mul_self_eq_one_of_orderOf hy
    calc x = x * (y * y) := by rw [hy1, mul_one]
      _ = (x * y) * y := by rw [mul_assoc]
      _ = y := by rw [h, one_mul]

theorem false_of_four_group (hD : DData p D) {f₁ f₂ : G}
    (h₁N : f₁ ∈ Subgroup.normalizer (D : Set G)) (h₂N : f₂ ∈ Subgroup.normalizer (D : Set G))
    (ho₁ : orderOf f₁ = 2) (ho₂ : orderOf f₂ = 2) (hne : f₁ ≠ f₂) (hc : f₁ * f₂ = f₂ * f₁)
    {Y : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (D : Set G))
    (hY₁ : ∀ y ∈ Y, y * f₁ = f₁ * y) (hY₂ : ∀ y ∈ Y, y * f₂ = f₂ * y) {T : Type*} [Group T]
    [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ) : False := by
  have := hD.isElementaryAbelian
  set ρ := frattiniLinN p D with hρ
  set n₁ : Subgroup.normalizer (D : Set G) := ⟨f₁, h₁N⟩
  set n₂ : Subgroup.normalizer (D : Set G) := ⟨f₂, h₂N⟩
  have h₃N : f₁ * f₂ ∈ Subgroup.normalizer (D : Set G) := mul_mem h₁N h₂N
  have ho₃ := orderOf_mul_eq_two ho₁ ho₂ hne hc
  have hA : ρ n₁ * ρ n₁ = 1 := by
    rw [← map_mul, show n₁ * n₁ = 1 from Subtype.ext (mul_self_eq_one_of_orderOf ho₁), map_one]
  have hB : ρ n₂ * ρ n₂ = 1 := by
    rw [← map_mul, show n₂ * n₂ = 1 from Subtype.ext (mul_self_eq_one_of_orderOf ho₂), map_one]
  have hAB : ρ n₁ * ρ n₂ = ρ n₂ * ρ n₁ := frattiniLinN_mul_comm hc
  have hn₃ : ρ ⟨f₁ * f₂, h₃N⟩ = ρ n₁ * ρ n₂ := by rw [← map_mul]; rfl
  set ρY := ρ.comp (Subgroup.inclusion hYN) with hρY
  have hcomm : ∀ (y : Y) (f : G) (hf : f ∈ Subgroup.normalizer (D : Set G)),
      (y : G) * f = f * y → ∀ w, ρ ⟨f, hf⟩ w = w → ρ ⟨f, hf⟩ (ρY y w) = ρY y w := by
    intro y f hf hyf w hw
    have h1 : ρY y * ρ ⟨f, hf⟩ = ρ ⟨f, hf⟩ * ρY y := frattiniLinN_mul_comm hyf
    rw [← Module.End.mul_apply, ← h1, Module.End.mul_apply, hw]
  have hinv : ∀ (f : G) (hf : f ∈ Subgroup.normalizer (D : Set G)),
      (∀ y ∈ Y, y * f = f * y) → ∀ (y : Y), ∀ w ∈ Module.End.eigenspace (ρ ⟨f, hf⟩) 1,
        ρY y w ∈ Module.End.eigenspace (ρ ⟨f, hf⟩) 1 := by
    intro f hf hYf y w hw
    rw [mem_eigenspace_one_iff'] at hw ⊢
    exact hcomm y f hf (hYf y y.2) w hw
  have hY₃ : ∀ y ∈ Y, y * (f₁ * f₂) = (f₁ * f₂) * y := fun y hy => by
    rw [← mul_assoc, hY₁ y hy, mul_assoc, hY₂ y hy, mul_assoc]
  refine false_of_rep_three hD.five_le ρY (Module.End.eigenspace (ρ n₁) 1)
    (Module.End.eigenspace (ρ n₂) 1) (Module.End.eigenspace (ρ ⟨f₁ * f₂, h₃N⟩) 1)
    (hD.finrank_fixed h₁N ho₁) (hD.finrank_fixed h₂N ho₂) (hD.finrank_fixed h₃N ho₃)
    (hinv f₁ h₁N hY₁) (hinv f₂ h₂N hY₂) (hinv _ h₃N hY₃) hT ψ hψ ?_
  intro y hy₁ hy₂ hy₃
  refine hD.map_eq_one_of_frattiniLinN_eq_one hYN hT ψ hψ y ?_
  refine eq_one_of_fix_three hD.two_ne_zero' hA hB hAB _ (fun v hv => ?_) (fun v hv => ?_)
    (fun v hv => ?_)
  · exact hy₁ v ((mem_eigenspace_one_iff' _ v).mpr hv)
  · exact hy₂ v ((mem_eigenspace_one_iff' _ v).mpr hv)
  · rw [← hn₃] at hv
    exact hy₃ v ((mem_eigenspace_one_iff' _ v).mpr hv)

theorem false_of_quaternion (hD : DData p D) {z i j e : G}
    (hzN : z ∈ Subgroup.normalizer (D : Set G)) (hiN : i ∈ Subgroup.normalizer (D : Set G))
    (hjN : j ∈ Subgroup.normalizer (D : Set G)) (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hz : orderOf z = 2) (hii : i * i = z) (hjj : j * j = z) (hij : i * j = z * (j * i))
    (he : orderOf e = 2) (hez : e * z = z * e) (hne : e ≠ z)
    {Y : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (D : Set G))
    (hYi : ∀ y ∈ Y, y * i = i * y) (hYj : ∀ y ∈ Y, y * j = j * y) {T : Type*} [Group T]
    [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ) : False := by
  have := hD.isElementaryAbelian
  set ρ := frattiniLinN p D with hρ
  set nz : Subgroup.normalizer (D : Set G) := ⟨z, hzN⟩
  set ni : Subgroup.normalizer (D : Set G) := ⟨i, hiN⟩
  set nj : Subgroup.normalizer (D : Set G) := ⟨j, hjN⟩
  set ne : Subgroup.normalizer (D : Set G) := ⟨e, heN⟩
  have hzeN : z * e ∈ Subgroup.normalizer (D : Set G) := mul_mem hzN heN
  have hoze : orderOf (z * e) = 2 :=
    orderOf_mul_eq_two hz he (Ne.symm hne) hez.symm
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have hq : QuatData (ρ nz) (ρ ni) (ρ nj) (ρ ne) a b :=
    { zz := by
        rw [← map_mul, show nz * nz = 1 from Subtype.ext (mul_self_eq_one_of_orderOf hz),
          map_one]
      ii := by rw [← map_mul, show ni * ni = nz from Subtype.ext hii]
      jj := by rw [← map_mul, show nj * nj = nz from Subtype.ext hjj]
      ij := by
        rw [← map_mul, ← map_mul, ← map_mul, show ni * nj = nz * (nj * ni) from Subtype.ext hij]
      ee := by
        rw [← map_mul, show ne * ne = 1 from Subtype.ext (mul_self_eq_one_of_orderOf he),
          map_one]
      ez := frattiniLinN_mul_comm hez
      ab := hab }
  have hZE : ρ nz * ρ ne = ρ ⟨z * e, hzeN⟩ := by rw [← map_mul]; rfl
  set ρY := ρ.comp (Subgroup.inclusion hYN) with hρY
  have hYI : ∀ (y : Y) v, ρY y (ρ ni v) = ρ ni (ρY y v) := fun y v => by
    have h1 : ρY y * ρ ni = ρ ni * ρY y := frattiniLinN_mul_comm (hYi y y.2)
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply]
  have hYJ : ∀ (y : Y) v, ρY y (ρ nj v) = ρ nj (ρY y v) := fun y v => by
    have h1 : ρY y * ρ nj = ρ nj * ρY y := frattiniLinN_mul_comm (hYj y y.2)
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply]
  have hYZ : ∀ (y : Y) v, ρY y (ρ nz v) = ρ nz (ρY y v) := fun y v => by
    rw [← hq.ii' v, hYI, hYI, hq.ii']
  have hYU : ∀ (y : Y) v, ρY y (hq.U v) = hq.U (ρY y v) := fun y v => by
    simp only [hq.U_apply, map_add, map_smul, hYI, hYJ]
  have h₁ : Module.finrank (ZMod p) (Module.End.eigenspace (ρ nz) 1) ≤ 2 :=
    hD.finrank_fixed hzN hz
  have h₂ : Module.finrank (ZMod p) hq.Eplus ≤ 2 := by
    have h1 := hq.two_mul_finrank_le hD.two_ne_zero'
    have h2 : Module.finrank (ZMod p) (Module.End.eigenspace (ρ ne) 1) ≤ 2 :=
      hD.finrank_fixed heN he
    have h3 : Module.finrank (ZMod p) (Module.End.eigenspace (ρ nz * ρ ne) 1) ≤ 2 := by
      rw [hZE]
      exact hD.finrank_fixed hzeN hoze
    omega
  have hW₁ : ∀ (y : Y), ∀ w ∈ Module.End.eigenspace (ρ nz) 1,
      ρY y w ∈ Module.End.eigenspace (ρ nz) 1 := by
    intro y w hw
    rw [mem_eigenspace_one_iff'] at hw ⊢
    rw [← hYZ, hw]
  have hW₂ : ∀ (y : Y), ∀ w ∈ hq.Eplus, ρY y w ∈ hq.Eplus := by
    intro y w hw
    rw [hq.mem_Eplus] at hw ⊢
    refine ⟨?_, ?_⟩
    · rw [← hYZ, hw.1, map_neg]
    · rw [← hYU, hw.2]
  refine false_of_rep_two hD.five_le ρY _ _ h₁ h₂ hW₁ hW₂ hT ψ hψ ?_
  intro y hy₁ hy₂
  refine hD.map_eq_one_of_frattiniLinN_eq_one hYN hT ψ hψ y ?_
  exact hq.eq_one hD.two_ne_zero' (ρY y) (hYI y) (hYJ y)
    (fun v hv => hy₁ v ((mem_eigenspace_one_iff' _ v).mpr hv)) hy₂

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
