module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Rad
import CFSG.RankThree.PartTwo.Sec9.Item95

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG CFSG.RankThree CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def U4PlusAt {X : Type} [Group X] (E : Subgroup X) (x : X) (q : ℕ) : Prop :=
  x ∈ E ∧ x ≠ 1 ∧
    x ∈ inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X)) ∧
    Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X))) q ∧
    (∀ y ∈ E, inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X)) ≤
      Subgroup.centralizer ({y} : Set X) → y ∈ Subgroup.zpowers x) ∧
    ∃ y ∈ E, ∃ U : Subgroup X,
      U ≤ inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X)) ∧ IsPGroup 2 U ∧
      y ∈ Subgroup.normalizer (U : Set X) ∧ ¬ U ≤ Subgroup.centralizer ({y} : Set X)

namespace Item2130Res4Proof

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem u4PlusAt_of_mulEquiv [Finite X] [Finite Y] (e : X ≃* Y) {E : Subgroup X} {x : X}
    {q : ℕ} (h : U4PlusAt (E.map e.toMonoidHom) (e x) q) : U4PlusAt E x q := by
  obtain ⟨hxE, hx1, h1, h2, hα, y', hy'E, U', hU'R, hU'2, hy'N, hy'C⟩ := h
  have hC : ∀ z : X, (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set Y) := by
    intro z
    ext w
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hw
      have := congrArg e hw
      simpa using this
    · intro hw
      apply e.injective
      simpa using hw
  have hR : (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X))).map
      e.toMonoidHom = inSubgroup perfectResidual (Subgroup.centralizer ({e x} : Set Y)) := by
    rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ e.injective, hC]
  obtain ⟨hR1, hR2⟩ := Item2130Res4Proof.perfectResidual_centralizer_of_mulEquiv e x h1 h2
  have hmemE : ∀ z, e z ∈ E.map e.toMonoidHom → z ∈ E := by
    rintro z ⟨w, hw, hwz⟩
    rwa [show w = z from e.injective hwz] at hw
  refine ⟨hmemE x hxE, fun h1' => hx1 (by rw [h1', map_one]), hR1, hR2, fun y hy hle => ?_, ?_⟩
  · have hle' : inSubgroup perfectResidual (Subgroup.centralizer ({e x} : Set Y)) ≤
        Subgroup.centralizer ({e y} : Set Y) := by
      rw [← hR, ← hC]
      exact Subgroup.map_mono hle
    have hz := hα (e y) ⟨y, hy, rfl⟩ hle'
    have hzp : (Subgroup.zpowers x).map e.toMonoidHom = Subgroup.zpowers (e x) :=
      MonoidHom.map_zpowers e.toMonoidHom x
    rw [← hzp] at hz
    obtain ⟨z, hz, hzy⟩ := hz
    rwa [show z = y from e.injective hzy] at hz
  · obtain ⟨y, hyE, rfl⟩ := hy'E
    refine ⟨y, hyE, U'.comap e.toMonoidHom, ?_, hU'2.comap_of_injective _ e.injective, ?_, ?_⟩
    · intro u hu
      have hu' : e u ∈ (inSubgroup perfectResidual
          (Subgroup.centralizer ({x} : Set X))).map e.toMonoidHom := hR ▸ hU'R hu
      obtain ⟨w, hw, hwu⟩ := hu'
      rwa [show w = u from e.injective hwu] at hw
    · rw [Subgroup.mem_normalizer_iff] at hy'N ⊢
      intro u
      rw [Subgroup.mem_comap, Subgroup.mem_comap]
      have := hy'N (e u)
      simpa using this
    · intro hle
      apply hy'C
      intro w hw
      have hu : e.symm w ∈ U'.comap e.toMonoidHom := by
        rw [Subgroup.mem_comap]
        simpa using hw
      have := Subgroup.mem_centralizer_singleton_iff.mp (hle hu)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg e this
      simpa using this

theorem u4PlusAt_of_subtype {G : Type} [Group G] [Finite G] (S : Subgroup G) {E : Subgroup S}
    {x : S} {q : ℕ} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (h1 : (x : G) ∈ inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G)))
    (h2 : Sec4.IsSLThreePiAt
      (inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G))) q)
    (hα : ∀ y ∈ E, inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G)) ≤
      Subgroup.centralizer ({(y : G)} : Set G) → y ∈ Subgroup.zpowers x)
    (hβ : ∃ y ∈ E, ∃ U : Subgroup G,
      U ≤ inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G)) ∧
      IsPGroup 2 U ∧ (y : G) ∈ Subgroup.normalizer (U : Set G) ∧
      ¬ U ≤ Subgroup.centralizer ({(y : G)} : Set G)) : U4PlusAt E x q := by
  have hR : (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set S))).map S.subtype =
      inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
    rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      S.subtype_injective, GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]
  obtain ⟨hR1, hR2⟩ := Item2130Res4Proof.perfectResidual_centralizer_of_subtype S x h1 h2
  refine ⟨hxE, hx1, hR1, hR2, fun y hy hle => hα y hy ?_, ?_⟩
  · rw [← hR]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hle hz))
  · obtain ⟨y, hyE, U, hUR, hU2, hyN, hyC⟩ := hβ
    have hUS : U ≤ S := hUR.trans ((Subgroup.map_subtype_le _).trans inf_le_left)
    refine ⟨y, hyE, U.comap S.subtype, ?_, hU2.comap_subtype, ?_, ?_⟩
    · intro u hu
      have hu' : (u : G) ∈ (inSubgroup perfectResidual
          (Subgroup.centralizer ({x} : Set S))).map S.subtype := hR ▸ hUR hu
      obtain ⟨w, hw, hwu⟩ := hu'
      rwa [show w = u from S.subtype_injective hwu] at hw
    · rw [Subgroup.mem_normalizer_iff] at hyN ⊢
      intro u
      rw [Subgroup.mem_comap, Subgroup.mem_comap]
      simpa using hyN u
    · intro hle
      apply hyC
      intro w hw
      have hu : (⟨w, hUS hw⟩ : S) ∈ U.comap S.subtype := hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hle hu))

end Transport

section Conj

variable {G : Type} [Group G]

theorem map_conj_le_centralizer_iff (P y : G) (H : Subgroup G) :
    H.map (MulAut.conj P).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G) ↔
      H ≤ Subgroup.centralizer ({P⁻¹ * y * P} : Set G) := by
  have e : Subgroup.centralizer ({y} : Set G) =
      (Subgroup.centralizer ({P⁻¹ * y * P} : Set G)).map (MulAut.conj P).toMonoidHom := by
    rw [map_conj_centralizer_singleton]
    congr 2
    group
  rw [e]
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj P).injective)

theorem mem_normalizer_map_conj_iff (P y : G) (H : Subgroup G) :
    y ∈ Subgroup.normalizer ((H.map (MulAut.conj P).toMonoidHom : Subgroup G) : Set G) ↔
      P⁻¹ * y * P ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hy h
    have := hy (P * h * P⁻¹)
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at this
    rw [show P⁻¹ * (P * h * P⁻¹) * P = h by group,
      show P⁻¹ * (y * (P * h * P⁻¹) * y⁻¹) * P = P⁻¹ * y * P * h * (P⁻¹ * y * P)⁻¹ by group]
      at this
    exact this
  · intro hy h
    have := hy (P⁻¹ * h * P)
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [show P⁻¹ * y * P * (P⁻¹ * h * P) * (P⁻¹ * y * P)⁻¹ = P⁻¹ * (y * h * y⁻¹) * P by group]
      at this
    exact this

end Conj

section Model

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K)

theorem exists_u4PlusAt_uS (hf : Odd f) (hf1 : 1 < f) (E : Subgroup (uS h 4))
    (hE : Late.IsE27 E) : ∃ x, U4PlusAt E x (2 ^ f) := by
  classical
  obtain ⟨ω, v, x, y₀, hxE, hy₀E, hω3, hω1, hωbar, hv, hxv, hy₀v, hdiagE⟩ :=
    exists_orthonormal_eigen_plus h hf E hE
  have hv0 : v 0 ≠ 0 := by
    intro h0
    have := hv 0 0
    rw [h0, (uF h 4).β_zero_left, ite_eq_left rfl] at this
    exact zero_ne_one this
  have hx1 : x ≠ 1 := by
    rintro rfl
    have e := hxv 0
    rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec, ite_eq_right (by decide)] at e
    apply hω1
    have e' : (ω - 1) • v 0 = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.mp e' with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hv0
  set P := frameGL h hv with hPdef
  have hPU : P ∈ uU h 4 := frameGL_mem_uU h hv
  have hPmat : (P : Matrix (Fin 4) (Fin 4) K) = frameMat v := rfl
  have hPinv : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * frameMat v = 1 := P.inv_val
  have hconj_diag : ∀ (Z : GL (Fin 4) K) (μ : Fin 4 → K),
      (∀ i, (Z : Matrix (Fin 4) (Fin 4) K) *ᵥ v i = μ i • v i) →
      ((P⁻¹ * Z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal μ := by
    intro Z μ hZ
    have hZP : (Z : Matrix (Fin 4) (Fin 4) K) * frameMat v = frameMat v * diagonal μ := by
      ext r i
      rw [mul_diagonal, Matrix.mul_apply]
      have e := congrFun (hZ i) r
      rw [Pi.smul_apply, smul_eq_mul] at e
      simp only [frameMat, Matrix.of_apply]
      rw [mul_comm]
      exact e
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hPmat, hZP, ← Matrix.mul_assoc, hPinv,
      Matrix.one_mul]
  set X : GL (Fin 4) K := (x : GL (Fin 4) K) with hX
  set D : GL (Fin 4) K := P⁻¹ * X * P with hDdef
  have hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, ω, ω, 1] := by
    refine hconj_diag X ![ω, ω, ω, 1] fun i => ?_
    rw [hxv i]
    congr 1
    fin_cases i <;> rfl
  have hXD : X = P * D * P⁻¹ := by rw [hDdef]; group
  have hmapC : (uS h 4 ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 4) K))).map
      (MulAut.conj P).toMonoidHom = uS h 4 ⊓ Subgroup.centralizer ({X} : Set (GL (Fin 4) K)) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj P).injective, map_conj_uS h hPU,
      map_conj_centralizer_singleton, ← hXD]
  have hR : inSubgroup perfectResidual
      (uS h 4 ⊓ Subgroup.centralizer ({X} : Set (GL (Fin 4) K))) =
      (blk3SU h).map (MulAut.conj P).toMonoidHom := by
    rw [← hmapC, ← GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      (MulAut.conj P).injective, perfectResidual_blk3SU h hf1 hω1 hD]
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  have hωbar' : h.bar ω * ω = 1 := by rw [hωbar, inv_mul_cancel₀ hω0]
  have hDmem : D ∈ blk3SU h := mem_blk3SU_diagonal h hω3 hωbar' hD
  refine ⟨x, u4PlusAt_of_subtype (uS h 4) hxE hx1 ?_ ?_ ?_ ?_⟩
  · rw [hR, show (x : GL (Fin 4) K) = P * D * P⁻¹ from hXD]
    exact ⟨D, hDmem, rfl⟩
  · rw [hR]
    exact Sec9.isSLThreePiAt_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj P).injective) (isSLThreePiAt_blk3SU h hf)
  ·
    intro y hy hle
    obtain ⟨μ, hμ, hμx⟩ := hdiagE y hy
    rw [hR, map_conj_le_centralizer_iff] at hle
    obtain ⟨h01, h12⟩ := eq_of_le_centralizer_blk3SU h (hconj_diag _ μ hμ) hle
    exact hμx h01 h12
  ·
    obtain ⟨U, hUle, hU2, hUN, hUC⟩ := exists_two_subgroup_blk3SU h hf1 hω3 hω1 hωbar
      (Y₀ := P⁻¹ * (y₀ : GL (Fin 4) K) * P) (hconj_diag _ _ hy₀v)
    refine ⟨y₀, hy₀E, U.map (MulAut.conj P).toMonoidHom, ?_, hU2.map _, ?_, ?_⟩
    · rw [hR]
      exact Subgroup.map_mono hUle
    · rw [mem_normalizer_map_conj_iff]
      exact hUN
    · rw [map_conj_le_centralizer_iff]
      exact hUC

end Model

end Item2130Res4Proof

open Item2130Res4Proof

theorem ku4OrderThreeSU3Plus_holds :
    ∀ n : ℕ, 1 < n → Odd n → ∀ E : Subgroup (projSU 4 2 n), Late.IsE27 E →
      ∃ x, U4PlusAt E x (2 ^ n) := by
  intro n hn hno E hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, by omega, by rw [GaloisField.card 2 (2 * n) (by omega)]⟩
  have : CharP (GaloisField 2 (2 * n)) 2 := h.charP
  obtain ⟨e⟩ := nonempty_projSU_mulEquiv_uS n (by omega) h
  have : Finite (projSU 4 2 n) := Finite.of_equiv _ e.symm.toEquiv
  have hE' : Late.IsE27 (E.map e.toMonoidHom) := hE.map e
  obtain ⟨x', hx'⟩ := exists_u4PlusAt_uS h hno hn _ hE'
  obtain ⟨x, -, rfl⟩ := hx'.1
  exact ⟨x, u4PlusAt_of_mulEquiv e hx'⟩

end CFSG.RankThree.PartTwo.Sec21
