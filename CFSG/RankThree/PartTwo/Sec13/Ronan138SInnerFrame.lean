module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SBase
import CFSG.RankThree.PartTwo.Sec13.Ronan138SQE
import CFSG.RankThree.PartTwo.Sec13.Ronan138SRefl
import CFSG.RankThree.PartTwo.Sec13.Ronan138SModel
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldB
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree qSubPi diagUnits diagTau cycThree)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (GeneralLinearGroup ProjGenLinGroup)
open scoped commutatorElement

section Mat

variable {K : Type} [Field K]

theorem cycThree_comm_diagUnits (w : Kˣ) :
    cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹ * (diagUnits w 1 w⁻¹)⁻¹ =
      diagUnits (w⁻¹ * w⁻¹) w w := by
  rw [Sec4.cycThree_conj_diagUnits, Sec4.diagUnits_inv, Sec4.diagUnits_mul]
  congr 1 <;> simp

theorem cycThree_sq_conj_diagUnits (w : Kˣ) :
    cycThree * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹) * cycThree⁻¹ =
      (diagUnits w 1 w⁻¹ * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹))⁻¹ := by
  rw [Sec4.cycThree_conj_diagUnits, Sec4.cycThree_conj_diagUnits, Sec4.diagUnits_mul,
    Sec4.diagUnits_inv]
  congr 1 <;> simp

theorem scalar_eq_diagUnits (l : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) l = diagUnits l l l := by
  apply Units.ext
  rw [Sec4.coe_diagUnits_eq, Sec4.coe_scalar_eq_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mk_diagUnits_pow_three {τ₀ : K} (hτ₀ : τ₀ ^ 3 = 1) (hτ0 : τ₀ ≠ 0) {w : Kˣ}
    (hw : w ^ 3 = Units.mk0 τ₀ hτ0) :
    ProjGenLinGroup.mk (diagUnits w 1 w⁻¹) ^ 3 = (ProjGenLinGroup.mk (diagTau hτ₀))⁻¹ := by
  set τ := Units.mk0 τ₀ hτ0 with hτ
  have hτ3 : τ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hτ, Units.val_mk0, hτ₀,
    Units.val_one])
  have hτinv : τ⁻¹ = τ ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hτ3]
  have heq : diagUnits w 1 w⁻¹ ^ 3 =
      GeneralLinearGroup.scalar (Fin 3) (τ ^ 2) * (diagTau hτ₀)⁻¹ := by
    rw [Sec4.diagUnits_pow, Sec4.diagTau_eq_diagUnits hτ₀ hτ0, ← hτ, Sec4.diagUnits_inv,
      scalar_eq_diagUnits, Sec4.diagUnits_mul, inv_pow, hw, one_pow]
    congr 1
    · rw [hτinv, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hτ3, one_mul]
    · rw [mul_inv_cancel]
    · rw [hτinv, inv_one, mul_one]
  rw [← map_pow, heq, map_mul, Sec13.mk_scalar, one_mul, map_inv]

theorem mk_diagUnits_comm (w : Kˣ) :
    ProjGenLinGroup.mk (diagUnits (w⁻¹ * w⁻¹) w w) =
      ProjGenLinGroup.mk (diagUnits (w ^ 3)⁻¹ 1 1) := by
  have heq : diagUnits (w⁻¹ * w⁻¹) w w =
      GeneralLinearGroup.scalar (Fin 3) w * diagUnits (w ^ 3)⁻¹ 1 1 := by
    rw [scalar_eq_diagUnits, Sec4.diagUnits_mul]
    congr 1
    · rw [pow_succ, pow_two]
      group
    · rw [mul_one]
    · rw [mul_one]
  rw [heq, map_mul, Sec13.mk_scalar, one_mul]

theorem mk_diagUnits_not_mem_zpowers {τ₀ : K} (hτ₀ : τ₀ ^ 3 = 1) (hτ1 : τ₀ ≠ 1) (g : GL (Fin 3) K)
    {a : Kˣ} (ha : a ≠ 1) :
    ProjGenLinGroup.mk (g * diagUnits a 1 1 * g⁻¹) ∉
      Subgroup.zpowers (ProjGenLinGroup.mk (g * diagTau hτ₀ * g⁻¹)) := by
  have hτ0 : τ₀ ≠ 0 := by
    rintro rfl
    simp at hτ₀
  intro hmem
  have h3 : ProjGenLinGroup.mk (g * diagTau hτ₀ * g⁻¹) ^ 3 = 1 := by
    rw [← map_pow, conj_pow, Sec4.diagTau_pow_three, mul_one, mul_inv_cancel, map_one]
  have hcases : ∀ k : ℕ, k < 3 → ProjGenLinGroup.mk (diagUnits a 1 1) ≠
      ProjGenLinGroup.mk (diagTau hτ₀ ^ k) := by
    intro k hk h
    obtain ⟨ν, hν⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
    rw [Sec4.diagTau_eq_diagUnits hτ₀ hτ0, Sec4.diagUnits_pow, scalar_eq_diagUnits,
      Sec4.diagUnits_mul] at hν
    have e0 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) hν
    have e1 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 1 1) hν
    have e2 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 2 2) hν
    simp only [Sec4.coe_diagUnits_eq] at e0 e1 e2
    simp at e0 e1 e2
    rw [e2] at e0 e1
    simp only [Units.val_one, mul_one] at e0 e1
    interval_cases k
    · exact ha (Units.ext (by simpa using e0))
    · have h2 : τ₀ ^ 2 = 1 := by simpa using e1.symm
      apply hτ1
      calc τ₀ = τ₀ * τ₀ ^ 2 := by rw [h2, mul_one]
        _ = τ₀ ^ 3 := by ring
        _ = 1 := hτ₀
    · have h4 : (τ₀ ^ 2) ^ 2 = 1 := e1.symm
      apply hτ1
      calc τ₀ = τ₀ ^ 3 * τ₀ := by rw [hτ₀, one_mul]
        _ = (τ₀ ^ 2) ^ 2 := by ring
        _ = 1 := h4
  rcases eq_of_mem_zpowers_of_pow_three h3 hmem with h | h | h
  · apply hcases 0 (by norm_num)
    have := congrArg (fun X => (ProjGenLinGroup.mk g)⁻¹ * X * ProjGenLinGroup.mk g) h
    simp only [map_mul, map_inv] at this
    simpa [mul_assoc] using this
  · apply hcases 1 (by norm_num)
    have := congrArg (fun X => (ProjGenLinGroup.mk g)⁻¹ * X * ProjGenLinGroup.mk g) h
    simp only [map_mul, map_inv] at this
    simpa [mul_assoc] using this
  · apply hcases 2 (by norm_num)
    have := congrArg (fun X => (ProjGenLinGroup.mk g)⁻¹ * X * ProjGenLinGroup.mk g) h
    simp only [map_mul, map_inv, ← map_pow, conj_pow] at this
    simpa [mul_assoc] using this

theorem mk_diagUnits_one_mem_zpowers {τ₀ : K} (hτ₀ : τ₀ ^ 3 = 1) (hτ1 : τ₀ ≠ 1)
    (g : GL (Fin 3) K) {u : Kˣ} (hu : u ^ 3 = 1) :
    ProjGenLinGroup.mk (g * diagUnits 1 u u⁻¹ * g⁻¹) ∈
      Subgroup.zpowers (ProjGenLinGroup.mk (g * diagTau hτ₀ * g⁻¹)) := by
  have hτ0 : τ₀ ≠ 0 := by
    rintro rfl
    simp at hτ₀
  set τ := Units.mk0 τ₀ hτ0 with hτ
  have hu' : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hmk : ∀ (l : Kˣ) (X : GL (Fin 3) K), ProjGenLinGroup.mk
      (g * (GeneralLinearGroup.scalar (Fin 3) l * X) * g⁻¹) = ProjGenLinGroup.mk (g * X * g⁻¹) := by
    intro l X
    simp only [map_mul, map_inv, Sec13.mk_scalar, one_mul]
  rcases Sec4.eq_one_or_eq_tau_or_eq_tau_sq hτ₀ hτ1 hu' with h | h | h
  · have hu1 : u = 1 := Units.ext (by simpa using h)
    subst hu1
    rw [inv_one, Sec4.diagUnits_one, mul_one, mul_inv_cancel, map_one]
    exact one_mem _
  · have hut : u = τ := Units.ext (by simpa [hτ] using h)
    subst hut
    refine Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩
    have : diagTau hτ₀ = GeneralLinearGroup.scalar (Fin 3) τ * diagUnits 1 τ τ⁻¹ := by
      rw [Sec4.diagTau_eq_diagUnits hτ₀ hτ0, ← hτ, scalar_eq_diagUnits, Sec4.diagUnits_mul]
      congr 1
      · rw [mul_one]
      · rw [pow_two]
      · rw [mul_inv_cancel]
    rw [zpow_one, this, hmk]
  · have hut : u = τ ^ 2 := Units.ext (by simp [hτ, h])
    subst hut
    refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
    have : diagTau hτ₀ ^ 2 = GeneralLinearGroup.scalar (Fin 3) (τ ^ 2) *
        diagUnits 1 (τ ^ 2) (τ ^ 2)⁻¹ := by
      rw [Sec4.diagTau_eq_diagUnits hτ₀ hτ0, ← hτ, Sec4.diagUnits_pow, scalar_eq_diagUnits,
        Sec4.diagUnits_mul]
      congr 1
      · rw [mul_one]
      · rw [← pow_mul, ← pow_add]
      · rw [one_pow, mul_inv_cancel]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← map_pow, conj_pow, this, hmk]

end Mat

section Lift

variable {G : Type} [Group G] [Finite G] {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem fixed_of_diag {L E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (L : Set G))
    {φ : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K)}
    {D : Subgroup (GL (Fin 3) K)} {g : GL (Fin 3) K}
    (hτD : ∀ τ ∈ Sec4.autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    (hdiag : ∀ a ∈ D, ∃ l s t : Kˣ, s ∈ rootsOfUnity 3 K ∧ t ∈ rootsOfUnity 3 K ∧
      g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    {z : L ⧸ aschbacherSolvableCore 3 L} {a b c' : Kˣ}
    (hz : ((φ z : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagUnits a b c' * g⁻¹)) :
    ∀ (x : G) (hx : x ∈ E), Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩) z = z := by
  intro x hx
  obtain ⟨y, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hEN hx, hx, rfl⟩)
  obtain ⟨l, s, t, -, -, hl⟩ := hdiag y hyD
  apply φ.injective
  apply Subtype.ext
  rw [hyz z, hz, ← map_inv, ← map_mul, ← map_mul, conj_diag_comm hl]

theorem conj_mem_sup_of_comm {L E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hE3 : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    {φ : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K)}
    {D : Subgroup (GL (Fin 3) K)} {g : GL (Fin 3) K}
    (hτD : ∀ τ ∈ Sec4.autThetaQuot E L, ∃ y ∈ D, ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
        ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    (hdiag : ∀ a ∈ D, ∃ l s t : Kˣ, s ∈ rootsOfUnity 3 K ∧ t ∈ rootsOfUnity 3 K ∧
      g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    {M : GL (Fin 3) K}
    (hM : ∀ y ∈ D, ∃ a b c' : Kˣ, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c' ^ 3 = 1 ∧
      M * y * M⁻¹ * y⁻¹ = g * diagUnits a b c' * g⁻¹)
    (w : L) (hw : ((φ (w : L ⧸ aschbacherSolvableCore 3 L) : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) :
    ∀ x ∈ E, (w : G) * x * (w : G)⁻¹ ∈ E ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  intro x hx
  set θ := aschbacherSolvableCore 3 L with hθ
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  set σ := L.normalizerMonoidHom ⟨x, hEN hx⟩ with hσ
  set k : L := w * (σ w)⁻¹ with hk
  have hkG : (k : G) = (w : G) * (x * (w : G) * x⁻¹)⁻¹ := rfl
  obtain ⟨y, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hEN hx, hx, rfl⟩)
  obtain ⟨a, b, c', ha, hb, hc, hcomm⟩ := hM y hyD
  have hmk : (k : L ⧸ θ) = (w : L ⧸ θ) * (Sec4.thetaQuotMulAut L σ (w : L ⧸ θ))⁻¹ := by
    rw [hk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← Sec4.thetaQuotMulAut_mk]
  have hek : ((φ (k : L ⧸ θ) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagUnits a b c' * g⁻¹) := by
    rw [hmk, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyz, hw, ← hcomm]
    simp only [map_mul, map_inv]
    group
  have hk3 : (k : L ⧸ θ) ^ 3 = 1 := by
    apply φ.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, hek, ← map_pow, conj_pow,
      diagUnits_pow_three ha hb hc, mul_one, mul_inv_cancel, map_one]
  obtain ⟨n, hnE, hnk⟩ := exists_mem_of_fixed hEN hE3 hEmax hk3
    (fixed_of_diag hEN hτD hdiag hek)
  have hnk' : (n : G)⁻¹ * (k : G) ∈ θG := (mk_eq_mk_iff n k).mp hnk
  have hθx : x⁻¹ * ((n : G)⁻¹ * (k : G)) * x⁻¹⁻¹ ∈ θG :=
    conj_mem_theta_of_normalizer (inv_mem (hEN hx)) hnk'
  have heq : (w : G) * x * (w : G)⁻¹ =
      ((n : G) * x) * (x⁻¹ * ((n : G)⁻¹ * (k : G)) * x⁻¹⁻¹) := by
    rw [hkG]
    group
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem hnE hx)) (Subgroup.mem_sup_right hθx)

theorem mem_centralizer_of_fixed' {L E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hEp : IsPGroup 3 E) {n : L} (hnN : (n : G) ∈ Subgroup.normalizer (E : Set G))
    (hfix : ∀ (x : G) (hx : x ∈ E), Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩)
      (n : L ⧸ aschbacherSolvableCore 3 L) = (n : L ⧸ aschbacherSolvableCore 3 L)) :
    (n : G) ∈ Subgroup.centralizer (E : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have h1 : x * (n : G) * x⁻¹ * (n : G)⁻¹ ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp hnN x⁻¹).mp (inv_mem hx)
    rw [show x * (n : G) * x⁻¹ * (n : G)⁻¹ = x * ((n : G) * x⁻¹ * (n : G)⁻¹) by group]
    exact mul_mem hx this
  have h2 : x * (n : G) * x⁻¹ * (n : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h := hfix x hx
    rw [Sec4.thetaQuotMulAut_mk, mk_eq_mk_iff, Sec4.normalizerMonoidHom_apply_coe] at h
    refine mul_inv_mem_theta_of_inv_mul_mem n.2 ?_
    have := inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have h3 : x * (n : G) * x⁻¹ * (n : G)⁻¹ ∈ E ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨h1, h2⟩
  rw [inf_theta_eq_bot hEp L, Subgroup.mem_bot] at h3
  calc x * (n : G) = x * (n : G) * x⁻¹ * (n : G)⁻¹ * ((n : G) * x) := by group
    _ = (n : G) * x := by rw [h3, one_mul]

theorem eq_of_mk_eq_of_mem {L E : Subgroup G} (hEp : IsPGroup 3 E) {a b : L} (haE : (a : G) ∈ E)
    (hbE : (b : G) ∈ E)
    (hab : (a : L ⧸ aschbacherSolvableCore 3 L) = (b : L ⧸ aschbacherSolvableCore 3 L)) :
    (a : G) = b := by
  have h1 : (a : G)⁻¹ * (b : G) ∈ E ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
    Subgroup.mem_inf.mpr ⟨E.mul_mem (E.inv_mem haE) hbE, (mk_eq_mk_iff a b).mp hab⟩
  rw [inf_theta_eq_bot hEp L, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

end Lift

section Inner

variable {G : Type} [Group G] [Finite G]

structure InnerFrame138 (A L E F : Subgroup G) (c x y t n : G) : Prop where
  base : Frame138Base A L E F c x y t
  hinner : E ≤ Subgroup.zpowers c ⊔ L
  hnL : n ∈ L
  hnC : n ∈ Subgroup.centralizer (E : Set G)
  hn9 : n ^ 9 = 1
  hn3 : n ^ 3 ≠ 1
  hn3d : n ^ 3 ∈ Subgroup.zpowers ⁅x, y⁆
  hnyE : ⁅n, y⁆ ∈ E
  hnyZ : ⁅n, y⁆ ∉ E ⊓ F

theorem exists_innerFrame138 {A : Subgroup G} {c : G} {L E : Subgroup G} (hH : Hyp138 A c L E)
    (hle : E ≤ Subgroup.zpowers c ⊔ L) :
    ∃ (F : Subgroup G) (x y t n : G), InnerFrame138 A L E F c x y t n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, hE27, hEN, hCE, hST, hC⟩ := hH'
  have hEE : E ∈ partTwoE G := by
    rcases hST with hS | hT
    · exact hS.1
    · exact hT.1
  have hEF : E ∈ partTwoF G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ hEE
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hEF.2.1
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3.2 g g.2)⟩
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨π, p, f, K, _, hK, hq, φ, D, hD, hτD, hDτ⟩ := hC
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  haveI : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hLq.1
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
  have hq2 := two_lt_of_mulEquiv hLq hK hq φ
  have hZ := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hCEset := sectionCentralizer_eq_inf hEN
  rw [hCE] at hCEset
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := by
    have : c ∈ ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
      rw [← hCEset]
      exact Subgroup.mem_zpowers c
    exact (Subgroup.mem_inf.mp this).2
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun l hl => hLc l hl))
  obtain ⟨τ₀, hτ₀3, hτ₀1⟩ := Sec4.exists_tau hK hq
  have hτ₀0 : τ₀ ≠ 0 := by
    rintro rfl
    simp at hτ₀3
  set τ := Units.mk0 τ₀ hτ₀0 with hτdef
  have hτ : τ ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτdef, Units.val_mk0, hτ₀3, Units.val_one])
  have hτ1 : τ ≠ 1 := fun h1 => hτ₀1 (by simpa [hτdef] using congrArg Units.val h1)
  obtain ⟨g, hg, hdiag, hsurj⟩ := Sec4.isTypeC_conj_std hK hq hD
  obtain ⟨a, haD, l, hal⟩ := hsurj τ hτ τ hτ
  obtain ⟨σ, hσ, hσa⟩ := hDτ a haD
  obtain ⟨x₀, hxN, hxE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
  have hxa : ActsPGL φ x₀ a := ⟨hxN, hD.1 haD, hσa⟩
  have hx' : x₀ ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hle hxE
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hx'
  obtain ⟨_, ⟨k, rfl⟩, l', hl', rfl⟩ := hx'
  obtain ⟨s, hs, hse⟩ :=
    Subgroup.mem_map.mp (φ ((⟨l', hl'⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)).2
  have hxs : ActsPGL φ (c ^ k * l') (1 * s) :=
    (actsPGL_of_mem_thetaQuotCentralizer (zpow_mem hcC k)).mul (actsPGL_of_mem hπ hl' hs hse.symm)
  obtain ⟨ν, hν⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp (ActsPGL.mk_eq hK hq hxa hxs)
  rw [one_mul] at hν
  obtain ⟨w, hw, hw3⟩ := exists_cube_root_of_inner hK hq hg (hD.1 haD) hs hτ hal hν
  have hU : g * diagUnits w 1 w⁻¹ * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
    have h1 := Sec4.conj_mem_slPi hπ hg (Sec4.torusHom_mem_slPi hK hw (one_mem _))
    have h2 : Sec4.torusHom (w, 1) = diagUnits w 1 w⁻¹ := by
      show diagUnits w 1 (w * 1)⁻¹ = _
      rw [mul_one]
    rwa [h2] at h1
  have hD₁ : g * diagTau hτ₀3 * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (Sec4.diagTau_mem_slPi hπ hq' hτ₀3)
  have hR : g * cycThree * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (Sec4.cycThree_mem_slPi hπ)
  have hW : g * swapTwoThree * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (swapTwoThree_mem_slPi hπ)
  set θ := aschbacherSolvableCore 3 L with hθ
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  set ub : L ⧸ θ := φ.symm (Sec4.projOf _ ⟨_, hU⟩) with hub
  set y₁b : L ⧸ θ := φ.symm (Sec4.projOf _ ⟨_, hD₁⟩) with hy₁b
  set y₂b : L ⧸ θ := φ.symm (Sec4.projOf _ ⟨_, hR⟩) with hy₂b
  set swb : L ⧸ θ := φ.symm (Sec4.projOf _ ⟨_, hW⟩) with hswb
  have heu : ((φ ub : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagUnits w 1 w⁻¹ * g⁻¹) := by
    rw [hub, MulEquiv.apply_symm_apply, Sec4.coe_projOf]
  have he₁ : ((φ y₁b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagTau hτ₀3 * g⁻¹) := by
    rw [hy₁b, MulEquiv.apply_symm_apply, Sec4.coe_projOf]
  have he₂ : ((φ y₂b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * cycThree * g⁻¹) := by
    rw [hy₂b, MulEquiv.apply_symm_apply, Sec4.coe_projOf]
  have hew : ((φ swb : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * swapTwoThree * g⁻¹) := by
    rw [hswb, MulEquiv.apply_symm_apply, Sec4.coe_projOf]
  have hφinj : ∀ z z' : L ⧸ θ, ((φ z : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = (φ z' : ProjGenLinGroup (Fin 3) K) → z = z' :=
    fun z z' hzz => φ.injective (Subtype.ext hzz)
  have hφmul : ∀ z z' : L ⧸ θ, ((φ (z * z') : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = (φ z : ProjGenLinGroup (Fin 3) K) * (φ z' : _) := by
    intro z z'
    rw [map_mul, Subgroup.coe_mul]
  have hφinv : ∀ z : L ⧸ θ, ((φ z⁻¹ : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = (φ z : ProjGenLinGroup (Fin 3) K)⁻¹ := by
    intro z
    rw [map_inv, Subgroup.coe_inv]
  have hφpow : ∀ (z : L ⧸ θ) (m : ℕ), ((φ (z ^ m) : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = (φ z : ProjGenLinGroup (Fin 3) K) ^ m := by
    intro z m
    rw [map_pow, Subgroup.coe_pow]
  have hφone : ((φ (1 : L ⧸ θ) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      1 := by rw [map_one, Subgroup.coe_one]
  have hy₁3 : y₁b ^ 3 = 1 := by
    apply hφinj
    rw [hφpow, hφone, he₁, ← map_pow, conj_pow, Sec4.diagTau_pow_three, mul_one, mul_inv_cancel,
      map_one]
  have hy₂3 : y₂b ^ 3 = 1 := by
    apply hφinj
    rw [hφpow, hφone, he₂, ← map_pow, conj_pow, Sec4.cycThree_pow_three, mul_one, mul_inv_cancel,
      map_one]
  have hy₁1 : y₁b ≠ 1 := by
    intro h1
    apply mk_diagTau_ne_one hτ₀3 hτ₀1
    have h2 := congrArg (fun z => ((φ z : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K)) h1
    simp only [hφone, he₁, map_mul, map_inv] at h2
    calc ProjGenLinGroup.mk (diagTau hτ₀3) = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ₀3) * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h2]; group
  have hord₁ : orderOf y₁b = 3 := orderOf_eq_prime hy₁3 hy₁1
  have hy12 : y₁b * y₂b = y₂b * y₁b := by
    apply hφinj
    rw [hφmul, hφmul, he₁, he₂]
    simp only [map_mul, map_inv]
    have hc := Sec4.mk_diagTau_cycThree hτ₀3
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ₀3) * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (diagTau hτ₀3) * ProjGenLinGroup.mk cycThree) *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk cycThree *
          ProjGenLinGroup.mk (diagTau hτ₀3)) * (ProjGenLinGroup.mk g)⁻¹ := by rw [hc]
      _ = _ := by group
  have hy₂₁ : y₂b ∉ Subgroup.zpowers y₁b := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ((φ y₂b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((φ y₁b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ^ m := by
      rw [← hm, map_zpow, Subgroup.coe_zpow]
    rw [he₁, he₂, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, conj_zpow] at h1
    apply mk_cycThree_not_mem_zpowers hτ₀3
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    calc ProjGenLinGroup.mk (diagTau hτ₀3) ^ m = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ₀3) ^ m *
            (ProjGenLinGroup.mk g)⁻¹) * ProjGenLinGroup.mk g := by group
      _ = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by rw [h1]
      _ = ProjGenLinGroup.mk cycThree := by group
  have hu3 : ub ^ 3 = y₁b⁻¹ := by
    apply hφinj
    rw [hφpow, hφinv, heu, he₁]
    simp only [map_mul, map_inv]
    rw [conj_pow, mk_diagUnits_pow_three hτ₀3 hτ₀0 hw3]
    group
  have hu9 : ub ^ 9 = 1 := by
    rw [show 9 = 3 * 3 from rfl, pow_mul, hu3, inv_pow, hy₁3, inv_one]
  have hu3ne : ub ^ 3 ≠ 1 := by
    rw [hu3]
    exact fun h1 => hy₁1 (inv_eq_one.mp h1)
  set ub' := y₂b * ub * y₂b⁻¹ with hub'
  have heu' : ((φ ub' : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹) * g⁻¹) := by
    rw [hub', hφmul, hφmul, hφinv, he₂, heu]
    simp only [map_mul, map_inv]
    group
  have huu' : ub * ub' = ub' * ub := by
    apply hφinj
    rw [hφmul ub ub', hφmul ub' ub, heu, heu', Sec4.cycThree_conj_diagUnits, ← map_mul, ← map_mul]
    congr 1
    calc g * diagUnits w 1 w⁻¹ * g⁻¹ * (g * diagUnits w⁻¹ w 1 * g⁻¹) =
        g * (diagUnits w 1 w⁻¹ * diagUnits w⁻¹ w 1) * g⁻¹ := by group
      _ = g * (diagUnits w⁻¹ w 1 * diagUnits w 1 w⁻¹) * g⁻¹ := by rw [diagUnits_comm]
      _ = g * diagUnits w⁻¹ w 1 * g⁻¹ * (g * diagUnits w 1 w⁻¹ * g⁻¹) := by group
  have hsq : y₂b * ub' * y₂b⁻¹ = (ub * ub')⁻¹ := by
    apply hφinj
    rw [hφmul (y₂b * ub') y₂b⁻¹, hφmul y₂b ub', hφinv y₂b, hφinv (ub * ub'), hφmul ub ub', he₂,
      heu, heu', ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    have h1 := cycThree_sq_conj_diagUnits w
    calc g * cycThree * g⁻¹ * (g * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹) * g⁻¹) *
          (g * cycThree * g⁻¹)⁻¹ =
        g * (cycThree * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹) * cycThree⁻¹) * g⁻¹ := by
          group
      _ = g * (diagUnits w 1 w⁻¹ * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹))⁻¹ * g⁻¹ := by
          rw [h1]
      _ = (g * diagUnits w 1 w⁻¹ * g⁻¹ *
          (g * (cycThree * diagUnits w 1 w⁻¹ * cycThree⁻¹) * g⁻¹))⁻¹ := by group
  have hu'9 : ub' ^ 9 = 1 := by rw [hub', conj_pow, hu9, mul_one, mul_inv_cancel]
  have hcommb : ((φ ⁅ub, y₂b⁆ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagUnits τ 1 1 * g⁻¹) := by
    rw [commutatorElement_def, hφmul, hφmul, hφmul, hφinv, hφinv, heu, he₂]
    have h1 := cycThree_comm_diagUnits w
    have h2 := mk_diagUnits_comm w
    rw [hw3] at h2
    have h3 : diagUnits w 1 w⁻¹ * cycThree * (diagUnits w 1 w⁻¹)⁻¹ * cycThree⁻¹ =
        (diagUnits (w⁻¹ * w⁻¹) w w)⁻¹ := by
      rw [← h1]
      group
    have h4 : ProjGenLinGroup.mk (diagUnits w 1 w⁻¹ * cycThree * (diagUnits w 1 w⁻¹)⁻¹ *
        cycThree⁻¹) = ProjGenLinGroup.mk (diagUnits τ 1 1) := by
      rw [h3, map_inv, h2, ← map_inv, Sec4.diagUnits_inv, inv_inv, inv_one]
    simp only [map_mul, map_inv] at h4 ⊢
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagUnits w 1 w⁻¹) * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagUnits w 1 w⁻¹) *
            (ProjGenLinGroup.mk g)⁻¹)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹)⁻¹ =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (diagUnits w 1 w⁻¹) *
          ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk (diagUnits w 1 w⁻¹))⁻¹ *
          (ProjGenLinGroup.mk cycThree)⁻¹) * (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagUnits τ 1 1) *
          (ProjGenLinGroup.mk g)⁻¹ := by rw [h4]
  have hcomm3 : ⁅ub, y₂b⁆ ^ 3 = 1 := by
    apply hφinj
    have hτ3 : τ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hτ
    rw [hφpow, hφone, hcommb, ← map_pow, conj_pow, Sec4.diagUnits_pow, hτ3, one_pow,
      Sec4.diagUnits_one, mul_one, mul_inv_cancel, map_one]
  have hcomm_not : ⁅ub, y₂b⁆ ∉ Subgroup.zpowers y₁b := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply mk_diagUnits_not_mem_zpowers hτ₀3 hτ₀1 g hτ1
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [← hcommb, ← hm, map_zpow, Subgroup.coe_zpow, he₁]
  have hp9 : ∀ z : L ⧸ θ, z ^ 9 = 1 → IsPGroup 3 (Subgroup.zpowers z) := by
    intro z hz
    rintro ⟨u, hu⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine ⟨2, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show (((3 : ℕ) ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, hz, one_zpow]
  have hy₂9 : y₂b ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl, pow_mul, hy₂3, one_pow]
  set A' : Subgroup (L ⧸ θ) := Subgroup.zpowers ub ⊔ Subgroup.zpowers ub' with hA'
  set B : Subgroup (L ⧸ θ) := A' ⊔ Subgroup.zpowers y₂b with hB
  have hnorm1 : Subgroup.zpowers ub' ≤ Subgroup.normalizer (Subgroup.zpowers ub : Set (L ⧸ θ)) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_map_le
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    change ub' * ub * ub'⁻¹ ∈ _
    rw [← huu', mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _
  have hA'p : IsPGroup 3 A' :=
    IsPGroup.to_sup_of_normal_left' (hp9 ub hu9) (hp9 ub' hu'9) hnorm1
  have hnorm2 : Subgroup.zpowers y₂b ≤ Subgroup.normalizer (A' : Set (L ⧸ θ)) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_map_le
    rw [hA', Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      change y₂b * ub * y₂b⁻¹ ∈ _
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [Subgroup.zpowers_le]
      change y₂b * ub' * y₂b⁻¹ ∈ _
      rw [hsq]
      exact inv_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hBp : IsPGroup 3 B := IsPGroup.to_sup_of_normal_left' hA'p (hp9 y₂b hy₂9) hnorm2
  set M : Subgroup L := (Subgroup.normalizer (E : Set G)).comap L.subtype with hM
  have hmapN : ∀ w' : L, (∀ x ∈ E, (w' : G) * x * (w' : G)⁻¹ ∈ E ⊔ θG) →
      (w' : L ⧸ θ) ∈ M.map (QuotientGroup.mk' θ) := by
    intro w' hw'
    obtain ⟨m, hmL, hmN, hmw⟩ := exists_mem_normalizer_of_conj_mem hEN hEp w'.2 hw'
    refine ⟨⟨m, hmL⟩, hmN, ?_⟩
    change ((⟨m, hmL⟩ : L) : L ⧸ θ) = (w' : L ⧸ θ)
    rw [mk_eq_mk_iff]
    refine inv_mul_mem_theta_of_mul_inv_mem hmL ?_
    have := inv_mem hmw
    rwa [mul_inv_rev, inv_inv] at this
  have hfixu := fixed_of_diag hEN hτD hdiag heu
  have hfix₁ := fixed_of_diag hEN hτD hdiag (z := y₁b) (a := τ) (b := τ ^ 2) (c' := 1)
    (by rw [he₁, Sec4.diagTau_eq_diagUnits hτ₀3 hτ₀0])
  obtain ⟨wu, hwu⟩ := QuotientGroup.mk_surjective ub
  have hubM : ub ∈ M.map (QuotientGroup.mk' θ) := by
    rw [← hwu]
    exact hmapN wu (conj_mem_sup_of_fixed hEN wu fun x hx => by rw [hwu]; exact hfixu x hx)
  obtain ⟨w₂, hw₂⟩ := QuotientGroup.mk_surjective y₂b
  have hy₂M : y₂b ∈ M.map (QuotientGroup.mk' θ) := by
    rw [← hw₂]
    refine hmapN w₂ (conj_mem_sup_of_comm hEN hE3 hEmax hτD hdiag ?_ w₂ (by rw [hw₂]; exact he₂))
    intro y hyD
    obtain ⟨l₀, s₀, t₀, hs₀, ht₀, hl₀⟩ := hdiag y hyD
    have hs3 : s₀ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs₀
    have ht3 : t₀ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht₀
    exact ⟨t₀, s₀⁻¹, s₀ * t₀⁻¹, ht3, by rw [inv_pow, hs3, inv_one],
      by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul], comm_cycThree_conj hl₀⟩
  have hu'M : ub' ∈ M.map (QuotientGroup.mk' θ) := mul_mem (mul_mem hy₂M hubM) (inv_mem hy₂M)
  have hBM : B ≤ M.map (QuotientGroup.mk' θ) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hubM) (Subgroup.zpowers_le.mpr hu'M))
      (Subgroup.zpowers_le.mpr hy₂M)
  obtain ⟨S, -, hSM, hS3, hSB⟩ := exists_isPGroup_le_map_eq hBp hBM IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  have hinjS := injOn_mk_of_isPGroup Nat.prime_three hS3
  set Ybar := Subgroup.zpowers y₁b ⊔ Subgroup.zpowers y₂b with hYbar
  have hy₁B : y₁b ∈ B := by
    have : y₁b = (ub ^ 3)⁻¹ := by rw [hu3, inv_inv]
    rw [this]
    exact inv_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers ub))) 3)
  have hYB : Ybar ≤ S.map (QuotientGroup.mk' θ) := by
    rw [hSB]
    exact sup_le (Subgroup.zpowers_le.mpr hy₁B)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hY9 : Nat.card Ybar = 9 := Sec4.card_zpowers_sup_zpowers hy₂3 hord₁ hy₂₁ hy12.symm
  have hYab : CFSG.Assembly.IsElemAbelian 3 Ybar := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hY9]; norm_num), ?_⟩
    intro u hu
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hy12 hu
    rw [(Commute.zpow_zpow hy12 i j).mul_pow, zpow_pow_three hy₁3 i, zpow_pow_three hy₂3 j,
      mul_one]
  obtain ⟨Y₀, hY₀S, hY₀ab, hY₀9, hY₀Y⟩ := Sec13.exists_elemAbelian_map_eq hYab hYB
  have hY₀3 : IsPGroup 3 Y₀ := fun u => ⟨1, Subtype.ext (by simpa using hY₀ab.2 u u.2)⟩
  obtain ⟨y₁', hy₁'Y, hy₁'b⟩ : y₁b ∈ Y₀.map (QuotientGroup.mk' θ) := by
    rw [hY₀Y]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  obtain ⟨y', hy'Y, hy'b⟩ : y₂b ∈ Y₀.map (QuotientGroup.mk' θ) := by
    rw [hY₀Y]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨n', hn'S, hn'b⟩ : ub ∈ S.map (QuotientGroup.mk' θ) := by
    rw [hSB]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hy₁'b' : ((y₁' : L) : L ⧸ θ) = y₁b := hy₁'b
  have hy'b' : ((y' : L) : L ⧸ θ) = y₂b := hy'b
  have hn'b' : ((n' : L) : L ⧸ θ) = ub := hn'b
  have hy₁'S := hY₀S hy₁'Y
  have hy'S := hY₀S hy'Y
  have hy₁N : (y₁' : G) ∈ Subgroup.normalizer (E : Set G) := hSM hy₁'S
  have hyN : (y' : G) ∈ Subgroup.normalizer (E : Set G) := hSM hy'S
  have hnN : (n' : G) ∈ Subgroup.normalizer (E : Set G) := hSM hn'S
  have hy₁C : (y₁' : G) ∈ Subgroup.centralizer (E : Set G) :=
    mem_centralizer_of_fixed' hEN hEp hy₁N fun x hx => by rw [hy₁'b']; exact hfix₁ x hx
  have hnC : (n' : G) ∈ Subgroup.centralizer (E : Set G) :=
    mem_centralizer_of_fixed' hEN hEp hnN fun x hx => by rw [hn'b']; exact hfixu x hx
  have hy₁3' : (y₁' : G) ^ 3 = 1 := by
    have := hY₀ab.2 y₁' hy₁'Y
    simpa using congrArg Subtype.val this
  have hy3' : (y' : G) ^ 3 = 1 := by
    have := hY₀ab.2 y' hy'Y
    simpa using congrArg Subtype.val this
  have hmemE : ∀ z ∈ Subgroup.centralizer (E : Set G), z ^ 3 = 1 → z ∈ E := by
    intro z hzC hz3
    by_contra hzE
    obtain ⟨hab, -⟩ := Sec5.isElemAbelian_sup_zpowers hE3 hzE hz3
      (fun a ha => Subgroup.mem_centralizer_iff.mp hzC a ha)
    exact hzE (hEmax _ hab le_sup_left ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hy₁E : (y₁' : G) ∈ E := hmemE _ hy₁C hy₁3'
  have hy₁1 : (y₁' : G) ≠ 1 := by
    intro h1
    apply hy₁1
    rw [← hy₁'b', show y₁' = 1 from Subtype.ext h1, QuotientGroup.mk_one]
  have hn9 : (n' : G) ^ 9 = 1 := by
    have : n' ^ 9 = 1 := hinjS (S.pow_mem hn'S 9) S.one_mem (by
      rw [map_pow, map_one]
      exact hn'b ▸ hu9)
    simpa using congrArg Subtype.val this
  have hn3y : (n' : G) ^ 3 = (y₁' : G)⁻¹ := by
    have : n' ^ 3 = y₁'⁻¹ := hinjS (S.pow_mem hn'S 3) (S.inv_mem hy₁'S) (by
      rw [map_pow, map_inv]
      change ((n' : L) : L ⧸ θ) ^ 3 = (((y₁' : L) : L ⧸ θ))⁻¹
      rw [hn'b', hy₁'b', hu3])
    simpa using congrArg Subtype.val this
  have hn3 : (n' : G) ^ 3 ≠ 1 := by
    rw [hn3y]
    exact fun h1 => hy₁1 (inv_eq_one.mp h1)
  have hbS : ⁅n', y'⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hn'S hy'S) (S.inv_mem hn'S)) (S.inv_mem hy'S)
  have hbb : ((⁅n', y'⁆ : L) : L ⧸ θ) = ⁅ub, y₂b⁆ := by
    rw [commutatorElement_def, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hn'b', hy'b']
  have hb3 : (⁅(n' : G), (y' : G)⁆) ^ 3 = 1 := by
    have : ⁅n', y'⁆ ^ 3 = 1 := hinjS (S.pow_mem hbS 3) S.one_mem (by
      rw [map_pow, map_one]
      change ((⁅n', y'⁆ : L) : L ⧸ θ) ^ 3 = 1
      rw [hbb, hcomm3])
    have h2 := congrArg Subtype.val this
    simpa [commutatorElement_def] using h2
  have hbC : ⁅(n' : G), (y' : G)⁆ ∈ Subgroup.centralizer (E : Set G) := by
    have hconjC : (y' : G) * (n' : G)⁻¹ * (y' : G)⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : (y' : G)⁻¹ * e * (y' : G) ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) e).mp he
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp (inv_mem hnC) _ he'
      calc e * ((y' : G) * (n' : G)⁻¹ * (y' : G)⁻¹) =
          (y' : G) * (((y' : G)⁻¹ * e * (y' : G)) * (n' : G)⁻¹) * (y' : G)⁻¹ := by group
        _ = (y' : G) * ((n' : G)⁻¹ * ((y' : G)⁻¹ * e * (y' : G))) * (y' : G)⁻¹ := by rw [hc]
        _ = (y' : G) * (n' : G)⁻¹ * (y' : G)⁻¹ * e := by group
    rw [commutatorElement_def, show (n' : G) * (y' : G) * (n' : G)⁻¹ * (y' : G)⁻¹ =
      (n' : G) * ((y' : G) * (n' : G)⁻¹ * (y' : G)⁻¹) by group]
    exact mul_mem hnC hconjC
  have hbE : ⁅(n' : G), (y' : G)⁆ ∈ E := hmemE _ hbC hb3
  have hbL : ⁅(n' : G), (y' : G)⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem n'.2 y'.2) (L.inv_mem n'.2)) (L.inv_mem y'.2)
  have hbcoe : ((⁅n', y'⁆ : L) : G) = ⁅(n' : G), (y' : G)⁆ := by
    simp [commutatorElement_def]
  have hb_not : ∀ m : ℤ, ⁅(n' : G), (y' : G)⁆ ≠ (y₁' : G) ^ m := by
    intro m hm
    apply hcomm_not
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have h1 : ⁅n', y'⁆ = y₁' ^ m := Subtype.ext (by rw [hbcoe, hm]; simp)
    rw [← hbb, h1, QuotientGroup.mk_zpow, hy₁'b']
  have hyE : (y' : G) ∉ E := by
    intro hyE
    have h1 : ⁅(n' : G), (y' : G)⁆ = 1 := by
      rw [commutatorElement_def, (Subgroup.mem_centralizer_iff.mp hnC _ hyE).symm]
      group
    exact hb_not 0 (by rw [h1, zpow_zero])
  set Y : Subgroup G := Y₀.map L.subtype with hYdef
  have hYL : Y ≤ L := Subgroup.map_subtype_le Y₀
  have hYN : Y ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.map_le_iff_le_comap.mpr (hY₀S.trans hSM)
  have hYab' : CFSG.Assembly.IsElemAbelian 3 Y := Sec13.isElemAbelian_map hY₀ab L.subtype
  have hYcard : Nat.card Y = 9 := by
    rw [hYdef, Subgroup.card_map_of_injective L.subtype_injective, hY₀9, hY9]
  have hcY : c ∉ Y := fun hc => hcL (hYL hc)
  obtain ⟨hFab, hF27⟩ :=
    Sec5.isElemAbelian_sup_zpowers hYab' hcY hc3 (fun a ha => hLc a (hYL ha))
  set F : Subgroup G := Y ⊔ Subgroup.zpowers c with hFdef
  have hFL : F ⊓ L = Y := by
    rw [hFdef, sup_comm]
    exact Sec13.zpowers_sup_inf_eq hc3 hcL hYL (fun y hy => (hLc y (hYL hy)).symm)
  have hy₁Y : (y₁' : G) ∈ Y := ⟨y₁', hy₁'Y, rfl⟩
  have hyY : (y' : G) ∈ Y := ⟨y', hy'Y, rfl⟩
  have hFEL : F ≤ E ⊔ L := sup_le (hYL.trans le_sup_right)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcE))
  have hFN : F ≤ Subgroup.normalizer (E : Set G) :=
    sup_le hYN (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hcE))
  have hF27' : Nat.card F = 27 := by rw [hF27, hYcard]
  have htr := Sec4.transitive_of_normal_form (L := (⊤ : Subgroup (L ⧸ θ))) hK hq
    (Subgroup.topEquiv.trans φ) hτ₀3 hτ₀1 hg (x₁ := y₁b) (x₂ := y₂b) (Subgroup.mem_top _)
    (Subgroup.mem_top _) he₁ he₂
  have htr' : ∀ u ∈ Y₀.map (QuotientGroup.mk' θ), u ≠ 1 →
      ∀ v ∈ Y₀.map (QuotientGroup.mk' θ), v ≠ 1 →
        ∃ m ∈ Subgroup.normalizer ((Y₀.map (QuotientGroup.mk' θ) : Subgroup (L ⧸ θ)) :
          Set (L ⧸ θ)), m * u * m⁻¹ = v := by
    rw [hY₀Y]
    intro u hu hu1 v hv hv1
    obtain ⟨m, hm, hmuv⟩ := htr u hu hu1 v hv hv1
    exact ⟨m, hm.2, hmuv⟩
  have hF : IsF138N L E F := by
    refine ⟨⟨hFEL, hFab, hF27', ?_, hFN⟩, by rw [hFL, hYcard]⟩
    intro u hu hu1 v hv hv1
    rw [hFL] at hu hv
    obtain ⟨u', hu'Y, rfl⟩ := hu
    obtain ⟨v', hv'Y, rfl⟩ := hv
    have hu'1 : u' ≠ 1 := fun h1 => hu1 (by rw [h1, map_one])
    have hv'1 : v' ≠ 1 := fun h1 => hv1 (by rw [h1, map_one])
    obtain ⟨m, -, hm⟩ := exists_conj_of_map_mk hY₀3 htr' hu'Y hu'1 hv'Y hv'1
    exact ⟨m, m.2, congrArg Subtype.val hm⟩
  have hc1 : c ≠ 1 := h.ne_one
  have hcF : c ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hy₁F : (y₁' : G) ∈ F := Subgroup.mem_sup_left hy₁Y
  have hyF : (y' : G) ∈ F := Subgroup.mem_sup_left hyY
  have hy₁c : (y₁' : G) ∉ Subgroup.zpowers c := by
    intro hmem
    have : (y₁' : G) ∈ Subgroup.zpowers c ⊓ L := Subgroup.mem_inf.mpr ⟨hmem, y₁'.2⟩
    rw [zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at this
    exact hy₁1 this
  have hZ9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers (y₁' : G) : Subgroup G) = 9 :=
    Sec4.card_zpowers_sup_zpowers hy₁3' (orderOf_eq_prime hc3 hc1) hy₁c (hLc _ y₁'.2)
  have hZle : Subgroup.zpowers c ⊔ Subgroup.zpowers (y₁' : G) ≤ E ⊓ F :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcE, hcF⟩))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hy₁E, hy₁F⟩))
  have h9 : Nat.card (E ⊓ F : Subgroup G) = 9 := by
    have hdvd : Nat.card (E ⊓ F : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h9dvd : 9 ∣ Nat.card (E ⊓ F : Subgroup G) := hZ9 ▸ Subgroup.card_dvd_of_le hZle
    obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hne : Nat.card (E ⊓ F : Subgroup G) ≠ 27 := by
      intro h27
      have hEF' : E ⊓ F = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hE27])
      have hEF'' : E = F := Subgroup.eq_of_le_of_card_ge (hEF' ▸ inf_le_right)
        (by rw [hE27, hF27'])
      exact hyE (hEF'' ▸ hyF)
    rw [hm] at h9dvd hne ⊢
    interval_cases m <;> revert h9dvd hne <;> norm_num
  have h81 : Nat.card (E ⊔ F : Subgroup G) = 81 := by
    have h1 := Sec6.card_sup_mul_card_inf hFN
    rw [hF27', hE27, sup_comm, inf_comm, h9] at h1
    omega
  obtain ⟨x, hxE, hxy⟩ : ∃ x ∈ E, x * (y' : G) ≠ (y' : G) * x := by
    by_contra hall
    push Not at hall
    have hsup := Sec15.isElemAbelian_sup_zpowers hE3 hy3' hall
    have heq := hEmax _ hsup le_sup_left
    exact hyE (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hx3 : x ^ 3 = 1 := hE3.2 x hxE
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hFab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPNF : E ⊔ F ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_of_card le_sup_right hF27' h81
  set y := (y' : G) with hydef
  have hd₀1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    apply hxy
    rw [commutatorElement_def] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hd₀E : ⁅x, y⁆ ∈ E := by
    rw [commutatorElement_def]
    have : y * x⁻¹ * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hFN hyF) _).mp (inv_mem hxE)
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hxE this
  have hd₀F : ⁅x, y⁆ ∈ F := by
    rw [commutatorElement_def]
    have : x * y * x⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hPNF (Subgroup.mem_sup_left hxE)) _).mp hyF
    exact mul_mem this (inv_mem hyF)
  have hd₀L : ⁅x, y⁆ ∈ L := by
    rw [commutatorElement_def]
    have h1 : x * y * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hEN hxE) y).mp y'.2
    exact mul_mem h1 (inv_mem y'.2)
  have hd₀3 : ⁅x, y⁆ ^ 3 = 1 := hE3.2 _ hd₀E
  have hframe : HeisFrame (E ⊓ F) x y := by
    refine ⟨hx3, hy3', fun z hz => hEc z hz.1 x hxE, fun z hz => hFc z hz.2 y hyF,
      fun z hz z' hz' => hEc z hz.1 z' hz'.1, Subgroup.mem_inf.mpr ⟨hd₀E, hd₀F⟩,
      fun i j hij => ?_⟩
    have hij' := Subgroup.mem_inf.mp hij
    have hxi : x ^ i ∈ E ⊓ F := by
      refine Subgroup.mem_inf.mpr ⟨pow_mem hxE i, ?_⟩
      have := F.mul_mem hij'.2 (F.inv_mem (F.pow_mem hyF j))
      rwa [mul_inv_cancel_right] at this
    have hyj : y ^ j ∈ E ⊓ F := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem hyF j⟩
      have := E.mul_mem (E.inv_mem (E.pow_mem hxE i)) hij'.1
      rwa [inv_mul_cancel_left] at this
    constructor
    · by_contra hi
      have hxZ : x ∈ E ⊓ F := Subgroup.zpowers_le.mpr hxi (mem_zpowers_pow_of_not_dvd hx3 hi)
      exact hxy (hFc x hxZ.2 y hyF)
    · by_contra hj
      have hyZ : y ∈ E ⊓ F := Subgroup.zpowers_le.mpr hyj (mem_zpowers_pow_of_not_dvd hy3' hj)
      exact hxy (hEc x hxE y hyZ.1)
  have hEY : E ⊓ F ⊓ L = E ⊓ Y := by rw [inf_assoc, hFL]
  have hEYle : Nat.card (E ⊓ Y : Subgroup G) ≤ 3 := by
    have hdvd : Nat.card (E ⊓ Y : Subgroup G) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hYcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨m, hm2, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hne : Nat.card (E ⊓ Y : Subgroup G) ≠ 9 := by
      intro h9'
      have : E ⊓ Y = Y := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h9', hYcard])
      have hyEY : y ∈ E ⊓ Y := by rw [this]; exact hyY
      exact hyE hyEY.1
    rw [hm] at hne ⊢
    interval_cases m <;> revert hne <;> norm_num
  have hEFL : E ⊓ F ⊓ L = Subgroup.zpowers ⁅x, y⁆ := by
    rw [hEY]
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ?_) ?_).symm
    · rw [← hEY]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hd₀E, hd₀F⟩, hd₀L⟩
    · rw [card_zpowers_of_pow_three hd₀3 hd₀1]
      exact hEYle
  have hy₁d : (y₁' : G) ∈ Subgroup.zpowers ⁅x, y⁆ := by
    rw [← hEFL, hEY]
    exact Subgroup.mem_inf.mpr ⟨hy₁E, hy₁Y⟩
  have hzd : Subgroup.zpowers (y₁' : G) = Subgroup.zpowers ⁅x, y⁆ :=
    zpowers_eq_of_mem hy₁3' hy₁1 hd₀3 hd₀1 hy₁d
  obtain ⟨wt, hwt⟩ := QuotientGroup.mk_surjective swb
  have hcommW : ∀ y ∈ D, ∃ a b c' : Kˣ, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c' ^ 3 = 1 ∧
      (g * swapTwoThree * g⁻¹) * y * (g * swapTwoThree * g⁻¹)⁻¹ * y⁻¹ =
        g * diagUnits a b c' * g⁻¹ := by
    intro y hyD
    obtain ⟨l₀, s₀, t₀, hs₀, ht₀, hl₀⟩ := hdiag y hyD
    have hs3 : s₀ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs₀
    have ht3 : t₀ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht₀
    exact ⟨1, t₀ * s₀⁻¹, s₀ * t₀⁻¹, one_pow 3,
      by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul],
      by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul], comm_swapTwoThree_conj hl₀⟩
  obtain ⟨t, htL, htN, htw⟩ := exists_mem_normalizer_of_conj_mem hEN hEp wt.2
    (conj_mem_sup_of_comm hEN hE3 hEmax hτD hdiag hcommW wt (by rw [hwt]; exact hew))
  have htw' : ((⟨t, htL⟩ : L) : L ⧸ θ) = swb := by
    rw [← hwt, mk_eq_mk_iff]
    refine inv_mul_mem_theta_of_mul_inv_mem htL ?_
    have := inv_mem htw
    rwa [mul_inv_rev, inv_inv] at this
  have hinvbar : swb * y₁b * swb⁻¹ = y₁b⁻¹ := by
    apply hφinj
    rw [hφmul, hφmul, hφinv, hφinv, hew, he₁]
    have h1 := mk_swapTwoThree_conj_diagTau (K := K) hτ₀3
    simp only [map_mul, map_inv] at h1 ⊢
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk swapTwoThree * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ₀3) * (ProjGenLinGroup.mk g)⁻¹) *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk swapTwoThree * (ProjGenLinGroup.mk g)⁻¹)⁻¹ =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk swapTwoThree *
          ProjGenLinGroup.mk (diagTau hτ₀3) * (ProjGenLinGroup.mk swapTwoThree)⁻¹) *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ₀3) *
          (ProjGenLinGroup.mk g)⁻¹)⁻¹ := by rw [h1]; group
  have htyL : t * (y₁' : G) * t⁻¹ ∈ L := mul_mem (mul_mem htL y₁'.2) (inv_mem htL)
  have hty₁ : t * (y₁' : G) * t⁻¹ = (y₁' : G)⁻¹ := by
    have hE1 : t * (y₁' : G) * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp htN _).mp hy₁E
    have := eq_of_mk_eq_of_mem (a := ⟨t * (y₁' : G) * t⁻¹, htyL⟩) (b := y₁'⁻¹) hEp hE1
      (inv_mem hy₁E) (by
        have e1 : (⟨t * (y₁' : G) * t⁻¹, htyL⟩ : L) = ⟨t, htL⟩ * y₁' * (⟨t, htL⟩)⁻¹ := rfl
        rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, htw', hy₁'b',
          QuotientGroup.mk_inv, hy₁'b', hinvbar])
    simpa using this
  have htd : t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆⁻¹ := by
    have hdy : ⁅x, y⁆ ∈ Subgroup.zpowers (y₁' : G) := hzd ▸ Subgroup.mem_zpowers _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdy
    rw [← hm, ← conj_zpow, hty₁, inv_zpow]
  have hEt : ∀ a ∈ E, t * a * t⁻¹ * a⁻¹ ∈ Subgroup.zpowers ⁅x, y⁆ := by
    intro a ha
    rw [← hzd]
    have hkL : t * a * t⁻¹ * a⁻¹ ∈ L := by
      have h1 : a * t⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hEN ha) _).mp (inv_mem htL)
      rw [show t * a * t⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) by group]
      exact mul_mem htL h1
    have hkE : t * a * t⁻¹ * a⁻¹ ∈ E :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp htN a).mp ha) (inv_mem ha)
    set σa := L.normalizerMonoidHom ⟨a, hEN ha⟩ with hσa
    have hkdef : (⟨t * a * t⁻¹ * a⁻¹, hkL⟩ : L) = ⟨t, htL⟩ * (σa ⟨t, htL⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσa, Sec4.normalizerMonoidHom_apply_coe]
      group
    obtain ⟨yd, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, hEN ha, ha, rfl⟩)
    obtain ⟨a', b', c', ha', hb', hc', hcomm⟩ := hcommW yd hyD
    obtain ⟨l₀, s₀, t₀, hs₀, ht₀, hl₀⟩ := hdiag yd hyD
    have hs3 : s₀ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs₀
    have ht3 : t₀ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht₀
    have hkb : ((φ ((⟨t * a * t⁻¹ * a⁻¹, hkL⟩ : L) : L ⧸ θ) : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * diagUnits 1 (t₀ * s₀⁻¹) (t₀ * s₀⁻¹)⁻¹ * g⁻¹) := by
      have hinvu : (t₀ * s₀⁻¹)⁻¹ = s₀ * t₀⁻¹ := by rw [mul_inv_rev, inv_inv]
      rw [hkdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← Sec4.thetaQuotMulAut_mk, htw',
        hφmul, hφinv, hyz, hew, hinvu, ← comm_swapTwoThree_conj hl₀]
      simp only [map_mul, map_inv]
      group
    have hu3 : (t₀ * s₀⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul]
    have hmem := mk_diagUnits_one_mem_zpowers hτ₀3 hτ₀1 g hu3
    rw [← hkb, ← he₁] at hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hkm : (((⟨t * a * t⁻¹ * a⁻¹, hkL⟩ : L) : L ⧸ θ)) = y₁b ^ m := by
      apply hφinj
      rw [map_zpow, Subgroup.coe_zpow, hm]
    have := eq_of_mk_eq_of_mem (a := ⟨t * a * t⁻¹ * a⁻¹, hkL⟩) (b := y₁' ^ m) hEp hkE
      (by simpa using zpow_mem hy₁E m) (by rw [hkm, QuotientGroup.mk_zpow, hy₁'b'])
    rw [show t * a * t⁻¹ * a⁻¹ = ((y₁' ^ m : L) : G) from this]
    simpa using zpow_mem (Subgroup.mem_zpowers (y₁' : G)) m
  refine ⟨F, x, y, t, n', ⟨⟨hH, hF, hxE, hyF, hframe, hd₀1, hd₀L, hcF, h81, h9, hEFL, htL, htN,
    htd, hLc t htL, hEt⟩, hle, n'.2, hnC, hn9, hn3, ?_, hbE, ?_⟩⟩
  · rw [hn3y, ← hzd]
    exact inv_mem (Subgroup.mem_zpowers _)
  · intro hmem
    have hmemL : ⁅(n' : G), y⁆ ∈ E ⊓ F ⊓ L := Subgroup.mem_inf.mpr ⟨hmem, hbL⟩
    rw [hEFL, ← hzd] at hmemL
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemL
    exact hb_not m hm.symm

end Inner

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
