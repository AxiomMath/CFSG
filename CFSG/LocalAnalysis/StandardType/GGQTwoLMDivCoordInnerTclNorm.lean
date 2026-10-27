module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

private lemma qTwoLMDivCoordInner_tclnorm_diagonal_ne_zero {F0 : Type} [Field F0] {m : ℕ}
    (hm : 4 ≤ m) {g : GL (Fin m) F0} {lam : F0}
    (h : ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun _ => lam)) :
    lam ≠ 0 := by
  intro h0
  let i : Fin m := ⟨0, by omega⟩
  have hg : ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      (((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hentry : lam * ((((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) i i) = 1 := by
    have h1 := congrFun (congrFun hg i) i
    simpa [h] using h1
  rw [h0, zero_mul] at hentry
  exact zero_ne_one hentry

private lemma qTwoLMDivCoordInner_tclnorm_matrix_smul {F0 : Type} [Field F0] {m : ℕ}
    {A Z U B : GL (Fin m) F0} {lam : F0} (hAZ : A * Z = U * B * U⁻¹)
    (hZ : ((Z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun _ => lam)) :
    ((U : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((B : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      lam • (((A : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((U : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) := by
  have hUB : U * B = A * Z * U := by
    rw [hAZ, mul_assoc, inv_mul_cancel, mul_one]
  have hmat : ((U : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      ((B : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((A : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((Z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          ((U : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
    have h := congrArg
      (fun x : GL (Fin m) F0 => ((x : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) hUB
    simpa only [Units.val_mul] using h
  rw [hmat, hZ, ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul]

theorem qTwoLMDivCoordInner_tcl_norm {B Bs L : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 4 ≤ m) (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ)
    (hrange : ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t) :
    ∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ π' : Equiv.Perm (Fin m), ∀ f,
        (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV π' f) : ↥L) : G) := by
  classical
  intro n hn
  obtain ⟨u, hu⟩ := hU.π_surj (c n)
  have hmonoHyp : ∀ f : ↥(sumZero m 3), ∃ f' : ↥(sumZero m 3), ∃ z : F0, z ≠ 0 ∧
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        (((δ f : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      z • (((δ f' : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
    intro f
    set t : ↥L := n * τ f * n⁻¹ with htdef
    have htG : (t : G) ∈ Bs := by
      have hcoe : (t : G) = (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ := by simp [htdef]
      rw [hcoe]
      exact (Subgroup.mem_normalizer_iff.mp hn (τ f : G)).mp (hτ.mem f)
    obtain ⟨f', hf'⟩ := hrange t htG
    have hct : c t = π (δ f') := by rw [← hf', hτ.comm]
    have hcu : c t = π (u * δ f * u⁻¹) := by
      calc c t = c n * c (τ f) * (c n)⁻¹ := by simp [htdef]
        _ = π u * π (δ f) * (π u)⁻¹ := by rw [hτ.comm f, ← hu]
        _ = π (u * δ f * u⁻¹) := by simp
    set z : Su F0 2 1 m := (δ f')⁻¹ * (u * δ f * u⁻¹) with hzdef
    have hzmem : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hzdef]
      calc π ((δ f')⁻¹ * (u * δ f * u⁻¹))
          = (π (δ f'))⁻¹ * π (u * δ f * u⁻¹) := by simp only [map_mul, map_inv]
        _ = (c t)⁻¹ * c t := by rw [← hct, ← hcu]
        _ = 1 := inv_mul_cancel _
    have hzcenter : z ∈ Subgroup.center (Su F0 2 1 m) := hU.π_ker hzmem
    obtain ⟨lam, hlam⟩ := qTwoLMDivCoordInner_center_scalar hU.card hm hzcenter
    have hlamne : lam ≠ 0 :=
      qTwoLMDivCoordInner_tclnorm_diagonal_ne_zero (m := m) hm (g := (z : GL (Fin m) F0)) hlam
    refine ⟨f', lam, hlamne, ?_⟩
    rw [Matrix.smul_mul]
    exact qTwoLMDivCoordInner_tclnorm_matrix_smul
      (A := (δ f' : GL (Fin m) F0)) (Z := (z : GL (Fin m) F0))
      (U := (u : GL (Fin m) F0)) (B := (δ f : GL (Fin m) F0)) (lam := lam) (by
        have hgroup : (δ f' : Su F0 2 1 m) * z = u * δ f * u⁻¹ := by
          rw [hzdef]
          group
        have h := congrArg (fun x : Su F0 2 1 m => (x : GL (Fin m) F0)) hgroup
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h) hlam
  obtain ⟨ρ', hρ'⟩ := hδ.mono (u : GL (Fin m) F0) hmonoHyp
  refine ⟨ρ', fun f => ?_⟩
  set t : ↥L := n * τ f * n⁻¹ with htdef
  have htG : (t : G) ∈ Bs := by
    have hcoe : (t : G) = (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ := by simp [htdef]
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp hn (τ f : G)).mp (hτ.mem f)
  have hconjSu : u * δ f * u⁻¹ = δ (permAutV ρ' f) := by
    have hρSu : u * δ f = δ (permAutV ρ' f) * u := by
      apply Subtype.ext
      apply Units.ext
      have h := congrArg (fun x : GL (Fin m) F0 => (x : Matrix (Fin m) (Fin m) F0)) (hρ' f)
      simpa only [Subgroup.coe_mul, Units.val_mul] using h
    rw [hρSu, mul_assoc, mul_inv_cancel, mul_one]
  have hpi : π (u * δ f * u⁻¹) = π (δ (permAutV ρ' f)) := by rw [hconjSu]
  have hct : c t = π (u * δ f * u⁻¹) := by
    calc c t = c n * c (τ f) * (c n)⁻¹ := by simp [htdef]
      _ = π u * π (δ f) * (π u)⁻¹ := by rw [hτ.comm f, ← hu]
      _ = π (u * δ f * u⁻¹) := by simp
  set z' : ↥L := (τ (permAutV ρ' f))⁻¹ * t with hz'def
  have hz'ker : z' ∈ c.ker := by
    rw [MonoidHom.mem_ker, hz'def]
    calc c ((τ (permAutV ρ' f))⁻¹ * t)
        = (c (τ (permAutV ρ' f)))⁻¹ * c t := by rw [map_mul, map_inv]
      _ = (π (δ (permAutV ρ' f)))⁻¹ * π (u * δ f * u⁻¹) := by rw [hτ.comm, hct]
      _ = (π (δ (permAutV ρ' f)))⁻¹ * π (δ (permAutV ρ' f)) := by rw [hpi]
      _ = 1 := inv_mul_cancel _
  have hz'G : (z' : G) ∈ Bs := by
    have hcoe : (z' : G) = (((τ (permAutV ρ' f) : ↥L) : G))⁻¹ * (t : G) := by simp [hz'def]
    rw [hcoe]
    exact Bs.mul_mem (Bs.inv_mem (hτ.mem (permAutV ρ' f))) htG
  have hz3 : z' ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hBs.2.1.2 (z' : G) hz'G
  obtain ⟨k, hk⟩ := hU.c_two ⟨z', hz'ker⟩
  have hz2 : z' ^ 2 ^ k = 1 := by
    have h := congrArg (fun x : c.ker => (x : ↥L)) hk
    simpa using h
  have hcop : Nat.Coprime 3 (2 ^ k) := by
    rcases k with _ | k
    · simp
    · rw [Nat.coprime_pow_right_iff (Nat.succ_pos k)]
      decide
  have hz1 : z' = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hz3, hz2⟩
  have ht_perm : t = τ (permAutV ρ' f) := by
    have h : (τ (permAutV ρ' f))⁻¹ * t = 1 := by
      rw [← hz'def]
      exact hz1
    have h2 : (τ (permAutV ρ' f))⁻¹ * t =
        (τ (permAutV ρ' f))⁻¹ * τ (permAutV ρ' f) := by rw [h, inv_mul_cancel]
    exact mul_left_cancel h2
  show (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ = ((τ (permAutV ρ' f) : ↥L) : G)
  have htcoe : (t : G) = (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ := by simp [htdef]
  rw [← htcoe, ht_perm]

end CFSG.StandardType.QTwo

end
