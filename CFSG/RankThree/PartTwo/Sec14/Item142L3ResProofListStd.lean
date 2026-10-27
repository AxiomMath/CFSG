module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListMat
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofNormal
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem exists_std_conj (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y s : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (hy3 : Type123 π (p ^ f) K y 3) (hsSL : s ∈ slPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) :
    ∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧
      ∃ (g : GL (Fin 3) K) (β : K) (cβ : GL (Fin 3) K),
        (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β ∧ (¬ ∃ μ : K, μ ^ 3 = β) ∧
        (ProjGenLinGroup.mk (g⁻¹ * y * g) = ProjGenLinGroup.mk cβ ∨
          ProjGenLinGroup.mk (g⁻¹ * y⁻¹ * g) = ProjGenLinGroup.mk cβ) ∧
        ProjGenLinGroup.mk (g⁻¹ * s * g) = ProjGenLinGroup.mk (diagTau hτ) := by
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hK hq
  obtain ⟨ℓ, hℓ⟩ := hys
  have hysl : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * s := by
    rw [hℓ]
    group
  have hℓ3 : ℓ ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hysl
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hsSL).2
  have hℓ1 : ℓ ≠ 1 := by
    intro h1
    refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ₀ hτ₀1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [h1, map_one, one_mul] at hysl
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hysl]
  obtain ⟨τ, hτ, hτ1, z₀, hz₀, g₁, hg₁, hD⟩ := Proof142Res.type1_of_commute_mod_type3 hK hq hy3
    hsSL hsZ hs3 ⟨ℓ, hℓ⟩
  have hz₀S : z₀ ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₀
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ, Units.val_one])
  have hτu1 : τu ≠ 1 := fun h => hτ1 (by
    have := congrArg Units.val h
    rwa [hτu, Units.val_mk0, Units.val_one] at this)
  have hmks : ∀ g : GL (Fin 3) K, g⁻¹ * (s * z₀) * g = diagTau hτ →
      ProjGenLinGroup.mk (g⁻¹ * s * g) = ProjGenLinGroup.mk (diagTau hτ) := by
    intro g hg
    rw [← hg, map_mul, map_mul, map_mul, map_mul, map_mul,
      mk_eq_one_iff_mem_statedScalars.mpr hz₀S, mul_one]
  have key : ∀ (w : GL (Fin 3) K) (hw : w ∈ glPi π 3 (p ^ f) K),
      w * s * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * s →
      (∀ ν : K, (w : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1 → ∀ μ : K, μ ^ 3 ≠ ν) →
      ∃ (g : GL (Fin 3) K) (β : K) (cβ : GL (Fin 3) K),
        (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β ∧ (¬ ∃ μ : K, μ ^ 3 = β) ∧
        g⁻¹ * w * g = cβ ∧ ProjGenLinGroup.mk (g⁻¹ * s * g) = ProjGenLinGroup.mk (diagTau hτ) := by
    intro w hw hws hwc
    obtain ⟨g, -, β, cβ, -, hcβm, hgw, hgs⟩ := exists_std_form hK hτ hτ1 hw hg₁ hz₀S hD rfl hws
    have hw3 : (w : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1 := by
      have e : w = g * cβ * g⁻¹ := by rw [← hgw]; group
      rw [e, ← Units.val_pow_eq_pow_val, conj_pow, Units.val_mul, Units.val_mul,
        Units.val_pow_eq_pow_val, hcβm, heisC_pow_three, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact ⟨g, β, cβ, hcβm, fun ⟨μ, hμ⟩ => hwc β hw3 μ hμ, hgw, hmks g hgs⟩
  have hy3' : ∀ ν : K, (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1 → ∀ μ : K, μ ^ 3 ≠ ν :=
    fun ν hν => Sec12.KS128NotHJTC.not_cube_of_irreducible hτ₀ hτ₀1 h3 hν hy3.2.2
  refine ⟨τ, hτ, hτ1, ?_⟩
  rcases Res8Hess.mul_eq_one_or_of_cube hℓ3 hτu3 hℓ1 hτu1 with h | h
  ·
    have hℓτ : ℓ = τu ^ 2 := by
      have : ℓ = τu⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, inv_eq_of_mul_eq_one_right (show τu * τu ^ 2 = 1 by rw [← pow_succ']; exact hτu3)]
    obtain ⟨g, β, cβ, hcβm, hβ, hgw, hgs⟩ := key y hy (by rw [hysl, hℓτ]) hy3'
    exact ⟨g, β, cβ, hcβm, hβ, Or.inl (by rw [hgw]), hgs⟩
  ·
    have hℓτ : ℓ⁻¹ = τu ^ 2 := by
      have : ℓ = (τu ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, inv_inv]
    have hyi : y⁻¹ * s * y⁻¹⁻¹ = GeneralLinearGroup.scalar (Fin 3) (τu ^ 2) * s := by
      rw [← hℓτ, inv_inv, map_inv]
      calc y⁻¹ * s * y = y⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ *
            (y * s * y⁻¹) * y := by rw [hysl]; group
        _ = (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ * s := by
            rw [show y⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ =
              (GeneralLinearGroup.scalar (Fin 3) ℓ)⁻¹ * y⁻¹ by
                rw [← map_inv, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ⁻¹ y⁻¹).eq]]
            group
    have hyic : ∀ ν : K, ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1 →
        ∀ μ : K, μ ^ 3 ≠ ν := by
      intro ν hν μ hμ
      have hν0 : ν ≠ 0 := by
        rintro rfl
        have := congrArg Matrix.det hν
        rw [zero_smul, Matrix.det_zero, Matrix.det_pow] at this
        exact ((y⁻¹).isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
          (pow_eq_zero_iff (by norm_num) |>.mp this)
      have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν⁻¹ • 1 := by
        have e : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 * ((y⁻¹ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
            inv_pow, mul_inv_cancel, Units.val_one]
        rw [hν, Matrix.mul_smul, Matrix.mul_one] at e
        calc (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν⁻¹ • (ν • (y : Matrix (Fin 3) (Fin 3) K) ^ 3) :=
              by rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
          _ = ν⁻¹ • 1 := by rw [e]
      exact hy3' ν⁻¹ hy3m μ⁻¹ (by rw [inv_pow, hμ])
    obtain ⟨g, β, cβ, hcβm, hβ, hgw, hgs⟩ := key y⁻¹ (inv_mem hy) hyi hyic
    exact ⟨g, β, cβ, hcβm, hβ, Or.inr (by rw [hgw]), hgs⟩

theorem mk_conj (g x : GL (Fin 3) K) :
    (ProjGenLinGroup.mk g)⁻¹ * ProjGenLinGroup.mk x * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk (g⁻¹ * x * g) := by
  rw [map_mul, map_mul, map_inv]

theorem comm_conj {G : Type*} [Group G] {x z : G} (g : G) (h : x * z = z * x) :
    g⁻¹ * x * g * (g⁻¹ * z * g) = g⁻¹ * z * g * (g⁻¹ * x * g) := by
  calc g⁻¹ * x * g * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
    _ = g⁻¹ * (z * x) * g := by rw [h]
    _ = g⁻¹ * z * g * (g⁻¹ * x * g) := by group

theorem eq_one_of_comm_ys (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y s : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (hy3 : Type123 π (p ^ f) K y 3) (hsSL : s ∈ slPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) {x : ProjGenLinGroup (Fin 3) K}
    (hxy : x * ProjGenLinGroup.mk y = ProjGenLinGroup.mk y * x)
    (hxs : x * ProjGenLinGroup.mk s = ProjGenLinGroup.mk s * x)
    (hx3 : Nat.Coprime 3 (orderOf x)) : x = 1 := by
  obtain ⟨τ, hτ, hτ1, g, β, cβ, hcβm, -, hyc, hsd⟩ :=
    exists_std_conj hπ hK hq hy hy3 hsSL hsZ hs3 hys
  set G := ProjGenLinGroup.mk g with hG
  have hd : G⁻¹ * x * G * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * (G⁻¹ * x * G) := by
    rw [← hsd, ← mk_conj]
    exact comm_conj G hxs
  have hc : G⁻¹ * x * G * ProjGenLinGroup.mk cβ = ProjGenLinGroup.mk cβ * (G⁻¹ * x * G) := by
    rcases hyc with h | h
    · rw [← h, ← mk_conj]
      exact comm_conj G hxy
    · rw [← h, ← mk_conj, map_inv]
      exact comm_conj G ((comm_iff_comm_inv _ x).mp hxy)
  have h3 : Nat.Coprime 3 (orderOf (G⁻¹ * x * G)) := by
    rw [show G⁻¹ * x * G = G⁻¹ * x * G⁻¹⁻¹ by rw [inv_inv], Res8Hess.orderOf_conj_eq]
    exact hx3
  have h1 := eq_one_of_comm_d_c hτ hτ1 hcβm hd hc h3
  calc x = G * (G⁻¹ * x * G) * G⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_le_thetaP_ys (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y s : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (hy3 : Type123 π (p ^ f) K y 3) (hsSL : s ∈ slPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K)
    {Y : Subgroup (ProjGenLinGroup (Fin 3) K)} (hY3 : ¬ 3 ∣ Nat.card Y)
    (hyY : ProjGenLinGroup.mk y ∈ Subgroup.normalizer (Y : Set (ProjGenLinGroup (Fin 3) K)))
    (hsY : ProjGenLinGroup.mk s ∈ Subgroup.normalizer (Y : Set (ProjGenLinGroup (Fin 3) K))) :
    ∃ b ∈ Subgroup.zpowers (ProjGenLinGroup.mk s) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y),
      b ≠ 1 ∧ Y ≤ thetaP b := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  obtain ⟨τ, hτ, hτ1, g, β, cβ, hcβm, hβ, hyc, hsd⟩ :=
    exists_std_conj hπ hK hq hy hy3 hsSL hsZ hs3 hys
  set G := ProjGenLinGroup.mk g with hG
  set Yq := Y.map (MulAut.conj G⁻¹).toMonoidHom with hYq
  have hmemYq : ∀ z, z ∈ Yq ↔ G * z * G⁻¹ ∈ Y := by
    intro z
    rw [hYq, Subgroup.mem_map_equiv]
    simp
  have hYq3 : ¬ 3 ∣ Nat.card Yq := by
    rw [hYq, Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective]
    exact hY3
  have hs' : G * ProjGenLinGroup.mk (diagTau hτ) * G⁻¹ = ProjGenLinGroup.mk s := by
    rw [← hsd, ← mk_conj, ← hG]
    group
  have hw' : G * ProjGenLinGroup.mk cβ * G⁻¹ = ProjGenLinGroup.mk y ∨
      G * ProjGenLinGroup.mk cβ * G⁻¹ = (ProjGenLinGroup.mk y)⁻¹ := by
    rcases hyc with h | h
    · left
      rw [← h, ← mk_conj, ← hG]
      group
    · right
      rw [← h, ← mk_conj, map_inv, ← hG]
      group
  have hnorm : ∀ u : ProjGenLinGroup (Fin 3) K,
      G * u * G⁻¹ ∈ Subgroup.normalizer (Y : Set (ProjGenLinGroup (Fin 3) K)) →
      u ∈ Subgroup.normalizer (Yq : Set (ProjGenLinGroup (Fin 3) K)) := by
    intro u hu
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    simp only [SetLike.mem_coe] at hz ⊢
    rw [hmemYq] at hz ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp hu _).mp hz
    have e : G * u * G⁻¹ * (G * z * G⁻¹) * (G * u * G⁻¹)⁻¹ = G * (u * z * u⁻¹) * G⁻¹ := by
      group
    rwa [e] at h1
  have hEY : Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk cβ) ≤
        Subgroup.normalizer (Yq : Set (ProjGenLinGroup (Fin 3) K)) := by
    refine sup_le (Subgroup.zpowers_le.mpr (hnorm _ (by rw [hs']; exact hsY)))
      (Subgroup.zpowers_le.mpr (hnorm _ ?_))
    rcases hw' with h | h
    · rw [h]
      exact hyY
    · rw [h]
      exact inv_mem hyY
  obtain ⟨b, hbE, hb1, hYb⟩ := exists_le_thetaP hτ hτ1 hcβm hβ hYq3 hEY
  refine ⟨G * b * G⁻¹, ?_, fun h => hb1 ?_, fun z hz => ?_⟩
  ·
    have hle : Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
        Subgroup.zpowers (ProjGenLinGroup.mk cβ) ≤
        (Subgroup.zpowers (ProjGenLinGroup.mk s) ⊔
          Subgroup.zpowers (ProjGenLinGroup.mk y)).map (MulAut.conj G⁻¹).toMonoidHom := by
      have hmem : ∀ u, G * u * G⁻¹ ∈ Subgroup.zpowers (ProjGenLinGroup.mk s) ⊔
          Subgroup.zpowers (ProjGenLinGroup.mk y) →
          u ∈ (Subgroup.zpowers (ProjGenLinGroup.mk s) ⊔
            Subgroup.zpowers (ProjGenLinGroup.mk y)).map (MulAut.conj G⁻¹).toMonoidHom := by
        intro u hu
        refine ⟨G * u * G⁻¹, hu, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      refine sup_le (Subgroup.zpowers_le.mpr (hmem _ ?_)) (Subgroup.zpowers_le.mpr (hmem _ ?_))
      · rw [hs']
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rcases hw' with h | h
        · rw [h]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
        · rw [h]
          exact inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    obtain ⟨u, hu, hub⟩ := hle hbE
    have e : u = G * b * G⁻¹ := by
      rw [← hub]
      simp [MulAut.conj_apply, mul_assoc]
    rw [← e]
    exact hu
  · calc b = G⁻¹ * (G * b * G⁻¹) * G := by group
      _ = 1 := by rw [h]; group
  · have hz' : G⁻¹ * z * G ∈ Yq := by
      rw [hmemYq]
      simpa [mul_assoc] using hz
    have h1 := conj_mem_thetaP G (hYb hz')
    simpa [mul_assoc] using h1

theorem thetaP_facts_ys (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y s : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (hy3 : Type123 π (p ^ f) K y 3) (hsSL : s ∈ slPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) {b : ProjGenLinGroup (Fin 3) K}
    (hb : b ∈ Subgroup.zpowers (ProjGenLinGroup.mk s) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y))
    (hb1 : b ≠ 1) :
    (∀ x ∈ thetaP b, ∀ z ∈ thetaP b, x * z = z * x) ∧
      ∀ x ∈ thetaP b, Nat.Coprime 3 (orderOf x) := by
  have := hK.finite
  obtain ⟨τ, hτ, hτ1, g, β, cβ, hcβm, hβ, hyc, hsd⟩ :=
    exists_std_conj hπ hK hq hy hy3 hsSL hsZ hs3 hys
  set G := ProjGenLinGroup.mk g with hG
  have hs' : G⁻¹ * ProjGenLinGroup.mk s * G = ProjGenLinGroup.mk (diagTau hτ) := by
    rw [hG, mk_conj, hsd]
  set E₀ := Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) ⊔
    Subgroup.zpowers (ProjGenLinGroup.mk cβ) with hE₀
  have hle : Subgroup.zpowers (ProjGenLinGroup.mk s) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y) ≤
      E₀.map (MulAut.conj G).toMonoidHom := by
    have hmem : ∀ u, G⁻¹ * u * G ∈ E₀ → u ∈ E₀.map (MulAut.conj G).toMonoidHom := by
      intro u hu
      refine ⟨G⁻¹ * u * G, hu, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    refine sup_le (Subgroup.zpowers_le.mpr (hmem _ ?_)) (Subgroup.zpowers_le.mpr (hmem _ ?_))
    · rw [hs']
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rcases hyc with h | h
      · rw [hG, mk_conj, h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · have e : G⁻¹ * ProjGenLinGroup.mk y * G = (ProjGenLinGroup.mk cβ)⁻¹ := by
          rw [← h, ← mk_conj, map_inv, ← hG]
          group
        rw [e]
        exact inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨b₀, hb₀, hb₀b⟩ := hle hb
  have hbb₀ : b = G * b₀ * G⁻¹ := by
    rw [← hb₀b]
    simp [MulAut.conj_apply]
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    apply hb1
    rw [hbb₀]
    group
  have hcomm := thetaSet_comm hτ hτ1 hcβm hβ hb₀ hb₀1
  refine thetaP_facts fun x hx z hz => ?_
  have hx' : G⁻¹ * x * G ∈ thetaSet b₀ := by
    refine ⟨?_, by
      rw [show G⁻¹ * x * G = G⁻¹ * x * G⁻¹⁻¹ by rw [inv_inv], Res8Hess.orderOf_conj_eq]
      exact hx.2⟩
    have e : b₀ = G⁻¹ * b * G := by rw [hbb₀]; group
    rw [e]
    exact comm_conj G hx.1
  have hz' : G⁻¹ * z * G ∈ thetaSet b₀ := by
    refine ⟨?_, by
      rw [show G⁻¹ * z * G = G⁻¹ * z * G⁻¹⁻¹ by rw [inv_inv], Res8Hess.orderOf_conj_eq]
      exact hz.2⟩
    have e : b₀ = G⁻¹ * b * G := by rw [hbb₀]; group
    rw [e]
    exact comm_conj G hz.1
  have h1 := hcomm _ hx' _ hz'
  calc x * z = G * (G⁻¹ * x * G * (G⁻¹ * z * G)) * G⁻¹ := by group
    _ = G * (G⁻¹ * z * G * (G⁻¹ * x * G)) * G⁻¹ := by rw [h1]
    _ = z * x := by group

end CFSG.RankThree.PartTwo.Sec14.L3PGL
