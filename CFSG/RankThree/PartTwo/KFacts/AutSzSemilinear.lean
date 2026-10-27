module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.AutTransport
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega
open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open CFSG.Open
open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

section

variable (m : ℕ)

local notation "F" => BinaryGaloisField (2 * m + 1)

theorem torus_one : torus m (1 : Fˣ) = 1 :=
  Subtype.ext (suzukiTorusGL_one m)

theorem torus_mul (x y : Fˣ) : torus m x * torus m y = torus m (x * y) :=
  Subtype.ext (suzukiTorusGL_mul m x y)

theorem torus_inv (x : Fˣ) : (torus m x)⁻¹ = torus m x⁻¹ :=
  Subtype.ext (suzukiTorusGL_inv m x)

private theorem map_rootSub_eq_of_normalizes (α : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m) :
    (rootSub m).map α.toMonoidHom = rootSub m := by
  have hle : (rootSub m).map α.toMonoidHom ≤ rootSub m := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    exact hR r hr
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective α.injective])

private theorem mul_tits_injective :
    Function.Injective (fun x : F => x * tits m x) := by
  intro u v h
  by_cases hv : v = 0
  · subst v
    have hu : u * tits m u = 0 := by simpa using h
    rcases mul_eq_zero.mp hu with h0 | h0
    · exact h0
    · exact (tits m).injective (by rw [h0, map_zero])
  · exact eq_of_mul_tits_eq m hv h

private theorem mul_tits_surjective :
    Function.Surjective (fun x : F => x * tits m x) :=
  Finite.injective_iff_surjective.mp (mul_tits_injective m)

private theorem exists_psi_of_normalizes (hm : 0 < m) (α : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m) :
    ∃ ψ : F → F, Function.Bijective ψ ∧ (∀ a b : F, ψ (a + b) = ψ a + ψ b) ∧
      ∀ b : F, α (root m 0 b) = root m 0 (ψ b) := by
  have hmap := map_rootSub_eq_of_normalizes m α hR
  have hZ : ∀ b : F, α (root m 0 b) ∈ sylowCenter (rootSub m) := by
    intro b
    have h1 : α (root m 0 b) ∈ sylowCenter ((rootSub m).map α.toMonoidHom) := by
      rw [mem_sylowCenter_map]
      exact (mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩
    rwa [hmap] at h1
  choose ψ hψ using fun b => (mem_sylowCenter_rootSub m hm).mp (hZ b)
  have hψadd : ∀ a b : F, ψ (a + b) = ψ a + ψ b := by
    intro a b
    have h := congrArg α (root_mul m hm 0 a 0 b)
    simp only [zero_add, map_zero, zero_mul, add_zero, map_mul] at h
    rw [hψ a, hψ b, hψ (a + b)] at h
    rw [root_mul m hm 0 (ψ a) 0 (ψ b)] at h
    simp only [zero_add, map_zero, zero_mul, add_zero] at h
    exact (root_injective m h).2.symm
  have hψinj : Function.Injective ψ := by
    intro a b h
    have h1 : α (root m 0 a) = α (root m 0 b) := by rw [hψ a, hψ b, h]
    exact (root_injective m (α.injective h1)).2
  exact ⟨ψ, ⟨hψinj, Finite.injective_iff_surjective.mp hψinj⟩, hψadd, hψ⟩

private theorem tits_map_ringEquiv (τ : F ≃+* F) (a : F) :
    τ (tits m a) = tits m (τ a) := by
  rw [tits_apply, tits_apply, map_pow]

private theorem units_map_pow_succ (τ : F ≃+* F) (k : ℕ) (x : Fˣ) :
    Units.map ((τ ^ (k + 1) : F ≃+* F) : F →* F) x =
      Units.map (τ : F →* F) (Units.map ((τ ^ k : F ≃+* F) : F →* F) x) := by
  rw [pow_succ']
  rfl

private theorem tau_fun_mul {ψ : F → F} (hψ0 : ψ 0 = 0)
    (c : Fˣ) (θ : Fˣ → Fˣ)
    (hrel : ∀ (x : Fˣ) (b : F),
      ψ ((x : F) * tits m (x : F) * b) =
        ((θ x : F) * tits m (θ x : F)) * ψ b)
    (hτN : ∀ x : Fˣ, (c : F)⁻¹ * ψ ((x : F) * tits m (x : F)) =
      (θ x : F) * tits m (θ x : F)) :
    ∀ a b : F, (c : F)⁻¹ * ψ (a * b) =
      ((c : F)⁻¹ * ψ a) * ((c : F)⁻¹ * ψ b) := by
  intro a b
  by_cases ha : a = 0
  · subst a
    simp [hψ0]
  · obtain ⟨x, hx⟩ := mul_tits_surjective m a
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h0 : (0 : F) = a := by simpa using hx
      exact ha h0.symm
    let xu : Fˣ := Units.mk0 x hx0
    have hxu : (xu : F) * tits m (xu : F) = a := hx
    calc
      (c : F)⁻¹ * ψ (a * b) =
          (c : F)⁻¹ * ψ (((xu : F) * tits m (xu : F)) * b) := by rw [hxu]
      _ = (c : F)⁻¹ * (((θ xu : F) * tits m (θ xu : F)) * ψ b) := by
        rw [hrel xu b]
      _ = ((θ xu : F) * tits m (θ xu : F)) * ((c : F)⁻¹ * ψ b) := by ring
      _ = (c : F)⁻¹ * ψ ((xu : F) * tits m (xu : F)) * ((c : F)⁻¹ * ψ b) := by
        rw [hτN xu]
      _ = (c : F)⁻¹ * ψ a * ((c : F)⁻¹ * ψ b) := by rw [hxu]

private theorem theta_eq_tau_of_relation (θ : Fˣ → Fˣ) (τ : F ≃+* F)
    (hτN : ∀ x : Fˣ, τ ((x : F) * tits m (x : F)) =
      (θ x : F) * tits m (θ x : F)) :
    ∀ x : Fˣ, (θ x : F) = τ (x : F) := by
  intro x
  have hτtits : ∀ a : F, τ (tits m a) = tits m (τ a) := tits_map_ringEquiv m τ
  have hNτ : τ ((x : F) * tits m (x : F)) =
      (τ (x : F)) * tits m (τ (x : F)) := by rw [map_mul, hτtits]
  apply mul_tits_injective m
  change (θ x : F) * tits m (θ x : F) = (τ (x : F)) * tits m (τ (x : F))
  rw [← hτN, hNτ]

private theorem tau_fun_N {ψ : F → F} (c : Fˣ) (hc : (c : F) = ψ 1)
    (θ : Fˣ → Fˣ)
    (hrel : ∀ (x : Fˣ) (b : F),
      ψ ((x : F) * tits m (x : F) * b) =
        ((θ x : F) * tits m (θ x : F)) * ψ b) :
    ∀ x : Fˣ, (c : F)⁻¹ * ψ ((x : F) * tits m (x : F)) =
      (θ x : F) * tits m (θ x : F) := by
  intro x
  have h := hrel x 1
  simp only [mul_one] at h
  rw [h, ← hc]
  rw [mul_comm ((θ x : F) * tits m (θ x : F)) (c : F), ← mul_assoc,
    inv_mul_cancel₀ c.ne_zero, one_mul]

private theorem exists_tau_of_tits_relation {ψ : F → F}
    (hψ0 : ψ 0 = 0) (hψadd : ∀ a b : F, ψ (a + b) = ψ a + ψ b)
    (hψinj : Function.Injective ψ) (θ : Fˣ → Fˣ)
    (hrel : ∀ (x : Fˣ) (b : F),
      ψ ((x : F) * tits m (x : F) * b) =
        ((θ x : F) * tits m (θ x : F)) * ψ b) :
    ∃ (τ : F ≃+* F) (c : Fˣ),
      (∀ b : F, ψ b = (c : F) * τ b) ∧
        ∀ x : Fˣ, (θ x : F) = τ (x : F) := by
  classical
  have hc : ψ 1 ≠ 0 := by
    intro h
    have h1 : (1 : F) = 0 := hψinj (by rw [h, hψ0])
    exact one_ne_zero h1
  let c : Fˣ := Units.mk0 (ψ 1) hc
  let τfun : F → F := fun b => (c : F)⁻¹ * ψ b
  have hτN : ∀ x : Fˣ, (c : F)⁻¹ * ψ ((x : F) * tits m (x : F)) =
      (θ x : F) * tits m (θ x : F) := tau_fun_N m c rfl θ hrel
  have hτ0 : τfun 0 = 0 := by simp [τfun, hψ0]
  have hτadd : ∀ a b : F, τfun (a + b) = τfun a + τfun b := by
    intro a b
    simp only [τfun, hψadd a b, mul_add]
  have hτone : τfun 1 = 1 := by
    simp only [τfun]
    rw [show ψ 1 = (c : F) from rfl, inv_mul_cancel₀ c.ne_zero]
  have hτmul : ∀ a b : F, τfun (a * b) = τfun a * τfun b :=
    tau_fun_mul m hψ0 c θ hrel hτN
  have hτinj : Function.Injective τfun := by
    intro a b h
    apply hψinj
    exact mul_left_cancel₀ (inv_ne_zero c.ne_zero) h
  let τhom : F →+* F :=
    { toFun := τfun
      map_zero' := hτ0
      map_one' := hτone
      map_add' := hτadd
      map_mul' := hτmul }
  let τ : F ≃+* F :=
    RingEquiv.ofBijective τhom (Finite.injective_iff_bijective.mp hτinj)
  have hτψ : ∀ b : F, (c : F) * τ b = ψ b := by
    intro b
    change (c : F) * ((c : F)⁻¹ * ψ b) = ψ b
    rw [← mul_assoc, mul_inv_cancel₀ c.ne_zero, one_mul]
  have hτNτ : ∀ x : Fˣ, τ ((x : F) * tits m (x : F)) =
      (θ x : F) * tits m (θ x : F) := fun x => hτN x
  exact ⟨τ, c, fun b => (hτψ b).symm, theta_eq_tau_of_relation m θ τ hτNτ⟩

theorem exists_ringEquiv_of_normalizes (hm : 0 < m) (α : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m)
    (hH : ∀ x : Fˣ, ∃ x' : Fˣ, α (torus m x) = torus m x') :
    ∃ (τ : F ≃+* F) (c : Fˣ),
      (∀ b : F, α (root m 0 b) = root m 0 ((c : F) * τ b)) ∧
        ∀ x : Fˣ, α (torus m x) = torus m (Units.map (τ : F →* F) x) := by
  classical
  obtain ⟨ψ, hψbij, hψadd, hψ⟩ := exists_psi_of_normalizes m hm α hR
  have hψinj : Function.Injective ψ := hψbij.1
  choose θ hθ using hH
  have hψ0 : ψ 0 = 0 := by
    have h := hψ 0
    rw [root_zero_zero, map_one, ← root_zero_zero] at h
    exact (root_injective m h).2.symm
  have hrel : ∀ (x : Fˣ) (b : F),
      ψ ((x : F) * tits m (x : F) * b) =
        ((θ x : F) * tits m (θ x : F)) * ψ b := by
    intro x b
    have h := congrArg α (torus_conj_root m 0 b x)
    rw [map_mul, map_mul, map_inv, mul_zero] at h
    rw [hθ, hψ b, hψ ((x : F) * tits m (x : F) * b)] at h
    rw [torus_conj_root m 0 (ψ b) (θ x)] at h
    simp only [mul_zero] at h
    exact (root_injective m h).2.symm
  obtain ⟨τ, c, hψc, hθτ⟩ := exists_tau_of_tits_relation m hψ0 hψadd hψinj θ hrel
  refine ⟨τ, c, ?_, ?_⟩
  · intro b
    rw [hψ b]
    congr 1
    exact hψc b
  · intro x
    rw [hθ x]
    congr 1
    apply Units.ext
    simpa using hθτ x

theorem exists_conj_inv_mul_normalizes_torus (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m) :
    ∃ r ∈ rootSub m, ∀ x : Fˣ, ∃ x' : Fˣ,
      ((MulAut.conj r)⁻¹ * α) (torus m x) = torus m x' := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow m hm
  obtain ⟨hSE, -, -, -⟩ := benderBorel_sylowCenter (bender_suzukiMatrixGroup_borel m hm) S
  have hHN : torusSub m ≤
      Subgroup.normalizer (((S : Subgroup (SuzukiMatrixGroup m))) : Set _) := by
    rw [hS]
    exact torusSub_le_normalizer m
  have hS₁ : weyl m • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer m
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : torusSub m ≤ Subgroup.normalizer
      ((((weyl m • S : Sylow 2 (SuzukiMatrixGroup m)) :
        Subgroup (SuzukiMatrixGroup m))) : Set _) := by
    intro h hh
    obtain ⟨x, rfl⟩ := (mem_torusSub m hm).mp hh
    rw [mem_normalizer_conj_smul_iff, weyl_inv_conj_torus]
    exact hHN (torus_mem m x⁻¹)
  rw [← hS] at hNR hcard hR
  have hαS : α • S = S := smul_eq_of_mapsTo hR
  obtain ⟨r, hr, hrS₁⟩ := exists_conj_adjust hSE hcard hS₁ α hαS
  set α' := (MulAut.conj r)⁻¹ * α with hα'
  have hα'S : α' • S = S := by
    rw [hα', mul_smul, hαS, inv_smul_eq_iff, conj_smul_self hr]
  have hrR : r ∈ rootSub m := by
    rwa [hS] at hr
  refine ⟨r, hrR, fun x => ?_⟩
  have h1 := mem_normalizer_smul (α := α') (hHN (torus_mem m x))
  have h2 := mem_normalizer_smul (α := α') (hHN₁ (torus_mem m x))
  rw [hα'S] at h1
  rw [hrS₁] at h2
  have hmem := mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
  obtain ⟨x', hx'⟩ := (mem_torusSub m hm).mp hmem
  exact ⟨x', by simpa [hα'] using hx'⟩

theorem torus_mem_rootSub_iff (hm : 0 < m) (x : Fˣ) :
    torus m x ∈ rootSub m ↔ x = 1 := by
  constructor
  · intro hx
    obtain ⟨a, b, hab⟩ := (mem_rootSub m).mp hx
    have h01 : a = 0 := by
      have h := congrArg (fun g : SuzukiMatrixGroup m =>
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1) hab
      simpa [torus, root, SuzukiRootGL, SuzukiTorusGL, SuzukiRootMatrix,
        SuzukiTorusMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero] using h.symm
    subst a
    have h02 : b = 0 := by
      have h := congrArg (fun g : SuzukiMatrixGroup m =>
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 2) hab
      simpa [torus, root, SuzukiRootGL, SuzukiTorusGL, SuzukiRootMatrix,
        SuzukiTorusMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero] using h.symm
    subst b
    have htorus : torus m x = 1 := by
      rw [hab, root_zero_zero]
    have h11 := congrArg (fun g : SuzukiMatrixGroup m =>
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1) htorus
    have h00 := congrArg (fun g : SuzukiMatrixGroup m =>
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) htorus
    have h11' : (x : F) ^ (2 ^ m) = 1 := by
      simpa [torus, SuzukiTorusGL, SuzukiTorusMatrix,
        Matrix.GeneralLinearGroup.mkOfDetNeZero] using h11
    have h00' : (x : F) ^ (1 + 2 ^ m) = 1 := by
      simpa [torus, SuzukiTorusGL, SuzukiTorusMatrix,
        Matrix.GeneralLinearGroup.mkOfDetNeZero] using h00
    have h00'' : (x : F) ^ (2 ^ m + 1) = 1 := by
      simpa [Nat.add_comm] using h00'
    have hxx : (x : F) ^ (2 ^ m) * (x : F) = 1 := by
      rw [← pow_succ]
      exact h00''
    apply Units.ext
    simpa [h11'] using hxx
  · rintro rfl
    rw [torus_one m]
    exact (rootSub m).one_mem

private theorem pow_eq_one_step (α : MulAut (SuzukiMatrixGroup m)) (τ : F ≃+* F)
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m)
    (hτ : ∀ x : Fˣ,
      (torus m (Units.map (τ : F →* F) x))⁻¹ * α (torus m x) ∈ rootSub m)
    (k : ℕ) (x : Fˣ)
    (ih : (torus m (Units.map ((τ ^ k : F ≃+* F) : F →* F) x))⁻¹ *
      (α ^ k) (torus m x) ∈ rootSub m) :
    (torus m (Units.map ((τ ^ (k + 1) : F ≃+* F) : F →* F) x))⁻¹ *
      (α ^ (k + 1)) (torus m x) ∈ rootSub m := by
  let σ : F ≃+* F := τ ^ k
  let β : MulAut (SuzukiMatrixGroup m) := α ^ k
  let A : SuzukiMatrixGroup m := torus m (Units.map (σ : F →* F) x)
  let s : SuzukiMatrixGroup m := A⁻¹ * β (torus m x)
  let B : SuzukiMatrixGroup m := torus m (Units.map (τ : F →* F)
    (Units.map (σ : F →* F) x))
  let r : SuzukiMatrixGroup m := B⁻¹ * α A
  have hs : s ∈ rootSub m := ih
  have hr : r ∈ rootSub m := hτ (Units.map (σ : F →* F) x)
  have hβ : β (torus m x) = A * s := by
    change (α ^ k) (torus m x) =
      torus m (Units.map (σ : F →* F) x) *
        ((torus m (Units.map (σ : F →* F) x))⁻¹ * (α ^ k) (torus m x))
    group
  have hαA : α A = B * r := by
    change α (torus m (Units.map (σ : F →* F) x)) =
      torus m (Units.map (τ : F →* F) (Units.map (σ : F →* F) x)) *
        ((torus m (Units.map (τ : F →* F) (Units.map (σ : F →* F) x)))⁻¹ *
          α (torus m (Units.map (σ : F →* F) x)))
    group
  have hσ : Units.map ((τ ^ (k + 1) : F ≃+* F) : F →* F) x =
      Units.map (τ : F →* F) (Units.map (σ : F →* F) x) :=
    units_map_pow_succ m τ k x
  have hEq : (torus m (Units.map ((τ ^ (k + 1) : F ≃+* F) : F →* F) x))⁻¹ *
      (α ^ (k + 1)) (torus m x) = r * α s := by
    rw [hσ, pow_succ', MulAut.mul_apply, hβ, map_mul, hαA]
    dsimp only [B]
    group
  rw [hEq]
  exact (rootSub m).mul_mem hr (hR s hs)

private theorem pow_eq_one_key (α : MulAut (SuzukiMatrixGroup m)) (τ : F ≃+* F)
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m)
    (hτ : ∀ x : Fˣ,
      (torus m (Units.map (τ : F →* F) x))⁻¹ * α (torus m x) ∈ rootSub m) :
    ∀ k : ℕ, ∀ x : Fˣ,
      (torus m (Units.map ((τ ^ k : F ≃+* F) : F →* F) x))⁻¹ *
        (α ^ k) (torus m x) ∈ rootSub m := by
  intro k
  induction k with
  | zero =>
    intro x
    have hτ0 : Units.map ((τ ^ 0 : F ≃+* F) : F →* F) x = x := by
      rw [pow_zero]
      ext
      rfl
    rw [hτ0, pow_zero]
    simpa using (rootSub m).one_mem
  | succ k ih =>
    intro x
    exact pow_eq_one_step m α τ hR hτ k x (ih x)

theorem pow_eq_one_of_mul_torus_mem (hm : 0 < m) (α : MulAut (SuzukiMatrixGroup m))
    (τ : F ≃+* F) (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m)
    (hτ : ∀ x : Fˣ,
      (torus m (Units.map (τ : F →* F) x))⁻¹ * α (torus m x) ∈ rootSub m)
    {n : ℕ} (hn : α ^ n = 1) : τ ^ n = 1 := by
  classical
  have key := pow_eq_one_key m α τ hR hτ
  apply RingEquiv.ext
  intro b
  by_cases hb : b = 0
  · simp [hb]
  · let x : Fˣ := Units.mk0 b hb
    let u : Fˣ := Units.map ((τ ^ n : F ≃+* F) : F →* F) x
    have hkey := key n x
    rw [hn] at hkey
    have hmem : torus m (u⁻¹ * x) ∈ rootSub m := by
      rw [← torus_mul m u⁻¹ x, ← torus_inv m u]
      simpa using hkey
    have hunit : u⁻¹ * x = 1 := (torus_mem_rootSub_iff m hm _).mp hmem
    have hxu : u = x := inv_mul_eq_one.mp hunit
    have hval := congrArg Units.val hxu
    simpa [u, x] using hval

end

end CFSG.RankThree.PartTwo.KFacts
