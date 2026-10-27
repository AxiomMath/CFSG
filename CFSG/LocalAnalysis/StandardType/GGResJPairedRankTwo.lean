module

public import CFSG.LocalAnalysis.StandardType.GGResJPairedBlock
public import CFSG.LocalAnalysis.StandardType.GGResJPairedResidual
public import CFSG.LocalAnalysis.StandardType.GGResJLineBCGamma
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNs
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNsNorm
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus

public section

namespace CFSG.StandardType
namespace ResJPairedBlock
namespace ActualA
namespace RankTwo

open Matrix Polynomial CoordSL Multiplicative SpCoord CFSG.Assembly
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [Finite G]
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ} {Bs J : Subgroup G}
  {g : K[X]} [Fact (Irreducible g)]
  {r : ℕ} {ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin 2) ⊕ Fin r}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K}

theorem exact_automizer_of_frame_rankTwo
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K)
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range =
      (ggGamma J hN).range) :
    ∃ Θ : (Fin 2 → Multiplicative (ZMod 3)) ≃* ↥(ggGamma J hN).range,
      (∀ (m : ↥J) (hm : MulAut.conj m ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm
          (ggConjAut (ggGamma J hN).range hm))) ∧
      (∀ i : Fin 2, ∃ (m : ↥J) (hm : MulAut.conj m ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        ggConjAut (ggGamma J hN).range hm = MulAut.congr Θ (sgnAut i)) ∧
      (∀ σ : Equiv.Perm (Fin 2), ∃ (m : ↥J) (hm : MulAut.conj m ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        ggConjAut (ggGamma J hN).range hm = MulAut.congr Θ (permAut σ)) ∧
      Nat.card (ggAutomizer J Bs) = 8 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpK' : (3 : K) ≠ 0 := by
    intro h
    have h' : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at h'
  have hpKpos : 3 ∣ Nat.card K + 1 := three_dvd_card_add_one_exact (K := K) hpK
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot (g := g) Nat.prime_three hpK' hgd).pow_eq_one
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    isPerfect_SL_of_frame (ε' := ε) hgd hpK (hs := by norm_num)
  have hφc : ∀ x, φ x ∈ Subgroup.center ↥J →
      x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    intro x hx
    have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperf φ hφ hker
    rw [← hcomap]
    exact hx
  have hfinj : Function.Injective (CoordSL.frameHom (psi φ) A₀ ε hC hCp) :=
    frameHom_psi_injective (φ := φ) (hC := hC) (hCp := hCp)
      (hφ := hφ) (hker := hker) (hgd := hgd) (hpK := hpK) (hs := by norm_num)
  let F : (Fin 2 → Multiplicative (ZMod 3)) →* ↥A :=
    (CoordSL.frameHom (psi φ) A₀ ε hC hCp).codRestrict A (fun t => by
      have h : CoordSL.frameHom (psi φ) A₀ ε hC hCp t ∈
          (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := ⟨t, rfl⟩
      rw [hframeA] at h
      exact h)
  have hFbij : Function.Bijective F := by
    refine ⟨fun a b hab => hfinj (congrArg Subtype.val hab), fun a => ?_⟩
    have ha : (a : MulAut ↥J) ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
      rw [hframeA]
      exact a.2
    obtain ⟨t, ht⟩ := ha
    exact ⟨t, Subtype.ext ht⟩
  let Θ : (Fin 2 → Multiplicative (ZMod 3)) ≃* ↥A :=
    MulEquiv.ofBijective F hFbij
  let oa : (Fin 2 → ZMod 3) → (Fin 2 → Multiplicative (ZMod 3)) :=
    fun t i => ofAdd (t i)
  let T : (Fin 2 → ZMod 3) → Matrix.SpecialLinearGroup (Fin n) K :=
    fun t => SlNsRootGen.torusSL ε hC hCp (ofAdd t)
  let Y : (Fin 2 → ZMod 3) → Matrix.SpecialLinearGroup (Fin n) K :=
    fun t => A₀ * T t * A₀⁻¹
  have hpowT : ∀ t : Fin 2 → ZMod 3, (T t) ^ 3 = 1 := by
    intro t
    have h := SlNsRootGen.pow_torusSL (p := 3) (ε := ε) (hC := hC) (hCp := hCp)
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin n) K)) t
    simpa [T] using h
  have hconjY3 : ∀ t : Fin 2 → ZMod 3, (Y t) ^ 3 = 1 := by
    intro t
    dsimp [Y]
    rw [conj_pow, hpowT t, mul_one, mul_inv_cancel]
  have hF_apply : ∀ t : Fin 2 → ZMod 3,
      ((F (oa t) : ↥A) : MulAut ↥J) = MulAut.conj (φ (Y t)) := by
    intro t
    change CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t) = MulAut.conj (φ (Y t))
    rw [CoordSL.frameHom_apply, psi_apply]
    congr 1
    simp [Y, T, SlNsRootGen.torusSL_apply]
  have hact_val : ∀ (x : Matrix.SpecialLinearGroup (Fin n) K) (t t' : Fin 2 → ZMod 3),
      (A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹ = T t' →
      MulAut.conj (φ x) * ((F (oa t) : ↥A) : MulAut ↥J) *
        (MulAut.conj (φ x))⁻¹ = ((F (oa t') : ↥A) : MulAut ↥J) := by
    intro x t t' hT
    have hYeq : x * Y t * x⁻¹ = Y t' := by
      calc x * Y t * x⁻¹ =
          A₀ * ((A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹) * A₀⁻¹ := by
            change x * (A₀ * T t * A₀⁻¹) * x⁻¹ =
              A₀ * ((A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹) * A₀⁻¹
            group
        _ = A₀ * T t' * A₀⁻¹ := by rw [hT]
        _ = Y t' := by dsimp [Y]
    rw [hF_apply t, hF_apply t']
    calc MulAut.conj (φ x) * MulAut.conj (φ (Y t)) * (MulAut.conj (φ x))⁻¹
        = MulAut.conj (φ x * φ (Y t) * (φ x)⁻¹) := by
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = MulAut.conj (φ (x * Y t * x⁻¹)) := by
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = MulAut.conj (φ (Y t')) := by rw [hYeq]
  have hact : ∀ (x : Matrix.SpecialLinearGroup (Fin n) K) (t t' : Fin 2 → ZMod 3),
      (A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹ = T t' →
      ∀ (hm : MulAut.conj (φ x) ∈ Subgroup.normalizer (A : Set (MulAut ↥J))),
      ggConjAut A hm (Θ (oa t)) = Θ (oa t') := by
    intro x t t' hT hm
    apply Subtype.ext
    rw [ggConjAut_apply]
    change MulAut.conj (φ x) * ((F (oa t) : ↥A) : MulAut ↥J) *
      (MulAut.conj (φ x))⁻¹ = ((F (oa t') : ↥A) : MulAut ↥J)
    exact hact_val x t t' hT
  have hsurj_oa : ∀ a : ↥A, ∃ t : Fin 2 → ZMod 3, Θ (oa t) = a := by
    intro a
    obtain ⟨f, hf⟩ := Θ.surjective a
    refine ⟨fun i => toAdd (f i), ?_⟩
    have hf' : oa (fun i => toAdd (f i)) = f := by
      funext i
      rfl
    rw [hf']
    exact hf
  have haction : ∀ (x : Matrix.SpecialLinearGroup (Fin n) K)
      (s : MulAut (Fin 2 → Multiplicative (ZMod 3))),
      (∀ t : Fin 2 → ZMod 3,
        (A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹ =
          T (fun i => toAdd (s (oa t) i))) →
      ∀ t : Fin 2 → ZMod 3,
        MulAut.conj (φ x) * (Θ (oa t) : MulAut ↥J) * (MulAut.conj (φ x))⁻¹ =
          Θ (s (oa t)) := by
    intro x s hval t
    have h := hact_val x t (fun i => toAdd (s (oa t) i)) (hval t)
    have hX : oa (fun i => toAdd (s (oa t) i)) = s (oa t) := by
      funext i
      rfl
    rw [hX] at h
    exact h
  have hnormalizer : ∀ (x : Matrix.SpecialLinearGroup (Fin n) K)
      (s : MulAut (Fin 2 → Multiplicative (ZMod 3))),
      (∀ t : Fin 2 → ZMod 3,
        (A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹ =
          T (fun i => toAdd (s (oa t) i))) →
      (∀ t : Fin 2 → ZMod 3,
        (A₀⁻¹ * x⁻¹ * A₀) * T t * (A₀⁻¹ * x⁻¹ * A₀)⁻¹ =
          T (fun i => toAdd (s (oa t) i))) →
      MulAut.conj (φ x) ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) := by
    intro x s hval hval_inv
    have hpos : ∀ a ∈ A, MulAut.conj (φ x) * a * (MulAut.conj (φ x))⁻¹ ∈ A := by
      intro a ha
      obtain ⟨t, ht⟩ := hsurj_oa ⟨a, ha⟩
      have htval : ((Θ (oa t) : ↥A) : MulAut ↥J) = a := congrArg Subtype.val ht
      rw [← htval, haction x s hval t]
      exact (Θ (s (oa t))).2
    have hinv : ∀ a ∈ A, (MulAut.conj (φ x))⁻¹ * a * MulAut.conj (φ x) ∈ A := by
      intro a ha
      obtain ⟨t, ht⟩ := hsurj_oa ⟨a, ha⟩
      have htval : ((Θ (oa t) : ↥A) : MulAut ↥J) = a := congrArg Subtype.val ht
      have h1 : (MulAut.conj (φ x))⁻¹ = MulAut.conj (φ x⁻¹) := by
        ext y
        simp [MulAut.conj_apply]
      have h2 : (MulAut.conj (φ x⁻¹))⁻¹ = MulAut.conj (φ x) := by
        rw [← map_inv]
        simp
      rw [← htval, h1, ← h2, haction x⁻¹ s hval_inv t]
      exact (Θ (s (oa t))).2
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hpos a
    · intro ha
      have h1 := hinv (MulAut.conj (φ x) * a * (MulAut.conj (φ x))⁻¹) ha
      simpa [mul_assoc] using h1
  have hsp : ∀ (m : ↥J) (hm : MulAut.conj m ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))),
      SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hm)) := by
    intro m hm
    obtain ⟨x, rfl⟩ := hφ m
    let y : Matrix.SpecialLinearGroup (Fin n) K := A₀⁻¹ * x * A₀
    have hx : ∀ t : Fin 2 → ZMod 3, ∃ t', y * T t * y⁻¹ = T t' := by
      intro t
      have hmemFrame : MulAut.conj (φ (Y t)) ∈
          (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
        refine ⟨ofAdd t, ?_⟩
        simp [Y, T, CoordSL.frameHom_apply, psi_apply, SlNsRootGen.torusSL_apply]
      have hmemA : MulAut.conj (φ (Y t)) ∈ A := by
        rw [show A = (ggGamma J hN).range from rfl, ← hframeA]
        exact hmemFrame
      have hconjmem : MulAut.conj (φ x) * MulAut.conj (φ (Y t)) *
          (MulAut.conj (φ x))⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hm (MulAut.conj (φ (Y t)))).mp hmemA
      have hpre : MulAut.conj (φ x) * MulAut.conj (φ (Y t)) *
          (MulAut.conj (φ x))⁻¹ ∈
          (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
        rw [hframeA]
        exact hconjmem
      obtain ⟨tm, htm⟩ := hpre
      let t' : Fin 2 → ZMod 3 := toAdd tm
      have ht' : CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t') =
          MulAut.conj (φ x) * MulAut.conj (φ (Y t)) * (MulAut.conj (φ x))⁻¹ := by
        simpa [t'] using htm
      have hconjphi : MulAut.conj (φ (x * Y t * x⁻¹)) =
          MulAut.conj (φ (Y t')) := by
        have hL : CoordSL.frameHom (psi φ) A₀ ε hC hCp (ofAdd t') =
            MulAut.conj (φ (Y t')) := by
          simp [Y, T, CoordSL.frameHom_apply, psi_apply, SlNsRootGen.torusSL_apply]
        have hR : (MulAut.conj (φ x) * MulAut.conj (φ (Y t)) *
            (MulAut.conj (φ x))⁻¹) = MulAut.conj (φ (x * Y t * x⁻¹)) := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rw [← map_mul, ← map_inv, ← map_mul]
        rw [hL] at ht'
        rw [hR] at ht'
        exact ht'.symm
      have ha3 : (x * Y t * x⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hconjY3 t, mul_one, mul_inv_cancel]
      have hb3 : (Y t') ^ 3 = 1 := hconjY3 t'
      have hYeq : x * Y t * x⁻¹ = Y t' :=
        eq_of_conj_phi_eq (φ := φ) hφc hpK ha3 hb3 hconjphi
      refine ⟨t', ?_⟩
      have hYeq' : A₀ * (y * T t * y⁻¹) * A₀⁻¹ = Y t' := by
        calc A₀ * (y * T t * y⁻¹) * A₀⁻¹ = x * Y t * x⁻¹ := by dsimp [y, Y]; group
          _ = Y t' := hYeq
      calc y * T t * y⁻¹ = A₀⁻¹ * (A₀ * (y * T t * y⁻¹) * A₀⁻¹) * A₀ := by group
        _ = A₀⁻¹ * Y t' * A₀ := by rw [hYeq']
        _ = T t' := by dsimp [Y]; group
    let α : MulAut (Fin 2 → Multiplicative (ZMod 3)) :=
      (MulAut.congr Θ).symm (ggConjAut A hm)
    obtain ⟨π, σ, hσ, hrel⟩ :=
      SlNsRootGen.exists_signedPerm_of_conj (p := 3) hpKpos hgd ε hC hCp y hx
    refine ⟨π, σ, hσ, fun f i => ?_⟩
    let t : Fin 2 → ZMod 3 := fun i => toAdd (f i)
    let t' : Fin 2 → ZMod 3 := Classical.choose (hx t)
    have ht' : y * T t * y⁻¹ = T t' := Classical.choose_spec (hx t)
    have hact' : ggConjAut A hm (Θ (oa t)) = Θ (oa t') := hact x t t' ht' hm
    have hα : α (oa t) = oa t' := by
      apply Θ.injective
      have h1 : Θ (α (oa t)) = ggConjAut A hm (Θ (oa t)) := by
        simp [α]
      exact h1.trans hact'
    have hf : f = oa t := by
      funext i
      rfl
    have hα' : ∀ i, α (oa t) i = oa t' i := fun i => congrFun hα i
    have hrel' := hrel t t' ht' i
    change toAdd (α f (π i)) = σ i * toAdd (f i)
    calc toAdd (α f (π i))
        = toAdd (α (oa t) (π i)) := by rw [hf]
      _ = toAdd (oa t' (π i)) := by rw [hα' (π i)]
      _ = t' (π i) := by
            change toAdd (ofAdd (t' (π i))) = t' (π i)
            exact toAdd_ofAdd (t' (π i))
      _ = σ i * toAdd (f i) := by simpa [t] using hrel'
  have hsgn : ∀ i : Fin 2, ∃ (m : ↥J) (hm : MulAut.conj m ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))),
      ggConjAut A hm = MulAut.congr Θ (sgnAut i) := by
    intro i
    obtain ⟨w, _hw, hwconj⟩ :=
      SlNsRootGen.exists_neg_mem_zeroBlock (p := 3) (ε := ε) hC hCp hζ hpKpos i
    let x : Matrix.SpecialLinearGroup (Fin n) K := A₀ * w * A₀⁻¹
    have hxval : A₀⁻¹ * x * A₀ = w := by dsimp [x]; group
    have hxval_inv : A₀⁻¹ * x⁻¹ * A₀ = w⁻¹ := by dsimp [x]; group
    have hsgn_ofAdd : ∀ t : Fin 2 → ZMod 3,
        (fun j => toAdd (sgnAut i (oa t) j)) = SlNsRootGen.negMap i t := by
      intro t
      funext k
      by_cases hk : k = i
      · subst hk
        simp [oa, sgnAut_apply, SlNsRootGen.negMap]
      · simp [oa, sgnAut_apply, SlNsRootGen.negMap, Function.update_of_ne hk]
    have hval : ∀ t : Fin 2 → ZMod 3,
        (A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹ =
          T (fun j => toAdd (sgnAut i (oa t) j)) := by
      intro t
      rw [hxval, hsgn_ofAdd]
      exact hwconj t
    have hval_inv : ∀ t : Fin 2 → ZMod 3,
        (A₀⁻¹ * x⁻¹ * A₀) * T t * (A₀⁻¹ * x⁻¹ * A₀)⁻¹ =
          T (fun j => toAdd (sgnAut i (oa t) j)) := by
      intro t
      rw [hxval_inv, hsgn_ofAdd]
      have h1 := hwconj (SlNsRootGen.negMap i t)
      rw [SlNsRootGen.negMap_negMap] at h1
      have h2 : w⁻¹ * T t * w = T (SlNsRootGen.negMap i t) := by
        have h3 := congrArg (fun z => w⁻¹ * z * w) h1
        simpa [mul_assoc] using h3.symm
      simpa [inv_inv] using h2
    have hm : MulAut.conj (φ x) ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) :=
      hnormalizer x (sgnAut i) hval hval_inv
    refine ⟨φ x, hm, ?_⟩
    apply MulEquiv.ext
    intro a
    obtain ⟨t, ht⟩ := hsurj_oa a
    rw [← ht]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [ggConjAut_apply]
    exact haction x (sgnAut i) hval t
  have hperm : ∀ σ : Equiv.Perm (Fin 2), ∃ (m : ↥J) (hm : MulAut.conj m ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))),
      ggConjAut A hm = MulAut.congr Θ (permAut σ) := by
    intro σ
    have hcases : σ = 1 ∨ σ = Equiv.swap (0 : Fin 2) 1 := by
      revert σ
      decide
    rcases hcases with rfl | rfl
    · refine ⟨1, ?_, ?_⟩
      · have h1 : MulAut.conj (1 : ↥J) = 1 := map_one _
        rw [h1]
        exact Subgroup.one_mem _
      · apply MulEquiv.ext
        intro a
        obtain ⟨t, ht⟩ := hsurj_oa a
        rw [← ht]
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        apply Subtype.ext
        rw [ggConjAut_apply]
        simp [permAut]
    · obtain ⟨w, _hw, hwconj⟩ :=
        SlNsRootGen.exists_swap_mem_pairBlock (p := 3) (ε := ε) hC hCp
          (0 : Fin 2) (1 : Fin 2)
      let x : Matrix.SpecialLinearGroup (Fin n) K := A₀ * w * A₀⁻¹
      have hxval : A₀⁻¹ * x * A₀ = w := by dsimp [x]; group
      have hxval_inv : A₀⁻¹ * x⁻¹ * A₀ = w⁻¹ := by dsimp [x]; group
      have hswap_ofAdd : ∀ t : Fin 2 → ZMod 3,
          (fun j => toAdd (permAut (Equiv.swap (0 : Fin 2) 1) (oa t) j)) =
            SlNsRootGen.swapMap (0 : Fin 2) 1 t := by
        intro t
        funext k
        simp [oa, SpCoord.permAut_apply, SlNsRootGen.swapMap, Equiv.swap_inv]
      have hval : ∀ t : Fin 2 → ZMod 3,
          (A₀⁻¹ * x * A₀) * T t * (A₀⁻¹ * x * A₀)⁻¹ =
            T (fun j => toAdd (permAut (Equiv.swap (0 : Fin 2) 1) (oa t) j)) := by
        intro t
        rw [hxval, hswap_ofAdd]
        exact hwconj t
      have hval_inv : ∀ t : Fin 2 → ZMod 3,
          (A₀⁻¹ * x⁻¹ * A₀) * T t * (A₀⁻¹ * x⁻¹ * A₀)⁻¹ =
            T (fun j => toAdd (permAut (Equiv.swap (0 : Fin 2) 1) (oa t) j)) := by
        intro t
        rw [hxval_inv, hswap_ofAdd]
        have h1 := hwconj (SlNsRootGen.swapMap (0 : Fin 2) 1 t)
        rw [SlNsRootGen.swapMap_swapMap] at h1
        have h2 : w⁻¹ * T t * w = T (SlNsRootGen.swapMap (0 : Fin 2) 1 t) := by
          have h3 := congrArg (fun z => w⁻¹ * z * w) h1
          simpa [mul_assoc] using h3.symm
        simpa [inv_inv] using h2
      have hm : MulAut.conj (φ x) ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) :=
        hnormalizer x (permAut (Equiv.swap (0 : Fin 2) 1)) hval hval_inv
      refine ⟨φ x, hm, ?_⟩
      apply MulEquiv.ext
      intro a
      obtain ⟨t, ht⟩ := hsurj_oa a
      rw [← ht]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact haction x (permAut (Equiv.swap (0 : Fin 2) 1)) hval t
  let W := ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A
  have hcardW : Nat.card W = 2 ^ 2 * Nat.factorial 2 :=
    SignedPermCount.ggAutomizer_card_eq_signed_of_model (p := 3) (k := 2)
      Nat.prime_three (by norm_num) (L' := ↥J) (A := A) Θ hsp hsgn hperm
  have hcardW8 : Nat.card W = 8 := by
    rw [hcardW]
    norm_num
  have hW : ∀ n : ↥J, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) →
      GGTorusWeylElt 3 A n := by
    intro n hn
    exact ggTorusWeylElt_of_conj_mem_normalizer
      (isElemAbelian_gammaRange (hN := hN) (φ := φ) (hC := hC) (hCp := hCp) hframeA)
      (fun a ha => exists_conj_of_mem_gammaRange (hN := hN) (φ := φ)
        (hC := hC) (hCp := hCp) hframeA ha)
      (fun x y hx hy => comm_of_conj_mem_gammaRange (hN := hN) (φ := φ)
        (hC := hC) (hCp := hCp) hframeA hx hy) hn
  have hWset : (W : Set (MulAut ↥A)) = ggTorusWeylAut 3 A :=
    weylAut_eq_automizer_of_weyl (A := A) hW
  let f := ggAutomizerGammaHom hN
  have hfinjGamma : Function.Injective f :=
    ggAutomizerGammaHom_injective (p := 3) Nat.prime_three hBs hNoTr hN hZ
  have hrange := ggAutomizerGammaHom_range (p := 3) hBs hSC hN
  have hsurj : Function.Surjective f := by
    intro w
    have hw : (w : MulAut ↥A) ∈ ggTorusWeylAut 3 A := by
      rw [← hWset]
      exact w.2
    have hmem : (w : MulAut ↥A) ∈ (f.range.map W.subtype : Set (MulAut ↥A)) := by
      rw [hrange]
      exact hw
    obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hc
    exact ⟨d, by rw [hd, Subtype.ext hcw]⟩
  have hcardOrig : Nat.card (ggAutomizer J Bs) = Nat.card W :=
    Nat.card_congr (Equiv.ofBijective f ⟨hfinjGamma, hsurj⟩)
  exact ⟨Θ, hsp, hsgn, hperm, hcardOrig.trans hcardW8⟩


theorem actual_exact_automizer_of_boundary_frame
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hJperf : commutator ↥J = ⊤)
    {g : K[X]} [Fact (Irreducible g)]
    (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K)
    (hCardA : 9 ≤ Nat.card (ggGamma J hN).range)
    (hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ x : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ x) = φ (CatalogueBHigherLinearAction.slConjugation n K Y x)) :
    ∃ (s r : ℕ) (ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin n) K),
      2 ≤ s ∧
      (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range = (ggGamma J hN).range ∧
      r ≤ 1 ∧
      ∃ (Θ : (Fin s → Multiplicative (ZMod 3)) ≃* ↥(ggGamma J hN).range),
        (∀ (m : ↥J) (hm : MulAut.conj m ∈
            Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
          SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm
            (ggConjAut (ggGamma J hN).range hm))) ∧
        (∀ i : Fin s, ∃ (m : ↥J) (hm : MulAut.conj m ∈
            Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
          ggConjAut (ggGamma J hN).range hm = MulAut.congr Θ (sgnAut i)) ∧
        (∀ σ : Equiv.Perm (Fin s), ∃ (m : ↥J) (hm : MulAut.conj m ∈
            Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
          ggConjAut (ggGamma J hN).range hm = MulAut.congr Θ (permAut σ)) ∧
        Nat.card (ggAutomizer J Bs) = 2 ^ s * s.factorial := by
  classical
  obtain ⟨s, r, ε, A₀, hs2, hframeA⟩ :=
    exists_frame_range_eq_gamma (hN := hN) (hBs := hBs) (hSC := hSC)
      (φ := φ) (hφ := hφ) (hker := hker) (hCardA := hCardA)
      (hY := hY) (hn3 := hn3) (hpK := hpK) (hC := hC) (hCp := hCp) (hgd := hgd)
  have hr1 : r ≤ 1 :=
    residual_le_one (hN := hN) (hSC := hSC) (hn3 := hn3) (φ := φ)
      (hφ := hφ) (hker := hker) (hpK := hpK) (hC := hC) (hCp := hCp)
      (hgd := hgd) (hframeA := hframeA)
  rcases Nat.lt_or_ge s 3 with hslt | hs3
  · have hs : s = 2 := by omega
    subst s
    obtain ⟨Θ, hsp, hsgn, hperm, hcard⟩ :=
      exact_automizer_of_frame_rankTwo (hN := hN) (hBs := hBs) (hSC := hSC)
        (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
        (hpK := hpK) (hC := hC) (hCp := hCp) (hgd := hgd) (hframeA := hframeA)
    exact ⟨2, r, ε, A₀, by norm_num, hframeA, hr1, Θ, hsp, hsgn, hperm, by simpa using hcard⟩
  · obtain ⟨Θ, hsp, hsgn, hperm, hcard⟩ :=
      exact_automizer_of_frame (hN := hN) (hBs := hBs) (hSC := hSC)
        (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
        (hn3 := hn3) (hpK := hpK) (hJperf := hJperf) (hC := hC) (hCp := hCp)
        (hgd := hgd) (hframeA := hframeA) (hs3 := hs3)
    exact ⟨s, r, ε, A₀, hs2, hframeA, hr1, Θ, hsp, hsgn, hperm, hcard⟩

theorem actual_exact_automizer_of_boundary
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hn3 : 3 ≤ n) (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hJperf : commutator ↥J = ⊤)
    {g : K[X]} [Fact (Irreducible g)]
    (hC : (CoordSL.rootMat g).det = 1) (hCp : CoordSL.rootMat g ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K)
    (hCardA : 9 ≤ Nat.card (ggGamma J hN).range)
    (hY : ∀ a ∈ (ggGamma J hN).range, ∃ Y : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ x : Matrix.SpecialLinearGroup (Fin n) K,
        a (φ x) = φ (CatalogueBHigherLinearAction.slConjugation n K Y x)) :
    ∃ (s : ℕ) (Θ : (Fin s → Multiplicative (ZMod 3)) ≃* ↥(ggGamma J hN).range),
      (∀ (m : ↥J) (hm : MulAut.conj m ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm
          (ggConjAut (ggGamma J hN).range hm))) ∧
      (∀ i : Fin s, ∃ (m : ↥J) (hm : MulAut.conj m ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        ggConjAut (ggGamma J hN).range hm = MulAut.congr Θ (sgnAut i)) ∧
      (∀ σ : Equiv.Perm (Fin s), ∃ (m : ↥J) (hm : MulAut.conj m ∈
          Subgroup.normalizer ((ggGamma J hN).range : Set (MulAut ↥J))),
        ggConjAut (ggGamma J hN).range hm = MulAut.congr Θ (permAut σ)) ∧
      Nat.card (ggAutomizer J Bs) = 2 ^ s * s.factorial := by
  obtain ⟨s, r, ε, A₀, hs2, hframeA, hr1, Θ, hsp, hsgn, hperm, hcard⟩ :=
    actual_exact_automizer_of_boundary_frame (hN := hN) (hBs := hBs) (hSC := hSC)
      (hNoTr := hNoTr) (hZ := hZ) (φ := φ) (hφ := hφ) (hker := hker)
      (hn3 := hn3) (hpK := hpK) (hJperf := hJperf) (hC := hC) (hCp := hCp)
      (hgd := hgd) (hCardA := hCardA) (hY := hY)
  exact ⟨s, Θ, hsp, hsgn, hperm, hcard⟩


end RankTwo

section OppositeLinearBC

open Matrix Polynomial CoordSL Multiplicative SpCoord CFSG.Assembly
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem _root_.CFSG.StandardType.GGResHyp.exists_lineJLabel_of_B3C3_oppositeLinear
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel T lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, _, hP₀⟩ := hQ₀
  have htag : tag = .A := hP₀.1.1
  have h3n : 3 ∣ 2 ^ n + 1 := hP₀.1.2
  subst htag
  have hHas : GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel)
      (J ⧸ Subgroup.center J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    intro R' _ I' F' hQ'
    obtain ⟨-, -, θ', -⟩ := hQ'
    exact ⟨θ'⟩
  have hEquot : ∃ E' : Subgroup (J ⧸ Subgroup.center J),
      IsElemAbelian 3 E' ∧ Nat.card E' = 27 := by
    obtain ⟨E, hE, hEelem, hEcard, hEbot⟩ := exists_coroot_subgroup_of_B3C3 hN hD hT
    have hEJ : E ≤ J := hE.trans inf_le_right
    let H : Subgroup ↥J := E.subgroupOf J
    let π : ↥J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
    have hker : H ⊓ Subgroup.center ↥J = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro z ⟨hzH, hzZ⟩
      have hzE : (z : G) ∈ E := hzH
      have hzC : (z : G) ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hzc := Subgroup.mem_center_iff.mp hzZ (⟨j, hj⟩ : ↥J)
        exact congrArg Subtype.val hzc
      have hmem : (z : G) ∈ E ⊓ Subgroup.centralizer (J : Set G) := ⟨hzE, hzC⟩
      rw [hEbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hinj_on : Set.InjOn π (H : Set ↥J) := by
      intro a ha b hb hab
      have hq : π a = π b := hab
      have hz : a / b ∈ Subgroup.center ↥J := (QuotientGroup.eq_iff_div_mem).mp hq
      have hzH : a / b ∈ H := H.div_mem ha hb
      have hz1 : a / b = 1 := by
        have hmem : a / b ∈ H ⊓ Subgroup.center ↥J := ⟨hzH, hz⟩
        rwa [hker, Subgroup.mem_bot] at hmem
      exact div_eq_one.mp hz1
    let E' : Subgroup (J ⧸ Subgroup.center J) := H.map π
    have hE'card : Nat.card E' = 27 := by
      have h1 : Nat.card E' = Nat.card H := by
        dsimp only [E']
        change Nat.card (π '' (H : Set ↥J)) = Nat.card H
        exact Nat.card_image_of_injOn hinj_on
      calc Nat.card E' = Nat.card H := h1
        _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
        _ = 27 := hEcard
    exact ⟨E', (hEelem.subgroupOf J).map π, hE'card⟩
  obtain ⟨E', hE'a, hE'card⟩ := hEquot
  haveI : Group.IsPerfect ↥J := ⟨hperfJ⟩
  have h3rank : 3 ≤ rank :=
    ggSmallThreeRank_linear_rank_three_of_elemAbelian (H := ↥J)
      (lab := (⟨.A, rank, n⟩ : LargeEvenLabel)) hΛ hHas hE'a
      (by simpa [hE'card]) (Or.inl rfl)
  have hrank5 : 5 ≤ rank := by
    by_contra h
    have hrankle : rank ≤ 4 := by omega
    have hpe : ∀ j, 0 < j →
        3 * j ≤ (if (⟨.A, rank, n⟩ : LargeEvenLabel).tag = .D then 4
          else (⟨.A, rank, n⟩ : LargeEvenLabel).rank + 1) →
        ¬ 3 ∣ (2 ^ (⟨.A, rank, n⟩ : LargeEvenLabel).n) ^ j - 1 := by
      intro j hj hdj
      have hdj' : 3 * j ≤ rank + 1 := by simpa using hdj
      have hj1 : j = 1 := by omega
      subst hj1
      have hsub : ¬ 3 ∣ 2 ^ n - 1 :=
        fun hdiv => not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hdiv h3n
      simpa using hsub
    have hall := largeEvenLabelAll_card_lt_linear_of_ord (p := 3) Nat.prime_three (by norm_num)
      (lab := (⟨.A, rank, n⟩ : LargeEvenLabel))
      (Or.inl ⟨rfl, le_trans (by norm_num : 2 ≤ 3) h3rank⟩) hpe
    exact not_ggHasLabel_of_elemAbelian_of_labelAll_bound
      (H := ↥J) (lab := (⟨.A, rank, n⟩ : LargeEvenLabel))
      hHas hall hE'a (by simpa [hE'card])
  have hMarkLab : GGInnerDiagOnLabel
      (fun _ l => l = (⟨.A, rank, n⟩ : LargeEvenLabel)) 3 Bs J := by
    refine ⟨hperfJ, ⟨.A, rank, n⟩, hΛ, ?_⟩
    refine largeEvenRawDatum_mono (lab := (⟨.A, rank, n⟩ : LargeEvenLabel))
      (fun R _ I F hQ => ?_) hraw
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    exact ⟨hs, hna, θ, ⟨rfl, hP.2.1, hP.2.2⟩⟩
  obtain ⟨F, hFfield, hFfinite, hFchar, hFcard, hFsign, φ, hφsurj, hkerφ, hYact, _hHas'⟩ :=
    CFSG.StandardType.ResJPairedBlock.ActualA.exists_actual_oppositeLinear_cover_of_marking
      (hH := hH) (hMark := hMarkLab) (h3f := h3n) (h5 := by omega)
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  let d : ℕ := rank + 1
  have hpK : ¬ 3 ∣ Nat.card F - 1 := hFsign
  have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 := by
    let E : Subgroup G := Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)
    have hEBs : E ≤ Bs := inf_le_left.trans inf_le_left
    have hEJ : E ≤ J := inf_le_left.trans inf_le_right
    have hcenter3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥J) :=
      not_three_dvd_center_J_of_pairedCover (J := J) (n := rank + 1) (K := F)
        φ hφsurj hkerφ (by omega) hpK
    let E' : Subgroup ↥J := E.subgroupOf J
    have hE'le : E' ≤ Subgroup.center ↥J := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
      have hxC : (x : G) ∈ Subgroup.centralizer (J : Set G) := (Subgroup.mem_inf.mp hxE).2
      exact Subgroup.mem_centralizer_iff.mp hxC (y : G) y.2
    have hE'card : Nat.card E' = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
    have hcarddvd : Nat.card E ∣ Nat.card (Subgroup.center ↥J) := by
      rw [← hE'card]
      exact Subgroup.card_dvd_of_le hE'le
    have hE3 : IsPGroup 3 E := (hH.1.2.1.2.1.mono hEBs).isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
    have hk0 : k = 0 := by
      by_contra hkne
      have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
      have h3dvdE : 3 ∣ Nat.card E := by
        rw [hk]
        exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hkpos)
      exact hcenter3 (h3dvdE.trans hcarddvd)
    have hEcard : Nat.card E = 1 := by
      rw [hk, hk0, pow_zero]
    change Nat.card E ≤ 3
    omega
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three F
  let : Fact (Irreducible g) := ⟨hg⟩
  have hpq : 3 ∣ Nat.card F + 1 := by rw [hFcard]; exact h3n
  have hp3 : ((3 : ℕ) : F) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  have hC : (CoordSL.rootMat g).det = 1 :=
    CoordSL.det_rootMat Nat.prime_three hpK hp3 hgd
  have hCp : (CoordSL.rootMat g) ^ 3 = 1 :=
    CoordSL.rootMat_pow_eq_one Nat.prime_three hp3 hgd
  have hCardA : 9 ≤ Nat.card (ggGamma J hN).range :=
    card_gamma_nine_of_GGResHyp hN hH
  have hY : ∀ a ∈ (ggGamma J hN).range,
      ∃ Y : Matrix.GeneralLinearGroup (Fin d) F,
        ∀ x : Matrix.SpecialLinearGroup (Fin d) F,
          a (φ x) = φ (CatalogueBHigherLinearAction.slConjugation d F Y x) := by
    rintro a ⟨b, rfl⟩
    obtain ⟨Y, hYb⟩ := hYact b
    refine ⟨Y, fun x => ?_⟩
    apply Subtype.ext
    change (b : G) * ((φ x : ↥J) : G) * (b : G)⁻¹ =
      ((φ (CatalogueBHigherLinearAction.slConjugation d F Y x) : ↥J) : G)
    exact hYb x
  obtain ⟨s, rr, ε, A₀, hs2, hframeA, hr1, Θ, hsp, hsgn, hperm, hcard⟩ :=
    RankTwo.actual_exact_automizer_of_boundary_frame
      (hN := hN) (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2)
      (hNoTr := hH.2.2.2.1) (hZ := hZ)
      (φ := φ) (hφ := hφsurj) (hker := hkerφ) (n := d)
      (hn3 := by omega) (hpK := hpK) (hJperf := hperfJ)
      (g := g) (hC := hC) (hCp := hCp) (hgd := hgd)
      (hCardA := hCardA) (hY := hY)
  have h48 : Nat.card (ggAutomizer J Bs) = 48 := by
    rcases hT with rfl | rfl
    · exact ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
    · exact ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
  have hs3 : s = 3 := by
    have hrank_of : ∀ k : ℕ, 2 ≤ k → 48 = 2 ^ k * k.factorial → k = 3 := by
      intro k hk h
      have hle3 : k ≤ 3 := by
        by_contra hle
        have h4 : 4 ≤ k := by omega
        have hpow : 16 ≤ 2 ^ k := by
          have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h4
          norm_num at this ⊢
          exact this
        have hfact : 24 ≤ k.factorial := by
          have := Nat.factorial_le h4
          norm_num at this ⊢
          exact this
        have : 384 ≤ 2 ^ k * k.factorial := Nat.mul_le_mul hpow hfact
        omega
      interval_cases k
      · norm_num at h
      · rfl
    exact hrank_of s hs2 (by rw [← hcard, h48])
  have hcardε : (CoordSL.rootPB g).dim * s + rr = rank + 1 := by
    have h := Fintype.card_congr ε
    dsimp [d] at h
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_sum] at h
    omega
  have hdim : (CoordSL.rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) hp3 hgd hpq
  have hrank56 : rank = 5 ∨ rank = 6 := by
    rw [hs3, hdim] at hcardε
    rcases Nat.eq_zero_or_pos rr with h0 | hpos
    · left; omega
    · right; omega
  refine ⟨(⟨.A, rank, n⟩ : LargeEvenLabel), hΛ, ?_, hHas⟩
  rcases hT with rfl | rfl <;>
    · unfold ggResLineJLabel
      exact Or.inr (Or.inl ⟨rfl, hrank56, h3n⟩)

end OppositeLinearBC

end ActualA
end ResJPairedBlock
end CFSG.StandardType

end
