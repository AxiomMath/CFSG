module

public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralLemmaI
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LinearAlgebra.CoprimeActions.PermutationFunctionFixedDimension
public import CFSG.LocalAnalysis.StandardType.GGLatPerpRefl
public import CFSG.LocalAnalysis.StandardType.GGLatPermExc
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTags
public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace StepTwoToralIndex

open GGStepTwoToralLemmaI
open CFSG.LinearAlgebra.CoprimeActions.PermutationFunctionFixedDimension (fixedSpace)

section Defs

variable {N : ℕ}

@[expose] def redModP (p : ℕ) (y : Fin N → ℤ) : Fin N → ZMod p := fun i => (y i : ZMod p)

@[expose] def rootAnnihilator (p : ℕ) (O : Set (Fin N → ℤ)) :
    Submodule (ZMod p) (Fin N → ZMod p) where
  carrier := {g | ∀ α ∈ O, latChar p g α = 0}
  add_mem' := fun {a b} ha hb α hα => by
    simp only [latChar, Pi.add_apply, mul_add, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha α hα, hb α hα, add_zero]
  zero_mem' := fun α _ => by simp [latChar]
  smul_mem' := fun c g hg α hα => by
    have h := hg α hα
    simp only [latChar, Pi.smul_apply, smul_eq_mul] at h ⊢
    rw [show (∑ i, (α i : ZMod p) * (c * g i)) = c * ∑ i, (α i : ZMod p) * g i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, h, mul_zero]

@[expose] def corootModP (p : ℕ) (cor : (Fin N → ℤ) → (Fin N → ℤ)) (O : Set (Fin N → ℤ)) :
    Submodule (ZMod p) (Fin N → ZMod p) :=
  Submodule.span (ZMod p) (redModP p '' (cor '' O))

theorem mem_rootAnnihilator {p : ℕ} {O : Set (Fin N → ℤ)} {g : Fin N → ZMod p} :
    g ∈ rootAnnihilator p O ↔ ∀ α ∈ O, latChar p g α = 0 := Iff.rfl

theorem redModP_zero (p : ℕ) : redModP p (0 : Fin N → ℤ) = 0 := by
  funext i; simp [redModP]

theorem redModP_add (p : ℕ) (x y : Fin N → ℤ) :
    redModP p (x + y) = redModP p x + redModP p y := by
  funext i; simp [redModP]

theorem redModP_neg (p : ℕ) (x : Fin N → ℤ) : redModP p (-x) = -redModP p x := by
  funext i; simp [redModP]

theorem redModP_sub (p : ℕ) (x y : Fin N → ℤ) :
    redModP p (x - y) = redModP p x - redModP p y := by
  funext i; simp [redModP]

theorem redModP_zsmul (p : ℕ) (c : ℤ) (x : Fin N → ℤ) :
    redModP p (c • x) = (c : ZMod p) • redModP p x := by
  funext i; simp [redModP]

theorem redModP_surjective (p : ℕ) : Function.Surjective (redModP (N := N) p) := by
  intro g
  exact ⟨fun i => (ZMod.intCast_surjective (g i)).choose,
    funext fun i => (ZMod.intCast_surjective (g i)).choose_spec⟩

theorem latChar_redModP (p : ℕ) (y α : Fin N → ℤ) :
    latChar p (redModP p y) α = ((∑ i, α i * y i : ℤ) : ZMod p) := by
  simp [latChar, redModP]

end Defs

section Abstract

variable {N p : ℕ}

theorem redModP_mem_corootModP {cor : (Fin N → ℤ) → (Fin N → ℤ)} {O : Set (Fin N → ℤ)}
    {x : Fin N → ℤ} (hx : x ∈ Submodule.span ℤ (cor '' O)) :
    redModP p x ∈ corootModP p cor O := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [redModP_zero]; exact (corootModP p cor O).zero_mem
  | add x y _ _ hx hy => rw [redModP_add]; exact (corootModP p cor O).add_mem hx hy
  | smul c x _ hx => rw [redModP_zsmul]; exact (corootModP p cor O).smul_mem _ hx

theorem exists_lift_of_mem_corootModP {cor : (Fin N → ℤ) → (Fin N → ℤ)} {O : Set (Fin N → ℤ)}
    {u : Fin N → ZMod p} (hu : u ∈ corootModP p cor O) :
    ∃ x ∈ Submodule.span ℤ (cor '' O), redModP p x = u := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨_, ⟨α, hα, rfl⟩, rfl⟩ := hu
    exact ⟨cor α, Submodule.subset_span ⟨α, hα, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, redModP_zero p⟩
  | add u v _ _ hu hv =>
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨x + y, Submodule.add_mem _ hx hy, redModP_add p x y⟩
  | smul c u _ hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨c', rfl⟩ := ZMod.intCast_surjective c
    exact ⟨c' • x, Submodule.smul_mem _ c' hx, redModP_zsmul p c' x⟩

open scoped Matrix in
theorem isCompl_and_saturated (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type*} [Group H] [Finite H] (hH : ¬ p ∣ Nat.card H)
    (act : H →* Matrix (Fin N) (Fin N) ℤ) (O : Set (Fin N → ℤ))
    (cor : (Fin N → ℤ) → (Fin N → ℤ)) (r : (Fin N → ℤ) → H)
    (hgen : Subgroup.closure (r '' O) = ⊤)
    (hr : ∀ α ∈ O, ∀ y, act (r α) *ᵥ y = y - (∑ i, α i * y i) • cor α)
    (h2 : ∀ α ∈ O, ∑ i, α i * cor α i = 2) :
    IsCompl (corootModP p cor O) (rootAnnihilator p O) ∧
      ∀ y : Fin N → ℤ, (p : ℤ) • y ∈ Submodule.span ℤ (cor '' O) →
        y ∈ Submodule.span ℤ (cor '' O) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype H := Fintype.ofFinite H
  set Λ : Submodule ℤ (Fin N → ℤ) := Submodule.span ℤ (cor '' O) with hΛ
  have hmemΛ : ∀ α ∈ O, cor α ∈ Λ := fun α hα => Submodule.subset_span ⟨α, hα, rfl⟩
  have hsub : ∀ (h : H) (y : Fin N → ℤ), y - act h *ᵥ y ∈ Λ := by
    intro h
    have hmem : h ∈ Subgroup.closure (r '' O) := by rw [hgen]; exact Subgroup.mem_top h
    induction hmem using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      intro y
      rw [hr α hα y, sub_sub_cancel]
      exact Λ.smul_mem _ (hmemΛ α hα)
    | one => intro y; simp
    | mul x y hx hy ihx ihy =>
      intro v
      have hw : v - act y *ᵥ v ∈ Λ := ihy v
      have hxw : act x *ᵥ (v - act y *ᵥ v) ∈ Λ := by
        have := Λ.sub_mem hw (ihx (v - act y *ᵥ v))
        simpa using this
      have e : v - act (x * y) *ᵥ v = (v - act x *ᵥ v) + act x *ᵥ (v - act y *ᵥ v) := by
        rw [map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]; abel
      rw [e]
      exact Λ.add_mem (ihx v) hxw
    | inv x hx ih =>
      intro v
      have e : act x *ᵥ (act x⁻¹ *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
      have := Λ.neg_mem (ih (act x⁻¹ *ᵥ v))
      rw [e] at this
      simpa using this
  have hsum : ∀ x ∈ Λ, ∑ h : H, act h *ᵥ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      have hrefl : act (r α) *ᵥ cor α = - cor α := by
        rw [hr α hα, h2 α hα]
        module
      have hre : ∑ h : H, act (h * r α) *ᵥ cor α = ∑ h : H, act h *ᵥ cor α :=
        Fintype.sum_equiv (Equiv.mulRight (r α)) _ _ (fun h => rfl)
      have key : ∑ h : H, act h *ᵥ cor α = - ∑ h : H, act h *ᵥ cor α := by
        calc ∑ h : H, act h *ᵥ cor α = ∑ h : H, act (h * r α) *ᵥ cor α := hre.symm
          _ = ∑ h : H, -(act h *ᵥ cor α) := by
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [map_mul, ← Matrix.mulVec_mulVec, hrefl, Matrix.mulVec_neg]
          _ = - ∑ h : H, act h *ᵥ cor α := Finset.sum_neg_distrib _
      funext i
      have h1 := congrFun key i
      rw [Pi.neg_apply] at h1
      have h0 : (∑ h : H, act h *ᵥ cor α) i = 0 := by omega
      simpa using h0
    | zero => simp
    | add x y _ _ hx hy => simp [Matrix.mulVec_add, Finset.sum_add_distrib, hx, hy]
    | smul c x _ hx =>
      simp only [Matrix.mulVec_smul]
      rw [← Finset.smul_sum, hx, smul_zero]
  have hsat : ∀ y : Fin N → ℤ, (p : ℤ) • y ∈ Λ → y ∈ Λ := by
    intro y hy
    letI inst : DistribMulAction H (Fin N → ℤ) :=
      { smul := fun h y => act h *ᵥ y
        one_smul := fun y => by
          show act 1 *ᵥ y = y
          rw [map_one, Matrix.one_mulVec]
        mul_smul := fun a b y => by
          show act (a * b) *ᵥ y = act a *ᵥ (act b *ᵥ y)
          rw [map_mul, ← Matrix.mulVec_mulVec]
        smul_zero := fun h => by
          show act h *ᵥ (0 : Fin N → ℤ) = 0
          rw [Matrix.mulVec_zero]
        smul_add := fun h x y => by
          show act h *ᵥ (x + y) = act h *ᵥ x + act h *ᵥ y
          rw [Matrix.mulVec_add] }
    have hcard : ¬ p ∣ Fintype.card H := by rwa [← Nat.card_eq_fintype_card]
    exact mem_of_smul_mem_of_coprime Λ.toAddSubgroup (fun h y => hsub h y) hsum hp hcard hy
  refine ⟨?_, hsat⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  let ρ : Representation (ZMod p) H (Fin N → ZMod p) :=
    (Matrix.toLinAlgEquiv' (R := ZMod p) (n := Fin N)).toMonoidHom.comp
      ((RingHom.mapMatrix (Int.castRingHom (ZMod p))).toMonoidHom.comp act)
  have hρ : ∀ (h : H) (y : Fin N → ℤ), ρ h (redModP p y) = redModP p (act h *ᵥ y) := by
    intro h y
    funext i
    have h1 := RingHom.map_mulVec (Int.castRingHom (ZMod p)) (act h) y i
    have h3 : ρ h (redModP p y) i = (((act h).map (Int.castRingHom (ZMod p))).mulVec
        ((Int.castRingHom (ZMod p)) ∘ y)) i := rfl
    rw [h3, ← h1]
    simp [redModP]
  have hcardp : ((Fintype.card H : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, ← Nat.card_eq_fintype_card]
    exact hH
  have hcompl := isCompl_span_sub_invariants ρ hcardp
  have hrefl : ∀ α ∈ O, act (r α) *ᵥ cor α = - cor α := fun α hα => by
    rw [hr α hα, h2 α hα]
    module
  have hspan : Submodule.span (ZMod p) {v | ∃ (h : H) (u : Fin N → ZMod p), v = u - ρ h u} =
      corootModP p cor O := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro v ⟨h, u, rfl⟩
      obtain ⟨y, rfl⟩ := redModP_surjective p u
      rw [hρ, ← redModP_sub]
      exact redModP_mem_corootModP (hsub h y)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
      have e : redModP p (cor α) =
          (2 : ZMod p)⁻¹ • (redModP p (cor α) - ρ (r α) (redModP p (cor α))) := by
        rw [hρ, hrefl α hα, redModP_neg, sub_neg_eq_add,
          ← two_smul (ZMod p) (redModP p (cor α)), smul_smul, inv_mul_cancel₀ h2ne, one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r α, redModP p (cor α), rfl⟩)
  have hform : ∀ α ∈ O, ∀ v : Fin N → ZMod p,
      ρ (r α) v = v - latChar p v α • redModP p (cor α) := by
    intro α hα v
    obtain ⟨y, rfl⟩ := redModP_surjective p v
    rw [hρ, hr α hα, redModP_sub, redModP_zsmul, latChar_redModP]
  have hchar : ∀ α ∈ O, latChar p (redModP p (cor α)) α = 2 := by
    intro α hα
    rw [latChar_redModP, h2 α hα]
    simp
  have hinv : ρ.invariants = rootAnnihilator p O := by
    ext v
    rw [Representation.mem_invariants, mem_rootAnnihilator]
    constructor
    · intro hv α hα
      have h1 := hv (r α)
      rw [hform α hα v, sub_eq_self] at h1
      have h3 := congrArg (fun g => latChar p g α) h1
      simp only [LatPerp.latChar_smul, hchar α hα] at h3
      have h4 : latChar p (0 : Fin N → ZMod p) α = 0 := by simp [latChar]
      rw [h4] at h3
      exact (mul_eq_zero.mp h3).resolve_right h2ne
    · intro hv h
      have hmem : h ∈ Subgroup.closure (r '' O) := by rw [hgen]; exact Subgroup.mem_top h
      induction hmem using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨α, hα, rfl⟩ := hx
        rw [hform α hα v, hv α hα, zero_smul, sub_zero]
      | one => simp
      | mul x y hx hy ihx ihy =>
        rw [map_mul, Module.End.mul_apply, ihy, ihx]
      | inv x hx ih =>
        have : ρ x⁻¹ (ρ x v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rwa [ih] at this
  rw [hspan, hinv] at hcompl
  exact hcompl

end Abstract

section Perm

variable {N p : ℕ}

@[expose] def permEndo (p : ℕ) (π : Equiv.Perm (Fin N)) :
    Module.End (ZMod p) (Fin N → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) π.symm

theorem permEndo_apply (π : Equiv.Perm (Fin N)) (g : Fin N → ZMod p) (i : Fin N) :
    permEndo p π g i = g (π.symm i) := rfl

theorem fixedSpace_eq_eigenspace [Fact p.Prime] (π : Equiv.Perm (Fin N)) :
    fixedSpace (ZMod p) π = Module.End.eigenspace (permEndo p π) 1 := by
  ext g
  rw [Module.End.mem_eigenspace_iff, one_smul]
  constructor
  · intro h
    funext i
    have := h (π.symm i)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro h i
    have := congrFun h (π i)
    rw [permEndo_apply, Equiv.symm_apply_apply] at this
    exact this.symm

theorem latChar_permEndo (π : Equiv.Perm (Fin N)) (g : Fin N → ZMod p) (α : Fin N → ℤ) :
    latChar p (permEndo p π g) α = latChar p g (latPerm π.symm α) := by
  simp only [latChar, permEndo_apply, latPerm, Equiv.symm_symm]
  rw [← Equiv.sum_comp π (fun i => (α i : ZMod p) * g (π.symm i))]
  simp

theorem latPerm_single (π : Equiv.Perm (Fin N)) (j : Fin N) :
    latPerm π (Pi.single j (1 : ℤ)) = Pi.single (π j) 1 := by
  funext i
  simp only [latPerm, Pi.single_apply]
  congr 1
  exact propext (by rw [Equiv.symm_apply_eq])

theorem latCorootZ_latPerm {S : Matrix (Fin N) (Fin N) ℤ} {π : Equiv.Perm (Fin N)}
    (hGram : ∀ α β, latGram S (latPerm π α) (latPerm π β) = latGram S α β)
    (α : Fin N → ℤ) :
    latCorootZ S (latPerm π α) = fun i => latCorootZ S α (π.symm i) := by
  funext i
  simp only [latCorootZ]
  have h1 : (Pi.single i (1 : ℤ) : Fin N → ℤ) = latPerm π (Pi.single (π.symm i) 1) := by
    rw [latPerm_single, Equiv.apply_symm_apply]
  rw [h1, hGram, hGram]

theorem latPerm_symm_mem {π : Equiv.Perm (Fin N)} {O : Set (Fin N → ℤ)} (hfin : O.Finite)
    (hπO : ∀ α ∈ O, latPerm π α ∈ O) : ∀ α ∈ O, latPerm π.symm α ∈ O := by
  have hinj : Function.Injective (latPerm π : (Fin N → ℤ) → (Fin N → ℤ)) := by
    intro a b h
    funext i
    have := congrFun h (π i)
    simpa [latPerm] using this
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (fun α hα => hπO α hα)).mp hinj.injOn
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := hbij.surjOn hα
  have : latPerm π.symm (latPerm π β) = β := by funext i; simp [latPerm]
  rw [this]
  exact hβ

open scoped Matrix in
theorem exists_complement_of_reflections [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Type*} [Group H] [Finite H] (hH : ¬ p ∣ Nat.card H)
    (act : H →* Matrix (Fin N) (Fin N) ℤ) (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (O : Set (Fin N → ℤ)) (r : (Fin N → ℤ) → H)
    (hgen : Subgroup.closure (r '' O) = ⊤)
    (hr : ∀ α ∈ O, ∀ y, act (r α) *ᵥ y = y - (∑ i, α i * y i) • latCorootZ S α)
    (h2 : ∀ α ∈ O, ∑ i, α i * latCorootZ S α i = 2)
    (hGram : ∀ α β, latGram S (latPerm π α) (latPerm π β) = latGram S α β)
    (hfin : O.Finite) (hπO : ∀ α ∈ O, latPerm π α ∈ O) :
    ∃ A : Submodule (ZMod p) (Fin N → ZMod p), A ≤ fixedSpace (ZMod p) π ∧
      (A : Set (Fin N → ZMod p)) ⊆ latEigenCoroot p S π O ∧ A ⊓ rootAnnihilator p O = ⊥ ∧
      Module.finrank (ZMod p) A +
        Module.finrank (ZMod p) ↥(fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) =
        Module.finrank (ZMod p) (fixedSpace (ZMod p) π) := by
  classical
  obtain ⟨hcompl, hsat⟩ :=
    isCompl_and_saturated Fact.out hp2 hH act O (latCorootZ S) r hgen hr h2
  set Λ : Submodule ℤ (Fin N → ℤ) := Submodule.span ℤ (latCorootZ S '' O) with hΛ
  have hπO' := latPerm_symm_mem hfin hπO
  have hcor := latCorootZ_latPerm hGram
  have hU : ∀ y ∈ corootModP p (latCorootZ S) O,
      permEndo p π y ∈ corootModP p (latCorootZ S) O := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨α, hα, rfl⟩, rfl⟩ := hy
      have e : permEndo p π (redModP p (latCorootZ S α)) =
          redModP p (latCorootZ S (latPerm π α)) := by
        funext i
        simp [permEndo_apply, redModP, hcor]
      rw [e]
      exact Submodule.subset_span ⟨_, ⟨latPerm π α, hπO α hα, rfl⟩, rfl⟩
    | zero => simpa using (corootModP p (latCorootZ S) O).zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact (corootModP p (latCorootZ S) O).add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact (corootModP p (latCorootZ S) O).smul_mem _ hx
  have hP : ∀ y ∈ rootAnnihilator p O, permEndo p π y ∈ rootAnnihilator p O := by
    intro y hy α hα
    rw [latChar_permEndo]
    exact hy _ (hπO' α hα)
  have hdec := eigenspace_eq_sup_inf (permEndo p π) 1 hcompl hU hP
  rw [← fixedSpace_eq_eigenspace] at hdec
  have hΛπ : ∀ y ∈ Λ, (fun i => y (π.symm i)) ∈ Λ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨α, hα, rfl⟩ := hy
      have e : (fun i => latCorootZ S α (π.symm i)) = latCorootZ S (latPerm π α) :=
        (hcor α).symm
      rw [e]
      exact Submodule.subset_span ⟨_, hπO α hα, rfl⟩
    | zero => exact Λ.zero_mem
    | add x y _ _ hx hy => exact Λ.add_mem hx hy
    | smul c x _ hx => exact Λ.smul_mem c hx
  refine ⟨fixedSpace (ZMod p) π ⊓ corootModP p (latCorootZ S) O, inf_le_left, ?_, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨hgV, hgU⟩ := hg
    obtain ⟨x, hxΛ, hxg⟩ := exists_lift_of_mem_corootModP hgU
    have hd : redModP p ((fun i => x (π.symm i)) - x) = 0 := by
      funext i
      simp only [redModP, Pi.sub_apply, Int.cast_sub, Pi.zero_apply]
      have hxi : (x i : ZMod p) = g i := congrFun hxg i
      have hxi' : (x (π.symm i) : ZMod p) = g (π.symm i) := congrFun hxg (π.symm i)
      rw [hxi, hxi', sub_eq_zero]
      have := hgV (π.symm i)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have hdiv : ∀ i, (p : ℤ) ∣ ((fun i => x (π.symm i)) - x) i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hd i)
    choose z hz using hdiv
    have hzd : (p : ℤ) • z = (fun i => x (π.symm i)) - x := funext fun i => (hz i).symm
    have hdΛ : (fun i => x (π.symm i)) - x ∈ Λ := Λ.sub_mem (hΛπ x hxΛ) hxΛ
    have hzΛ : z ∈ Λ := hsat z (by rw [hzd]; exact hdΛ)
    exact ⟨x, hxΛ, fun i => by rw [← hxg]; rfl, z, hzΛ, hzd.symm⟩
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : x ∈ corootModP p (latCorootZ S) O ⊓ rootAnnihilator p O := ⟨hx.1.2, hx.2⟩
    rwa [hcompl.inf_eq_bot] at hx'
  · have hdisj : (fixedSpace (ZMod p) π ⊓ corootModP p (latCorootZ S) O) ⊓
        (fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : x ∈ corootModP p (latCorootZ S) O ⊓ rootAnnihilator p O := ⟨hx.1.2, hx.2.2⟩
      rwa [hcompl.inf_eq_bot] at hx'
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (fixedSpace (ZMod p) π ⊓ corootModP p (latCorootZ S) O)
      (fixedSpace (ZMod p) π ⊓ rootAnnihilator p O)
    rw [hdisj, finrank_bot, ← hdec] at h1
    omega

end Perm

section Tag

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint

open scoped Matrix

@[expose] noncomputable def weylLatticeMat (τ : Tag) :
    WeylGroup τ →* Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  (LinearMap.toMatrixAlgEquiv' (R := ℤ) (n := Fin τ.rank)).toMonoidHom.comp
    (weylAction (isFiniteType_cartan τ))

theorem weylLatticeMat_apply {τ : Tag} (w : WeylGroup τ) (k m : Fin τ.rank) :
    weylLatticeMat τ w k m = (w • (Pi.single m 1 : Fin τ.rank → ℤ)) k := by
  show LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan τ) w) k m = _
  rw [LinearMap.toMatrixAlgEquiv'_apply]
  rfl

@[expose] noncomputable def weylCoactMat (τ : Tag) :
    WeylGroup τ →* Matrix (Fin τ.rank) (Fin τ.rank) ℤ where
  toFun w := (weylLatticeMat τ w⁻¹)ᵀ
  map_one' := by simp
  map_mul' a b := by simp [mul_inv_rev, Matrix.transpose_mul]

section Cert


theorem weylCoactMat_rootReflection {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (y : Fin τ.rank → ℤ) :
    weylCoactMat τ (rootReflection α) *ᵥ y =
      y - (∑ i, α i * y i) • fun m => corootPair α (Pi.single m 1 : Fin τ.rank → ℤ) := by
  funext m
  have h1 : ∀ k, weylLatticeMat τ (rootReflection α) k m =
      (Pi.single m 1 : Fin τ.rank → ℤ) k - corootPair α (Pi.single m 1) * α k := by
    intro k
    rw [weylLatticeMat_apply, rootReflection_smul hα]
    simp
  have hmul : (weylCoactMat τ (rootReflection α) *ᵥ y) m =
      ∑ k, weylLatticeMat τ (rootReflection α) k m * y k := by
    simp [weylCoactMat, rootReflection_inv hα, Matrix.mulVec, dotProduct]
  rw [hmul]
  simp only [h1, sub_mul, Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : ∑ k, (Pi.single m 1 : Fin τ.rank → ℤ) k * y k = y m := by
    simp [Pi.single_apply]
  rw [h2, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_mul_corootPair_single {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∑ i, α i * corootPair α (Pi.single i 1 : Fin τ.rank → ℤ) = 2 := by
  have hpos := iform_self_pos_of_isRoot hα
  have hα' : α = ∑ i, α i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : iform α α = ∑ i, α i * iform α (Pi.single i 1) := by
    calc iform α α = iform α (∑ i, α i • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
          congrArg (iform α) hα'
      _ = ∑ i, α i * iform α (Pi.single i 1) := by
          rw [iform_finset_sum_right]
          exact Finset.sum_congr rfl fun i _ => iform_smul_right _ _ _
  have h : (∑ i, α i * corootPair α (Pi.single i 1 : Fin τ.rank → ℤ)) * iform α α =
      2 * iform α α := by
    rw [Finset.sum_mul]
    calc ∑ i, α i * corootPair α (Pi.single i 1 : Fin τ.rank → ℤ) * iform α α
        = ∑ i, α i * (corootPair α (Pi.single i 1 : Fin τ.rank → ℤ) * iform α α) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, α i * (2 * iform α (Pi.single i 1)) :=
          Finset.sum_congr rfl fun i _ => by rw [corootPair_mul hα]
      _ = 2 * iform α α := by
          rw [hsum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  exact mul_right_cancel₀ hpos.ne' h

end Cert

theorem latGram_smul_symmetrizedCartan (τ : Tag) (k : ℤ) (x y : Fin τ.rank → ℤ) :
    latGram (k • τ.symmetrizedCartan) x y = k * iform x y := by
  simp only [latGram, iform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latCorootZ_smul_symmetrizedCartan
    (τ : Tag) {k : ℤ} (hk : 0 < k)
    (α : Fin τ.rank → ℤ) :
    latCorootZ (k • τ.symmetrizedCartan) α = fun m => corootPair α (Pi.single m 1) := by
  funext m
  simp only [latCorootZ, corootPair, latGram_smul_symmetrizedCartan,
    iform_comm (Pi.single m 1) α]
  rw [show 2 * (k * iform α (Pi.single m 1)) = k * (2 * iform α (Pi.single m 1)) by ring]
  exact Int.mul_ediv_mul_of_pos _ _ hk

end Tag

section TagLemma

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint

open scoped Matrix


theorem exists_complement_tag (τ : Tag) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) {k : ℤ} (hk : 0 < k) (π : Equiv.Perm (Fin τ.rank))
    (hGram : ∀ α β, latGram (k • τ.symmetrizedCartan) (latPerm π α) (latPerm π β) =
      latGram (k • τ.symmetrizedCartan) α β)
    (O : Set (Fin τ.rank → ℤ)) (hO : ∀ α ∈ O, IsRoot τ α)
    (hπO : ∀ α ∈ O, latPerm π α ∈ O) :
    ∃ A : Submodule (ZMod p) (Fin τ.rank → ZMod p), A ≤ fixedSpace (ZMod p) π ∧
      (A : Set (Fin τ.rank → ZMod p)) ⊆ latEigenCoroot p (k • τ.symmetrizedCartan) π O ∧
      A ⊓ rootAnnihilator p O = ⊥ ∧
      Module.finrank (ZMod p) A +
        Module.finrank (ZMod p) ↥(fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) =
        Module.finrank (ZMod p) (fixedSpace (ZMod p) π) := by
  classical
  have hfin : O.Finite := (Finset.finite_toSet (rootFinset τ)).subset fun α hα =>
    Finset.mem_coe.mpr (mem_rootFinset.mpr (hO α hα))
  let H : Subgroup (WeylGroup τ) := Subgroup.closure (rootReflection '' O)
  have hHcard : ¬ p ∣ Nat.card H := fun h => hW (h.trans (Subgroup.card_subgroup_dvd_card H))
  let r' : (Fin τ.rank → ℤ) → H := fun α =>
    if h : α ∈ O then ⟨rootReflection α, Subgroup.subset_closure ⟨α, h, rfl⟩⟩ else 1
  have hr'val : ∀ α ∈ O, ((r' α : H) : WeylGroup τ) = rootReflection α := by
    intro α hα
    simp [r', hα]
  have hgen : Subgroup.closure (r' '' O) = ⊤ := by
    have himg : r' '' O = (Subtype.val ⁻¹' (rootReflection '' O) : Set H) := by
      ext h
      constructor
      · rintro ⟨α, hα, rfl⟩
        exact ⟨α, hα, (hr'val α hα).symm⟩
      · rintro ⟨α, hα, hαh⟩
        exact ⟨α, hα, Subtype.ext ((hr'val α hα).trans hαh)⟩
    rw [himg]
    exact Subgroup.closure_closure_coe_preimage
  have hcor := latCorootZ_smul_symmetrizedCartan τ hk
  refine exists_complement_of_reflections hp2 hHcard ((weylCoactMat τ).comp H.subtype) _ π O
    r' hgen ?_ ?_ hGram hfin hπO
  · intro α hα y
    show weylCoactMat τ ((r' α : H) : WeylGroup τ) *ᵥ y = _
    rw [hr'val α hα, weylCoactMat_rootReflection (hO α hα), hcor]
  · intro α hα
    rw [hcor]
    exact sum_mul_corootPair_single (hO α hα)

end TagLemma

section Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly.LowTwoRank

theorem exists_complement_exc {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hW : ¬ p ∣ ggExcWeylOrder t)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU (absTag t) 6 f).D S)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)) (hπ : IsDiagAut (ggU (absTag t) 6 f).D π)
    (O : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ)) (hO : O ⊆ (ggU (absTag t) 6 f).D.roots)
    (hπO : ∀ α ∈ O, latPerm π α ∈ O) :
    ∃ A : Submodule (ZMod p) (Fin (ggU (absTag t) 6 f).D.rank → ZMod p),
      A ≤ fixedSpace (ZMod p) π ∧ (A : Set (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) ⊆
        latEigenCoroot p S π O ∧ A ⊓ rootAnnihilator p O = ⊥ ∧
      Module.finrank (ZMod p) A +
        Module.finrank (ZMod p) ↥(fixedSpace (ZMod p) π ⊓ rootAnnihilator p O) =
        Module.finrank (ZMod p) (fixedSpace (ZMod p) π) := by
  have hGram := latGram_latPerm_exc t f ht S hS π hπ
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨k, hk, rfl⟩ := isRootGram_F4 6 f S hS
    refine exists_complement_tag Tag.F4 hp2 ?_ (Int.natCast_pos.mpr hk) π hGram O
      (fun α hα => mem_rootFinset.mp ((mem_roots_F4 6 f α).mp (hO hα))) hπO
    rw [CFSG.Monster.B.Geometry.card_f4WeylGroup]
    exact hW
  · obtain ⟨k, hk, rfl⟩ := isRootGram_E6 6 f S hS
    refine exists_complement_tag Tag.E6 hp2 ?_ (Int.natCast_pos.mpr hk) π hGram O
      (fun α hα => mem_rootFinset.mp ((mem_roots_E6 6 f α).mp (hO hα))) hπO
    haveI : Fintype (WeylGroup .E6) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
    exact hW
  · obtain ⟨k, hk, rfl⟩ := isRootGram_E7 6 f S hS
    refine exists_complement_tag Tag.E7 hp2 ?_ (Int.natCast_pos.mpr hk) π hGram O
      (fun α hα => mem_rootFinset.mp ((mem_roots_E7 6 f α).mp (hO hα))) hπO
    haveI : Fintype (WeylGroup .E7) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E7_weyl_length_polynomial).2]
    exact hW
  · obtain ⟨k, hk, rfl⟩ := isRootGram_E8 6 f S hS
    refine exists_complement_tag Tag.E8 hp2 ?_ (Int.natCast_pos.mpr hk) π hGram O
      (fun α hα => mem_rootFinset.mp ((mem_roots_E8 6 f α).mp (hO hα))) hπO
    haveI : Fintype (WeylGroup .E8) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2]
    exact hW
  · obtain ⟨k, hk, rfl⟩ := isRootGram_E6 6 f S hS
    refine exists_complement_tag Tag.E6 hp2 ?_ (Int.natCast_pos.mpr hk) π hGram O
      (fun α hα => mem_rootFinset.mp ((mem_roots_E6 6 f α).mp (hO hα))) hπO
    haveI : Fintype (WeylGroup .E6) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
    exact hW

end Exc

end StepTwoToralIndex

end CFSG.StandardType
