module

public import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.RankThree.PartOne.KLAY.RootSL2
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer
public import CFSG.RankThree.PartOne.KE.F4Regular
public import CFSG.RankThree.PartOne.KF.F4Torus

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.LocalCores CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.KFU CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SectionRank.LargeRee CFSG.RankThree.Chevalley CFSG.LieType.Ree.LargeReeCover
open CFSG.Timmesfeld.ExceptionalOrders (rootList mem_rootList)

open scoped Pointwise

@[expose] noncomputable def rhoM (K : Type) [Field K] (i : Fin F4.tag.rank) :
    SL2 K →* ↥(adjointGroup F4.tag K) :=
  (simpleRootSL2 F4.tag K i).codRestrict (adjointGroup F4.tag K)
    (fun A => simpleRootSL2_mem_adjointGroup i A)

theorem coe_rhoM {K : Type} [Field K] (i : Fin F4.tag.rank) (A : SL2 K) :
    ((rhoM K i A : ↥(adjointGroup F4.tag K)) : ModGL F4.tag K) = simpleRootSL2 F4.tag K i A :=
  rfl

section Action

variable {a : ℕ} {K : Type} [Field K] [CharP K ReeTag.F4.prime]

theorem rhoM_injective (i : Fin F4.tag.rank) : Function.Injective (rhoM K i) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  intro A B h
  exact simpleRootSL2_injective_of_charTwo i (congrArg Subtype.val h)

omit [CharP K ReeTag.F4.prime] in
theorem commute_rhoM (A B : SL2 K) : Commute (rhoM K largeReeI1 A) (rhoM K largeReeI4 B) :=
  Subtype.ext (commute_largeReeRankOne A B).eq

theorem finiteReeAut_rhoM_zero [Finite K] (A : SL2 K) :
    F4.finiteReeAut K a (rhoM K largeReeI1 A) =
      rhoM K largeReeI4 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) A) := by
  have h : (F4.finiteReeAut K a).toMonoidHom.comp (rhoM K largeReeI1) =
      (rhoM K largeReeI4).comp (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a)) := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change F4.finiteReeAut K a (rhoM K largeReeI1 (uSL c)) =
        rhoM K largeReeI4 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) (uSL c))
      have e1 : rhoM K largeReeI1 (uSL c) = xElement largeReeI1 c :=
        Subtype.ext (simpleRootSL2_uSL _ _)
      have e2 : rhoM K largeReeI4 (uSL (largeReeRhoHom K a c)) =
          xElement largeReeI4 (largeReeRhoHom K a c) := Subtype.ext (simpleRootSL2_uSL _ _)
      rw [e1, finiteReeAut_xElement, map_uSL, e2, largeRee_A1_data.1,
        (largeRee_relationExponent a).1, largeReeRhoHom_apply]
    · change F4.finiteReeAut K a (rhoM K largeReeI1 (vSL c)) =
        rhoM K largeReeI4 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) (vSL c))
      have e1 : rhoM K largeReeI1 (vSL c) = yElement largeReeI1 c :=
        Subtype.ext (simpleRootSL2_vSL _ _)
      have e2 : rhoM K largeReeI4 (vSL (largeReeRhoHom K a c)) =
          yElement largeReeI4 (largeReeRhoHom K a c) := Subtype.ext (simpleRootSL2_vSL _ _)
      rw [e1, finiteReeAut_yElement, map_vSL, e2, largeRee_A1_data.1,
        (largeRee_relationExponent a).1, largeReeRhoHom_apply]
  exact DFunLike.congr_fun h A

theorem finiteReeAut_rhoM_three [Finite K] (B : SL2 K) :
    F4.finiteReeAut K a (rhoM K largeReeI4 B) =
      rhoM K largeReeI1 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K (a + 1)) B) := by
  have h : (F4.finiteReeAut K a).toMonoidHom.comp (rhoM K largeReeI4) =
      (rhoM K largeReeI1).comp (Matrix.SpecialLinearGroup.map (largeReeRhoHom K (a + 1))) := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change F4.finiteReeAut K a (rhoM K largeReeI4 (uSL c)) =
        rhoM K largeReeI1 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K (a + 1)) (uSL c))
      have e1 : rhoM K largeReeI4 (uSL c) = xElement largeReeI4 c :=
        Subtype.ext (simpleRootSL2_uSL _ _)
      have e2 : rhoM K largeReeI1 (uSL (largeReeRhoHom K (a + 1) c)) =
          xElement largeReeI1 (largeReeRhoHom K (a + 1) c) := Subtype.ext (simpleRootSL2_uSL _ _)
      rw [e1, finiteReeAut_xElement, map_uSL, e2, largeRee_A1_data.2.1,
        (largeRee_relationExponent a).2, largeReeRhoHom_apply, pow_succ, mul_comm]
    · change F4.finiteReeAut K a (rhoM K largeReeI4 (vSL c)) =
        rhoM K largeReeI1 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K (a + 1)) (vSL c))
      have e1 : rhoM K largeReeI4 (vSL c) = yElement largeReeI4 c :=
        Subtype.ext (simpleRootSL2_vSL _ _)
      have e2 : rhoM K largeReeI1 (vSL (largeReeRhoHom K (a + 1) c)) =
          yElement largeReeI1 (largeReeRhoHom K (a + 1) c) := Subtype.ext (simpleRootSL2_vSL _ _)
      rw [e1, finiteReeAut_yElement, map_vSL, e2, largeRee_A1_data.2.1,
        (largeRee_relationExponent a).2, largeReeRhoHom_apply, pow_succ, mul_comm]
  exact DFunLike.congr_fun h B

end Action

section Fixed

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

@[expose] def f4S03 : Set (Fin F4.tag.rank → ℤ) :=
  {Pi.single largeReeI1 1, -Pi.single largeReeI1 1, Pi.single largeReeI4 1,
    -Pi.single largeReeI4 1}

theorem isRoot_of_mem_f4S03 {α : Fin F4.tag.rank → ℤ} (h : α ∈ f4S03) : IsRoot F4.tag α := by
  rcases h with rfl | rfl | rfl | rfl
  · exact IsRoot.basis _
  · exact IsRoot.neg (IsRoot.basis _)
  · exact IsRoot.basis _
  · exact IsRoot.neg (IsRoot.basis _)

theorem neg_mem_f4S03 {α : Fin F4.tag.rank → ℤ} (h : α ∈ f4S03) : -α ∈ f4S03 := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [f4S03]

theorem coord_f4S03 {α : Fin F4.tag.rank → ℤ} (h : α ∈ f4S03) :
    α (f4i 1) = 0 ∧ α (f4i 2) = 0 := by
  have h10 : f4i 1 ≠ largeReeI1 := by decide
  have h20 : f4i 2 ≠ largeReeI1 := by decide
  have h13 : f4i 1 ≠ largeReeI4 := by decide
  have h23 : f4i 2 ≠ largeReeI4 := by decide
  rcases h with rfl | rfl | rfl | rfl <;> simp [h10, h20, h13, h23]

@[expose] noncomputable def muF4 (K : Type) [Field K] [CharP K ReeTag.F4.prime] :
    SL2 K × SL2 K →* ModGL F4.tag K :=
  (simpleRootSL2 F4.tag K largeReeI1).noncommCoprod (simpleRootSL2 F4.tag K largeReeI4)
    fun A B => commute_largeReeRankOne A B

omit [Finite K] in
theorem muF4_apply (A B : SL2 K) :
    muF4 K (A, B) = simpleRootSL2 F4.tag K largeReeI1 A * simpleRootSL2 F4.tag K largeReeI4 B :=
  rfl

omit [Finite K] in
theorem exists_of_mem_rootSpan_f4S03 {x : ModGL F4.tag K} (hx : x ∈ rootSpan F4.tag K f4S03) :
    ∃ A B : SL2 K,
      x = simpleRootSL2 F4.tag K largeReeI1 A * simpleRootSL2 F4.tag K largeReeI4 B := by
  have hle : rootSpan F4.tag K f4S03 ≤ (muF4 K).range := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rcases hα with rfl | rfl | rfl | rfl
    · refine ⟨(uSL c, 1), ?_⟩
      rw [muF4_apply, map_one, mul_one, simpleRootSL2_uSL, pinnedX_single]
    · refine ⟨(vSL c, 1), ?_⟩
      rw [muF4_apply, map_one, mul_one, simpleRootSL2_vSL, pinnedX_neg_single]
    · refine ⟨(1, uSL c), ?_⟩
      rw [muF4_apply, map_one, one_mul, simpleRootSL2_uSL, pinnedX_single]
    · refine ⟨(1, vSL c), ?_⟩
      rw [muF4_apply, map_one, one_mul, simpleRootSL2_vSL, pinnedX_neg_single]
  obtain ⟨⟨A, B⟩, h⟩ := hle hx
  exact ⟨A, B, h.symm⟩

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem simpleRootSL2_mem_rootSpan_f4S03 {i : Fin F4.tag.rank}
    (hi : Pi.single i 1 ∈ f4S03) (A : SL2 K) :
    simpleRootSL2 F4.tag K i A ∈ rootSpan F4.tag K f4S03 := by
  have h := KE.rootRankOneGroup_le_rootSpan (τ := F4.tag) (L := K) (isRoot_of_mem_f4S03 hi) hi
    (neg_mem_f4S03 hi) ⟨A, by rw [rootSL2_single]⟩
  exact h

theorem largeReeA1Hom_mem_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) (A : SL2 K) :
    largeReeA1Hom K a A ∈ F4.reeGamma K a := by
  have h : largeReeA1Hom K a A ∈ (largeReeA1Hom K a).range := ⟨A, rfl⟩
  rw [largeReeA1Hom_range hK] at h
  exact (sup_le inf_le_right inf_le_right : largeReeA1M K a ≤ F4.reeGamma K a) h

@[expose] noncomputable def f4Phi (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SL2 K →* ↥(F4.reeGamma K a) :=
  (largeReeA1Hom K a).codRestrict (F4.reeGamma K a) (largeReeA1Hom_mem_reeGamma hK)

theorem f4Phi_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) : Function.Injective (f4Phi hK) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  exact eq_one_of_largeReeA1Hom_eq_one a (congrArg Subtype.val hA)

theorem reeGamma_inf_rootSpan_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (f4Phi hK).range.map (F4.reeGamma K a).subtype =
      F4.reeGamma K a ⊓ rootSpan F4.tag K f4S03 := by
  have h0 : (Pi.single largeReeI1 1 : Fin F4.tag.rank → ℤ) ∈ f4S03 := Or.inl rfl
  have h3 : (Pi.single largeReeI4 1 : Fin F4.tag.rank → ℤ) ∈ f4S03 := Or.inr (Or.inr (Or.inl rfl))
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨(f4Phi hK A).2, ?_⟩
    change largeReeA1Hom K a A ∈ _
    rw [largeReeA1Hom_apply]
    exact mul_mem (simpleRootSL2_mem_rootSpan_f4S03 h0 A) (simpleRootSL2_mem_rootSpan_f4S03 h3 _)
  · rintro ⟨hxΓ, hxQ⟩
    obtain ⟨A, B, rfl⟩ := exists_of_mem_rootSpan_f4S03 hxQ
    obtain ⟨hxA, hxF⟩ := ReeTag.mem_reeGamma.1 hxΓ
    have hxe : (⟨_, hxA⟩ : ↥(adjointGroup F4.tag K)) = rhoM K largeReeI1 A * rhoM K largeReeI4 B :=
      rfl
    rw [hxe, map_mul, finiteReeAut_rhoM_zero, finiteReeAut_rhoM_three] at hxF
    have hcomm := commute_rhoM (K := K) (Matrix.SpecialLinearGroup.map (largeReeRhoHom K (a + 1)) B)
      (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) A)
    rw [← hcomm.eq] at hxF
    obtain ⟨-, hB⟩ := eq_of_mul_eq_mul_of_commute (rhoM_injective largeReeI1)
      (rhoM_injective largeReeI4) (fun A B => commute_rhoM A B) hxF
    refine ⟨f4Phi hK A, ⟨A, rfl⟩, ?_⟩
    change largeReeA1Hom K a A = _
    rw [largeReeA1Hom_apply, hB]
    rfl

end Fixed

section Kernel

variable {p : ℕ}

theorem cartan_f4 (i j : Fin 4) : F4.tag.cartan (f4i i) (f4i j) =
    ![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -2, 2, -1], ![0, 0, -1, 2]] i j := by
  revert i j
  decide

theorem sum_f4 (g : Fin F4.tag.rank → ℤ) :
    ∑ k, g k = g (f4i 0) + g (f4i 1) + g (f4i 2) + g (f4i 3) := Fin.sum_univ_four g

theorem torusExp_combo (θ : ℤ) (β : Fin F4.tag.rank → ℤ) :
    torusExp0 θ β + 2 * torusExp1 θ β =
      (3 * β (f4i 1) - 2 * β (f4i 2)) + θ * (3 * β (f4i 2) - 4 * β (f4i 1)) := by
  simp only [torusExp0, torusExp1, ReeTag.cartanPair, sum_f4, cartan_f4]
  simp
  ring

set_option maxRecDepth 100000 in
theorem f4_root_check :
    ∀ β ∈ rootList F4.tag,
      ((β (f4i 1) = 0 ∧ β (f4i 2) = 0) →
        (β = Pi.single largeReeI1 1 ∨ β = -Pi.single largeReeI1 1 ∨ β = Pi.single largeReeI4 1 ∨
          β = -Pi.single largeReeI4 1)) ∧
      ((β (f4i 1) ≠ 0 ∨ β (f4i 2) ≠ 0) → 2 * β (f4i 1) ^ 2 - β (f4i 2) ^ 2 ∣ 8) := by
  decide +kernel

theorem f4_kernel_sub {θ : ℤ} (hp : p.Prime) (h5 : 5 ≤ p) (hθ : (p : ℤ) ∣ 2 * θ ^ 2 - 1)
    {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (A : Fin F4.tag.rank → Kˣ)
    (hA : ∀ β, IsRoot F4.tag β →
      rootChar A β = ζ ^ ((3 * β (f4i 1) - 2 * β (f4i 2)) + θ * (3 * β (f4i 2) - 4 * β (f4i 1)))) :
    rootCharKernel A ⊆ f4S03 := by
  rintro β ⟨hβ, hχ⟩
  rw [hA β hβ] at hχ
  have hdvd := (hζ.zpow_eq_one_iff_dvd _).1 hχ
  obtain ⟨h1, h2⟩ := f4_root_check β ((mem_rootList).2 hβ)
  by_cases hz : β (f4i 1) = 0 ∧ β (f4i 2) = 0
  · rcases h1 hz with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exfalso
    have hne : β (f4i 1) ≠ 0 ∨ β (f4i 2) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz hcon
    have h8 := h2 hne
    set x := 3 * β (f4i 1) - 2 * β (f4i 2) with hx
    set y := 3 * β (f4i 2) - 4 * β (f4i 1) with hy
    have hid : 2 * β (f4i 1) ^ 2 - β (f4i 2) ^ 2 =
        2 * (x + θ * y) * (x - θ * y) + y ^ 2 * (2 * θ ^ 2 - 1) := by
      rw [hx, hy]
      ring
    have hpN : (p : ℤ) ∣ 2 * β (f4i 1) ^ 2 - β (f4i 2) ^ 2 := by
      rw [hid]
      exact dvd_add (Dvd.dvd.mul_right (Dvd.dvd.mul_left hdvd _) _) (Dvd.dvd.mul_left hθ _)
    have hp8 : (p : ℤ) ∣ 8 := hpN.trans h8
    have hp8' : p ∣ 8 := by exact_mod_cast hp8
    have : p ∣ 2 ^ 3 := by simpa using hp8'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
    omega

end Kernel

section Torus

variable {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem torusExp_e0 (θ : ℤ) :
    torusExp0 θ (Pi.single (f4i 0) 1) = 2 ∧ torusExp1 θ (Pi.single (f4i 0) 1) = -1 := by
  simp [torusExp0, torusExp1, ReeTag.cartanPair, cartan_f4, Pi.single_apply]

theorem torusExp_e3 (θ : ℤ) :
    torusExp0 θ (Pi.single (f4i 3) 1) = 2 * θ ∧ torusExp1 θ (Pi.single (f4i 3) 1) = -θ := by
  simp [torusExp0, torusExp1, ReeTag.cartanPair, cartan_f4, Pi.single_apply]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem rootChar_eq_torusWeight {A : Fin F4.tag.rank → Kˣ} {u v : Kˣ}
    (hA : torusPair (K := K) a (u, v) = rootDiagUnit F4.tag A) {β : Fin F4.tag.rank → ℤ}
    (hβ : IsRoot F4.tag β) : rootChar A β = torusWeight a β (u, v) := by
  have h1 := rootDiagUnit_conj_pinnedX A hβ (1 : K)
  have h2 := torusPair_conj_pinnedX a (u, v) hβ (1 : K)
  rw [hA] at h2
  have h3 := pinnedX_injective F4.tag K β (h1.symm.trans h2)
  exact Units.ext (by simpa using h3)

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem torusWeight_e0 {u v : Kˣ} :
    torusWeight (K := K) a (Pi.single (f4i 0) 1) (u, v) = u ^ (2 : ℤ) * v ^ (-1 : ℤ) := by
  rw [torusWeight_apply, (torusExp_e0 _).1, (torusExp_e0 _).2]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem torusWeight_e3 {u v : Kˣ} :
    torusWeight (K := K) a (Pi.single (f4i 3) 1) (u, v) =
      (u ^ (2 : ℤ) * v ^ (-1 : ℤ)) ^ (2 ^ a : ℕ) := by
  rw [torusWeight_apply, (torusExp_e3 _).1, (torusExp_e3 _).2, mul_pow,
    ← zpow_natCast (u ^ (2 : ℤ)), ← zpow_natCast (v ^ (-1 : ℤ)), ← zpow_mul, ← zpow_mul]
  congr 2
  push_cast
  ring

omit [Finite K] in
theorem f4_act (b : Fin 2 → rootsOfUnity p K) :
    ∃ χ : Kˣ, χ = ((b 0 : rootsOfUnity p K) : Kˣ) ^ (2 : ℤ) *
        ((b 1 : rootsOfUnity p K) : Kˣ) ^ (-1 : ℤ) ∧
      ∀ A : SL2 K, tp4Hom p a K b * largeReeA1Hom K a A * (tp4Hom p a K b)⁻¹ =
        largeReeA1Hom K a (conjSL (diagUnitOne χ) A) := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (tp4Hom_mem_torusGroup (p := p)
    (a := a) (K := K) b)
  set u : Kˣ := ((b 0 : rootsOfUnity p K) : Kˣ) with hu
  set v : Kˣ := ((b 1 : rootsOfUnity p K) : Kˣ) with hv
  have hA : torusPair (K := K) a (u, v) = rootDiagUnit F4.tag l := by
    rw [← tp4Hom_apply]
    exact hl
  have e0 : largeReeI1 = f4i 0 := rfl
  have e3 : largeReeI4 = f4i 3 := rfl
  have hθ0 : IsRoot F4.tag (Pi.single largeReeI1 1) := IsRoot.basis _
  have hθ3 : IsRoot F4.tag (Pi.single largeReeI4 1) := IsRoot.basis _
  have h0 : rootChar l (Pi.single largeReeI1 1) = u ^ (2 : ℤ) * v ^ (-1 : ℤ) := by
    rw [rootChar_eq_torusWeight hA hθ0, e0, torusWeight_e0]
  have h3 : rootChar l (Pi.single largeReeI4 1) =
      Units.map (largeReeRhoHom K a : K →* K) (rootChar l (Pi.single largeReeI1 1)) := by
    rw [rootChar_eq_torusWeight hA hθ3, e3, torusWeight_e3, h0]
    apply Units.ext
    simp [largeReeRhoHom_apply]
    ring
  refine ⟨u ^ (2 : ℤ) * v ^ (-1 : ℤ), rfl, fun A => ?_⟩
  have c0 := rootDiagUnit_conj_rootSL2 l hθ0 A
  have c3 := rootDiagUnit_conj_rootSL2 l hθ3
    (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) A)
  rw [rootSL2_single] at c0 c3
  rw [h3] at c3
  rw [← h0]
  rw [map_conjSL_diagUnitOne] at c3
  rw [hl, largeReeA1Hom_apply, largeReeA1Hom_apply]
  calc rootDiagUnit F4.tag l * (simpleRootSL2 F4.tag K largeReeI1 A *
        simpleRootSL2 F4.tag K largeReeI4 (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) A)) *
        (rootDiagUnit F4.tag l)⁻¹ =
      (rootDiagUnit F4.tag l * simpleRootSL2 F4.tag K largeReeI1 A * (rootDiagUnit F4.tag l)⁻¹) *
        (rootDiagUnit F4.tag l * simpleRootSL2 F4.tag K largeReeI4
          (Matrix.SpecialLinearGroup.map (largeReeRhoHom K a) A) * (rootDiagUnit F4.tag l)⁻¹) := by
        group
    _ = _ := by
      rw [c0, c3]
      rfl

end Torus

section Side

variable {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem f4_SL2Torus (hP : F4Param p a K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    SL2Torus p (f4Phi hP.card) (Tp4 hP) := by
  have hK := hP.card
  refine ⟨f4Phi_injective hK, fun t ht => Tp4_exp hP t ht, ?_, ?_, ?_⟩
  · rintro t ⟨b, rfl⟩
    obtain ⟨χ, -, hχ⟩ := f4_act (a := a) b
    exact ⟨χ, fun A => Subtype.ext (hχ A)⟩
  · intro s hs
    have hsp : (s : Kˣ) ∈ rootsOfUnity p K := (mem_rootsOfUnity p s).2 hs
    refine ⟨![⟨s, hsp⟩, 1], Subtype.ext ?_⟩
    change tp4Hom p a K _ = largeReeA1Hom K a (HSL s)
    have hmap : Units.map (largeReeRhoHom K a).toMonoidHom s = s ^ 2 ^ a :=
      Units.ext (by simp [largeReeRhoHom_apply])
    rw [tp4Hom_apply, largeReeA1Hom_HSL, hmap]
    simp [torusPair_apply, torusElt_one]
    rfl
  · have hz : ζ ^ p = 1 := hζ.pow_eq_one
    let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hz⟩
    obtain ⟨χ, hχ, hact⟩ := f4_act (p := p) (a := a) (K := K) ![z, 1]
    refine ⟨tp4M hP ![z, 1], ⟨_, rfl⟩, fun h => ?_⟩
    have h1 : tp4M hP ![z, 1] * f4Phi hK (uSL 1) * (tp4M hP ![z, 1])⁻¹ =
        f4Phi hK (conjSL (diagUnitOne χ) (uSL 1)) := Subtype.ext (hact _)
    rw [h1, conjSL_diagUnitOne_uSL] at h
    have hu : (uSL ((χ : K) * 1) : SL2 K) = uSL 1 := f4Phi_injective hK h
    have := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 1) hu
    simp only [coe_uSL, mul_one] at this
    have hχ1 : χ = 1 := Units.ext this
    rw [hχ] at hχ1
    simp [z] at hχ1
    exact hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by have := hP.five_le; omega) hχ1

theorem f4_layerD (hP : F4Param p a K) {z z2 : rootsOfUnity p K}
    (hz : IsPrimitiveRoot (z : Kˣ) p) (hz2 : (z2 : Kˣ) = (z : Kˣ) ^ 2) :
    layerD (tp4M hP ![z, z2]) = (f4Phi hP.card).range := by
  classical
  have hK := hP.card
  have hp := hP.prime
  have h5 := hP.five_le
  have hζp : (z : Kˣ) ^ p = 1 := hz.pow_eq_one
  have hζ1 : (z : Kˣ) ≠ 1 := hz.ne_one (by omega)
  have h4 : 4 ≤ Nat.card K := by
    have hpf : p ≤ 2 ^ (2 * a + 1) - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := 2 * a + 1) (by omega)
      omega) hP.dvd
    rw [hK]
    omega
  set bM : ↥(F4.reeGamma K a) := tp4M hP ![z, z2] with hbM
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (tp4Hom_mem_torusGroup (p := p) (a := a) (K := K) ![z, z2])
  have hA : torusPair (K := K) a ((z : Kˣ), (z : Kˣ) ^ 2) = rootDiagUnit F4.tag l := by
    rw [← hl, tp4Hom_apply, ← hz2]
    rfl
  have hA' : ∀ β : Fin F4.tag.rank → ℤ, IsRoot F4.tag β → rootChar l β =
      (z : Kˣ) ^ ((3 * β (f4i 1) - 2 * β (f4i 2)) +
        (2 : ℤ) ^ a * (3 * β (f4i 2) - 4 * β (f4i 1))) := by
    intro β hβ
    rw [rootChar_eq_torusWeight hA hβ, torusWeight_apply, ← torusExp_combo ((2 : ℤ) ^ a) β,
      zpow_add, zpow_mul]
    simp
  have hap : ∀ i, l i ^ p = 1 := fun i => by
    have h := hA' (Pi.single i 1) (IsRoot.basis i)
    rw [rootChar_single] at h
    rw [h, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have hθ : (p : ℤ) ∣ 2 * ((2 : ℤ) ^ a) ^ 2 - 1 := by
    have := hP.theta_dvd
    push_cast at this
    exact this
  have hker : rootCharKernel l ⊆ f4S03 := f4_kernel_sub hp h5 hθ hz l hA'
  have hSker : f4S03 ⊆ rootCharKernel l := by
    intro α hα
    refine ⟨isRoot_of_mem_f4S03 hα, ?_⟩
    rw [hA' α (isRoot_of_mem_f4S03 hα)]
    have h1 := coord_f4S03 hα
    rw [h1.1, h1.2]
    simp
  have hbMd : ((bM : ↥(F4.reeGamma K a)) : ModGL F4.tag K) = rootDiagUnit F4.tag l := by
    rw [hbM, coe_tp4M]
    exact hl
  have hbM1 : bM ≠ 1 := fun h => hζ1 (by
    have h1 : (![z, z2] : Fin 2 → rootsOfUnity p K) = 1 :=
      tp4M_injective hP (h.trans (map_one _).symm)
    have := congrFun h1 0
    exact congrArg (fun x : rootsOfUnity p K => ((x : Kˣ))) this)
  have ha1 : l ≠ 1 := fun h => hbM1 (Subtype.ext (by rw [hbMd, h, rootDiagUnit_one]; rfl))
  have hSL := f4_SL2Torus hP hz
  refine inSubgroup_perfectResidual_centralizer_eq (F4.reeGamma K a) bM
    (torusGroup F4.tag K) (rootSpan F4.tag K f4S03)
    (triangular_borel_structure.{0, 0} F4.tag K).1
    (KE.torusGroup_le_normalizer_rootSpan fun α hα => isRoot_of_mem_f4S03 hα) ?_ ?_
    (f4Phi hK).range (reeGamma_inf_rootSpan_eq hK) (hSL.isQuasisimple_range h4).1
  · intro x hx
    rw [hbMd]
    exact rootSpan_le_centralizer_of_char_one (fun α hα => hSker hα) hx
  · intro y hy
    have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
    have hc' : (y : ModGL F4.tag K) * rootDiagUnit F4.tag l =
        rootDiagUnit F4.tag l * (y : ModGL F4.tag K) := by
      rw [← hbMd]
      exact hc
    exact KE.mem_torus_mul_rootSpan_of_commute hp (KE.not_dvd_card_weylGroup_F4 hp (by omega))
      hap ha1 (fun α hα => isRoot_of_mem_f4S03 hα) (fun α hα => neg_mem_f4S03 hα) hker
      (ReeTag.mem_reeGamma.1 y.2).1 hc'

theorem f4_side (hP : F4Param p a K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ bM ∈ Tp4 hP, bM ^ p = 1 ∧ bM ≠ 1 ∧ MSide p (2 * a + 1) (Tp4 hP) bM := by
  classical
  have hK := hP.card
  have hp := hP.prime
  have h5 := hP.five_le
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have h4 : 4 ≤ Nat.card K := by
    have hpf : p ≤ 2 ^ (2 * a + 1) - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := 2 * a + 1) (by omega)
      omega) hP.dvd
    rw [hK]
    omega
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp⟩
  let z2 : rootsOfUnity p K := ⟨ζ ^ 2, (mem_rootsOfUnity p _).2 (by
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow])⟩
  set bM : ↥(F4.reeGamma K a) := tp4M hP ![z, z2] with hbM
  have hbMT : bM ∈ Tp4 hP := tp4M_mem_Tp4 hP _
  have hbM1 : bM ≠ 1 := fun h => hζ1 (by
    have h1 : (![z, z2] : Fin 2 → rootsOfUnity p K) = 1 :=
      tp4M_injective hP (h.trans (map_one _).symm)
    have := congrFun h1 0
    exact congrArg (fun x : rootsOfUnity p K => ((x : Kˣ))) this)
  refine ⟨bM, hbMT, Tp4_exp hP bM hbMT, hbM1, ?_⟩
  have hSL := f4_SL2Torus hP hζ
  have hD := f4_layerD hP (z := z) (z2 := z2) hζ rfl
  have hchar : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact MSide.of_SL2Torus hSL hp ⟨ζ, hζ⟩ hK h4 hD

end Side

end CFSG.RankThree.PartOne.KLAY
