module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open Subgroup
open scoped Pointwise commutatorElement

section Generic

variable {C : Type*} [Group C] [Finite C]

theorem aschbacherSolvableCore_fixes_of_layer_eq_top
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ} (hp : p.Prime)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C)
    {R : Subgroup C} (hRx : R ≤ centralizer ({x} : Set C))
    (hRinv : ∀ η : MulAut C, η x = x → ∀ r ∈ R, η r ∈ R) (hRL : layer R = ⊤) :
    ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R, (s : MulAut C) r = r := by
  classical
  have hconj : ∀ (η : MulAut C) (y : C), η * MulAut.conj y * η⁻¹ = MulAut.conj (η y) :=
    fun η y => MulEquiv.ext fun z => by
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hcomm : ∀ {η : MulAut C} {y : C}, η * MulAut.conj y = MulAut.conj y * η → η y = y :=
    fun {η y} h => hinj (by rw [← hconj, h, mul_inv_cancel_right])
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ with hb
  set M : Subgroup B := centralizer ({b} : Set B) with hM
  have hfix : ∀ m ∈ M, (m : MulAut C) x = x := fun m hm =>
    hcomm (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  set β : C →* B := (MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩ with hβ
  have hβinj : Function.Injective β := fun c d h => hinj (congrArg Subtype.val h)
  have hRM : R.map β ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    change MulAut.conj r * MulAut.conj x = MulAut.conj x * MulAut.conj r
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 (hRx hr))]
  set N : Subgroup M := (R.map β).subgroupOf M with hN
  have hNnormal : N.Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨r, hr, hrn⟩ := hn
    refine ⟨(m : MulAut C) r, hRinv _ (hfix m m.2) r hr, Subtype.ext ?_⟩
    change MulAut.conj ((m : MulAut C) r) = (m : MulAut C) * ((n : B) : MulAut C) * (m : MulAut C)⁻¹
    rw [← hconj, show MulAut.conj r = ((n : B) : MulAut C) from congrArg Subtype.val hrn]
  let e : R ≃* N := (Subgroup.equivMapOfInjective R β hβinj).trans
    (Subgroup.subgroupOfEquivOfLe hRM).symm
  have he : ∀ r : R, ((e r : M) : B) = β r := fun r => rfl
  obtain ⟨hsolv, -⟩ := solvable_prime_complement_core_characterization (H := M) hp
  have hcent := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (aschbacherSolvableCore_normal p M).isSubnormal).1
  intro s hs r hr
  obtain ⟨s', hs', rfl⟩ := hs
  set X : Subgroup R := (centralizer ({s'} : Set M)).comap (N.subtype.comp e.toMonoidHom) with hX
  have hlayer : layer R ≤ X := by
    refine sSup_le fun L hL => ?_
    set L' : Subgroup M := (L.map e.toMonoidHom).map N.subtype with hL'
    have hL'comp : IsComponent L' := by
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.equivMapOfInjective L
        e.toMonoidHom e.injective).trans (Subgroup.equivMapOfInjective _ N.subtype
          N.subtype_injective)) hL.1, ?_⟩
      refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_ hNnormal.isSubnormal
      rw [show L'.subgroupOf N = L.map e.toMonoidHom from
        Subgroup.comap_map_eq_self_of_injective N.subtype_injective _]
      exact hL.2.map e.surjective
    intro l hl
    have hl' : N.subtype (e l) ∈ L' := ⟨e l, ⟨l, hl, rfl⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcent L' hL'comp) hl') s' hs'
    exact Subgroup.mem_centralizer_singleton_iff.2 h1.symm
  have hrX : (⟨r, hr⟩ : R) ∈ X := hlayer (hRL ▸ Subgroup.mem_top _)
  have h2 := congrArg (fun m : M => ((m : B) : MulAut C))
    (Subgroup.mem_centralizer_singleton_iff.1 hrX)
  exact hcomm h2.symm

end Generic

section F4

variable {K : Type} [Field K]

theorem card_core_dvd_of_fixes_descended {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (x : adjointGroup .F4 K) (R R₀ : Subgroup (adjointGroup .F4 K)) (M : Type) [Field M]
    [Finite M] (ι : K →+* M) {g : ModGL .F4 M} (hg : g ∈ adjointGroup .F4 M)
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (P : GL (Fin 2) M)
    (hRg : (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        (rootSL2 .F4 M α))
    (hfixR : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R, (s : MulAut (adjointGroup .F4 K)) r = r)
    (hfixR₀ : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R₀, (s : MulAut (adjointGroup .F4 K)) r = r) :
    Nat.card (inSubgroup (aschbacherSolvableCore p)
        (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B))) ∣
      Nat.card (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
        centralizer (R : Set (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hinner : ∀ η : MulAut (adjointGroup .F4 K), (∀ r ∈ R₀, η r = r) →
      η ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    (even_F4_descended_root_SL2_pointwise_automorphisms_inner hf K hK M ι R₀ hg hα P hRg).1
  set β : adjointGroup .F4 K →* B :=
    (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).codRestrict B
      fun c => hB ⟨c, rfl⟩ with hβ
  have hβinj : Function.Injective β := fun c d h => hinj (congrArg Subtype.val h)
  have hle : inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)) ≤
      (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
        centralizer (R : Set (adjointGroup .F4 K))).map β := by
    intro s hs
    obtain ⟨c, hc⟩ := hinner (s : MulAut (adjointGroup .F4 K)) (hfixR₀ s hs)
    have hsM : s ∈ centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B) :=
      Subgroup.map_subtype_le _ hs
    refine ⟨c, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_),
      Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, Subtype.ext hc⟩
    · have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hsM)
      simp only [Subgroup.coe_mul] at h1
      rw [map_mul, map_mul, hc]
      exact h1
    · have h1 := hfixR s hs r hr
      rw [← hc, MulAut.conj_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective hβinj] at h

theorem apply_mem_derived_centralizer {C : Type*} [Group C] {η : MulAut C} {x : C}
    (hη : η x = x) {r : C}
    (hr : r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆) :
    η r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ := by
  have hY : (centralizer ({x} : Set C)).map η.toMonoidHom = centralizer ({x} : Set C) := by
    rw [CFSG.RankThree.PartOne.map_centralizer_singleton_mulEquiv, hη]
  have h1 : η r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆.map η.toMonoidHom :=
    ⟨r, hr, rfl⟩
  rwa [Subgroup.map_commutator, hY] at h1

theorem derived_centralizer_le {C : Type*} [Group C] (x : C) :
    ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ ≤ centralizer ({x} : Set C) :=
  Subgroup.commutator_le.2 fun u hu v hv => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)


theorem even_F4_descended_root_layer_centralizer_local_core_odd {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (x : adjointGroup .F4 K)
    (hRL : layer (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) = ⊤)
    (hodd : Odd (Nat.card (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
      centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
          Set (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K))))
    (R₀ : Subgroup (adjointGroup .F4 K))
    (hR₀ : R₀ ≤ ⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆)
    (M : Type) [Field M] [Finite M] (ι : K →+* M) {g : ModGL .F4 M}
    (hg : g ∈ adjointGroup .F4 M) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (P : GL (Fin 2) M)
    (hRg : (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        (rootSL2 .F4 M α)) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hfixR := aschbacherSolvableCore_fixes_of_layer_eq_top hinj hp hB x
    (derived_centralizer_le x) (fun η hη r hr => apply_mem_derived_centralizer hη hr) hRL
  exact hodd.of_dvd_nat (card_core_dvd_of_fixes_descended hf hK B hB x _ R₀ M ι hg hα P hRg
    hfixR fun s hs r hr => hfixR s hs r (hR₀ hr))

theorem sl2Upper_sq_eq_one_of_charTwo {F : Type*} [Field F] [CharP F 2] (c : F) :
    sl2Upper F c ^ 2 = 1 := by
  ext i j
  rw [sq, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem sl2Lower_sq_eq_one_of_charTwo {F : Type*} [Field F] [CharP F 2] (c : F) :
    sl2Lower F c ^ 2 = 1 := by
  ext i j
  rw [sq, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem le_of_forall_sq_eq_one_mem_of_descended [CharP K 2]
    (R₀ : Subgroup (adjointGroup .F4 K)) (M : Type) [Field M] (ι : K →+* M)
    {g : ModGL .F4 M} {α : Fin Tag.F4.rank → ℤ} (P : GL (Fin 2) M)
    (hRg : (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        (rootSL2 .F4 M α))
    {X : Subgroup (adjointGroup .F4 K)} (hX : ∀ u ∈ R₀, u ^ 2 = 1 → u ∈ X) : R₀ ≤ X := by
  classical
  set F : adjointGroup .F4 K →* ModGL .F4 M := (MulAut.conj g).toMonoidHom.comp
    ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype) with hFdef
  have hF : Function.Injective F := (MulAut.conj g).injective.comp
    ((baseChangeGL_injective (τ := .F4) ι).comp Subtype.val_injective)
  set φ₁ : SL2 K →* ModGL .F4 M := (rootSL2 .F4 M α).comp
    ((CFSG.RankThree.Classical.conjSL P).comp (Matrix.SpecialLinearGroup.map ι)) with hφ₁
  have hrange : φ₁.range = R₀.map F := by
    rw [hφ₁, MonoidHom.range_comp, MonoidHom.range_comp, hFdef, ← Subgroup.map_map, hRg]
  have hmem : ∀ A, φ₁ A ∈ R₀.map F := fun A => hrange ▸ ⟨A, rfl⟩
  let e : R₀ ≃* R₀.map F := R₀.equivMapOfInjective F hF
  set Ψ : SL2 K →* adjointGroup .F4 K :=
    R₀.subtype.comp (e.symm.toMonoidHom.comp (φ₁.codRestrict _ hmem)) with hΨ
  have hFΨ : ∀ A, F (Ψ A) = φ₁ A := fun A => by
    change ((e (e.symm ⟨φ₁ A, hmem A⟩) : R₀.map F) : ModGL .F4 M) = φ₁ A
    rw [MulEquiv.apply_symm_apply]
  have hΨR : ∀ A, Ψ A ∈ R₀ := fun A => (e.symm ⟨φ₁ A, hmem A⟩).2
  have hR₀ : R₀ ≤ Ψ.range := by
    intro r hr
    obtain ⟨A, hA⟩ : F r ∈ φ₁.range := hrange ▸ ⟨r, hr, rfl⟩
    exact ⟨A, hF (by rw [hFΨ, hA])⟩
  refine hR₀.trans ?_
  rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨A, hA | hA, rfl⟩
  · obtain ⟨c, rfl⟩ := hA
    exact hX _ (hΨR _) (by rw [← map_pow, sl2Upper_sq_eq_one_of_charTwo, map_one])
  · obtain ⟨c, rfl⟩ := hA
    exact hX _ (hΨR _) (by rw [← map_pow, sl2Lower_sq_eq_one_of_charTwo, map_one])

theorem even_F4_central_derived_layer_and_descended_root_local_core_odd {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    (x : adjointGroup .F4 K)
    (hRL : layer (⁅centralizer ({x} : Set (adjointGroup .F4 K)),
      centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) = ⊤)
    (hZ : centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
        centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
          centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
            Set (adjointGroup .F4 K)) =
      (center (centralizer ({x} : Set (adjointGroup .F4 K)))).map
        (centralizer ({x} : Set (adjointGroup .F4 K))).subtype)
    (hodd : Odd (Nat.card (centralizer ({x} : Set (adjointGroup .F4 K)) ⊓
      centralizer ((⁅centralizer ({x} : Set (adjointGroup .F4 K)),
        centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)) :
          Set (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K))))
    (R₀ : Subgroup (adjointGroup .F4 K)) (hR₀ : R₀ ≤ centralizer ({x} : Set (adjointGroup .F4 K)))
    (M : Type) [Field M] [Finite M] (ι : K →+* M) {g : ModGL .F4 M}
    (hg : g ∈ adjointGroup .F4 M) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (P : GL (Fin 2) M)
    (hRg : (R₀.map ((baseChangeGL ι).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        (rootSL2 .F4 M α)) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  set D := centralizer ({x} : Set (adjointGroup .F4 K)) with hD
  set R := (⁅D, D⁆ : Subgroup (adjointGroup .F4 K)) with hR
  have hfixR := aschbacherSolvableCore_fixes_of_layer_eq_top hinj hp hB x
    (derived_centralizer_le x) (fun η hη r hr => apply_mem_derived_centralizer hη hr) hRL
  have hfixx : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      (s : MulAut (adjointGroup .F4 K)) x = x := by
    intro s hs
    have hsM := Subgroup.map_subtype_le _ hs
    have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hsM)
    simp only [Subgroup.coe_mul] at h1
    apply hinj
    have e : (s : MulAut (adjointGroup .F4 K)) * MulAut.conj x * (s : MulAut _)⁻¹ =
        MulAut.conj ((s : MulAut (adjointGroup .F4 K)) x) := MulEquiv.ext fun y => by
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [← e, h1, mul_inv_cancel_right]
  have hfixinv : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ u ∈ D, u ^ 2 = 1 → (s : MulAut (adjointGroup .F4 K)) u = u := by
    intro s hs u hu hu2
    obtain ⟨η, hη⟩ : ∃ η : MulAut (adjointGroup .F4 K), η = s := ⟨_, rfl⟩
    rw [← hη]
    obtain ⟨z, hz⟩ : ∃ z, z = η u * u⁻¹ := ⟨_, rfl⟩
    have hηx : η x = x := hη ▸ hfixx s hs
    have hηu : η u ∈ D := by
      rw [hD, mem_centralizer_singleton_iff] at hu ⊢
      rw [← hηx, ← map_mul, ← map_mul, hu]
    have hzR : z ∈ D ⊓ centralizer (R : Set (adjointGroup .F4 K)) := by
      refine Subgroup.mem_inf.2 ⟨hz ▸ mul_mem hηu (inv_mem hu),
        Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have hconj : (MulAut.conj u⁻¹) x = x := by
        rw [MulAut.conj_apply, (mem_centralizer_singleton_iff.1 (inv_mem hu)), mul_inv_cancel_right]
      have hr' : u⁻¹ * r * u ∈ R := by
        have := apply_mem_derived_centralizer hconj hr
        rwa [MulAut.conj_apply, inv_inv] at this
      have h1 : η (u⁻¹ * r * u) = u⁻¹ * r * u := hη ▸ hfixR s hs _ hr'
      have h2 : η r = r := hη ▸ hfixR s hs r hr
      rw [map_mul, map_mul, map_inv] at h1
      have h3 : z * r * z⁻¹ = r := by
        calc z * r * z⁻¹ = η u * (u⁻¹ * r * u) * (η u)⁻¹ := by rw [hz]; group
          _ = η u * ((η u)⁻¹ * η r * η u) * (η u)⁻¹ := by rw [h1]
          _ = r := by rw [h2]; group
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    have hzZ := hZ ▸ hzR
    obtain ⟨zD, hzD, hzz⟩ := hzZ
    have hzu : z * u = u * z := by
      have := Subgroup.mem_center_iff.1 hzD ⟨u, hu⟩
      rw [← hzz]
      exact (congrArg Subtype.val this).symm
    have hz2 : z ^ 2 = 1 := by
      have h1 : η u = z * u := by rw [hz, inv_mul_cancel_right]
      calc z ^ 2 = z ^ 2 * u ^ 2 := by rw [hu2, mul_one]
        _ = (z * u) ^ 2 := (Commute.mul_pow hzu 2).symm
        _ = η (u ^ 2) := by rw [map_pow, h1]
        _ = 1 := by rw [hu2, map_one]
    have hz2' : (⟨z, hzR⟩ : (D ⊓ centralizer (R : Set (adjointGroup .F4 K)) :
        Subgroup (adjointGroup .F4 K))) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    have hcop : Nat.Coprime (orderOf (⟨z, hzR⟩ : (D ⊓ centralizer (R : Set (adjointGroup .F4 K)) :
        Subgroup (adjointGroup .F4 K))))
        (Nat.card (D ⊓ centralizer (R : Set (adjointGroup .F4 K)) :
          Subgroup (adjointGroup .F4 K))) :=
      (Nat.coprime_two_left.2 hodd).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hz2')
    have hord := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_natCard _)
    have hz1 : z = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 hord)
    rw [hz] at hz1
    exact mul_inv_eq_one.1 hz1
  have hfixR₀ : ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)),
      ∀ r ∈ R₀, (s : MulAut (adjointGroup .F4 K)) r = r := by
    intro s hs r hr
    exact le_of_forall_sq_eq_one_mem_of_descended R₀ M ι P hRg
      (X := MonoidHom.eqLocus (s : MulAut (adjointGroup .F4 K)).toMonoidHom (MonoidHom.id _))
      (fun u hu hu2 => hfixinv s hs u (hR₀ hu) hu2) hr
  exact hodd.of_dvd_nat (card_core_dvd_of_fixes_descended hf hK B hB x R R₀ M ι hg hα P hRg
    hfixR hfixR₀)

end F4

end CFSG.RankThree.Chevalley
