module

public import CFSG.Sporadic.Schreier.Co1OuterImage
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions CFSG.RepresentationTheory
open Matrix

section Generic

variable {G : Type*} [Group G] (K : Subgroup G)

theorem normalizerMonoidHom_coe (A : Subgroup.normalizer (K : Set G)) (h : K) :
    ((K.normalizerMonoidHom A h : K) : G) = A * h * A⁻¹ := rfl

theorem normalizerMonoidHom_of_mem (g : K) :
    K.normalizerMonoidHom ⟨g, Subgroup.le_normalizer g.2⟩ = MulAut.conj g :=
  MulEquiv.ext fun _ => Subtype.ext rfl

@[expose] noncomputable def normOuter : Subgroup.normalizer (K : Set G) →* Outer K :=
  (QuotientGroup.mk' (inner K)).comp K.normalizerMonoidHom

theorem ker_normOuter (hC : Subgroup.centralizer (K : Set G) = ⊥) :
    (normOuter K).ker = K.subgroupOf (Subgroup.normalizer (K : Set G)) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hA
    have hA' : K.normalizerMonoidHom A ∈ inner K := by
      have := (QuotientGroup.eq_one_iff (N := inner K) (K.normalizerMonoidHom A)).mp
      exact this hA
    obtain ⟨k, hk⟩ := hA'
    have hcent : (k : G)⁻¹ * A ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hc := congrArg (fun α : MulAut K => ((α ⟨h, hh⟩ : K) : G)) hk
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        normalizerMonoidHom_coe] at hc
      calc h * ((k : G)⁻¹ * A) = (k : G)⁻¹ * (k * h * (k : G)⁻¹) * A := by group
        _ = (k : G)⁻¹ * (A * h * (A : G)⁻¹) * A := by rw [hc]
        _ = (k : G)⁻¹ * A * h := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    rw [← hcent]
    exact k.2
  · intro hA
    show QuotientGroup.mk' (inner K) (K.normalizerMonoidHom A) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨A, hA⟩, ?_⟩
    rw [← normalizerMonoidHom_of_mem]

theorem card_normalizer_quotient (hC : Subgroup.centralizer (K : Set G) = ⊥) :
    Nat.card (Subgroup.normalizer (K : Set G) ⧸ K.subgroupOf (Subgroup.normalizer (K : Set G))) =
      Nat.card (normOuter K).range := by
  rw [← ker_normOuter K hC]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (normOuter K)).toEquiv

theorem normOuter_range_le (N : Subgroup (MulAut K))
    (hN : ∀ A : Subgroup.normalizer (K : Set G), ∃ g : K,
      K.normalizerMonoidHom (⟨g, Subgroup.le_normalizer g.2⟩ * A) ∈ N) :
    (normOuter K).range ≤ N.map (QuotientGroup.mk' (inner K)) := by
  rintro _ ⟨A, rfl⟩
  obtain ⟨g, hg⟩ := hN A
  refine ⟨_, hg, ?_⟩
  show QuotientGroup.mk' (inner K) (K.normalizerMonoidHom (⟨g, Subgroup.le_normalizer g.2⟩ * A)) =
    QuotientGroup.mk' (inner K) (K.normalizerMonoidHom A)
  have h1 : QuotientGroup.mk' (inner K) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff (N := inner K) (MulAut.conj g)).mpr ⟨g, rfl⟩
  rw [map_mul, normalizerMonoidHom_of_mem, map_mul, h1, one_mul]

theorem mem_subgroupStabAut_of_iff {H : Subgroup G} {α : MulAut G}
    (h : ∀ x, x ∈ H ↔ α x ∈ H) : α ∈ subgroupStabAut H := by
  show H.map α.toMonoidHom = H
  ext x
  rw [Subgroup.mem_map_equiv, h (α.symm x), MulEquiv.apply_symm_apply]

end Generic

attribute [local instance] xAct

abbrev linNorm : Subgroup GL24 := Subgroup.normalizer (GA : Set GL24)

theorem finite_GL24 : Finite GL24 :=
  Finite.of_injective (fun u : GL24 => ((u : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    Fin 24 → Fin 24 → ZMod 2)) fun _ _ h => Units.ext h

theorem nMH_val (B : linNorm) (x : GA) :
    ((GA.normalizerMonoidHom B x : GA) : GL24) = (B : GL24) * x * (B : GL24)⁻¹ := rfl

theorem mulVec_injective (A : GL24) :
    Function.Injective fun v : Vec24 => (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v :=
  fun v w h => by
    have := congrArg (fun u => ((A⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u) h
    simpa only [inv_mulVec_mulVec] using this

theorem kOrbit_GA_mulVec {A : GL24} (hA : A ∈ linNorm) (v : Vec24) :
    kOrbit GA ((A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
      (fun w => (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) '' kOrbit GA v := by
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨((A⁻¹ * g * A : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v,
      ⟨A⁻¹ * g * A, (Subgroup.mem_normalizer_iff''.mp hA g).mp hg, rfl⟩, ?_⟩
    show (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((A⁻¹ * g * A : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
      (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ ((A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show A * (A⁻¹ * g * A) = g * A by group]
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨A * g * A⁻¹, (Subgroup.mem_normalizer_iff.mp hA g).mp hg, ?_⟩
    show ((A * g * A⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        ((A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
      (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show A * g * A⁻¹ * A = A * g by group]

theorem mulVec_z_mem_co1X
    {A : GL24} (hA : A ∈ linNorm) :
    (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 ∈ co1X := by
  have hcard : (kOrbit GA ((A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0)).ncard =
      98280 := by
    rw [kOrbit_GA_mulVec hA, Set.ncard_image_of_injective _ (mulVec_injective A),
      ← co1X_eq_kOrbit, ncard_co1X]
  have h := full_binary_vector_orbits.2.2.2.2.2.1 _ hcard
  rw [← h]
  exact mem_kOrbit_self _ _

theorem eq_z_of_fixed
    {x : Vec24} (hx : x ∈ co1X)
    (hfix : ∀ h ∈ stabH, ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x = x) :
    x = stabVecOf 0 := by
  have hsing : kOrbit stabH x = {x} := by
    ext w
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hfix h hh
    · intro hw
      rw [Set.mem_singleton_iff.mp hw]
      exact mem_kOrbit_self _ _
  have hu := mem_union_of_mem_co1X hx
  simp only [Set.mem_union] at hu
  have key : ∀ k < 4, x ∈ kOrbit stabH (stabVecOf k) → k = 0 := by
    intro k hk hxk
    have he := kOrbit_eq_of_mem hxk
    have hn := ncard_kOrbit_stabH hk
    rw [← he, hsing, Set.ncard_singleton] at hn
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rfl
    all_goals exact absurd hn (by decide)
  have h0 : x ∈ kOrbit stabH (stabVecOf 0) := by
    rcases hu with ((h | h) | h) | h
    · exact h
    · exact absurd (key 1 (by norm_num) h) (by norm_num)
    · exact absurd (key 2 (by norm_num) h) (by norm_num)
    · exact absurd (key 3 (by norm_num) h) (by norm_num)
  rw [kOrbit_stabH_zero] at h0
  exact h0

theorem centralizer_GA :
    Subgroup.centralizer (GA : Set GL24) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  have hcomm : ∀ g ∈ GA, ∀ v : Vec24, (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      ((A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
      (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) := by
    intro g hg v
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      Subgroup.mem_centralizer_iff.mp hA g hg]
  have hAz : (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0 :=
    eq_z_of_fixed (mulVec_z_mem_co1X (Subgroup.centralizer_le_normalizer _ hA)) fun h hh => by
      rw [hcomm h (stabH_le_GA hh), stabH_fix_z hh]
  have hX : ∀ x ∈ co1X, (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x = x := by
    intro x hx
    rw [co1X_eq_kOrbit] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hcomm g hg, hAz]
  have hker : Submodule.span (ZMod 2) co1X ≤ eqSub (A : Matrix (Fin 24) (Fin 24) (ZMod 2))
      ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    rw [Submodule.span_le]
    intro x hx
    show (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x =
      ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x
    rw [hX x hx, Units.val_one, one_mulVec]
  rw [span_co1X] at hker
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun i => ?_
  exact hker (Submodule.mem_top (x := Pi.single i 1))

theorem xz_val :
    (xz : Vec24) = stabVecOf 0 := rfl

theorem mem_stabSub_iff_fix
    {g : GA} :
    g ∈ stabSub ↔ ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 =
      stabVecOf 0 := by
  rw [stabSub, ← stabilizer_eq, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [xAct_val, xz_val] at h'
    exact h'
  · intro h
    apply Subtype.ext
    rw [xAct_val, xz_val]
    exact h

theorem normalizerMonoidHom_mem_subgroupStabAut
    (B : linNorm)
    (hBz : ((B : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0) :
    GA.normalizerMonoidHom B ∈ subgroupStabAut stabSub := by
  have hBz' : (((B : GL24)⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 =
      stabVecOf 0 := by
    conv_lhs => rw [← hBz]
    exact inv_mulVec_mulVec (B : GL24) _
  refine mem_subgroupStabAut_of_iff fun x => ?_
  rw [mem_stabSub_iff_fix, mem_stabSub_iff_fix, nMH_val, Units.val_mul, Units.val_mul,
    ← mulVec_mulVec, ← mulVec_mulVec, hBz']
  constructor
  · intro hx
    rw [hx, hBz]
  · intro hx
    have := congrArg (fun v => (((B : GL24)⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) hx
    simp only [inv_mulVec_mulVec] at this
    rw [this, hBz']

theorem normOuter_GA_range_le :
    (normOuter GA).range ≤ (subgroupStabAut stabSub).map (QuotientGroup.mk' (inner GA)) := by
  refine normOuter_range_le GA _ fun A => ?_
  have hX := mulVec_z_mem_co1X A.2
  rw [co1X_eq_kOrbit] at hX
  have hz : stabVecOf 0 ∈
      kOrbit GA (((A : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0) := by
    rw [kOrbit_eq_of_mem hX]
    exact mem_kOrbit_self _ _
  obtain ⟨g, hg, hgz⟩ := hz
  refine ⟨⟨g, hg⟩, normalizerMonoidHom_mem_subgroupStabAut _ ?_⟩
  show ((g * (A : GL24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0
  rw [Units.val_mul, ← mulVec_mulVec]
  exact hgz

theorem matrixVecStabilizer_eq :
    matrixVecStabilizer GA.subtype (stabVecOf 0) = stabSub := by
  ext g
  rw [mem_matrixVecStabilizer, mem_stabSub_iff_fix]
  rfl

theorem matrixOrbit_eq (w : Vec24) : matrixOrbit GA.subtype w = kOrbit GA w := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem classInvariant_of_module_uniqueness
    (huniq : ∀ ρ : GA →* GL (Fin 24) (ZMod 2), Function.Injective ρ →
      IsIrreducibleMatrixRep ρ → ∃ P : GL (Fin 24) (ZMod 2), ∀ g, ρ g = P * GA.subtype g * P⁻¹) :
    ClassInvariant stabSub := by
  have hfin := finite_GA
  have hirr : IsIrreducibleMatrixRep GA.subtype := fun W hW =>
    full_binary_vector_orbits.2.2.2.2.2.2 W fun g hg v hv => hW ⟨g, hg⟩ v hv
  have horbit : ∀ w : Vec24, Nat.card (matrixOrbit GA.subtype w) =
      Nat.card (matrixOrbit GA.subtype (stabVecOf 0)) →
      matrixOrbit GA.subtype w = matrixOrbit GA.subtype (stabVecOf 0) := by
    intro w hw
    rw [matrixOrbit_eq, matrixOrbit_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      ← co1X_eq_kOrbit, ncard_co1X] at hw
    rw [matrixOrbit_eq, matrixOrbit_eq, ← co1X_eq_kOrbit]
    exact full_binary_vector_orbits.2.2.2.2.2.1 w hw
  intro α
  have h := @unique_vector_orbit_module_twisting_class_invariance (ZMod 2) (↥GA) _
    (Subgroup.toGroup GA) 24 _ (by norm_num) hfin GA.subtype GA.subtype_injective hirr huniq
    (stabVecOf 0) horbit α
  rw [matrixVecStabilizer_eq] at h
  exact h

theorem linear_normalizer_and_module_uniqueness_reduction_of_inputs
    (hCo2 : ∀ (K : Type*) [Group K], K ≃* Blueprint.NativeSporadic.Co2 →
      Finite (Outer K) ∧ IsPGroup 2 (Outer K) ∧ Group.IsSolvable (Outer K)) :
    Subgroup.centralizer (GA : Set GL24) = ⊥ ∧
    Nat.card (linNorm ⧸ GA.subgroupOf linNorm) ∣ Nat.card (Outer Blueprint.NativeSporadic.Co2) ∧
    Finite (linNorm ⧸ GA.subgroupOf linNorm) ∧ IsPGroup 2 (linNorm ⧸ GA.subgroupOf linNorm) ∧
    ((∀ ρ : GA →* GL (Fin 24) (ZMod 2), Function.Injective ρ → IsIrreducibleMatrixRep ρ →
        ∃ P : GL (Fin 24) (ZMod 2), ∀ g, ρ g = P * GA.subtype g * P⁻¹) →
      Finite (Outer Blueprint.NativeSporadic.Co1) ∧
        IsPGroup 2 (Outer Blueprint.NativeSporadic.Co1)) := by
  obtain ⟨⟨-, -, hN⟩, -, hcls⟩ := co2_stabilizing_outer_image_two_group_of_inputs hCo2
  obtain ⟨n, hn⟩ := exists_card_outer_stabSub hCo2
  have hOutH : Nat.card (Outer stabSub) = Nat.card (Outer Blueprint.NativeSporadic.Co2) :=
    card_outer_congr stabSubEquiv
  have hdiv : Nat.card (linNorm ⧸ GA.subgroupOf linNorm) ∣
      Nat.card (Outer Blueprint.NativeSporadic.Co2) := by
    rw [card_normalizer_quotient GA centralizer_GA]
    exact (Subgroup.card_dvd_of_le normOuter_GA_range_le).trans hN
  have hdiv2 : Nat.card (linNorm ⧸ GA.subgroupOf linNorm) ∣ 2 ^ n := by
    rw [← hn, hOutH]
    exact hdiv
  have hGL := finite_GL24
  refine ⟨centralizer_GA, hdiv, inferInstance, isPGroup_two_of_card_dvd hdiv2, fun huniq => ?_⟩
  obtain ⟨h1, h2, -⟩ := hcls (classInvariant_of_module_uniqueness huniq)
  exact ⟨h1, h2⟩

end CFSG.Sporadic.Co1Schreier
