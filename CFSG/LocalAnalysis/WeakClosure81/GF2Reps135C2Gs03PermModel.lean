module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03AutGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.OuterAutomorphisms

private noncomputable def w135c2_actFunAux {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) (g : A) (s : S) : S :=
  Classical.choose (hN g g.2 s)

private lemma w135c2_actFunAux_spec {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) (g : A) (s : S) :
    ι (w135c2_actFunAux ι A hN g s) =
      (g : Equiv.Perm Ω) * ι s * (g : Equiv.Perm Ω)⁻¹ :=
  Classical.choose_spec (hN g g.2 s)

private noncomputable def w135c2_actMul {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι) (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) (g : A) : MulAut S where
  toFun := w135c2_actFunAux ι A hN g
  invFun := w135c2_actFunAux ι A hN g⁻¹
  left_inv := by
    intro s
    apply hι
    simp only [w135c2_actFunAux_spec, Subgroup.coe_inv, inv_inv]
    group
  right_inv := by
    intro s
    apply hι
    simp only [w135c2_actFunAux_spec, Subgroup.coe_inv, inv_inv]
    group
  map_mul' := by
    intro s t
    apply hι
    simp only [w135c2_actFunAux_spec, map_mul]
    group

private lemma w135c2_actMul_apply {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι) (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) (g : A) (s : S) :
    (w135c2_actMul ι hι A hN g) s = w135c2_actFunAux ι A hN g s := rfl

private noncomputable def w135c2_actAut {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι) (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) : A →* MulAut S where
  toFun := w135c2_actMul ι hι A hN
  map_one' := by
    apply MulEquiv.ext
    intro s
    apply hι
    simp only [w135c2_actMul_apply, w135c2_actFunAux_spec, Subgroup.coe_one, one_mul, mul_one,
      inv_one, MulAut.one_apply]
  map_mul' := by
    intro g h
    apply MulEquiv.ext
    intro s
    apply hι
    simp only [MulAut.mul_apply, w135c2_actMul_apply, w135c2_actFunAux_spec, Subgroup.coe_mul,
      mul_inv_rev]
    group

private lemma w135c2_actAut_apply {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι) (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) (g : A) (s : S) :
    (w135c2_actAut ι hι A hN g) s = w135c2_actFunAux ι A hN g s := rfl

private lemma w135c2_actAut_apply_iota {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι) (A : Subgroup (Equiv.Perm Ω))
    (hSA : ι.range ≤ A)
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) (u : S) :
    w135c2_actAut ι hι A hN ⟨ι u, hSA ⟨u, rfl⟩⟩ = MulAut.conj u := by
  apply MulEquiv.ext
  intro s
  apply hι
  rw [w135c2_actAut_apply, w135c2_actFunAux_spec, MulAut.conj_apply]
  simp only [map_mul, map_inv]

private lemma w135c2_actAut_injective {S : Type} [Group S] {Ω : Type} [Fintype Ω]
    (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι)
    (hC : ∀ τ : Equiv.Perm Ω, (∀ s : S, τ * ι s = ι s * τ) → τ = 1)
    (A : Subgroup (Equiv.Perm Ω))
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range) :
    Function.Injective (w135c2_actAut ι hι A hN) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff]
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hg
    apply Subtype.ext
    apply hC (g : Equiv.Perm Ω)
    intro s
    have hpoint : w135c2_actFunAux ι A hN g s = s := by
      have hthis := congrArg (fun f : MulAut S => f s) hg
      rw [w135c2_actAut_apply] at hthis
      simpa using hthis
    have hspec := w135c2_actFunAux_spec ι A hN g s
    rw [hpoint] at hspec
    conv_rhs => rw [hspec]
    group
  · intro hg
    rw [hg, map_one]

theorem autGenBound_of_permModel {S : Type} [Group S] [Finite S] {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (ι : S →* Equiv.Perm Ω) (hι : Function.Injective ι)
    (hC : ∀ τ : Equiv.Perm Ω, (∀ s : S, τ * ι s = ι s * τ) → τ = 1)
    (A : Subgroup (Equiv.Perm Ω)) (hSA : ι.range ≤ A)
    (hN : ∀ g ∈ A, ∀ s : S, g * ι s * g⁻¹ ∈ ι.range)
    (hcard : Nat.card (MulAut S) ≤ Nat.card A) {k : ℕ} (outerOnly : Prop)
    (hgen : ∀ g ∈ A, g * g = 1 → g ≠ 1 → (outerOnly → g ∉ ι.range) →
      ∃ s : Fin k → S,
        ι.range ≤ Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i))) :
    AutGenBound S k (fun a => outerOnly → a ∉ inner S) := by
  classical
  intro a ha2 hP
  have hinj : Function.Injective (w135c2_actAut ι hι A hN) :=
    w135c2_actAut_injective ι hι hC A hN
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  obtain ⟨g, hg_eq⟩ := (hinj.bijective_of_nat_card_le hcard).surjective a
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hg2 : g * g = 1 := by
    apply hinj
    rw [map_mul, hg_eq, haa, map_one]
  have hg2' : (g : Equiv.Perm Ω) * (g : Equiv.Perm Ω) = 1 := by
    have h := congrArg (fun x : A => (x : Equiv.Perm Ω)) hg2
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h
  have hg_not : outerOnly → (g : Equiv.Perm Ω) ∉ ι.range := by
    intro ho hmem
    apply hP ho
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    have hgu : g = ⟨ι u, hSA ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
    rw [← hg_eq, hgu, w135c2_actAut_apply_iota]
    exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hg1 : (g : Equiv.Perm Ω) ≠ 1 := by
    intro h
    have hg1' : g = 1 := Subtype.ext h
    rw [hg1', map_one] at hg_eq
    rw [← hg_eq, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨s, hclos⟩ := hgen (g : Equiv.Perm Ω) g.2 hg2' hg1 hg_not
  refine ⟨s, ?_⟩
  let gen : Fin k → Equiv.Perm Ω := fun i => (ι (s i))⁻¹ * (g : Equiv.Perm Ω) * ι (s i)
  let z : Fin k → A := fun i =>
    ⟨gen i, by
      simp only [gen]
      exact A.mul_mem (A.mul_mem (A.inv_mem (hSA ⟨s i, rfl⟩)) g.2) (hSA ⟨s i, rfl⟩)⟩
  have hzi : ∀ i, w135c2_actAut ι hι A hN (z i) =
      (MulAut.conj (s i))⁻¹ * a * MulAut.conj (s i) := by
    intro i
    have hz_eq : z i =
        (⟨ι (s i), hSA ⟨s i, rfl⟩⟩ : A)⁻¹ * g * ⟨ι (s i), hSA ⟨s i, rfl⟩⟩ := by
      apply Subtype.ext
      rfl
    rw [hz_eq]
    simp only [map_mul, map_inv, hg_eq, w135c2_actAut_apply_iota]
  have hsub : A.subtype '' Set.range z = Set.range gen := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hPmap : Subgroup.closure (Set.range gen) =
      (Subgroup.closure (Set.range z)).map A.subtype := by
    rw [MonoidHom.map_closure, hsub]
  intro x hx
  change x ∈ (MulAut.conj : S →* MulAut S).range at hx
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
  have hqK : (⟨ι u, hSA ⟨u, rfl⟩⟩ : A) ∈ Subgroup.closure (Set.range z) := by
    have hmem : A.subtype (⟨ι u, hSA ⟨u, rfl⟩⟩ : A) ∈
        (Subgroup.closure (Set.range z)).map A.subtype := by
      rw [← hPmap]
      exact hclos ⟨u, rfl⟩
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp hmem
    have hyq' : y = ⟨ι u, hSA ⟨u, rfl⟩⟩ := Subtype.ext hyq
    rwa [hyq'] at hy
  have hKmap : (Subgroup.closure (Set.range z)).map (w135c2_actAut ι hι A hN) =
      Subgroup.closure
        (Set.range fun i => (MulAut.conj (s i))⁻¹ * a * MulAut.conj (s i)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hzi i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, hzi i⟩
  have hmemT : w135c2_actAut ι hι A hN (⟨ι u, hSA ⟨u, rfl⟩⟩ : A) ∈
      Subgroup.closure
        (Set.range fun i => (MulAut.conj (s i))⁻¹ * a * MulAut.conj (s i)) := by
    have hmap : w135c2_actAut ι hι A hN (⟨ι u, hSA ⟨u, rfl⟩⟩ : A) ∈
        (Subgroup.closure (Set.range z)).map (w135c2_actAut ι hι A hN) :=
      Subgroup.mem_map.mpr ⟨⟨ι u, hSA ⟨u, rfl⟩⟩, hqK, rfl⟩
    rwa [hKmap] at hmap
  rwa [w135c2_actAut_apply_iota] at hmemT

end CFSG.LocalAnalysis.WeakClosure81
