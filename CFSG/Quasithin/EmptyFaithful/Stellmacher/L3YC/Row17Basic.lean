module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1Aux
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCM24Glue

public section

namespace CFSG.Quasithin.Stellmacher.L3YC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Row17Conc {X : Type} [Group X] (B : Subgroup X) (ω : X) : Prop :=
  ω ∈ Subgroup.normalizer (B : Set X) ∧ ω ^ 3 = 1 ∧
    ∀ b ∈ B, ∃ q ∈ ⁅(CFSG.pCore 2 ↥B).map B.subtype, B⁆, ω * q * ω⁻¹ ≠ b * q * b⁻¹

theorem commutator_pCore_map_eq {X : Type} [Group X] (B : Subgroup X) :
    ⁅(CFSG.pCore 2 ↥B).map B.subtype, B⁆ =
      (⁅CFSG.pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆).map B.subtype := by
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem Row17Conc.of_row14 {X : Type} [Group X] {B : Subgroup X} {ω : X}
    (h : Stellmacher.PU.L3YC.M24.Row14Conc B ω) : Row17Conc B ω := by
  obtain ⟨hN, h3, hq, hC⟩ := h
  refine ⟨hN, h3, fun b hb => ?_⟩
  obtain ⟨q, hq', hne⟩ := hq b hb
  refine ⟨q, ?_, hne⟩
  rw [commutator_pCore_map_eq, hC]
  exact hq'

theorem exists_pow_three_lift_of_surj {Γ Λ : Type} [Group Γ] [Group Λ] (f : Γ →* Λ)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) {x : Λ} (hx : x ^ 3 = 1) :
    ∃ g : Γ, g ^ 3 = 1 ∧ f g = x := by
  obtain ⟨h, rfl⟩ := hf x
  have hmem : h ^ 3 ^ 1 ∈ f.ker := by
    rw [MonoidHom.mem_ker, pow_one, map_pow, hx]
  obtain ⟨g₂, hg₂, g₃, -, hsplit, hg₃⟩ := exists_two_three_split (m := 1) hk hmem
  refine ⟨g₃, by simpa using hg₃, ?_⟩
  have h2 : f g₂ = 1 := hg₂
  calc f g₃ = f g₂ * f g₃ := by rw [h2, one_mul]
    _ = f h := by rw [← map_mul, ← hsplit]

theorem not_five_dvd (a : ℕ) : ¬ (5 : ℕ) ∣ 2 ^ a * 168 := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
    omega
  · omega

theorem Row17Conc.map {X X' : Type} [Group X] [Group X'] (f : X →* X')
    (hf : Function.Injective f) {B : Subgroup X} {ω : X} (h : Row17Conc B ω) :
    Row17Conc (B.map f) (f ω) := by
  obtain ⟨hN, h3, hNI⟩ := h
  let ι : ↥B ≃* ↥(B.map f) := Subgroup.equivMapOfInjective B f hf
  have hpc : (CFSG.pCore 2 ↥B).map ι.toMonoidHom = CFSG.pCore 2 ↥(B.map f) :=
    CFSG.pCore_map_iso 2 ι
  have hcomp : (B.map f).subtype.comp ι.toMonoidHom = f.comp B.subtype := by
    ext x; rfl
  have hpm : (CFSG.pCore 2 ↥(B.map f)).map (B.map f).subtype =
      ((CFSG.pCore 2 ↥B).map B.subtype).map f := by
    rw [← hpc, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  refine ⟨?_, ?_, ?_⟩
  · have hfwd : ∀ ω₀ ∈ Subgroup.normalizer (B : Set X), ∀ b ∈ B,
        f ω₀ * f b * (f ω₀)⁻¹ ∈ B.map f :=
      fun ω₀ hω₀ b hb => ⟨ω₀ * b * ω₀⁻¹, (Subgroup.mem_normalizer_iff.mp hω₀ b).mp hb, by simp⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hfwd ω hN b hb
    · intro hy
      obtain ⟨b2, hb2, hb2'⟩ := hy
      have hωinv : ω⁻¹ ∈ Subgroup.normalizer (B : Set X) := (Subgroup.normalizer _).inv_mem hN
      refine ⟨ω⁻¹ * b2 * ω, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hωinv b2).mp hb2
        simpa using this
      · have : y = (f ω)⁻¹ * (f ω * y * (f ω)⁻¹) * f ω := by group
        rw [this, ← hb2']
        simp
  · rw [← map_pow, h3, map_one]
  · intro b'' hb''
    obtain ⟨b, hb, rfl⟩ := hb''
    obtain ⟨q, hq, hne⟩ := hNI b hb
    refine ⟨f q, ?_, ?_⟩
    · rw [hpm, ← Subgroup.map_commutator]
      exact ⟨q, hq, rfl⟩
    · intro heq
      apply hne
      apply hf
      simp only [map_mul, map_inv]
      simpa using heq

theorem nonempty_modO2_equiv_map {Λ Γ : Type} [Group Λ] [Group Γ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (B : Subgroup Λ) :
    Nonempty (ModO2 B ≃* ModO2 (B.map φ)) := by
  let ε : ↥B ≃* ↥(B.map φ) := Subgroup.equivMapOfInjective B φ hφ
  have hε : (CFSG.pCore 2 ↥B).map ε.toMonoidHom = CFSG.pCore 2 ↥(B.map φ) :=
    CFSG.pCore_map_iso 2 ε
  exact ⟨QuotientGroup.congr _ _ ε hε⟩

theorem nonempty_modO2_equiv_of_eq {Γ : Type} [Group Γ] {A B : Subgroup Γ} (h : A = B) :
    Nonempty (ModO2 A ≃* ModO2 B) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem isPSL_modO2_map {Λ Γ : Type} [Group Λ] [Group Γ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (B : Subgroup Λ) (h : IsPSL 3 2 1 (ModO2 B)) :
    IsPSL 3 2 1 (ModO2 (B.map φ)) := by
  obtain ⟨e⟩ := nonempty_modO2_equiv_map φ hφ B
  exact IsPSL.of_mulEquiv e h

theorem isPSL_modO2_of_map {Λ Γ : Type} [Group Λ] [Group Γ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (B : Subgroup Λ) (h : IsPSL 3 2 1 (ModO2 (B.map φ))) :
    IsPSL 3 2 1 (ModO2 B) := by
  obtain ⟨e⟩ := nonempty_modO2_equiv_map φ hφ B
  exact IsPSL.of_mulEquiv e.symm h

theorem isPGroup_ker_comp_equiv {A B C : Type} [Group A] [Group B] [Group C] (e : A ≃* B)
    (g : B →* C) (hg : IsPGroup 2 g.ker) : IsPGroup 2 (g.comp e.toMonoidHom).ker := by
  intro x
  have hx : g (e x) = 1 := x.2
  obtain ⟨k, hk⟩ := hg ⟨e x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (e x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  show (x : A) ^ 2 ^ k = 1
  apply e.injective
  rw [map_pow, map_one]
  exact h1

theorem exists_surj_ker_pGroup_of_equiv {A B' C : Type} [Group A] [Group B'] [Group C]
    (e : A ≃* B') (θ : B' →* C) (hθk : IsPGroup 2 θ.ker) :
    ∃ φ : A →* ↥θ.range, Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  refine ⟨θ.rangeRestrict.comp e.toMonoidHom, ?_, ?_⟩
  · exact (MonoidHom.rangeRestrict_surjective θ).comp e.surjective
  · exact isPGroup_ker_comp_equiv e θ.rangeRestrict (by rw [MonoidHom.ker_rangeRestrict]; exact hθk)

theorem exists_surj_ker_pGroup_of_embed {X Y C : Type} [Group X] [Group Y] [Group C]
    {Lb K : Subgroup X} (hLbK : Lb ≤ K) (φ : ↥K →* Y) (hφ : Function.Injective φ) {B : Subgroup Y}
    (hB : B = (Lb.subgroupOf K).map φ) (θ : ↥B →* C) (hθk : IsPGroup 2 θ.ker) :
    ∃ φ' : ↥Lb →* ↥θ.range, Function.Surjective φ' ∧ IsPGroup 2 φ'.ker := by
  have e₂ : ↥Lb ≃* ↥B :=
    ((Subgroup.subgroupOfEquivOfLe hLbK).symm.trans
      (Subgroup.equivMapOfInjective (Lb.subgroupOf K) φ hφ)).trans
      (MulEquiv.subgroupCongr hB.symm)
  exact exists_surj_ker_pGroup_of_equiv e₂ θ hθk

end CFSG.Quasithin.Stellmacher.L3YC
