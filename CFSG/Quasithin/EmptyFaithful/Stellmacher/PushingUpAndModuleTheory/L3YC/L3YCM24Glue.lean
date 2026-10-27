module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCM24Main

public section

namespace CFSG.Quasithin.Stellmacher.PU.L3YC.M24

open CFSG.Quasithin.A312M24 CFSG.QuasithinUnique
open scoped commutatorElement

section Conc

variable {X X' : Type} [Group X] [Group X']

@[expose] def Row14Conc (B : Subgroup X) (ω : X) : Prop :=
  ω ∈ Subgroup.normalizer (B : Set X) ∧ ω ^ 3 = 1 ∧
    (∀ b ∈ B, ∃ q ∈ (CFSG.pCore 2 ↥B).map B.subtype, ω * q * ω⁻¹ ≠ b * q * b⁻¹) ∧
    ⁅CFSG.pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆ = CFSG.pCore 2 ↥B

theorem Row14Conc.map (f : X →* X') (hf : Function.Injective f) {B : Subgroup X} {ω : X}
    (h : Row14Conc B ω) : Row14Conc (B.map f) (f ω) := by
  obtain ⟨hN, h3, hNI, hC⟩ := h
  let ι : ↥B ≃* ↥(B.map f) := Subgroup.equivMapOfInjective B f hf
  have hpc : (CFSG.pCore 2 ↥B).map ι.toMonoidHom = CFSG.pCore 2 ↥(B.map f) :=
    CFSG.pCore_map_iso 2 ι
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hfwd : ∀ ω₀ ∈ Subgroup.normalizer (B : Set X), ∀ b ∈ B, f ω₀ * f b * (f ω₀)⁻¹ ∈ B.map f :=
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
    obtain ⟨q, ⟨c, hc, rfl⟩, hq⟩ := hNI b hb
    refine ⟨f c, ⟨ι c, ?_, rfl⟩, ?_⟩
    · rw [← hpc]
      exact ⟨c, hc, rfl⟩
    · intro heq
      apply hq
      apply hf
      simp only [map_mul, map_inv]
      simpa using heq
  · have hι : Function.Surjective ι.toMonoidHom := ι.surjective
    rw [← hpc, ← Subgroup.map_top_of_surjective _ hι, ← Subgroup.map_commutator, hC]

end Conc

section Wrapper

theorem isExt_e2_psl_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsExt X (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y)) :
    IsExt X' (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  obtain ⟨V, hVn, hVE, hVQ⟩ := h
  refine ⟨V.map e.toMonoidHom, hVn.map _ e.surjective, ?_, ?_⟩
  · obtain ⟨e2⟩ := hVE
    exact ⟨(Subgroup.equivMapOfInjective V e.toMonoidHom e.injective).symm.trans e2⟩
  · exact IsPSL.of_mulEquiv (QuotientGroup.congr V (V.map e.toMonoidHom) e rfl) hVQ


theorem row14_M24 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {Y : Type} [Group Y] [Finite Y] {K B S₀ : Subgroup Y}
    (hK : Nonempty (↥K ≃* ↥CFSG.Blueprint.NativeSporadic.M24)) (hBK : B ≤ K)
    (hS₀ : IsSylowTwoOf S₀ K) (hS₀N : S₀ ≤ Subgroup.normalizer (B : Set Y)) (hperf : ⁅B, B⁆ = B)
    (hext : IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y)) :
    ∃ x ∈ K, Row14Conc B x := by
  obtain ⟨e⟩ := hK
  obtain ⟨φ, hφ⟩ := CFSG.Quasithin.E2P.SporB.exists_equiv_sylow e hS₀ m24_S_sylow'
  set Bk : Subgroup ↥K := B.subgroupOf K with hBk
  set B' : Subgroup G24 := Bk.map φ.toMonoidHom with hB'
  have hBkB : Bk.map K.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBK
  have hperfk : ⁅Bk, Bk⁆ = Bk := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hBkB, hperf]
  have hperf' : ⁅B', B'⁆ = B' := by
    rw [hB', ← Subgroup.map_commutator, hperfk]
  have hSk : S₀.subgroupOf K ≤ Subgroup.normalizer (Bk : Set ↥K) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.mp (hS₀N (Subgroup.mem_subgroupOf.mp hs)) (h : Y)
    simpa [hBk, Subgroup.mem_subgroupOf] using this
  have hN' : m24CtxE.S ≤ Subgroup.normalizer (B' : Set G24) := by
    rw [← hφ]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hh := Subgroup.mem_normalizer_iff.mp (hSk hs) (φ.symm h)
    have e1 : h ∈ B' ↔ φ.symm h ∈ Bk := by
      rw [hB']
      exact Subgroup.mem_map_equiv
    have e2 : φ.toMonoidHom s * h * (φ.toMonoidHom s)⁻¹ ∈ B' ↔ s * φ.symm h * s⁻¹ ∈ Bk := by
      rw [hB']
      refine Subgroup.mem_map_equiv.trans ?_
      simp
    rw [e1, e2]
    exact hh
  have hext' : IsExt ↥B' (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y) := by
    refine isExt_e2_psl_of_mulEquiv
      (((Subgroup.subgroupOfEquivOfLe hBK).symm).trans
        (Subgroup.equivMapOfInjective Bk φ.toMonoidHom φ.injective)) hext
  obtain ⟨ω', hω'⟩ := m24_row14_native hperf' hN' hext'
  have h1 := Row14Conc.map φ.symm.toMonoidHom φ.symm.injective hω'
  have hmap1 : B'.map φ.symm.toMonoidHom = Bk := by
    rw [hB', Subgroup.map_map]
    ext x
    simp
  rw [hmap1] at h1
  have h2 := Row14Conc.map K.subtype K.subtype_injective h1
  rw [hBkB] at h2
  exact ⟨((φ.symm ω' : ↥K) : Y), (φ.symm ω').2, h2⟩

end Wrapper

end CFSG.Quasithin.Stellmacher.PU.L3YC.M24
