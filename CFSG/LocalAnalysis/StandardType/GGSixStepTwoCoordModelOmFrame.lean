module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOm
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmMain
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmExcl

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)

namespace CoordOm

section Transport

variable {H G : Type} [Group H] [Group G] {Ω : Subgroup H} {φ : ↥Ω →* G}

theorem map_centralizer_set (hφ : Function.Injective φ) (S : Set ↥Ω) :
    (Subgroup.centralizer S).map φ = φ.range ⊓ Subgroup.centralizer (φ '' S) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hy s hs]
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, fun s hs => hφ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hy _ ⟨s, hs, rfl⟩

theorem isComponentOf_transport_set (hφ : Function.Injective φ) (S : Set ↥Ω)
    {L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer (φ '' S))) :
    IsComponentOf ((L₁.comap φ).map Ω.subtype) (Ω ⊓ Subgroup.centralizer (Ω.subtype '' S)) ∧
      (L₁.comap φ).map φ = L₁ := by
  rw [← map_centralizer_set hφ S] at hL₁
  obtain ⟨h1, h2⟩ := isComponentOf_comap_of_injective φ hφ hL₁
  have h3 := isComponentOf_map_of_injective Ω.subtype Ω.subtype_injective h1
  rw [map_centralizer_set Ω.subtype_injective, Subgroup.range_subtype] at h3
  exact ⟨h3, h2⟩

theorem image_comap_eq {E : Subgroup G} (hE : E ≤ φ.range) :
    φ '' ((E.comap φ : Subgroup ↥Ω) : Set ↥Ω) = (E : Set G) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hy
    obtain ⟨g, rfl⟩ := hE hy
    exact ⟨g, hy, rfl⟩

theorem card_inf_centralizer_le_of_transport [Finite G] (hφ : Function.Injective φ)
    {A : Subgroup H} {Bs : Subgroup G} (hAΩ : A ≤ Ω)
    (hAB : ∀ g : ↥Ω, (g : H) ∈ A ↔ φ g ∈ Bs) {L₁ : Subgroup G} (hL₁ : L₁ ≤ φ.range) :
    Nat.card (A ⊓ Subgroup.centralizer (((L₁.comap φ).map Ω.subtype : Subgroup H) : Set H) :
      Subgroup H) ≤ Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) := by
  classical
  have hmem : ∀ c : ↥(A ⊓ Subgroup.centralizer
      (((L₁.comap φ).map Ω.subtype : Subgroup H) : Set H)),
      φ ⟨c, hAΩ (Subgroup.mem_inf.mp c.2).1⟩ ∈ Bs ⊓ Subgroup.centralizer (L₁ : Set G) := by
    intro c
    obtain ⟨hcA, hcC⟩ := Subgroup.mem_inf.mp c.2
    refine Subgroup.mem_inf.mpr ⟨(hAB _).mp hcA, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    obtain ⟨g, rfl⟩ := hL₁ hl
    have h1 := Subgroup.mem_centralizer_iff.mp hcC (g : H) ⟨g, hl, rfl⟩
    have h2 : g * (⟨c, hAΩ hcA⟩ : ↥Ω) = ⟨c, hAΩ hcA⟩ * g := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  refine Nat.card_le_card_of_injective (fun c => ⟨_, hmem c⟩) fun c c' hcc => ?_
  have h0 := congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G)) => (z : G)) hcc
  have h1 := hφ h0
  have h2 : (c : H) = c' := congrArg (fun z : ↥Ω => (z : H)) h1
  exact Subtype.ext h2

end Transport

section Moves

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def FrameMoves {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) (O : Subgroup (ZMod p)ˣ) : Prop :=
  ∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ), (∀ i, η i ∈ O) → ∏ i, η i = 1 →
    ∃ w ∈ orthDerived Q ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)), ∀ s : Fin r → ZMod p,
      w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun i => (η i : ZMod p) * s (π i))

end Moves

end CoordOm

@[expose] def GGOmFrameMoveInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ Q : QuadraticForm K V, (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) →
    ∀ A : Subgroup (V ≃ₗ[K] V), A ≤ orthDerived Q → (∀ a ∈ A, a ^ p = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A) →
      ∃ (r : ℕ) (F : SevOm.Frame Q p A r),
        CoordOm.FrameMoves F (CoordSpNs.galSigns p (Nat.card K))

@[expose] def GGOmFrameCompInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ Q : QuadraticForm K V, (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) →
    ∀ A : Subgroup (V ≃ₗ[K] V), A ≤ orthDerived Q →
      (∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A) →
    ∀ (r : ℕ) (F : SevOm.Frame Q p A r), 4 ≤ r →
      CoordOm.FrameMoves F (CoordSpNs.galSigns p (Nat.card K)) →
    ∀ (L : Subgroup (V ≃ₗ[K] V)) (β : Fin r → ZMod p), β ≠ 0 →
      IsComponentOf L (orthDerived Q ⊓ Subgroup.centralizer {F.ι (ofAdd β)}) →
      Nat.card (A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2 →
        (∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
          ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → F.ι (ofAdd s) ∈ L) ∨
        (∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧
          (∀ i, ε i ∈ CoordSpNs.galSigns p (Nat.card K)) ∧
          (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
          ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
            F.ι (ofAdd s) ∈ L)

@[expose] def GGOmFrameShapeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ Q : QuadraticForm K V, (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) →
    ∀ A : Subgroup (V ≃ₗ[K] V), A ≤ orthDerived Q →
      (∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A) →
    ∀ (r : ℕ) (F : SevOm.Frame Q p A r), 4 ≤ r →
      CoordOm.FrameMoves F (CoordSpNs.galSigns p (Nat.card K)) →
    ∀ (E J : Subgroup (V ≃ₗ[K] V)), E ≤ A →
      IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V))) →
      Nat.card (A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 3 →
        StepTwoToral.GGStepTwoCoordShape p r (CoordSpNs.galSigns p (Nat.card K)) F.ι E

theorem ggOmCoordInput_of_frame (hmove : GGOmFrameMoveInput) (hcomp : GGOmFrameCompInput)
    (hshape : GGOmFrameShapeInput) : GGOmCoordInput := by
  intro G _ _ K _ _ _ V _ _ _ p _ hp2 Q hnd hT φ hφ Bs hBφ hBel hcard hmaxG
  classical
  have hp : p.Prime := Fact.out
  set A : Subgroup (V ≃ₗ[K] V) := (Bs.comap φ).map (orthDerived Q).subtype with hAdef
  have hAΩ : A ≤ orthDerived Q := Subgroup.map_subtype_le _
  have hAB : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ A ↔ φ g ∈ Bs := by
    intro g
    constructor
    · rintro ⟨y, hy, hyg⟩
      have : y = g := Subtype.ext hyg
      rw [← this]
      exact hy
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : φ (y ^ p) = 1 := by rw [map_pow]; exact hBel.2 _ hy
    have h2 : y ^ p = 1 := hφ (h1.trans (map_one φ).symm)
    rw [← map_pow, h2, map_one]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    have h1 : φ (y * y') = φ (y' * y) := by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBel hy hy'
    exact congrArg Subtype.val (hφ h1)
  have hAmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine (hAB ⟨g, hg⟩).mpr (hmaxG _ (Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩) ?_)
    · obtain ⟨c, rfl⟩ := hBφ hy
      have h1 := hgc c ((hAB c).mpr hy)
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext h1.symm)
    · rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥(orthDerived Q)) ^ p = 1 := Subtype.ext (by simpa using hgp)
      rw [h1, map_one]
  obtain ⟨r, F, hF⟩ := hmove K V p hp2 Q hnd hT A hAΩ hApow hAcomm hAmax
  have hcardA : Nat.card A = Nat.card Bs := by
    rw [hAdef, Subgroup.card_map_of_injective (orthDerived Q).subtype_injective]
    conv_rhs => rw [← Subgroup.map_comap_eq_self hBφ]
    rw [Subgroup.card_map_of_injective hφ]
  have hcA : Nat.card A = p ^ r := by
    rw [← F.range, Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hr4 : 4 ≤ r := by
    by_contra h
    have hlt : p ^ r < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (hcard.trans (hcardA.symm.trans hcA).le) (not_le.mpr hlt)
  set ι₀ : Multiplicative (Fin r → ZMod p) →* ↥(orthDerived Q) :=
    F.ι.codRestrict (orthDerived Q) (fun s => hAΩ (F.mem s)) with hι₀
  set ι : Multiplicative (Fin r → ZMod p) →* G := φ.comp ι₀ with hιdef
  have hιinj : Function.Injective ι :=
    hφ.comp fun s s' h => F.inj (congrArg Subtype.val h)
  have hιrange : ι.range = Bs := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact (hAB (ι₀ s)).mp (F.mem s)
    · intro hy
      obtain ⟨g, rfl⟩ := hBφ hy
      obtain ⟨s, hs⟩ := F.exists_eq ((hAB g).mpr hy)
      refine ⟨s, ?_⟩
      simp only [hιdef, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hs
  refine ⟨r, ι, hιinj, hιrange, fun π η hη hprod => ?_,
    fun b L₁ hb hb1 hL₁ hcardL β hβ => ?_, fun E J hE hJ hcardJ => ?_⟩
  ·
    obtain ⟨w, hw, hws⟩ := hF π η hη hprod
    obtain ⟨hwΩ, hwN⟩ := Subgroup.mem_inf.mp hw
    set w' : ↥(orthDerived Q) := ⟨w, hwΩ⟩ with hw'
    have hW : φ w' ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨g, rfl⟩ := hBφ hh
        have hgA := (hAB g).mpr hh
        have h1 : ((w' * g * w'⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ A :=
          (Subgroup.mem_normalizer_iff.mp hwN _).mp hgA
        rw [← map_inv, ← map_mul, ← map_mul]
        exact (hAB _).mp h1
      · intro hh
        obtain ⟨g, hg⟩ := hBφ hh
        have hgA := (hAB g).mpr (hg ▸ hh)
        have h2 : ((w'⁻¹ * g * w' : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ A := by
          refine (Subgroup.mem_normalizer_iff.mp hwN _).mpr ?_
          have e : w * ((w'⁻¹ * g * w' : ↥(orthDerived Q)) : V ≃ₗ[K] V) * w⁻¹ =
              (g : V ≃ₗ[K] V) := by
            show w * (w⁻¹ * (g : V ≃ₗ[K] V) * w) * w⁻¹ = g
            group
          rw [e]
          exact hgA
        have h3 : h = φ (w'⁻¹ * g * w') := by
          rw [map_mul, map_mul, map_inv, hg]
          group
        rw [h3]
        exact (hAB _).mp h2
    refine ⟨φ w', Subgroup.mem_inf.mpr ⟨⟨w', rfl⟩, hW⟩, fun s => ?_⟩
    simp only [hιdef, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show w⁻¹ * F.ι (ofAdd s) * w = F.ι _
    exact hws s
  ·
    have hβ0 : β ≠ 0 := fun h0 => hb1 (by rw [← hβ, h0, ofAdd_zero, map_one])
    have hL₁' : IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer (φ '' {ι₀ (ofAdd β)})) := by
      rw [Set.image_singleton]
      exact hβ ▸ hL₁
    obtain ⟨hLc, -⟩ := CoordOm.isComponentOf_transport_set hφ {ι₀ (ofAdd β)} hL₁'
    rw [Set.image_singleton] at hLc
    have hL₁r : L₁ ≤ φ.range := hL₁.1.trans inf_le_left
    have hcardL' :=
      (CoordOm.card_inf_centralizer_le_of_transport hφ hAΩ hAB hL₁r).trans hcardL
    rcases hcomp K V p hp2 Q hnd hT A hAΩ hAmax r F hr4 hF _ β hβ0 hLc hcardL' with
      ⟨j, j', hz, hL⟩ | ⟨k, c, ε, hc, hε, hβε, hL⟩
    · refine Or.inl ⟨j, j', hz, fun s hj hj' => ?_⟩
      obtain ⟨g, hg, hgs⟩ := hL s hj hj'
      have e : g = ι₀ (ofAdd s) := Subtype.ext hgs
      rw [e] at hg
      exact hg
    · refine Or.inr ⟨k, c, ε, hc, hε, hβε, fun s hk hs => ?_⟩
      obtain ⟨g, hg, hgs⟩ := hL s hk hs
      have e : g = ι₀ (ofAdd s) := Subtype.ext hgs
      rw [e] at hg
      exact hg
  ·
    have hEr : E ≤ φ.range := hE.trans hBφ
    have hJ' : IsComponentOf J
        (φ.range ⊓ Subgroup.centralizer
          (φ '' ((E.comap φ : Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)))) := by
      rw [CoordOm.image_comap_eq hEr]
      exact hJ
    obtain ⟨hJc, -⟩ := CoordOm.isComponentOf_transport_set hφ _ hJ'
    rw [← Subgroup.coe_map] at hJc
    have hJr : J ≤ φ.range := hJ.1.trans inf_le_left
    have hcardJ' :=
      (CoordOm.card_inf_centralizer_le_of_transport hφ hAΩ hAB hJr).trans hcardJ
    have hEA : (E.comap φ).map (orthDerived Q).subtype ≤ A := by
      rintro _ ⟨g, hg, rfl⟩
      exact (hAB g).mpr (hE hg)
    have hmemE : ∀ s, ι (ofAdd s) ∈ E → F.ι (ofAdd s) ∈ (E.comap φ).map (orthDerived Q).subtype :=
      fun s hs => ⟨ι₀ (ofAdd s), hs, rfl⟩
    rcases hshape K V p hp2 Q hnd hT A hAΩ hAmax r F hr4 hF _ _ hEA hJc hcardJ' with
      ⟨k, hk⟩ | ⟨j, j', ε, hε, hal⟩
    · exact Or.inl ⟨k, fun s hs => hk s (hmemE s hs)⟩
    · exact Or.inr ⟨j, j', ε, hε, fun s hs => hal s (hmemE s hs)⟩

end CFSG.StandardType
