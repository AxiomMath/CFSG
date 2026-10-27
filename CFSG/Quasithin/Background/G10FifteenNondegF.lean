module

public import CFSG.Quasithin.Background.G10FifteenNondegE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_alternatingGroup_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem exists_PK {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I) {x : GLV V}
    (hx : x ∈ X)
    (hsplit : ∀ h ∈ normalClosure Γ L, ∃ r ∈ centralizerOn (normalClosure Γ L) I,
      ∃ r' ∈ centralizerOn (normalClosure Γ L) (conjSub x I), h = r * r') :
    ∃ PK : Sylow 2 ↥(restrictRange (normalClosure Γ L) I hI.1),
      ∀ s ∈ PK, ∃ d ∈ X ⊓ normalClosure Γ L, ∀ u : ↥I,
        (((s : ↥(restrictRange (normalClosure Γ L) I hI.1)) : GLV ↥I) u : V) = d (u : V) := by
  have hx2 : x * x = 1 := hyp.X_sq x hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxH : ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
    normalClosure_normal Γ L x (hyp.X_le hx)
  have hI' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  obtain ⟨T, PH, hXT, hP, hcomm⟩ := hyp.exists_sylow_H
  have hS : IsSylowTwoOf (T ⊓ normalClosure Γ L) (normalClosure Γ L) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.mpr ⟨PH, hP⟩
  set R' := centralizerOn (normalClosure Γ L) (conjSub x I) with hR'
  have hR'le : R' ≤ normalClosure Γ L := fun r hr => hr.1
  have hnorm : (R'.subgroupOf (normalClosure Γ L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hR'le]
    intro h k hh hk
    exact centralizerOn_normal hI' k hk h hh
  obtain ⟨PR, hPR⟩ := CFSG.QuasithinUnique.RankOneRecog.exists_sylow_inf_of_subnormal hS hR'le
    hnorm.isSubnormal
  let π' : ↥R' →* ↥(restrictRange (normalClosure Γ L) I hI.1) :=
    (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict.comp (Subgroup.inclusion hR'le)
  have hπ' : Function.Surjective π' := by
    rintro ⟨_, ⟨⟨h, hh⟩, rfl⟩⟩
    obtain ⟨r, hr, r', hr', rfl⟩ := hsplit h hh
    refine ⟨⟨r', hr'⟩, ?_⟩
    apply Subtype.ext
    have h1 : restrictHom (normalClosure Γ L) I hI.1 ⟨r, hr.1⟩ = 1 := by
      rw [restrictHom_eq_one_iff]
      exact hr.2
    show restrictHom (normalClosure Γ L) I hI.1 ⟨r', hR'le hr'⟩ =
      restrictHom (normalClosure Γ L) I hI.1 ⟨r * r', hh⟩
    have : (⟨r * r', hh⟩ : ↥(normalClosure Γ L)) = ⟨r, hr.1⟩ * ⟨r', hR'le hr'⟩ := rfl
    rw [this, map_mul, h1, one_mul]
  refine ⟨PR.mapSurjective hπ', ?_⟩
  intro s hs
  have hs' : s ∈ (PR : Subgroup ↥R').map π' := hs
  obtain ⟨t, ht, rfl⟩ := hs'
  have htmem : (t : GLV V) ∈ (T ⊓ normalClosure Γ L) ⊓ R' := by
    have : (t : GLV V) ∈ (PR : Subgroup ↥R').map R'.subtype := ⟨t, ht, rfl⟩
    rw [hPR] at this
    exact this
  obtain ⟨⟨htT, htH⟩, htR'⟩ := htmem
  set z : GLV V := x * (t : GLV V) * x⁻¹ with hz
  have hzR : z ∈ centralizerOn (normalClosure Γ L) I := by
    have := centralizerOn_conj hxH (t : GLV V) htR'
    rwa [conjSub_conjSub_of_sq hx2] at this
  have hzT : z ∈ T := T.mul_mem (T.mul_mem (hXT hx) htT) (T.inv_mem (hXT hx))
  have hzH : z ∈ normalClosure Γ L := hxH _ htH
  have h1 := hcomm x hx z⁻¹ ⟨T.inv_mem hzT, (normalClosure Γ L).inv_mem hzH⟩
  have hxz : x * z * x⁻¹ = (t : GLV V) := by
    rw [hz]
    have hxx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
    calc x * (x * (t : GLV V) * x⁻¹) * x⁻¹ = (x * x) * (t : GLV V) * (x⁻¹ * x⁻¹) := by group
      _ = (t : GLV V) := by rw [hx2, hxx']; simp
  have hd : z⁻¹ * (t : GLV V) = (x * z⁻¹ * x⁻¹ * (z⁻¹)⁻¹)⁻¹ := by
    calc z⁻¹ * (t : GLV V) = z⁻¹ * (x * z * x⁻¹) := by rw [hxz]
      _ = (x * z⁻¹ * x⁻¹ * (z⁻¹)⁻¹)⁻¹ := by group
  refine ⟨z⁻¹ * (t : GLV V), ?_, fun u => ?_⟩
  · rw [hd]
    exact (X ⊓ normalClosure Γ L).inv_mem h1
  · have htu : (t : GLV V) (u : V) ∈ I := hI.1 _ htH u u.2
    have h2 : z⁻¹ ((t : GLV V) (u : V)) = (t : GLV V) (u : V) :=
      ((centralizerOn (normalClosure Γ L) I).inv_mem hzR).2 _ htu
    show (t : GLV V) (u : V) = z⁻¹ ((t : GLV V) (u : V))
    exact h2.symm


theorem split_structure (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hSQT : SectionSQTInput)
    (h1212 : G1212Stmt) (hSimple : InspectSimple) (hOuter : InspectOuter)
    (hSylow : InspectSylow) (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hc : IsCompl I (conjSub x I)) {i : V}
    (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hFT : FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)
    (hnd : NondegOn B I) (hnle : ¬ I ≤ perp B v₁) :
    (∀ h ∈ normalClosure Γ L, ∃ r ∈ centralizerOn (normalClosure Γ L) I,
        ∃ r' ∈ centralizerOn (normalClosure Γ L) (conjSub x I), h = r * r') ∧
      Module.finrank (ZMod 2) ↥I = 4 ∧ Nat.card ↥(stabilizerOf X I) = 4 ∧
      X ⊓ normalClosure Γ L = stabilizerOf X I ∧
      ∃ (φ : ↥(restrictRange (normalClosure Γ L) I hI.1) ≃* ↥(alternatingGroup (Fin 5)))
        (ψ : ↥I ≃ₗ[ZMod 2] ↥(permCore 5)),
        ∀ (k : ↥(restrictRange (normalClosure Γ L) I hI.1)) (u w : ↥I),
          w = (k : GLV ↥I) u → (ψ w : Fin 5 → ZMod 2) =
            permAct ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ u) := by
  have hYI := invariant_stabilizerOf X I
  obtain ⟨f, hD, hsimp, hqK⟩ := hyp.nondeg_data hq hSQT h1212 hSimple hI hi hi0 hFT hnd hnle
  rcases hyp.dichotomy hI hx hc hsimp with hR' | hsplit
  · exfalso
    refine hyp.faithful_absurd hq hSQT h1212 hSimple hOuter hI hfix hx hne hi hi0 hFT hnd hnle ?_
    rw [faithfulOn_iff]
    intro k hk hkI
    have h1 := centralizerOn_conj (normalClosure_normal Γ L x (hyp.X_le hx)) (U := I) k ⟨hk, hkI⟩
    have h2 := hR' _ h1
    calc k = x⁻¹ * (x * k * x⁻¹) * x := by group
      _ = 1 := by rw [h2]; group
  · obtain ⟨PK, hPK⟩ := hyp.exists_PK hI hx hsplit
    have hQ : ∀ s ∈ PK, ((s : ↥(restrictRange (normalClosure Γ L) I hI.1)) : GLV ↥I) ∈
        restrictRange (stabilizerOf X I) I hYI := by
      intro s hs
      obtain ⟨d, hd, hdu⟩ := hPK s hs
      refine ⟨⟨d, hd.1, hI.1.conjSub_eq hd.2⟩, ?_⟩
      apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      exact (hdu u).symm
    obtain ⟨h4, hQ4, φ, ψ, hφψ⟩ := hSylow ↥I f _ _ _ _ hD hqK PK hQ
    have hYinj : Function.Injective (restrictHom (stabilizerOf X I) I hYI) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      rw [restrictHom_eq_one_iff] at ha
      apply Subtype.ext
      exact (faithfulOn_iff.1 (hyp.faithfulOn_stabilizerOf h10 h11 h12 hI hfix hx hne)) a a.2 ha
    have hYcard : Nat.card ↥(stabilizerOf X I) = 4 := by
      rw [← hQ4]
      exact Nat.card_congr (MonoidHom.ofInjective hYinj).toEquiv
    have hKcard : Nat.card ↥(restrictRange (normalClosure Γ L) I hI.1) = 60 := by
      rw [Nat.card_congr φ.toEquiv]
      exact card_alternatingGroup_five
    have hPKcard : Nat.card ↥(PK : Subgroup ↥(restrictRange (normalClosure Γ L) I hI.1)) = 4 := by
      rw [Sylow.card_eq_multiplicity PK, hKcard]
      have : (60 : ℕ).factorization 2 = 2 := by
        rw [Nat.factorization_def _ Nat.prime_two]
        decide +kernel
      rw [this]
      norm_num
    have hXHinv : Invariant (X ⊓ normalClosure Γ L) I := hI.1.mono inf_le_right
    have hle : (PK : Subgroup ↥(restrictRange (normalClosure Γ L) I hI.1)).map
        (restrictRange (normalClosure Γ L) I hI.1).subtype ≤
        (restrictHom (X ⊓ normalClosure Γ L) I hXHinv).range := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨d, hd, hdu⟩ := hPK s hs
      refine ⟨⟨d, hd⟩, ?_⟩
      apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      exact (hdu u).symm
    have hc1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (restrictRange (normalClosure Γ L) I hI.1).subtype_injective,
      hPKcard] at hc1
    have hc2 : Nat.card ↥(restrictHom (X ⊓ normalClosure Γ L) I hXHinv).range ≤
        Nat.card ↥(X ⊓ normalClosure Γ L) :=
      Nat.card_le_card_of_surjective
        (restrictHom (X ⊓ normalClosure Γ L) I hXHinv).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    have hc3 : 4 ≤ Nat.card ↥(X ⊓ normalClosure Γ L) := le_trans hc1 hc2
    have hXH : X ⊓ normalClosure Γ L = stabilizerOf X I := by
      refine Subgroup.eq_of_le_of_card_ge (fun d hd => ⟨hd.1, hI.1.conjSub_eq hd.2⟩) ?_
      rw [hYcard]
      exact hc3
    exact ⟨hsplit, h4, hYcard, hXH, φ, ψ, hφψ⟩

end G108Hyp

end G11

end CFSG.Quasithin
