module

public import CFSG.Quasithin.Background.RonanG1015Inputs
public import CFSG.Quasithin.Background.G10FifteenMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace RonanG1015

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Twist

variable {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem restrictHom_conj (hI : Invariant H I) {y : GLV V} (hyI : conjSub y I = I)
    (hyH : ∀ h ∈ H, y * h * y⁻¹ ∈ H) (h : ↥H) :
    restrictHom H I hI ⟨y * (h : GLV V) * y⁻¹, hyH h h.2⟩ =
      restrictEquiv y I hyI * restrictHom H I hI h * (restrictEquiv y I hyI)⁻¹ := by
  have hyiI : conjSub y⁻¹ I = I := by
    have := congrArg (conjSub y⁻¹) hyI
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have e1 : restrictEquiv (y * (h : GLV V) * y⁻¹) I (hI.conjSub_eq (hyH h h.2)) =
      restrictEquiv y I hyI * restrictEquiv (h : GLV V) I (hI.conjSub_eq h.2) *
        (restrictEquiv y I hyI)⁻¹ := by
    rw [← restrictEquiv_inv hyI hyiI]
    rw [restrictEquiv_mul (by rw [conjSub_mul, hI.conjSub_eq h.2, hyI]) hyiI,
      restrictEquiv_mul hyI (hI.conjSub_eq h.2)]
  exact e1

theorem conj_conj_comm {G : Type*} [Group G] {x y : G} (hxy : x * y = y * x) (h : G) :
    x * (y * h * y⁻¹) * x⁻¹ = y * (x * h * x⁻¹) * y⁻¹ := by
  have h1 : x * y * x⁻¹ = y := by rw [hxy]; group
  calc x * (y * h * y⁻¹) * x⁻¹
      = (x * y * x⁻¹) * (x * h * x⁻¹) * (x * y * x⁻¹)⁻¹ := by group
    _ = y * (x * h * x⁻¹) * y⁻¹ := by rw [h1]

theorem twistAut_cent {x y : GLV V} (hx2 : x * x = 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hyH : ∀ h ∈ H, y * h * y⁻¹ ∈ H) (hxy : x * y = y * x) (hI : Invariant H I)
    (hf : FaithfulOn H I) (hyI : conjSub y I = I) (k k' : ↥(restrictRange H I hI))
    (hk' : (k' : GLV ↥I) =
      restrictEquiv y I hyI * (k : GLV ↥I) * (restrictEquiv y I hyI)⁻¹) :
    ((twistAut hx2 hxH hI hf k' : ↥(restrictRange H I hI)) : GLV ↥I) =
      restrictEquiv y I hyI * ((twistAut hx2 hxH hI hf k : ↥(restrictRange H I hI)) : GLV ↥I) *
        (restrictEquiv y I hyI)⁻¹ := by
  obtain ⟨h, rfl⟩ := (faithfulEquiv hI hf).surjective k
  obtain ⟨h', rfl⟩ := (faithfulEquiv hI hf).surjective k'
  have hyh : y * (h : GLV V) * y⁻¹ ∈ H := hyH h h.2
  have hh' : h' = ⟨y * (h : GLV V) * y⁻¹, hyh⟩ := by
    apply restrictHom_injective_of_faithful hI hf
    rw [restrictHom_conj hI hyI hyH h]
    rw [coe_faithfulEquiv, coe_faithfulEquiv] at hk'
    exact hk'
  subst hh'
  rw [twistAut_apply, twistAut_apply, coe_faithfulEquiv, coe_faithfulEquiv]
  have hcomm : ((G11.conjAut hx2 hxH ⟨y * (h : GLV V) * y⁻¹, hyh⟩ : ↥H) : GLV V) =
      y * ((G11.conjAut hx2 hxH h : ↥H) : GLV V) * y⁻¹ := by
    rw [G11.coe_conjAut, G11.coe_conjAut]
    exact conj_conj_comm hxy (h : GLV V)
  have hcomm' : G11.conjAut hx2 hxH ⟨y * (h : GLV V) * y⁻¹, hyh⟩ =
      ⟨y * (G11.conjAut hx2 hxH h : GLV V) * y⁻¹, hyH _ (G11.conjAut hx2 hxH h).2⟩ :=
    Subtype.ext hcomm
  rw [hcomm']
  exact restrictHom_conj hI hyI hyH _

end Twist

section Package

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}

theorem twist_package_Q (hyp : G108Hyp B Γ v₁ W X X₀ L) {x : GLV V} (hx : x ∈ X)
    {I : Submodule (ZMod 2) V} (hI : Invariant (normalClosure Γ L) I)
    (hf : FaithfulOn (normalClosure Γ L) I) :
    ∃ (α : ↥(restrictRange (normalClosure Γ L) I hI) ≃* ↥(restrictRange (normalClosure Γ L) I hI))
      (P : Sylow 2 ↥(restrictRange (normalClosure Γ L) I hI)),
      (∀ s ∈ P, α s ∈ P) ∧ (∀ s, α (α s) = s) ∧
      (∀ s ∈ P, ∀ t ∈ P, (s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) ∧
      (∀ q ∈ restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I),
        ∀ k k' : ↥(restrictRange (normalClosure Γ L) I hI),
          (k' : GLV ↥I) = q * (k : GLV ↥I) * q⁻¹ →
            ((α k' : ↥(restrictRange (normalClosure Γ L) I hI)) : GLV ↥I) =
              q * ((α k : ↥(restrictRange (normalClosure Γ L) I hI)) : GLV ↥I) * q⁻¹) ∧
      ((∃ c : GLV ↥I, ∀ k : ↥(restrictRange (normalClosure Γ L) I hI),
          ((α k : ↥(restrictRange (normalClosure Γ L) I hI)) : GLV ↥I) =
            c * (k : GLV ↥I) * c⁻¹) → HIso (normalClosure Γ L) I (conjSub x I)) := by
  have hx2 : x * x = 1 := hyp.X_sq x hx
  have hxH : ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
    normalClosure_normal Γ L x (hyp.X_le hx)
  obtain ⟨T, PH, hXT, hP, hcomm⟩ := hyp.exists_sylow_H
  have hmem : ∀ h : ↥(normalClosure Γ L), h ∈ PH ↔ (h : GLV V) ∈ T := by
    intro h
    constructor
    · intro hh
      have : (h : GLV V) ∈
          (PH : Subgroup ↥(normalClosure Γ L)).map (normalClosure Γ L).subtype := ⟨h, hh, rfl⟩
      rw [hP] at this
      exact this.1
    · intro hh
      have : (h : GLV V) ∈ T ⊓ normalClosure Γ L := ⟨hh, h.2⟩
      rw [← hP] at this
      obtain ⟨h', hh', hh'eq⟩ := this
      have : h' = h := Subtype.ext hh'eq
      rw [← this]
      exact hh'
  have hsurj : Function.Surjective (restrictHom (normalClosure Γ L) I hI).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  set PK := PH.mapSurjective hsurj with hPK
  have hmemK : ∀ s : ↥(restrictRange (normalClosure Γ L) I hI), s ∈ PK ↔
      ∃ h ∈ PH, G11.faithfulEquiv hI hf h = s := by
    intro s
    constructor
    · intro hs
      have : s ∈ (PH : Subgroup ↥(normalClosure Γ L)).map
          (restrictHom (normalClosure Γ L) I hI).rangeRestrict := hs
      obtain ⟨h, hh, rfl⟩ := this
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h, hh, rfl⟩
  have hconjP : ∀ h ∈ PH, G11.conjAut hx2 hxH h ∈ PH := by
    intro h hh
    rw [hmem] at hh ⊢
    rw [G11.coe_conjAut]
    exact T.mul_mem (T.mul_mem (hXT hx) hh) (T.inv_mem (hXT hx))
  have hcX : ∀ h ∈ PH, ((h⁻¹ * G11.conjAut hx2 hxH h : ↥(normalClosure Γ L)) : GLV V) ∈ X := by
    intro h hh
    have hhT : (h : GLV V) ∈ T := (hmem h).1 hh
    have h1 := hcomm x hx (h : GLV V)⁻¹ ⟨T.inv_mem hhT, (normalClosure Γ L).inv_mem h.2⟩
    have h2 := X.inv_mem h1.1
    have : ((h⁻¹ * G11.conjAut hx2 hxH h : ↥(normalClosure Γ L)) : GLV V) =
        (x * (h : GLV V)⁻¹ * x⁻¹ * ((h : GLV V)⁻¹)⁻¹)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, G11.coe_conjAut]
      group
    rw [this]
    exact h2
  refine ⟨G11.twistAut hx2 hxH hI hf, PK, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨h, hh, rfl⟩ := (hmemK s).1 hs
    rw [G11.twistAut_apply]
    exact (hmemK _).2 ⟨_, hconjP h hh, rfl⟩
  · intro s
    obtain ⟨h, rfl⟩ := (G11.faithfulEquiv hI hf).surjective s
    rw [G11.twistAut_apply, G11.twistAut_apply, G11.conjAut_conjAut]
  · intro s hs t ht
    obtain ⟨h, hh, rfl⟩ := (hmemK s).1 hs
    obtain ⟨h', hh', rfl⟩ := (hmemK t).1 ht
    have e1 : (G11.faithfulEquiv hI hf h)⁻¹ *
        G11.twistAut hx2 hxH hI hf (G11.faithfulEquiv hI hf h) =
        G11.faithfulEquiv hI hf (h⁻¹ * G11.conjAut hx2 hxH h) := by
      rw [G11.twistAut_apply, map_mul, map_inv]
    have e2 : (G11.faithfulEquiv hI hf h')⁻¹ *
        G11.twistAut hx2 hxH hI hf (G11.faithfulEquiv hI hf h') =
        G11.faithfulEquiv hI hf (h'⁻¹ * G11.conjAut hx2 hxH h') := by
      rw [G11.twistAut_apply, map_mul, map_inv]
    rw [e1, e2]
    have hXc : ∀ a b : ↥(normalClosure Γ L), (a : GLV V) ∈ X → (b : GLV V) ∈ X →
        a * b = b * a := by
      intro a b ha hb
      apply Subtype.ext
      exact hyp.X_comm _ ha _ hb
    have hXs : ∀ a : ↥(normalClosure Γ L), (a : GLV V) ∈ X → a * a = 1 := by
      intro a ha
      apply Subtype.ext
      exact hyp.X_sq _ ha
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul, hXc _ _ (hcX h hh) (hcX h' hh')]
    · rw [← map_mul, hXs _ (hcX h hh), map_one]
  · intro q hq k k' hk'
    obtain ⟨⟨y, hy⟩, rfl⟩ := hq
    have hyX : y ∈ X := hy.1
    exact twistAut_cent hx2 hxH
      (fun h hh => normalClosure_normal Γ L y (hyp.X_le hyX) h hh) (hyp.X_comm x hx y hyX) hI hf
      hy.2 k k' hk'
  · rintro ⟨c, hc⟩
    exact G11.hiso_of_twist hx2 hxH hI hf c hc

theorem nondeg_data_free (hyp : G108Hyp B Γ v₁ W X X₀ L) (h1212 : G1212Stmt)
    (hSimple : InspectSimple) {I : Submodule (ZMod 2) V} (hI : G11.IrrPlus (normalClosure Γ L) I)
    {i : V} (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hFT : FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)
    (hnd : NondegOn B I) (hnle : ¬ I ≤ perp B v₁) :
    ∃ f : LinearMap.BilinForm (ZMod 2) ↥I,
      G121Data f (restrictRange (normalClosure Γ L) I hI.1 ⊔
          restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I))
        (restrictRange (normalClosure Γ L) I hI.1)
        (restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I)) ⟨i, hi.1⟩ ∧
      IsSimpleGroup ↥(restrictRange (normalClosure Γ L) I hI.1) := by
  obtain ⟨f, hD⟩ := hyp.apply_h1212 h1212 hI hi hi0 hFT hnd hnle
  exact ⟨f, hD, hSimple ↥I f _ _ _ _ hD⟩

theorem faithful_absurd_free (hyp : G108Hyp B Γ v₁ W X X₀ L) (h1212 : G1212Stmt)
    (hSimple : InspectSimple) (hOuter : InspectOuterQ) {I : Submodule (ZMod 2) V}
    (hI : G11.IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {i : V} (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hFT : FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)
    (hnd : NondegOn B I) (hnle : ¬ I ≤ perp B v₁)
    (hfaith : FaithfulOn (normalClosure Γ L) I) : False := by
  obtain ⟨f, hD, -⟩ := nondeg_data_free hyp h1212 hSimple hI hi hi0 hFT hnd hnle
  obtain ⟨α, P, hαP, hαα, hel, hcent, hreal⟩ := twist_package_Q hyp hx hI.1 hfaith
  obtain ⟨g, hg⟩ := hOuter ↥I f _ _ _ _ hD α P hαP hαα hel hcent
  exact hne (hfix x hx (hreal ⟨g, hg⟩))

theorem split_structure_free (hyp : G108Hyp B Γ v₁ W X X₀ L) (h1212 : G1212Stmt)
    (hSimple : InspectSimple) (hOuter : InspectOuterQ) (hSylow : InspectSylowFree)
    (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L) (h12 : G1012Concl Γ v₁ W X L)
    {I : Submodule (ZMod 2) V} (hI : G11.IrrPlus (normalClosure Γ L) I)
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
  obtain ⟨f, hD, hsimp⟩ := nondeg_data_free hyp h1212 hSimple hI hi hi0 hFT hnd hnle
  rcases hyp.dichotomy hI hx hc hsimp with hR' | hsplit
  · exfalso
    refine faithful_absurd_free hyp h1212 hSimple hOuter hI hfix hx hne hi hi0 hFT hnd hnle ?_
    rw [faithfulOn_iff]
    intro k hk hkI
    have h1 := G11.centralizerOn_conj (normalClosure_normal Γ L x (hyp.X_le hx)) (U := I) k
      ⟨hk, hkI⟩
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
    obtain ⟨h4, hQ4, φ, ψ, hφψ⟩ := hSylow ↥I f _ _ _ _ hD PK hQ
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
      exact G11.card_alternatingGroup_five
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

theorem III_of_nondeg_free (hyp : G108Hyp B Γ v₁ W X X₀ L) (h1212 : G1212Stmt)
    (hSimple : InspectSimple) (hOuter : InspectOuterQ) (hSylow : InspectSylowFree) (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : G11.IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hnd : NondegOn B I)
    (hL : L ≤ centralizerOn (normalClosure Γ L) (conjSub x I)) :
    ¬ Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧ NondegOn B I ∧
      ¬ FaithfulOn (normalClosure Γ L) I ∧ Module.finrank (ZMod 2) V = 8 ∧
      ∃ x ∈ X, conjSub x I ≠ I ∧
        normalClosure Γ L = L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
        Nat.card X = 8 ∧ X = (X ⊓ normalClosure Γ L) ⊔ Subgroup.zpowers x ∧
        I = commSpace L ⊤ ∧ IsA5Module L I ∧ conjSub x I = fixedSpace L := by
  have hx2 : x * x = 1 := hyp.X_sq x hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
  have hxH : ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
    normalClosure_normal Γ L x (hyp.X_le hx)
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hI' : G11.IrrPlus (normalClosure Γ L) (conjSub x I) := hyp.irrPlus_conj hI hx
  have hinv' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hn : ¬ HIso (normalClosure Γ L) I (conjSub x I) := fun h => hne (hfix x hx h)
  have hc := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
  obtain ⟨i, hi, hi0, hv, hY⟩ := hyp.exists_i h10 hI hfix hx hne
  have hFT := hyp.fullTransvections hI hfix hx hne hi hv
  have horth := hyp.conj_le_orthogonal h10 h11 h12 hI hfix hx hne hnd
  have hnle := hyp.not_le_perp_of_nondeg hi.1 hi0 hv hnd horth
  obtain ⟨hsplit, h4, hY4, hXH, φ, ψ, hφψ⟩ := split_structure_free hyp h1212 hSimple hOuter
    hSylow h10 h11 h12 hI hfix hx hne hc hi hi0 hFT hnd hnle
  obtain ⟨f, hD, hsimpK⟩ := nondeg_data_free hyp h1212 hSimple hI hi hi0 hFT hnd hnle
  have hsimpR' : IsSimpleGroup ↥(centralizerOn (normalClosure Γ L) (conjSub x I)) :=
    (R'Equiv hI.1 hc hsplit).isSimpleGroup
  have hLeq : L = centralizerOn (normalClosure Γ L) (conjSub x I) :=
    hyp.component_eq_of_le_simple (fun r hr => hyp.H_le hr.1) hsimpR' hL
  obtain ⟨l₀, hl₀L, hl₀1⟩ := hyp.exists_ne_one_mem_L
  have hLne : ∃ r ∈ centralizerOn (normalClosure Γ L) (conjSub x I), r ≠ 1 :=
    ⟨l₀, hL hl₀L, hl₀1⟩
  have hnoI : ∀ r ∈ centralizerOn (normalClosure Γ L) (conjSub x I), (∀ u ∈ I, r u = u) →
      r = 1 := fun r hr hu => eq_one_of_centralizes_compl hc hu hr.2
  have hmapL : L.map (MulAut.conj x).toMonoidHom = centralizerOn (normalClosure Γ L) I := by
    have h1 := map_conj_centralizerOn hx2 hxH (U := I)
    refine le_antisymm ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      exact h1.le ⟨l, hL hl, rfl⟩
    · intro r hr
      rw [← h1] at hr
      obtain ⟨t, ht, rfl⟩ := hr
      exact ⟨t, hLeq.symm.le ht, rfl⟩
  refine ⟨fun h => hn (h I (conjSub x I) hI hI'), selfDual_of_nondegOn hyp.toG101Hyp.isRefl
    hyp.H_isometry hnd, hnd, ?_, ?_, x, hx, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hf
    have hr : x * l₀ * x⁻¹ ∈ centralizerOn (normalClosure Γ L) I := by
      have := hmapL.le ⟨l₀, hl₀L, rfl⟩
      exact this
    have h1 : x * l₀ * x⁻¹ = 1 := faithfulOn_iff.1 hf _ hr.1 hr.2
    apply hl₀1
    calc l₀ = x⁻¹ * (x * l₀ * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  ·
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_conjSub] at h1
    omega
  ·
    rw [hmapL]
    refine le_antisymm (fun h hh => ?_) (sup_le (le_normalClosure Γ L) (fun r hr => hr.1))
    obtain ⟨r, hr, r', hr', rfl⟩ := hsplit h hh
    have hcomm := hyp.centralizers_comm hI.1 hx hc hr hr'
    rw [hcomm]
    exact Subgroup.mul_mem_sup (hLeq.symm.le hr') hr
  ·
    have hYX : stabilizerOf X I ≤ X := fun y hy => hy.1
    have hmul := Subgroup.relIndex_mul_card (stabilizerOf X I) X
    rw [inf_eq_left.2 hYX, hyp.relIndex_stabilizerOf_eq_two hI hfix hx hne, hY4] at hmul
    omega
  ·
    rw [hXH]
    refine le_antisymm (fun g hg => ?_) (sup_le (fun y hy => hy.1)
      ((Subgroup.zpowers_le).2 hx))
    rcases hyp.permutes hI hfix hx hne g hg with h1 | h1
    · exact Subgroup.mem_sup_left ⟨hg, h1⟩
    · have hy : x⁻¹ * g ∈ stabilizerOf X I := by
        refine ⟨X.mul_mem (X.inv_mem hx) hg, ?_⟩
        rw [conjSub_mul, h1, conjSub_inv_conjSub]
      have : g = x * (x⁻¹ * g) := by group
      rw [this, sup_comm]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers x) hy
  ·
    rw [hLeq]
    exact (commSpace_centralizerOn_conj hirr hinv' hc hLne).symm
  ·
    refine ⟨(MulEquiv.subgroupCongr hLeq).trans ((R'Equiv hI.1 hc hsplit).trans φ), ψ, ?_⟩
    intro γ v w hw
    exact hφψ _ v w (Subtype.ext hw)
  ·
    rw [hLeq]
    exact (fixedSpace_centralizerOn_conj hirr hinv' hc hLne hnoI).symm


theorem case2_free (hyp : G108Hyp B Γ v₁ W X X₀ L) (hOut : OuterGLInput) (h1212 : G1212Stmt)
    (hSimple : InspectSimple) (hOuter : InspectOuterQ) (hSylow : InspectSylowFree)
    (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L) (h12 : G1012Concl Γ v₁ W X L)
    {I : Submodule (ZMod 2) V} (hI : G11.IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : G1015Concl B Γ v₁ W X L := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  rcases hyp.isotropic_or_nondegOn hirr with hiso | hnd
  · obtain ⟨hII, h3⟩ := hyp.caseTwo_isotropic hOut h10 h11 h12 hI hfix hx hne hiso
    exact ⟨I, hI, Or.inr (hyp.caseOne_ii h10 h11 h12 hI hfix hx hne), Or.inr (Or.inl hII), h3⟩
  · have hc := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
    obtain ⟨i, hi, hi0, hv, hY⟩ := hyp.exists_i h10 hI hfix hx hne
    have hFT := hyp.fullTransvections hI hfix hx hne hi hv
    have horth := hyp.conj_le_orthogonal h10 h11 h12 hI hfix hx hne hnd
    have hnle := hyp.not_le_perp_of_nondeg hi.1 hi0 hv hnd horth
    obtain ⟨hsplit, -⟩ := split_structure_free hyp h1212 hSimple hOuter hSylow h10 h11 h12 hI
      hfix hx hne hc hi hi0 hFT hnd hnle
    have hx2 : x * x = 1 := hyp.X_sq x hx
    rcases hyp.component_le_centralizer hI.1 hx hc hsplit with hL | hL
    · have hIII := III_of_nondeg_free hyp h1212 hSimple hOuter hSylow h10 h11 h12 hI hfix hx hne
        hnd hL
      exact ⟨I, hI, Or.inr (hyp.caseOne_ii h10 h11 h12 hI hfix hx hne), Or.inr (Or.inr hIII),
        Or.inl (not_autAll_of_selfDual (hyp.two_lt_finrank hirr) hIII.2.1)⟩
    · have hI' : G11.IrrPlus (normalClosure Γ L) (conjSub x I) := hyp.irrPlus_conj hI hx
      have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) := hI'.isIrr hyp.fixedSpace_H
      have hfix' := hyp.fix_conj hI hfix hx hne
      have hne' := hyp.conj_conj_ne (I := I) hx hne
      have hnd' : NondegOn B (conjSub x I) :=
        nondegOn_conj hnd (hyp.isometry x (hyp.X_le hx))
      have hL' : L ≤ centralizerOn (normalClosure Γ L) (conjSub x (conjSub x I)) := by
        rw [conjSub_conjSub_of_sq hx2]
        exact hL
      have hIII := III_of_nondeg_free hyp h1212 hSimple hOuter hSylow h10 h11 h12 hI' hfix' hx
        hne' hnd' hL'
      exact ⟨conjSub x I, hI', Or.inr (hyp.caseOne_ii h10 h11 h12 hI' hfix' hx hne'),
        Or.inr (Or.inr hIII), Or.inl (not_autAll_of_selfDual (hyp.two_lt_finrank hirr') hIII.2.1)⟩

end Package

@[expose] def G1015Free : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      G1015Concl B Γ v₁ W X L

theorem g10_15_free (h10 : G1010Stmt) (h11 : G1011Stmt) (h12 : G1012Stmt) (h13 : G1013Stmt)
    (h1212 : G1212Stmt) (hOut : OuterGLInput) (hSimple : InspectSimple)
    (hOuter : InspectOuterQ) (hSylow : InspectSylowFree) : G1015Free := by
  intro V _ _ _ B Γ v₁ W X X₀ L hyp
  have h10' := h10 V B Γ v₁ W X X₀ L hyp
  have h11' := h11 V B Γ v₁ W X X₀ L hyp
  have h12' := h12 V B Γ v₁ W X X₀ L hyp
  have h13' := h13 V B Γ v₁ W X X₀ L hyp
  obtain ⟨I, hI, hfix⟩ := hyp.exists_irr_fixed
  by_cases hall : ∀ x ∈ X, conjSub x I = I
  · refine hyp.case1 h10' h11' h13' hI fun k hk u hu => ?_
    have := apply_mem_conjSub (g := k) hu
    rwa [hall k hk] at this
  · push Not at hall
    obtain ⟨x, hx, hne⟩ := hall
    exact case2_free hyp hOut h1212 hSimple hOuter hSylow h10' h11' h12' hI hfix hx hne



end RonanG1015

end CFSG.Quasithin
