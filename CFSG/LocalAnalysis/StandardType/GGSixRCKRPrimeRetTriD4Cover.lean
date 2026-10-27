module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTriD4Core

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
open CFSG.LieType.Steinberg.TwistedD4 (nd)

theorem rckReturnedCover_triD4_of_pinnedFrame
    {τ : Tag} (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) {h : ℕ}
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (SK : LangSetup Tag.D4 GGL 5) (hSKq : SK.D.q = 2 ^ h) (hSKΦ : SK.D.Φ = triPsi h 1)
    (hfr : RCKTriD4PinnedFrameAt S (componentRoots (rootCharHom a) i) h 1 SK.D.n)
    (hA : RCKTriD4Model h) :
    RCKReturnedCover S a i h (fun M g => ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F →+* F), TriField F σ g ∧ M = triD4Universal F σ) := by
  classical
  obtain ⟨hY, Ξ, ι, hstep₀, hbij, hiform, hroot, htor⟩ := hfr
  obtain ⟨F, _, _, σ, hF, ιA, β₀, hιA, hιArange, hβ₀, hβ₀long, hβ₀pos, hβ₀neg⟩ := hA
  have hstep : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i)),
      (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) =
        SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) := by
    intro y hy
    rw [hstep₀ y hy]
    simp only [LangDatum.step, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hSKΦ]
  have hFinF : Finite F :=
    (Nat.card_pos_iff.1 (by rw [hF.2.1]; positivity)).2
  have hh1 : 1 ≤ h := hF.1
  have hq2 : 2 ≤ 2 ^ h := le_self_pow (by norm_num) (by omega)
  have hcard3 : Nat.card F = 2 ^ (3 * h) := by
    rw [hF.2.1, ← pow_mul, mul_comm]
  have hcharF : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 3 * h) Nat.prime_two (by omega) hcard3
  have hMfin : Finite (triD4Universal F σ).K := by
    have : Finite (ModGL Tag.D4 F) := finite_modGL
    have : Finite (adjointGroup Tag.D4 F) := Subtype.finite
    exact Subtype.finite
  have hMperf : Group.IsPerfect (triD4Universal F σ).K := by
    exact CFSG.LieType.Steinberg.TwistedD4.twistedGroup_isPerfect_of_card hq2 hF.2.1 hF.2.2
  have hModd : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (triD4Universal F σ).K := by
    have hσ3 : ∀ c : F, σ (σ (σ c)) = c :=
      CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hF.2.1 hF.2.2
    intro E hEG hEfin π hπ hker hodd
    obtain ⟨s, hs, -, -⟩ :=
      CFSG.SectionRank.triality_even_central_odd_extension_splitting (σ := σ) hσ3 hπ hker hodd
    exact ⟨s, hs⟩
  have hMcenter : Subgroup.center (triD4Universal F σ).K = ⊥ := by
    exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
      hq2 hF.2.1 hF.2.2
  obtain ⟨hmodelK, hΓK⟩ := retTriD4_model_eq hSKΦ hMperf ιA hιArange
  have hperfK : Group.IsPerfect ↥SK.D.model := by
    have := hMperf
    rw [hmodelK, ← MonoidHom.range_comp]
    exact Group.IsPerfect.range ((MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp ιA)
  obtain ⟨hmodel, hRi'⟩ := retTriD4_component_eq S a i hs SK hY Ξ hstep
  have hRi := hRi' hperfK
  have hRU : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ GGL (componentRoots (rootCharHom a) i) := by
    rw [hRi]
    exact inf_le_left
  let κ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →* ModGL Tag.D4 GGL :=
    (adjointGroup Tag.D4 GGL).subtype.comp (Ξ.toMonoidHom.comp (Subgroup.inclusion hRU))
  have hκ : ∀ x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      κ x = (Ξ ⟨x, hRU x.2⟩ : ModGL Tag.D4 GGL) := fun _ => rfl
  have hκinj : Function.Injective κ := by
    intro x y hxy
    have h1 : (Ξ ⟨x, hRU x.2⟩ : ModGL Tag.D4 GGL) =
        (Ξ ⟨y, hRU y.2⟩ : ModGL Tag.D4 GGL) := by
      rw [← hκ x, ← hκ y]
      exact hxy
    have h2 : (⟨x, hRU x.2⟩ : ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i))) =
        ⟨y, hRU y.2⟩ := Ξ.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (fun z : ↥(rootSpan τ GGL
      (componentRoots (rootCharHom a) i)) => (z : ModGL τ GGL)) h2)
  have hκrange : κ.range = SK.Γ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hxmem : (x : ModGL τ GGL) ∈
          rootSpan τ GGL (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
        rw [← hRi]
        exact x.2
      have hxmodel : (x : ModGL τ GGL) ∈ S.D.model := hxmem.2
      have hxΞ : (Ξ ⟨x, hRU x.2⟩ : ModGL Tag.D4 GGL) ∈ SK.D.model :=
        (hmodel x.1 (hRU x.2)).1 hxmodel
      rw [hΓK, hκ]
      exact hxΞ
    · intro t ht
      rw [hΓK] at ht
      have htadj : t ∈ adjointGroup Tag.D4 GGL := ht.1
      obtain ⟨y, hy⟩ := Ξ.surjective ⟨t, htadj⟩
      have hyval : (Ξ y : ModGL Tag.D4 GGL) = t := by rw [hy]
      have hymodel : (y : ModGL τ GGL) ∈ S.D.model := by
        refine (hmodel y.1 y.2).2 ?_
        have h2 : (Ξ (⟨y.1, y.2⟩ : ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i))) :
            ModGL Tag.D4 GGL) = t := hyval
        rw [h2]
        exact ht
      have hyR : (y : ModGL τ GGL) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
        rw [hRi]
        exact ⟨y.2, hymodel⟩
      refine ⟨⟨y.1, hyR⟩, ?_⟩
      rw [hκ]
      exact hyval
  have hconj_apply : ∀ a : ModGL Tag.D4 GGL,
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom a = SK.D.g0⁻¹ * a * SK.D.g0 := by
    intro a
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp
  have hκrange' : κ.range = ιA.range.map (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by
    rw [hκrange, hΓK, hmodelK]
  obtain ⟨φ, hφ⟩ : ∃ φ : (triD4Universal F σ).K →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      ∀ x, κ (φ x) = SK.D.g0⁻¹ * ιA x * SK.D.g0 := by
    have hex : ∀ x : (triD4Universal F σ).K,
        ∃ r : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
          κ r = SK.D.g0⁻¹ * ιA x * SK.D.g0 := by
      intro x
      have hmem : SK.D.g0⁻¹ * ιA x * SK.D.g0 ∈ κ.range := by
        rw [hκrange']
        exact ⟨ιA x, ⟨x, rfl⟩, hconj_apply (ιA x)⟩
      obtain ⟨r, hr⟩ := hmem
      exact ⟨r, hr⟩
    let f : (triD4Universal F σ).K →
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := fun x => Classical.choose (hex x)
    have hf : ∀ x, κ (f x) = SK.D.g0⁻¹ * ιA x * SK.D.g0 :=
      fun x => Classical.choose_spec (hex x)
    let φ : (triD4Universal F σ).K →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      { toFun := f
        map_one' := by
          apply hκinj
          rw [map_one κ, hf 1, map_one ιA]
          simp
        map_mul' := by
          intro x y
          apply hκinj
          rw [map_mul κ, hf (x * y), hf x, hf y, map_mul ιA]
          group }
    exact ⟨φ, hf⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : κ (φ x) = κ (φ y) := by rw [hxy]
    rw [hφ x, hφ y] at h1
    have h2 : ιA x = ιA y := by
      have h3 := congrArg (fun t => SK.D.g0 * t * SK.D.g0⁻¹) h1
      simpa [mul_assoc] using h3
    exact hιA h2
  have hφsurj : Function.Surjective φ := by
    intro r
    have hmem : κ r ∈ κ.range := ⟨r, rfl⟩
    rw [hκrange'] at hmem
    obtain ⟨a, ha, har⟩ := hmem
    obtain ⟨x, rfl⟩ := ha
    refine ⟨x, ?_⟩
    apply hκinj
    rw [hφ x]
    have h4 : (MulAut.conj SK.D.g0⁻¹).toMonoidHom (ιA x) = κ r := har
    rw [hconj_apply] at h4
    exact h4
  have hcenterR : Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨w, rfl⟩ := hφsurj z
    have hwK : w ∈ Subgroup.center (triD4Universal F σ).K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply hφinj
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.1 hz) (φ k)
    rw [hMcenter] at hwK
    rw [Subgroup.mem_bot] at hwK
    rw [hwK, map_one φ]
  have htorusK : ∀ b ∈ S.D.torus, ∃ t ∈ SK.D.torus,
      (∀ (x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i),
        κ ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ = t * κ x * t⁻¹) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, rckRootVal t (ι γ) = rckRootVal b γ := by
    intro b hb
    have hbtorus : b ∈ torusGroup τ GGL :=
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
    obtain ⟨t, ht, hbt, hroot⟩ := htor b hbtorus
    have htK : t ∈ SK.D.torus := by
      refine retTriD4_torus_mem S a i hs SK hSKΦ hY Ξ hstep hb ht ?_
      intro y hy hby
      exact hbt y hy hby
    refine ⟨t, htK, ?_, hroot⟩
    intro x hx
    have hby : b * (x : ModGL τ GGL) * b⁻¹ ∈
        rootSpan τ GGL (componentRoots (rootCharHom a) i) := by
      have hx' : b * (x : ModGL τ GGL) * b⁻¹ ∈
          rootSpan τ GGL (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
        rw [← hRi]
        exact hx
      exact hx'.1
    have hframe := hbt x.1 (hRU x.2) hby
    rw [hκ ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩, hκ x]
    exact hframe
  have hdiag : ∀ b ∈ S.D.torus, GGPsiInnerDiag (triD4Universal F σ).D
      ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subtype.comp φ) b := by
    intro b hb
    obtain ⟨t, ht, hbt, -⟩ := htorusK b hb
    have hbmodel : b ∈ S.D.model := S.D.torus_le_model hb
    have hbtorus : b ∈ torusGroup τ GGL :=
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
    have hbNspan : b ∈ Subgroup.normalizer
        (rootSpan τ GGL (componentRoots (rootCharHom a) i) : Set (ModGL τ GGL)) :=
      CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
        (S := componentRoots (rootCharHom a) i) (fun γ hγ => hγ.1.1) hbtorus
    have hbNmodel : b ∈ Subgroup.normalizer (S.D.model : Set (ModGL τ GGL)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact S.D.model.mul_mem (S.D.model.mul_mem hbmodel hx) (S.D.model.inv_mem hbmodel)
      · intro hx
        have h := S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.inv_mem hbmodel) hx) hbmodel
        simpa [mul_assoc] using h
    have hbN : b ∈ Subgroup.normalizer
        (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ GGL)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hx' : x ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
          rw [← hRi]
          exact hx
        rw [hRi]
        exact ⟨(Subgroup.mem_normalizer_iff.1 hbNspan x).1 hx'.1,
          (Subgroup.mem_normalizer_iff.1 hbNmodel x).1 hx'.2⟩
      · intro hx
        have hx' : b * x * b⁻¹ ∈
            rootSpan τ GGL (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
          rw [← hRi]
          exact hx
        rw [hRi]
        exact ⟨(Subgroup.mem_normalizer_iff.1 hbNspan x).2 hx'.1,
          (Subgroup.mem_normalizer_iff.1 hbNmodel x).2 hx'.2⟩
    have hbR : ∀ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        b * y * b⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      fun y hy => (Subgroup.mem_normalizer_iff.1 hbN y).1 hy
    have hbRinv : ∀ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        b⁻¹ * y * b ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      fun y hy => (Subgroup.mem_normalizer_iff''.1 hbN y).1 hy
    have htmodel : t ∈ SK.D.model := SK.D.torus_le_model ht
    have htΓ : t ∈ SK.Γ := by rw [hΓK]; exact htmodel
    have htκ : t ∈ κ.range := by rw [hκrange]; exact htΓ
    obtain ⟨r, hr⟩ := htκ
    obtain ⟨x₀, hx₀⟩ := hφsurj r
    have hagree : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        b * x * b⁻¹ = r * x * r⁻¹ := by
      intro x hx
      have hbx : b * x * b⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := hbR x hx
      have hrx : r * x * r⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ r.2 hx) (Subgroup.inv_mem _ r.2)
      have e1 : κ ⟨b * x * b⁻¹, hbx⟩ = t * κ ⟨x, hx⟩ * t⁻¹ := hbt ⟨x, hx⟩ hbx
      have e2 : κ ⟨r * x * r⁻¹, hrx⟩ = t * κ ⟨x, hx⟩ * t⁻¹ := by
        rw [show (⟨r * x * r⁻¹, hrx⟩ :
          ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) =
            ⟨r, r.2⟩ * ⟨x, hx⟩ * ⟨r⁻¹, Subgroup.inv_mem _ r.2⟩ from rfl]
        rw [map_mul, map_mul]
        have hr' : κ (⟨r, r.2⟩ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = t := hr
        have hrinv : κ (⟨r⁻¹, Subgroup.inv_mem _ r.2⟩ :
            ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = t⁻¹ := by
          show κ ((⟨r, r.2⟩ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))⁻¹) = t⁻¹
          rw [map_inv, hr']
        rw [hr', hrinv]
      have hEq : (⟨b * x * b⁻¹, hbx⟩ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) =
          ⟨r * x * r⁻¹, hrx⟩ := by
        apply hκinj
        rw [e1, e2]
      exact congrArg Subtype.val hEq
    refine ⟨r⁻¹, ⟨x₀⁻¹, ?_⟩, ?_⟩
    · show ((φ x₀⁻¹ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ GGL) =
        ((r⁻¹ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ GGL)
      rw [map_inv, hx₀]
    · intro γ hγ
      refine ⟨1, ?_, ?_⟩
      · simp [ggTorus]
      · intro z hz
        simp only [one_mul, inv_one, mul_one]
        have hzR : (φ z : ModGL τ GGL) ∈
            rationalComponent S.ρ S.Γ (rootCharHom a) i := (φ z).2
        have hyR : b⁻¹ * (φ z : ModGL τ GGL) * b ∈
            rationalComponent S.ρ S.Γ (rootCharHom a) i := hbRinv _ hzR
        have key : b * (b⁻¹ * (φ z : ModGL τ GGL) * b) * b⁻¹ =
            r * (b⁻¹ * (φ z : ModGL τ GGL) * b) * r⁻¹ := hagree _ hyR
        have key' : (φ z : ModGL τ GGL) =
            r * b⁻¹ * (φ z : ModGL τ GGL) * b * r⁻¹ := by
          calc (φ z : ModGL τ GGL) =
              b * (b⁻¹ * (φ z : ModGL τ GGL) * b) * b⁻¹ := by group
            _ = r * (b⁻¹ * (φ z : ModGL τ GGL) * b) * r⁻¹ := key
            _ = r * b⁻¹ * (φ z : ModGL τ GGL) * b * r⁻¹ := by group
        calc (b * (↑(r⁻¹) : ModGL τ GGL))⁻¹ * (φ z : ModGL τ GGL) *
              (b * (↑(r⁻¹) : ModGL τ GGL))
            = r * b⁻¹ * (φ z : ModGL τ GGL) * b * r⁻¹ := by
              simp only [Subgroup.coe_inv]
              group
          _ = (φ z : ModGL τ GGL) := key'.symm
  have hcharGGL : CharP GGL 2 := inferInstance
  have hιρ : ∀ γ ∈ componentRoots (rootCharHom a) i, ι (S.ρ γ) = SK.ρ (ι γ) := by
    intro γ hγ
    have hγroot : IsRoot τ γ := hγ.1.1
    have hstab : S.ρ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
      have hne : {s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] ''
          componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i}.Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have h0 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 0 := by
          unfold componentOrbitLength
          rw [hemp, Nat.sInf_empty]
        rw [hs] at h0
        exact Nat.one_ne_zero h0
      have himg : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) i := by
        rw [← hs]
        exact (Nat.sInf_mem hne).2
      simpa using himg
    have hρΨ : S.ρ γ ∈ componentRoots (rootCharHom a) i := by
      rw [← hstab]
      exact Set.mem_image_of_mem _ hγ
    have hριroot : IsRoot Tag.D4 (ι (S.ρ γ)) := hbij.mapsTo hρΨ
    have hιγroot : IsRoot Tag.D4 (ι γ) := hbij.mapsTo hγ
    have hRroot : IsRoot Tag.D4 (SK.ρ (ι γ)) := (SK.frob.isRoot_iff (ι γ)).2 hιγroot
    apply rootSubgroup_injective_of_isRoot (L := GGL) hριroot hRroot
    ext w
    constructor
    · intro hw
      have hwadj : w ∈ adjointGroup Tag.D4 GGL := rootSubgroup_le_adjointGroup _ hw
      obtain ⟨y, hyw⟩ := Ξ.surjective ⟨w, hwadj⟩
      have hw' : w = (Ξ y : ModGL Tag.D4 GGL) := by rw [hyw]
      rw [hw'] at hw ⊢
      have hyU : (y : ModGL τ GGL) ∈ rootSubgroup τ GGL (S.ρ γ) :=
        (hroot (S.ρ γ) hρΨ (y : ModGL τ GGL) y.2).2 hw
      rw [← S.frob.map_rootSubgroup γ hγroot] at hyU
      obtain ⟨u, hu, hstepu⟩ := hyU
      have huSpan : u ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i) :=
        rootSubgroup_le_rootSpan hγ hu
      have hstep' : (Ξ (⟨S.D.step u, hY u huSpan⟩ :
          ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i))) : ModGL Tag.D4 GGL) =
          SK.D.step (Ξ ⟨u, huSpan⟩) := hstep u huSpan
      have hyEq : (⟨S.D.step u, hY u huSpan⟩ :
          ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i))) = y :=
        Subtype.ext hstepu
      have hwstep : (Ξ y : ModGL Tag.D4 GGL) = SK.D.step (Ξ ⟨u, huSpan⟩) := by
        rw [← hyEq]
        exact hstep'
      rw [hwstep, ← SK.frob.map_rootSubgroup (ι γ) hιγroot]
      exact ⟨Ξ ⟨u, huSpan⟩, (hroot γ hγ u huSpan).1 hu, rfl⟩
    · intro hw
      have hwadj : w ∈ adjointGroup Tag.D4 GGL := rootSubgroup_le_adjointGroup _ hw
      obtain ⟨y, hyw⟩ := Ξ.surjective ⟨w, hwadj⟩
      have hw' : w = (Ξ y : ModGL Tag.D4 GGL) := by rw [hyw]
      rw [hw'] at hw ⊢
      rw [← SK.frob.map_rootSubgroup (ι γ) hιγroot] at hw
      obtain ⟨b, hb, hstepb⟩ := hw
      have hbadj : b ∈ adjointGroup Tag.D4 GGL := rootSubgroup_le_adjointGroup _ hb
      obtain ⟨uA, huA⟩ := Ξ.surjective ⟨b, hbadj⟩
      have huAU : (uA : ModGL τ GGL) ∈ rootSubgroup τ GGL γ := by
        refine (hroot γ hγ (uA : ModGL τ GGL) uA.2).2 ?_
        rw [huA]
        exact hb
      have huSpan : (uA : ModGL τ GGL) ∈
          rootSpan τ GGL (componentRoots (rootCharHom a) i) :=
        rootSubgroup_le_rootSpan hγ huAU
      have hstep' : (Ξ (⟨S.D.step (uA : ModGL τ GGL), hY (uA : ModGL τ GGL) huSpan⟩ :
          ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i))) : ModGL Tag.D4 GGL) =
          SK.D.step (Ξ uA) := hstep (uA : ModGL τ GGL) huSpan
      have hb_eq : SK.D.step (Ξ uA) = (Ξ y : ModGL Tag.D4 GGL) := by
        rw [huA]
        exact hstepb
      have hEq : (⟨S.D.step (uA : ModGL τ GGL), hY (uA : ModGL τ GGL) huSpan⟩ :
          ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i))) = y := by
        apply Ξ.injective
        apply Subtype.ext
        rw [hstep', hb_eq]
      have hyU : (y : ModGL τ GGL) ∈ rootSubgroup τ GGL (S.ρ γ) := by
        rw [← S.frob.map_rootSubgroup γ hγroot]
        exact ⟨(uA : ModGL τ GGL), huAU, congrArg Subtype.val hEq⟩
      exact (hroot (S.ρ γ) hρΨ (y : ModGL τ GGL) y.2).1 hyU
  have hκφ : κ.comp φ = (MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp ιA := by
    refine MonoidHom.ext fun x => ?_
    show κ (φ x) = (MulAut.conj SK.D.g0⁻¹).toMonoidHom (ιA x)
    rw [hφ x, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp
  have hstep_conj : ∀ x : ModGL Tag.D4 GGL,
      SK.D.step (SK.D.g0⁻¹ * x * SK.D.g0) = SK.D.g0⁻¹ * SK.D.Φ x * SK.D.g0 := by
    intro x
    rw [LangDatum.step, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_mul, map_inv, SK.D.lang]
    group
  have hfixmap : (SK.D.Φ.eqLocus (MonoidHom.id (ModGL Tag.D4 GGL))).map
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom = SK.D.step.eqLocus (MonoidHom.id _) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show SK.D.step (SK.D.g0⁻¹ * x * SK.D.g0) = SK.D.g0⁻¹ * x * SK.D.g0
      rw [hstep_conj, hx]
      rfl
    · intro hy
      refine ⟨SK.D.g0 * y * SK.D.g0⁻¹, ?_, ?_⟩
      · show SK.D.Φ (SK.D.g0 * y * SK.D.g0⁻¹) = SK.D.g0 * y * SK.D.g0⁻¹
        rw [map_mul, map_mul, map_inv, SK.D.lang]
        have hy' : SK.D.n * SK.D.Φ y * SK.D.n⁻¹ = y := hy
        calc (SK.D.g0 * SK.D.n) * SK.D.Φ y * (SK.D.g0 * SK.D.n)⁻¹
            = SK.D.g0 * (SK.D.n * SK.D.Φ y * SK.D.n⁻¹) * SK.D.g0⁻¹ := by group
          _ = SK.D.g0 * y * SK.D.g0⁻¹ := by rw [hy']
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have htriPsi_eq : triPsi h 1 =
      frobTwistGL TwistTag.D4.tag GGL 2 h (diagramMap TwistTag.D4 GGL) := by
    rw [triPsi, pow_one]
    rfl
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : ∀ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ → ∃ μ : GGLˣ, ∀ c : GGL,
      diagramMap TwistTag.D4 GGL * pinnedX TwistTag.D4.tag GGL γ c *
        (diagramMap TwistTag.D4 GGL)⁻¹ =
        pinnedX TwistTag.D4.tag GGL (permLattice TwistTag.D4.perm γ) (μ * c) := by
    intro γ hγ
    obtain ⟨ε, hε, hX⟩ := diagramMap_conj_pinnedX (t := TwistTag.D4) (K := GGL) hγ
    refine ⟨Units.mkOfMulEqOne ε ε (by rw [mul_comm]; exact hε), fun c => ?_⟩
    rw [Units.val_mkOfMulEqOne]
    exact hX c
  have hperm2 : TwistTag.D4.perm (nd 2) = nd 2 := by decide
  have hδperm : permLattice TwistTag.D4.perm (Pi.single (nd 2) 1) = Pi.single (nd 2) 1 := by
    funext j
    simp only [permLattice, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq, hperm2]
  have hpermneg : permLattice TwistTag.D4.perm (-(Pi.single (nd 2) 1)) =
      -(Pi.single (nd 2) 1) := by
    funext j
    simp only [permLattice, Function.comp_apply, Pi.neg_apply, Pi.single_apply,
      Equiv.symm_apply_eq, hperm2]
  have hfixroot : ∀ δ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 δ →
      permLattice TwistTag.D4.perm δ = δ →
      (rootSubgroup Tag.D4 GGL δ).map (triPsi h 1) = rootSubgroup Tag.D4 GGL δ := by
    intro δ hδ hδperm
    show (rootSubgroup TwistTag.D4.tag GGL δ).map
        (frobTwistGL TwistTag.D4.tag GGL 2 h (diagramMap TwistTag.D4 GGL)) =
      rootSubgroup TwistTag.D4.tag GGL δ
    rw [map_frobTwistGL_rootSubgroup_of_conj (p := 2) (e := h)
      (Q := diagramMap TwistTag.D4 GGL) (θ := permLattice TwistTag.D4.perm) hQ hδ, hδperm]
  have hfixγ : (rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1)).map (triPsi h 1) =
      rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1) :=
    hfixroot _ (isRoot_single Tag.D4 (nd 2)) hδperm
  have hfixγneg : (rootSubgroup Tag.D4 GGL (-(Pi.single (nd 2) 1))).map (triPsi h 1) =
      rootSubgroup Tag.D4 GGL (-(Pi.single (nd 2) 1)) :=
    hfixroot _ (isRoot_neg_single Tag.D4 (nd 2)) hpermneg
  have hpair : ∃ γ₀ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ₀ ∧
      ∃ z₀ ∈ adjointGroup Tag.D4 GGL,
        ((rootSubgroup Tag.D4 GGL γ₀).map (MulAut.conj z₀).toMonoidHom).map SK.D.step =
            (rootSubgroup Tag.D4 GGL γ₀).map (MulAut.conj z₀).toMonoidHom ∧
        ((rootSubgroup Tag.D4 GGL (-γ₀)).map (MulAut.conj z₀).toMonoidHom).map SK.D.step =
            (rootSubgroup Tag.D4 GGL (-γ₀)).map (MulAut.conj z₀).toMonoidHom ∧
        ((triD4Universal F σ).D.rootGroup β₀).map (κ.comp φ) =
          (rootSubgroup Tag.D4 GGL γ₀).map (MulAut.conj z₀).toMonoidHom ⊓
            SK.D.step.eqLocus (MonoidHom.id _) ∧
        ((triD4Universal F σ).D.rootGroup (-β₀)).map (κ.comp φ) =
          (rootSubgroup Tag.D4 GGL (-γ₀)).map (MulAut.conj z₀).toMonoidHom ⊓
            SK.D.step.eqLocus (MonoidHom.id _) := by
    have hcomp : SK.D.step.comp (MulAut.conj SK.D.g0⁻¹).toMonoidHom =
        (MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp SK.D.Φ := by
      refine MonoidHom.ext fun x => ?_
      show SK.D.step (SK.D.g0⁻¹ * x * SK.D.g0) = SK.D.g0⁻¹ * SK.D.Φ x * SK.D.g0
      exact hstep_conj x
    have hstab : ∀ δ : Fin Tag.D4.rank → ℤ,
        (rootSubgroup Tag.D4 GGL δ).map (triPsi h 1) = rootSubgroup Tag.D4 GGL δ →
        ((rootSubgroup Tag.D4 GGL δ).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom).map SK.D.step =
          (rootSubgroup Tag.D4 GGL δ).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by
      intro δ hδ
      calc ((rootSubgroup Tag.D4 GGL δ).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom).map SK.D.step
          = (rootSubgroup Tag.D4 GGL δ).map
              (SK.D.step.comp (MulAut.conj SK.D.g0⁻¹).toMonoidHom) := by
            rw [Subgroup.map_map]
        _ = (rootSubgroup Tag.D4 GGL δ).map
              ((MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp SK.D.Φ) := by rw [hcomp]
        _ = ((rootSubgroup Tag.D4 GGL δ).map SK.D.Φ).map
              (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by rw [← Subgroup.map_map]
        _ = ((rootSubgroup Tag.D4 GGL δ).map (triPsi h 1)).map
              (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by rw [hSKΦ]
        _ = (rootSubgroup Tag.D4 GGL δ).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by
            rw [hδ]
    refine ⟨Pi.single (nd 2) 1, isRoot_single Tag.D4 (nd 2), SK.D.g0⁻¹,
      Subgroup.inv_mem _ SK.D.g0_mem, ?_, ?_, ?_, ?_⟩
    · exact hstab _ hfixγ
    · exact hstab _ hfixγneg
    · rw [hκφ, ← Subgroup.map_map, hβ₀pos,
        Subgroup.map_inf _ _ (MulAut.conj SK.D.g0⁻¹).toMonoidHom
          (MulAut.conj SK.D.g0⁻¹).injective, ← hSKΦ, hfixmap]
    · rw [hκφ, ← Subgroup.map_map, hβ₀neg,
        Subgroup.map_inf _ _ (MulAut.conj SK.D.g0⁻¹).toMonoidHom
          (MulAut.conj SK.D.g0⁻¹).injective, ← hSKΦ, hfixmap]
      rfl
  refine ⟨triD4Universal F σ, φ, Tag.D4, SK, κ, ι, ?_, ?_, hφsurj, ?_, hMfin, hMperf, hModd,
    ?_, hdiag, Or.inl rfl, ?_, ?_, hκrange, hbij, ?_, hiform, ?_, htorusK⟩
  ·
    refine ⟨F, inferInstance, hFinF, σ, ?_, rfl⟩
    rw [hs, mul_one]
    exact hF
  ·
    refine Or.inr ⟨F, inferInstance, hFinF, σ, ?_, rfl⟩
    rw [hs, mul_one]
    exact hF
  ·
    rw [MonoidHom.ker_eq_bot φ hφinj]
    exact bot_le
  ·
    obtain ⟨γ₀, hγ₀, z₀, hz₀, hA, hB, hC, hD⟩ := hpair
    exact ⟨β₀, hβ₀, hβ₀long, γ₀, hγ₀, z₀, hz₀, hA, hB, hC, hD⟩
  ·
    rw [hs, mul_one]
    exact hSKq
  ·
    rw [MonoidHom.ker_eq_bot κ hκinj, hcenterR]
  ·
    intro γ hγ
    exact map_neg ι γ
  ·
    intro γ hγ
    rw [hs, Function.iterate_one]
    exact hιρ γ hγ

end CFSG.StandardType.RCKRP

end
