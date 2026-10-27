module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo
import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameRecog
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCharSum
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameLift

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.Assembly
open CFSG.RankThree.Classical2


theorem exists_orthFrameCore_of_marking {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (hRig : GGLabelRigidInput) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {P : ℕ → LargeEvenLabel → Prop}
    (hProw : ∀ lab, P p lab → ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)
    (hmark : GGInnerDiagOnLabel P p Bs K)
    (hZK : ∀ lab, P p lab → GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → Subgroup.center ↥K = ⊥)
    (hact : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), ∃ b : ↥Bs, ggGamma K hN b ≠ 1) :
    ∃ lab : LargeEvenLabel, P p lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      ∃ Φ : OrthFrameCore p Bs K, Φ.r = lab.rank ∧ Nat.card Φ.F = 2 ^ lab.n ∧
        (QuadraticMap.polarBilin Φ.Q).Nondegenerate ∧ Module.finrank Φ.F Φ.V = 2 * Φ.r ∧
        (CFSG.GroupTheory.WeirSylow.IsPlusType Φ.Q ↔ lab.tag = .D) := by
  classical
  have hmarkK : GGInnerDiagOn Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  obtain ⟨lab, hΛ, hhas, R, hRgrp, I, F', θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  obtain ⟨hPlab, hnormK, hinner⟩ := hP
  have hrow := hProw lab hPlab
  have hZ : Subgroup.center ↥K = ⊥ := hZK lab hPlab hhas
  rcases lab with ⟨tag, rank, n⟩
  have hrow' : (tag = .D ∧ 4 ≤ rank ∧ Even rank ∧ p ∣ 2 ^ n + 1) ∨
      (tag = .twD ∧ 5 ≤ rank ∧ Odd rank ∧ p ∣ 2 ^ n + 1) := by
    simpa [ggRowP_EOmP, ggRowP_EOmM] using hrow
  have htag : tag = .D ∨ tag = .twD := by
    rcases hrow' with ⟨h, -, -, -⟩ | ⟨h, -, -, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hrank : 4 ≤ rank := by
    rcases hrow' with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩
    · exact h
    · omega
  have hpqA : p ∣ 2 ^ n + 1 := by
    rcases hrow' with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
    · exact h
    · exact h
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := GGInnerDiagOn.le_normalizer hmarkK
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, eQ, ρ,
    hcard, hring, hT, hdim, hplus, himage, hcompat0⟩ :=
    OrthKExactTwo.exists_quadratic_image_of_orthogonal_marking hRig hp2 hmarkK hBs hSC
      hΛ hhas htag hrank
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  letI : Nontrivial V := hNontrivial
  have hdim' : Module.finrank F V = 2 * rank := hdim
  have hcard' : Nat.card F = 2 ^ n := hcard
  let σ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(orthDerived Q) :=
    eQ.trans (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
  let EQ : Subgroup ↥(orthDerived Q) := ρ.range.map σ.toMonoidHom
  let β : ↥Bs →* ↥(orthDerived Q) := σ.toMonoidHom.comp ρ
  let A : Subgroup (V ≃ₗ[F] V) := EQ.map (orthDerived Q).subtype
  have hEimage : IsElemAbelian p EQ ∧
      ∀ g ∈ Subgroup.centralizer (EQ : Set ↥(orthDerived Q)), g ^ p = 1 → g ∈ EQ := by
    simpa [σ, EQ] using himage
  have hβrange : β.range = EQ := by
    simp only [β, EQ, MonoidHom.range_comp]
  have hβmem : ∀ b : ↥Bs, β b ∈ EQ := by
    intro b
    rw [← hβrange]
    exact ⟨b, rfl⟩
  have hβA : ∀ b : ↥Bs, (β b : V ≃ₗ[F] V) ∈ A := by
    intro b
    exact ⟨β b, hβmem b, rfl⟩
  have hβsurj : ∀ a ∈ A, ∃ b : ↥Bs, (β b : V ≃ₗ[F] V) = a := by
    rintro a ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp (by rw [hβrange]; exact hy)
    exact ⟨b, congrArg Subtype.val hb⟩
  let Z : Subgroup ↥K := Subgroup.center ↥K
  have hZ' : Z = ⊥ := hZ
  have hker : Z ≤ (MonoidHom.id ↥K).ker := by rw [hZ']; simp
  let κ' : ↥K ⧸ Z →* ↥K := QuotientGroup.lift Z (MonoidHom.id ↥K) hker
  have hκ'mk : ∀ z : ↥K, κ' (QuotientGroup.mk z) = z := by
    intro z
    simpa [κ'] using QuotientGroup.lift_mk' (N := Z) (φ := MonoidHom.id ↥K) hker z
  have hκ'inj : Function.Injective κ' := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hκ'mk, hκ'mk] at hxy
    rw [hxy]
  have hκ'surj : Function.Surjective κ' := fun z => ⟨QuotientGroup.mk z, hκ'mk z⟩
  let κe : (↥K ⧸ Z) ≃* ↥K := MulEquiv.ofBijective κ' ⟨hκ'inj, hκ'surj⟩
  have hκemk : ∀ z : ↥K, κe (QuotientGroup.mk z) = z := by
    intro z
    change κ' (QuotientGroup.mk z) = z
    exact hκ'mk z
  let e : ↥(orthDerived Q) ≃* ↥K := (κe.symm.trans σ).symm
  let ψ : ↥(orthDerived Q) →* G := K.subtype.comp e.toMonoidHom
  have heσ : ∀ x : ↥K ⧸ Z, e (σ x) = κe x := by
    intro x
    have h : (κe.symm.trans σ) (κe x) = σ x := by simp
    calc e (σ x) = e ((κe.symm.trans σ) (κe x)) := by rw [h]
      _ = κe x := MulEquiv.symm_apply_apply (κe.symm.trans σ) (κe x)
  have heβ : ∀ b : ↥Bs, e (β b) = κe (ρ b) := by
    intro b
    simpa [β] using heσ (ρ b)
  have he_mk : ∀ z : ↥K, e (σ (QuotientGroup.mk z)) = z := by
    intro z
    rw [heσ, hκemk]
  have hconj : ∀ (b : ↥Bs) (z : ↥K),
      ggGamma K hN b z = κe (ρ b) * z * (κe (ρ b))⁻¹ := by
    intro b z
    have h1 : σ (QuotientGroup.mk (ggGamma K hN b z)) =
        MulAut.conj (β b) (σ (QuotientGroup.mk z)) := by
      have h := congrArg (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
        (hcompat0 b z)
      simpa [σ, β, MulAut.conj_apply] using h
    have h2 := congrArg e h1
    simpa [MulAut.conj_apply, heβ, he_mk] using h2
  have hcompat : ∀ (b : ↥Bs) (y : ↥(orthDerived Q)),
      ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹ := by
    intro b y
    have hL : e (β b * y * (β b)⁻¹) = κe (ρ b) * e y * (κe (ρ b))⁻¹ := by
      simp only [map_mul, map_inv, heβ]
    calc ψ (β b * y * (β b)⁻¹) = ((e (β b * y * (β b)⁻¹) : ↥K) : G) := rfl
      _ = ((κe (ρ b) * e y * (κe (ρ b))⁻¹ : ↥K) : G) := by rw [hL]
      _ = ((ggGamma K hN b (e y) : ↥K) : G) := by rw [← hconj b (e y)]
      _ = (b : G) * ψ y * (b : G)⁻¹ := by rw [ggGamma_coe]; rfl
  have hcomm : ∀ b b' : ↥Bs, β b * β b' = β b' * β b := by
    intro b b'
    exact CFSG.Open.IsElemAbelian.comm hEimage.1 (hβmem b) (hβmem b')
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val (hEimage.1.2 x hx)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hEimage.1 hx hy)
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    apply hEimage.2 ⟨g, hg⟩
    · intro e he
      exact Subtype.ext (by
        change (e : V ≃ₗ[F] V) * g = g * (e : V ≃ₗ[F] V)
        exact (hgc (e : V ≃ₗ[F] V) ⟨e, he, rfl⟩).symm)
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)
  have hne : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb⟩ := hact hN
    have hβb : β b ≠ 1 := by
      intro h1
      apply hb
      ext z
      have hρb : ρ b = 1 := by
        apply σ.injective
        simpa [β] using h1
      have hc := hcompat0 b z
      simp only [hρb, map_one, MulAut.one_apply] at hc
      have hz : QuotientGroup.mk (ggGamma K hN b z) = QuotientGroup.mk z := eQ.injective hc
      rw [QuotientGroup.eq, hZ, Subgroup.mem_bot] at hz
      have h2 : z = ggGamma K hN b z := by
        calc z = ggGamma K hN b z * ((ggGamma K hN b z)⁻¹ * z) := by group
          _ = ggGamma K hN b z := by rw [hz, mul_one]
      simpa using h2.symm
    refine ⟨(β b : V ≃ₗ[F] V), hβA b, ?_⟩
    intro h
    exact hβb (Subtype.ext h)
  have hpqF : p ∣ Nat.card F + 1 := by rw [hcard']; exact hpqA
  obtain ⟨r, τ, Fframe, D, hDadd, hDmod, hDfin, c, θ, hτF, hτinj, hτrange, hfinD,
    hcpow, hcfix, hctwist, hcroot, hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign,
    hnoFixed, hexFixed⟩ :=
    exists_torus_blocks (K := F) (V := V) (Q := Q) (p := p) (A := A)
      hp2 (Or.inr hpqF) hQ hT hAΩ hApow hAcomm hmax hne
  letI : AddCommGroup D := hDadd
  letI : Module F D := hDmod
  letI : FiniteDimensional F D := hDfin
  let Δ : TBJOmData Q p A r :=
    { τ := τ
      F := Fframe
      D := D
      c := c
      θ := θ
      τ_eq := hτF
      τ_inj := hτinj
      τ_range := hτrange
      finrank_D := hfinD
      c_pow := hcpow
      c_fix := hcfix
      c_twist := hctwist
      c_roots := hcroot
      θ_inj := hθinj
      θ_range := hθrange
      θ_act := hθact
      normalizer := hnorm
      swapMove := hswap
      dinvMove := hdinv
      signMove := hsign
      noFixed := hnoFixed
      exFixed := hexFixed }
  have htype : (CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Even rank) ∨
      (¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Odd rank) := by
    rcases hrow' with ⟨hD, -, heven, -⟩ | ⟨hM, -, hodd, -⟩
    · exact Or.inl ⟨hplus.mpr hD, heven⟩
    · refine Or.inr ⟨?_, hodd⟩
      rw [hplus]
      intro h
      rw [hM] at h
      cases h
  have hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] :=
    charSum_top_modEq_one_of_witt hQ (r := rank) (by omega) hdim' hpqF htype
  have hfinrank : Module.finrank F V = 2 * r :=
    finrank_eq_two_mul_of_charSum (p := p) hp2 (Or.inr hpqF) hQ hT hAΩ hApow hAcomm hmax hne
      hτinj hτrange hchar
  have hr_eq : r = rank := by omega
  have hr4 : 4 ≤ r := by omega
  have hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0 := Δ.noFixed hchar
  let Φ : OrthFrameCore p Bs K :=
    { F := F
      V := V
      Q := Q
      A := A
      r := r
      Δ := Δ
      ψ := ψ
      β := β
      hA := hAΩ
      hr := hr4
      hpq := hpqF
      hfix := hfix
      hinj := by
        intro x y hxy
        exact e.injective (Subtype.val_injective hxy)
      hrange := by
        ext g
        constructor
        · rintro ⟨x, rfl⟩
          exact (e x).2
        · intro hg
          refine ⟨e.symm ⟨g, hg⟩, ?_⟩
          change ((e (e.symm ⟨g, hg⟩) : ↥K) : G) = g
          rw [MulEquiv.apply_symm_apply]
      hβA := hβA
      hβsurj := hβsurj
      hcompat := hcompat
      swapReal := by
        intro i j hij
        obtain ⟨w, hwmem, -, hwact⟩ := hswap i j hij
        refine ⟨⟨w, hwmem⟩, ?_, ?_⟩
        · intro f'
          exact hwact f'
        · apply mem_normalizer_of_conj_mem_range ψ β hBs hSC hcompat hcomm
          intro b
          have hbmem : (β b : V ≃ₗ[F] V) ∈ τ.range := by
            rw [hτrange]
            exact hβA b
          obtain ⟨f, hf⟩ := hbmem
          have humem : τ (SpCoord.permAut (Equiv.swap i j) f) ∈ A := by
            rw [← hτrange]
            exact ⟨SpCoord.permAut (Equiv.swap i j) f, rfl⟩
          have hu_od : τ (SpCoord.permAut (Equiv.swap i j) f) ∈ orthDerived Q := hAΩ humem
          obtain ⟨y, hy, hyval⟩ := humem
          have hu_eq : (⟨τ (SpCoord.permAut (Equiv.swap i j) f), hu_od⟩ :
              ↥(orthDerived Q)) = y := Subtype.ext hyval.symm
          have hu : (⟨τ (SpCoord.permAut (Equiv.swap i j) f), hu_od⟩ :
              ↥(orthDerived Q)) ∈ β.range := by
            rw [hβrange]
            rwa [hu_eq]
          obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp hu
          refine ⟨b', ?_⟩
          rw [hb']
          apply Subtype.ext
          change (w : V ≃ₗ[F] V) * (β b : V ≃ₗ[F] V) * (w : V ≃ₗ[F] V)⁻¹ =
            τ (SpCoord.permAut (Equiv.swap i j) f)
          rw [← hf]
          exact hwact f
      dinvReal := by
        intro i j hij
        obtain ⟨w, hwmem, -, hwact⟩ := hdinv i j hij
        refine ⟨⟨w, hwmem⟩, ?_, ?_⟩
        · intro f'
          exact hwact f'
        · apply mem_normalizer_of_conj_mem_range ψ β hBs hSC hcompat hcomm
          intro b
          have hbmem : (β b : V ≃ₗ[F] V) ∈ τ.range := by
            rw [hτrange]
            exact hβA b
          obtain ⟨f, hf⟩ := hbmem
          have humem : τ (NbrOrth.dinv i j f) ∈ A := by
            rw [← hτrange]
            exact ⟨NbrOrth.dinv i j f, rfl⟩
          have hu_od : τ (NbrOrth.dinv i j f) ∈ orthDerived Q := hAΩ humem
          obtain ⟨y, hy, hyval⟩ := humem
          have hu_eq : (⟨τ (NbrOrth.dinv i j f), hu_od⟩ :
              ↥(orthDerived Q)) = y := Subtype.ext hyval.symm
          have hu : (⟨τ (NbrOrth.dinv i j f), hu_od⟩ :
              ↥(orthDerived Q)) ∈ β.range := by
            rw [hβrange]
            rwa [hu_eq]
          obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp hu
          refine ⟨b', ?_⟩
          rw [hb']
          apply Subtype.ext
          change (w : V ≃ₗ[F] V) * (β b : V ≃ₗ[F] V) * (w : V ≃ₗ[F] V)⁻¹ =
            τ (NbrOrth.dinv i j f)
          rw [← hf]
          exact hwact f }
  exact ⟨⟨tag, rank, n⟩, hPlab, hhas, Φ, hr_eq, hcard, hQ, hfinrank, hplus⟩

theorem exists_orthWeakFrame_of_marking {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (hRig : GGLabelRigidInput) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) p Bs K)
    (hact : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), ∃ b : ↥Bs, ggGamma K hN b ≠ 1) :
    ∃ Φ : OrthWeakFrame p Bs K, Φ.Recognized := by
  classical
  haveI hperf : Group.IsPerfect ↥K := Group.IsPerfect.mk hmark.1
  have hZK : ∀ lab : LargeEvenLabel, (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → Subgroup.center ↥K = ⊥ := by
    rintro ⟨tag, rank, n⟩ ⟨hrow, hn2⟩ hhas
    have hrow' : (tag = .D ∧ 4 ≤ rank) ∨ (tag = .twD ∧ 5 ≤ rank) := by
      rcases hrow with ⟨h, h4, -, -⟩ | ⟨h, h5, -, -⟩
      · exact Or.inl ⟨h, h4⟩
      · exact Or.inr ⟨h, h5⟩
    have htag : tag = .D ∨ tag = .twD := hrow'.imp And.left And.left
    have hrank : 4 ≤ rank := by
      rcases hrow' with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · omega
    exact center_eq_bot_of_hasLabel_orth htag hrank hn2 hhas
  obtain ⟨⟨tag, rank, n⟩, ⟨hrow, hn2⟩, hhas, Φ, hr_eq, hcard, hQ, hfinrank, hplus⟩ :=
    exists_orthFrameCore_of_marking hRig hp2 hBs hSC (fun _ hP => hP.1) hmark hZK hact
  change Φ.r = rank at hr_eq
  change 2 ≤ n at hn2
  change Nat.card Φ.F = 2 ^ n at hcard
  have hrow' : (tag = .D ∧ 4 ≤ rank ∧ Even rank ∧ p ∣ 2 ^ n + 1) ∨
      (tag = .twD ∧ 5 ≤ rank ∧ Odd rank ∧ p ∣ 2 ^ n + 1) := by
    simpa [ggRowP_EOmP, ggRowP_EOmM] using hrow
  have hr4 : 4 ≤ Φ.r := Φ.hr
  have hrec :
      (Even Φ.r → Nonempty ((CFSG.LieType.Universal.lieUniversal
        CFSG.Open.StatedLieTag.POmegaPlus Φ.r 2 n Nat.prime_two).K ≃* ↥(orthDerived Φ.Q))) ∧
      (Odd Φ.r → Nonempty ((CFSG.LieType.Universal.lieUniversal
        CFSG.Open.StatedLieTag.POmegaMinus Φ.r 2 n Nat.prime_two).K ≃* ↥(orthDerived Φ.Q))) ∧
      ((Even Φ.r ∧ GGHasLabel ⟨.D, Φ.r, n⟩ (↥K ⧸ Subgroup.center ↥K)) ∨
        (Odd Φ.r ∧ GGHasLabel ⟨.twD, Φ.r, n⟩ (↥K ⧸ Subgroup.center ↥K))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hEven
      have heven : Even rank := by rwa [hr_eq] at hEven
      have hplusQ : CFSG.GroupTheory.WeirSylow.IsPlusType Φ.Q := by
        rcases hrow' with ⟨hD, -, -, -⟩ | ⟨hM, -, hodd, -⟩
        · exact hplus.mpr hD
        · obtain ⟨k, hk⟩ := heven
          obtain ⟨l, hl⟩ := hodd
          omega
      exact nonempty_lieUniversal_plus_equiv_orthDerived hQ (by omega) hcard hfinrank hplusQ
    · intro hOdd
      have hodd : Odd rank := by rwa [hr_eq] at hOdd
      have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Φ.Q := by
        intro hp
        have hD : tag = .D := hplus.mp hp
        rcases hrow' with ⟨-, -, heven, -⟩ | ⟨hM, -, -, -⟩
        · obtain ⟨k, hk⟩ := heven
          obtain ⟨l, hl⟩ := hodd
          omega
        · rw [hM] at hD
          cases hD
      exact nonempty_lieUniversal_minus_equiv_orthDerived hQ (by omega) hcard hfinrank hminus
    · rcases hrow' with ⟨hD, -, heven, -⟩ | ⟨hM, -, hodd, -⟩
      · left
        refine ⟨?_, ?_⟩
        · rwa [hr_eq]
        · rw [hr_eq]
          simpa [hD] using hhas
      · right
        refine ⟨?_, ?_⟩
        · rwa [hr_eq]
        · rw [hr_eq]
          simpa [hM] using hhas
  exact ⟨Φ.toWeakFrame n hcard hn2, hrec⟩

theorem pair_of_orthogonal_marking {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (hRig : GGLabelRigidInput) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {P : ℕ → LargeEvenLabel → Prop}
    (hProw : ∀ lab, P p lab → ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)
    (hmark : GGInnerDiagOnLabel P p Bs K)
    (hZK : ∀ lab, P p lab → GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → Subgroup.center ↥K = ⊥)
    (r s : MulAut ↥Bs) (hr : r ∈ ggAutomizer K Bs) (hs : s ∈ ggAutomizer K Bs)
    (hrefl : GGIsReflection p r) (hsrefl : GGIsReflection p s) (hrs : r ≠ s) :
    GGPairConcl Bs K r s := by
  have hact : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      ∃ b : ↥Bs, ggGamma K hN b ≠ 1 :=
    nontrivial_action_of_automizer_reflection r hr hrefl
  obtain ⟨lab, _hPlab, _hhas, Φ, _hrank, _hfield, _hQ, _hdim, _htype⟩ :=
    exists_orthFrameCore_of_marking hRig hp2 hBs hSC hProw hmark hZK hact
  exact Φ.pair_of_reflections hp2 r s hr hs hrefl hsrefl hrs

end OrthTorus

end CFSG.StandardType

end
