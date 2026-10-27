module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveLangRational

public section

namespace CFSG.StandardType.TableCRes


open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartOne.KE

section E8Lang

theorem exists_langSetup_of_E8Five
    {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    (E : Subgroup ↥(adjointGroup Tag.E8 K)) (hE : IsElemAbelian 5 E) (h4 : 5 ^ 4 ≤ Nat.card E) :
    ∃ (S : LangSetup Tag.E8 (AlgebraicClosure K) 5)
      (ι : ↥(adjointGroup Tag.E8 K) →* ModGL Tag.E8 (AlgebraicClosure K)),
      S.D.q = 2 ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ S.D.q) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      S.D.n = canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) NoOffRest.weylE8W ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ∀ x ∈ E, ι x ∈ S.D.torus := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hkey : ∀ x : ZMod 5, x * x + 1 = 0 → (-x) * (-x) = -1 ∧ x * (-x) = 1 := by decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : CharP K 2 := charP_two_of_finite_field_card_two_pow hK
  have hperf : commutator ↥(adjointGroup Tag.E8 K) = ⊤ := single_edge_perfect Tag.E8 K (by simp)
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  set L := AlgebraicClosure K with hLdef
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobenius_def 2 f c
  have hFrK : ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  obtain ⟨g₀, hg₀C, hg₀⟩ := lang_conjugator Tag.E8 K (ℓ := 2) (f := f) hf1 L NoOffRest.weylE8W
  have h5ℓ : ¬ ringChar L ∣ 5 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨ζ, hζo⟩ := NoOffE8Five.exists_unit_orderOf_five_of_isAlgClosed (L := L) h5ℓ
  have hζ : ζ ^ 5 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨hlam, hqlam⟩ := hkey ((Nat.card K : ℕ) : ZMod 5) (by
    have h := (ZMod.natCast_eq_zero_iff _ _).2 h5
    push_cast at h
    exact h)
  obtain ⟨ι₁, hι₁inj, hι₁val⟩ := NoOffE8Five.exists_langTorsionHom hFrK hζo hζ hqlam hg₀C hg₀
  have hXel : IsElemAbelian 5 ι₁.range := NoOffE8Five.isElemAbelian_range_of_module ι₁
  have hXcard : Nat.card ι₁.range = 5 ^ 4 := by
    rw [← NoOffRest.card_eigE8 (p := 5) (by norm_num) hlam]
    exact (Nat.card_congr (MonoidHom.ofInjective hι₁inj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  obtain ⟨c, hc⟩ := NoOffE8Five.exists_conj_map_eq_E8_five h5 hXel hE hXcard.ge h4
  set D : LangDatum Tag.E8 L :=
    LangDatum.ofFrobenius (iterateFrobenius L 2 f) (2 ^ f) hFr NoOffRest.weylE8W hg₀C hg₀ with hD
  have hDq : D.q = 2 ^ f := rfl
  have hDg0 : D.g0 = g₀ := rfl
  set ι₀ : ↥(adjointGroup Tag.E8 K) →* ModGL Tag.E8 L := adjEmb Tag.E8 K L with hι₀
  have hι₀inj : Function.Injective ι₀ := adjEmb_injective
  have hd : LangDescent D 7 ι₀ :=
    langDescent_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hFrK D rfl Nat.prime_seven (by norm_num)
      hperf
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E8 L D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨Nat.prime_two.isPrimePow.pow (by omega),
      (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 (by omega))⟩
  have hpq5 : ¬ 5 ∣ D.q := by
    rw [hDq]
    intro h
    have h5' := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  have hq5 : 5 ≤ 5 ∨ 4 ≤ D.q := Or.inl le_rfl
  let ι : ↥(adjointGroup Tag.E8 K) →* ModGL Tag.E8 L :=
    ((MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀).comp (MulAut.conj c⁻¹).toMonoidHom
  have hι : ∀ y, ι y = D.g0⁻¹ * ι₀ (c⁻¹ * y * c) * D.g0 := fun y => by
    change (MulAut.conj D.g0⁻¹) (ι₀ ((MulAut.conj c⁻¹) y)) = _
    simp
  have hιinj : Function.Injective ι :=
    ((MulAut.conj D.g0⁻¹).injective.comp hι₀inj).comp (MulAut.conj c⁻¹).injective
  refine ⟨D.toSetup 5 ρ hρ Nat.prime_five hq5 hqpow hpq5 hd.finite_model, ι, hDq,
    ⟨iterateFrobenius L 2 f, hFr, rfl⟩, rfl, hιinj, ?_, fun x hx => ?_⟩
  · show ι.range = D.Γ
    rw [hd.Γ_eq]
    have hcc : ∀ y : ↥(adjointGroup Tag.E8 K),
        (MulAut.conj c⁻¹) ((MulAut.conj c) y) = y := fun y => by
      simp [MulAut.conj_apply, mul_assoc]
    have hr : ι.range = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨ι₀ ((MulAut.conj c⁻¹) y), ⟨_, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        refine ⟨(MulAut.conj c) y, ?_⟩
        show (MulAut.conj D.g0⁻¹) (ι₀ ((MulAut.conj c⁻¹) ((MulAut.conj c) y))) = _
        rw [hcc]
        rfl
    rw [hr]
  · rw [← hc] at hx
    obtain ⟨y, ⟨v, hvy⟩, hyx⟩ := hx
    obtain ⟨s, hvs⟩ : ∃ s, v = Multiplicative.ofAdd s := ⟨Multiplicative.toAdd v, rfl⟩
    have hxs : c⁻¹ * x * c = ι₁ (Multiplicative.ofAdd s) := by
      rw [← hyx, ← hvy, hvs]
      show c⁻¹ * ((MulAut.conj c) (ι₁ (Multiplicative.ofAdd s))) * c = _
      rw [MulAut.conj_apply]
      group
    have h2 : ι₀ (ι₁ (Multiplicative.ofAdd s)) =
        g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) * g₀⁻¹ := by
      rw [← NoOffE8Five.frameElt_apply ζ hζ (-(Nat.card K : ZMod 5)) s]
      exact hι₁val s
    rw [hι, hxs, h2, hDg0]
    have h3 : g₀⁻¹ * (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        (s : Fin Tag.E8.rank → ZMod 5) * g₀⁻¹) * g₀ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) := by group
    rw [h3]
    exact (NoOffE8Five.frameDiag_mem_twistedTorus_iff hFrK hζo hζ hqlam _).2 s.2

end E8Lang

section E8Frame

private theorem exists_uframe_untwE8
    {X : Type} [Group X] {G₀ B : Subgroup X} {f : ℕ}
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian 5 B)
    (hB4 : 5 ^ 4 ≤ Nat.card B) (h5 : 5 ∣ 2 ^ f * 2 ^ f + 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S : LangSetup Tag.E8 (AlgebraicClosure K) 5) (fr : GGTCUFrame S.Γ G₀ B), S.D.q = 2 ^ f ∧
      (∀ γ, IsRoot Tag.E8 γ → S.ρ γ = NoOffRest.weylE8W • γ) ∧ fr.BLang ≤ S.D.torus := by
  classical
  obtain ⟨K, instF, instFin, hKcard, ⟨eK⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_finite_field_card_two_pow hKcard
  have hZadj : Subgroup.center ↥(adjointGroup Tag.E8 K) = ⊥ := center_adjointGroup_eq_bot
  let θ : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃* ↥(adjointGroup Tag.E8 K) :=
    eK.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans QuotientGroup.quotientBot)
  have hcl : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := by
    have h1 := Subgroup.map_center_eq θ
    rw [hZadj] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h1
  obtain ⟨ν, hνinj, hνact⟩ := exists_inner_hom_of_faithful_inner hBN hin hfaith hcl
  set E : Subgroup ↥(adjointGroup Tag.E8 K) :=
    ((⊤ : Subgroup ↥B).map ν).map θ.toMonoidHom with hE
  have hEel : IsElemAbelian 5 E := by
    have h1 : IsElemAbelian 5 (B.subgroupOf B) := hBel.subgroupOf B
    rw [Subgroup.subgroupOf_self] at h1
    exact (h1.map ν).map θ.toMonoidHom
  have hEcard : Nat.card E = Nat.card B := by
    rw [hE, Subgroup.card_map_of_injective θ.injective, Subgroup.card_map_of_injective hνinj,
      Subgroup.card_top]
  have h5K : 5 ∣ Nat.card K * Nat.card K + 1 := by
    rw [hKcard]
    exact h5
  obtain ⟨S, ι, hq, ⟨Fr, hFr1, hFr2⟩, hn, hinj, hrange, hEtor⟩ :=
    exists_langSetup_of_E8Five hKcard h5K E hEel (by rw [hEcard]; exact hB4)
  let fr : GGTCUFrame S.Γ G₀ B :=
    ⟨ν, hνinj, hνact, θ.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩
  refine ⟨K, instF, instFin, inferInstance, S, fr, hq, fun γ hγ => ?_, ?_⟩
  · exact S.rho_eq_smul_of_frob (Fr := Fr) hFr1 hFr2 hn hγ
  · rintro _ ⟨b, rfl⟩
    exact hEtor _ ⟨_, ⟨b, Subgroup.mem_top b, rfl⟩, rfl⟩

theorem uframe_data_of_frame
    (hR : LangFamilyCompFieldSL) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] {S₁ : LangSetup τ (AlgebraicClosure K) 5}
    (fr₁ : GGTCUFrame S₁.Γ G₀ B) (hqq : S₁.D.q = 2 ^ f) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hJG : J ≤ G₀) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (hDT : fr₁.DLang D ≤ S₁.D.torus) :
    ∃ (a : ↥(fr₁.DLang D) → Fin τ.rank → (AlgebraicClosure K)ˣ)
      (i : KernelComponent (famCharHom a)),
      (∀ u : ↥(fr₁.DLang D), (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ (a u)) ∧
      (∀ u j, a u j ^ p = 1) ∧
      fr₁.JLang J ≤ rootSpan τ (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
      2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) ∧
      CFSG.StandardType.GGCompFieldAtSL
        (2 ^ (f * componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i))) (fr₁.JLang J) := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hpar : ∀ u : fr₁.DLang D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hDT u.2).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hDT u.2
  have hrange : (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u)) =
      ((fr₁.DLang D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DLang D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u))) := by
    rw [hrange]
    exact fr₁.isComponentOf_JLang hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hR τ (AlgebraicClosure K) 5 p S₁ hτ hp hp2 (↥(fr₁.DLang D)) a haT hap (fr₁.JLang J) hcomp
  rw [hqq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JLang hJG hJ.2.2).some hfield.toAt hF
  exact ⟨a, i, ha, hap, hspan, h2, hfield⟩

theorem uframe_dataE8
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} {f : ℕ}
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian 5 B)
    (hB4 : 5 ^ 4 ≤ Nat.card B) (h5 : 5 ∣ 2 ^ f * 2 ^ f + 1)
    (hDB : D ≤ B) (hJG : J ≤ G₀) (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S₁ : LangSetup Tag.E8 (AlgebraicClosure K) 5) (fr₁ : GGTCUFrame S₁.Γ G₀ B),
      S₁.D.q = 2 ^ f ∧ fr₁.DLang D ≤ S₁.D.torus ∧
      (∀ γ, IsRoot Tag.E8 γ → S₁.ρ γ = NoOffRest.weylE8W • γ) ∧
      ∃ (a : ↥(fr₁.DLang D) → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
        (i : KernelComponent (famCharHom a)),
        (∀ u : ↥(fr₁.DLang D),
          (u : ModGL Tag.E8 (AlgebraicClosure K)) = rootDiagUnit Tag.E8 (a u)) ∧
        (∀ u j, a u j ^ 5 = 1) ∧
        fr₁.JLang J ≤ rootSpan Tag.E8 (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
        2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) ∧
        CFSG.StandardType.GGCompFieldAtSL
          (2 ^ (f * componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i)))
          (fr₁.JLang J) := by
  classical
  obtain ⟨K, instF, instFin, instChar, S₁, fr₁, hq, hρ, hBT⟩ :=
    exists_uframe_untwE8 hmod hBN hin hfaith hBel hB4 h5
  have hDT : fr₁.DLang D ≤ S₁.D.torus := fr₁.DLang_le_BLang.trans hBT
  obtain ⟨a, i, ha, hap, hspan, h2, hfield⟩ :=
    uframe_data_of_frame hR (Or.inr (Or.inr rfl)) Nat.prime_five (by norm_num) fr₁ hq hBel hDB hJG
      hJ hF hDT
  exact ⟨K, instF, instFin, instChar, S₁, fr₁, hq, hDT, hρ, a, i, ha, hap, hspan, h2, hfield⟩

end E8Frame

end CFSG.StandardType.TableCRes

end
