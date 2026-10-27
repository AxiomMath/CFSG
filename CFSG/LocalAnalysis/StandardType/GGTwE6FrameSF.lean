module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameSFDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ScalarFree
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusPackage
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TwE6TB

theorem ggTwE6FramePackageSF_of_mulEquiv {p : ℕ} [NeZero p] {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ β' ∈ I', MulAut.congr e.symm β' ∈ I) (h : GGTwE6FramePackageSF p R I) :
    GGTwE6FramePackageSF p R' I' := by
  obtain ⟨t, m, ht, hact, hsc, haut, hdiag⟩ := h
  refine ⟨e.toMonoidHom.comp t, e.toMonoidHom.comp m, e.injective.comp ht, ?_, ?_, ?_, ?_⟩
  · intro v s
    simpa only [MonoidHom.comp_apply, map_mul, map_inv] using congrArg e.toMonoidHom (hact v s)
  · intro E' hE' h4' hSC'
    let E : Subgroup R := E'.comap e.toMonoidHom
    have hE : IsElemAbelian p E := by
      dsimp only [E]
      rw [Subgroup.comap_equiv_eq_map_symm' e E']
      exact IsElemAbelian.map hE' e.symm.toMonoidHom
    have hcardE : Nat.card E = Nat.card E' := by
      dsimp only [E]
      rw [Subgroup.comap_equiv_eq_map_symm' e E',
        Subgroup.card_map_of_injective e.symm.injective]
    have h4 : p ^ 4 ≤ Nat.card E := by rw [hcardE]; exact h4'
    have hmap : E' = E.map e.toMonoidHom := by
      dsimp only [E]
      exact (Subgroup.map_comap_eq_self_of_surjective e.surjective E').symm
    have hSC : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E := by
      intro g hg hgp
      show e g ∈ E'
      apply hSC' (e g)
      · intro y hy
        rw [hmap] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        show e g * e x = e x * e g
        rw [← map_mul, ← map_mul, hg x hx]
      · rw [← map_pow, hgp, map_one]
    obtain ⟨c, hc⟩ := hsc E hE h4 hSC
    refine ⟨e c, ?_⟩
    rw [hmap, hc, MonoidHom.range_comp]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change e (c * x * c⁻¹) = e c * e x * (e c)⁻¹
    rw [map_mul, map_mul, map_inv]
  · intro β' hstab'
    let β : MulAut R := MulAut.congr e.symm β'
    have hstab : ∀ b ∈ t.range, β b ∈ t.range := by
      rintro b ⟨s, rfl⟩
      have hb' : β' (e (t s)) ∈ (e.toMonoidHom.comp t).range := hstab' (e (t s)) ⟨s, rfl⟩
      rw [MonoidHom.range_comp] at hb'
      obtain ⟨y, hy, hyeq⟩ := hb'
      have hβ : β (t s) = y := by
        dsimp only [β]
        rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
          MulEquiv.trans_apply, ← hyeq]
        exact MulEquiv.symm_apply_apply e y
      rw [hβ]; exact hy
    obtain ⟨w, c, hc0, hw⟩ := haut β hstab
    refine ⟨w, c, hc0, ?_⟩
    intro s
    change β' (e (t (Multiplicative.ofAdd s))) =
      e (t (Multiplicative.ofAdd (c • TableBExc.torusAct TwistTag.E6.tag p w s)))
    have h := congrArg e (hw s)
    have hβs : β (t (Multiplicative.ofAdd s)) =
        e.symm (β' (e (t (Multiplicative.ofAdd s)))) := by
      dsimp only [β]
      rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [hβs] at h
    simpa only [MulEquiv.apply_symm_apply] using h
  · intro β' hβ'I hstab'
    let β : MulAut R := MulAut.congr e.symm β'
    have hβI : β ∈ I := hI β' hβ'I
    have hstab : ∀ b ∈ t.range, β b ∈ t.range := by
      rintro b ⟨s, rfl⟩
      have hb' : β' (e (t s)) ∈ (e.toMonoidHom.comp t).range := hstab' (e (t s)) ⟨s, rfl⟩
      rw [MonoidHom.range_comp] at hb'
      obtain ⟨y, hy, hyeq⟩ := hb'
      have hβ : β (t s) = y := by
        dsimp only [β]
        rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
          MulEquiv.trans_apply, ← hyeq]
        exact MulEquiv.symm_apply_apply e y
      rw [hβ]; exact hy
    obtain ⟨w, hw⟩ := hdiag β hβI hstab
    refine ⟨w, fun s => ?_⟩
    change β' (e (t (Multiplicative.ofAdd s))) =
      e (t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p w s)))
    have h := congrArg e (hw s)
    have hβs : β (t (Multiplicative.ofAdd s)) =
        e.symm (β' (e (t (Multiplicative.ofAdd s)))) := by
      dsimp only [β]
      rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [hβs] at h
    simpa only [MulEquiv.apply_symm_apply] using h

end TwE6TB

namespace ExcFrames

theorem exists_frameAutPackageSF
    {f p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    TwE6TB.GGTwE6FramePackageSF p ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      (Set.range (RecipeExcLang.twConj K σ)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hlang, hι₀, hbase, hTcomm, hrangeT, htors, _,
    hcent⟩ := exists_langFrame hp5 hf hpq K hK σ.toRingHom hσ L Fr hFr
  obtain ⟨m, -, hm⟩ :=
    exists_langFrame_weyl hf K hK σ.toRingHom hσ L Fr hFr hζ hg₀C hlang ι₀ hbase
  refine ⟨ι₀, m, hι₀, hm, ?_, ?_, ?_⟩
  · intro E hE h4 hSC
    have hXel : IsElemAbelian p ι₀.range := by
      let : Module (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p) := inferInstance
      exact NoOffE8Five.isElemAbelian_range_of_module (p := p) ι₀
    have hXcard : Nat.card ι₀.range = p ^ 6 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hι₀).toEquiv,
        Nat.card_congr Multiplicative.toAdd]
      simp [ZMod.card]
      rfl
    have hXSC : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        (∀ x ∈ ι₀.range, c * x = x * c) → c ^ p = 1 → c ∈ ι₀.range :=
      fun c hc hcp => htors c (hcent c hc) hcp
    by_cases hp5eq : p = 5
    · subst hp5eq
      have h54 : 5 ^ 4 ≤ Nat.card ι₀.range := by rw [hXcard]; norm_num
      exact twistedE6SCUnique_five hf hpq K hK σ.toRingHom hσ hXel h54 hXSC hE h4 hSC
    · have hp7 : 7 ≤ p := by
        have hpne6 : p ≠ 6 := by
          rintro rfl
          exact absurd (Fact.out : Nat.Prime 6) (by decide)
        omega
      obtain ⟨c, hc⟩ := twistedE6SCUnique_ge_seven (p := p) hp7 hf hpq K hK σ.toRingHom hσ hι₀
        hTcomm hrangeT htors hcent hE hSC
      exact ⟨c, hc.symm⟩
  · intro β hstab
    obtain ⟨w, c, hc0, -, hw⟩ :=
      langFrame_aut hp5 hf K hK σ.toRingHom hσ L hζKord hζ hg₀C ι₀ hι₀ hbase β hstab
    exact ⟨w, c, hc0, hw⟩
  · rintro β ⟨w, rfl⟩ hstab
    exact exists_scalarFree_twConj (n := f) hf hK hσ hFr hg₀C ι₀ hbase w hstab

end ExcFrames

namespace TwE6TB

theorem ggTwE6FramePackageSF_recipeR
    {n p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTwE6FramePackageSF p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  let σ : K →+* K := iterateFrobenius K 2 n
  let σ' : K ≃+* K := RingEquiv.ofBijective σ (Finite.injective_iff_bijective.mp σ.injective)
  have hσ' : ∀ c, σ' c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε, -⟩ := TwE6FieldCore.exists_recipeConj_field hn hK σ' hσ'
  have hI : ∀ β' ∈ TwE6Delta.RecipeI K n,
      MulAut.congr ε.symm β' ∈ Set.range (RecipeExcLang.twConj K σ') := by
    intro β' hβ'
    obtain ⟨w, hw⟩ := (hε β').2 hβ'
    have hβ'congr : MulAut.congr ε (RecipeExcLang.twConj K σ' w) = β' := by
      rw [← TwE6Transport.recipeConj_eq]
      exact hw
    refine ⟨w, ?_⟩
    rw [← hβ'congr]
    exact (MulEquiv.symm_apply_apply (MulAut.congr ε) _).symm
  exact ggTwE6FramePackageSF_of_mulEquiv ε hI
    (ExcFrames.exists_frameAutPackageSF hp5 hn hpq K hK σ' hσ')

end TwE6TB

end CFSG.StandardType
