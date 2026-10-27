module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Two
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5OneLang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5OneData
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Model
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inner

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit)

theorem false_of_labelTwA5 (hRig : GGLabelRigidInput) {Y : Type} [Group Y] {L : Subgroup Y}
    {p f : ℕ} (hp5 : 5 ≤ p) (hc : orderOf ((2 : ZMod p) ^ f) = 1)
    (hsplit : LargeEvenMarking ↥L fun lab _ _ _ _ _ => LargeEvenSplit p lab)
    (hlab : GGHasLabel ⟨LargeEvenLieTag.twA, 5, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (hΛ : LargeEvenInLambda2 ⟨LargeEvenLieTag.twA, 5, f⟩) : False := by
  obtain ⟨lab', hΛ', hlab', R, _, I, F, θ, hsp⟩ := largeEvenMarking_exists_hasLabel hsplit
  have hiso := hRig _ _ _ hΛ hΛ' hlab hlab'
  have heq : lab' = ⟨LargeEvenLieTag.twA, 5, f⟩ := by
    rcases hiso with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact h.symm
    all_goals simp at h
  rw [heq] at hsp
  rcases hsp with ⟨hU, -⟩ | ⟨-, -, hd⟩ | ⟨h3, -⟩ | ⟨-, hp3'⟩
  · exact hU
  · have h1 : ((2 ^ f + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ f + 1) p).2 hd
    push_cast at h1
    have h2 : (2 : ZMod p) ^ f = 1 := orderOf_eq_one_iff.1 hc
    rw [h2] at h1
    have h3 : (2 : ZMod p) = 0 := by
      have h4 : (2 : ZMod p) = 1 + 1 := by norm_num
      rw [h4]
      exact h1
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h3
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · rcases h3 with h3 | h3 <;> simp at h3
  · exact absurd hp3' (by omega)

theorem false_twE6_one
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    (hR : LangFamilyCompFieldSL) (hL : LangFamilyCompLabel)
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hc : orderOf ((2 : ZMod p) ^ f) = 1)
    (hp : p ≠ 3) : False := by
  have hp2 := h.ne_two
  have hp5 : 5 ≤ p := by
    have h2 := h.prime.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd h.prime (by decide)
    omega
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .E6 p (Nat.card B) :=
    utoralAt_of_nonTorsion h.prime hp2 (fun _ => hp) (fun h => by cases h) hBpos
  have hf : 1 ≤ f := h.adm.2.1
  obtain ⟨K, instF, instFin, σ, hK, hσ, ⟨θ'⟩⟩ := h.exists_twE6_rootGroup_equiv
  have : CharP K 2 :=
    charP_two_of_finite_field_card_two_pow (f := f * 2) (by rw [hK, pow_mul])
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨S₁, fr₁, hq, hBT, a, i, ha, hap, hspan, h2, hΨ, horth, hcard, hrk⟩ :=
    uframe_data_twE6 (uFieldInput_of_SL hR (Or.inl rfl)) hf h.prime hp2 hK σ hσ θ'
      h.b_norm (h.inner_twE6 (Or.inl hp)) h.b_faithful h.b_elem h.d_le h.d_card
      (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
      ⟨t', m, f', hlt, hm⟩ hTor
  have hr2 : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) = 2 := by
    have hle := e6_finrank_le_two hΨ S₁.frob.iform_eq horth
    by_contra hne
    have hlt2 : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) < 2 := by
      omega
    have hpow : p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) <
        p ^ 4 :=
      Nat.pow_lt_pow_right (by have := h.prime.two_le; omega) (by omega)
    have h4 := h.b_card
    omega
  have hDcard : Nat.card ↥(fr₁.DLang D) = p ^ 2 := by
    rw [fr₁.card_DLang h.d_le, h.d_card]
  have hT : ∀ u : ↥(fr₁.DLang D), rootDiagUnit .E6 (a u) ∈ S₁.D.torus := fun u =>
    (ha u) ▸ hBT (fr₁.DLang_le_BLang u.2)
  have hxB : x ∈ B := h.d_le h.x_mem
  have hxD : fr₁.toLang ⟨x, hxB⟩ ∈ fr₁.DLang D := fr₁.toLang_mem_DLang h.d_le h.x_mem
  have hx1 : (⟨fr₁.toLang ⟨x, hxB⟩, hxD⟩ : ↥(fr₁.DLang D)) ≠ 1 := by
    intro h1
    have h2 : fr₁.toLang ⟨x, hxB⟩ = 1 := congrArg Subtype.val h1
    have h3 : (⟨x, hxB⟩ : ↥B) = 1 := fr₁.toLang_injective (h2.trans (map_one fr₁.toLang).symm)
    exact h.x_ne (congrArg Subtype.val h3)
  have hJc := fr₁.isComponentOf_JLang h.d_le (h.j_comp.1.trans inf_le_left)
    (Assembly.isComponentOf_iff_open.1 h.j_comp)
  have hLG : L ≤ G₀ := h.l_le
  have hLq : CFSG.Open.IsQuasisimple ↥L := (Assembly.isComponentOf_iff_open.1 h.l_comp).2.2
  have hLc0 := fr₁.isComponentOf_JLang (D := Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxB)
    hLG (by
      rw [centralizer_zpowers_eq_single]
      exact Assembly.isComponentOf_iff_open.1 h.l_comp)
  rw [fr₁.centralizer_DLang_zpowers hxB] at hLc0
  have hres := e6one_lang hR hL S₁ h.prime hp5 hq hc (langSetup_rho_linear S₁) (fr₁.DLang D)
    hDcard a ha hap hT i hΨ hr2 horth hspan hJc ⟨fr₁.toLang ⟨x, hxB⟩, hxD⟩ hx1 hLc0
    (fr₁.JLang_mono h.j_le_l)
  rcases hres with hcen | hlab
  ·
    have hDC : D ≤ Subgroup.centralizer (L : Set X) :=
      fr₁.le_centralizer_of_lang_commute h.d_le hLG hLq.1 hcen
    have hcyc : IsCyclic ↥D := h.l_cyc D hDC (IsPGroup.of_card h.d_card)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using h.b_elem.2 g (h.d_le g.2))
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rw [hord, h.d_card] at hdvd
    have hp2' := h.prime.two_le
    have := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  ·
    obtain ⟨e⟩ := fr₁.nonempty_equiv_JLang hLG hLq
    have hlabL : GGHasLabel ⟨LargeEvenLieTag.twA, 5, f⟩ (↥L ⧸ Subgroup.center ↥L) :=
      ggHasLabel_of_mulEquiv e.symm hlab.2.2.1
    exact false_of_labelTwA5 ggLabelRigidInput_holds hp5 hc h.l_split hlabL hlab.1

end CFSG.StandardType.TableCRes

end
