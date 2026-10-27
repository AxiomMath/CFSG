module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofL2Tools
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofL2Inner
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofU43McL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CenterlessCover

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction)
open Item434CharThree (pglAction_injective)
open CFSG.RankThree.PartTwo.KFacts (stdPinnedPSL2 inducedAutHom)
open CFSG.Assembly.RankThreeEven (projSL)

section Of


open Res413Cover in
theorem inputs413L2Three_of (h45 : Item4_5) : Inputs413L2Three := by
  intro G _ _ L A E c hyp e he1 hiso
  obtain ⟨e₁⟩ := hiso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZodd := odd_card_center_of_hyp413 h45 hyp
  obtain ⟨hG, hL, hT, hr⟩ := hyp
  have hTsave := hT
  obtain ⟨hAmax, hAc, hc3, hE27, hEA, -⟩ := hT
  have hA := hAmax.prop
  obtain ⟨n, hn5, hn⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hzC : Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hcAC.2
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, n, by omega, hn⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have he0 : e ≠ 0 := by omega
  have hKc : Nat.card (GaloisField 3 e) = 3 ^ e := GaloisField.card 3 e he0
  set K := GaloisField 3 e with hKdef
  set e₂ : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K := e₁.trans (projSLEquivPSL K) with he₂
  have hZs : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_equiv e₂ (psl2_center_eq_bot K)
  have hZ3 := center_pow_three_eq_one hZs
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcL := zpowers_inf_eq_bot hZ3 hcAC.2 hc3'
  set R := (thetaAct hAN).range with hR
  have hRe : CFSG.Assembly.IsElemAbelian 3 R := isElemAbelian_range_thetaAct hAN hA
  have hRcard : Nat.card R = 3 ^ (n - 1) := by
    have h1 := card_range_thetaAct_mul hL.1 hAN
    rw [hAc, Nat.card_zpowers, hc3, hn] at h1
    have h2 : 3 ^ n = 3 ^ (n - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  set Φ := (MulAut.congr e₂).toMonoidHom with hΦ
  set R' := R.map Φ with hR'
  have hR'e : CFSG.Assembly.IsElemAbelian 3 R' := isElemAbelian_map _ hRe
  have hR'card : Nat.card R' = 3 ^ (n - 1) := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.congr e₂).injective, hRcard]
  set P := R' ⊓ (pglAction K).range with hP
  have hP27 : 27 ≤ Nat.card P := by
    have h1 : Nat.card R' ≤ 3 * Nat.card P := card_le_three_mul_inf_pglAction he0 hR'e
    rw [hR'card] at h1
    have : 3 ^ 4 ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hinner_of : ∀ a ∈ A, ¬ InducesOuterTheta a L →
      ∃ l ∈ A ⊓ L, a * l⁻¹ ∈ Subgroup.zpowers c := fun a ha hout =>
    exists_mem_inf_of_inner hZ3 hAmax hAc hAN ha
      (exists_inner_of_not_inducesOuterTheta hL.1 (hAN ha) hout)
  have h27 : 27 ≤ Nat.card (A ⊓ L : Subgroup G) := by
    set Q := ((A ⊓ L).subgroupOf A).map (Φ.comp (thetaAct hAN)) with hQ
    have hPQ : P ≤ Q := by
      rintro π ⟨hπR', hπpgl⟩
      obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hπR'
      have hπ3 : (Φ (thetaAct hAN a)) ^ 3 = 1 := hR'e.2 _ ⟨_, ⟨a, rfl⟩, rfl⟩
      have hinn := mem_range_conj_of_mem_range_pglAction hπpgl hπ3
      have hout : ¬ InducesOuterTheta (a : G) L := by
        rintro ⟨ha', hnot⟩
        apply hnot
        have h1 : KFacts.IsInnerAut (MulAut.congr e₂ (thetaAct hAN a)) := hinn
        exact (KFacts.isInnerAut_congr e₂ _).mp h1
      obtain ⟨l, hl, hal⟩ := hinner_of a a.2 hout
      refine ⟨⟨l, hl.1⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
      show Φ (thetaAct hAN ⟨l, hl.1⟩) = Φ (thetaAct hAN a)
      congr 1
      have h1 : thetaAct hAN (a * (⟨l, hl.1⟩ : A)⁻¹) = 1 :=
        (thetaAct_eq_one_iff hL.1 hAN _).mpr (hzC hal)
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1.symm
    calc 27 ≤ Nat.card P := hP27
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hPQ
      _ ≤ Nat.card ((A ⊓ L).subgroupOf A) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
      _ = Nat.card (A ⊓ L : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcent : ∀ b ∈ A ⊓ L, b ≠ 1 → ∀ y ∈ L, y * b = b * y →
      y ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
    intro b hb hb1 y hy hyb
    set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    have hb3 : b ^ 3 = 1 := hA.2 b hb.1
    have hb'1 : e₂ (q ⟨b, hb.2⟩) ≠ 1 := by
      intro h1
      have h2 : q ⟨b, hb.2⟩ = 1 := e₂.injective (h1.trans (map_one e₂).symm)
      have hbθ : (⟨b, hb.2⟩ : L) ∈ aschbacherSolvableCore 3 L := by
        rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
        exact h2
      have h3 : orderOf (⟨⟨b, hb.2⟩, hbθ⟩ : aschbacherSolvableCore 3 L) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext hb3))
      have h4 : orderOf (⟨⟨b, hb.2⟩, hbθ⟩ : aschbacherSolvableCore 3 L) ∣
          Nat.card (aschbacherSolvableCore 3 L) := orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h5 | h5
      · exact hb1 (congrArg Subtype.val (congrArg Subtype.val (orderOf_eq_one_iff.mp h5)))
      · rw [h5] at h4
        exact hθ3 h4
    have hb'3 : e₂ (q ⟨b, hb.2⟩) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow]
      have : (⟨b, hb.2⟩ : L) ^ 3 = 1 := Subtype.ext hb3
      rw [this, map_one, map_one]
    have hy'b' : e₂ (q ⟨y, hy⟩) * e₂ (q ⟨b, hb.2⟩) = e₂ (q ⟨b, hb.2⟩) * e₂ (q ⟨y, hy⟩) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 2
      exact Subtype.ext hyb
    have h3 := pow_three_eq_one_of_commute he0 hb'1 hb'3 hy'b'
    have h4 : q ((⟨y, hy⟩ : L) ^ 3) = 1 := by
      apply e₂.injective
      rw [map_pow, map_pow, h3, map_one]
    have hθ : (⟨y, hy⟩ : L) ^ 3 ∈ aschbacherSolvableCore 3 L := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
      exact h4
    have hZ := aschbacherSolvableCore_le_center hL.1 hθ
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := Subgroup.mem_center_iff.mp hZ ⟨u, hu⟩
    have h5 := congrArg Subtype.val this
    simpa using h5
  obtain ⟨x, hxE, hxout⟩ : ∃ x ∈ E, InducesOuterTheta x L := by
    by_contra hall
    push Not at hall
    exact false_of_inner_E hG hL hTsave (fun x hx => hinner_of x (hEA hx) (hall x hx)) hcL h27
      hcent
  have hxA := hEA hxE
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  obtain ⟨hxN, -⟩ := id hxout
  set τ := inducedAutHom L e₂ ⟨x, hxN⟩ with hτdef
  have hτ3 : τ ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L e₂ hxN hx3
  have hτout : ¬ KFacts.IsInnerAut τ := (KFacts.not_isInnerAut_inducedAutHom_iff L e₂ hxN).mpr hxout
  have hfield : (stdPinnedPSL2 K).IsField τ := by
    rcases KFacts.hasKind_psl2_diagonal_or_field_of_pow_three_eq_one hτ3 hτout with hD | hF
    · exfalso
      obtain ⟨hD1, hD2⟩ := hD
      exact hD2 (mem_range_conj_of_mem_range_pglAction hD1 hτ3)
    · exact hF
  have hkind : KFacts.InducesStdKind L x .field := .psl2 K ⟨e₂, hxN, hfield⟩
  have hτR' : τ ∈ R' := ⟨thetaAct hAN ⟨x, hxA⟩, ⟨⟨x, hxA⟩, rfl⟩, rfl⟩
  obtain ⟨φ, ⟨σ, rfl⟩, hφ1, d, ⟨h, rfl⟩, hτeq⟩ := hfield
  have hσ3 : σ ^ 3 = 1 := by
    apply psl2FieldAut_injective K
    rw [map_pow, map_one]
    have h1 := hτ3
    rw [hτeq, conj_pow] at h1
    have h2 : (psl2FieldAut K σ) ^ 3 =
        (pglAction K h)⁻¹ * (pglAction K h * psl2FieldAut K σ ^ 3 * (pglAction K h)⁻¹) *
          pglAction K h := by group
    rw [h2, h1]
    group
  have hσ1 : σ ≠ 1 := fun h1 => hφ1 (by rw [h1, map_one])
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have h3e : 3 ∣ e := by
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K
      hKc).1
    have h2 : orderOf σ ∣ Nat.card (RingAut K) := orderOf_dvd_natCard σ
    rw [hσo, h1] at h2
    exact h2
  obtain ⟨m, hm⟩ := h3e
  have hk : Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ) =
      3 ^ m := by
    have h1 := (CFSG.RankThree.LinearTwo.card_fixedSubfield Nat.prime_three (by omega) hKc σ).2
    have he3 : e / orderOf σ = m := by rw [hσo]; omega
    rw [he3] at h1
    exact h1
  have hm3 : 2 < m := by
    set Ph : Subgroup (PGL2 K) := (P.comap (pglAction K)).map (MulAut.conj h⁻¹).toMonoidHom
      with hPh
    have hPcomap : (P.comap (pglAction K)).map (pglAction K) = P :=
      Subgroup.map_comap_eq_self inf_le_right
    have hPhcard : Nat.card Ph = Nat.card P := by
      rw [hPh, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, ← hPcomap,
        Subgroup.card_map_of_injective (pglAction_injective K)]
      rw [hPcomap]
    have hP3 : IsPGroup 3 P :=
      isPGroup_of_isElemAbelian (isElemAbelian_of_le hR'e inf_le_left)
    have hPh3 : IsPGroup 3 Ph := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP3
      exact IsPGroup.of_card (n := a) (by rw [hPhcard, ha])
    have hfix : ∀ g ∈ Ph, pgl2FieldAut K σ g = g := by
      rintro _ ⟨g₀, hg₀, rfl⟩
      set π := pglAction K g₀ with hπ
      have hπR' : π ∈ R' := hg₀.1
      have hτπ : τ * π = π * τ :=
        congrArg Subtype.val (hR'e.1.1.comm ⟨τ, hτR'⟩ ⟨π, hπR'⟩)
      set g := (MulAut.conj h⁻¹).toMonoidHom g₀ with hg
      have hgdef : g = h⁻¹ * g₀ * h := by
        rw [hg]
        simp
      have hφeq : psl2FieldAut K σ = (pglAction K h)⁻¹ * τ * pglAction K h := by
        rw [hτeq]
        group
      have hgπ : pglAction K g = (pglAction K h)⁻¹ * π * pglAction K h := by
        rw [hgdef, map_mul, map_mul, map_inv]
      have key : psl2FieldAut K σ * pglAction K g * (psl2FieldAut K σ)⁻¹ = pglAction K g := by
        calc psl2FieldAut K σ * pglAction K g * (psl2FieldAut K σ)⁻¹ =
            (pglAction K h)⁻¹ * (τ * π * τ⁻¹) * pglAction K h := by rw [hφeq, hgπ]; group
          _ = (pglAction K h)⁻¹ * π * pglAction K h := by
              rw [show τ * π * τ⁻¹ = π by rw [hτπ]; group]
          _ = pglAction K g := hgπ.symm
      rw [KFacts.psl2FieldAut_mul_pglAction_mul_inv] at key
      exact pglAction_injective K key
    have hle := card_le_of_forall_fixed hPh3 hfix hk
    rw [hPhcard] at hle
    by_contra hm2
    push Not at hm2
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center L) := by
    intro h3
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3 h3
    have hz3 : (z : L) ^ 3 = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have h1 := hZ3 z z.2 hz3
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    norm_num at hz
  have hLq : GorensteinWalter.IsQuasisimple L := by
    have := hL.1.2.1
    exact ⟨(QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial,
      hL.1.1.commutator_eq_top, hL.1.2.1⟩
  have hZL : Subgroup.center L = ⊥ := by
    refine center_eq_bot_of_quasisimple_psl2_quotient_coprime hLq K
      ⟨3, e, Nat.prime_three, by decide, he1, hKc⟩ ?_ hZodd ?_
      ⟨(Res417Three.thetaQuotCenterEquiv hL.1).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZs).trans (QuotientGroup.quotientBot.trans e₂))⟩
    · rw [hKc]
      calc 7 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hKc]
      exact Nat.Coprime.pow_right e
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Z).symm
  have hθ : aschbacherSolvableCore 3 L = ⊥ :=
    le_bot_iff.mp ((aschbacherSolvableCore_le_center hL.1).trans hZL.le)
  have eL : L ≃* L ⧸ aschbacherSolvableCore 3 L :=
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).symm
  refine ⟨x, hxE, m, hm3, ?_, hkind⟩
  rw [hm] at e₁
  exact ⟨eL.trans e₁⟩

end Of

section Closed

theorem inputs413L2Three_holds
    : Inputs413L2Three :=
  inputs413L2Three_of rank3II_4_5

end Closed

end CFSG.RankThree.PartTwo.Sec4
