module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Realization
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACExc
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient

public section

namespace CFSG.StandardType.GGQ2CentPort.Q2TwE6

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.E6ThreeModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open

private theorem frame_realization
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hL : labelOn (fun lab => lab.tag = .twE6) 3 Bs L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))),
      Nat.card K = 4 ∧ (∀ c, σ c = c ^ 2) ∧
      S = (ggBeta L θ hN).range.map
        (MulAut.congr (centerQuotEquivOfBot
          (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom ∧
      S ≤ (RecipeExcLang.twConj K σ).range ∧
      3 ^ 5 ≤ Nat.card (ggGamma L hN).range := by
  classical
  have hLkeep := hL
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, hN1, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hmarkLab : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', hθ⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩
  have hmarkI : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L :=
    QTwoCav.innerDiagOnLabel_of_setting hS hmarkLab
  have hsplit : LargeEvenSplit 3 lab := Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htag],
    by simp [htag], by rw [hn1]; norm_num⟩)
  have hmarkTB : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F h => by
        obtain ⟨hs, hna, θ, hθ⟩ := h
        exact ⟨hs, hna, θ, ⟨⟨htag, rfl, by rw [hn1]; norm_num⟩, hsplit,
          hθ.2.1, hθ.2.2⟩⟩) hraw⟩
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hN1).range :=
    ggQ2TwE6_lower hS rfl hmarkTB (hN := hN1)
  have hup : Nat.card (ggGamma L hN1).range ≤ 3 ^ 6 :=
    ggQ2TwE6_upper hS rfl hLkeep (hN := hN1)
  obtain ⟨e, he⟩ : ∃ e, ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ e := by
    rcases ggQ2TwE6_index hS rfl (hN := hN1) hr hup with h6 | h5
    · exact ⟨6, h6⟩
    · exact ⟨5, h5⟩
  obtain ⟨K, instF, instFin, σ, θ, hN, S, hK4, hσ, hSdef, -, -, hSrange, -, -, -⟩ :=
    QTwoE6.actual_beta_image_of_marking hS rfl hq htag hmarkI he
  have hNN : hN = hN1 := Subsingleton.elim hN hN1
  have hr' : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range := by
    rw [hNN]
    exact hr
  exact ⟨K, instF, instFin, σ, θ, hN, S, hK4, hσ, hSdef, hSrange, hr'⟩

private theorem frame_setup
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK4 : Nat.card K = 4)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hSrange : S ≤ (RecipeExcLang.twConj K σ).range)
    (hr : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (ζ : (AlgebraicClosure K)ˣ)
      (eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ)),
      ζ ^ 3 = 1 ∧ orderOf ζ = 3 ∧ (∀ c, Fr c = c ^ 2) ∧
      Function.Surjective (ggQuotHom (θ.trans eR)) ∧
      (ggQuotHom (θ.trans eR)).ker = Subgroup.center ↥L ∧
      IsElemAbelian 3 (ggGamma L hN).range ∧
      GGTorusSelfCent 3 (ggGamma L hN).range ∧
      3 ^ 5 ≤ Nat.card (ggGamma L hN).range ∧
      (∀ (b : ↥Bs) (l : ↥L),
        MulAut.congr eR (ggBeta L θ hN b) (ggQuotHom (θ.trans eR) l) =
          ggQuotHom (θ.trans eR) (ggGamma L hN b l)) ∧
      (∀ a ∈ (ggGamma L hN).range, ∃ φ : MulAut ↥(twistedE6RootGroup K σ),
        φ ∈ (RecipeExcLang.twConj K σ).range ∧
        ∀ l, φ (ggQuotHom (θ.trans eR) l) = ggQuotHom (θ.trans eR) (a l)) := by
  classical
  have : CharP K 2 := charP_two_of_card (m := 2) (by rw [hK4]; norm_num)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two Nat.prime_three (by norm_num)
  have hζ : ζ ^ 3 = 1 := hζp.pow_eq_one
  have hζo : orderOf ζ = 3 := hζp.eq_orderOf.symm
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 :=
    fun c => iterateFrobenius_def (R := AlgebraicClosure K) 2 1 c
  let eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ) :=
    centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let θ' : L ⧸ Subgroup.center L ≃* ↥(twistedE6RootGroup K σ) := θ.trans eR
  let ψ₀ : ↥L →* ↥(twistedE6RootGroup K σ) := ggQuotHom θ'
  have hψ₀ : Function.Surjective ψ₀ := ggQuotHom_surjective θ'
  have hkerEq : ψ₀.ker = Subgroup.center ↥L := ker_ggQuotHom θ'
  let A : Subgroup (MulAut ↥L) := (ggGamma L hN).range
  obtain ⟨hA, hsc⟩ := QTwoCav.gamma_hyps hS hN
  have hβtrans : ∀ (b : ↥Bs),
      ggBeta L θ' hN b = MulAut.congr eR (ggBeta L θ hN b) := by
    intro b
    exact (congrArg (fun f => f b) (QTwoCav.beta_trans θ eR hN)).symm
  have hβψ : ∀ (b : ↥Bs) (l : ↥L),
      MulAut.congr eR (ggBeta L θ hN b) (ψ₀ l) = ψ₀ (ggGamma L hN b l) := by
    intro b l
    rw [← hβtrans b]
    exact ggBeta_ggQuotHom L hN θ' b l
  have hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l, φ (ψ₀ l) = ψ₀ (a l) := by
    rintro _ ⟨b, rfl⟩
    have hφS : MulAut.congr eR (ggBeta L θ hN b) ∈ S := by
      rw [hSdef]
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨_, hSrange hφS, fun l => hβψ b l⟩
  exact ⟨Fr, ζ, eR, hζ, hζo, by simpa using hFr, hψ₀, hkerEq, hA, hsc, hr, hβψ, hAH⟩

private theorem frame_torus
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK4 : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ)}
    (hψ₀ : Function.Surjective (ggQuotHom (θ.trans eR)))
    (hker : (ggQuotHom (θ.trans eR)).ker ≤ Subgroup.center ↥L)
    (hperf : commutator ↥L = ⊤)
    {A : Subgroup (MulAut ↥L)} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ : MulAut ↥(twistedE6RootGroup K σ),
      φ ∈ (RecipeExcLang.twConj K σ).range ∧
      ∀ l, φ (ggQuotHom (θ.trans eR) l) = ggQuotHom (θ.trans eR) (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    ∃ (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (κ : A →* Multiplicative (Fin 6 → ZMod 3))
      (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K) (T : Subgroup ↥L),
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
        g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
      (∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
        g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) ∧
      (∀ (a : A) (l : ↥L),
        ((ggQuotHom (θ.trans eR) ((a : MulAut ↥L) l) :
          ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          t (Multiplicative.toAdd (κ a)) *
            ((ggQuotHom (θ.trans eR) l : ↥(twistedE6RootGroup K σ)) :
              ModGL TwistTag.E6.tag K) *
            (t (Multiplicative.toAdd (κ a)))⁻¹) ∧
      (∀ z ∈ (ggQuotHom (θ.trans eR)).ker, Odd (orderOf z) → z ∈ T) ∧
      (∀ a ∈ A, ∀ y ∈ T, a y = y) ∧
      (∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
        MulAut.conj y = (b : MulAut ↥L) ∧ Multiplicative.toAdd (κ b) = x) := by
  classical
  have hK1 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK4]; norm_num
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := by simpa using hσ
  have hFr1 : ∀ c, Fr c = c ^ 2 ^ 1 := by simpa using hFr
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have : CharP K 2 := charP_two_of_card (m := 2) (by rw [hK4]; norm_num)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  obtain ⟨g, κ, t, T, hg, hgF, -, -, ht, hconj, hTodd, hTfix, hHyp, -⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (n := 1) le_rfl hK1 σ hσ1 h3 hFr1 hζ hζo
      hψ₀ hker hperf hA hAH h5 hsc
  exact ⟨g, κ, t, T, hg, hgF, ht, hconj, hTodd, hTfix, hHyp⟩

private theorem frame_beta_center
    {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ)}
    {κ : (ggGamma L hN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    {T : Subgroup ↥L}
    (hψ₀ : Function.Surjective (ggQuotHom (θ.trans eR)))
    (hkerEq : (ggQuotHom (θ.trans eR)).ker = Subgroup.center ↥L)
    (hconj : ∀ (a : (ggGamma L hN).range) (l : ↥L),
      ((ggQuotHom (θ.trans eR) ((a : MulAut ↥L) l) :
        ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        t (Multiplicative.toAdd (κ a)) *
          ((ggQuotHom (θ.trans eR) l : ↥(twistedE6RootGroup K σ)) :
            ModGL TwistTag.E6.tag K) *
          (t (Multiplicative.toAdd (κ a)))⁻¹)
    (hTodd : ∀ z ∈ (ggQuotHom (θ.trans eR)).ker, Odd (orderOf z) → z ∈ T)
    (hTfix : ∀ a ∈ (ggGamma L hN).range, ∀ y ∈ T, a y = y)
    (hHyp : ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : (ggGamma L hN).range,
      MulAut.conj y = (b : MulAut ↥L) ∧ Multiplicative.toAdd (κ b) = x) :
    ∃ (κB : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)),
      (∀ v ∈ NoOffRest.hypE6, Multiplicative.ofAdd v ∈ κB.range) ∧
      (∀ (hN' : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs)
        (r : ↥(twistedE6RootGroup K σ)),
        ((ggBeta L (θ.trans eR) hN' b r : ↥(twistedE6RootGroup K σ)) :
            ModGL TwistTag.E6.tag K) =
          t (Multiplicative.toAdd (κB b)) * (r : ModGL TwistTag.E6.tag K) *
            (t (Multiplicative.toAdd (κB b)))⁻¹) ∧
      (∀ z ∈ Subgroup.center L, IsPGroup 3 (Subgroup.zpowers z) →
        ∀ b ∈ Bs, b * (z : G) = (z : G) * b) := by
  classical
  let κB : ↥Bs →* Multiplicative (Fin 6 → ZMod 3) :=
    κ.comp (ggGamma L hN).rangeRestrict
  have hκhyp : ∀ v ∈ NoOffRest.hypE6, Multiplicative.ofAdd v ∈ κB.range := by
    intro v hv
    obtain ⟨y, hyT, hy3, b, hb, hκb⟩ := hHyp v hv
    obtain ⟨c, hc⟩ := (ggGamma L hN).rangeRestrict_surjective b
    refine ⟨c, ?_⟩
    change κ ((ggGamma L hN).rangeRestrict c) = Multiplicative.ofAdd v
    rw [hc]
    exact congrArg Multiplicative.ofAdd hκb
  have hβclause : ∀ (hN' : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs)
      (r : ↥(twistedE6RootGroup K σ)),
      ((ggBeta L (θ.trans eR) hN' b r : ↥(twistedE6RootGroup K σ)) :
          ModGL TwistTag.E6.tag K) =
        t (Multiplicative.toAdd (κB b)) * (r : ModGL TwistTag.E6.tag K) *
          (t (Multiplicative.toAdd (κB b)))⁻¹ := by
    intro hN' b r
    rw [Subsingleton.elim hN' hN]
    obtain ⟨l, rfl⟩ := hψ₀ r
    rw [ggBeta_ggQuotHom L hN (θ.trans eR) b l]
    exact hconj ((ggGamma L hN).rangeRestrict b) l
  have hcenter : ∀ z ∈ Subgroup.center L, IsPGroup 3 (Subgroup.zpowers z) →
      ∀ b ∈ Bs, b * (z : G) = (z : G) * b := by
    intro z hz hzP b hb
    have hzker : z ∈ (ggQuotHom (θ.trans eR)).ker := by
      rw [hkerEq]
      exact hz
    have hodd : Odd (orderOf z) := by
      obtain ⟨k, hk⟩ := hzP.exists_orderOf_dvd_pow
        (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z)
      rw [← Subgroup.orderOf_coe] at hk
      exact Odd.of_dvd_nat (Odd.pow (n := k) (by norm_num : Odd 3)) hk
    have hzT : z ∈ T := hTodd z hzker hodd
    have hfix : ggGamma L hN ⟨b, hb⟩ z = z :=
      hTfix (ggGamma L hN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ z hzT
    have hcoe : (b : G) * (z : G) * (b : G)⁻¹ = (z : G) := by
      have := congrArg Subtype.val hfix
      simpa [ggGamma_coe] using this
    calc b * (z : G) = ((b : G) * (z : G) * (b : G)⁻¹) * (b : G) := by group
      _ = (z : G) * (b : G) := by rw [hcoe]
  exact ⟨κB, hκhyp, hβclause, hcenter⟩

private theorem frame_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {κ : (ggGamma L hN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥L}
    (hTfix : ∀ a ∈ (ggGamma L hN).range, ∀ y ∈ T, a y = y)
    (hHyp : ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : (ggGamma L hN).range,
      MulAut.conj y = (b : MulAut ↥L) ∧ Multiplicative.toAdd (κ b) = x) :
    3 ^ 5 ≤ Nat.card ((Bs.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)) := by
  classical
  have hchoice : ∀ v : NoOffRest.hypE6, ∃ (y : ↥L) (b : (ggGamma L hN).range),
      y ∈ T ∧ y ^ 3 = 1 ∧ MulAut.conj y = (b : MulAut ↥L) ∧
        Multiplicative.toAdd (κ b) = (v : Fin Tag.E6.rank → ZMod 3) := by
    intro v
    obtain ⟨y, hyT, hy3, b, hb, hκ⟩ := hHyp v v.2
    exact ⟨y, b, hyT, hy3, hb, hκ⟩
  choose y b hyT hy3 hbconj hκb using hchoice
  have hyBs : ∀ v, (y v : G) ∈ Bs := by
    intro v
    have hcent : (y v : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hfix : ggGamma L hN ⟨c, hc⟩ (y v) = y v :=
        hTfix (ggGamma L hN ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩ (y v) (hyT v)
      have hcoe : (c : G) * (y v : G) * (c : G)⁻¹ = (y v : G) := by
        have := congrArg Subtype.val hfix
        simpa [ggGamma_coe] using this
      calc (c : G) * (y v : G) = ((c : G) * (y v : G) * (c : G)⁻¹) * (c : G) := by
            group
        _ = (y v : G) * (c : G) := by rw [hcoe]
    have hy3G : (y v : G) ^ 3 = 1 := by
      have := congrArg Subtype.val (hy3 v)
      simpa using this
    exact hS.1.1.2.1.2.2.2 _ hcent hy3G
  let f : NoOffRest.hypE6 →
      (Bs.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) := fun v =>
    ⟨MulAut.conj (y v), ⟨y v, Subgroup.mem_subgroupOf.mpr (hyBs v), rfl⟩⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have hconj : MulAut.conj (y v) = MulAut.conj (y w) := congrArg Subtype.val hvw
    have hb : b v = b w := by
      apply Subtype.ext
      rw [← hbconj v, ← hbconj w]
      exact hconj
    have hκ := congrArg (fun z : (ggGamma L hN).range => Multiplicative.toAdd (κ z)) hb
    exact Subtype.ext ((hκb v).symm.trans (hκ.trans (hκb w)))
  have hle : Nat.card NoOffRest.hypE6 ≤
      Nat.card ((Bs.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)) :=
    Nat.card_le_card_of_injective f hf
  rw [NoOffRest.card_hypE6] at hle
  exact hle

theorem exists_frame
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hL : labelOn (fun lab => lab.tag = .twE6) 3 Bs L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (θ : L ⧸ Subgroup.center L ≃* ↥(twistedE6RootGroup K σ))
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (ζ : (AlgebraicClosure K)ˣ)
      (hζ : ζ ^ 3 = 1) (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K)
      (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)),
      Nat.card K = 4 ∧ (∀ c, σ c = c ^ 2) ∧ (∀ c, Fr c = c ^ 2) ∧ orderOf ζ = 3 ∧
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
        g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
      (∀ v, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t v) =
        g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ v) * g⁻¹) ∧
      (∀ v ∈ NoOffRest.hypE6, Multiplicative.ofAdd v ∈ κ.range) ∧
      (∀ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs)
        (r : ↥(twistedE6RootGroup K σ)),
        ((ggBeta L θ hN b r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          t (Multiplicative.toAdd (κ b)) * (r : ModGL TwistTag.E6.tag K) *
            (t (Multiplicative.toAdd (κ b)))⁻¹) ∧
      (∀ z ∈ Subgroup.center L, IsPGroup 3 (Subgroup.zpowers z) →
        ∀ b ∈ Bs, b * (z : G) = (z : G) * b) ∧
      3 ^ 5 ≤ Nat.card ((Bs.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)) := by
  classical
  have hperf : commutator ↥L = ⊤ := hL.1
  obtain ⟨K, instF, instFin, σ, θ, hN, S, hK4, hσ, hSdef, hSrange, hr⟩ :=
    frame_realization hS hL
  obtain ⟨Fr, ζ, eR, hζ, hζo, hFr, hψ₀, hkerEq, hA, hsc, h5, -, hAH⟩ :=
    frame_setup hS hK4 hSdef hSrange hr
  obtain ⟨g, κ, t, T, hg, hgF, ht, hconj, hTodd, hTfix, hHyp⟩ :=
    frame_torus hK4 hσ hFr hζ hζo hψ₀ hkerEq.le hperf hA hAH h5 hsc
  obtain ⟨κB, hκBhyp, hβclause, hcenter⟩ :=
    frame_beta_center (hN := hN) hψ₀ hkerEq hconj hTodd hTfix hHyp
  have hcardE := frame_card (hN := hN) hS hTfix hHyp
  exact ⟨K, instF, instFin, σ, θ.trans eR, Fr, ζ, hζ, g, t, κB, hK4, hσ, hFr, hζo, hg, hgF,
    ht, hκBhyp, hβclause, hcenter, hcardE⟩

end CFSG.StandardType.GGQ2CentPort.Q2TwE6

end
